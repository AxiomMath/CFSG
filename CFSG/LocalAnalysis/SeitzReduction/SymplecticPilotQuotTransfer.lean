module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGen
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueReduce

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect map_perfectCore
  perfectCore_eq_self_of_perfect)

section Groups

variable {M : Type*} [Group M]

theorem commute_of_perfect_of_mk_commute {H : Subgroup M} (hH : ⁅H, H⁆ = H) {u : M}
    (hu : ∀ h ∈ H, (QuotientGroup.mk (h * u) : M ⧸ center M) = QuotientGroup.mk (u * h)) :
    ∀ h ∈ H, h * u = u * h := by
  have hc : ∀ h ∈ H, h * u * h⁻¹ * u⁻¹ ∈ center M := by
    intro h hh
    have h1 := QuotientGroup.eq.1 (hu h hh)
    have h2 : h * u * h⁻¹ * u⁻¹ = (h * u) * ((h * u)⁻¹ * (u * h))⁻¹ * (h * u)⁻¹ := by group
    rw [h2]
    exact (inferInstance : (center M).Normal).conj_mem _ (inv_mem h1) _
  have : Group.IsPerfect H := isPerfect_iff.mpr hH
  let φ : H →* center M :=
    { toFun := fun h => ⟨(h : M) * u * (h : M)⁻¹ * u⁻¹, hc h h.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change ((a : M) * b) * u * ((a : M) * b)⁻¹ * u⁻¹ =
          ((a : M) * u * (a : M)⁻¹ * u⁻¹) * ((b : M) * u * (b : M)⁻¹ * u⁻¹)
        have hb := mem_center_iff.1 (hc b b.2)
        calc ((a : M) * b) * u * ((a : M) * b)⁻¹ * u⁻¹ =
            (a : M) * ((b : M) * u * (b : M)⁻¹ * u⁻¹) * (u * (a : M)⁻¹ * u⁻¹) := by group
          _ = ((b : M) * u * (b : M)⁻¹ * u⁻¹) * (a : M) * (u * (a : M)⁻¹ * u⁻¹) := by
            rw [hb (a : M)]
          _ = ((b : M) * u * (b : M)⁻¹ * u⁻¹) * ((a : M) * u * (a : M)⁻¹ * u⁻¹) := by group
          _ = ((a : M) * u * (a : M)⁻¹ * u⁻¹) * ((b : M) * u * (b : M)⁻¹ * u⁻¹) :=
            (hb _).symm) }
  have hφ := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative φ
  intro h hh
  have h1 : (h : M) * u * h⁻¹ * u⁻¹ = 1 :=
    congrArg Subtype.val (DFunLike.congr_fun hφ ⟨h, hh⟩)
  calc h * u = (h * u * h⁻¹ * u⁻¹) * (u * h) := by group
    _ = u * h := by rw [h1, one_mul]

theorem eq_top_of_map_mk_eq_top [Group.IsPerfect M] {S : Subgroup M}
    (h : S.map (QuotientGroup.mk' (center M)) = ⊤) : S = ⊤ := by
  refine LinearPilot.eq_top_of_sup_center_eq_top_of_perfect ?_
  have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' (center M))) h
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h1

end Groups

theorem commutator_subgroupOf_eq {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (hH : ⁅H, H⁆ = H) : ⁅H.subgroupOf K, H.subgroupOf K⁆ = H.subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hHK, hH]

section Transfer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] in
theorem injective_mk_comp_inclusion {M : Subgroup G} (hLM : L ≤ M) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hZ : Odd (Nat.card (center M))) :
    Function.Injective ((QuotientGroup.mk' (center M)).comp (Subgroup.inclusion hLM)) := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hxZ : Subgroup.inclusion hLM x ∈ center M := by
    rw [← QuotientGroup.ker_mk' (center M), MonoidHom.mem_ker]
    exact hx
  have h1 := eq_one_of_mem_center_of_commute hLM ht hKt hZ hxZ
    (mem_centralizer_iff.1 htC (x : G) x.2)
  have h2 : ((Subgroup.inclusion hLM x : M) : G) = ((1 : M) : G) := by rw [h1]
  exact (mem_bot).2 (Subtype.ext h2)

theorem exists_conj_fieldSp_of_quot (hset : SeitzSetting G L) {n : ℕ} (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hLS : L ≤ G₀) (hZ : Odd (Nat.card (center G₀)))
    (htN : t ∈ normalizer (G₀ : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (G₀ : Set G))
    (γ : MulAut (G₀ ⧸ center G₀))
    (hγ : γ * centerQuotAction G₀ ⟨t, htN⟩ = centerQuotAction G₀ ⟨g⁻¹ * t * g, hg⟩ * γ) :
    ∃ (l : G) (σ : K ≃+* K), l ∈ L ∧ ∀ x : StatedSp n K,
      ∃ hu : g⁻¹ * (l * ((e.symm (fieldSp n K σ x) : L) : G) * l⁻¹) * g ∈ G₀,
        γ (QuotientGroup.mk' (center G₀) (Subgroup.inclusion hLS (e.symm x))) =
          QuotientGroup.mk' (center G₀) ⟨_, hu⟩ := by
  set π : G₀ →* G₀ ⧸ center G₀ := QuotientGroup.mk' (center G₀) with hπ
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp hn e)
  have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
  set θt := G₀.normalizerMonoidHom ⟨t, htN⟩ with hθt
  set θw := G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθw
  have hfixt := map_mk_fixedSubgroup_eq_centerQuot hZ ht htN
  have hfixw := map_mk_fixedSubgroup_eq_centerQuot hZ hw2 hg
  have hγfix : ∀ y, y ∈ fixedSubgroup (centerQuotAction G₀ ⟨t, htN⟩) →
      γ y ∈ fixedSubgroup (centerQuotAction G₀ ⟨g⁻¹ * t * g, hg⟩) := by
    intro y hy
    have hy' : centerQuotAction G₀ ⟨t, htN⟩ y = y := hy
    change centerQuotAction G₀ ⟨g⁻¹ * t * g, hg⟩ (γ y) = γ y
    have h1 := congrArg (fun φ : MulAut (G₀ ⧸ center G₀) => φ y) hγ
    simp only [MulAut.mul_apply] at h1
    rw [← h1, hy']
  have hLfix : ∀ x : L, Subgroup.inclusion hLS x ∈ fixedSubgroup θt := by
    intro x
    change θt _ = _
    apply Subtype.ext
    rw [hθt, Subgroup.normalizerMonoidHom_apply_apply_coe]
    change t * (x : G) * t⁻¹ = x
    rw [← mem_centralizer_iff.1 htC (x : G) x.2, mul_inv_cancel_right]
  set φ₁ : L →* G₀ ⧸ center G₀ := γ.toMonoidHom.comp (π.comp (Subgroup.inclusion hLS)) with hφ₁
  have hφ₁inj : Function.Injective φ₁ :=
    γ.injective.comp (injective_mk_comp_inclusion hLS ht hKt hZ)
  set A : Subgroup (G₀ ⧸ center G₀) := φ₁.range with hA
  have hAw : A ≤ fixedSubgroup (centerQuotAction G₀ ⟨g⁻¹ * t * g, hg⟩) := by
    rintro _ ⟨x, rfl⟩
    refine hγfix _ ?_
    rw [← hfixt]
    exact ⟨_, hLfix x, rfl⟩
  set Y : Subgroup G₀ := fixedSubgroup θw ⊓ A.comap π with hY
  have hYmap : Y.map π = A := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · intro a ha
      have ha' := hAw ha
      rw [← hfixw] at ha'
      obtain ⟨y, hy, rfl⟩ := ha'
      exact ⟨y, ⟨hy, ha⟩, rfl⟩
  have hSpP : Group.IsPerfect (StatedSp n K) := isPerfect_statedSp_of_charTwo hn
  have hLP : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hAP : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := φ₁.rangeRestrict) φ₁.rangeRestrict_surjective
  have hAperf : ⁅A, A⁆ = A := isPerfect_iff.mp hAP
  set P : Subgroup G₀ := perfectCore Y with hP
  have hPmap : P.map π = A := by
    rw [hP, map_perfectCore, hYmap, perfectCore_eq_self_of_perfect hAperf]
  have hPperf : ⁅P, P⁆ = P := perfectCore_perfect Y
  have hPw : P ≤ fixedSubgroup θw := (perfectCore_le Y).trans inf_le_left
  set c : G₀ →* G := (MulAut.conj g).toMonoidHom.comp G₀.subtype with hc
  have hcinj : Function.Injective c := (MulAut.conj g).injective.comp G₀.subtype_injective
  have hQperf : ⁅P.map c, P.map c⁆ = P.map c := by rw [← Subgroup.map_commutator, hPperf]
  have hQt : P.map c ≤ centralizer ({t} : Set G) :=
    (Subgroup.map_mono hPw).trans (map_fixedSubgroup_conj_le_centralizer hg)
  have hQL : P.map c ≤ L := std_perfect_le hset.standardSetting hOut htC ht hQperf hQt
  have hcardA : Nat.card A = Nat.card L :=
    (Nat.card_congr (MonoidHom.ofInjective hφ₁inj).toEquiv).symm
  set ρ : P →* G₀ ⧸ center G₀ := π.comp P.subtype with hρ
  have hρrange : ρ.range = A := by rw [hρ, MonoidHom.range_comp, Subgroup.range_subtype, hPmap]
  have hρinj : Function.Injective ρ := by
    have hle : Nat.card P ≤ Nat.card ρ.range := by
      rw [hρrange, hcardA, ← Subgroup.card_map_of_injective hcinj]
      exact Subgroup.card_le_of_le hQL
    have hbij := ρ.rangeRestrict_surjective.bijective_of_nat_card_le hle
    intro a b hab
    exact hbij.1 (Subtype.ext hab)
  set ι : A ≃* P := (MulEquiv.subgroupCongr hρrange.symm).trans (MonoidHom.ofInjective hρinj).symm
    with hι
  have hπι : ∀ a : A, π (ι a : G₀) = a := by
    intro a
    have h1 := MonoidHom.ofInjective_apply hρinj (x := ι a)
    rw [hι, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  set α : L →* L := MonoidHom.codRestrict
    (c.comp (P.subtype.comp (ι.toMonoidHom.comp φ₁.rangeRestrict))) L
    (fun x => hQL ⟨_, (ι (φ₁.rangeRestrict x)).2, rfl⟩) with hα
  have hαinj : Function.Injective α := by
    intro x y hxy
    have h1 : c (ι (φ₁.rangeRestrict x) : G₀) = c (ι (φ₁.rangeRestrict y) : G₀) :=
      congrArg Subtype.val hxy
    have h2 := ι.injective (Subtype.ext (hcinj h1))
    exact hφ₁inj (congrArg Subtype.val h2)
  let αE : L ≃* L := MulEquiv.ofBijective α hαinj.bijective_of_finite
  obtain ⟨s, σ, hβ⟩ := exists_eq_conj_mul_fieldSp hn ((e.symm.trans αE).trans e)
  set l : G := ((e.symm s : L) : G) with hl
  have hkey : ∀ x : StatedSp n K, ((α (e.symm x) : L) : G) =
      l * ((e.symm (fieldSp n K σ x) : L) : G) * l⁻¹ := by
    intro x
    have h1 := congrArg (fun β : MulAut (StatedSp n K) => β x) hβ
    simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.conj_apply] at h1
    have h2 : αE (e.symm x) = e.symm (s * fieldSp n K σ x * s⁻¹) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    have h3 := congrArg Subtype.val h2
    rw [map_mul, map_mul, map_inv] at h3
    exact h3
  refine ⟨l, σ, (e.symm s).2, fun x => ?_⟩
  have hux : g⁻¹ * (l * ((e.symm (fieldSp n K σ x) : L) : G) * l⁻¹) * g =
      ((ι (φ₁.rangeRestrict (e.symm x)) : G₀) : G) := by
    rw [← hkey x]
    change g⁻¹ * (g * ((ι (φ₁.rangeRestrict (e.symm x)) : G₀) : G) * g⁻¹) * g = _
    group
  have hu : g⁻¹ * (l * ((e.symm (fieldSp n K σ x) : L) : G) * l⁻¹) * g ∈ G₀ := by
    rw [hux]
    exact (ι (φ₁.rangeRestrict (e.symm x)) : G₀).2
  refine ⟨hu, ?_⟩
  have h1 : (⟨_, hu⟩ : G₀) = (ι (φ₁.rangeRestrict (e.symm x)) : G₀) := Subtype.ext hux
  rw [h1]
  change φ₁ (e.symm x) = _
  rw [hπι]
  rfl

omit [Finite K] [CharP K 2] in
theorem map_conj_perfectCore_le_spGlobal {n : ℕ} (e : L ≃* StatedSp n K) (hLS : L ≤ spGlobal e)
    (γ : MulAut (spGlobal e ⧸ center (spGlobal e))) {g l : G} (hlL : l ∈ L) {σ : K ≃+* K}
    (hkey : ∀ x : StatedSp n K,
      ∃ hu : g⁻¹ * (l * ((e.symm (fieldSp n K σ x) : L) : G) * l⁻¹) * g ∈ spGlobal e,
        γ (QuotientGroup.mk' (center (spGlobal e)) (Subgroup.inclusion hLS (e.symm x))) =
          QuotientGroup.mk' (center (spGlobal e)) ⟨_, hu⟩) (j : Fin n) :
    (perfectCore (((((pieceCore e ({j} : Finset (Fin n))).subgroupOf (spGlobal e)).map
        (QuotientGroup.mk' (center (spGlobal e)))).map γ.toMonoidHom).comap
          (QuotientGroup.mk' (center (spGlobal e))))).map
        ((MulAut.conj g).toMonoidHom.comp (spGlobal e).subtype) ≤ spGlobal e := by
  have hPle : pieceCore e ({j} : Finset (Fin n)) ≤ spGlobal e := by
    rw [spGlobal_def]
    exact le_iSup (fun i : Fin n => pieceCore e ({i} : Finset (Fin n))) j
  set R := perfectCore (((((pieceCore e ({j} : Finset (Fin n))).subgroupOf (spGlobal e)).map
      (QuotientGroup.mk' (center (spGlobal e)))).map γ.toMonoidHom).comap
        (QuotientGroup.mk' (center (spGlobal e)))) with hR
  have hRperf : ⁅R, R⁆ = R := perfectCore_perfect _
  have hRmap : R.map (QuotientGroup.mk' (center (spGlobal e))) =
      (((pieceCore e ({j} : Finset (Fin n))).subgroupOf (spGlobal e)).map
        (QuotientGroup.mk' (center (spGlobal e)))).map γ.toMonoidHom := by
    rw [hR, map_perfectCore, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _)]
    refine perfectCore_eq_self_of_perfect ?_
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_subgroupOf_eq hPle (F4Pilot.commutator_centralizerPerfectCore _)]
  have hlS : l ∈ spGlobal e := hLS hlL
  set T₀ : Subgroup G := modelToG e (leviTorusSp K ({j} : Finset (Fin n))) with hT₀
  have hcent : ∀ y ∈ R, ∀ x ∈ leviTorusSp K ({j} : Finset (Fin n)),
      (l⁻¹ * (g * ((y : spGlobal e) : G) * g⁻¹) * l) * ((e.symm x : L) : G) =
        ((e.symm x : L) : G) * (l⁻¹ * (g * ((y : spGlobal e) : G) * g⁻¹) * l) := by
    intro y hy x hx
    have hx' : fieldSp n K σ⁻¹ x ∈ leviTorusSp K ({j} : Finset (Fin n)) :=
      fieldSp_mem_leviTorusSp σ⁻¹ hx
    have hσ : fieldSp n K σ (fieldSp n K σ⁻¹ x) = x := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    obtain ⟨hu, hγu⟩ := hkey (fieldSp n K σ⁻¹ x)
    have hmod : ∀ z ∈ R, (QuotientGroup.mk (z * ⟨_, hu⟩) : spGlobal e ⧸ center (spGlobal e)) =
        QuotientGroup.mk (⟨_, hu⟩ * z) := by
      intro z hz
      have hz' : QuotientGroup.mk' (center (spGlobal e)) z ∈
          R.map (QuotientGroup.mk' (center (spGlobal e))) := ⟨z, hz, rfl⟩
      rw [hRmap] at hz'
      obtain ⟨_, ⟨p, hp, rfl⟩, hpz⟩ := hz'
      have hpP : ((p : spGlobal e) : G) ∈ pieceCore e ({j} : Finset (Fin n)) := hp
      have hpc : ((p : spGlobal e) : G) * ((e.symm (fieldSp n K σ⁻¹ x) : L) : G) =
          ((e.symm (fieldSp n K σ⁻¹ x) : L) : G) * ((p : spGlobal e) : G) :=
        (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ hpP) _
          ((mem_modelToG e).2 ⟨_, hx', rfl⟩)).symm
      have hpc' : p * Subgroup.inclusion hLS (e.symm (fieldSp n K σ⁻¹ x)) =
          Subgroup.inclusion hLS (e.symm (fieldSp n K σ⁻¹ x)) * p := Subtype.ext hpc
      have h1 := congrArg (fun v => γ (QuotientGroup.mk' (center (spGlobal e)) v)) hpc'
      simp only [map_mul] at h1
      rw [hγu] at h1
      change γ (QuotientGroup.mk' (center (spGlobal e)) p) = QuotientGroup.mk' _ z at hpz
      rw [hpz] at h1
      change QuotientGroup.mk' _ z * QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _ *
        QuotientGroup.mk' _ z at h1
      rw [← map_mul, ← map_mul] at h1
      exact h1
    have hc := commute_of_perfect_of_mk_commute hRperf hmod y hy
    have hc' : ((y : spGlobal e) : G) *
        (g⁻¹ * (l * ((e.symm (fieldSp n K σ (fieldSp n K σ⁻¹ x)) : L) : G) * l⁻¹) * g) =
        (g⁻¹ * (l * ((e.symm (fieldSp n K σ (fieldSp n K σ⁻¹ x)) : L) : G) * l⁻¹) * g) *
          ((y : spGlobal e) : G) := congrArg Subtype.val hc
    rw [hσ] at hc'
    calc (l⁻¹ * (g * ((y : spGlobal e) : G) * g⁻¹) * l) * ((e.symm x : L) : G) =
        l⁻¹ * g * (((y : spGlobal e) : G) * (g⁻¹ * (l * ((e.symm x : L) : G) * l⁻¹) * g)) *
          g⁻¹ * l := by group
      _ = l⁻¹ * g * ((g⁻¹ * (l * ((e.symm x : L) : G) * l⁻¹) * g) * ((y : spGlobal e) : G)) *
          g⁻¹ * l := by rw [hc']
      _ = ((e.symm x : L) : G) * (l⁻¹ * (g * ((y : spGlobal e) : G) * g⁻¹) * l) := by group
  set Q : Subgroup G := (R.map ((MulAut.conj g).toMonoidHom.comp (spGlobal e).subtype)).map
    (MulAut.conj l⁻¹).toMonoidHom with hQ
  have hQperf : ⁅Q, Q⁆ = Q := by
    rw [hQ, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hRperf]
  have hQT : Q ≤ centralizer (T₀ : Set G) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hh
    have h1 := hcent y hy x hx
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Subgroup.coe_subtype, inv_inv]
    exact h1.symm
  have hQle : Q ≤ pieceCore e ({j} : Finset (Fin n)) :=
    F4Pilot.le_centralizerPerfectCore hQperf hQT
  rintro _ ⟨y, hy, rfl⟩
  have hmem : l⁻¹ * (g * ((y : spGlobal e) : G) * g⁻¹) * l ∈ spGlobal e := by
    refine hPle (hQle ⟨_, ⟨y, hy, rfl⟩, ?_⟩)
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Subgroup.coe_subtype, inv_inv]
  have h2 : ((MulAut.conj g).toMonoidHom.comp (spGlobal e).subtype) y =
      l * (l⁻¹ * (g * ((y : spGlobal e) : G) * g⁻¹) * l) * l⁻¹ := by
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Subgroup.coe_subtype]
    group
  rw [h2]
  exact mul_mem (mul_mem hlS hmem) (inv_mem hlS)

theorem mem_normalizer_of_conj_centerQuotAction (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hperf : Group.IsPerfect (spGlobal e)) (hZ : Odd (Nat.card (center (spGlobal e))))
    (htN : t ∈ normalizer (spGlobal e : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G))
    (γ : MulAut (spGlobal e ⧸ center (spGlobal e)))
    (hγ : γ * centerQuotAction (spGlobal e) ⟨t, htN⟩ =
      centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩ * γ) :
    g ∈ normalizer (spGlobal e : Set G) := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hLS : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  obtain ⟨l, σ, hlL, hkey⟩ :=
    exists_conj_fieldSp_of_quot hset hn e ht hKt hLS hZ htN hg γ hγ
  set c : spGlobal e →* G := (MulAut.conj g).toMonoidHom.comp (spGlobal e).subtype with hc
  set R : Fin n → Subgroup (spGlobal e) := fun j =>
    perfectCore (((((pieceCore e ({j} : Finset (Fin n))).subgroupOf (spGlobal e)).map (QuotientGroup.mk' (center (spGlobal e)))).map
      γ.toMonoidHom).comap (QuotientGroup.mk' (center (spGlobal e)))) with hR
  have hRle : ∀ j, (R j).map c ≤ spGlobal e := fun j =>
    map_conj_perfectCore_le_spGlobal e hLS γ hlL hkey j
  have hPle : ∀ j, pieceCore e ({j} : Finset (Fin n)) ≤ spGlobal e := fun j => by
    rw [spGlobal_def]
    exact le_iSup (fun i : Fin n => pieceCore e ({i} : Finset (Fin n))) j
  have hRmap : ∀ j, (R j).map (QuotientGroup.mk' (center (spGlobal e))) =
      (((pieceCore e ({j} : Finset (Fin n))).subgroupOf (spGlobal e)).map (QuotientGroup.mk' (center (spGlobal e)))).map γ.toMonoidHom := by
    intro j
    rw [hR, map_perfectCore, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _)]
    refine perfectCore_eq_self_of_perfect ?_
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_subgroupOf_eq (hPle j) (F4Pilot.commutator_centralizerPerfectCore _)]
  have hPsup : ⨆ j, (pieceCore e ({j} : Finset (Fin n))).subgroupOf (spGlobal e) = ⊤ := by
    apply Subgroup.map_injective (spGlobal e).subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp only [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hPle _)]
    exact (spGlobal_def e).symm
  have hRsup : ⨆ j, R j = ⊤ := by
    refine eq_top_of_map_mk_eq_top ?_
    rw [Subgroup.map_iSup, iSup_congr hRmap, ← Subgroup.map_iSup, ← Subgroup.map_iSup, hPsup, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 γ.surjective]
  have hconj : ∀ y ∈ spGlobal e, g * y * g⁻¹ ∈ spGlobal e := by
    intro y hy
    have h1 : (⟨y, hy⟩ : spGlobal e) ∈ ⨆ j, R j := by rw [hRsup]; exact mem_top _
    have h2 : c ⟨y, hy⟩ ∈ (⨆ j, R j).map c := ⟨_, h1, rfl⟩
    rw [Subgroup.map_iSup] at h2
    exact (iSup_le hRle) h2
  have hmap : (spGlobal e).map (MulAut.conj g).toMonoidHom ≤ spGlobal e := by
    rintro _ ⟨y, hy, rfl⟩
    exact hconj y hy
  have hcard : Nat.card ((spGlobal e).map (MulAut.conj g).toMonoidHom) = Nat.card (spGlobal e) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : (spGlobal e).map (MulAut.conj g).toMonoidHom = spGlobal e :=
    Subgroup.eq_of_le_of_card_ge hmap (le_of_eq hcard.symm)
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hconj h hh
  · intro hh
    rw [← heq] at hh
    obtain ⟨y, hy, hyh⟩ := hh
    have : y = h := by
      change g * y * g⁻¹ = g * h * g⁻¹ at hyh
      simpa using hyh
    exact this ▸ hy

end Transfer

@[expose] def SpGraphStandardClassQuotInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobalQuot e t f κ →
      ∀ (htN : t ∈ normalizer (spGlobal e : Set G)) (g : G)
        (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
        ∃ γ : MulAut (spGlobal e ⧸ center (spGlobal e)),
          γ * centerQuotAction (spGlobal e) ⟨t, htN⟩ =
            centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩ * γ

@[expose] def SpOmegaRowUniqueQuotInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobalQuot e t f κ →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
        g ∈ normalizer (spGlobal e : Set G)

theorem spOmegaRowUniqueQuotInput_of_standardClass {κ : Sp2mKind}
    (h : SpGraphStandardClassQuotInput κ) : SpOmegaRowUniqueQuotInput κ := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob g hg
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  obtain ⟨γ, hγ⟩ := h G L hset n f K hn hKc hf e t ht hKt hroot hglob htN g hg
  exact mem_normalizer_of_conj_centerQuotAction hset (by omega) hKc hf e ht hKt hglob.1.1.1
    hglob.1.2.1 htN hg γ hγ

end CFSG.SeitzReduction.SymplecticPilot
