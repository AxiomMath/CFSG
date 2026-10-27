module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldCT

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)

section Global

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem le_nsGlobal {m : ℕ} (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) :
    L ≤ nsGlobal e := by
  have h : modelToG e (⊤ : Subgroup (StatedSp (m + 1) K)) ≤ nsGlobal e := by
    rw [← iSup_spBlock_compl_singleton_eq_top (F := K) (by omega : 3 ≤ m + 1),
      UnitaryPilot.modelToG_iSup, nsGlobal_def]
    refine iSup_mono fun k => ?_
    rw [spBlock_compl_singleton]
    exact modelToG_complSp_le_centralizerPerfectCore_nsTorusSp hK hm e k
  rwa [UnitaryPilot.modelToG_top e] at h

end Global

section Field

variable {K : Type} [Field K] {n : ℕ}

theorem fieldSp_eq_self_of_mem_nsTorusSp (σ : K ≃+* K) {k : Fin n} {x : StatedSp n K}
    (hx : x ∈ nsTorusSp K k) : fieldSp n K σ x = x := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
  rw [map_zpow, F4Pilot.fieldSp_eq_statedSpMap, ← spFieldMap_eq_statedSpMap, spFieldMap_nsElt]

end Field

section Transfer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem le_nsGlobal_of_injective_commute (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (φ : nsGlobal e →* G) (hφ : Function.Injective φ)
    (hφt : ∀ x : nsGlobal e, (x : G) * t = t * x → φ x * t = t * φ x) :
    φ.range ≤ nsGlobal e := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hLS : L ≤ nsGlobal e := le_nsGlobal hK hm e
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega : 3 ≤ m + 1) e)
  have hSpP : Group.IsPerfect (StatedSp (m + 1) K) := isPerfect_statedSp_of_charTwo (by omega)
  have hLP : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hLsP : Group.IsPerfect (L.subgroupOf (nsGlobal e)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLS).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hLφP : Group.IsPerfect ((L.subgroupOf (nsGlobal e)).map φ) :=
    Group.IsPerfect.ofSurjective (f := φ.subgroupMap _) (φ.subgroupMap_surjective _)
  have hLφt : (L.subgroupOf (nsGlobal e)).map φ ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    refine hφt x ?_
    have hx' : (x : G) ∈ L := hx
    exact mem_centralizer_iff.1 htC (x : G) hx'
  have hLφL : (L.subgroupOf (nsGlobal e)).map φ ≤ L :=
    std_perfect_le hset.standardSetting hOut htC ht (Subgroup.isPerfect_iff.mp hLφP) hLφt
  let α : L →* L :=
    { toFun := fun x => ⟨φ ⟨x, hLS x.2⟩, hLφL ⟨⟨x, hLS x.2⟩, x.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        change φ ⟨1, _⟩ = 1
        exact φ.map_one
      map_mul' := fun x y => by
        apply Subtype.ext
        change φ (⟨(x : G), hLS x.2⟩ * ⟨(y : G), hLS y.2⟩) = φ ⟨x, _⟩ * φ ⟨y, _⟩
        exact φ.map_mul _ _ }
  have hαinj : Function.Injective α := by
    intro x y hxy
    have h1 : φ ⟨x, hLS x.2⟩ = φ ⟨y, hLS y.2⟩ := congrArg Subtype.val hxy
    have h2 := congrArg Subtype.val (hφ h1)
    exact Subtype.ext h2
  let αE : L ≃* L := MulEquiv.ofBijective α hαinj.bijective_of_finite
  obtain ⟨s, σ, hβ⟩ := exists_eq_conj_mul_fieldSp (by omega : 3 ≤ m + 1)
    ((e.symm.trans αE).trans e)
  set l : G := ((e.symm s : L) : G) with hl
  have hlS : l ∈ nsGlobal e := hLS (e.symm s).2
  have hkey : ∀ x : StatedSp (m + 1) K, φ ⟨((e.symm x : L) : G), hLS (e.symm x).2⟩ =
      l * ((e.symm (fieldSp (m + 1) K σ x) : L) : G) * l⁻¹ := by
    intro x
    have h1 := congrArg (fun γ : MulAut (StatedSp (m + 1) K) => γ x) hβ
    simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.conj_apply] at h1
    have h2 : αE (e.symm x) = e.symm (s * fieldSp (m + 1) K σ x * s⁻¹) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    have h3 := congrArg Subtype.val h2
    rw [map_mul, map_mul, map_inv] at h3
    exact h3
  have hpiece : ∀ (k : Fin (m + 1)) (y : G)
      (hy : y ∈ centralizerPerfectCore (modelToG e (nsTorusSp K k))),
      ∀ hyS : y ∈ nsGlobal e, φ ⟨y, hyS⟩ ∈ nsGlobal e := by
    intro k y hy hyS
    set P := centralizerPerfectCore (modelToG e (nsTorusSp K k)) with hP
    have hPle : P ≤ nsGlobal e := by
      rw [nsGlobal_def]
      exact le_iSup (fun i : Fin (m + 1) =>
        centralizerPerfectCore (modelToG e (nsTorusSp K i))) k
    set Q : Subgroup G := ((P.subgroupOf (nsGlobal e)).map φ).map (MulAut.conj l⁻¹).toMonoidHom
      with hQ
    have hPP : Group.IsPerfect P :=
      Subgroup.isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore _)
    have hPsP : Group.IsPerfect (P.subgroupOf (nsGlobal e)) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPle).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have hPφP : Group.IsPerfect ((P.subgroupOf (nsGlobal e)).map φ) :=
      Group.IsPerfect.ofSurjective (f := φ.subgroupMap _) (φ.subgroupMap_surjective _)
    have hQP : Group.IsPerfect Q :=
      Group.IsPerfect.ofSurjective (f := (MulAut.conj l⁻¹).toMonoidHom.subgroupMap _)
        (MonoidHom.subgroupMap_surjective _ _)
    have hQc : Q ≤ centralizer (modelToG e (nsTorusSp K k) : Set G) := by
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hz' : (z : G) ∈ P := hz
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hh
      have hk := hkey x
      rw [fieldSp_eq_self_of_mem_nsTorusSp σ hx] at hk
      have hzc : (z : G) * ((e.symm x : L) : G) = ((e.symm x : L) : G) * (z : G) := by
        have := mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ hz')
          _ ((mem_modelToG e).2 ⟨_, hx, rfl⟩)
        exact this.symm
      have hφc : φ z * φ ⟨((e.symm x : L) : G), hLS (e.symm _).2⟩ =
          φ ⟨((e.symm x : L) : G), hLS (e.symm _).2⟩ * φ z := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hzc
      rw [hk] at hφc
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc ((e.symm x : L) : G) * (l⁻¹ * φ z * l) =
          l⁻¹ * ((l * ((e.symm x : L) : G) * l⁻¹) * φ z) * l := by group
        _ = l⁻¹ * (φ z * (l * ((e.symm x : L) : G) * l⁻¹)) * l := by rw [hφc]
        _ = l⁻¹ * φ z * l * ((e.symm x : L) : G) := by group
    have hQle : Q ≤ P :=
      F4Pilot.le_centralizerPerfectCore (Subgroup.isPerfect_iff.mp hQP) hQc
    have hmem : l⁻¹ * φ ⟨y, hyS⟩ * l ∈ Q := by
      refine ⟨φ ⟨y, hyS⟩, ⟨⟨y, hyS⟩, hy, rfl⟩, ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h1 : l⁻¹ * φ ⟨y, hyS⟩ * l ∈ nsGlobal e := hPle (hQle hmem)
    have h2 : φ ⟨y, hyS⟩ = l * (l⁻¹ * φ ⟨y, hyS⟩ * l) * l⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hlS h1) (inv_mem hlS)
  have hall : nsGlobal e ≤ ((nsGlobal e).comap φ).map (nsGlobal e).subtype := by
    conv_lhs => rw [nsGlobal_def]
    refine iSup_le fun k => ?_
    intro y hy
    have hyS : y ∈ nsGlobal e := by
      rw [nsGlobal_def]
      exact le_iSup (fun i : Fin (m + 1) =>
        centralizerPerfectCore (modelToG e (nsTorusSp K i))) k hy
    exact ⟨⟨y, hyS⟩, hpiece k y hy hyS, rfl⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨a, ha, haz⟩ := hall z.2
  have : a = z := Subtype.ext haz
  rw [← this]
  exact ha

theorem mem_normalizer_nsGlobal_of_conj_mulAut (hset : SeitzSetting G L) {m : ℕ}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (htN : t ∈ normalizer (nsGlobal e : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)) (β : MulAut (nsGlobal e))
    (hβ : β * (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
      (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ * β) :
    g ∈ normalizer (nsGlobal e : Set G) := by
  let φ : (nsGlobal e) →* G :=
    (MulAut.conj g).toMonoidHom.comp ((nsGlobal e).subtype.comp β.toMonoidHom)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : g * ((β x : (nsGlobal e)) : G) * g⁻¹ = g * ((β y : (nsGlobal e)) : G) * g⁻¹ := hxy
    have h2 : ((β x : (nsGlobal e)) : G) = ((β y : (nsGlobal e)) : G) := by
      have := congrArg (fun z => g⁻¹ * z * g) h1
      simpa [mul_assoc] using this
    exact β.injective (Subtype.ext h2)
  have hφt : ∀ x : (nsGlobal e), (x : G) * t = t * x → φ x * t = t * φ x := by
    intro x hx
    have hfix : (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ x = x := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * (x : G) * t⁻¹ = x
      rw [← hx, mul_inv_cancel_right]
    have h1 := congrArg (fun γ : MulAut (nsGlobal e) => γ x) hβ
    simp only [MulAut.mul_apply] at h1
    rw [hfix] at h1
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
    set b : G := ((β x : (nsGlobal e)) : G) with hb
    change b = (g⁻¹ * t * g) * b * (g⁻¹ * t * g)⁻¹ at h2
    change g * b * g⁻¹ * t = t * (g * b * g⁻¹)
    have h3 : b * (g⁻¹ * t * g) = (g⁻¹ * t * g) * b := by
      calc b * (g⁻¹ * t * g) = ((g⁻¹ * t * g) * b * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by
            rw [← h2]
        _ = (g⁻¹ * t * g) * b := by group
    calc g * b * g⁻¹ * t = g * (b * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * b) * g⁻¹ := by rw [h3]
      _ = t * (g * b * g⁻¹) := by group
  have hle := le_nsGlobal_of_injective_commute hset hK hm e ht hKt φ hφ hφt
  have hconj : ∀ y ∈ (nsGlobal e), g * y * g⁻¹ ∈ (nsGlobal e) := by
    intro y hy
    refine hle ⟨β.symm ⟨y, hy⟩, ?_⟩
    change g * ((β (β.symm ⟨y, hy⟩) : (nsGlobal e)) : G) * g⁻¹ = g * y * g⁻¹
    rw [MulEquiv.apply_symm_apply]
  have hmap : (nsGlobal e).map (MulAut.conj g).toMonoidHom ≤ (nsGlobal e) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hconj y hy
  have hcard : Nat.card ((nsGlobal e).map (MulAut.conj g).toMonoidHom) = Nat.card (nsGlobal e) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : (nsGlobal e).map (MulAut.conj g).toMonoidHom = (nsGlobal e) :=
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

end CFSG.SeitzReduction.SymplecticPilot
