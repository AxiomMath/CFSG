module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotTransfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphGlobal

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect map_perfectCore
  perfectCore_eq_self_of_perfect)

section Transfer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem centralizerPerfectCore_nsTorusSp_le_nsGlobal {n : ℕ} (e : L ≃* StatedSp n K)
    (k : Fin n) : centralizerPerfectCore (modelToG e (nsTorusSp K k)) ≤ nsGlobal e := by
  rw [nsGlobal_def]
  exact le_iSup (fun i : Fin n => centralizerPerfectCore (modelToG e (nsTorusSp K i))) k

omit [Finite K] [CharP K 2] in
theorem map_conj_perfectCore_le_nsGlobal {n : ℕ} (e : L ≃* StatedSp n K)
    (hLS : L ≤ nsGlobal e) (γ : MulAut (nsGlobal e ⧸ center (nsGlobal e))) {g l : G}
    (hlL : l ∈ L) {σ : K ≃+* K}
    (hkey : ∀ x : StatedSp n K,
      ∃ hu : g⁻¹ * (l * ((e.symm (fieldSp n K σ x) : L) : G) * l⁻¹) * g ∈ nsGlobal e,
        γ (QuotientGroup.mk' (center (nsGlobal e)) (Subgroup.inclusion hLS (e.symm x))) =
          QuotientGroup.mk' (center (nsGlobal e)) ⟨_, hu⟩) (k : Fin n) :
    (perfectCore ((((((centralizerPerfectCore (modelToG e (nsTorusSp K k))).subgroupOf
        (nsGlobal e)).map (QuotientGroup.mk' (center (nsGlobal e)))).map γ.toMonoidHom).comap
          (QuotientGroup.mk' (center (nsGlobal e)))))).map
        ((MulAut.conj g).toMonoidHom.comp (nsGlobal e).subtype) ≤ nsGlobal e := by
  set P := centralizerPerfectCore (modelToG e (nsTorusSp K k)) with hPdef
  have hPle : P ≤ nsGlobal e := centralizerPerfectCore_nsTorusSp_le_nsGlobal e k
  set R := perfectCore ((((P.subgroupOf (nsGlobal e)).map
      (QuotientGroup.mk' (center (nsGlobal e)))).map γ.toMonoidHom).comap
        (QuotientGroup.mk' (center (nsGlobal e)))) with hR
  have hRperf : ⁅R, R⁆ = R := perfectCore_perfect _
  have hRmap : R.map (QuotientGroup.mk' (center (nsGlobal e))) =
      ((P.subgroupOf (nsGlobal e)).map
        (QuotientGroup.mk' (center (nsGlobal e)))).map γ.toMonoidHom := by
    rw [hR, map_perfectCore, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _)]
    refine perfectCore_eq_self_of_perfect ?_
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_subgroupOf_eq hPle (F4Pilot.commutator_centralizerPerfectCore _)]
  have hlS : l ∈ nsGlobal e := hLS hlL
  set T₀ : Subgroup G := modelToG e (nsTorusSp K k) with hT₀
  have hcent : ∀ y ∈ R, ∀ x ∈ nsTorusSp K k,
      (l⁻¹ * (g * ((y : nsGlobal e) : G) * g⁻¹) * l) * ((e.symm x : L) : G) =
        ((e.symm x : L) : G) * (l⁻¹ * (g * ((y : nsGlobal e) : G) * g⁻¹) * l) := by
    intro y hy x hx
    have hσ : fieldSp n K σ x = x := fieldSp_eq_self_of_mem_nsTorusSp σ hx
    obtain ⟨hu, hγu⟩ := hkey x
    have hmod : ∀ z ∈ R, (QuotientGroup.mk (z * ⟨_, hu⟩) : nsGlobal e ⧸ center (nsGlobal e)) =
        QuotientGroup.mk (⟨_, hu⟩ * z) := by
      intro z hz
      have hz' : QuotientGroup.mk' (center (nsGlobal e)) z ∈
          R.map (QuotientGroup.mk' (center (nsGlobal e))) := ⟨z, hz, rfl⟩
      rw [hRmap] at hz'
      obtain ⟨_, ⟨p, hp, rfl⟩, hpz⟩ := hz'
      have hpP : ((p : nsGlobal e) : G) ∈ P := hp
      have hpc : ((p : nsGlobal e) : G) * ((e.symm x : L) : G) =
          ((e.symm x : L) : G) * ((p : nsGlobal e) : G) :=
        (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ hpP) _
          ((mem_modelToG e).2 ⟨_, hx, rfl⟩)).symm
      have hpc' : p * Subgroup.inclusion hLS (e.symm x) =
          Subgroup.inclusion hLS (e.symm x) * p := Subtype.ext hpc
      have h1 := congrArg (fun v => γ (QuotientGroup.mk' (center (nsGlobal e)) v)) hpc'
      simp only [map_mul] at h1
      rw [hγu] at h1
      change γ (QuotientGroup.mk' (center (nsGlobal e)) p) = QuotientGroup.mk' _ z at hpz
      rw [hpz] at h1
      change QuotientGroup.mk' _ z * QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _ *
        QuotientGroup.mk' _ z at h1
      rw [← map_mul, ← map_mul] at h1
      exact h1
    have hc := commute_of_perfect_of_mk_commute hRperf hmod y hy
    have hc' : ((y : nsGlobal e) : G) *
        (g⁻¹ * (l * ((e.symm (fieldSp n K σ x)) : L) * l⁻¹) * g) =
        (g⁻¹ * (l * ((e.symm (fieldSp n K σ x)) : L) * l⁻¹) * g) *
          ((y : nsGlobal e) : G) := congrArg Subtype.val hc
    rw [hσ] at hc'
    calc (l⁻¹ * (g * ((y : nsGlobal e) : G) * g⁻¹) * l) * ((e.symm x : L) : G) =
        l⁻¹ * g * (((y : nsGlobal e) : G) * (g⁻¹ * (l * ((e.symm x : L) : G) * l⁻¹) * g)) *
          g⁻¹ * l := by group
      _ = l⁻¹ * g * ((g⁻¹ * (l * ((e.symm x : L) : G) * l⁻¹) * g) * ((y : nsGlobal e) : G)) *
          g⁻¹ * l := by rw [hc']
      _ = ((e.symm x : L) : G) * (l⁻¹ * (g * ((y : nsGlobal e) : G) * g⁻¹) * l) := by group
  set Q : Subgroup G := (R.map ((MulAut.conj g).toMonoidHom.comp (nsGlobal e).subtype)).map
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
  have hQle : Q ≤ P := F4Pilot.le_centralizerPerfectCore hQperf hQT
  rintro _ ⟨y, hy, rfl⟩
  have hmem : l⁻¹ * (g * ((y : nsGlobal e) : G) * g⁻¹) * l ∈ nsGlobal e := by
    refine hPle (hQle ⟨_, ⟨y, hy, rfl⟩, ?_⟩)
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Subgroup.coe_subtype, inv_inv]
  have h2 : ((MulAut.conj g).toMonoidHom.comp (nsGlobal e).subtype) y =
      l * (l⁻¹ * (g * ((y : nsGlobal e) : G) * g⁻¹) * l) * l⁻¹ := by
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Subgroup.coe_subtype]
    group
  rw [h2]
  exact mul_mem (mul_mem hlS hmem) (inv_mem hlS)

theorem mem_normalizer_nsGlobal_of_conj_centerQuotAction (hset : SeitzSetting G L) {m : ℕ}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hperf : Group.IsPerfect (nsGlobal e)) (hZ : Odd (Nat.card (center (nsGlobal e))))
    (htN : t ∈ normalizer (nsGlobal e : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G))
    (γ : MulAut (nsGlobal e ⧸ center (nsGlobal e)))
    (hγ : γ * centerQuotAction (nsGlobal e) ⟨t, htN⟩ =
      centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩ * γ) :
    g ∈ normalizer (nsGlobal e : Set G) := by
  have hLS : L ≤ nsGlobal e := le_nsGlobal hK hm e
  obtain ⟨l, σ, hlL, hkey⟩ :=
    exists_conj_fieldSp_of_quot hset (by omega) e ht hKt hLS hZ htN hg γ hγ
  set c : nsGlobal e →* G := (MulAut.conj g).toMonoidHom.comp (nsGlobal e).subtype with hc
  set P : Fin (m + 1) → Subgroup G := fun k =>
    centralizerPerfectCore (modelToG e (nsTorusSp K k)) with hPdef
  set R : Fin (m + 1) → Subgroup (nsGlobal e) := fun k =>
    perfectCore (((((P k).subgroupOf (nsGlobal e)).map
      (QuotientGroup.mk' (center (nsGlobal e)))).map γ.toMonoidHom).comap
        (QuotientGroup.mk' (center (nsGlobal e)))) with hR
  have hRle : ∀ k, (R k).map c ≤ nsGlobal e := fun k =>
    map_conj_perfectCore_le_nsGlobal e hLS γ hlL hkey k
  have hPle : ∀ k, P k ≤ nsGlobal e := fun k => centralizerPerfectCore_nsTorusSp_le_nsGlobal e k
  have hRmap : ∀ k, (R k).map (QuotientGroup.mk' (center (nsGlobal e))) =
      (((P k).subgroupOf (nsGlobal e)).map
        (QuotientGroup.mk' (center (nsGlobal e)))).map γ.toMonoidHom := by
    intro k
    rw [hR, map_perfectCore, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _)]
    refine perfectCore_eq_self_of_perfect ?_
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_subgroupOf_eq (hPle k) (F4Pilot.commutator_centralizerPerfectCore _)]
  have hPsup : ⨆ k, (P k).subgroupOf (nsGlobal e) = ⊤ := by
    apply Subgroup.map_injective (nsGlobal e).subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp only [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hPle _)]
    exact (nsGlobal_def e).symm
  have hRsup : ⨆ k, R k = ⊤ := by
    refine eq_top_of_map_mk_eq_top ?_
    rw [Subgroup.map_iSup, iSup_congr hRmap, ← Subgroup.map_iSup, ← Subgroup.map_iSup, hPsup,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _),
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 γ.surjective]
  have hconj : ∀ y ∈ nsGlobal e, g * y * g⁻¹ ∈ nsGlobal e := by
    intro y hy
    have h1 : (⟨y, hy⟩ : nsGlobal e) ∈ ⨆ k, R k := by rw [hRsup]; exact mem_top _
    have h2 : c ⟨y, hy⟩ ∈ (⨆ k, R k).map c := ⟨_, h1, rfl⟩
    rw [Subgroup.map_iSup] at h2
    exact (iSup_le hRle) h2
  have hmap : (nsGlobal e).map (MulAut.conj g).toMonoidHom ≤ nsGlobal e := by
    rintro _ ⟨y, hy, rfl⟩
    exact hconj y hy
  have hcard : Nat.card ((nsGlobal e).map (MulAut.conj g).toMonoidHom) =
      Nat.card (nsGlobal e) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : (nsGlobal e).map (MulAut.conj g).toMonoidHom = nsGlobal e :=
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
