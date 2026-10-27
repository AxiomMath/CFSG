module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall
open scoped Pointwise

theorem L34Config.toAConfig_aux_elemAbelian {G : Type} [Group G] {p : ℕ} {M A : Subgroup G}
    (h : IsElemAbelian p A) : IsElemAbelian p (A.subgroupOf M) := by
  obtain ⟨hc, hp⟩ := h
  haveI := hc
  refine ⟨inferInstance, fun x hx => ?_⟩
  have hx' : (x : G) ∈ A := hx
  apply Subtype.ext
  simpa using hp (x : G) hx'

theorem L34Config.toAConfig_aux_card {G : Type} [Group G] {M A : Subgroup G} (hA : A ≤ M) :
    Nat.card (A.subgroupOf M) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem L34Config.toAConfig_aux_mul_subset {G : Type} [Group G] {M A T : Subgroup G} (hA : A ≤ M)
    (hT : T ≤ M) (h : (A : Set G) * (T : Set G) ⊆ (T : Set G) * (A : Set G)) :
    ((A.subgroupOf M : Subgroup M) : Set M) * (T.subgroupOf M : Subgroup M) ⊆
      ((T.subgroupOf M : Subgroup M) : Set M) * (A.subgroupOf M : Subgroup M) := by
  rintro _ ⟨a, ha, t, ht, rfl⟩
  have hat : (a : G) * (t : G) ∈ (A : Set G) * (T : Set G) := ⟨a, ha, t, ht, rfl⟩
  obtain ⟨t₁, ht₁, a₁, ha₁, he⟩ := h hat
  refine ⟨⟨t₁, hT ht₁⟩, ht₁, ⟨a₁, hA ha₁⟩, ha₁, ?_⟩
  apply Subtype.ext
  exact he

theorem L34Config.toAConfig_aux_perm {G : Type} [Group G] {M A T : Subgroup G} (hA : A ≤ M)
    (hT : T ≤ M) (h : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)) :
    Permutable (A.subgroupOf M) (T.subgroupOf M) :=
  Set.Subset.antisymm (L34Config.toAConfig_aux_mul_subset hA hT h.subset)
    (L34Config.toAConfig_aux_mul_subset hT hA h.symm.subset)

theorem L34Config.toAConfig_aux_pCoreOf {G : Type} [Group G] {U M : Subgroup G} (hU : U ≤ M) (p : ℕ) :
    (pCoreOf p U).subgroupOf M = pCoreOf p (U.subgroupOf M) := by
  have hφ : CFSG.pCore p ↥U =
      (CFSG.pCore p ↥(U.subgroupOf M)).map (Subgroup.subgroupOfEquivOfLe hU).toMonoidHom :=
    (CFSG.pCore_map_iso p (Subgroup.subgroupOfEquivOfLe hU)).symm
  have hpc : pCoreOf p U = (CFSG.pCore p ↥U).map U.subtype := rfl
  ext ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, hpc, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [hφ, Subgroup.mem_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    refine Subgroup.mem_map.mpr ⟨w, hw, ?_⟩
    subst hwz
    apply Subtype.ext
    exact hzy
  · intro hmem
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hmem
    refine ⟨(Subgroup.subgroupOfEquivOfLe hU) w, ?_, ?_⟩
    · rw [hφ]
      exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    · have hv : ((w : ↥M) : G) = y := congrArg Subtype.val hwy
      exact hv

theorem L34Config.toAConfig_aux_core {G : Type} [Group G] {M A T R : Subgroup G} (hA : A ≤ M)
    (hT : T ≤ M) (h : R = pCoreOf 2 (A ⊔ T)) :
    R.subgroupOf M = pCoreOf 2 (A.subgroupOf M ⊔ T.subgroupOf M) := by
  rw [← Subgroup.subgroupOf_sup hA hT, ← L34Config.toAConfig_aux_pCoreOf (sup_le hA hT), h]

theorem L34Config.toAConfig_aux_maximal {G : Type} [Group G] {M A R : Subgroup G} (hA : A ≤ M)
    (hR : R ≤ M) (h : IsMaxInvariantTwo A R) :
    IsMaxInvariantTwo (A.subgroupOf M) (R.subgroupOf M) := by
  obtain ⟨h2, hn, hmax⟩ := h
  refine ⟨h2.comap_subtype, ?_, ?_⟩
  · rw [Subgroup.le_normalizer_iff]
    intro a ha x hx
    exact Subgroup.le_normalizer_iff.1 hn (a : G) ha (x : G) hx
  · intro S hS hSn hRS
    have hSM : IsPGroup 2 (S.map M.subtype) := hS.map _
    have hSn' : A ≤ Subgroup.normalizer ((S.map M.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      rintro a ha _ ⟨y, hy, rfl⟩
      have ha' : (⟨a, hA ha⟩ : M) ∈ A.subgroupOf M := ha
      exact ⟨_, Subgroup.le_normalizer_iff.1 hSn _ ha' y hy, rfl⟩
    have hRS' : R ≤ S.map M.subtype := fun x hx => ⟨⟨x, hR hx⟩, hRS hx, rfl⟩
    have hEq := hmax _ hSM hSn' hRS'
    calc S = (S.map M.subtype).subgroupOf M :=
          (Subgroup.comap_map_eq_self_of_injective M.subtype_injective S).symm
      _ = R.subgroupOf M := by rw [hEq]

theorem L34Config.toAConfig_aux_solvable {G : Type} [Group G] {M R H' : Subgroup G} (hR : R ≤ M)
    (hN : Subgroup.normalizer (R : Set G) ≤ H')
    (hs : Group.IsSolvable ↥(H' ⊓ M ⊓ Subgroup.normalizer (R : Set G))) :
    Group.IsSolvable ↥(Subgroup.normalizer ((R.subgroupOf M : Subgroup M) : Set M)) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hR]
  let f : ↥((Subgroup.normalizer (R : Set G)).subgroupOf M) →*
      ↥(H' ⊓ M ⊓ Subgroup.normalizer (R : Set G)) :=
    MonoidHom.codRestrict (M.subtype.comp ((Subgroup.normalizer (R : Set G)).subgroupOf M).subtype) _
      (fun x => ⟨⟨hN x.2, x.1.2⟩, x.2⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((x : M) : G) = ((y : M) : G) :=
      congrArg (fun z : ↥(H' ⊓ M ⊓ Subgroup.normalizer (R : Set G)) => (z : G)) hxy
    exact Subtype.ext (Subtype.ext h1)
  haveI := hs
  exact Group.isSolvable_of_isSolvable_injective hf

theorem L34Config.toAConfig_aux_transitive {G : Type} [Group G] {M A T : Subgroup G} (hT : T ≤ M)
    (h : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      ∃ t ∈ T ⊓ Subgroup.normalizer (A : Set G), t * a * t⁻¹ = b) :
    ∀ a ∈ A.subgroupOf M, a ≠ 1 → ∀ b ∈ A.subgroupOf M, b ≠ 1 →
      ∃ t ∈ T.subgroupOf M ⊓ Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M),
        t * a * t⁻¹ = b := by
  intro a ha ha1 b hb hb1
  have ha1' : (a : G) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  have hb1' : (b : G) ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  obtain ⟨t, ht, hta⟩ := h (a : G) ha ha1' (b : G) hb hb1'
  obtain ⟨htT, htN⟩ := Subgroup.mem_inf.1 ht
  exact ⟨⟨t, hT htT⟩, Subgroup.mem_inf.2 ⟨htT, Subgroup.le_normalizer_comap M.subtype htN⟩,
    Subtype.ext hta⟩

theorem L34Config.toAConfig_aux_quaternion {G : Type} [Group G] {M A T : Subgroup G} (hA : A ≤ M)
    (hT : T ≤ M) (h : HasQ8 (autInduced T A)) :
    HasQ8 (autInduced (T.subgroupOf M) (A.subgroupOf M)) := by
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := h
  let φ : ↥A ≃* ↥(A.subgroupOf M) := (Subgroup.subgroupOfEquivOfLe hA).symm
  let e : MulAut ↥A ≃* MulAut ↥(A.subgroupOf M) := MulAut.congr φ
  refine ⟨Q.map e.toMonoidHom, ?_,
    ⟨((Q.equivMapOfInjective e.toMonoidHom e.injective).symm).trans eQ⟩⟩
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 (hQ hσ)
  have htM : (t' : G) ∈ M := hT ht'
  refine Subgroup.mem_map.2 ⟨⟨⟨t', htM⟩, Subgroup.le_normalizer_comap M.subtype t'.2⟩, ht', ?_⟩
  ext x
  rfl

theorem L34Config.toAConfig {G : Type} [Group G] [Finite G] {M A T R H' : Subgroup G}
    (h : L34Config M A T R H') :
    AConfig (T.subgroupOf M) (R.subgroupOf M) (A.subgroupOf M) := by
  have hA : A ≤ M := h.le_M
  have hT : T ≤ M := h.sylow.le
  have hRAT : R ≤ A ⊔ T := by
    rw [h.core]
    exact Subgroup.map_subtype_le _
  have hR : R ≤ M := hRAT.trans (sup_le hA hT)
  exact
    { elemAbelian := L34Config.toAConfig_aux_elemAbelian h.elemAbelian
      card_eq := (L34Config.toAConfig_aux_card hA).trans h.card_eq
      perm := L34Config.toAConfig_aux_perm hA hT h.perm
      core := L34Config.toAConfig_aux_core hA hT h.core
      maximal := L34Config.toAConfig_aux_maximal hA hR h.maximal
      solvable := L34Config.toAConfig_aux_solvable hR h.normalizer_le h.solvable
      quaternion := L34Config.toAConfig_aux_quaternion hA hT h.quaternion
      transitive := L34Config.toAConfig_aux_transitive hT h.transitive }

end CFSG.LocalAnalysis.RankThreeUC.S15
