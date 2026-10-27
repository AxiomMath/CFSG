module

public import CFSG.CGT.Foote82.BlocksCommute
public import CFSG.CGT.PushingUpLit.ThreeFromEightOneCore
import CFSG.GroupTheory.ConjugatePairSubnormality

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.ThreeFromEight
open scoped commutatorElement

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem isFooteBlock_map {H J : Subgroup G} (hJ : IsFooteBlock H J) (φ : G ≃* G') :
    IsFooteBlock (H.map φ.toMonoidHom) (J.map φ.toMonoidHom) := by
  have e : J ≃* J.map φ.toMonoidHom := J.equivMapOfInjective φ.toMonoidHom φ.injective
  refine ⟨Subgroup.map_mono hJ.le, hJ.subnormal.map φ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro N _ hN
    have hmap : (N.comap e.toMonoidHom).map e.toMonoidHom = N :=
      Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N
    have h2 : IsPGroup 2 (J ⧸ N.comap e.toMonoidHom) :=
      hN.of_equiv (QuotientGroup.congr _ _ e hmap).symm
    rw [← hmap, hJ.residual _ h2, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  · have e' := QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e'.symm hJ.quasisimple
  · rw [← blockZ_map φ J, ← blockU_map φ J]
    exact (Subgroup.map_lt_map_iff_of_injective (f := φ.toMonoidHom) φ.injective).mpr
      hJ.chief.1
  · intro W hZW hWU hLW
    obtain ⟨W₀, rfl⟩ : ∃ W₀ : Subgroup G, W₀.map φ.toMonoidHom = W :=
      ⟨W.map φ.symm.toMonoidHom, by
        rw [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G' from
          MonoidHom.ext φ.apply_symm_apply, Subgroup.map_id]⟩
    rw [← blockZ_map, Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective]
      at hZW
    rw [← blockU_map, Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective]
      at hWU
    rw [← Subgroup.map_equiv_normalizer_eq,
      Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective] at hLW
    rcases hJ.chief.2 W₀ hZW hWU hLW with rfl | rfl
    · exact Or.inl (blockZ_map φ J)
    · exact Or.inr (blockU_map φ J)

end Transport

section Conversions

variable {G : Type} [Group G]

private theorem isMaximalTwoLocal_of_glb {M : Subgroup G} (hM : GLBIsMaxTwoLocal M) :
    CFSG.IsMaximalTwoLocal M :=
  ⟨hM.1, fun H hlt hH => (ne_of_gt hlt) (hM.2 H hH hlt.le)⟩

private theorem glb_of_isMaximalTwoLocal {M : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M) :
    GLBIsMaxTwoLocal M :=
  ⟨hM.1, fun X hX hMX => by
    by_contra hne
    exact hM.2 X (lt_of_le_of_ne hMX (Ne.symm hne)) hX⟩

end Conversions

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_unique_maximalTwoLocal_of_comm (𝔛 : Set (Subgroup G))
    (hconj : ∀ Z ∈ 𝔛, ∀ g : G, CFSG.conjugate Z g ∈ 𝔛)
    (h81 : ∀ Z ∈ 𝔛, ∀ N : Subgroup G, N ∈ CFSG.maximalTwoLocalsContaining (Z : Set G) →
      (Z.subgroupOf N).IsSubnormal)
    (comm : ∀ N : Subgroup G, CFSG.IsMaximalTwoLocal N → ∀ Y ∈ 𝔛, ∀ Z ∈ 𝔛, Y ≤ N → Z ≤ N →
      Y ≠ Z → ⁅Y, Z⁆ = ⊥)
    {X : Subgroup G} (hXm : X ∈ 𝔛) (hOne : oTwoIn X ≠ ⊥) :
    ∃ M : Subgroup G, CFSG.maximalTwoLocalsContaining (X : Set G) = {M} ∧
      (X.subgroupOf M).IsSubnormal := by
  obtain ⟨N₀, hN₀, hN₀max⟩ := exists_isMaximalTwoLocal_ge
    (isPLocal_normalizer_of_isPGroup (isPGroup_oTwoIn X) hOne)
  have hNX₀ : Subgroup.normalizer (X : Set G) ≤ N₀ :=
    (normalizer_le_normalizer_oTwoIn X).trans hN₀
  have hXN₀ : N₀ ∈ CFSG.maximalTwoLocalsContaining (X : Set G) :=
    ⟨hN₀max, fun x hx => hNX₀ (Subgroup.le_normalizer hx)⟩
  have key : ∀ N ∈ CFSG.maximalTwoLocalsContaining (X : Set G),
      N = setNormalizer (memberSet 𝔛 (Subgroup.normalizer (X : Set G))) := by
    rintro N ⟨hNmax, hXN'⟩
    have hXN : X ≤ N := fun x hx => hXN' hx
    have hsub : ∀ Z ∈ memberSet 𝔛 N, (Z.subgroupOf N).IsSubnormal :=
      fun Z hZ => h81 Z hZ.1 N ⟨hNmax, fun x hx => hZ.2 hx⟩
    have hOle : ∀ Z ∈ memberSet 𝔛 N, oTwoIn Z ≤ oTwoIn N :=
      fun Z hZ => oTwoIn_le_oTwoIn_of_isSubnormal hZ.2 (hsub Z hZ)
    have hΔΓ : memberSet 𝔛 N ⊆ memberSet 𝔛 (Subgroup.normalizer (X : Set G)) := by
      intro Z hZ
      refine ⟨hZ.1, ?_⟩
      by_cases hZX : Z = X
      · rw [hZX]
        exact Subgroup.le_normalizer
      · have hc : ⁅Z, X⁆ = ⊥ := comm N hNmax Z hZ.1 X hXm hZ.2 hXN hZX
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc).trans
          (Subgroup.centralizer_le_normalizer _)
    have hd : setNormalizer (memberSet 𝔛 N) = N :=
      setNormalizer_eq_of_isMaximalTwoLocal hNmax (le_setNormalizer_memberSet hconj N) hOle
        ⟨X, ⟨hXm, hXN⟩, hOne⟩
    have hΓΔ : memberSet 𝔛 (Subgroup.normalizer (X : Set G)) ⊆ memberSet 𝔛 N := by
      intro Z hZ
      refine ⟨hZ.1, ?_⟩
      have hnz : ∀ Z₁ ∈ memberSet 𝔛 N, Z ≤ Subgroup.normalizer (Z₁ : Set G) := by
        intro Z₁ hZ₁
        by_cases hZZ : Z = Z₁
        · rw [← hZZ]
          exact Subgroup.le_normalizer
        · have hc : ⁅Z, Z₁⁆ = ⊥ := comm N₀ hN₀max Z hZ.1 Z₁ hZ₁.1 (hZ.2.trans hNX₀)
            ((hΔΓ hZ₁).2.trans hNX₀) hZZ
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc).trans
            (Subgroup.centralizer_le_normalizer _)
      have hZs : Z ≤ setNormalizer (memberSet 𝔛 N) := by
        intro z hz Z₂
        refine ⟨fun hZ₂ => ?_, fun hZ₂ => ?_⟩
        · rwa [conjugate_eq_self_of_mem_normalizer (hnz Z₂ hZ₂ hz)]
        · have h1 := conjugate_eq_self_of_mem_normalizer (hnz _ hZ₂ (inv_mem hz))
          rw [CFSG.GroupTheory.conjugate_conjugate, mul_inv_cancel, conjugate_one] at h1
          rw [h1]
          exact hZ₂
      rw [hd] at hZs
      exact hZs
    rw [Set.Subset.antisymm hΓΔ hΔΓ, hd]
  refine ⟨N₀, Set.eq_singleton_iff_unique_mem.2 ⟨hXN₀, fun N hN => ?_⟩,
    h81 X hXm N₀ hXN₀⟩
  exact (key N hN).trans (key N₀ hXN₀).symm

theorem ef2 {X K : Subgroup G} (hK : IsFooteBlock X K)
    (hall : ∀ N : Subgroup G, GLBIsMaxTwoLocal N → K ≤ N → IsSubnormal K N) :
    ∃ M : Subgroup G, GLBIsMaxTwoLocal M ∧ IsFooteBlock M K ∧
      ∀ M' : Subgroup G, GLBIsMaxTwoLocal M' → K ≤ M' → M' = M := by
  have hOne : oTwoIn K ≠ ⊥ := by
    intro h
    have hQ : blockQ K = ⊥ := h
    have hU : blockU K = ⊥ := by
      rw [blockU, hQ, Subgroup.commutator_bot_left]
    have hlt := hK.chief.1
    rw [hU] at hlt
    exact not_lt_bot hlt
  have hfb : ∀ (a : G) (N : Subgroup G), CFSG.IsMaximalTwoLocal N →
      CFSG.conjugate K a ≤ N → IsFooteBlock N (CFSG.conjugate K a) := by
    intro a N hN hZN
    have hN'max : CFSG.IsMaximalTwoLocal (CFSG.conjugate N a⁻¹) := by
      have h1 := isMaximalTwoLocal_map_conj hN a
      rwa [← conjugate_inv_eq_map] at h1
    have hKN' : K ≤ CFSG.conjugate N a⁻¹ := by
      intro x hx
      have h1 : a⁻¹ * x * a⁻¹⁻¹ ∈ CFSG.conjugate K a := by
        rw [mem_conjugate_iff]
        simpa [mul_assoc] using hx
      exact mem_conjugate_iff.2 (hZN h1)
    have hKsub : IsSubnormal K (CFSG.conjugate N a⁻¹) :=
      hall _ (glb_of_isMaximalTwoLocal hN'max) hKN'
    have h2 := isFooteBlock_map (⟨hKN', hKsub, hK.residual, hK.quasisimple, hK.chief⟩ :
      IsFooteBlock (CFSG.conjugate N a⁻¹) K) (MulAut.conj a⁻¹)
    have h3 : CFSG.conjugate (CFSG.conjugate N a⁻¹) a = N := by
      rw [CFSG.GroupTheory.conjugate_conjugate, inv_mul_cancel, conjugate_one]
    change IsFooteBlock (CFSG.conjugate (CFSG.conjugate N a⁻¹) a) (CFSG.conjugate K a) at h2
    rwa [h3] at h2
  let 𝔛 : Set (Subgroup G) := {Z | ∃ g : G, Z = CFSG.conjugate K g}
  have hXm : K ∈ 𝔛 := ⟨1, (conjugate_one K).symm⟩
  have hconj : ∀ Z ∈ 𝔛, ∀ g : G, CFSG.conjugate Z g ∈ 𝔛 := by
    rintro Z ⟨a, rfl⟩ g
    exact ⟨a * g, CFSG.GroupTheory.conjugate_conjugate K a g⟩
  have h81 : ∀ Z ∈ 𝔛, ∀ N : Subgroup G, N ∈ CFSG.maximalTwoLocalsContaining (Z : Set G) →
      (Z.subgroupOf N).IsSubnormal := by
    rintro Z ⟨a, rfl⟩ N ⟨hN, hZN⟩
    have hle : CFSG.conjugate K a ≤ N := fun x hx => hZN hx
    exact (IsSubnormal.iff_subgroupOf hle).mp (hfb a N hN hle).subnormal
  have comm : ∀ N : Subgroup G, CFSG.IsMaximalTwoLocal N → ∀ Y ∈ 𝔛, ∀ Z ∈ 𝔛, Y ≤ N → Z ≤ N →
      Y ≠ Z → ⁅Y, Z⁆ = ⊥ := by
    rintro N hN Y ⟨a, rfl⟩ Z ⟨b, rfl⟩ hY hZ hne
    exact blocks_commute (hfb a N hN hY) (hfb b N hN hZ) hne
  obtain ⟨M, hM1, hM2⟩ := exists_unique_maximalTwoLocal_of_comm 𝔛 hconj h81 comm hXm hOne
  have hMmem : M ∈ CFSG.maximalTwoLocalsContaining (K : Set G) := by
    rw [hM1]
    exact Set.mem_singleton M
  have hKM : K ≤ M := fun x hx => hMmem.2 hx
  refine ⟨M, glb_of_isMaximalTwoLocal hMmem.1,
    ⟨hKM, (IsSubnormal.iff_subgroupOf hKM).mpr hM2, hK.residual, hK.quasisimple, hK.chief⟩,
    fun M' hM' hKM' => ?_⟩
  have hM'mem : M' ∈ CFSG.maximalTwoLocalsContaining (K : Set G) :=
    ⟨isMaximalTwoLocal_of_glb hM', fun x hx => hKM' hx⟩
  rw [hM1] at hM'mem
  exact hM'mem

end Main

end CFSG.CGT.Foote82
