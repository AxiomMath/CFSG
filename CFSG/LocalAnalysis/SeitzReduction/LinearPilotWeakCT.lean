module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTBlocks
public import CFSG.ClassicalInvolution.WeakCT.Coherent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAlignImages

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open scoped MatrixGroups

section Pair

variable {G : Type*} [Group G] {L : Subgroup G} {m : ℕ} {K : Type*} [Field K] {F : Type}
  [Field F] {e : L ≃* LinearFlag.projectiveSL (m + 1) K} {t : G} {ι : K →+* F} {σ : F ≃+* F}
  {X : Subgroup G} {N : Finset (Fin (m + 1))}

theorem map_conj_one_inv_eq (H : Subgroup SL(3, F)) :
    H.map (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = H := by
  ext x
  simp

theorem exists_theta_of_fieldNeighbourParam [Finite G] [Finite F]
    (P : FieldNeighbourParam e t ι σ X N) (i j : Fin m) (hj : (j : ℕ) = i + 1)
    (hN : ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ} ⊆ N)
    {k : Fin (m + 1)} (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1) (hF : 4 ≤ Nat.card F)
    (hX : X ≤ modelToG e (blockTorus (K := K)
      (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}))) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧
      (CFSG.ClassicalInvolution.WeakCT.B12 F).map θ =
        pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∧
      (CFSG.ClassicalInvolution.WeakCT.B23 F).map θ =
        pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1))) ∧
      θ.range = pieceCore e
        (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}) := by
  have h : (i : ℕ) + 1 < m := by have := j.isLt; omega
  let β : SL(3, F) →* blockSpecialLinear (K := F) N :=
    (CFSG.ClassicalInvolution.WeakCT.blockSL3 F m i h).codRestrict (blockSpecialLinear N)
      (fun A => blockSpecialLinear_mono hN (range_blockSL3_le m i j hj h ⟨A, rfl⟩))
  have hβ : ∀ A, ((β A : blockSpecialLinear (K := F) N) : SL(m + 1, F)) =
      CFSG.ClassicalInvolution.WeakCT.blockSL3 F m i h A := fun A => rfl
  have hβinj : Function.Injective β := fun A B hAB =>
    CFSG.ClassicalInvolution.WeakCT.blockSL3_injective m i h (by rw [← hβ, ← hβ, hAB])
  have hmapβ : ∀ (H : Subgroup SL(3, F)) (I : Finset (Fin (m + 1))),
      H.map (CFSG.ClassicalInvolution.WeakCT.blockSL3 F m i h) = blockSpecialLinear (K := F) I →
      H.map β = (blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N) := by
    intro H I hHI
    ext x
    rw [mem_map, mem_subgroupOf, ← hHI, mem_map]
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, hAx⟩
      exact ⟨A, hA, Subtype.ext hAx⟩
  have hpiece : ∀ I : Finset (Fin (m + 1)),
      I ⊆ ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ} → I.card = 2 →
      pieceCore e I =
        ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map P.Φ :=
    fun I hIS hI2 => P.pieceCore_eq_map_of_notMem (hIS.trans hN) hI2.ge hk hκ hF
      (hX.trans (modelToG_mono e (blockTorus_anti hIS)))
  refine ⟨P.Φ.comp β, ?_, ?_, ?_, ?_⟩
  · intro A hA
    have hz : β A ∈ center (blockSpecialLinear (K := F) N) := P.ker_le hA
    rw [mem_center_iff] at hz ⊢
    intro B
    apply hβinj
    rw [map_mul, map_mul, hz (β B)]
  · rw [← map_map,
      hmapβ _ _ ((CFSG.ClassicalInvolution.WeakCT.map_B12_blockSL3 (K := F) m i h).trans
        (range_blockSL2_eq m i)), hpiece _ Finset.subset_union_left (card_nodePair i)]
  · have hji : (⟨(i : ℕ) + 1, h⟩ : Fin m) = j := Fin.ext hj.symm
    have hB23 := CFSG.ClassicalInvolution.WeakCT.map_B23_blockSL3 (K := F) m i h
    rw [hji] at hB23
    rw [← map_map, hmapβ _ _ (hB23.trans (range_blockSL2_eq m j)),
      hpiece _ Finset.subset_union_right (card_nodePair j)]
  · have hτ : (⊤ : Subgroup SL(3, F)).map (CFSG.ClassicalInvolution.WeakCT.blockSL3 F m i h) =
        blockSpecialLinear (K := F)
          (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}) := by
      rw [← MonoidHom.range_eq_map, ← consecutiveBlock_three i j hj]
      exact range_blockSL_eq _
    have hτ2 : 2 ≤ (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}).card :=
      (card_nodePair i).symm.le.trans (Finset.card_le_card Finset.subset_union_left)
    rw [MonoidHom.range_eq_map, ← map_map, hmapβ _ _ hτ,
      P.pieceCore_eq_map_of_notMem hN hτ2 hk hκ hF hX]

end Pair

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {m : ℕ} {K : Type*} [Field K]
  {F : Type} [Field F] [Finite F] {e : L ≃* LinearFlag.projectiveSL (m + 1) K} {t : G}
  {ι : K →+* F} {σ : F ≃+* F}

theorem four_le_of_card_eq_two_pow_two_mul {α : Type*} {f : ℕ} (hF : Nat.card α = 2 ^ (2 * f))
    (hf : 1 ≤ f) : 4 ≤ Nat.card α := by
  rw [hF]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem exists_weakCT_of_fieldNeighbourCover (hm : 3 ≤ m) {f : ℕ}
    (hF : Nat.card F = 2 ^ (2 * f)) (hf : 1 ≤ f) {κ : Kˣ} (hκ : κ ≠ 1)
    (hcov : FieldNeighbourCover e t ι σ 3)
    (hcomm : ∀ i j : Fin m, (i : ℕ) + 1 < j →
      pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ≤
        centralizer (pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1))) : Set G))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    ∃ ψ : SL(m + 1, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, F) ∧
      (∀ i : Fin m,
        (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
          (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) ∧
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) := by
  have hF4 : 4 ≤ Nat.card F := four_le_of_card_eq_two_pow_two_mul hF hf
  have hle : ∀ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ≤ G₀ :=
    fun i => hG₀ ▸ le_iSup (fun i : Fin m =>
      pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) i
  have hUmap : ∀ i : Fin m,
      ((pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀).map
        G₀.subtype = pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := fun i => by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (hle i)]
  have hcomm' : ∀ i j : Fin m, (i : ℕ) + 1 < j →
      ∀ x ∈ (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀,
      ∀ y ∈ (pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1)))).subgroupOf G₀,
        x * y = y * x := by
    intro i j hij x hx y hy
    have h1 := mem_centralizer_iff.1 (hcomm i j hij (mem_subgroupOf.1 hx)) (y : G)
      (mem_subgroupOf.1 hy)
    exact Subtype.ext h1.symm
  have hpair : ∀ i j : Fin m, (j : ℕ) = i + 1 →
      ∃ W, CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair F W
        ((pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀)
        ((pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) := by
    intro i j hj
    obtain ⟨X, N, hSN, ⟨k, hk⟩, hX, ⟨P⟩⟩ := hcov _ (card_union_nodePair_adjacent_le i j hj)
    obtain ⟨θ, hθker, hθ12, hθ23, -⟩ :=
      exists_theta_of_fieldNeighbourParam P i j hj hSN hk hκ hF4 hX
    have hθG₀ : ∀ A, θ A ∈ G₀ := by
      intro A
      have hA : θ A ∈ θ.range := ⟨A, rfl⟩
      rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.WeakCT.B12_sup_B23 (K := F),
        Subgroup.map_sup, hθ12, hθ23] at hA
      exact sup_le (hle i) (hle j) hA
    let θ' : SL(3, F) →* G₀ := θ.codRestrict G₀ hθG₀
    have hθθ' : G₀.subtype.comp θ' = θ := MonoidHom.ext fun _ => rfl
    have hθ' : ∀ H : Subgroup SL(3, F), (H.map θ').map G₀.subtype = H.map θ := fun H => by
      rw [map_map, hθθ']
    refine ⟨θ'.range, θ', 1, rfl, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [MonoidHom.ker_codRestrict]
      exact hθker
    · rw [map_conj_one_inv_eq]
      apply map_injective G₀.subtype_injective
      rw [hθ', hθ12, hUmap]
    · rw [map_conj_one_inv_eq]
      apply map_injective G₀.subtype_injective
      rw [hθ', hθ23, hUmap]
  have hgen : ⨆ i : Fin m,
      (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀ = ⊤ := by
    apply map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp only [hUmap]
    exact hG₀.symm
  obtain ⟨Fam, hFam⟩ := CFSG.ClassicalInvolution.WeakCT.exists_ctFamily_of_pairs hF4
    (by omega) hcomm' hpair
  have hgen' : ⨆ i, (Fam.ι i).range = ⊤ := by
    simp only [fun i => (hFam i).1]
    exact hgen
  have hnt : ∃ i, ∃ A, Fam.ι i A ≠ 1 := by
    obtain ⟨s, hs⟩ := CFSG.ClassicalInvolution.WeakCT.exists_unit_ne_one (K := F) (by omega)
    refine ⟨⟨0, by omega⟩, CFSG.ClassicalInvolution.WeakCT.torusHom F s, fun h => hs ?_⟩
    apply CFSG.ClassicalInvolution.WeakCT.torusHom_injective
    rw [map_one]
    exact (hFam ⟨0, by omega⟩).2 (h.trans (map_one _).symm)
  obtain ⟨ψ, hψ, hsurj, hker, hqs, -, hmodel⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_recognition hm Nat.prime_two (by omega : 1 ≤ 2 * f)
      hF Fam hgen' hnt
  refine ⟨ψ, hsurj, hker, fun i => ?_, hqs, hmodel⟩
  rw [← range_blockSL2_eq m i, ← MonoidHom.range_comp, ← (hFam i).1]
  congr 1
  exact MonoidHom.ext fun A => hψ i A

theorem exists_ne_one_of_three_le_card {α : Type*} [Field α] [Finite α] (hα : 3 ≤ Nat.card α) :
    ∃ κ : αˣ, κ ≠ 1 := by
  have h2 : Nat.card αˣ = Nat.card α - 1 := Nat.card_units α
  have h3 : 1 < Nat.card αˣ := by omega
  have := Finite.one_lt_card_iff_nontrivial.mp h3
  exact exists_ne 1

end Recognition

end CFSG.SeitzReduction.LinearPilot
