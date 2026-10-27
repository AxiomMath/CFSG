module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowPieces
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open scoped MatrixGroups

section Pair

variable {G : Type*} [Group G] {L : Subgroup G} {m : ℕ} {K : Type*} [Field K] {F : Type}
  [Field F] {e : L ≃* LinearFlag.projectiveSL (m + 1) K} {t : G} {ι : K →+* F} {σ : F ≃+* F}
  {X : Subgroup G} {N : Finset (Fin (m + 1))}

theorem exists_theta_of_fieldNeighbourParam_of_eq (P : FieldNeighbourParam e t ι σ X N)
    (i j : Fin m) (hj : (j : ℕ) = i + 1)
    (hN : ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ} ⊆ N)
    {U₁ U₂ : Subgroup G}
    (h₁ : U₁ = ((blockSpecialLinear (K := F)
      ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf (blockSpecialLinear N)).map P.Φ)
    (h₂ : U₂ = ((blockSpecialLinear (K := F)
      ({j.castSucc, j.succ} : Finset (Fin (m + 1)))).subgroupOf (blockSpecialLinear N)).map P.Φ) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧
      (CFSG.ClassicalInvolution.WeakCT.B12 F).map θ = U₁ ∧
      (CFSG.ClassicalInvolution.WeakCT.B23 F).map θ = U₂ := by
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
  refine ⟨P.Φ.comp β, ?_, ?_, ?_⟩
  · intro A hA
    have hz : β A ∈ center (blockSpecialLinear (K := F) N) := P.ker_le hA
    rw [mem_center_iff] at hz ⊢
    intro B
    apply hβinj
    rw [map_mul, map_mul, hz (β B)]
  · rw [← map_map,
      hmapβ _ _ ((CFSG.ClassicalInvolution.WeakCT.map_B12_blockSL3 (K := F) m i h).trans
        (range_blockSL2_eq m i)), h₁]
  · have hji : (⟨(i : ℕ) + 1, h⟩ : Fin m) = j := Fin.ext hj.symm
    have hB23 := CFSG.ClassicalInvolution.WeakCT.map_B23_blockSL3 (K := F) m i h
    rw [hji] at hB23
    rw [← map_map, hmapβ _ _ (hB23.trans (range_blockSL2_eq m j)), h₂]

end Pair

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {m : ℕ} {K : Type*} [Field K]
  {F : Type} [Field F] [Finite F] {e : L ≃* LinearFlag.projectiveSL (m + 1) K} {t : G}
  {ι : K →+* F} {σ : F ≃+* F}

omit [Finite G] in
theorem exists_weakCT_of_pieces (hm : 3 ≤ m) {f : ℕ} (hF : Nat.card F = 2 ^ (2 * f))
    (hf : 1 ≤ f) (U : Fin m → Subgroup G)
    (hpair : ∀ i j : Fin m, (j : ℕ) = i + 1 → ∃ (X : Subgroup G) (N : Finset (Fin (m + 1)))
      (P : FieldNeighbourParam e t ι σ X N),
      ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ} ⊆ N ∧
      U i = ((blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf
        (blockSpecialLinear N)).map P.Φ ∧
      U j = ((blockSpecialLinear (K := F) ({j.castSucc, j.succ} : Finset (Fin (m + 1)))).subgroupOf
        (blockSpecialLinear N)).map P.Φ)
    (hcomm : ∀ i j : Fin m, (i : ℕ) + 1 < j → U i ≤ centralizer (U j : Set G))
    {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ i : Fin m, U i) :
    ∃ ψ : SL(m + 1, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, F) ∧
      (∀ i : Fin m,
        (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
          (U i).subgroupOf G₀) ∧
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) := by
  have hF4 : 4 ≤ Nat.card F := four_le_of_card_eq_two_pow_two_mul hF hf
  have hle : ∀ i : Fin m, U i ≤ G₀ := fun i => hG₀ ▸ le_iSup U i
  have hUmap : ∀ i : Fin m, ((U i).subgroupOf G₀).map G₀.subtype = U i := fun i => by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (hle i)]
  have hcomm' : ∀ i j : Fin m, (i : ℕ) + 1 < j →
      ∀ x ∈ (U i).subgroupOf G₀, ∀ y ∈ (U j).subgroupOf G₀, x * y = y * x := by
    intro i j hij x hx y hy
    have h1 := mem_centralizer_iff.1 (hcomm i j hij (mem_subgroupOf.1 hx)) (y : G)
      (mem_subgroupOf.1 hy)
    exact Subtype.ext h1.symm
  have hpair' : ∀ i j : Fin m, (j : ℕ) = i + 1 →
      ∃ W, CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair F W
        ((U i).subgroupOf G₀) ((U j).subgroupOf G₀) := by
    intro i j hj
    obtain ⟨X, N, P, hSN, hUi, hUj⟩ := hpair i j hj
    obtain ⟨θ, hθker, hθ12, hθ23⟩ := exists_theta_of_fieldNeighbourParam_of_eq P i j hj hSN hUi hUj
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
  have hgen : ⨆ i : Fin m, (U i).subgroupOf G₀ = ⊤ := by
    apply map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp only [hUmap]
    exact hG₀.symm
  obtain ⟨Fam, hFam⟩ := CFSG.ClassicalInvolution.WeakCT.exists_ctFamily_of_pairs hF4
    (by omega) hcomm' hpair'
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

end Recognition

section Root

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type*}
  [Field F]

@[expose] def FieldRevComm (e : L ≃* LinearFlag.projectiveSL n K) {t : G} {ι : K →+* F}
    {σ : F ≃+* F} {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n))) : Prop :=
  ∀ (a b : Fin n) (hab : a ≠ b) (A : Finset (Fin n)), A.card = 2 →
    Disjoint A ({a, b} : Finset (Fin n)) →
    ((blockSpecialLinear (K := F) A).subgroupOf
      (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map (P a b hab).Φ ≤
      centralizer (modelToG e (blockSL (K := K) Aᶜ) : Set G)

theorem exists_root_disjoint {S : Finset (Fin n)} (hS : S.card + 2 ≤ n) :
    ∃ a b : Fin n, a ≠ b ∧ Disjoint S ({a, b} : Finset (Fin n)) := by
  have hc : 1 < Sᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hc
  refine ⟨a, b, hab, ?_⟩
  rw [← Finset.subset_compl_iff_disjoint_right]
  intro x hx
  rw [Finset.mem_compl]
  intro h
  rcases Finset.mem_insert.1 h with rfl | h
  · exact (Finset.mem_compl.1 ha) hx
  · rw [Finset.mem_singleton.1 h] at hx
    exact (Finset.mem_compl.1 hb) hx

theorem two_le_card_compl_sdiff {a b : Fin n} (hab : a ≠ b) {A : Finset (Fin n)}
    (hA : A.card = 2) (hdis : Disjoint A ({a, b} : Finset (Fin n))) (hn : 6 ≤ n) :
    2 ≤ (({a, b} : Finset (Fin n))ᶜ \ A).card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_compl_iff_disjoint_right.2 hdis),
    Finset.card_compl, Fintype.card_fin, Finset.card_pair hab, hA]
  omega

variable [Finite G] [Finite F]

theorem complPieceCore_eq_map_root (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    {ι : K →+* F} {σ : F ≃+* F} {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n)))
    (hrev : FieldRevComm e P) (hn : 6 ≤ n) (hF : 4 ≤ Nat.card F) {a b : Fin n} (hab : a ≠ b)
    {A : Finset (Fin n)} (hA : A.card = 2) (hdis : Disjoint A ({a, b} : Finset (Fin n))) :
    complPieceCore e A = ((blockSpecialLinear (K := F) A).subgroupOf
      (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map (P a b hab).Φ := by
  have hAN : A ⊆ ({a, b}ᶜ : Finset (Fin n)) := Finset.subset_compl_iff_disjoint_right.2 hdis
  have hab' : ({a, b} : Finset (Fin n)) ⊆ Aᶜ := Finset.subset_compl_iff_disjoint_left.2 hdis
  exact complPieceCore_eq_map_of_le_centralizer (P a b hab) hAN
    (modelToG_mono e ((hXr a b).trans (blockSL_mono hab')))
    (two_le_card_compl_sdiff hab hA hdis hn) (commutator_blockSpecialLinear_eq_of_card_two hA hF)
    (hrev a b hab A hA hdis)

omit [Finite G] [Finite F] in
theorem modelToG_blockSL_le_map {e : L ≃* LinearFlag.projectiveSL n K} {t : G} {ι : K →+* F}
    {σ : F ≃+* F} {X : Subgroup G} {N A : Finset (Fin n)} (P : FieldNeighbourParam e t ι σ X N)
    (hAN : A ⊆ N) :
    modelToG e (blockSL (K := K) A) ≤
      ((blockSpecialLinear (K := F) A).subgroupOf (blockSpecialLinear N)).map P.Φ := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
  obtain ⟨B, hB, rfl⟩ := mem_blockSL.1 hx
  have hBN : B ∈ blockSpecialLinear (K := K) N := blockSpecialLinear_mono hAN hB
  refine ⟨⟨Matrix.SpecialLinearGroup.map ι B, map_ringHom_mem_blockSpecialLinear ι hBN⟩, ?_, ?_⟩
  · exact mem_subgroupOf.2 (map_ringHom_mem_blockSpecialLinear ι hB)
  · exact P.N1 ⟨B, hBN⟩

end Root

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_globalField_compl (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    {m f : ℕ} (hm : 5 ≤ m) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {Xr : Fin (m + 1) → Fin (m + 1) → Subgroup (LinearFlag.projectiveSL (m + 1) K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (P : ∀ a b : Fin (m + 1), a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin (m + 1))))
    (hrev : FieldRevComm e P) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, complPieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    ∃ (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)),
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) ∧
      (∃ ψ : SL(m + 1, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, F) ∧
        ∀ i : Fin m,
          (blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
            (complPieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) ∧
      ∃ ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F,
        (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = projMap (m + 1) ι (e x)) ∧
        ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
          LinearFlag.fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀)) := by
  have : Finite K := finite_of_card_eq_two_pow hKc
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  have hF4 : 4 ≤ Nat.card F := four_le_of_card_eq_two_pow_two_mul hF hf
  set U : Fin m → Subgroup G :=
    fun i => complPieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) with hU
  have hpiece : ∀ (i : Fin m) (a b : Fin (m + 1)) (hab : a ≠ b),
      Disjoint ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ({a, b} : Finset (Fin (m + 1))) →
      U i = ((blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf
        (blockSpecialLinear ({a, b}ᶜ : Finset (Fin (m + 1))))).map (P a b hab).Φ :=
    fun i a b hab hdis =>
      complPieceCore_eq_map_root e hXr P hrev (by omega) hF4 hab (card_nodePair i) hdis
  have hpair : ∀ i j : Fin m, (j : ℕ) = i + 1 → ∃ (X : Subgroup G) (N : Finset (Fin (m + 1)))
      (P' : FieldNeighbourParam e t ι σ X N),
      ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ} ⊆ N ∧
      U i = ((blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf
        (blockSpecialLinear N)).map P'.Φ ∧
      U j = ((blockSpecialLinear (K := F) ({j.castSucc, j.succ} : Finset (Fin (m + 1)))).subgroupOf
        (blockSpecialLinear N)).map P'.Φ := by
    intro i j hj
    obtain ⟨a, b, hab, hdis⟩ := exists_root_disjoint (n := m + 1)
      (S := ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ})
      (by have := card_union_nodePair_adjacent_le i j hj; omega)
    refine ⟨_, _, P a b hab, Finset.subset_compl_iff_disjoint_right.2 hdis,
      hpiece i a b hab (hdis.mono_left Finset.subset_union_left),
      hpiece j a b hab (hdis.mono_left Finset.subset_union_right)⟩
  have hcomm : ∀ i j : Fin m, (i : ℕ) + 1 < j → U i ≤ centralizer (U j : Set G) := by
    intro i j hij
    obtain ⟨a, b, hab, hdis⟩ := exists_root_disjoint (n := m + 1)
      (S := ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ})
      (by have := card_union_nodePair_le i j; omega)
    rw [hpiece i a b hab (hdis.mono_left Finset.subset_union_left),
      hpiece j a b hab (hdis.mono_left Finset.subset_union_right)]
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (commute_blockSpecialLinear_of_disjoint (disjoint_nodePair_of_lt i j hij)
      (mem_subgroupOf.1 hx) (mem_subgroupOf.1 hy)).symm.eq
  obtain ⟨ψ, hsurj, hker, himg, hqs, hmodel⟩ :=
    exists_weakCT_of_pieces (by omega) hF hf U hpair hcomm hG₀
  have hLG₀ : L ≤ G₀ := by
    refine (modelToG_top e).symm.le.trans ?_
    rw [← iSup_blockSL_pair_eq_top K m, modelToG_iSup, hG₀]
    refine iSup_mono fun i => ?_
    obtain ⟨a, b, hab, hdis⟩ := exists_root_disjoint (n := m + 1)
      (S := ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
      (by rw [card_nodePair]; omega)
    change _ ≤ U i
    rw [hpiece i a b hab hdis]
    exact modelToG_blockSL_le_map (P a b hab) (Finset.subset_compl_iff_disjoint_right.2 hdis)
  have htG₀ : t ∈ normalizer (G₀ : Set G) := by
    rw [hG₀]
    exact mem_normalizer_iSup_family fun _ => le_normalizer_complPieceCore e htC _
  obtain ⟨F', _, _, hF', ⟨ψ₁⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmodel
  have : Fintype F' := Fintype.ofFinite F'
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F' = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF', hF]
  let ψ₀ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F := ψ₁.trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcardF))
  obtain ⟨ψ', hψ'L, hψ't⟩ := exists_mulEquiv_globalNormal_center (by omega) ι hσ1 hσσ hfix e ψ₀
    hLG₀ (by rw [← ht]; exact pow_orderOf_eq_one t) htG₀
    (perfectCore_inf_centralizer_eq_of_standardSetting hset hOut (by omega) e hLG₀ htC ht)
  exact ⟨hLG₀, htG₀, hqs, hmodel, ⟨ψ, hsurj, hker, himg⟩, ψ', hψ'L, hψ't⟩

theorem false_of_fieldRow_compl (hset : SeitzSetting G L) {m f : ℕ} (hm : 5 ≤ m) {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (e : L ≃* LinearFlag.projectiveSL (m + 1) K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {Xr : Fin (m + 1) → Fin (m + 1) → Subgroup (LinearFlag.projectiveSL (m + 1) K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (P : ∀ a b : Fin (m + 1), a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin (m + 1))))
    (hrev : FieldRevComm e P) : False := by
  have : Finite K := finite_of_card_eq_two_pow hKc
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨hLG₀, htG₀, hq, -, -, ψ, -, hψt⟩ := exists_globalField_compl hset.standardSetting
    (isSolvable_outer_of_mulEquiv (by omega) e) hm hKc hf e htC ht ι hσ1 hσσ hfix hXr P hrev rfl
  exact false_of_globalField_compl_of_seitzSetting hset (by omega) hKc e ht hKt ι hσ1 hσσ hfix rfl
    hLG₀ htG₀ hq ψ hψt

end Global

end CFSG.SeitzReduction.LinearPilot
