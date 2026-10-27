module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.NormalizerSmall
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectionF4

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE8F

set_option linter.unusedSectionVars false


theorem exists_rootDiagUnit_word {τ : Tag} {K : Type} [Field K] {S : Set (Fin τ.rank → ℤ)}
    (ω : List (Fin τ.rank)) (i : Fin τ.rank)
    (hγ : (coxeterSystem τ).wordProd ω • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ S)
    (hγ' : -((coxeterSystem τ).wordProd ω • (Pi.single i 1 : Fin τ.rank → ℤ)) ∈ S) (t : Kˣ) :
    ∃ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ rootSpan τ K S ∧
      ∀ {β β' : Fin τ.rank → ℤ}, IsRoot τ β' → (coxeterSystem τ).wordProd ω • β' = β →
        rootChar a β = t ^ (∑ j, τ.cartan i j * β' j) := by
  set N : ModGL τ K := (ω.map fun i => weylElt τ K i 1).prod with hN
  have hx : ∀ c, N * xUnit τ K i c * N⁻¹ ∈ rootSpan τ K S := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K ω (IsRoot.basis (τ := τ) i)
    rw [← pinnedX_single, h]
    exact pinnedX_mem_rootSpan hγ _
  have hy : ∀ c, N * yUnit τ K i c * N⁻¹ ∈ rootSpan τ K S := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K ω (isRoot_neg_single τ i)
    rw [← pinnedX_neg_single, h, smul_neg]
    exact pinnedX_mem_rootSpan hγ' _
  have conj3 : ∀ a b : ModGL τ K, N * a * N⁻¹ ∈ rootSpan τ K S → N * b * N⁻¹ ∈ rootSpan τ K S →
      N * (a * b * a) * N⁻¹ ∈ rootSpan τ K S := fun a b ha hb => by
    have : N * (a * b * a) * N⁻¹ = (N * a * N⁻¹) * (N * b * N⁻¹) * (N * a * N⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) ha
  have hw : ∀ s : Kˣ, N * weylElt τ K i s * N⁻¹ ∈ rootSpan τ K S := by
    intro s
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    exact conj3 _ _ (hx _) (hy _)
  have hD : N * torusElt τ K i t * N⁻¹ ∈ rootSpan τ K S := by
    show N * (weylElt τ K i t * weylElt τ K i (-1)) * N⁻¹ ∈ rootSpan τ K S
    have : N * (weylElt τ K i t * weylElt τ K i (-1)) * N⁻¹ =
        (N * weylElt τ K i t * N⁻¹) * (N * weylElt τ K i (-1) * N⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ (hw t) (hw (-1))
  have hNn : N ∈ Subgroup.normalizer (torusGroup τ K : Set (ModGL τ K)) :=
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact weylElt_mem_normalizer_torus τ K j 1
  have hDT : N * torusElt τ K i t * N⁻¹ ∈ torusGroup τ K :=
    (Subgroup.mem_normalizer_iff.1 hNn _).1 (torusElt_mem_torusGroup i t)
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hDT
  refine ⟨a, ha ▸ hD, fun {β β'} hβ' hv => ?_⟩
  have hβ : IsRoot τ β := hv ▸ IsRoot.smul hβ' _
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K ω hβ'
  rw [hv] at h₂
  have h3 : pinnedX τ K β 1 = N * pinnedX τ K β' (ε₂ * 1) * N⁻¹ := by
    rw [h₂, ← mul_assoc, hε₂, one_mul]
  have hd : ∀ s : K, torusElt τ K i t * pinnedX τ K β' s * (torusElt τ K i t)⁻¹ =
      pinnedX τ K β' (((t ^ (∑ j, τ.cartan i j * β' j) : Kˣ) : K) * s) := by
    intro s
    rw [torusElt_eq_rootDiagUnit, rootDiagUnit_conj_pinnedX _ hβ', rootChar_cartan_zpow]
  have hkey : (N * torusElt τ K i t * N⁻¹) * pinnedX τ K β 1 * (N * torusElt τ K i t * N⁻¹)⁻¹ =
      pinnedX τ K β (((t ^ (∑ j, τ.cartan i j * β' j) : Kˣ) : K) * 1) := by
    calc (N * torusElt τ K i t * N⁻¹) * pinnedX τ K β 1 * (N * torusElt τ K i t * N⁻¹)⁻¹
        = N * (torusElt τ K i t * pinnedX τ K β' (ε₂ * 1) * (torusElt τ K i t)⁻¹) * N⁻¹ := by
          rw [h3]; group
      _ = N * pinnedX τ K β' (((t ^ (∑ j, τ.cartan i j * β' j) : Kˣ) : K) * (ε₂ * 1)) * N⁻¹ := by
          rw [hd]
      _ = pinnedX τ K β (ε₂ * (((t ^ (∑ j, τ.cartan i j * β' j) : Kˣ) : K) * (ε₂ * 1))) := h₂ _
      _ = _ := by
          congr 1
          linear_combination (((t ^ (∑ j, τ.cartan i j * β' j) : Kˣ) : K)) * hε₂
  rw [ha, rootDiagUnit_conj_pinnedX _ hβ] at hkey
  have := pinnedX_injective τ K β hkey
  rw [mul_one, mul_one] at this
  exact Units.ext this

@[expose] def thetaF4 : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

theorem thetaF4_mem : thetaF4 ∈ rootFinset .F4 := by decide +kernel

theorem f4_odd_table : ∀ β ∈ rootFinset .F4,
    (∃ k : Fin Tag.F4.rank, k ≠ 1 ∧ (∑ j, Tag.F4.cartan k j * β j) % 2 = 1) ∨
    (∑ j, Tag.F4.cartan 1 j * (f4Word.reverse.foldr (reflect .F4) β) j) % 2 = 1 := by
  decide +kernel

theorem frameNormalizerSolvable_F4_three (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 3) : FrameNormalizerSolvable .F4 K (cosetRoots .F4 1 3) := by
  have h2 := two_ne_zero_of_card_three K hK
  have hγ : (coxeterSystem Tag.F4).wordProd f4Word • (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) ∈
      cosetRoots .F4 1 3 :=
    ⟨IsRoot.smul (IsRoot.basis 1) _, by
      rw [wordProd_smul_eq_foldr, f4Word_apply]; exact dvd_refl _⟩
  have hγ' : -((coxeterSystem Tag.F4).wordProd f4Word • (Pi.single 1 1 : Fin Tag.F4.rank → ℤ)) ∈
      cosetRoots .F4 1 3 :=
    ⟨by rw [← smul_neg]; exact IsRoot.smul (isRoot_neg_single _ 1) _, by
      rw [Pi.neg_apply, wordProd_smul_eq_foldr, f4Word_apply]
      exact (dvd_neg.2 (dvd_refl _))⟩
  obtain ⟨a₀, ha₀, hχ⟩ := exists_rootDiagUnit_word (K := K) f4Word 1 hγ hγ' (-1)
  intro P hPG hPN hPX
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := exists_splitFrame_F4 K
  rw [← hrange] at hPN hPX
  refine isSolvable_of_le_normalizer_frame (isQuasisimple_SL (by norm_num))
    (isSolvable_out_SL (by norm_num)) hA hB hcomm (Gh := adjointGroup .F4 K)
    (hrange ▸ rootSpan_le_adjointGroup K _) (fun c hc d hd => ?_) hPG hPN hPX
  rw [hrange] at hc hd
  refine commute_of_mem_centralizer_cosetRoots_fam (mem_rootFinset.1 thetaF4_mem)
    (by decide) (by decide) (by decide)
    ({a | ∃ k : Fin Tag.F4.rank, k ≠ 1 ∧ a = negOneTuple .F4 K k} ∪ {a₀}) ?_ ?_ hc hd
  · rintro a (⟨k, hk, rfl⟩ | rfl)
    · have hsingle : (Pi.single k 1 : Fin Tag.F4.rank → ℤ) 1 = 0 := by simp [Ne.symm hk]
      have h1 : (Pi.single k 1 : Fin Tag.F4.rank → ℤ) ∈ cosetRoots .F4 1 3 :=
        ⟨IsRoot.basis k, by rw [hsingle]; exact dvd_zero _⟩
      have h2' : (-Pi.single k 1 : Fin Tag.F4.rank → ℤ) ∈ cosetRoots .F4 1 3 :=
        ⟨isRoot_neg_single _ k, by rw [Pi.neg_apply, hsingle, neg_zero]; exact dvd_zero _⟩
      unfold negOneTuple
      rw [← torusElt_eq_rootDiagUnit (i := k) (u := (-1 : Kˣ))]
      exact torusElt_mem_rootSpan h1 h2' (-1)
    · exact ha₀
  · intro α hα
    rcases f4_odd_table α (mem_rootFinset.2 hα) with ⟨k, hk, hodd⟩ | hodd
    · refine ⟨negOneTuple .F4 K k, Or.inl ⟨k, hk, rfl⟩, ?_⟩
      have := rootChar_cartan_zpow (K := K) (τ := .F4) (-1 : Kˣ) k α
      unfold negOneTuple
      rw [this]
      exact neg_one_zpow_ne_one (Int.odd_iff.2 hodd) h2
    · refine ⟨a₀, Or.inr rfl, ?_⟩
      have hrev : (coxeterSystem Tag.F4).wordProd f4Word.reverse • α =
          f4Word.reverse.foldr (reflect .F4) α := wordProd_smul_eq_foldr _ _ _
      have hv : (coxeterSystem Tag.F4).wordProd f4Word •
          ((coxeterSystem Tag.F4).wordProd f4Word.reverse • α) = α := by
        rw [CoxeterSystem.wordProd_reverse, smul_inv_smul]
      rw [hχ (IsRoot.smul hα _) hv, hrev]
      exact neg_one_zpow_ne_one (Int.odd_iff.2 hodd) h2

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
