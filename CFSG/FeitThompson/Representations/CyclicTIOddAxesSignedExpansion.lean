module

public import CFSG.FeitThompson.Representations.OddArrayCoefficientsSupportingDegree
public import CFSG.FeitThompson.Representations.SignedCyclicTIArrayCoprimeNonvanishing
public import CFSG.FeitThompson.Representations.SmallCharactersPerpendicularCyclicTIArray
public import CFSG.FeitThompson.Representations.DisjointCyclicTISupportSeparatesFamily
public import CFSG.FeitThompson.Representations.FrobeniusSemidirectIrrCharacterList

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open CrossFamilyProjection (coherentImage coherentImage_apply)

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} {ι : Type*} {ξ : ι → (↥L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}
  {W W1 W2 : Subgroup G} [Fintype ↥W] {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem exists_finEquiv_apply_zero_eq {α : Type*} [Finite α] [NeZero (Nat.card α)] (a₀ : α) :
    ∃ e : Fin (Nat.card α) ≃ α, e 0 = a₀ := by
  classical
  refine ⟨((Finite.equivFin α).trans (Equiv.swap (Finite.equivFin α a₀) 0)).symm, ?_⟩
  rw [Equiv.symm_apply_eq]
  simp [Equiv.swap_apply_left]

omit [Fintype G] [Fintype ↥W] in
theorem sum_smul_prodCharEta_reindex [Fintype (Irr ↥W1)] [Fintype (Irr ↥W2)] {m n : ℕ}
    (hW : IsCyclicTIPair W W1 W2) (e1 : Fin m ≃ Irr ↥W1) (e2 : Fin n ≃ Irr ↥W2)
    (ε : Fin m × Fin n → ℂ) :
    (∑ p : Fin m × Fin n, ε p • hW.prodCharEta σ (e1 p.1) (e2 p.2) : G → ℂ)
      = ∑ q : Irr ↥W1 × Irr ↥W2, ε (e1.symm q.1, e2.symm q.2) • hW.prodCharEta σ q.1 q.2 :=
  Fintype.sum_equiv (e1.prodCongr e2) _ _ fun p => by simp

variable [H.Normal] (hodd : Odd (Nat.card G)) (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
  (hinj : Function.Injective ξ) (hSIrr : Set.range ξ ⊆ Irr ↥L)
  (hν : IsCoherentWith (Set.range ξ) τ ν)
  (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζ1 : ξ k₀ 1 = (H.index : ℂ)) (hS2 : (Set.range ξ).Nontrivial)
  (hbound : 2 * H.index + 1 ≤ Nat.card ↥H)
  (hW : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
  (hV : ∀ F : dadeDomain L A, ∀ v ∈ cyclicTIDiff W W1 W2,
    ((dadeMap hD F : classFun G) : G → ℂ) v = 0)
  (heW : H.index ≤ Nat.card ↥W)
  (hrow : ∀ i : Irr ↥W1, i ≠ principalIrr ↥W1 → ∃ c : ℤ, Odd c ∧
    cfInner (dadeBeta A R H (ξ k₀)) (hW.prodCharEta σ i (principalIrr ↥W2)) = (c : ℂ))
  (hcol : ∀ j : Irr ↥W2, j ≠ principalIrr ↥W2 → ∃ c : ℤ, Odd c ∧
    cfInner (dadeBeta A R H (ξ k₀)) (hW.prodCharEta σ (principalIrr ↥W1) j) = (c : ℂ))

include hodd hD hA hS hinj hSIrr hν hτ hζ1 hS2 hbound hW hσ hV heW hrow hcol in
theorem cyclicTI_dade_saturation :
    H.index = Nat.card ↥W ∧
      ∃ ε : Irr ↥W1 × Irr ↥W2 → ℂ, (∀ p, ε p = 1 ∨ ε p = -1) ∧
        ∃ χ : G → ℂ, χ ∈ signedIrr G ∧
          (χ = (ν ⟨ξ k₀, Submodule.subset_span (Set.mem_range_self k₀)⟩ : G → ℂ) ∨
            χ = -(ν ⟨star (ξ k₀), Submodule.subset_span
              (star_mem_of_mem hS (Set.mem_range_self k₀))⟩ : G → ℂ)) ∧
          dadeBeta A R H (ξ k₀) = hW.signedProdCharEtaSum σ ε - χ ∧
          ∀ ψ : classFun ↥W, (ψ : ↥W → ℂ) ∈ Irr ↥W → IsOrthogonal χ (σ ψ : G → ℂ) := by
  classical
  have hfl : Finite ↥W1 := hW.finite_left
  have hfr : Finite ↥W2 := hW.finite_right
  have hfι : Finite ι := by
    have hfin : (Set.range ξ).Finite := hS ▸ indFam_finite H finite_Irr_diff_one
    have := hfin.to_subtype
    exact Finite.of_injective (fun i => (⟨ξ i, Set.mem_range_self i⟩ : Set.range ξ))
      fun a b h => hinj (congrArg Subtype.val h)
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype (Irr ↥W1) := Fintype.ofFinite _
  let _ : Fintype (Irr ↥W2) := Fintype.ofFinite _
  set m := Nat.card (Irr ↥W1) with hm
  set n := Nat.card (Irr ↥W2) with hn
  have : NeZero m := ⟨by
    have : 0 < Nat.card (Irr ↥W1) := Nat.card_pos_iff.2 ⟨⟨principalIrr ↥W1⟩, inferInstance⟩
    omega⟩
  have : NeZero n := ⟨by
    have : 0 < Nat.card (Irr ↥W2) := Nat.card_pos_iff.2 ⟨⟨principalIrr ↥W2⟩, inferInstance⟩
    omega⟩
  obtain ⟨e1, he1⟩ := exists_finEquiv_apply_zero_eq (principalIrr ↥W1)
  obtain ⟨e2, he2⟩ := exists_finEquiv_apply_zero_eq (principalIrr ↥W2)
  set θ : Fin m × Fin n → G → ℂ := fun p => hW.prodCharEta σ (e1 p.1) (e2 p.2) with hθdef
  have hθorth : IsOrthonormalFamily θ := IsOrthonormalFamily.of_cfInner_eq_ite fun p q => by
    have hiff : (e1 p.1 = e1 q.1 ∧ e2 p.2 = e2 q.2) ↔ p = q := by
      rw [Equiv.apply_eq_iff_eq, Equiv.apply_eq_iff_eq, Prod.ext_iff]
    rw [hθdef]
    simp only
    rw [hW.cfInner_prodCharEta hσ]
    exact if_congr hiff rfl rfl
  have hθmem : ∀ p, θ p ∈ virtualChars G := fun p =>
    hW.prodCharEta_mem_virtualChars hσ (e1 p.1) (e2 p.2)
  have hθ0 : θ (0, 0) = 1 := by
    rw [hθdef]
    simp only [he1, he2]
    exact hW.prodCharEta_principal hσ
  have hζS : ξ k₀ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ Set.mem_range_self k₀
  have hζIrr : ξ k₀ ∈ Irr ↥L := hSIrr (Set.mem_range_self k₀)
  have hβcf : dadeBeta A R H (ξ k₀) ∈ classFun G := dadeBeta_mem_classFun hD hA hζS hζ1
  have hβV : ∀ v ∈ cyclicTIDiff W W1 W2, dadeBeta A R H (ξ k₀) v = 0 := fun v hv => by
    rw [dadeBeta_eq_dadeMap_indClassFun_one_sub hD hA hζS hζ1]
    exact hV _ v hv
  have hfull := DisjointCoherentFamilies.isFullCoherentFamily_of_isDadeData hodd hD hA hS hSIrr
    (fun f hf => hτ f ⟨_, hf⟩ rfl) hν
  have hτV : ∀ f : charSpanZero (Set.range ξ), ∀ v ∈ cyclicTIDiff W W1 W2,
      (τ f : G → ℂ) v = 0 := fun f v hv => by
    rw [hτ f ⟨_, DisjointCoherentFamilies.mem_dadeDomain_of_charSpanZero hA hS f⟩ rfl]
    exact hV _ v hv
  have hθν : ∀ (l : ι) (p : Fin m × Fin n), cfInner (coherentImage ξ ν l) (θ p) = 0 := by
    intro l p
    have hψ : ((hW.basisProdIrr (e1 p.1, e2 p.2) : classFun ↥W) : ↥W → ℂ) ∈ Irr ↥W := by
      rw [hW.coe_basisProdIrr_apply]
      exact hW.prodChar_mem_Irr (e1 p.1).2 (e2 p.2).2
    have hor := hfull.isOrthogonal_coherentImage_apply hW hσ hτV l hψ
    rw [isOrthogonal_iff] at hor
    rw [hθdef]
    simpa [hW.prodCharEta_eq_coe_apply] using hor
  obtain ⟨b, hb⟩ := exists_int_cfInner_dadeBeta_array hD hA hS hζ1 hθmem
  have h00 : b (0, 0) = 1 := array_coeff_zero_eq_one hD hA hS hζ1 hθ0 hb
  have hexch : ∀ (i : Fin m) (j : Fin n), b (i, j) + b (0, 0) = b (i, 0) + b (0, j) := by
    intro i j
    have hx := hW.cfInner_prodCharEta_exchange hσ hβcf hβV (e1 i) (e2 j)
    rw [← he1, ← he2] at hx
    have hc : ((b (i, j) + b (0, 0) : ℤ) : ℂ) = ((b (i, 0) + b (0, j) : ℤ) : ℂ) := by
      push_cast
      rw [← hb (i, j), ← hb (0, 0), ← hb (i, 0), ← hb (0, j)]
      exact hx
    exact_mod_cast hc
  have hrow' : ∀ i : Fin m, Odd (b (i, 0)) := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [h00]; exact odd_one
    · obtain ⟨c, hcodd, hc⟩ := hrow (e1 i) fun hcon => hi (e1.injective (hcon.trans he1.symm))
      have hcast : ((b (i, 0) : ℤ) : ℂ) = (c : ℂ) := by
        rw [← hb (i, 0), hθdef]
        simp only [he2]
        exact hc
      have hbi : b (i, 0) = c := by exact_mod_cast hcast
      rw [hbi]; exact hcodd
  have hcol' : ∀ j : Fin n, Odd (b (0, j)) := by
    intro j
    by_cases hj : j = 0
    · subst hj; rw [h00]; exact odd_one
    · obtain ⟨c, hcodd, hc⟩ := hcol (e2 j) fun hcon => hj (e2.injective (hcon.trans he2.symm))
      have hcast : ((b (0, j) : ℤ) : ℂ) = (c : ℂ) := by
        rw [← hb (0, j), hθdef]
        simp only [he1]
        exact hc
      have hbj : b (0, j) = c := by exact_mod_cast hcast
      rw [hbj]; exact hcodd
  have hmn : m * n = Nat.card ↥W := by
    rw [hm, hn, hW.card_Irr_left, hW.card_Irr_right, ← hW.natCard_eq_mul]
  have hemn : (H.index : ℤ) ≤ (m : ℤ) * n := by
    have h' : (H.index : ℤ) ≤ ((m * n : ℕ) : ℤ) := by exact_mod_cast hmn ▸ heW
    push_cast at h' ⊢
    exact h'
  obtain ⟨hdeg, ε, hεsign, -, χ, hχsigned, hχval, hβeq, hχperp⟩ :=
    dade_signed_array_decomposition hodd hD hA hS hinj hν hτ hζIrr hζ1 hS2 hbound hθorth hθmem
      hθ0 hθν hb hexch hrow' hcol' hemn
  refine ⟨?_, fun q => ε (e1.symm q.1, e2.symm q.2), fun q => hεsign _, χ, hχsigned, hχval,
    ?_, ?_⟩
  · have h1 : (H.index : ℤ) = ((m * n : ℕ) : ℤ) := by push_cast; exact hdeg
    have h2 : H.index = m * n := by exact_mod_cast h1
    rw [h2, hmn]
  · rw [hβeq, hW.signedProdCharEtaSum_eq_sum, ← sum_smul_prodCharEta_reindex hW e1 e2 ε, hθdef]
  ·
    intro ψ hψ
    obtain ⟨i, j, hij⟩ := hW.exists_apply_eq_prodCharEta (σ := σ) hψ
    have hp := hχperp (e1.symm i, e2.symm j)
    rw [hθdef] at hp
    simp only [Equiv.apply_symm_apply] at hp
    rw [hij]
    exact hp

end NormalInducedFamily

end CFSG.FeitThompson

end
