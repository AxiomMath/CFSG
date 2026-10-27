module

public import CFSG.Quasithin.Background.C126NatDProd

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.C126.Nat

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem card_biSup_eq_prod_of_commuting {I : Finset (Subgroup Γ)}
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (A : Subgroup Γ → Subgroup Γ) (hA : ∀ L ∈ I, A L ≤ L) :
    ∀ J : Finset (Subgroup Γ), J ⊆ I →
      Nat.card ↥(⨆ L ∈ J, A L) = ∏ L ∈ J, Nat.card ↥(A L) := by
  classical
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro _
    have e : (⨆ L ∈ (∅ : Finset (Subgroup Γ)), A L) = ⊥ := by simp
    rw [e]
    simp
  | insert L₀ J hL₀J ih =>
    intro hJI
    have hL₀I : L₀ ∈ I := hJI (Finset.mem_insert_self _ _)
    have hJI' : J ⊆ I := fun y hy => hJI (Finset.mem_insert_of_mem hy)
    rw [Finset.iSup_insert, Finset.prod_insert hL₀J]
    have hcm : ∀ a ∈ A L₀, ∀ b ∈ ⨆ L ∈ J, A L, a * b = b * a := by
      intro a ha b hb
      have hle : (⨆ L ∈ J, A L) ≤ Subgroup.centralizer (A L₀ : Set Γ) := by
        refine iSup₂_le fun L hL c hc => Subgroup.mem_centralizer_iff.2 fun d hd => ?_
        have hne : L₀ ≠ L := fun he => hL₀J (he ▸ hL)
        exact (hcomm L₀ hL₀I L (hJI' hL) hne d (hA L₀ hL₀I hd) c (hA L (hJI' hL) hc))
      exact Subgroup.mem_centralizer_iff.1 (hle hb) a ha
    have hdisj : A L₀ ⊓ ⨆ L ∈ J, A L = ⊥ := by
      refine le_bot_iff.1 ?_
      calc A L₀ ⊓ ⨆ L ∈ J, A L ≤ L₀ ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L₀), L' := by
            refine inf_le_inf (hA L₀ hL₀I) (iSup₂_le fun L hL => ?_)
            have hne : L ≠ L₀ := fun he => hL₀J (he ▸ hL)
            exact (hA L (hJI' hL)).trans (le_iSup₂_of_le (f := fun (K : Subgroup Γ)
              (_ : K ∈ I) => ⨆ (_ : K ≠ L₀), K) L (hJI' hL) (le_iSup (fun _ : L ≠ L₀ => L) hne))
        _ = ⊥ := hind L₀ hL₀I
    rw [card_sup_of_commuting hcm hdisj, ih hJI']

theorem two_pow_factorization_prod {ι : Type*} (J : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ J, f i ≠ 0) :
    2 ^ (∏ i ∈ J, f i).factorization 2 = ∏ i ∈ J, 2 ^ (f i).factorization 2 := by
  rw [Nat.factorization_prod hf, Finsupp.finsetSum_apply, Finset.prod_pow_eq_pow_sum]

theorem eq_biSup_inf_of_fam {I : Finset (Subgroup Γ)}
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) {S : Subgroup Γ}
    (hS : IsSylowTwoOf S (⨆ L ∈ I, L)) : S = ⨆ L ∈ I, (S ⊓ L) := by
  classical
  have hnorm : ∀ L ∈ I, (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (L : Set Γ) := by
    intro L hL
    refine iSup₂_le fun L' hL' => ?_
    by_cases h : L' = L
    · rw [h]
      exact Subgroup.le_normalizer
    · exact le_normalizer_of_commuting (hcomm L hL L' hL' (Ne.symm h))
  have hSyl : ∀ L ∈ I, IsSylowTwoOf (S ⊓ L) L := fun L hL =>
    B6.isSylowTwoOf_inf_normal hS (le_iSup₂_of_le (f := fun (K : Subgroup Γ) (_ : K ∈ I) => K)
      L hL le_rfl) (hnorm L hL)
  have hle : (⨆ L ∈ I, (S ⊓ L)) ≤ S := iSup₂_le fun L _ => inf_le_left
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h1 := card_biSup_eq_prod_of_commuting hcomm hind (fun L => S ⊓ L)
    (fun L _ => inf_le_right) I le_rfl
  have h2 := card_biSup_eq_prod_of_commuting hcomm hind (fun L => L) (fun L _ => le_rfl) I le_rfl
  have h3 : twoPart (⨆ L ∈ I, L) = ∏ L ∈ I, twoPart L := by
    unfold twoPart
    rw [h2, two_pow_factorization_prod I _ (fun L _ => Nat.card_pos.ne')]
  rw [hS.card_eq, h3]
  beta_reduce at h1
  rw [h1, Finset.prod_congr rfl (fun L hL => (hSyl L hL).card_eq)]

theorem le_normalizer_of_factors {I : Finset (Subgroup Γ)}
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) {S X : Subgroup Γ}
    (hS : IsSylowTwoOf S (⨆ L ∈ I, L)) (hX : X ≤ ⨆ L ∈ I, L) (hSX : S ≤ X)
    (hD : ∀ L ∈ I, ∀ Z : Subgroup Γ, Z ≤ L → S ⊓ L ≤ Z →
      Z = L ∨ Z ≤ Subgroup.normalizer ((S ⊓ L : Subgroup Γ) : Set Γ))
    (hno : ∀ L ∈ I, ¬ L ≤ X) : X ≤ Subgroup.normalizer (S : Set Γ) := by
  classical
  have hnorm : ∀ L ∈ I, (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (L : Set Γ) := by
    intro L hL
    refine iSup₂_le fun L' hL' => ?_
    by_cases h : L' = L
    · rw [h]
      exact Subgroup.le_normalizer
    · exact le_normalizer_of_commuting (hcomm L hL L' hL' (Ne.symm h))
  have hSyl : ∀ L ∈ I, IsSylowTwoOf (S ⊓ L) L := fun L hL =>
    B6.isSylowTwoOf_inf_normal hS (le_iSup₂_of_le (f := fun (K : Subgroup Γ) (_ : K ∈ I) => K)
      L hL le_rfl) (hnorm L hL)
  have h1 : ∀ L ∈ I, X ≤ Subgroup.normalizer ((S ⊓ L : Subgroup Γ) : Set Γ) := fun L hL =>
    le_normalizer_inf_of_factor (hnorm L hL) (hSyl L hL) hX hSX (hD L hL) (hno L hL)
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have e := eq_biSup_inf_of_fam hcomm hind hS
  conv_lhs => rw [e]
  rw [Subgroup.map_iSup]
  conv_rhs => rw [e]
  refine iSup_congr fun L => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun hL => ?_
  exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (h1 L hL hx)

end CFSG.AGLEmbeddingD2.GN
