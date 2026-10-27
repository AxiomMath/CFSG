module

public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

variable {Γ : Type} [Group Γ]

theorem card_iSup_eq_prod_sylowIndep {ι : Type} [Fintype ι] {H : ι → Subgroup Γ}
    (hcomm : Pairwise fun i j => ∀ x y : Γ, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H) : Nat.card (⨆ i, H i : Subgroup Γ) = ∏ i, Nat.card (H i) := by
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm), ← Nat.card_pi]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem relIndex_mul_card_of_le_sylowIndep [Finite Γ] {H K : Subgroup Γ} (h : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  have h1 := Subgroup.relIndex_mul_index h
  have h2 := H.index_mul_card
  have h3 := K.index_mul_card
  have hK : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_left hK
  calc K.index * (H.relIndex K * Nat.card H) = (H.relIndex K * K.index) * Nat.card H := by ring
    _ = H.index * Nat.card H := by rw [h1]
    _ = Nat.card Γ := h2
    _ = K.index * Nat.card K := h3.symm

theorem isSylowOf_iSup_of_iSupIndep {Γ : Type} [Group Γ] [Finite Γ] {ι : Type} [Fintype ι]
    {A S : ι → Subgroup Γ}
    (hcomm : Pairwise fun i j => ∀ x y : Γ, x ∈ A i → y ∈ A j → Commute x y)
    (hind : iSupIndep A) (hS : ∀ i, CFSG.RankThree.PartOne.IsSylowOf 2 (S i) (A i)) :
    CFSG.RankThree.PartOne.IsSylowOf 2 (⨆ i, S i) (⨆ i, A i) := by
  have hle : ∀ i, S i ≤ A i := fun i => (hS i).1
  have hSA : (⨆ i, S i) ≤ ⨆ i, A i := iSup_mono hle
  have hcommS : Pairwise fun i j => ∀ x y : Γ, x ∈ S i → y ∈ S j → Commute x y :=
    fun i j hij x y hx hy => hcomm hij x y (hle i hx) (hle j hy)
  have hindS : iSupIndep S := hind.mono hle
  have hcardA := card_iSup_eq_prod_sylowIndep hcomm hind
  have hcardS := card_iSup_eq_prod_sylowIndep hcommS hindS
  have hpos : 0 < ∏ i, Nat.card (S i) :=
    Finset.prod_pos fun i _ => Nat.card_pos
  have hA : ∀ i, Nat.card (A i) = (S i).relIndex (A i) * Nat.card (S i) :=
    fun i => (relIndex_mul_card_of_le_sylowIndep (hle i)).symm
  have hrel : (⨆ i, S i).relIndex (⨆ i, A i) = ∏ i, (S i).relIndex (A i) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    have e1 := relIndex_mul_card_of_le_sylowIndep hSA
    rw [hcardS, hcardA] at e1
    calc (⨆ i, S i).relIndex (⨆ i, A i) * ∏ i, Nat.card (S i)
        = ∏ i, Nat.card (A i) := e1
      _ = ∏ i, ((S i).relIndex (A i) * Nat.card (S i)) :=
          Finset.prod_congr rfl fun i _ => hA i
      _ = (∏ i, (S i).relIndex (A i)) * ∏ i, Nat.card (S i) := Finset.prod_mul_distrib
  refine ⟨hSA, ?_, ?_⟩
  · rw [IsPGroup.iff_card]
    choose n hn using fun i => IsPGroup.iff_card.mp (hS i).2.1
    refine ⟨∑ i, n i, ?_⟩
    rw [hcardS]
    simp only [hn]
    rw [Finset.prod_pow_eq_pow_sum]
  · rw [hrel]
    intro h
    obtain ⟨i, _, hi⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).1 h
    exact (hS i).2.2 hi

end CFSG.AGLEmbeddingD2.Tits.E23

end
