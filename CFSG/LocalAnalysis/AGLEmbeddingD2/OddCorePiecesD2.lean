module

public import CFSG.LocalAnalysis.AGLEmbedding.OddCorePieces

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding

section Orbit

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

theorem exists_injective_fixedPiece_ne_bot_of_orbit [Finite A] [Finite V] {p m : ℕ} [Fact p.Prime]
    (hA : ∀ a : A, a ^ p = 1) (hV : ¬ p ∣ Nat.card V) (hnt : ∃ a : A, ∃ v : V, a • v ≠ v)
    {α : MulAut A} {β : MulAut V} (hαβ : ∀ a v, β (a • v) = α a • β v)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p →
      F.map (α ^ k).toMonoidHom ≠ F) :
    ∃ F : Fin m → Subgroup A, Function.Injective F ∧ (∀ j, (F j).index = p) ∧
      ∀ j, (fixedPiece (F j) : Subgroup V) ≠ ⊥ := by
  obtain ⟨F₀, hF₀, hne⟩ := exists_fixedPiece_ne_bot hA hV hnt
  have hmap : ∀ i j : ℕ, i < j → j < m →
      F₀.map (α ^ i).toMonoidHom ≠ F₀.map (α ^ j).toMonoidHom := by
    intro i j hij hjm h
    have hj : α ^ j = α ^ i * α ^ (j - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hj, map_mul_toMonoidHom] at h
    exact hlen (j - i) (by omega) (by omega) F₀ hF₀
      (Subgroup.map_injective (α ^ i).injective h).symm
  refine ⟨fun j => F₀.map (α ^ (j : ℕ)).toMonoidHom, ?_, fun j => ?_, fun j => ?_⟩
  · intro i j hij
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne') with h | h
    · exact hmap i j h j.2 hij
    · exact hmap j i h i.2 hij.symm
  · change (F₀.map (α ^ (j : ℕ)).toMonoidHom).index = p
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact hF₀
  · intro hbot
    obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
    have hmem := map_fixedPiece_le (pow_apply_smul hαβ j) F₀ ⟨w, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hw1 ((β ^ (j : ℕ)).injective (hmem.trans (map_one _).symm))

end Orbit

section Independent

variable {V : Type*} [CommGroup V]

theorem pow_card_le_card_iSup {ι : Type*} [Fintype ι] {W : ι → Subgroup V} (hW : iSupIndep W)
    {b : ℕ} (hb : ∀ i, b ≤ Nat.card (W i)) :
    b ^ Fintype.card ι ≤ Nat.card (⨆ i, W i : Subgroup V) := by
  rw [card_iSup_eq_prod_of_iSupIndep hW, ← Finset.card_univ]
  exact Finset.pow_card_le_prod _ _ _ fun i _ => hb i

theorem pow_two_mul_le_card_iSup {m : ℕ} {W : Fin m → Subgroup V} (hW : iSupIndep W) {s : ℕ}
    (hs : ∀ j, s ^ 2 ≤ Nat.card (W j)) : s ^ (2 * m) ≤ Nat.card (⨆ j, W j : Subgroup V) := by
  simpa only [pow_mul, Fintype.card_fin] using pow_card_le_card_iSup hW hs

end Independent

section Equivariant

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

theorem pow_two_mul_le_card_of_equivariant [Finite A] [Finite V] {s p m : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hV : IsPGroup s V)
    (hnt : ∃ a : A, ∃ v : V, a • v ≠ v) {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v)
    (hlen : ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup A, F.index = p →
      F.map (α ^ k).toMonoidHom ≠ F)
    (hpiece : ∀ F : Subgroup A, F.index = p → (fixedPiece F : Subgroup V) ≠ ⊥ →
      s ^ 2 ≤ Nat.card (fixedPiece F : Subgroup V)) :
    s ^ (2 * m) ≤ Nat.card V := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  have hAp : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hA a⟩
  obtain ⟨a, ha⟩ := hAp.exists_card_eq
  obtain ⟨b, hb⟩ := hV.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    rw [ha, hb]
    exact Nat.coprime_pow_primes a b hp hs hsp.symm
  have hpV : ¬ p ∣ Nat.card V := fun h => by
    rw [hb] at h
    exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp (hp.dvd_of_dvd_pow h)).symm
  obtain ⟨F, hinj, hF, hne⟩ := exists_injective_fixedPiece_ne_bot_of_orbit hA hpV hnt hαβ hlen
  have hind := iSupIndep_fixedPiece (pairwise_sup_eq_top_of_index_eq_prime hp hinj hF) hcop
  exact (pow_two_mul_le_card_iSup hind fun j => hpiece (F j) (hF j) (hne j)).trans
    (Subgroup.card_le_card_group _)

end Equivariant

end CFSG.AGLEmbeddingD2
