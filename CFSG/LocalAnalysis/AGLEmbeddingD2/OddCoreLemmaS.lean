module

public import CFSG.LocalAnalysis.AGLEmbedding.OddCorePiecesAux
import CFSG.LocalAnalysis.AGLEmbedding.OddCorePieces

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding

theorem two_le_log_fixedPiece {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]
    [Finite A] [Finite V] {p s : ℕ} (hp : p.Prime) (hs : s.Prime) (hsp : s ≠ p)
    (hA : ∀ a : A, a ^ p = 1) (hV : ∀ v : V, v ^ s = 1) {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v) (m lam : ℕ) (hα : ∀ a, (α ^ m) a = a ^ lam)
    (hlam : ¬ p ∣ lam - 1) {F : Subgroup A} (hF : F.index = p)
    (hne : (fixedPiece F : Subgroup V) ≠ ⊥) : s ^ 2 ≤ Nat.card (fixedPiece F : Subgroup V) := by
  have := Fact.mk hp
  have := Fact.mk hs
  by_contra hlt
  rw [not_le] at hlt
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    have hAp : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hA a⟩
    have hVp : IsPGroup s V := fun v => ⟨1, by rw [pow_one]; exact hV v⟩
    obtain ⟨a, ha⟩ := hAp.exists_card_eq
    obtain ⟨b, hb⟩ := hVp.exists_card_eq
    rw [ha, hb]
    exact Nat.coprime_pow_primes a b hp hs hsp.symm
  set W : Subgroup V := fixedPiece F
  have hWcard : Nat.card W = s := by
    obtain ⟨k, hk⟩ := (show IsPGroup s W from fun w => ⟨1, by
      rw [pow_one]; exact Subtype.ext (hV w)⟩).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq W (by simpa using hk))
    have hk2 : k < 2 := by
      by_contra h
      rw [not_lt] at h
      exact absurd hlt (not_lt.mpr (hk ▸ Nat.pow_le_pow_right hs.pos h))
    rw [hk, show k = 1 by omega, pow_one]
  have hgen : ∀ u ∈ W, u ≠ 1 → ∀ w ∈ W, ∃ j : ℤ, u ^ j = w := by
    intro u hu hu1 w hw
    have hord : orderOf u = s := by
      rcases (Nat.dvd_prime hs).mp (orderOf_dvd_of_pow_eq_one (hV u)) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hu1
      · exact h
    have hzW : Subgroup.zpowers u = W :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu) (by rw [Nat.card_zpowers, hord,
        hWcard])
    exact Subgroup.mem_zpowers_iff.mp (hzW ▸ hw)
  have hFmap : F.map (α ^ m).toMonoidHom = F := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      change (α ^ m) a ∈ F
      rw [hα]
      exact pow_mem ha lam
    · rw [Subgroup.card_map_of_injective (α ^ m).injective]
  have hθW : ∀ w ∈ W, (β ^ m) w ∈ W := fun w hw => by
    have h := map_fixedPiece_le (pow_apply_smul hαβ m) F ⟨w, hw, rfl⟩
    rwa [hFmap] at h
  obtain ⟨x, hx⟩ : ∃ x : A, x ∉ F := by
    by_contra hall
    push Not at hall
    have hFtop : F = ⊤ := eq_top_iff.mpr fun a _ => hall a
    rw [hFtop, Subgroup.index_top] at hF
    exact hp.one_lt.ne hF
  obtain ⟨w₀, hw₀, hw₀1⟩ := (Subgroup.bot_or_exists_ne_one W).resolve_left hne
  have hu : (β ^ m) w₀ ∈ W := hθW w₀ hw₀
  have hu1 : (β ^ m) w₀ ≠ 1 := fun h => hw₀1 ((β ^ m).injective (h.trans (map_one _).symm))
  have hxu : x • (β ^ m) w₀ ∈ W := smul_mem_fixedPiece x hu
  have hxu1 : x • (β ^ m) w₀ ≠ 1 := fun h =>
    hu1 (MulAction.injective x (h.trans (smul_one x).symm))
  have hcomm : (β ^ m) (x • w₀) = x • (β ^ m) w₀ := by
    obtain ⟨a, ha⟩ := hgen w₀ hw₀ hw₀1 ((β ^ m) w₀) hu
    obtain ⟨b, hb⟩ := hgen w₀ hw₀ hw₀1 (x • w₀) (smul_mem_fixedPiece x hw₀)
    calc (β ^ m) (x • w₀) = (β ^ m) (w₀ ^ b) := by rw [hb]
      _ = ((β ^ m) w₀) ^ b := map_zpow _ _ _
      _ = (w₀ ^ a) ^ b := by rw [ha]
      _ = (w₀ ^ b) ^ a := by rw [← zpow_mul, ← zpow_mul, mul_comm]
      _ = (x • w₀) ^ a := by rw [hb]
      _ = x • (w₀ ^ a) := (smul_zpow' x w₀ a).symm
      _ = x • (β ^ m) w₀ := by rw [ha]
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    exact hlam (by simp)
  have hkey : x ^ (lam - 1) • (x • (β ^ m) w₀) = x • (β ^ m) w₀ := by
    rw [← mul_smul, pow_sub_one_mul hlam0, ← hα x, ← pow_apply_smul hαβ m x w₀, hcomm]
  have hy : ∀ w ∈ W, x ^ (lam - 1) • w = w := fun w hw => by
    obtain ⟨j, rfl⟩ := hgen _ hxu hxu1 w hw
    rw [smul_zpow', hkey]
  have hxW : ∀ w ∈ W, x • w = w := fun w hw => by
    obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hlam).symm hp.one_lt
    have hxj : x = (x ^ (lam - 1)) ^ j := by
      rw [← pow_mul, pow_eq_pow_mod _ (hA x), hj, pow_one]
    have hmem : (x ^ (lam - 1)) ^ j ∈ MulAction.stabilizer A w :=
      Subgroup.pow_mem _ ((MulAction.mem_stabilizer_iff).mpr (hy w hw)) j
    rw [← hxj] at hmem
    exact (MulAction.mem_stabilizer_iff).mp hmem
  obtain ⟨u₀, hu₀, hu₀eq⟩ := exists_smul_mul_inv_eq hp hF hcop hx hw₀
  rw [hxW u₀ hu₀, mul_inv_cancel] at hu₀eq
  exact hw₀1 hu₀eq.symm

end CFSG.AGLEmbeddingD2
