module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.HardMathSupport.Curtis.Proving

lemma eq_bot_of_perfect_solvable {K : Type*} [Group K] [Group.IsSolvable K] (H : Subgroup K)
    (h : ⁅H, H⁆ = H) : H = ⊥ := by
  by_contra hne
  have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hne
  rw [h] at hlt
  exact lt_irrefl _ hlt

lemma top_eq_bot_of_perfect {W : Type*} [Group W] [Finite W] {a : ℕ}
    (hperf : ⁅(⊤ : Subgroup W), (⊤ : Subgroup W)⁆ = ⊤) (hcard : Nat.card W ∣ 2 ^ a * 3) :
    (⊤ : Subgroup W) = ⊥ := by
  have hpos : Nat.card W ≠ 0 := (Nat.card_pos).ne'
  obtain ⟨k, m, hmodd, hn⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have hm3 : m ∣ 3 := by
    have hdvd : m ∣ 2 ^ a * 3 := (Dvd.intro_left _ rfl).trans (hn ▸ hcard)
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right a hmodd.coprime_two_right) hdvd)
  rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with rfl | rfl
  ·
    have hp : IsPGroup 2 W := IsPGroup.of_card (by rw [hn, mul_one])
    have : Group.IsSolvable W := by
      have := IsPGroup.isNilpotent hp
      infer_instance
    exact eq_bot_of_perfect_solvable ⊤ hperf
  · obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := W) 2 (n := k) ⟨3, hn⟩
    have hidx : P.index = 3 := by
      have := P.card_mul_index
      rw [hP, hn] at this
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    exfalso
    have hcardα : Nat.card (W ⧸ P) ≤ 4 := by
      rw [show Nat.card (W ⧸ P) = P.index from rfl, hidx]
      norm_num
    have hsolvPerm : Group.IsSolvable (Equiv.Perm (W ⧸ P)) := Equiv.Perm.isSolvable hcardα
    have hH : ⁅(MulAction.toPermHom W (W ⧸ P)).range, (MulAction.toPermHom W (W ⧸ P)).range⁆
        = (MulAction.toPermHom W (W ⧸ P)).range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]
    have hbot := eq_bot_of_perfect_solvable _ hH
    have hPtop : P = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : (MulAction.toPermHom W (W ⧸ P)) g ∈
          (MulAction.toPermHom W (W ⧸ P)).range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hg
      have h2 : (QuotientGroup.mk g : W ⧸ P) = QuotientGroup.mk 1 := by
        have := congrArg (fun σ : Equiv.Perm (W ⧸ P) => σ (QuotientGroup.mk 1)) hg
        simpa [MulAction.toPermHom_apply] using this
      simpa using QuotientGroup.eq.mp h2
    rw [hPtop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)


theorem perfect_eq_bot_of_card_dvd_two_pow_mul_three {G : Type*} [Group G] [Finite G] {a : ℕ}
    (V : Subgroup G) (hV : ⁅V, V⁆ = V) (hcard : Nat.card V ∣ 2 ^ a * 3) : V = ⊥ := by
  have hmap : Subgroup.map V.subtype ⊤ = V := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hperf : ⁅(⊤ : Subgroup V), (⊤ : Subgroup V)⁆ = ⊤ := by
    apply Subgroup.map_injective (f := V.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, hmap, hV]
  have htop := top_eq_bot_of_perfect hperf hcard
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : (⟨x, hx⟩ : V) ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
  rw [htop, Subgroup.mem_bot] at hx'
  simpa using congrArg Subtype.val hx'

end CFSG.HardMathSupport.Curtis.Proving

end
