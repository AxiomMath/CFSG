module

public import CFSG.GF2Type.Smith1979.CaseI25U43

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.Case25.U43Weights

theorem map_sw_mem_of_invariant {𝒦 : Set (Subgroup A4)}
    (hinv : ∀ K ∈ 𝒦, ∀ k : Gen, K.map (sg k).toMonoidHom ∈ 𝒦) {K : Subgroup A4} (hK : K ∈ 𝒦) :
    ∀ w : List Gen, K.map (sw w).toMonoidHom ∈ 𝒦
  | [] => by simpa [sw] using hK
  | k :: w => by
    have h := hinv _ (map_sw_mem_of_invariant hinv hK w) k
    have hs : (sw (k :: w)).toMonoidHom = (sg k).toMonoidHom.comp (sw w).toMonoidHom := rfl
    rw [hs, ← Subgroup.map_map]
    exact h

theorem ten_le_ncard_of_invariant {𝒦 : Set (Subgroup A4)} (hfin : 𝒦.Finite)
    (hinv : ∀ K ∈ 𝒦, ∀ k : Gen, K.map (sg k).toMonoidHom ∈ 𝒦) {K : Subgroup A4} (hK : K ∈ 𝒦)
    (hidx : K.index = 3) : 10 ≤ 𝒦.ncard := by
  refine (ten_le_ncard_orbit K hidx).trans (Set.ncard_le_ncard ?_ hfin)
  rintro _ ⟨w, rfl⟩
  exact map_sw_mem_of_invariant hinv hK w

theorem eq_one_of_invariant (f : A4 →* Multiplicative (ZMod 3))
    (hf : ∀ k x, f (sg k x) = f x) : f = 1 := by
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard3 : Nat.card (Multiplicative (ZMod 3)) = 3 :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 3)
  have hker : f.ker.index = 3 := by
    rw [Subgroup.index_ker]
    have hd : Nat.card f.range ∣ 3 := by
      have := Subgroup.card_subgroup_dvd_card f.range
      rwa [hcard3] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exfalso
      apply hne
      have hbot : f.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      ext x
      have : f x ∈ f.range := ⟨x, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · exact h3
  have hinv : ∀ K ∈ ({f.ker} : Set (Subgroup A4)), ∀ k : Gen,
      K.map (sg k).toMonoidHom ∈ ({f.ker} : Set (Subgroup A4)) := by
    rintro K rfl k
    rw [Set.mem_singleton_iff]
    ext y
    simp only [Subgroup.mem_map, MonoidHom.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show f (sg k x) = 1
      rw [hf, hx]
    · intro hy
      refine ⟨(sg k).symm y, ?_, (sg k).apply_symm_apply y⟩
      have := hf k ((sg k).symm y)
      rw [(sg k).apply_symm_apply, hy] at this
      exact this.symm
  have := ten_le_ncard_of_invariant (Set.finite_singleton _) hinv rfl hker
  simp at this

end CFSG.GF2Type.Smith1979.IdxFour
