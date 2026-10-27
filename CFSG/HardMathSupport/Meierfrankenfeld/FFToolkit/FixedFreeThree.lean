module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.CenterIndex

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

theorem card_modEq_one_of_fpf {V : Type} [CommGroup V] [Finite V] {z : MulAut V}
    (hz3 : z ^ 3 = 1) (hfpf : ∀ v : V, z v = v → v = 1) : Nat.card V ≡ 1 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers z) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hz3, one_zpow, Subgroup.coe_one]
  have hmod := hP.card_modEq_card_fixedPoints V
  have hfix : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers z) V) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, fun g => map_one (g : MulAut V)⟩⟩⟩
    have ha : (a : V) = 1 := hfpf a (a.2 ⟨z, Subgroup.mem_zpowers z⟩)
    have hb : (b : V) = 1 := hfpf b (b.2 ⟨z, Subgroup.mem_zpowers z⟩)
    exact Subtype.ext (ha.trans hb.symm)
  rwa [hfix] at hmod

theorem exists_card_eq_four_pow {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    {z : MulAut V} (hz3 : z ^ 3 = 1) (hfpf : ∀ v : V, z v = v → v = 1) :
    ∃ k : ℕ, Nat.card V = 4 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one, sq]; exact hV v⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hmod := card_modEq_one_of_fpf hz3 hfpf
  rw [hn] at hmod
  obtain ⟨k, hk⟩ := even_of_two_pow_modEq_one hmod
  refine ⟨k, ?_⟩
  rw [hn, hk, ← two_mul, pow_mul]
  norm_num

theorem index_fixV_eq_four_pow {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {z : MulAut W} (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1)
    (X : Subgroup (MulAut W)) (hX : ∀ x ∈ X, x * z = z * x) :
    ∃ k : ℕ, (fixV X).index = 4 ^ k := by
  set U := fixV X with hU
  have hzU : ∀ u ∈ U, z u ∈ U := by
    intro u hu
    rw [hU, mem_fixV] at hu ⊢
    intro x hx
    have h1 := congrArg (fun f : MulAut W => f u) (hX x hx)
    simp only [MulAut.mul_apply] at h1
    rw [h1, hu x hx]
  have hz2 : ∀ w : W, z (z (z w)) = w := by
    intro w
    have := congrArg (fun f : MulAut W => f w) hz3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hstab : z ∈ stabSub U := by
    intro u
    constructor
    · intro h
      have h1 := hzU _ (hzU _ h)
      rwa [hz2] at h1
    · exact hzU u
  set zU := resHom U ⟨z, hstab⟩ with hzUdef
  have hzU3 : zU ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨z, hstab⟩ : stabSub U) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hzUfpf : ∀ u : U, zU u = u → u = 1 := by
    intro u hu
    apply Subtype.ext
    exact hfpf u (congrArg Subtype.val hu)
  have hU2 : ∀ u : U, u * u = 1 := fun u => Subtype.ext (by simpa using hW u)
  obtain ⟨m, hm⟩ := exists_card_eq_four_pow hU2 hzU3 hzUfpf
  obtain ⟨n, hn⟩ := exists_card_eq_four_pow hW hz3 hfpf
  have hmul := Subgroup.card_mul_index U
  rw [hm, hn] at hmul
  have hmn : m ≤ n := by
    by_contra hlt
    have h1 : 4 ^ n < 4 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h2 : 4 ^ m ≤ 4 ^ m * U.index := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite))
    omega
  refine ⟨n - m, ?_⟩
  have h4 : 4 ^ n = 4 ^ m * 4 ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [h4] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
