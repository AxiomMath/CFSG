module

public import CFSG.ClassicalInvolution.Asc77.AscT7TFAut
public import CFSG.ClassicalInvolution.Asc77.AscT7U6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {R V : Subgroup G} {z : G}

theorem prod_isFAut_inner (hR : IsQuatSub R) (hz : IsUniqueInvolution R z) (hV2 : IsPGroup 2 V)
    (hRV : R ≤ V) (hVR : ∀ y ∈ V, conjSub y R = R) {a b : G} (haV : a ∈ V) (hbV : b ∈ V)
    (hFa : IsFAut R a) (hFb : IsFAut R b) (ha2 : a * a ∈ Subgroup.zpowers z)
    (hb2 : b * b ∈ Subgroup.zpowers z) :
    ∃ v ∈ R, v * v = z ∧ a * v * a⁻¹ = v ∧ b * v * b⁻¹ = v ∧
      ∃ w : G, (w = 1 ∨ w = v) ∧ ∀ r ∈ R, (a * b) * r * (a * b)⁻¹ = w * r * w⁻¹ := by
  obtain ⟨x, y, n, c, hinv⟩ := T7F2.exists_coord hR hz hV2 hVR
  have s : T7F2.Out.Setting R V x y n := ⟨c, hRV, hVR, hinv⟩
  obtain ⟨hn2, hax, j, hay, hj⟩ := T7U.coord_of_isFAut hR hz s haV hFa ha2
  obtain ⟨-, hbx, j', hby, hj'⟩ := T7U.coord_of_isFAut hR hz s hbV hFb hb2
  have hzx : z = x ^ (2 ^ n) := T7U.z_eq_pow_of_coord c hz
  have hz2 : z * z = 1 := hz.sq
  have hzR : z ∈ R := hz.mem
  have hzc : ∀ g : G, conjSub g R = R → g * z * g⁻¹ = z := by
    intro g hg
    have h1 : g * z * g⁻¹ ∈ R := by
      have := conj_mem_conjSub (n := g) hzR
      rwa [hg] at this
    have h2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
      calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    rcases hz.unique _ h1 h2 with h | h
    · exfalso
      apply hz.ne_one
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact h
  have haz : a * z * a⁻¹ = z := hzc a (hVR a haV)
  have hbz : b * z * b⁻¹ = z := hzc b (hVR b hbV)
  have hxz : Commute x z := by rw [hzx]; exact (Commute.refl x).pow_right _
  have hxz2 : ∀ k : ℕ, Even k → z ^ k = 1 := by
    rintro k ⟨m, rfl⟩
    rw [← two_mul, pow_mul, pow_two, hz2, one_pow]
  have hpow : x ^ ((1 : ℤ) + 2 ^ n) = x * z := by
    rw [zpow_add, zpow_one]
    congr 1
    rw [show ((2 : ℤ) ^ n) = ((2 ^ n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← hzx]
  rw [hpow] at hax hbx
  have hjz : ∀ k : ℤ, (x ^ k = 1 ∨ x ^ k = x ^ (2 ^ n)) → x ^ k = 1 ∨ x ^ k = z := by
    intro k hk
    rcases hk with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hzx.symm)
  have hjz' : x ^ j * x ^ j' = 1 ∨ x ^ j * x ^ j' = z := by
    rcases hjz j hj with h1 | h1 <;> rcases hjz j' hj' with h2 | h2
    · left; rw [h1, h2, one_mul]
    · right; rw [h1, h2, one_mul]
    · right; rw [h1, h2, mul_one]
    · left; rw [h1, h2, hz2]
  have hconj_z : ∀ k : ℤ, (x ^ k = 1 ∨ x ^ k = z) → a * x ^ k * a⁻¹ = x ^ k := by
    intro k hk
    rcases hk with h | h
    · rw [h]; group
    · rw [h]; exact haz
  have hex : (a * b) * x * (a * b)⁻¹ = x := by
    calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * (x * z) * a⁻¹ := by rw [hbx]
      _ = (a * x * a⁻¹) * (a * z * a⁻¹) := by group
      _ = (x * z) * z := by rw [hax, haz]
      _ = x := by rw [mul_assoc, hz2, mul_one]
  have hey : (a * b) * y * (a * b)⁻¹ = y * (x ^ j * x ^ j') := by
    calc (a * b) * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      _ = a * (y * x ^ j') * a⁻¹ := by rw [hby]
      _ = (a * y * a⁻¹) * (a * x ^ j' * a⁻¹) := by group
      _ = (y * x ^ j) * x ^ j' := by rw [hay, hconj_z j' (hjz j' hj')]
      _ = y * (x ^ j * x ^ j') := by rw [mul_assoc]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  set v : G := x ^ (2 ^ (m + 1)) with hv
  have hvR : v ∈ R := R.pow_mem c.ha _
  have hvv : v * v = z := by
    rw [hv, ← pow_add, hzx]
    congr 1
    ring
  have hxv : Commute x v := (Commute.refl x).pow_right _
  have hav : a * v * a⁻¹ = v := by
    have h1 : (a * x * a⁻¹) ^ (2 ^ (m + 1)) = a * x ^ (2 ^ (m + 1)) * a⁻¹ := conj_pow
    rw [← h1, hax, hxz.mul_pow, hxz2 _ ⟨2 ^ m, by ring⟩, mul_one]
  have hbv : b * v * b⁻¹ = v := by
    have h1 : (b * x * b⁻¹) ^ (2 ^ (m + 1)) = b * x ^ (2 ^ (m + 1)) * b⁻¹ := conj_pow
    rw [← h1, hbx, hxz.mul_pow, hxz2 _ ⟨2 ^ m, by ring⟩, mul_one]
  have hyv : y * v * y⁻¹ = v⁻¹ := by
    have h1 : (y * x * y⁻¹) ^ (2 ^ (m + 1)) = y * x ^ (2 ^ (m + 1)) * y⁻¹ := conj_pow
    rw [← h1, c.hbab, inv_pow]
  have hvy : v * y * v⁻¹ = y * z := by
    have h1 : y * v⁻¹ * y⁻¹ = v := by
      have := congrArg (fun w => w⁻¹) hyv
      simpa [mul_assoc] using this
    have h2 : y * v⁻¹ = v * y := by
      calc y * v⁻¹ = (y * v⁻¹ * y⁻¹) * y := by group
        _ = v * y := by rw [h1]
    calc v * y * v⁻¹ = (v * y) * v⁻¹ := rfl
      _ = (y * v⁻¹) * v⁻¹ := by rw [h2]
      _ = y * (v * v)⁻¹ := by rw [mul_assoc, ← mul_inv_rev]
      _ = y * z := by rw [hvv]; congr 1; exact inv_eq_of_mul_eq_one_right hz2
  refine ⟨v, hvR, hvv, hav, hbv, ?_⟩
  rcases hjz' with hd | hd
  · refine ⟨1, Or.inl rfl, fun r hr => ?_⟩
    rcases c.cover r hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have h1 := T7T.conj_zpow hex i
      rw [h1]; group
    · have h1 := T7T.conj_zpow hex i
      calc (a * b) * (y * x ^ i) * (a * b)⁻¹
          = ((a * b) * y * (a * b)⁻¹) * ((a * b) * x ^ i * (a * b)⁻¹) := by group
        _ = (y * (x ^ j * x ^ j')) * x ^ i := by rw [hey, h1]
        _ = 1 * (y * x ^ i) * 1⁻¹ := by rw [hd]; group
  · refine ⟨v, Or.inr rfl, fun r hr => ?_⟩
    rcases c.cover r hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have h1 := T7T.conj_zpow hex i
      have h2 : v * x ^ i * v⁻¹ = x ^ i := by
        have : Commute v (x ^ i) := (hxv.symm).zpow_right i
        rw [this.eq]; group
      rw [h1, h2]
    · have h1 := T7T.conj_zpow hex i
      have h2 : v * x ^ i * v⁻¹ = x ^ i := by
        have : Commute v (x ^ i) := (hxv.symm).zpow_right i
        rw [this.eq]; group
      calc (a * b) * (y * x ^ i) * (a * b)⁻¹
          = ((a * b) * y * (a * b)⁻¹) * ((a * b) * x ^ i * (a * b)⁻¹) := by group
        _ = (y * (x ^ j * x ^ j')) * x ^ i := by rw [hey, h1]
        _ = (y * z) * x ^ i := by rw [hd]
        _ = (v * y * v⁻¹) * (v * x ^ i * v⁻¹) := by rw [hvy, h2]
        _ = v * (y * x ^ i) * v⁻¹ := by group

end CFSG.ClassicalInvolution.Asc77.C25V
