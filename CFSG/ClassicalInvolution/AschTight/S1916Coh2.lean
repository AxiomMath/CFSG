module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem eq_or_eq_inv_of_mul_self_eq {Z₀ : Subgroup G} {z : G} (hz : IsUniqueInvolution Z₀ z)
    (hab : ∀ x ∈ Z₀, ∀ y ∈ Z₀, x * y = y * x) {x y : G} (hx : x ∈ Z₀) (hy : y ∈ Z₀)
    (hx2 : x * x = z) (hy2 : y * y = z) : x = y ∨ x = y⁻¹ := by
  have hc := hab x hx y⁻¹ (Z₀.inv_mem hy)
  have h1 : (x * y⁻¹) * (x * y⁻¹) = 1 := by
    calc (x * y⁻¹) * (x * y⁻¹) = x * (y⁻¹ * x) * y⁻¹ := by group
      _ = x * (x * y⁻¹) * y⁻¹ := by rw [← hc]
      _ = (x * x) * (y * y)⁻¹ := by group
      _ = 1 := by rw [hx2, hy2, mul_inv_cancel]
  rcases hz.unique _ (Z₀.mul_mem hx (Z₀.inv_mem hy)) h1 with h | h
  · left
    calc x = x * y⁻¹ * y := by group
      _ = y := by rw [h, one_mul]
  · right
    calc x = x * y⁻¹ * y := by group
      _ = z * y := by rw [h]
      _ = (y * y) * y := by rw [hy2]
      _ = (y * y) * (y * y) * y⁻¹ := by group
      _ = y⁻¹ := by rw [hy2, hz.sq, one_mul]

theorem commute_of_not_square {Z₀ : Subgroup G} (hZcyc : IsCyclic Z₀) (hZ2 : IsPGroup 2 Z₀)
    {w s : G} (hw : w ∈ Z₀) (hsw : s * w = w * s) (hsq : ¬ ∃ x ∈ Z₀, x * x = w) :
    ∀ y ∈ Z₀, s * y = y * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := hZcyc.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w, hw⟩)
  have hi' : (g : G) ^ i = w := by simpa using congrArg Subtype.val hi
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' i
  · exact absurd ⟨(g : G) ^ j, Z₀.zpow_mem g.2 j, by rw [← zpow_add, ← hi', hj, two_mul]⟩ hsq
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZ2 g
  have hgk : (g : G) ^ ((2 : ℤ) ^ k) = 1 := by
    rw [show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← hk,
      ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
  obtain ⟨u, v, huv⟩ : IsCoprime i ((2 : ℤ) ^ k) :=
    IsCoprime.pow_right ⟨1, -j, by rw [hj]; ring⟩
  have hgw : (g : G) = w ^ u := by
    calc (g : G) = (g : G) ^ (u * i + v * 2 ^ k) := by rw [huv, zpow_one]
      _ = ((g : G) ^ i) ^ u * ((g : G) ^ ((2 : ℤ) ^ k)) ^ v := by
          rw [zpow_add, mul_comm u i, mul_comm v, zpow_mul, zpow_mul]
      _ = w ^ u := by rw [hgk, one_zpow, mul_one, hi']
  have hsg : s * (g : G) = (g : G) * s := by
    rw [hgw]
    exact (Commute.zpow_right (show Commute s w from hsw) u).eq
  intro y hy
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have hl' : (g : G) ^ l = y := by simpa using congrArg Subtype.val hl
  rw [← hl']
  exact (Commute.zpow_right (show Commute s (g : G) from hsg) l).eq

theorem mul_self_mem_of_dihedral {Z₀ : Subgroup G} {z q s : G} (hz : IsUniqueInvolution Z₀ z)
    (hab : ∀ x ∈ Z₀, ∀ y ∈ Z₀, x * y = y * x) (hy4 : ∃ y ∈ Z₀, y * y = z)
    (hq : ∀ x ∈ Z₀, q * x * q⁻¹ = x⁻¹) (hθ : ∀ x ∈ Z₀, s * x * s⁻¹ ∈ Z₀)
    (hsz : s * z * s⁻¹ = z) (hs2 : s * s ∈ Z₀ ∨ q⁻¹ * (s * s) ∈ Z₀) : s * s ∈ Z₀ := by
  rcases hs2 with h | h
  · exact h
  exfalso
  obtain ⟨y, hy, hyz⟩ := hy4
  have hθy : (s * y * s⁻¹) * (s * y * s⁻¹) = z := by
    calc (s * y * s⁻¹) * (s * y * s⁻¹) = s * (y * y) * s⁻¹ := by group
      _ = z := by rw [hyz, hsz]
  have e1 : (s * s) * y * (s * s)⁻¹ = s * (s * y * s⁻¹) * s⁻¹ := by group
  have h2 : (s * s) * y * (s * s)⁻¹ = y := by
    rcases eq_or_eq_inv_of_mul_self_eq hz hab (hθ y hy) hy hθy hyz with h1 | h1
    · rw [e1, h1, h1]
    · have e2 : s * y⁻¹ * s⁻¹ = (s * y * s⁻¹)⁻¹ := by group
      rw [e1, h1, e2, h1, inv_inv]
  have hxy : (q⁻¹ * (s * s)) * y * (q⁻¹ * (s * s))⁻¹ = y := by
    rw [hab _ h y hy]
    group
  have h3 : (s * s) * y * (s * s)⁻¹ = y⁻¹ := by
    calc (s * s) * y * (s * s)⁻¹ =
        q * ((q⁻¹ * (s * s)) * y * (q⁻¹ * (s * s))⁻¹) * q⁻¹ := by group
      _ = y⁻¹ := by rw [hxy, hq y hy]
  rw [h2] at h3
  apply hz.ne_one
  rw [← hyz]
  calc y * y = y * y⁻¹ := by rw [← h3]
    _ = 1 := mul_inv_cancel y

theorem exists_norm_mem_of_dihedral {Z₀ : Subgroup G} (hZcyc : IsCyclic Z₀) (hZ2 : IsPGroup 2 Z₀)
    {z q s : G} (hz : IsUniqueInvolution Z₀ z) (hab : ∀ x ∈ Z₀, ∀ y ∈ Z₀, x * y = y * x)
    (hy4 : ∃ y ∈ Z₀, y * y = z) (hq : ∀ x ∈ Z₀, q * x * q⁻¹ = x⁻¹)
    (hq2 : q * q = 1 ∨ q * q = z) (hθ : ∀ x ∈ Z₀, s * x * s⁻¹ ∈ Z₀) (hsz : s * z * s⁻¹ = z)
    (hsq : q⁻¹ * (s * q * s⁻¹) ∈ Z₀) (hs2 : s * s ∈ Z₀ ∨ q⁻¹ * (s * s) ∈ Z₀) :
    ∃ c : G, (c ∈ Z₀ ∨ q⁻¹ * c ∈ Z₀) ∧
      (s * c * s⁻¹ * (s * s) * c = 1 ∨ s * c * s⁻¹ * (s * s) * c = z) := by
  have hs2Z := mul_self_mem_of_dihedral hz hab hy4 hq hθ hsz hs2
  by_cases hsqr : ∃ x ∈ Z₀, x * x = s * s
  ·
    obtain ⟨x, hx, hxx⟩ := hsqr
    refine ⟨x⁻¹, Or.inl (Z₀.inv_mem hx), ?_⟩
    have hw : s * x⁻¹ * s⁻¹ * (s * s) * x⁻¹ = (s * x * s⁻¹)⁻¹ * x := by
      rw [← hxx]
      group
    have hwZ : (s * x * s⁻¹)⁻¹ * x ∈ Z₀ := Z₀.mul_mem (Z₀.inv_mem (hθ x hx)) hx
    have hc := hab _ (Z₀.inv_mem (hθ x hx)) x hx
    have hw2 : ((s * x * s⁻¹)⁻¹ * x) * ((s * x * s⁻¹)⁻¹ * x) = 1 := by
      calc ((s * x * s⁻¹)⁻¹ * x) * ((s * x * s⁻¹)⁻¹ * x)
          = (s * x * s⁻¹)⁻¹ * (x * (s * x * s⁻¹)⁻¹) * x := by group
        _ = (s * x * s⁻¹)⁻¹ * ((s * x * s⁻¹)⁻¹ * x) * x := by rw [← hc]
        _ = (s * (x * x) * s⁻¹)⁻¹ * (x * x) := by group
        _ = 1 := by rw [hxx]; group
    rw [hw]
    rcases hz.unique _ hwZ hw2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  ·
    have hcomm := commute_of_not_square (s := s) hZcyc hZ2 hs2Z (by group) hsqr
    have hθid : ∀ y ∈ Z₀, s * y * s⁻¹ = y := fun y hy => by rw [hcomm y hy]; group
    refine ⟨q, Or.inr (by rw [inv_mul_cancel]; exact Z₀.one_mem), ?_⟩
    obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = q⁻¹ * (s * q * s⁻¹) := ⟨_, rfl⟩
    have hy₁Z : y₁ ∈ Z₀ := hy₁ ▸ hsq
    have hθq : s * q * s⁻¹ = q * y₁ := by rw [hy₁]; group
    have hq' : ∀ x ∈ Z₀, q⁻¹ * x * q = x⁻¹ := fun x hx => by
      have h1 := hq x⁻¹ (Z₀.inv_mem hx)
      rw [inv_inv] at h1
      calc q⁻¹ * x * q = q⁻¹ * (q * x⁻¹ * q⁻¹) * q := by rw [h1]
        _ = x⁻¹ := by group
    have hθ2q : (s * s) * q * (s * s)⁻¹ = q * (y₁ * y₁) := by
      have e : (s * s) * q * (s * s)⁻¹ = s * (s * q * s⁻¹) * s⁻¹ := by group
      have e2 : s * (q * y₁) * s⁻¹ = (s * q * s⁻¹) * (s * y₁ * s⁻¹) := by group
      rw [e, hθq, e2, hθq, hθid y₁ hy₁Z, mul_assoc]
    have hθ2q' : (s * s) * q * (s * s)⁻¹ = (s * s) * (s * s) * q := by
      have h1 := hq (s * s)⁻¹ (Z₀.inv_mem hs2Z)
      rw [inv_inv] at h1
      calc (s * s) * q * (s * s)⁻¹ = (s * s) * (q * (s * s)⁻¹ * q⁻¹) * q := by group
        _ = (s * s) * (s * s) * q := by rw [h1]
    have hy₁2 : y₁ * y₁ = ((s * s) * (s * s))⁻¹ := by
      have h1 : y₁ * y₁ = q⁻¹ * ((s * s) * (s * s)) * q := by
        calc y₁ * y₁ = q⁻¹ * (q * (y₁ * y₁)) := by group
          _ = q⁻¹ * ((s * s) * (s * s) * q) := by rw [← hθ2q, hθ2q']
          _ = q⁻¹ * ((s * s) * (s * s)) * q := by group
      rw [h1, hq' _ (Z₀.mul_mem hs2Z hs2Z)]
    have hwZ : y₁ * (s * s) ∈ Z₀ := Z₀.mul_mem hy₁Z hs2Z
    have hc := hab _ hs2Z _ hy₁Z
    have hw2 : (y₁ * (s * s)) * (y₁ * (s * s)) = 1 := by
      calc (y₁ * (s * s)) * (y₁ * (s * s)) = y₁ * ((s * s) * y₁) * (s * s) := by group
        _ = y₁ * (y₁ * (s * s)) * (s * s) := by rw [hc]
        _ = (y₁ * y₁) * ((s * s) * (s * s)) := by group
        _ = 1 := by rw [hy₁2, inv_mul_cancel]
    have htarget : s * q * s⁻¹ * (s * s) * q = (y₁ * (s * s))⁻¹ * (q * q) := by
      have h1 := hq _ hwZ
      calc s * q * s⁻¹ * (s * s) * q = q * (y₁ * (s * s)) * q := by rw [hθq]; group
        _ = (q * (y₁ * (s * s)) * q⁻¹) * (q * q) := by group
        _ = (y₁ * (s * s))⁻¹ * (q * q) := by rw [h1]
    rw [htarget]
    rcases hz.unique _ hwZ hw2 with h | h <;> rcases hq2 with h' | h'
    · left; rw [h, h', inv_one, one_mul]
    · right; rw [h, h', inv_one, one_mul]
    · right; rw [h, h', mul_one, inv_eq_of_mul_eq_one_right hz.sq]
    · left; rw [h, h', inv_mul_cancel]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
