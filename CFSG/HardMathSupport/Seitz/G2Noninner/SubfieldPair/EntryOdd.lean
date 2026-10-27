module

public import CFSG.RankThree.PartOne.SEITZ6.G2Entry
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.FormOdd
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.WeylOdd

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ6

variable {K : Type} [Field K]

section Entry

variable (k : Subfield K) (hk : 4 ≤ Nat.card k)
  {R : Subgroup (adjointGroup .G2 K)} (hR : ∀ p < 12, ∀ c ∈ k, xp p c ∈ R)

theorem jFormO_mem_of_span {y : RootModule .G2 K}
    (hy : ∀ r ∈ R, ∀ σ ∈ longPos, jFormO K (r • rootVec .G2 K (rt σ)) y ∈ k)
    {x : RootModule .G2 K} (hx : x ∈ Submodule.span k (longOrbit R)) : jFormO K x y ∈ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, σ, hσ, rfl⟩ := hx
    exact hy r hr σ hσ
  | zero => simp [k.zero_mem]
  | add x z _ _ hx hz =>
    rw [map_add, LinearMap.add_apply]
    exact k.add_mem hx hz
  | smul a x _ hx =>
    have : a • x = (a : K) • x := rfl
    rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact k.mul_mem a.2 hx

theorem jFormO_smul_left (r : adjointGroup .G2 K) (x y : RootModule .G2 K) :
    jFormO K (r • x) y = jFormO K x (r⁻¹ • y) := by
  have := jFormO_invariant r x (r⁻¹ • y)
  rwa [smul_inv_smul] at this

theorem smul_chain {m w : adjointGroup .G2 K} {x y z : RootModule .G2 K} {ε₁ ε₂ : K}
    (h1 : m • x = ε₁ • y) (h2 : w • y = ε₂ • z) : (w * m) • x = (ε₂ * ε₁) • z := by
  rw [mul_smul, h1, smul_smul_comm, h2, smul_smul, mul_comm]

include hR in
theorem reach_longO : ∀ σ ∈ longPos, ∃ m ∈ R, ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
    m • rootVec .G2 K (rt 7) = ε • rootVec .G2 K (rt σ) := by
  obtain ⟨hw0, hw1⟩ := weylElement_mem k hR
  obtain ⟨a1, ha1, s73⟩ := weylElement_smul_rootVec_sign (K := K) e0 (t := 7) (by norm_num) reflect_7
  obtain ⟨a2, ha2, s30⟩ := weylElement_smul_rootVec_sign (K := K) e1 (t := 3) (by norm_num) reflect_3
  obtain ⟨a3, ha3, s02⟩ := weylElement_smul_rootVec_sign (K := K) e0 (t := 0) (by norm_num) reflect_0
  obtain ⟨a4, ha4, s26⟩ := weylElement_smul_rootVec_sign (K := K) e1 (t := 2) (by norm_num) reflect_2
  obtain ⟨a5, ha5, s610⟩ := weylElement_smul_rootVec_sign (K := K) e0 (t := 6) (by norm_num) reflect_6
  intro σ hσ
  simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, R.mul_mem hw1 hw0, _, sign_mul_sign ha2 ha1, smul_chain s73 s30⟩
  · exact ⟨_, R.mul_mem hw0 (R.mul_mem hw1 hw0), _, sign_mul_sign ha3 (sign_mul_sign ha2 ha1),
      smul_chain (smul_chain s73 s30) s02⟩
  · exact ⟨_, hw0, _, ha1, s73⟩
  · exact ⟨_, R.mul_mem hw1 (R.mul_mem hw0 (R.mul_mem hw1 hw0)), _,
      sign_mul_sign ha4 (sign_mul_sign ha3 (sign_mul_sign ha2 ha1)),
      smul_chain (smul_chain (smul_chain s73 s30) s02) s26⟩
  · exact ⟨1, R.one_mem, 1, Or.inl rfl, by rw [one_smul, one_smul]⟩
  · exact ⟨_, R.mul_mem hw0 (R.mul_mem hw1 (R.mul_mem hw0 (R.mul_mem hw1 hw0))), _,
      sign_mul_sign ha5 (sign_mul_sign ha4 (sign_mul_sign ha3 (sign_mul_sign ha2 ha1))),
      smul_chain (smul_chain (smul_chain (smul_chain s73 s30) s02) s26) s610⟩

theorem sq_sign {ε : K} (h : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases h with rfl | rfl <;> simp

end Entry

end CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair
