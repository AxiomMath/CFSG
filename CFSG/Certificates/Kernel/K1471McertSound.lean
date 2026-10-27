module

public import Certificates.Data.Kernel.K1471Mcert
public import CFSG.RankThree.Asc83Table.MatCert

public section

namespace CFSG.KC.K1471

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
open CFSG.RankThree.Asc83Table.Native
open scoped commutatorElement

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d) [Inhabited M]

theorem inv_eq_sq {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) : x⁻¹ = x ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx)

include Sp in
theorem sylFusionWitness_of_mcert {sA sB : String} {n : ℕ} {prog : List Op}
    {rx ry rn on a b k : ℕ}
    (h : mcertCheck O sA sB ⟨n, prog, fusFacts rx ry rn on a b k⟩ = true)
    (ha : a < 3) (hb : b < 3) (hk : k < 3) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ x y g : (certMonoid p d sA sB)ˣ, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ Commute ⁅x, y⁆ x ∧
      Commute ⁅x, y⁆ y ∧ ⁅x, y⁆ ≠ 1 ∧ ∃ a b k : ℕ, a < 3 ∧ b < 3 ∧ k < 3 ∧
        (a ≠ 0 ∨ b ≠ 0) ∧ g * ⁅x, y⁆ * g⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k := by
  set C : MCert := ⟨n, prog, fusFacts rx ry rn on a b k⟩ with hCdef
  have fX : MFact.ord rx 3 ∈ C.facts := by simp [C, fusFacts]
  have fY : MFact.ord ry 3 ∈ C.facts := by simp [C, fusFacts]
  have fN : MFact.ord rn on ∈ C.facts := by simp [C, fusFacts]
  have cX : MFact.conj rx (fusZ rx ry) (fusZ rx ry) ∈ C.facts := by simp [C, fusFacts]
  have cY : MFact.conj ry (fusZ rx ry) (fusZ rx ry) ∈ C.facts := by simp [C, fusFacts]
  have cN : MFact.conj rn (fusZ rx ry) ([(rx, a), (ry, b)] ++ wordPow (fusZ rx ry) k) ∈
      C.facts := by simp [C, fusFacts, wordPow]
  have nZ : MFact.ne (fusZ rx ry) [] 0 ∈ C.facts := by simp [C, fusFacts]
  have oXY : HasOrd C [(rx, a), (ry, b)] := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    exacts [⟨3, fX⟩, ⟨3, fY⟩]
  have oZ : HasOrd C (fusZ rx ry) := by
    intro q hq
    simp only [fusZ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    exacts [⟨3, fX⟩, ⟨3, fY⟩, ⟨3, fX⟩, ⟨3, fY⟩]
  set x := regUnit Sp h rx
  set y := regUnit Sp h ry
  have hx : x ^ 3 = 1 := regUnit_pow Sp h fX
  have hy : y ^ 3 = 1 := regUnit_pow Sp h fY
  have hz : wordUnit Sp h (fusZ rx ry) = ⁅x, y⁆ := by
    simp only [fusZ, wordUnit_cons, wordUnit_nil, pow_one, mul_one, commutatorElement_def,
      inv_eq_sq hx, inv_eq_sq hy, mul_assoc]
    rfl
  have comm : ∀ {r : ℕ}, MFact.conj r (fusZ rx ry) (fusZ rx ry) ∈ C.facts →
      MFact.ord r 3 ∈ C.facts → Commute ⁅x, y⁆ (regUnit Sp h r) := by
    intro r hc ho
    have e := regUnit_conj Sp h hc ho oZ oZ
    rw [hz] at e
    exact (mul_inv_eq_iff_eq_mul.1 e).symm
  have hg := regUnit_conj Sp h cN fN oZ (hasOrd_append oXY (hasOrd_wordPow oZ k))
  rw [wordUnit_append, wordUnit_wordPow, hz] at hg
  simp only [wordUnit_cons, wordUnit_nil, mul_one, ← mul_assoc] at hg
  refine ⟨x, y, regUnit Sp h rn, hx, hy, comm cX fX, comm cY fY, ?_, a, b, k, ha, hb, hk, hab, hg⟩
  have hne := regUnit_ne Sp h nZ oZ (hasOrd_nil C)
  rwa [hz, wordUnit_nil] at hne

end CFSG.KC.K1471

end
