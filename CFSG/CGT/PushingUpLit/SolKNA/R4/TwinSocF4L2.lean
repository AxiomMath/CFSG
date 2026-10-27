module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Defs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL2
public import CFSG.ClassicalInvolution.Q3.TL4MF163Gam

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open QuaternionGroup CFSG CFSG.GorensteinWalter
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2)
open CFSG.ClassicalInvolution.Q3

theorem l2_branch {A : Type} [Group A] (T : Subgroup A) [T.Normal] (hT : SmallL2 ↥T)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) {x b : A} (h : QRel8 x b) (ψ : MulAut ↥T)
    (hψ : ψ * ψ = 1) (hx : ψ * MulAut.conjNormal x = MulAut.conjNormal x * ψ)
    (hb : ψ * MulAut.conjNormal b = MulAut.conjNormal b * ψ) :
    ψ = 1 ∨ ψ = MulAut.conjNormal (x ^ 4) := by
  obtain ⟨p, f, K, hKf, hKfin, hp, hpodd, hf, h3, hKcard, ⟨e⟩⟩ := soc_l2_data hT
  haveI : Fact p.Prime := ⟨hp⟩
  have hOdd : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hpodd, hf, hKcard⟩
  have hcard : 3 < Nat.card K := by rw [hKcard]; exact h3
  have h2 : (2 : K) ≠ 0 := by
    have hodd : Odd (Nat.card K) := by rw [hKcard]; exact hpodd.pow
    exact CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hodd
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hOdd hcard
  let Φ : PGammaL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 K hOdd hcard)
      ⟨pGammaL2ToMulAutPSL2_injective K hOdd hcard, hsurj⟩
  let Ψ : MulAut ↥T ≃* PGammaL2 K := (MulAut.congr e).trans Φ.symm
  let θ : A →* PGammaL2 K := Ψ.toMonoidHom.comp MulAut.conjNormal
  have hθ : ∀ g, θ g = Ψ (MulAut.conjNormal g) := fun g => rfl
  have hθinj : ∀ g, θ g = 1 → g = 1 := fun g hg =>
    conjNormal_eq_one hC (Ψ.injective (by rw [← hθ, hg, map_one]))
  have hx4 : (θ (x ^ 2)) ^ 4 = 1 := by
    rw [← map_pow, ← pow_mul, show 2 * 4 = 8 by rfl, h.x8, map_one]
  have hbx : θ b * θ (x ^ 2) * (θ b)⁻¹ = (θ (x ^ 2))⁻¹ := by
    have h1 : b * x ^ 2 * b⁻¹ = (x ^ 2)⁻¹ := by
      calc b * x ^ 2 * b⁻¹ = (b * x * b⁻¹) ^ 2 := (conj_pow).symm
        _ = (x ^ 2)⁻¹ := by rw [h.bx, inv_pow]
    calc θ b * θ (x ^ 2) * (θ b)⁻¹ = θ (b * x ^ 2 * b⁻¹) := by simp [map_mul, map_inv]
      _ = θ ((x ^ 2)⁻¹) := by rw [h1]
      _ = (θ (x ^ 2))⁻¹ := map_inv θ _
  have hb2 : (θ b) ^ 2 = (θ (x ^ 2)) ^ 2 := by
    rw [← map_pow, ← map_pow, sq, h.b2, ← pow_mul]
  let ρ := LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift hx4 hbx hb2
  have hρ2 : ρ (QuaternionGroup.a 2) = θ (x ^ 4) := by
    show (θ (x ^ 2)) ^ (2 : ZMod 4).val = _
    rw [← map_pow, ← pow_mul]
    rfl
  have hψ' : Ψ ψ * Ψ ψ = 1 := by rw [← map_mul, hψ, map_one]
  have hcx : ∀ k : ℕ, Ψ ψ * (θ (x ^ 2)) ^ k = (θ (x ^ 2)) ^ k * Ψ ψ := by
    intro k
    have h1 : Commute (Ψ ψ) (θ x) := by
      show Ψ ψ * θ x = θ x * Ψ ψ
      rw [hθ, ← map_mul, ← map_mul, hx]
    have h2 : Commute (Ψ ψ) ((θ x ^ 2) ^ k) := (h1.pow_right 2).pow_right k
    rw [map_pow θ x 2]
    exact h2.eq
  have hcb : Ψ ψ * θ b = θ b * Ψ ψ := by
    rw [hθ, ← map_mul, ← map_mul, hb]
  have hcomm : ∀ g, Ψ ψ * ρ g = ρ g * Ψ ψ := by
    intro g
    rcases g with k | k
    · show Ψ ψ * (θ (x ^ 2)) ^ k.val = (θ (x ^ 2)) ^ k.val * Ψ ψ
      exact hcx _
    · show Ψ ψ * (θ b * (θ (x ^ 2)) ^ k.val) = θ b * (θ (x ^ 2)) ^ k.val * Ψ ψ
      rw [← mul_assoc, hcb, mul_assoc, hcx, mul_assoc]
  have hρne : ρ (QuaternionGroup.a 2) ≠ 1 := by
    rw [hρ2]
    intro h1
    exact h.x4 (hθinj _ h1)
  rcases TL4.MF163.pgammaL2_eq_of_quat_hom hOdd h2 ρ hρne hψ' hcomm with h1 | h1
  · left
    exact Ψ.injective (by rw [h1, map_one])
  · right
    exact Ψ.injective (by rw [h1, hρ2, hθ])

theorem autCentInv_of_smallL2 {r : ℕ} (hr : 4 ≤ r) {A : Type} [Group A] [Finite A] (T : Subgroup A)
    [T.Normal] (hC : Subgroup.centralizer (T : Set A) = ⊥) (hT : SmallL2 ↥T) {R : Subgroup A}
    {S : Sylow 2 R} {z : A} (hd : TightDatum R S z) (hc : TightClsR r A R S z) {ψ : MulAut ↥T}
    (hψ : ψ * ψ = 1) (hS : ψ ∈ autCentOf T (sylowSet S)) :
    ψ = 1 ∨ ψ = MulAut.conjNormal z := by
  obtain ⟨x, b, hx, hb, h, hxz⟩ := exists_qrel8_of_datum hr hd hc
  rw [mem_autCentOf_iff] at hS
  rw [← hxz]
  exact l2_branch T hT hC h ψ hψ (hS x hx) (hS b hb)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
