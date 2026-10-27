module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6Row
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6Core
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2InnerDiagConj

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)

theorem listMask_e6SignReps_one :
    listMask (τ := .E6) (e6SignReps.getD 1 []) = e6BitsD5 := by
  decide

theorem listMask_e6SignReps_two :
    listMask (τ := .E6) (e6SignReps.getD 2 []) = e6BitsA5 := by
  decide

theorem listMask_e6SignReps_zero :
    listMask (τ := .E6) (e6SignReps.getD 0 []) = fun _ => false := by
  decide

theorem length_e6SignReps : e6SignReps.length = 3 := rfl


theorem exists_conj_rootDiagAut_of_rootChar {K : Type} [Field K] {b c : Fin (Tag.rank .E6) → Kˣ}
    {w : WeylGroup .E6} (hw : ∀ v : Fin (Tag.rank .E6) → ℤ, rootChar b (w • v) = rootChar c v) :
    ∃ n : adjointGroup .E6 K, rootDiagAut .E6 K b =
      MulAut.conj n * rootDiagAut .E6 K c * (MulAut.conj n)⁻¹ := by
  have hd := (rootDiagUnit_eq_conj_canonicalRep_iff (K := K) b c w).2 hw
  set N := canonicalRep (coxeterSystem .E6) K w with hN
  refine ⟨⟨N, canonicalRep_mem_adjointGroup (coxeterSystem .E6) K w⟩,
    MulEquiv.ext fun g => Subtype.ext ?_⟩
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, coe_rootDiagAut,
    Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [hd]
  group

theorem burgRow_E6_innerDiag {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) {α : MulAut (adjointGroup .E6 K)}
    {g : adjointGroup .E6 K} {a : Fin (Tag.rank .E6) → Kˣ}
    (hαg : ∀ h : adjointGroup .E6 K, (α h : ModGL .E6 K) =
      (g : ModGL .E6 K) * rootDiagUnit .E6 a * h * (rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹)
    (hα : orderOf α = 2) : BurgCoreFor α ∨ BurgTorusFor α := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (one_le_and_three_le_of_card hp hp2 hK).1 hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  obtain ⟨ψ, b, hb, hψ⟩ := exists_conj_eq_rootDiagAut_of_innerDiagonal
    (Or.inr (Or.inr (Or.inl rfl))) hodd hαg hα2
  have hαψ : α = ψ⁻¹ * rootDiagAut .E6 K b * ψ⁻¹⁻¹ := by
    rw [← hψ]
    group
  obtain ⟨ρ, hρ, w, hw, -⟩ := exists_conj_toralCentralizer_of_orbitCheck hK2 e6SignOrbit_check hb
  obtain ⟨n, hn⟩ := exists_conj_rootDiagAut_of_rootChar hw
  have hrow : BurgCoreFor (rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ [])))) ∨
      BurgTorusFor (rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ [])))) →
      BurgCoreFor α ∨ BurgTorusFor α := by
    rintro (h | h)
    · left
      rw [hαψ, hn, show ψ⁻¹ * (MulAut.conj n *
          rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ []))) *
            (MulAut.conj n)⁻¹) * ψ⁻¹⁻¹ = (ψ⁻¹ * MulAut.conj n) *
          rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ []))) *
            (ψ⁻¹ * MulAut.conj n)⁻¹ by group]
      exact h.conj _
    · right
      rw [hαψ, hn, show ψ⁻¹ * (MulAut.conj n *
          rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ []))) *
            (MulAut.conj n)⁻¹) * ψ⁻¹⁻¹ = (ψ⁻¹ * MulAut.conj n) *
          rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ []))) *
            (ψ⁻¹ * MulAut.conj n)⁻¹ by group]
      exact h.conj _
  rw [length_e6SignReps] at hρ
  interval_cases ρ
  ·
    exfalso
    have h1 : rootDiagAut .E6 K (bitsTuple (listMask (τ := .E6) (e6SignReps.getD 0 []))) = 1 := by
      rw [listMask_e6SignReps_zero]
      have : bitsTuple (K := K) (fun _ : Fin (Tag.rank .E6) => false) = 1 := by
        funext j
        simp [bitsTuple]
      rw [this]
      exact (rootDiagAutHom .E6 K).map_one
    rw [h1, mul_one, mul_inv_cancel] at hn
    rw [hαψ, hn, mul_one, inv_inv, inv_mul_cancel, orderOf_one] at hα
    exact absurd hα (by decide)
  · apply hrow
    rw [listMask_e6SignReps_one]
    rcases Nat.lt_or_ge (Nat.card K) 5 with h | h
    · have hc3 : Nat.card K = 3 := by
        obtain ⟨-, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
        obtain ⟨k, hk⟩ := hodd
        omega
      exact Or.inl (burgCoreFor_E6_t1_three hc3)
    · exact Or.inr (burgTorusFor_E6_t1 hp hp2 hK h)
  · apply hrow
    rw [listMask_e6SignReps_two]
    exact Or.inl (burgCoreFor_E6_t2 hK2)

end CFSG.ComponentClassification.Burgoyne.E2
