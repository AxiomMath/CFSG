module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open

theorem exists_fixed_of_involutive' {α : Type*} [Finite α] {f : α → α}
    (hf : Function.Involutive f) (hodd : Odd (Nat.card α)) : ∃ a, f a = a := by
  classical
  let := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card]
    exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hsq : hf.toPerm f ^ 2 ^ 1 = 1 := by
    ext x
    simp only [pow_one, pow_two, Equiv.Perm.mul_apply, Function.Involutive.coe_toPerm, hf x,
      Equiv.Perm.one_apply]
  exact Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hnot hsq

variable {G : Type*} [Group G]

theorem exists_mul_mem_centralizer_of_odd [Finite G] {O : Subgroup G} (hO : Odd (Nat.card O))
    {a : G} (ha2 : a * a = 1) (haO : a ∈ Subgroup.normalizer (O : Set G)) {k : G}
    (hk : k⁻¹ * (a * k * a⁻¹) ∈ O) : ∃ o ∈ O, a * (k * o) * a⁻¹ = k * o := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hmem : ∀ o ∈ O, k⁻¹ * a * k * o * a⁻¹ ∈ O := by
    intro o ho
    have h1 : a * o * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp haO o).mp ho
    have e : k⁻¹ * a * k * o * a⁻¹ = k⁻¹ * (a * k * a⁻¹) * (a * o * a⁻¹) := by group
    rw [e]
    exact O.mul_mem hk h1
  let φ : O → O := fun o => ⟨k⁻¹ * a * k * o * a⁻¹, hmem o o.2⟩
  have hφ : Function.Involutive φ := by
    intro o
    apply Subtype.ext
    change k⁻¹ * a * k * (k⁻¹ * a * k * (o : G) * a⁻¹) * a⁻¹ = o
    calc k⁻¹ * a * k * (k⁻¹ * a * k * (o : G) * a⁻¹) * a⁻¹ =
        k⁻¹ * (a * a) * k * (o : G) * (a⁻¹ * a⁻¹) := by group
      _ = o := by rw [ha2, hainv, ha2]; group
  obtain ⟨o, ho⟩ := exists_fixed_of_involutive' hφ hO
  refine ⟨o, o.2, ?_⟩
  have h := congrArg Subtype.val ho
  change k⁻¹ * a * k * (o : G) * a⁻¹ = o at h
  calc a * (k * (o : G)) * a⁻¹ = k * (k⁻¹ * a * k * (o : G) * a⁻¹) := by group
    _ = k * o := by rw [h]

theorem nonempty_quotEquiv_of_surjective_of_odd {H Q : Type*} [Group H] [Finite H] [Group Q]
    (ψ : H →* Q) (hψ : Function.Surjective ψ) (hker : Odd (Nat.card ψ.ker))
    (hQ : classicalInvolutionOddCore Q = ⊥) :
    Nonempty (H ⧸ classicalInvolutionOddCore H ≃* Q) := by
  have hle : ψ.ker ≤ classicalInvolutionOddCore H := le_sSup ⟨inferInstance, hker⟩
  have hge : classicalInvolutionOddCore H ≤ ψ.ker := by
    intro x hx
    have hN : ((classicalInvolutionOddCore H).map ψ).Normal :=
      Subgroup.Normal.map inferInstance ψ hψ
    have hodd : Odd (Nat.card ((classicalInvolutionOddCore H).map ψ)) :=
      (CFSG.ComponentClassification.OddCore.odd_card H).of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hle' : (classicalInvolutionOddCore H).map ψ ≤ classicalInvolutionOddCore Q :=
      le_sSup ⟨hN, hodd⟩
    have h1 := hle' (Subgroup.mem_map_of_mem ψ hx)
    rw [hQ, Subgroup.mem_bot] at h1
    exact h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm hge hle)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
