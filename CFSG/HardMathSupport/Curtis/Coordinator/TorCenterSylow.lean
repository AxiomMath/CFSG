module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Subgroup

theorem abelian_of_max_isPGroup {Y : Type*} [Group Y] [Finite Y] {N X T : Subgroup Y} {p : ℕ}
    [Fact p.Prime] (hX : IsPGroup p X) (hXN : X ≤ N)
    (hmax : ∀ Y' : Subgroup Y, IsPGroup p Y' → Y' ≤ N → Nat.card Y' ≤ Nat.card X)
    (hT : IsPGroup p T) (hTN : T ≤ N) (hTX : Nat.card X ≤ Nat.card T)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  classical
  let X' : Subgroup N := X.subgroupOf N
  let T' : Subgroup N := T.subgroupOf N
  have hX'c : Nat.card X' = Nat.card X := Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv
  have hT'c : Nat.card T' = Nat.card T := Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv
  have hX' : IsPGroup p X' := hX.of_equiv (subgroupOfEquivOfLe hXN).symm
  have hT' : IsPGroup p T' := hT.of_equiv (subgroupOfEquivOfLe hTN).symm
  have himg : ∀ Q : Subgroup N, IsPGroup p Q → Nat.card Q ≤ Nat.card X := fun Q hQ => by
    have h1 := hmax (Q.map N.subtype) (hQ.map _) (by
      rintro _ ⟨q, -, rfl⟩; exact q.2)
    rwa [Subgroup.card_map_of_injective N.subtype_injective] at h1
  obtain ⟨P, hXP⟩ := hX'.exists_le_sylow
  obtain ⟨P', hTP⟩ := hT'.exists_le_sylow
  have hP : X' = P := Subgroup.eq_of_le_of_card_ge hXP (by
    have := himg (P : Subgroup N) P.isPGroup'
    omega)
  have hP' : T' = P' := Subgroup.eq_of_le_of_card_ge hTP (by
    have := himg (P' : Subgroup N) P'.isPGroup'
    omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N P P'
  intro a ha b hb
  have key : ∀ c ∈ X, ∃ t ∈ T', ∃ c' : N, (c' : Y) = c ∧ t = g * c' * g⁻¹ := fun c hc => by
    have hcP : (⟨c, hXN hc⟩ : N) ∈ (P : Subgroup N) := by
      rw [← hP]; exact hc
    have hmem : g * ⟨c, hXN hc⟩ * g⁻¹ ∈ ((g • P : Sylow p N) : Subgroup N) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hcP
    rw [hg, ← hP'] at hmem
    exact ⟨_, hmem, ⟨c, hXN hc⟩, rfl, rfl⟩
  obtain ⟨ta, hta, a', rfl, rfl⟩ := key a ha
  obtain ⟨tb, htb, b', rfl, rfl⟩ := key b hb
  have h1 := hcomm (g * a' * g⁻¹ : N) hta (g * b' * g⁻¹ : N) htb
  have h1' : (g * a' * g⁻¹ : N) * (g * b' * g⁻¹) = (g * b' * g⁻¹) * (g * a' * g⁻¹) :=
    Subtype.ext h1
  have h2 : a' * b' = b' * a' := by
    have := congrArg (fun z : N => g⁻¹ * z * g) h1'
    simpa [mul_assoc] using this
  exact congrArg Subtype.val h2

end CFSG.HardMathSupport.Curtis.Coordinator
