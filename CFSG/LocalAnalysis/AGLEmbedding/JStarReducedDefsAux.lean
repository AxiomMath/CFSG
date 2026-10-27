module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbits

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem exists_ne_zero_sq_ne_one_galoisField {p n : ℕ} [Fact p.Prime] (hn : 2 ≤ n) :
    ∃ a : GaloisField p n, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  have hp : p.Prime := Fact.out
  have hcard : 4 ≤ Nat.card (GaloisField p n) := by
    rw [GaloisField.card p n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  obtain ⟨x, hx⟩ : IsCyclic (GaloisField p n)ˣ := inferInstance
  refine ⟨x, Units.ne_zero x, fun h => ?_⟩
  have h1 : orderOf x ≤ 2 := orderOf_le_of_pow_eq_one zero_lt_two (Units.ext (by simpa using h))
  rw [orderOf_eq_card_of_forall_mem_zpowers hx] at h1
  have h2 := Nat.card_eq_card_units_add_one (GaloisField p n)
  omega

theorem psl2GF_isPerfect {p n : ℕ} [Fact p.Prime] (hn : 2 ≤ n) : Group.IsPerfect (PSL2GF p n) :=
  ⟨SL2Simple.PSL_commutator_eq_top (exists_ne_zero_sq_ne_one_galoisField hn)⟩

theorem ReducedNongeneration.sylow_le_normalCore_normalizer_component {p : ℕ} {X : Type*}
    [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀)
    {L : Subgroup X} (hL : IsComponentOf L ⊤) :
    (R : Subgroup X) ≤ (Subgroup.normalizer (L : Set X)).normalCore := by
  intro r hr b
  have hL' : IsComponentOf (L.map (MulAut.conj b⁻¹).toMonoidHom) ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj b⁻¹) L).mpr hL
  have hrN := h.sylow_le_normalizer_component hL' hr
  rw [Subgroup.mem_normalizer_iff] at hrN ⊢
  intro z
  have key : ∀ y, y ∈ L.map (MulAut.conj b⁻¹).toMonoidHom ↔ b * y * b⁻¹ ∈ L := by
    intro y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have e1 : b * (b⁻¹ * z * b) * b⁻¹ = z := by group
  have e2 : b * (r * (b⁻¹ * z * b) * r⁻¹) * b⁻¹ = b * r * b⁻¹ * z * (b * r * b⁻¹)⁻¹ := by group
  rw [← e2, ← key, ← hrN, key, e1]

end CFSG.AGLEmbedding
