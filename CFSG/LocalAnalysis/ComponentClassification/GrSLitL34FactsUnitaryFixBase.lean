
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Multipliers.KernelStructure
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {E : Type*} [Group E]

def fixT0 (q : E →* Equiv.Perm (Fin 42)) (β : E ≃* E) : Subgroup E where
  carrier := {e | q e ∈ T0 ∧ β e = e}
  one_mem' := ⟨by rw [map_one]; exact T0.one_mem, map_one β⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul]; exact T0.mul_mem ha.1 hb.1,
    by rw [map_mul, ha.2, hb.2]⟩
  inv_mem' := fun {a} ha => ⟨by rw [map_inv]; exact T0.inv_mem ha.1, by rw [map_inv, ha.2]⟩

theorem mem_fixT0 {q : E →* Equiv.Perm (Fin 42)} {β : E ≃* E} {e : E} :
    e ∈ fixT0 q β ↔ q e ∈ T0 ∧ β e = e := Iff.rfl

theorem pow_four_eq (e : E) : e ^ 4 = e * e * (e * e) := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem sup_eq_of_card {F K Y : Subgroup E} (hK : K ≤ F) (hY : Y ≤ F) (hKY : K ⊓ Y = ⊥)
    (hF : Nat.card F = 8) [Finite F]
    (hc : (Nat.card K = 2 ∧ Nat.card Y = 4) ∨ (Nat.card K = 4 ∧ Nat.card Y = 2)) :
    K ⊔ Y = F := by
  have hle : K ⊔ Y ≤ F := sup_le hK hY
  have : Finite ↥(K ⊔ Y) := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have h8 : Nat.card ↥(K ⊔ Y) ∣ 8 := hF ▸ Subgroup.card_dvd_of_le hle
  have hKd : Nat.card K ∣ Nat.card ↥(K ⊔ Y) := Subgroup.card_dvd_of_le le_sup_left
  have hYd : Nat.card Y ∣ Nat.card ↥(K ⊔ Y) := Subgroup.card_dvd_of_le le_sup_right
  have h4 : 4 ∣ Nat.card ↥(K ⊔ Y) := by
    rcases hc with ⟨-, h⟩ | ⟨h, -⟩
    · exact h ▸ hYd
    · exact h ▸ hKd
  have hcases : Nat.card ↥(K ⊔ Y) = 4 ∨ Nat.card ↥(K ⊔ Y) = 8 := by
    have hpos : 0 < Nat.card ↥(K ⊔ Y) := Nat.card_pos
    have hle8 : Nat.card ↥(K ⊔ Y) ≤ 8 := Nat.le_of_dvd (by norm_num) h8
    obtain ⟨k, hk⟩ := h4
    interval_cases h : Nat.card ↥(K ⊔ Y) <;> omega
  rcases hcases with h | h
  · exfalso
    rcases hc with ⟨hk2, hy4⟩ | ⟨hk4, hy2⟩
    · have hYeq : Y = K ⊔ Y := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h, hy4])
      have hKle : K ≤ K ⊓ Y := le_inf le_rfl (hYeq ▸ le_sup_left)
      rw [hKY, le_bot_iff] at hKle
      rw [hKle, Subgroup.card_bot] at hk2
      omega
    · have hKeq : K = K ⊔ Y := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hk4])
      have hYle : Y ≤ K ⊓ Y := le_inf (hKeq ▸ le_sup_right) le_rfl
      rw [hKY, le_bot_iff] at hYle
      rw [hYle, Subgroup.card_bot] at hy2
      omega
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h, hF])

theorem isCyclic_of_card_le_two {Z T : Subgroup E} [Finite Z] (hZc : Z ≤ center E)
    (h4 : ∀ z ∈ Z, z ^ 4 = 1) (hT : ∀ z, z ∈ T ↔ z ∈ Z ∧ z * z = 1) (h2 : Nat.card T ≤ 2) :
    IsCyclic Z := by
  have hcomm : ∀ a b : Z, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (mem_center_iff.mp (hZc a.2) b).symm)
  let sq : Z →* Z := MonoidHom.mk' (fun z => z * z) fun a b => by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm b a]
      _ = a * a * (b * b) := by group
  have hker : Nat.card sq.ker = Nat.card T := by
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1.1, (hT _).2 ⟨z.1.2, congrArg Subtype.val z.2⟩⟩
        invFun := fun t => ⟨⟨t.1, ((hT _).1 t.2).1⟩, Subtype.ext ((hT _).1 t.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : sq.range ≤ sq.ker := by
    rintro _ ⟨z, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show z.1 * z.1 * (z.1 * z.1) = 1
    rw [← pow_four_eq]
    exact h4 _ z.2
  have hcard : Nat.card Z ≤ 4 := by
    have h1 := Subgroup.card_ker_mul_card_range sq
    have h2' := Subgroup.card_le_of_le hrange
    calc Nat.card Z = Nat.card sq.ker * Nat.card sq.range := h1.symm
      _ ≤ 2 * 2 := Nat.mul_le_mul (hker ▸ h2) (h2'.trans (hker ▸ h2))
  by_cases hex : ∃ z ∈ Z, z * z ≠ 1
  · obtain ⟨z, hz, hz2⟩ := hex
    have hord : orderOf (⟨z, hz⟩ : Z) = 4 := by
      rw [orderOf_mk]
      have hdvd : orderOf z ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (h4 z hz)
      obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      interval_cases m
      · rw [pow_zero, orderOf_eq_one_iff] at hmo
        exact absurd (by rw [hmo, one_mul]) hz2
      · have := pow_orderOf_eq_one z
        rw [hmo, pow_one, pow_two] at this
        exact absurd this hz2
      · exact hmo
    have hge : 4 ≤ Nat.card Z := by
      rw [← hord]
      exact orderOf_le_card
    exact isCyclic_of_orderOf_eq_card _ (hord.trans (le_antisymm hge hcard))
  · push Not at hex
    have hle : Nat.card Z ≤ 2 := by
      have : Nat.card Z = Nat.card T := Nat.card_congr
        { toFun := fun z => ⟨z.1, (hT _).2 ⟨z.2, hex _ z.2⟩⟩
          invFun := fun t => ⟨t.1, ((hT _).1 t.2).1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [this]
      exact h2
    have hpos : 0 < Nat.card Z := Nat.card_pos
    interval_cases h : Nat.card Z
    · have : Subsingleton Z := (Nat.card_eq_one_iff_unique.mp h).1
      exact isCyclic_of_subsingleton
    · have : Fact (Nat.Prime (Nat.card Z)) := ⟨h ▸ Nat.prime_two⟩
      exact isCyclic_of_prime_card rfl

theorem orderOf_eq_four {X : Type*} [Group X] {g : X} (h4 : g ^ 4 = 1) (h2 : g * g ≠ 1) :
    orderOf g = 4 := by
  have hdvd : orderOf g ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h4
  obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases m
  · rw [pow_zero, orderOf_eq_one_iff] at hmo
    exact absurd (by rw [hmo, one_mul]) h2
  · have := pow_orderOf_eq_one g
    rw [hmo, pow_one, pow_two] at this
    exact absurd this h2
  · exact hmo

theorem orderOf_eq_two' {X : Type*} [Group X] {g : X} (h2 : g * g = 1) (h1 : g ≠ 1) :
    orderOf g = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two, h2]) h1

theorem eq_one_of_mem_zpowers_ker {X : Type*} [Group X] (q : E →* X) {m : E}
    (hm : orderOf (q m) = orderOf m) {y : E} (hy : y ∈ zpowers m) (hk : y ∈ q.ker) : y = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [MonoidHom.mem_ker, map_zpow, ← orderOf_dvd_iff_zpow_eq_one, hm] at hk
  exact orderOf_dvd_iff_zpow_eq_one.mp hk

theorem inf_ker_eq_bot {X : Type*} [Group X] (q : E →* X) (F : Subgroup E) {m : E}
    (hm : orderOf (q m) = orderOf m) : F ⊓ q.ker ⊓ zpowers m = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  exact (Subgroup.mem_bot).2 (eq_one_of_mem_zpowers_ker q hm hy.2 hy.1.2)

private theorem psi_four : ∀ d : Multiplicative (ZMod 4) × Multiplicative (ZMod 4), d ^ 4 = 1 := by
  decide

private theorem psi_key : ∀ d : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    (1, Multiplicative.ofAdd 2) * (d * d) =
      (1, Multiplicative.ofAdd 3) * (1, Multiplicative.ofAdd 3) * d⁻¹ * d⁻¹ := by
  decide

end CFSG.ComponentClassification.GrSLit.L34Facts
