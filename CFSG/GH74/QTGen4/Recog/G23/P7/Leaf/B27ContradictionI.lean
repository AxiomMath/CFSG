module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Defs
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionA

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.GH74.QTGen4.Recog.G23.P7.B27A

variable {G : Type} [Group G]

theorem cube_one_of_H [Finite G] {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hF : HFacts H H₁ H₂ e)
    (x : G) (hx : x ∈ H) (k : ℕ) (hk : x ^ (3 ^ k) = 1) : x ^ 3 = 1 := by
  have hSH : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hx
  have hord : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) hord
  obtain ⟨hdvd, hex⟩ := hF.odd_sub (Subgroup.zpowers x) hSH hodd
  by_cases h9 : Nat.card (Subgroup.zpowers x) = 9
  · obtain ⟨h, -, hmem⟩ := hex h9
    have hPS : (Psub e).map (MulAut.conj h).toMonoidHom ≤ Subgroup.zpowers x := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
      exact hmem p hp
    have hcardP : Nat.card ↥((Psub e).map (MulAut.conj h).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hF.card_P]
    have heq : (Psub e).map (MulAut.conj h).toMonoidHom = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hPS (by rw [hcardP, h9])
    have hxmem : x ∈ (Psub e).map (MulAut.conj h).toMonoidHom := by
      rw [heq]
      exact Subgroup.mem_zpowers x
    obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hxmem
    have hp3 : p ^ 3 = 1 := hF.elem_P.2 p hp
    rw [← hpx]
    show (h * p * h⁻¹) ^ 3 = 1
    rw [conj_pow, hp3, mul_one, mul_inv_cancel]
  · have hdvd3 : orderOf x ∣ 3 := by
      rw [← Nat.card_zpowers]
      have hm : Nat.card (Subgroup.zpowers x) ∈ Nat.divisors 9 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hdiv] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h
      · rw [h]; exact one_dvd _
      · rw [h]
      · exact absurd h h9
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd3

theorem V_abstract {V : Type} [CommGroup V] [Finite V] (hV : Nat.card V = 81)
    (α ζ τ : V →* V) (hα : ∀ v, α (α (α v)) = v) (hζ : ∀ v, ζ (ζ v) = v)
    (hτinv : ∀ v, τ v = v⁻¹) (hζfix : ∀ v, ζ v = v → v ^ 3 = 1)
    (hτζfix : ∀ v, τ (ζ v) = v → v ^ 3 = 1) :
    (∀ v : V, v ^ 3 = 1) ∧ 9 ≤ Nat.card {v : V // α v = v} := by
  have hexp : ∀ v : V, v ^ 3 = 1 := by
    intro v
    set a := v * ζ v with ha_def
    set b := v * (ζ v)⁻¹ with hb_def
    have ha : ζ a = a := by
      rw [ha_def, map_mul, hζ, mul_comm]
    have hb : τ (ζ b) = b := by
      have hzb : ζ b = b⁻¹ := by
        rw [hb_def, map_mul, map_inv, hζ, mul_inv_rev, inv_inv, mul_comm]
      rw [hzb, hτinv, inv_inv]
    have hab : a * b = v * v := by
      rw [ha_def, hb_def, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    have hv81 : v ^ 81 = 1 := by
      rw [← hV]
      exact pow_card_eq_one'
    have hv : v = a ^ 41 * b ^ 41 := by
      have h1 : (v * v) ^ 41 = v := by
        rw [← pow_two, ← pow_mul]
        calc v ^ (2 * 41) = v ^ 81 * v := by rw [← pow_succ]
          _ = v := by rw [hv81, one_mul]
      rw [← hab, mul_pow] at h1
      exact h1.symm
    have ha3 : a ^ 3 = 1 := hζfix a ha
    have hb3 : b ^ 3 = 1 := hτζfix b hb
    have e1 : (a ^ 41) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ha3, one_pow]
    have e2 : (b ^ 41) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hb3, one_pow]
    rw [hv, mul_pow, e1, e2, mul_one]
  refine ⟨hexp, ?_⟩
  let aW : Additive V →+ Additive V := (α : V →* V).toAdditive
  have hαW : ∀ x : Additive V, aW (aW (aW x)) = x := fun x => hα (Additive.toMul x)
  have hexpW : ∀ x : Additive V, (3 : ℕ) • x = 0 := by
    intro x
    have h := hexp (Additive.toMul x)
    have h2 : Additive.ofMul ((Additive.toMul x) ^ 3) = (3 : ℕ) • x := by
      rw [ofMul_pow]
      rfl
    rw [← h2]
    have h3 : Additive.ofMul ((Additive.toMul x) ^ 3) = Additive.ofMul 1 := by rw [h]
    rw [h3]
    rfl
  let Tadd : Additive V →+ Additive V := aW - AddMonoidHom.id (Additive V)
  have hT3 : ∀ x : Additive V, Tadd (Tadd (Tadd x)) = 0 := by
    intro x
    have key : Tadd (Tadd (Tadd x)) = aW (aW (aW x)) - x + (3 : ℕ) • (aW x - aW (aW x)) := by
      simp only [Tadd, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub]
      abel
    rw [key, hαW, hexpW, sub_self, zero_add]
  have hcard : 9 ≤ Nat.card Tadd.ker :=
    card_ker_ge_nine Tadd hT3 (by
      rw [Nat.card_congr (Additive.ofMul : V ≃ Additive V).symm, hV])
  have hkerc : Nat.card Tadd.ker = Nat.card {v : V // α v = v} := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨Additive.toMul x.1, by
          have hx := x.2
          rw [AddMonoidHom.mem_ker] at hx
          simp only [Tadd, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero] at hx
          exact hx⟩
        invFun := fun y => ⟨Additive.ofMul y.1, by
          rw [AddMonoidHom.mem_ker]
          simp only [Tadd, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]
          exact y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [← hkerc]
  exact hcard

end CFSG.GH74.QTGen4.Recog.G23.P7
