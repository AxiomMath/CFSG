module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

variable {G : Type*} [Group G]

theorem card_inf_centralizer_mul_ncard [Finite G] (K : Subgroup G) (g : G) :
    Nat.card (K ⊓ Subgroup.centralizer {g} : Subgroup G) *
      {m | ∃ k ∈ K, m = k * g * k⁻¹}.ncard = Nat.card K := by
  let _ : MulAction K G := MulAction.compHom G (MulAut.conj.comp K.subtype)
  have hsmul : ∀ (k : K) (m : G), k • m = (k : G) * m * (k : G)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit K g = {m | ∃ k ∈ K, m = k * g * k⁻¹} := by
    ext m
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, hsmul k g⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, hsmul _ g⟩
  have hstab : Nat.card (MulAction.stabilizer K g) =
      Nat.card (K ⊓ Subgroup.centralizer {g} : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨s.1.1, Subgroup.mem_inf.2 ⟨s.1.2, ?_⟩⟩
        invFun := fun s => ⟨⟨s.1, (Subgroup.mem_inf.1 s.2).1⟩, ?_⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    · have h1 : s.1 • g = g := MulAction.mem_stabilizer_iff.1 s.2
      rw [hsmul] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (s.1 : G) * g = s.1 * g * (s.1 : G)⁻¹ * s.1 := by group
        _ = g * s.1 := by rw [h1]
    · rw [MulAction.mem_stabilizer_iff, hsmul]
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 s.2).2
      change (s : G) * g * (s : G)⁻¹ = g
      rw [h2, mul_inv_cancel_right]
  rw [← hstab, ← horb, ← MulAction.index_stabilizer, Subgroup.card_mul_index]

theorem ncard_conj_class_dvd [Finite G] (K : Subgroup G) (g : G) :
    {m | ∃ k ∈ K, m = k * g * k⁻¹}.ncard ∣ Nat.card K :=
  ⟨_, (card_inf_centralizer_mul_ncard K g).symm.trans (mul_comm _ _)⟩

theorem exists_pow_modEq_of_prime_orderOf [Finite G] {V : Subgroup G} {x : G} {p m : ℕ}
    [hp : Fact p.Prime] (hx : orderOf x = p) (hV : Nat.card V = 2 ^ m)
    (hn : ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hnc : ∃ v ∈ V, x * v ≠ v * x) :
    ∃ d < m, 2 ^ d ≡ 2 ^ m [MOD p] := by
  classical
  have := Fintype.ofFinite V
  let f : Function.End V := fun v => ⟨x * v * x⁻¹, hn v v.2⟩
  have hfk : ∀ k : ℕ, ∀ v : V, ((f ^ k) v : G) = x ^ k * v * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero =>
      intro v
      show (v : G) = x ^ 0 * v * (x ^ 0)⁻¹
      simp
    | succ k ih =>
      intro v
      rw [pow_succ]
      show (((f ^ k) (f v) : V) : G) = _
      rw [ih, pow_succ]
      show x ^ k * (x * v * x⁻¹) * (x ^ k)⁻¹ = _
      group
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hf : f ^ p ^ 1 = 1 := by
    funext v
    apply Subtype.ext
    show (((f ^ p ^ 1) v : V) : G) = (v : G)
    rw [pow_one, hfk, hxp]
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  let C : Subgroup V :=
    { carrier := {v : V | x * v = v * x}
      mul_mem' := by
        intro a b ha hb
        have ha' : x * (a : G) = a * x := ha
        have hb' : x * (b : G) = b * x := hb
        show x * ((a : G) * b) = ((a : G) * b) * x
        calc x * ((a : G) * b) = (x * a) * b := by group
          _ = a * (x * b) := by rw [ha']; group
          _ = a * (b * x) := by rw [hb']
          _ = a * b * x := by group
      one_mem' := by show x * (1 : G) = 1 * x; group
      inv_mem' := by
        intro a ha
        have ha' : x * (a : G) = a * x := ha
        show x * (a : G)⁻¹ = (a : G)⁻¹ * x
        calc x * (a : G)⁻¹ = (a : G)⁻¹ * (a * x) * (a : G)⁻¹ := by group
          _ = (a : G)⁻¹ * (x * a) * (a : G)⁻¹ := by rw [ha']
          _ = (a : G)⁻¹ * x := by group }
  have hcardC : Fintype.card (Function.fixedPoints f) = Nat.card C := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h
      have := congrArg Subtype.val h
      change x * v * x⁻¹ = v at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    · intro h
      apply Subtype.ext
      change x * v * x⁻¹ = v
      rw [mul_inv_eq_iff_eq_mul]
      exact h
  have hdvd : Nat.card C ∣ 2 ^ m := by
    have h1 : Nat.card C ∣ Nat.card V := Subgroup.card_subgroup_dvd_card C
    rwa [hV] at h1
  obtain ⟨d, hd, hCd⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hdm : d < m := by
    by_contra hlt
    have hge : m ≤ d := not_lt.1 hlt
    have hle : 2 ^ d ≤ 2 ^ m := Nat.le_of_dvd (by positivity) (hCd ▸ hdvd)
    have hd' : d = m := by
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
      omega
    subst hd'
    have hcard : Nat.card C = Nat.card V := by rw [hCd, hV]
    have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C hcard
    obtain ⟨v, hv, hxv⟩ := hnc
    have : (⟨v, hv⟩ : V) ∈ C := by rw [htop]; trivial
    exact hxv this
  refine ⟨d, hdm, ?_⟩
  have h1 : Fintype.card V = 2 ^ m := by rw [Fintype.card_eq_nat_card, hV]
  rw [h1, hcardC, hCd] at hmod
  exact hmod.symm

theorem no_pow_modEq_277 : ∀ d < 12, ¬ 2 ^ d ≡ 2 ^ 12 [MOD 277] := by decide

theorem no_pow_modEq_443 : ∀ d < 12, ¬ 2 ^ d ≡ 2 ^ 12 [MOD 443] := by decide

end CFSG.EvenSporadicStandard.J4Std
