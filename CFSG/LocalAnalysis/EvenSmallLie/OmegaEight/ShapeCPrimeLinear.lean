module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeTrans

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

theorem card_V6 : Nat.card V6 = 64 := by
  rw [Nat.card_eq_fintype_card]
  simp

theorem card_ne_zero_V6 : Nat.card {v : V6 | v ≠ 0} = 63 := by
  classical
  have h : ({v | v ≠ 0} : Set V6) = ↑(Finset.univ.erase (0 : V6)) := by
    ext v
    simp
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ← Nat.card_eq_fintype_card, card_V6]

section Order3


theorem order3_facts : bmulVec 6 6 (genRows .plus 0) 1 = 1 ∧
    (∀ x < 64, bmulVec 6 6 (genRows .plus 0) (bmulVec 6 6 (genRows .plus 0)
      (bmulVec 6 6 (genRows .plus 0) x)) = x) ∧ bmulVec 6 6 (genRows .plus 0) 2 ≠ 2 := by
  have h := order3Check_eq
  simp only [order3Check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem genMat_plus_zero_fix : genMat .plus 0 *ᵥ toVec 6 1 = toVec 6 1 := by
  rw [genMat, mulVec_toVec, order3_facts.1]

theorem genMat_plus_zero_cube (v : V6) :
    genMat .plus 0 *ᵥ (genMat .plus 0 *ᵥ (genMat .plus 0 *ᵥ v)) = v := by
  conv_lhs => rw [← toVec_vecBits v]
  rw [genMat, mulVec_toVec, mulVec_toVec, mulVec_toVec, order3_facts.2.1 _ (vecBits_lt v),
    toVec_vecBits]

theorem genMat_plus_zero_ne : genMat .plus 0 *ᵥ toVec 6 2 ≠ toVec 6 2 := by
  rw [genMat, mulVec_toVec]
  exact fun h => order3_facts.2.2 (toVec_injective (bmulVec_lt _ _) (by norm_num) h)

end Order3

namespace Setting

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G} {c : G}
  {v₀ : ℕ} (hS : Setting ε t L U Q P a ψ p c v₀)
include hS

theorem card_range_eq [Finite G]
    (hZ : ∀ v, v ∈ Zset t Q ψ) : Nat.card hS.affHom.range = 64 * oBound ε := by
  classical
  have hZ' : ∀ s, qfV ε s = 0 → s ∈ Zset t Q ψ := fun s _ => hZ s
  have hcardZ : Nat.card (Zset t Q ψ) = 64 := by
    rw [Set.eq_univ_of_forall hZ, Nat.card_univ, card_V6]
  have hge := hS.le_card_range hZ'
  rw [hcardZ] at hge
  have e := MulAction.orbitProdStabilizerEquivGroup hS.affHom.range (0 : V6)
  have hle : Nat.card hS.affHom.range ≤ 64 * oBound ε := by
    rw [← Nat.card_congr e, Nat.card_prod]
    refine Nat.mul_le_mul ?_ ?_
    · rw [← card_V6]
      exact Nat.card_le_card_of_injective _ Subtype.val_injective
    · have hmem : ∀ σ : MulAction.stabilizer hS.affHom.range (0 : V6),
          ((σ : hS.affHom.range) : Equiv.Perm V6) ∈ orthGroup ε := by
        intro σ
        obtain ⟨g, hg⟩ := (σ : hS.affHom.range).2
        have h0 : ((σ : hS.affHom.range) : Equiv.Perm V6) 0 = 0 := σ.2
        rw [← hg] at h0 ⊢
        exact hS.affHom_mem_orthGroup h0
      have hinj : Function.Injective fun σ : MulAction.stabilizer hS.affHom.range (0 : V6) =>
          (⟨((σ : hS.affHom.range) : Equiv.Perm V6), hmem σ⟩ : orthGroup ε) := by
        intro σ τ h
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (Subtype.ext h)
      exact (Nat.card_le_card_of_injective _ hinj).trans (card_orthGroup_le ε)
  omega

@[expose] noncomputable def linHom : Kgrp t Q →* Equiv.Perm V6 where
  toFun g :=
    { toFun := lin ψ g
      invFun := lin ψ (g : G)⁻¹
      left_inv := fun v => hS.rad.lin_inv' g.2.2 v
      right_inv := fun v => hS.rad.lin_inv g.2.2 v }
  map_one' := Equiv.ext fun v => hS.rad.lin_one v
  map_mul' g h := Equiv.ext fun v => hS.rad.lin_mul g.2.2 h.2.2 v

theorem linHom_apply (g : Kgrp t Q) (v : V6) : hS.linHom g v = lin ψ g v := rfl

theorem linHom_mem_linGroup (g : Kgrp t Q) : hS.linHom g ∈ linGroup :=
  fun x y => hS.rad.lin_add g.2.2 x y

theorem ker_linHom_eq (hno : ∀ y, Equiv.addRight y ∈ hS.affHom.range → y = 0) :
    hS.linHom.ker = hS.affHom.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hg
    have hlin : ∀ v, lin ψ g v = v := fun v => congrArg (fun σ : Equiv.Perm V6 => σ v) hg
    have htr : hS.affHom g = Equiv.addRight (aff t ψ g 0) := Equiv.ext fun v => by
      change aff t ψ g v = v + aff t ψ g 0
      rw [hS.aff_eq g.2, hlin, add_comm]
    have h0 := hno _ ⟨g, htr⟩
    rw [htr, h0]
    exact Equiv.ext fun v => by simp
  · intro hg
    have haff : ∀ v, aff t ψ g v = v := fun v => congrArg (fun σ : Equiv.Perm V6 => σ v) hg
    refine Equiv.ext fun v => ?_
    change lin ψ g v = v
    have h := hS.aff_eq g.2 v
    rw [haff, haff 0, zero_add] at h
    exact h.symm

theorem card_range_linHom [Finite G]
    (hZ : ∀ v, v ∈ Zset t Q ψ)
    (hno : ∀ y, Equiv.addRight y ∈ hS.affHom.range → y = 0) :
    Nat.card hS.linHom.range = 64 * oBound ε := by
  have h1 := Subgroup.card_ker_mul_card_range hS.linHom
  have h2 := Subgroup.card_ker_mul_card_range hS.affHom
  rw [hS.ker_linHom_eq hno, ← h2] at h1
  rw [← hS.card_range_eq hZ]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem orderOf_linHom_p_zero (hε : ε = .plus) :
    orderOf (hS.linHom ⟨p 0, hS.P_le_Kgrp (hS.rad.p_mem 0)⟩) = 3 ∧
      hS.linHom ⟨p 0, hS.P_le_Kgrp (hS.rad.p_mem 0)⟩ (toVec 6 1) = toVec 6 1 := by
  subst hε
  have happ : ∀ v, hS.linHom ⟨p 0, hS.P_le_Kgrp (hS.rad.p_mem 0)⟩ v = genMat .plus 0 *ᵥ v :=
    fun v => hS.rad.lin_p 0 v
  refine ⟨?_, by rw [happ]; exact genMat_plus_zero_fix⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Equiv.ext fun v => ?_) fun h => ?_
  · rw [pow_succ, pow_two, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply,
      Function.comp_apply, happ, happ, happ, genMat_plus_zero_cube, Equiv.Perm.coe_one, id]
  · have h2 := congrArg (fun σ : Equiv.Perm V6 => σ (toVec 6 2)) h
    simp only [happ, Equiv.Perm.coe_one, id] at h2
    exact genMat_plus_zero_ne h2

theorem false_of_no_translation [Finite G]
    (hZ : ∀ v, v ∈ Zset t Q ψ)
    (hno : ∀ y, Equiv.addRight y ∈ hS.affHom.range → y = 0) : False := by
  classical
  have hX : Nat.card hS.linHom.range = 64 * oBound ε := hS.card_range_linHom hZ hno
  have hXlin : ∀ σ ∈ hS.linHom.range, σ ∈ linGroup := by
    rintro σ ⟨g, rfl⟩
    exact hS.linHom_mem_linGroup g
  have hPX : ∀ x (hx : x ∈ P), hS.linHom ⟨x, hS.P_le_Kgrp hx⟩ ∈ hS.linHom.range :=
    fun x hx => ⟨_, rfl⟩
  have hinj : ∀ σ ∈ hS.linHom.range, ∀ v, σ v = 0 → v = 0 := fun σ hσ v h =>
    σ.injective (h.trans (map_zero_of_mem_linGroup (hXlin σ hσ)).symm)
  by_cases hpres : ∀ σ ∈ hS.linHom.range, ∀ s : V6, s ≠ 0 → qfV ε s = 0 → qfV ε (σ s) = 0
  · have hle : hS.linHom.range ≤ orthGroup ε := by
      intro σ hσ
      refine ⟨hXlin σ hσ, fun v => ?_⟩
      by_cases hv0 : v = 0
      · rw [hv0, map_zero_of_mem_linGroup (hXlin σ hσ)]
      rcases qfV_cases ε v with h | h
      · rw [h]
        exact hpres σ hσ v hv0 h
      · rw [h]
        rcases qfV_cases ε (σ v) with h' | h'
        · exfalso
          have hσv0 : σ v ≠ 0 := fun h0 => hv0 (hinj σ hσ v h0)
          have h2 := hpres σ⁻¹ (inv_mem hσ) (σ v) hσv0 h'
          rw [perm_inv_apply, h] at h2
          exact one_ne_zero h2
        · exact h'
    have h1 := (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)).trans
      (card_orthGroup_le ε)
    rw [hX] at h1
    have hob : 0 < oBound ε := by cases ε <;> decide
    omega
  · push Not at hpres
    obtain ⟨σ, hσ, s, hs0, hsq, hσs⟩ := hpres
    have hσs1 : qfV ε (σ s) = 1 := (qfV_cases ε _).resolve_left hσs
    have hσs0 : σ s ≠ 0 := fun h => hs0 (hinj σ hσ s h)
    have he₀ : qfV ε (toVec 6 1) = 0 := by rw [qfV_toVec ε (by norm_num), qfB_one, bz_false]
    have he₀0 : toVec 6 1 ≠ 0 := toVec_ne_zero (by norm_num) one_ne_zero
    have horb : MulAction.orbit hS.linHom.range (toVec 6 1) = {v | v ≠ 0} := by
      ext v
      constructor
      · rintro ⟨τ, rfl⟩ h
        exact he₀0 (hinj τ.1 τ.2 _ h)
      · intro hv
        rcases qfV_cases ε v with h | h
        · obtain ⟨x, hx, hxv⟩ := hS.rad.exists_lin_eq he₀0 hv (he₀.trans h.symm)
          exact ⟨⟨_, hPX x hx⟩, hxv⟩
        · obtain ⟨x₁, hx₁, h1⟩ := hS.rad.exists_lin_eq he₀0 hs0 (he₀.trans hsq.symm)
          obtain ⟨x₂, hx₂, h2⟩ := hS.rad.exists_lin_eq hσs0 hv (hσs1.trans h.symm)
          refine ⟨⟨_, mul_mem (mul_mem (hPX x₂ hx₂) hσ) (hPX x₁ hx₁)⟩, ?_⟩
          change hS.linHom ⟨x₂, _⟩ (σ (hS.linHom ⟨x₁, _⟩ (toVec 6 1))) = v
          rw [hS.linHom_apply, hS.linHom_apply, h1, h2]
    have hcard := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup hS.linHom.range
      (toVec 6 1))
    rw [Nat.card_prod, hX, horb, card_ne_zero_V6] at hcard
    cases ε with
    | minus =>
      simp only [oBound] at hcard
      omega
    | plus =>
      obtain ⟨h3, hfix⟩ := hS.orderOf_linHom_p_zero rfl
      set g₃ : MulAction.stabilizer hS.linHom.range (toVec 6 1) := ⟨⟨_, ⟨_, rfl⟩⟩, hfix⟩
      have hord : orderOf g₃ = 3 := by
        rw [← h3]
        exact (orderOf_injective ((hS.linHom.range).subtype.comp
          (MulAction.stabilizer hS.linHom.range (toVec 6 1)).subtype)
          (Subtype.coe_injective.comp Subtype.coe_injective) g₃).symm
      have hdvd := orderOf_dvd_natCard g₃
      rw [hord] at hdvd
      simp only [oBound] at hcard
      omega

theorem false_of_Zset_univ [Finite G]
    (hZ : ∀ v, v ∈ Zset t Q ψ) : False := by
  by_cases h : ∃ y : V6, y ≠ 0 ∧ Equiv.addRight y ∈ hS.affHom.range
  · obtain ⟨y, hy, hyM⟩ := h
    exact hS.false_of_translation hy hyM
  · push Not at h
    exact hS.false_of_no_translation hZ fun y hy => by
      by_contra hne
      exact h y hne hy

end Setting

end CFSG.EvenSmallLie.OmegaEight.CPrime
