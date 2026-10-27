module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ef2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3S4Rec

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

variable {Λ : Type} [Group Λ] [Finite Λ] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E] {ι : Λ →* (E ≃ₗ[ZMod 2] E)} {P W : Subgroup Λ} {r s : Λ}

theorem nonempty_perm_four_of_crit (h : Crit ι P W r s) :
    Nonempty (Λ ≃* Equiv.Perm (Fin 4)) := by
  have hcardP : Nat.card P = 4 := card_P_eq_four h
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcommP : IsMulCommutative ↥P :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by
        rw [hcardP]; norm_num)
    intro a ha b hb
    exact congrArg Subtype.val (hcommP.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hord : orderOf r = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h.r_cube h.r_ne
  have hmoved : ∃ n ∈ P, s * n * s⁻¹ ≠ n := by
    by_contra hc
    push Not at hc
    obtain hbot | ⟨n, hn, hn1⟩ := P.bot_or_exists_ne_one
    · rw [hbot, Subgroup.card_bot] at hcardP
      exact absurd hcardP (by norm_num)
    · refine hn1 (h.fpf n hn ?_)
      have hm : r * n * r⁻¹ ∈ P := h.normal.conj_mem n hn r
      have h1 : s * (r * n * r⁻¹) * s⁻¹ = r * n * r⁻¹ := hc _ hm
      have hr' : s * r⁻¹ * s⁻¹ = r := by
        have h := congrArg Inv.inv h.s_conj
        simpa [mul_inv_rev, mul_assoc] using h
      have h2 : s * (r * n * r⁻¹) * s⁻¹ = r⁻¹ * n * r := by
        have e : s * (r * n * r⁻¹) * s⁻¹
            = (s * r * s⁻¹) * (s * n * s⁻¹) * (s * r⁻¹ * s⁻¹) := by group
        rw [e, h.s_conj, hc n hn, hr']
      have hfix' : r * n * r⁻¹ = r⁻¹ * n * r := h1.symm.trans h2
      have hr2 : r * r = r⁻¹ := by
        have h3 : r * r * r = 1 := by
          have h := h.r_cube
          rw [pow_succ, pow_two] at h
          exact h
        exact eq_inv_of_mul_eq_one_left h3
      have hrinv2 : r⁻¹ * r⁻¹ = r := by
        have h := congrArg Inv.inv hr2
        simpa [mul_inv_rev] using h
      have hconj2 : r⁻¹ * (r * n * r⁻¹) * r = r⁻¹ * (r⁻¹ * n * r) * r := by rw [hfix']
      have hl : r⁻¹ * (r * n * r⁻¹) * r = n := by group
      have hr : r⁻¹ * (r⁻¹ * n * r) * r = r * n * r⁻¹ := by
        calc r⁻¹ * (r⁻¹ * n * r) * r = (r⁻¹ * r⁻¹) * n * (r * r) := by group
          _ = r * n * r⁻¹ := by rw [hrinv2, hr2]
      rw [hl, hr] at hconj2
      exact hconj2.symm
  exact CFSG.Quasithin.Fan86.Sigma3.Klein24.nonempty_perm_four
    { card := by rw [h.card_index, hcardP]
      normal := h.normal
      card_N := hcardP
      comm := hcomm
      ord := hord
      fix := h.fpf
      sq := h.s_sq
      moved := hmoved }

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
