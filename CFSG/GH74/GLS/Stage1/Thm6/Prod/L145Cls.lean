module

import CFSG.GH74.GLS.Stage1.Thm4.Core98
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12Ctx

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.M12Facts
  CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.Sec14 CFSG.GH74.GLS.Stage2.Local

@[expose] def pXU (p : NF) : Prop :=
  p.2.2.1 = 0 ∧ p.2.2.2 = 1 ∧ p.1.val % 2 = 0 ∧ p.2.1.val % 2 = 0

instance : DecidablePred pXU := fun p => by unfold pXU; infer_instance

@[expose] def pZx (p : NF) : Prop :=
  p.2.2.1 = 0 ∧ p.2.2.2 = 1 ∧ ¬ (p.1.val % 2 = 0 ∧ p.2.1.val % 2 = 0)

instance : DecidablePred pZx := fun p => by unfold pZx; infer_instance

theorem inv_cases : ∀ p : NF, nfMul p p = (0, 0, 0, 0) → p ≠ (0, 0, 0, 0) →
    pU p ∨ pXU p ∨ pZx p ∨ ¬ pQ0 p := by decide +kernel

theorem pXU_conj : ∀ p : NF, pXU p → ∃ q : NF, nfMul (nfMul q xNF) (nfInv q) = p := by
  decide +kernel


section Classes

variable {G : Type} [Group G] [Finite G] {S T V : Subgroup G} {a b y x : G}

theorem involution_conj_z_or_x (h144 : Lemma14_4) (hStd : Stage12.Std G)
    (o : Out13 G x T V S a b y) {u : G} (hu : orderOf u = 2) :
    IsConj (a ^ 2 * b ^ 2) u ∨ IsConj x u := by
  have h := o.data
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := (CFSG.ABGLocalTools.isSylowOf_iff).2 o.sylow
  have hu2 : IsPGroup 2 ↥(zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)
  obtain ⟨g, hg⟩ := Stage1.Thm4.exists_conj_mem_sylow hSyl hu2
  have huu : u * u = 1 := by rw [← _root_.sq, ← hu]; exact pow_orderOf_eq_one u
  have hs2 : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [huu]; group
  have hs1 : g * u * g⁻¹ ≠ 1 := by
    intro e
    have : u = 1 := by
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [e]; group
    rw [this, orderOf_one] at hu
    omega
  have hconj : IsConj u (g * u * g⁻¹) := (isConj_iff.2 ⟨g, rfl⟩ : IsConj u (g * u * g⁻¹))
  suffices hmain : IsConj (a ^ 2 * b ^ 2) (g * u * g⁻¹) ∨ IsConj x (g * u * g⁻¹) by
    rcases hmain with hz | hx
    · exact Or.inl (hz.trans hconj.symm)
    · exact Or.inr (hx.trans hconj.symm)
  obtain ⟨p, hp⟩ := exists_nf h hg
  have hpp : nfMul p p = (0, 0, 0, 0) := by
    apply nu_injective h
    rw [← nu_mul h, ← hp, hs2, nu_zero]
  have hp0 : p ≠ (0, 0, 0, 0) := by
    rintro rfl
    exact hs1 (by rw [hp, nu_zero])
  rcases inv_cases p hpp hp0 with hU | hXU | hZx | hQ
  ·
    left
    obtain ⟨f, hf3, hfN, -, v, hv, hfv⟩ := o.f3
    have hvU : v ∈ nfSub h pU closed_pU := by rw [← U_eq h, ← o.V_eq]; exact hv
    have huU : g * u * g⁻¹ ∈ nfSub h pU closed_pU := by
      rw [hp]; exact (nu_mem_nfSub h closed_pU p).2 hU
    obtain ⟨n, -, hn⟩ := exists_conj_U_to_z o hf3 hfN hvU hfv huU hs1
    exact (isConj_iff.2 ⟨n, hn⟩ : IsConj (g * u * g⁻¹) (a ^ 2 * b ^ 2)).symm
  ·
    right
    obtain ⟨q, hq⟩ := pXU_conj p hXU
    have hx' : nu a b y x xNF = x := by simp [nu, xNF]
    refine isConj_iff.2 ⟨nu a b y x q, ?_⟩
    rw [hp, ← hq]
    calc nu a b y x q * x * (nu a b y x q)⁻¹
        = nu a b y x q * nu a b y x xNF * nu a b y x (nfInv q) := by rw [hx', nu_inv h]
      _ = nu a b y x (nfMul (nfMul q xNF) (nfInv q)) := by rw [← nu_mul h, ← nu_mul h]
  ·
    left
    obtain ⟨hk, hl, hij⟩ := hZx
    have hp' : p = (p.1, p.2.1, 0, 1) := by
      obtain ⟨i, j, k, l⟩ := p
      simp only at hk hl ⊢
      rw [hk, hl]
    have := h144 G hStd x T V S a b y o p.1 p.2.1 hij
    rw [hp, hp']
    exact this
  ·
    right
    have hvP : g * u * g⁻¹ ∉ nfSub h pQ0 closed_pQ0 := by
      rw [hp, nu_mem_nfSub h closed_pQ0 p]; exact hQ
    obtain ⟨c, hc⟩ := involutions_conj_x o hg hs2 hvP
    exact isConj_iff.2 ⟨c, hc⟩

end Classes

end CFSG.GH74.GLS.Stage1.Thm6.Prod
