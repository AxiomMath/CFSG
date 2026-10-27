module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2H
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2Z
public import Certificates.Certificate441793

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 Certificates.FzBU

theorem fzb_classify {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G} (h : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 4) {T₂ P : Subgroup G} {q s : G}
    (hS : FzbStruct t S x₁ x₂ lam rho tau T₂ P q s) :
    ∃ (c : Bool) (β : ℕ → G), FzbChart c T₂ P x₁ x₂ t q s lam β ∧ s * q * s⁻¹ = q⁻¹ := by
  obtain ⟨C⟩ := fzb_exists_coding hS.P_iso
  have hR := fzb_rel h hK hS
  obtain ⟨hx₁, hx₂, hZP, hZcard⟩ := fzb_Z_facts h hS
  have hN : ∀ g ∈ T₂, FzbNorm P g := fun g hg p hp => hS.P_norm g hg p hp
  have hρ : FzbNorm P rho := hS.rho_norm
  have hsZ : ∀ p ∈ P, C.enc (s * p * s⁻¹ * p⁻¹) < 4 := fun p hp =>
    (fzb_Z_code C hx₁ hx₂ hZcard _ (hZP (fzb_s_comm_Z hS hp))).mp (fzb_s_comm_Z hS hp)
  obtain ⟨hrho, hQ, hSc, hinv, hyq, hys⟩ := fzb_tables_cond C hR hN hρ hS.rho_fpf hsZ
  have hNq : FzbNorm P q := hN q hR.q_mem
  have hNs : FzbNorm P s := hN s hR.s_mem
  have hNy : FzbNorm P lam := hN lam hR.lam_mem
  obtain ⟨hw, c, g, hg, hgq, hgs, hgy, hrep⟩ :=
    fzb_classSpec_extract (Certificates.certificate441793) (C.tab_isAut hρ)
      (C.tab_isAut hNq) (C.tab_isAut hNs) (C.tab_isAut hNy) hrho hQ hSc hinv hyq hys
  simp only [repOK, Bool.and_eq_true, and_assoc] at hrep
  obtain ⟨hAq, hAs, hAy, h4, h2, hs2', hsq', -, -, -⟩ := hrep
  have eq_q := fun x (hx : x < 64) => C.tab_twist hw hg hNq hgq hx
  have eq_s := fun x (hx : x < 64) => C.tab_twist hw hg hNs hgs hx
  have eq_y := fun x (hx : x < 64) => C.tab_twist hw hg hNy hgy hx
  obtain ⟨hs2, hsq⟩ := fzb_faithful (C.twist hw g hg) hNq hNs hR.q_pow hR.s_sq hR.s_q
    eq_q eq_s h4 h2 hs2' hsq'
  have tq := (fzb_modl_tables c).1
  have ts := (fzb_modl_tables c).2.1
  have ty := (fzb_modl_tables c).2.2
  have hE : FzbExact (C.twist hw g hg) c q s lam :=
    { hq := by rw [tq]; exact fun x hx => C.tab_twist_dec hw hg hNq hgq hx
      hs := by rw [ts]; exact fun x hx => C.tab_twist_dec hw hg hNs hgs hx
      hy := by rw [ty]; exact fun x hx => C.tab_twist_dec hw hg hNy hgy hx
      aq_lt := by rw [tq]; exact fun x hx => fzb_isAutArr_lt hAq hx
      as_lt := by rw [ts]; exact fun x hx => fzb_isAutArr_lt hAs hx
      ay_lt := by rw [ty]; exact fun x hx => fzb_isAutArr_lt hAy hx
      q_pow := hR.q_pow
      s_sq := hs2
      y_sq := hR.lam_sq
      s_q := hsq
      y_q := hR.lam_q
      y_s := hR.lam_s }
  have hβ := fzb_chart_exact (C.twist hw g hg) hE hR.q_sq hS.P_le hR.q_mem hR.s_mem hR.lam_mem
    hS.gen hS.card_T₂ hZP (fzb_Z_code (C.twist hw g hg) hx₁ hx₂ hZcard)
  exact ⟨c, fzbBeta (C.twist hw g hg) q s lam, hβ, hsq⟩

end CFSG.OddStandard.SmallF3.FritzII
