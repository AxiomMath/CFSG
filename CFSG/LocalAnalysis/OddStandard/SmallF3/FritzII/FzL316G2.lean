module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316P2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316G1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL22D

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private def conjOn (P : Subgroup G) (g : G) (h1 : ∀ p ∈ P, g * p * g⁻¹ ∈ P)
    (h2 : ∀ p ∈ P, g⁻¹ * p * g ∈ P) : MulAut ↥P where
  toFun p := ⟨g * p * g⁻¹, h1 p p.2⟩
  invFun p := ⟨g⁻¹ * p * g, h2 p p.2⟩
  left_inv p := Subtype.ext (by simp [mul_assoc])
  right_inv p := Subtype.ext (by simp [mul_assoc])
  map_mul' p q := Subtype.ext (by simp [mul_assoc])

theorem fzl_316_nonab {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P)
    (hna : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) : Nonempty (↥P ≃* SylSL3_4) := by
  have h3 : rho * rho * rho = 1 := by simpa [pow_succ] using h.rho_ord
  have e1 : rho * rho = rho⁻¹ := eq_inv_of_mul_eq_one_left h3
  have e2 : rho⁻¹ * rho⁻¹ = rho := by rw [← mul_inv_rev, e1, inv_inv]
  have hrP' : ∀ p ∈ P, rho⁻¹ * p * rho ∈ P := by
    intro p hp
    have := hPf.nrm_P_rho _ (hPf.nrm_P_rho p hp)
    have eq : rho⁻¹ * p * rho = rho * (rho * p * rho⁻¹) * rho⁻¹ :=
      calc rho⁻¹ * p * rho = (rho * rho) * p * (rho⁻¹ * rho⁻¹) := by rw [e1, e2]
        _ = rho * (rho * p * rho⁻¹) * rho⁻¹ := by group
    rw [eq]
    exact this
  have hll : lam * lam = 1 := by simpa [pow_two] using h.lam_sq
  have hl : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hll
  have hl1 : ∀ p ∈ P, lam * p * lam⁻¹ ∈ P := hPf.nrm_P lam h.lam_T
  have hl2 : ∀ p ∈ P, lam⁻¹ * p * lam ∈ P := by
    intro p hp
    have := hl1 p hp
    rwa [hl] at this ⊢
  let f : MulAut ↥P := conjOn P rho hPf.nrm_P_rho hrP'
  let u : MulAut ↥P := conjOn P lam hl1 hl2
  have hfix : ∀ g : ↥P, f g = g → g = 1 := fun g hg =>
    Subtype.ext (hPf.rho_fpf g g.2 (congrArg Subtype.val hg))
  have hf3 : f ^ 3 = 1 := by
    ext p
    have : (f ^ 3) p = f (f (f p)) := by simp [pow_succ, MulAut.mul_apply]
    rw [this]
    show rho * (rho * (rho * (p : G) * rho⁻¹) * rho⁻¹) * rho⁻¹ = p
    calc _ = (rho * rho * rho) * (p : G) * (rho * rho * rho)⁻¹ := by group
      _ = p := by rw [h3]; simp
  have hf1 : f ≠ 1 := by
    intro hf
    haveI : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hPf.card_P]; norm_num)
    obtain ⟨p, hp⟩ := exists_ne (1 : ↥P)
    exact hp (hfix p (by rw [hf]; rfl))
  have hu2 : u * u = 1 := by
    ext p
    show lam * (lam * (p : G) * lam⁻¹) * lam⁻¹ = p
    calc _ = (lam * lam) * (p : G) * (lam * lam)⁻¹ := by group
      _ = p := by rw [hll]; simp
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have huf : u * f * u⁻¹ = f⁻¹ := by
    rw [hui]
    ext p
    show lam * (rho * (lam * (p : G) * lam⁻¹) * rho⁻¹) * lam⁻¹ = rho⁻¹ * p * rho
    calc _ = (lam * rho * lam⁻¹) * ((lam * lam) * (p : G) * (lam * lam)⁻¹) *
          (lam * rho * lam⁻¹)⁻¹ := by group
      _ = rho⁻¹ * p * rho := by rw [h.lam_rho, hll]; simp
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    h.W_comm a (h.EW ha) b (h.EW hb)
  have hcent := fzl_cent_eq_E h.rho_ord hPf.card_P h.card_E hPf.EP hEcomm hPf.nrm_P_rho
    h.rho_nrm_E hPf.rho_fpf hna
  haveI hAn : (E.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    have := hPf.P_comm g g.2 n n.2
    have hE := mul_mem this hn
    simpa [commutatorElement_def, mul_assoc] using hE⟩
  refine fzl_sl_of_sigma3 ↥P hPf.card_P f u (orderOf_eq_prime hf3 hf1) hfix hu2 huf
    (E.subgroupOf P) (fun a ha => ?_) ?_ ?_
  · rw [mem_subgroupOf] at ha ⊢
    exact h.rho_nrm_E _ ha
  · obtain ⟨e⟩ := h.E_equiv
    exact ⟨(Subgroup.subgroupOfEquivOfLe hPf.EP).trans e⟩
  · ext x
    rw [mem_centralizer_iff]
    constructor
    · intro hx
      rw [mem_subgroupOf]
      refine hcent x x.2 fun e he => ?_
      have := congrArg Subtype.val (hx ⟨e, hPf.EP he⟩ he)
      exact this.symm
    · intro hx a ha
      exact Subtype.ext (hEcomm _ ha _ hx)

end CFSG.OddStandard.SmallF3.FritzII
