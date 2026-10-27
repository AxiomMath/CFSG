module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.AutBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIL34Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvOut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Parts
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import Certificates.Certificate27219

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.Blueprint CFSG.Open CFSG.ComponentClassification.PSL3Four
  CFSG.EvenSporadicStandard.HSStd.HL34 CFSG.EvenSporadicStandard.HSStd.HOv
  CFSG.EvenSporadicStandard.HSStd.HFI

theorem false_of_three_cent_l34
    {D : Type} [Group D] [Finite D] (H : Subgroup D) [H.Normal]
    (hC : centralizer (H : Set D) = ⊥) (hL : LieModel ↥H .PSL 3 2 2) {a b : D}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (da : 240 ∣ Nat.card ↥(centralizer ({a} : Set D)))
    (db : 240 ∣ Nat.card ↥(centralizer ({b} : Set D)))
    (dab : 240 ∣ Nat.card ↥(centralizer ({a * b} : Set D))) : False := by
  obtain ⟨ψ⟩ := nonempty_equiv_of_stated _ (by
    rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num))
  obtain ⟨e, he, -⟩ := full_automorphism_action
  have hinj : Function.Injective (rho H ψ e) := rho_injective H ψ e hC
  have hconj : ∀ {x : D}, orderOf x = 2 → 240 ∣ Nat.card ↥(centralizer ({x} : Set D)) →
      IsConj (rho H ψ e x) r₃R := by
    intro x hx dx
    have hρx : orderOf (rho H ψ e x) = 2 := by rw [orderOf_injective _ hinj x, hx]
    have hdvd : 240 ∣ Nat.card ↥(centralizer ({rho H ψ e x} : Set ↥R)) := by
      have hle : (centralizer ({x} : Set D)).map (rho H ψ e) ≤
          centralizer ({rho H ψ e x} : Set ↥R) := by
        rintro _ ⟨y, hy, rfl⟩
        have hy' : y ∈ centralizer ({x} : Set D) := hy
        rw [mem_centralizer_singleton_iff] at hy' ⊢
        rw [← map_mul, ← map_mul, hy']
      have := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective hinj] at this
      exact dx.trans this
    exact isConj_r₃_of_dvd hρx hdvd
  have hab2 : orderOf (a * b) = 2 := orderOf_mul_eq_two ha hb hab hcomm
  have hρa := hconj ha da
  have hρb := hconj hb db
  have hρab := hconj hab2 dab
  have hsq : ∀ {x : D}, orderOf x = 2 → rho H ψ e x * rho H ψ e x = 1 := by
    intro x hx
    rw [← map_mul, ← sq, ← hx, pow_orderOf_eq_one, map_one]
  have hne1 : ∀ {x : D}, orderOf x = 2 → rho H ψ e x ≠ 1 := by
    intro x hx h
    have : x = 1 := hinj (h.trans (map_one _).symm)
    rw [this, orderOf_one] at hx
    omega
  obtain ⟨c, hc⟩ := isConj_iff.1 hρa
  have hcomm' : rho H ψ e a * rho H ψ e b = rho H ψ e b * rho H ψ e a := by
    rw [← map_mul, ← map_mul, hcomm]
  refine hfi34Check_spec (x := c * rho H ψ e b * c⁻¹) Certificates.certificate27219
    ?_ ?_ ?_ ?_ ⟨?_, ?_⟩
  · rw [← hc]
    calc c * rho H ψ e b * c⁻¹ * (c * rho H ψ e a * c⁻¹) =
        c * (rho H ψ e b * rho H ψ e a) * c⁻¹ := by group
      _ = c * (rho H ψ e a * rho H ψ e b) * c⁻¹ := by rw [hcomm']
      _ = c * rho H ψ e a * c⁻¹ * (c * rho H ψ e b * c⁻¹) := by group
  · calc c * rho H ψ e b * c⁻¹ * (c * rho H ψ e b * c⁻¹) =
        c * (rho H ψ e b * rho H ψ e b) * c⁻¹ := by group
      _ = 1 := by rw [hsq hb]; group
  · intro h
    apply hne1 hb
    have := congrArg (fun z => c⁻¹ * z * c) h
    simpa [mul_assoc] using this
  · intro h
    have h' : c * rho H ψ e b * c⁻¹ = c * rho H ψ e a * c⁻¹ := h.trans hc.symm
    exact hab (hinj (mul_left_cancel (mul_right_cancel h'))).symm
  · exact (isConj_iff.2 ⟨c⁻¹, by group⟩).trans hρb
  · have : r₃R * (c * rho H ψ e b * c⁻¹) = c * rho H ψ e (a * b) * c⁻¹ := by
      rw [← hc, map_mul]
      group
    rw [this]
    exact (isConj_iff.2 ⟨c⁻¹, by group⟩).trans hρab

theorem noTwoCfgL34_holds :
    NoTwoCfgL34 := by
  intro G _ _ S hSn hS hcent t v J h _
  haveI := hSn
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  have h480 := h.card_centralizer htop
  have hv1 : orderOf v = 2 :=
    orderOf_eq_prime (by rw [sq]; exact h.hv) (h.v_ne_one htop)
  have hd : ∀ {x : G}, centralizer ({x} : Set G) = centralizer ({t} : Set G) →
      240 ∣ Nat.card ↥(centralizer ({x} : Set G)) := fun hx => by
    rw [hx, h480]
    norm_num
  exact false_of_three_cent_l34 S hcent hS h.ht hv1 (h.v_ne_t htop).symm h.tv_comm
    (hd rfl) (hd h.hCv) (hd h.hCtv)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
