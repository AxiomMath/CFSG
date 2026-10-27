module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIL34Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIBasic
public import Certificates.Certificate27219
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Action
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvCent
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Subgroup CFSG.Blueprint CFSG.Open CFSG.ComponentClassification.PSL3Four
  CFSG.EvenSporadicStandard.HSStd.HL34 CFSG.EvenSporadicStandard.HSStd.HOv

theorem false_of_good_triple_l34
    {D : Type} [Group D] [Finite D]
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥) {a b : D}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (ea : Nonempty (↥(centralizer ({a} : Set D)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)))
    (eb : Nonempty (↥(centralizer ({b} : Set D)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)))
    (eab : Nonempty (↥(centralizer ({a * b} : Set D)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)))
    (hL : LieModel ↥(commutator ↥(commutator D)) .PSL 3 2 2) : False := by
  obtain ⟨φ⟩ := nonempty_equiv_of_stated _ (by
    rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num))
  have hHeq : (commutator ↥(commutator D)).map (commutator D).subtype =
      ⁅commutator D, commutator D⁆ := by
    rw [show commutator ↥(commutator D) = ⁅(⊤ : Subgroup ↥(commutator D)), ⊤⁆ from rfl,
      map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hHn : ((commutator ↥(commutator D)).map (commutator D).subtype).Normal := by
    rw [hHeq]
    infer_instance
  let H : Subgroup D := (commutator ↥(commutator D)).map (commutator D).subtype
  have : H.Normal := hHn
  let ψ : ↥H ≃* ↥S := (Subgroup.equivMapOfInjective (commutator ↥(commutator D))
    (commutator D).subtype Subtype.val_injective).symm.trans φ
  obtain ⟨e, he, -⟩ := full_automorphism_action
  have hHcard : Nat.card H = 20160 := by rw [Nat.card_congr ψ.toEquiv]; exact card_S
  have hC : centralizer (H : Set D) = ⊥ :=
    centralizer_eq_bot_of_normal_of_card hZ ha ea H (by rw [hHcard]; norm_num)
      (by rw [hHcard]; norm_num)
  have hinj : Function.Injective (rho H ψ e) := rho_injective H ψ e hC
  have hconj : ∀ {x : D}, orderOf x = 2 →
      Nonempty (↥(centralizer ({x} : Set D)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) →
        IsConj (rho H ψ e x) r₃R := by
    intro x hx ex
    have hρx : orderOf (rho H ψ e x) = 2 := by rw [orderOf_injective _ hinj x, hx]
    have hdvd : 240 ∣ Nat.card ↥(centralizer ({rho H ψ e x} : Set ↥R)) := by
      have hle : (centralizer ({x} : Set D)).map (rho H ψ e) ≤
          centralizer ({rho H ψ e x} : Set ↥R) := by
        rintro _ ⟨y, hy, rfl⟩
        have hy' : y ∈ centralizer ({x} : Set D) := hy
        rw [mem_centralizer_singleton_iff] at hy' ⊢
        rw [← map_mul, ← map_mul, hy']
      have := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective hinj, card_centralizer_of_good ex] at this
    exact isConj_r₃_of_dvd hρx hdvd
  have hab2 : orderOf (a * b) = 2 := orderOf_mul_eq_two ha hb hab hcomm
  have hρa := hconj ha ea
  have hρb := hconj hb eb
  have hρab := hconj hab2 eab
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

end CFSG.EvenSporadicStandard.HSStd.HFI
