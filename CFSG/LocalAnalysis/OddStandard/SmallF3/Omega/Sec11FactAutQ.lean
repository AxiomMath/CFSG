module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11AutQBound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11AutQModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11InputsQ
public import Certificates.Certificate442008

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Certificates.OmegaAutQ

theorem asc82FactAutQ_of_check (h : check () = true) : Asc82FactAutQ := by
  intro G _ _ K1 K2 hc hcard h1 h2 P hPQ hP Φ hΦ
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ := h2
  obtain ⟨σ⟩ := twoCore_iso_qm0 K1 K2 hc hcard e1 e2
  haveI : IsMulCommutative ↥P := hP.1.1
  let τ : ↥(twoCoreIn (K1 ⊔ K2)) →* S81 := qm0.subtype.comp σ.toMonoidHom
  have hτ : Function.Injective τ := Subtype.val_injective.comp σ.injective
  let Pm : Subgroup S81 := (P.subgroupOf (twoCoreIn (K1 ⊔ K2))).map τ
  have hPm : ∀ x, x ∈ Pm ↔ ∃ p : ↥(twoCoreIn (K1 ⊔ K2)), (p : G) ∈ P ∧ τ p = x := by
    intro x
    simp [Pm, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hPmQ : Pm ≤ qm0 := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := (hPm x).1 hx
    exact (σ p).2
  have hcardPm : Nat.card Pm = 8 := by
    rw [Subgroup.card_map_of_injective hτ]
    have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPQ).toEquiv
    rw [this, hP.2]
    norm_num
  have hcommPm : ∀ x ∈ Pm, ∀ y ∈ Pm, x * y = y * x := by
    intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := (hPm x).1 hx
    obtain ⟨q, hq, rfl⟩ := (hPm y).1 hy
    rw [← map_mul, ← map_mul]
    exact congrArg τ (Subtype.ext (Subgroup.mul_comm_of_mem_isMulCommutative P hp hq))
  have hsqPm : ∀ x ∈ Pm, x * x = 1 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (hPm x).1 hx
    rw [← map_mul, ← map_one τ]
    refine congrArg τ (Subtype.ext ?_)
    have := hP.1.2 _ hp
    simpa [pow_two] using this
  let Φ' : Subgroup (MulAut ↥qm0) := Φ.map (MulAut.congr σ).toMonoidHom
  have hfix : ∀ γ ∈ Φ', ∀ p : ↥qm0, (p : S81) ∈ Pm → γ p = p := by
    intro γ hγ p hp
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.1 hγ
    obtain ⟨q, hq, hqp⟩ := (hPm _).1 hp
    have hσq : σ q = p := Subtype.ext hqp
    have h1 : δ q = q := hΦ δ hδ q hq
    show σ (δ (σ.symm p)) = p
    rw [← hσq, σ.symm_apply_apply, h1]
  have hcardΦ : Nat.card ↥Φ' = Nat.card ↥Φ :=
    Subgroup.card_map_of_injective (MulAut.congr σ).injective
  rw [← hcardΦ]
  exact AutQBound.aut_bound h mem_qm0 hPmQ hcardPm hcommPm hsqPm Φ' hfix

theorem asc82FactAutQ_of_cert : Asc82FactAutQ :=
  asc82FactAutQ_of_check Certificates.certificate442008

end CFSG.OddStandard.SmallF3.Omega
