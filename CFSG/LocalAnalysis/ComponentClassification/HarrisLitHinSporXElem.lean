module

public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinBasic
public import CFSG.Sporadic.Th.GroupTheory

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin.SporX

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem closure_comm_sq {G : Type*} [Group G] {S : Set G}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x ^ 2 = 1) :
    (∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a) ∧ ∀ a ∈ closure S, a ^ 2 = 1 := by
  have hcl : IsMulCommutative ↥(closure S) :=
    isMulCommutative_closure fun x hx y hy _ => hcomm x hx y hy
  have hc : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcl.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨hc, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy => rw [Commute.mul_pow (hc x hx y hy) 2, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem hinConcl_of_autModel {M : Type} [Group M] {P R : Subgroup M} (h : AutModel P R)
    {Rp : M → Prop}
    (hcover : ∀ t ∈ R, orderOf t = 2 → ∃ ρ, Rp ρ ∧ ∃ g ∈ R, t = g * ρ * g⁻¹)
    (hrep : ∀ ρ, Rp ρ → ∃ E : Subgroup M, E ≤ P ⊓ centralizer {ρ} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
      (ρ ∈ P → 2 ^ 3 < Nat.card E) ∧ (ρ ∉ P → 2 ^ 2 < Nat.card E))
    {Y : Type} [Group Y] (φ : Y ≃* P) (p m : ℕ) (τ : MulAut Y) (hτ : orderOf τ = 2) :
    HinConcl Y p m τ := by
  set τ' : MulAut P := MulAut.congr φ τ with hτ'
  set x : M := h.hom τ' with hx
  have hxR : x ∈ R := h.elt_mem τ'
  have hxspec : ∀ q : P, ((τ' q : P) : M) = x * q * x⁻¹ := h.elt_spec τ'
  have hx2 : orderOf x = 2 := by
    rw [hx, orderOf_injective h.hom h.hom_injective, hτ', MulEquiv.orderOf_eq]
    exact hτ
  obtain ⟨ρ, hρ, g, hgR, hxg⟩ := hcover x hxR hx2
  obtain ⟨E, hEC, hEc, hEs, hE3, hE2⟩ := hrep ρ hρ
  have hgP : ∀ a ∈ P, g * a * g⁻¹ ∈ P := fun a ha => h.conj_mem g hgR a ha
  have hxP : x ∈ P ↔ ρ ∈ P := by
    constructor
    · intro hx'
      have h1 := h.conj_mem g⁻¹ (R.inv_mem hgR) x hx'
      rwa [hxg, show g⁻¹ * (g * ρ * g⁻¹) * g⁻¹⁻¹ = ρ by group] at h1
    · intro hρ'
      rw [hxg]
      exact hgP ρ hρ'
  have hinn : τ ∈ innAut Y ↔ x ∈ P := by
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : x = ((φ y : P) : M) := by
        rw [hx, AutModel.hom_apply]
        refine h.elt_eq (h.le (φ y).2) fun q => ?_
        simp [hτ', MulAut.congr_apply, MulAut.conj_apply]
      rw [h1]
      exact (φ y).2
    · intro hx'
      refine ⟨φ.symm ⟨x, hx'⟩, (MulAut.congr φ).injective ?_⟩
      refine MulEquiv.ext fun q => Subtype.ext ?_
      rw [← hτ', hxspec q]
      simp [MulAut.congr_apply, MulAut.conj_apply]
  have hEP : ∀ a ∈ E, g * a * g⁻¹ ∈ P := fun a ha => hgP a (hEC ha).1
  let ψ : E →* Y :=
    { toFun := fun a => φ.symm ⟨g * a * g⁻¹, hEP a a.2⟩
      map_one' := by
        rw [← map_one φ.symm]
        congr 1
        ext
        simp
      map_mul' := fun a b => by
        rw [← map_mul]
        congr 1
        ext
        simp only [Subgroup.coe_mul]
        group }
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h1 := congrArg Subtype.val (φ.symm.injective hab)
    simp only at h1
    exact Subtype.ext (by simpa using h1)
  have hfix : ψ.range ≤ fixedPoints τ := by
    rintro _ ⟨a, rfl⟩
    rw [mem_fixedPoints]
    set q : P := ⟨g * a * g⁻¹, hEP a a.2⟩ with hqdef
    have hq : τ' q = q := by
      refine Subtype.ext ?_
      rw [hxspec, hxg]
      have hc := mem_centralizer_singleton_iff.mp (hEC a.2).2
      calc g * ρ * g⁻¹ * (q : M) * (g * ρ * g⁻¹)⁻¹ = g * ((↑a * ρ) * ρ⁻¹) * g⁻¹ := by
            rw [show (a : M) * ρ = ρ * a from hc, hqdef]
            group
        _ = (q : M) := by
            rw [hqdef]
            group
    change τ (φ.symm q) = φ.symm q
    calc τ (φ.symm q) = φ.symm (τ' q) := by simp [hτ', MulAut.congr_apply]
      _ = φ.symm q := by rw [hq]
  have hcard : Nat.card ψ.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hc : ∀ a ∈ ψ.range, ∀ b ∈ ψ.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEc a a.2 b b.2)
  have hs : ∀ a ∈ ψ.range, a ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, show a ^ 2 = 1 from Subtype.ext (by simpa using hEs a a.2), map_one]
  refine hinConcl_of_rank (fun hτi => ?_) (fun hτo => ?_)
  · exact not_sectionalTwoRankLE_of_le hfix hc hs
      (by rw [hcard]; exact hE3 (hxP.mp (hinn.mp hτi)))
  · exact not_sectionalTwoRankLE_of_le hfix hc hs
      (by rw [hcard]; exact hE2 fun hρP => hτo (hinn.mpr (hxP.mpr hρP)))

variable {n : ℕ}

end CFSG.ComponentClassification.HarrisLit.Hin.SporX
