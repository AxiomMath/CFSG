module

public import CFSG.ClassicalInvolution.Q3.Q3E7MStd
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclTwin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)


theorem involution_central_fund3 {R : Subgroup (Generic.modelUniv .E7 0 3 1 Nat.prime_three).K}
    (hR : R ∈ Generic.fundamentalSubgroups .E7 (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D)
    {r : (Generic.modelUniv .E7 0 3 1 Nat.prime_three).K} (hr : r ∈ R) (h2 : orderOf r = 2) :
    ∀ a ∈ R, a * r = r * a := by
  have hadm : StatedLieAdmissible .E7 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  obtain ⟨e⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (t := .E7) (n := 0)
    (e := 1) (by norm_num) trivial hadm (by decide) (by decide) hR
  have h2' : (⟨r, hr⟩ : R) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 odd_gf3 e _).mp (by rw [Subgroup.orderOf_mk, h2])
  have hc : (⟨r, hr⟩ : R) ∈ Subgroup.center R := by
    rw [mem_center_iff_of_equiv_sl2 e, h2', MulEquiv.apply_symm_apply]
    exact (mem_center_sl2_iff _).mpr (Or.inr rfl)
  intro a ha
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨a, ha⟩)

theorem mul_inv_mul_mem_center3 {g : M₇} {γ₁ γ₂ ρ : Fin (Tag.rank .E7) → ℤ}
    (hγ₁ : IsRoot .E7 γ₁) (hγ₂ : IsRoot .E7 γ₂) (hρ : IsRoot .E7 ρ)
    (hpar : ∀ i : Fin (Tag.rank .E7), iform ρ (Pi.single i 1) % 2 =
      (iform γ₁ (Pi.single i 1) + iform γ₂ (Pi.single i 1)) % 2) {r₁ r₂ r : M₇}
    (hr₁ : r₁ ∈ conjSub g (stdRankOne D₇ γ₁)) (hr₂ : r₂ ∈ conjSub g (stdRankOne D₇ γ₂))
    (hr : r ∈ conjSub g (stdRankOne D₇ ρ)) (ho₁ : orderOf r₁ = 2) (ho₂ : orderOf r₂ = 2)
    (ho : orderOf r = 2) : (r₁ * r₂)⁻¹ * r ∈ Subgroup.center M₇ := by
  obtain ⟨a₁, ha₁, rfl⟩ := Subgroup.mem_map.1 hr₁
  obtain ⟨a₂, ha₂, rfl⟩ := Subgroup.mem_map.1 hr₂
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hr
  have ord : ∀ b : M₇, orderOf ((MulAut.conj g).toMonoidHom b) = 2 → orderOf b = 2 := fun b hb => by
    rw [← hb]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective b).symm
  have o₁ := ord a₁ ho₁
  have o₂ := ord a₂ ho₂
  have o := ord a ho
  have h1 : εm (GaloisField 3 1) (a₁ * a₂) = rootDiagUnit .E7
      (thetaDiag γ₁ (-1 : (GaloisField 3 1)ˣ) * thetaDiag γ₂ (-1)) := by
    rw [map_mul, εm_involution_std3 hγ₁ ha₁ o₁, εm_involution_std3 hγ₂ ha₂ o₂,
      ← rootDiagUnit_mul]
  have h2 := εm_involution_std3 hρ ha o
  have hker : (a₁ * a₂)⁻¹ * a ∈ (εm (GaloisField 3 1)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, h2, thetaDiag_neg_one_eq_mul hpar,
      rootDiagUnit_mul]
    group
  have hc := εm_ker_le_center hker
  have e : ((MulAut.conj g).toMonoidHom a₁ * (MulAut.conj g).toMonoidHom a₂)⁻¹ *
      (MulAut.conj g).toMonoidHom a = g * ((a₁ * a₂)⁻¹ * a) * g⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e, mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_center_iff.mp hc g)]
  exact hc

end CFSG.ClassicalInvolution.Q3.Q3W
