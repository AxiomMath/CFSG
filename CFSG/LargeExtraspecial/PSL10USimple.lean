module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryScalarQuotient
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.PSLPSU10

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.GorensteinLyons.FourUnitary

variable {F : Type} [Field F] (hF : UnitaryFieldData 2 1 F)

theorem unitaryScalars_eq_bot {n : ℕ} (hn : 1 ≤ n) (h3 : Nat.gcd n 3 = 1) :
    unitaryScalars hF n = ⊥ := by
  rw [← Subgroup.card_eq_one, card_unitaryScalars hF hn]
  simpa using h3

@[expose] noncomputable def unitarySUEquivPSU {n : ℕ} (hn : 1 ≤ n) (h3 : Nat.gcd n 3 = 1) :
    unitarySU 2 1 F n ≃* unitaryPSU hF n :=
  ((QuotientGroup.quotientMulEquivOfEq (unitaryScalars_eq_bot hF hn h3)).trans
    QuotientGroup.quotientBot).symm

include hF in
theorem isSimpleGroup_unitarySU {n : ℕ} (hn : 3 ≤ n) (h3 : Nat.gcd n 3 = 1) :
    IsSimpleGroup (unitarySU 2 1 F n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite F := hF.finite
  have hK : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF.card]; norm_num
  have hne : (n, 2 ^ 1) ≠ (3, 2) := by
    intro h
    rw [Prod.mk.injEq] at h
    rw [h.1] at h3
    norm_num at h3
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 1 hK n hn hne
  exact ((unitarySUEquivPSU hF (by omega) h3).trans (unitaryPSUEquiv hF (by omega))).isSimpleGroup

variable {V : Type*} [AddCommGroup V] [Module F V] {B : V →ₛₗ[hF.bar] V →ₗ[F] F}

@[expose] noncomputable def suEquivUnitarySU {d : ℕ} (e : Basis (Fin d) F V)
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) :
    sesqSpecialUnitaryGroup B ≃* unitarySU 2 1 F d :=
  ((glEquiv e).subgroupMap (sesqSpecialUnitaryGroup B)).trans (MulEquiv.subgroupCongr (by
    ext A
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (mem_sesqSpecialUnitaryGroup_iff_glEquiv e he g).mp hg
    · intro hA
      refine ⟨(glEquiv e).symm A, (mem_sesqSpecialUnitaryGroup_iff_glEquiv e he _).mpr ?_,
        MulEquiv.apply_symm_apply _ _⟩
      rwa [MulEquiv.apply_symm_apply]))

theorem isSimpleGroup_sesqSpecialUnitaryGroup [FiniteDimensional F V] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {n : ℕ} (hn : finrank F V = n) (h3n : 3 ≤ n) (h3 : Nat.gcd n 3 = 1) :
    IsSimpleGroup (sesqSpecialUnitaryGroup B) := by
  obtain ⟨e, he⟩ := hF.exists_orthonormal_basis hB hBl
  have := isSimpleGroup_unitarySU hF (n := finrank F V) (hn ▸ h3n) (hn ▸ h3)
  exact (suEquivUnitarySU hF e he).isSimpleGroup

theorem two_pow_dvd_card_sesqSpecialUnitaryGroup [FiniteDimensional F V] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {n : ℕ} (hn : finrank F V = n) (hn1 : 1 ≤ n) :
    2 ^ (n * (n - 1) / 2) ∣ Nat.card (sesqSpecialUnitaryGroup B) := by
  have h := (unitary_full_group_order hF hB hBl hn hn1).2.2.2.2.2.2
  rw [pow_one] at h
  rw [← h]
  exact Nat.ordProj_dvd _ _

end CFSG.LargeExtraspecial.S14.PSLPSU10
