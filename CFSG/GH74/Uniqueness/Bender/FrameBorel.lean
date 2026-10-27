module

public import CFSG.GH74.Uniqueness.Bender.FrameDefs
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.Models.BenderSuzuki
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.Uniqueness.Bender.Frame

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {E : Type} [Field E]

namespace IsotropicLine

section Form

variable (hU : UnitaryFieldData p f E)

theorem herm_eq_gramForm (x y : Fin 3 → E) :
    herm hU x y = gramForm hU (1 : Matrix (Fin 3) (Fin 3) E) x y := by
  simp only [herm, gramForm_apply, one_mulVec, dotProduct]

theorem herm_add_right (x y z : Fin 3 → E) : herm hU x (y + z) = herm hU x y + herm hU x z := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem herm_smul_right (c : E) (x y : Fin 3 → E) : herm hU x (c • y) = c * herm hU x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem herm_smul_left (c : E) (x y : Fin 3 → E) :
    herm hU (c • x) y = hU.bar c * herm hU x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem herm_mulVec_mulVec (g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) (x y : Fin 3 → E) :
    herm hU (((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x)
      (((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ y) = herm hU x y := by
  rw [herm_eq_gramForm, herm_eq_gramForm]
  exact (mem_gramSU_iff_isometry.mp g.2).1 x y

end Form

section RootGroup

variable {hU : UnitaryFieldData p f E} {v : Fin 3 → E}

theorem transvection_mul (hiso : herm hU v v = 0) {g g' : GL (Fin 3) E} {c c' : E}
    (hg : ∀ x, (g : Matrix (Fin 3) (Fin 3) E) *ᵥ x = x + (c * herm hU v x) • v)
    (hg' : ∀ x, (g' : Matrix (Fin 3) (Fin 3) E) *ᵥ x = x + (c' * herm hU v x) • v)
    (x : Fin 3 → E) :
    ((g * g' : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x =
      x + ((c + c') * herm hU v x) • v := by
  rw [Units.val_mul, ← mulVec_mulVec, hg', mulVec_add, mulVec_smul, hg x, hg v, hiso, mul_zero,
    zero_smul, add_zero, add_mul, add_smul, add_assoc]

theorem transvection_inv (hiso : herm hU v v = 0) {g : GL (Fin 3) E} {c : E}
    (hg : ∀ x, (g : Matrix (Fin 3) (Fin 3) E) *ᵥ x = x + (c * herm hU v x) • v)
    (x : Fin 3 → E) :
    ((g⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x = x + (-c * herm hU v x) • v := by
  have hy : (g : Matrix (Fin 3) (Fin 3) E) *ᵥ (x + (-c * herm hU v x) • v) = x := by
    rw [hg, herm_add_right, herm_smul_right, hiso, mul_zero, add_zero, add_assoc, ← add_smul,
      neg_mul, neg_add_cancel, zero_smul, add_zero]
  conv_lhs => rw [← hy]
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

variable (hU) in
@[expose] def rootGroup (hiso : herm hU v v = 0) :
    Subgroup (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) where
  carrier := {g | ∃ c : E,
    ∀ x, ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x = x + (c * herm hU v x) • v}
  mul_mem' := by
    rintro g g' ⟨c, hg⟩ ⟨c', hg'⟩
    exact ⟨c + c', transvection_mul hiso hg hg'⟩
  one_mem' := ⟨0, fun x => by simp⟩
  inv_mem' := by
    rintro g ⟨c, hg⟩
    exact ⟨-c, transvection_inv hiso hg⟩

theorem mem_rootGroup (hiso : herm hU v v = 0) {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} :
    g ∈ rootGroup hU hiso ↔ ∃ c : E,
      ∀ x, ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x = x + (c * herm hU v x) • v :=
  Iff.rfl

theorem conj_mem_rootGroup (hiso : herm hU v v = 0)
    {g y : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} {μ : E}
    (hμ : ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ v = μ • v)
    (hy : y ∈ rootGroup hU hiso) : g * y * g⁻¹ ∈ rootGroup hU hiso := by
  obtain ⟨c, hc⟩ := hy
  refine ⟨c * (μ * hU.bar μ), fun x => ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  set w := ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x with hw
  have hgw : ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ w = x := by
    rw [hw, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hherm : herm hU v w = hU.bar μ * herm hU v x := by
    rw [← herm_mulVec_mulVec hU g v w, hμ, hgw, herm_smul_left]
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← hw, hc, mulVec_add,
    mulVec_smul, hgw, hμ, hherm, smul_smul]
  congr 2
  ring

theorem mul_self_eq_one_of_mem_rootGroup [CharP E 2] (hiso : herm hU v v = 0)
    {y : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hy : y ∈ rootGroup hU hiso) : y * y = 1 := by
  obtain ⟨c, hc⟩ := hy
  refine Subtype.ext (Units.ext (ext_of_mulVec_single fun i => ?_))
  rw [Subgroup.coe_mul, transvection_mul hiso hc hc, CharTwo.add_self_eq_zero, zero_mul,
    zero_smul, add_zero, Subgroup.coe_one, Units.val_one, one_mulVec]

end RootGroup

section Characteristic2

theorem exists_transvection_mem_gramSU (hU : UnitaryFieldData 2 f E) {v : Fin 3 → E}
    (hiso : herm hU v v = 0) :
    ∃ T : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E), ∀ x,
      ((T : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x = x + (1 * herm hU v x) • v := by
  have := hU.charP
  have h1 : (1 : E) ∈ hU.traceZero := by
    rw [hU.mem_traceZero, UnitaryFieldData.trace, map_one]
    exact CharTwo.add_self_eq_zero 1
  obtain ⟨T, hT⟩ := exists_mem_unitarySU_hermTransvection hU (n := 3) (a := v) hiso h1
  refine ⟨⟨T, (unitarySU_eq_gramSU hU 3) ▸ T.2⟩, fun x => ?_⟩
  have := LinearMap.congr_fun hT x
  rwa [mulVecLin_apply, CFSG.LinearGroups.hermTransvection_apply] at this

theorem exists_mem_rootGroup_notMem (hU : UnitaryFieldData 2 f E) {v : Fin 3 → E} (hv : v ≠ 0)
    (hiso : herm hU v v = 0) :
    ∃ y ∈ rootGroup hU hiso,
      y ∉ normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3 := by
  obtain ⟨T, hTx⟩ := exists_transvection_mem_gramSU hU hiso
  refine ⟨T, ⟨1, hTx⟩, ?_⟩
  rintro ⟨c, -, -, hc⟩
  have hsc : ∀ x, ((T : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x = (c : E) • x := by
    intro x
    rw [hc, GeneralLinearGroup.coe_scalar, scalar_apply]
    funext i
    simp [mulVec_diagonal]
  have hc1 : (c : E) = 1 := by
    have h := hsc v
    rw [hTx, hiso, mul_zero, zero_smul, add_zero] at h
    by_contra hne
    apply hv
    have h2 : ((c : E) - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h := hsc (Pi.single i 1)
  rw [hTx, hc1, one_smul, add_eq_left, smul_eq_zero, one_mul] at h
  have hherm : herm hU v (Pi.single i 1) = hU.bar (v i) := by
    simp [herm, Pi.single_apply]
  rcases h with h | h
  · rw [hherm] at h
    exact (map_ne_zero hU.bar).mpr hi h
  · exact hv h

theorem benderType_primeFormP (hU : UnitaryFieldData 2 f E) (hf : 2 ≤ f) :
    BenderType (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) f 3
      ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) := by
  have := hU.finite
  obtain ⟨χ⟩ := nonempty_primeFormP_mulEquiv hU (isPrimeFormGram_one (n := 3) (K := E))
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
      CFSG.Models.benderPSU3Model_eq_psu3 f
  exact .unitary f hf (χ.trans ((unitaryPSUEquiv hU (by norm_num)).trans
    ((CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hU.card).trans
      (MulEquiv.subgroupCongr hmodel.symm))))

end Characteristic2

end IsotropicLine

open IsotropicLine

theorem exists_sylow_normalizer_of_isotropic
    (hU : UnitaryFieldData 2 f E) (hf : 2 ≤ f)
    {v : Fin 3 → E} (hv : v ≠ 0) (hiso : herm hU v v = 0) :
    ∃ Q : Sylow 2 (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)),
      ∀ g : gramSU hU 1,
        (∃ μ : E, ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ v = μ • v) →
        (QuotientGroup.mk g : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ∈
          Subgroup.normalizer
            ((Q : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) : Set _) := by
  have := hU.finite
  have := hU.charP
  set Q₀ : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) :=
    (rootGroup hU hiso).map
      (QuotientGroup.mk' (normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3))
  have hsq : ∀ x ∈ Q₀, x * x = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_mul, mul_self_eq_one_of_mem_rootGroup hiso hy, map_one]
  have hQ₀2 : IsPGroup 2 Q₀ := fun x => ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hsq x x.2)⟩
  have hQ₀ : Q₀ ≠ ⊥ := by
    obtain ⟨y, hy, hyZ⟩ := exists_mem_rootGroup_notMem hU hv hiso
    intro hbot
    have hmem : QuotientGroup.mk' _ y ∈ Q₀ := ⟨y, hy, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hyZ hmem
  obtain ⟨S, hS⟩ := hQ₀2.exists_le_sylow
  obtain ⟨t, hc⟩ := (benderType_primeFormP hU hf).exists_benderCore S
  refine ⟨S, fun g hg => ?_⟩
  obtain ⟨μ, hμ⟩ := hg
  refine IsStronglyEmbedded.mem_of_conj_mem hc.strong (hS.trans (le_borel _)) ?_ hQ₀2 hQ₀
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine le_borel _ (hS ⟨g * y * g⁻¹, conj_mem_rootGroup hiso hμ hy, ?_⟩)
  simp only [map_mul, map_inv, QuotientGroup.mk'_apply]

end CFSG.GH74.Uniqueness.Bender.Frame
