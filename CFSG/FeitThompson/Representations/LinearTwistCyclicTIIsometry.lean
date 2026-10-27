module

public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair
import CFSG.FeitThompson.Representations.CyclicTISignedImageRecognition
import CFSG.FeitThompson.Representations.FixedDegreeCharacterSumVanishing
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
public import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

variable {G : Type*} [Group G]

theorem classFun.mul_mem {f h : G → ℂ} (hf : f ∈ classFun G) (hh : h ∈ classFun G) :
    f * h ∈ classFun G := mem_classFun.2 fun x y hxy => by
  simp only [Pi.mul_apply, classFun.apply_eq_of_isConj hf hxy, classFun.apply_eq_of_isConj hh hxy]

theorem exists_monoidHom_units_eq_of_mem_Irr_of_apply_one_eq_one {χ : G → ℂ} (hχ : χ ∈ Irr G)
    (h1 : χ 1 = 1) : ∃ ν : G →* ℂˣ, (fun g => (ν g : ℂ)) = χ := by
  obtain ⟨V, hirr, rfl⟩ := mem_Irr.1 hχ
  have hd : (finrank ℂ V.V : ℂ) = 1 := by rw [← FDRep.char_one V]; exact h1
  have hd1 : finrank ℂ V.V = 1 := by exact_mod_cast hd
  obtain ⟨ν, hν⟩ := Representation.exists_monoidHom_units_of_finrank_eq_one V.ρ hd1
  refine ⟨ν, funext fun g => ?_⟩
  have hg : V.ρ g = (ν g : ℂ) • LinearMap.id := by ext v; simpa using hν g v
  rw [FDRep.character, hg]
  simp [hd1]

theorem mul_mem_Irr_of_apply_one_eq_one {lam χ : G → ℂ} (hlam : lam ∈ Irr G) (hlam1 : lam 1 = 1)
    (hχ : χ ∈ Irr G) : lam * χ ∈ Irr G := by
  obtain ⟨ν, hν⟩ := exists_monoidHom_units_eq_of_mem_Irr_of_apply_one_eq_one hlam hlam1
  refine (show (fun x => (ν x : ℂ) * χ x) = lam * χ from by rw [← hν]; rfl) ▸ mul_mem_Irr ν hχ

theorem mul_mem_signedIrr_of_apply_one_eq_one {lam f : G → ℂ} (hlam : lam ∈ Irr G)
    (hlam1 : lam 1 = 1) (hf : f ∈ signedIrr G) : lam * f ∈ signedIrr G := by
  obtain ⟨ε, hε, ψ, hψ, rfl⟩ := mem_signedIrr_iff_exists_sign.1 hf
  refine mem_signedIrr_iff_exists_sign.2 ⟨ε, hε, lam * ψ,
    mul_mem_Irr_of_apply_one_eq_one hlam hlam1 hψ, ?_⟩
  ext x
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

def classFun.resMul (W : Subgroup G) (lam : classFun G) (f : classFun ↥W) : classFun ↥W :=
  ⟨resClassFun W (lam : G → ℂ) * (f : ↥W → ℂ),
    classFun.mul_mem (resClassFun_mem_classFun W lam.2) f.2⟩

@[simp]
theorem classFun.coe_resMul (W : Subgroup G) (lam : classFun G) (f : classFun ↥W) :
    (classFun.resMul W lam f : ↥W → ℂ) = resClassFun W (lam : G → ℂ) * (f : ↥W → ℂ) := (rfl)

theorem classFun.resMul_apply (W : Subgroup G) (lam : classFun G) (f : classFun ↥W) (x : ↥W) :
    (classFun.resMul W lam f : ↥W → ℂ) x = (lam : G → ℂ) (x : G) * (f : ↥W → ℂ) x := by
  rw [classFun.coe_resMul, Pi.mul_apply, resClassFun_apply]

@[simp]
theorem classFun.resMul_principalClassFun (W : Subgroup G) (lam : classFun G) :
    (classFun.resMul W lam (principalClassFun ↥W) : ↥W → ℂ) = resClassFun W (lam : G → ℂ) := by
  ext x
  rw [classFun.resMul_apply, principalClassFun_apply, mul_one, resClassFun_apply]

theorem classFun.resMul_add (W : Subgroup G) (lam : classFun G) (f h : classFun ↥W) :
    classFun.resMul W lam (f + h) = classFun.resMul W lam f + classFun.resMul W lam h :=
  Subtype.ext (by simp only [classFun.coe_resMul, Submodule.coe_add]; ring)

theorem classFun.resMul_smul (W : Subgroup G) (lam : classFun G) (c : ℂ) (f : classFun ↥W) :
    classFun.resMul W lam (c • f) = c • classFun.resMul W lam f :=
  Subtype.ext (by
    simp only [classFun.coe_resMul, Submodule.coe_smul_of_tower]
    ext x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring)

theorem classFun.resMul_mem_Irr {W : Subgroup G} {lam : classFun G}
    (hlam : (lam : G → ℂ) ∈ Irr G) (hlam1 : (lam : G → ℂ) 1 = 1) {f : classFun ↥W}
    (hf : (f : ↥W → ℂ) ∈ Irr ↥W) : (classFun.resMul W lam f : ↥W → ℂ) ∈ Irr ↥W := by
  obtain ⟨ν, hν⟩ := exists_monoidHom_units_eq_of_mem_Irr_of_apply_one_eq_one hlam hlam1
  refine (show (fun x : ↥W => ((ν.comp W.subtype) x : ℂ) * (f : ↥W → ℂ) x)
      = (classFun.resMul W lam f : ↥W → ℂ) from ?_) ▸ mul_mem_Irr (ν.comp W.subtype) hf
  ext x
  rw [classFun.resMul_apply]
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  rw [← hν]
  rfl

variable {W W1 W2 : Subgroup G} {σ : classFun ↥W →ₗ[ℂ] classFun G}

namespace IsCyclicTIIsometry

theorem apply_mem_signedIrr [Fintype G] [Fintype ↥W] (hσ : IsCyclicTIIsometry W W1 W2 σ)
    {χ : classFun ↥W} (hχ : (χ : ↥W → ℂ) ∈ Irr ↥W) : (σ χ : G → ℂ) ∈ signedIrr G :=
  mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one
    (mem_virtualChars_iff.1 (hσ.map_virtualChars χ (Irr_subset_virtualChars hχ)))
    (by rw [hσ.inner_eq]; exact cfInner_self_of_mem_Irr hχ)

theorem apply_resMul [Fintype G] [Fintype ↥W] (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {lam : classFun G} (hlam : (lam : G → ℂ) ∈ Irr G)
    (hlam1 : (lam : G → ℂ) 1 = 1) {χ : classFun ↥W} (hχ : (χ : ↥W → ℂ) ∈ Irr ↥W) :
    (σ (classFun.resMul W lam χ) : G → ℂ) = (lam : G → ℂ) * (σ χ : G → ℂ) := by
  refine (eq_apply_of_eqOn_cyclicTIDiff hW hσ (classFun.resMul_mem_Irr hlam hlam1 hχ)
    (mul_mem_signedIrr_of_apply_one_eq_one hlam hlam1 (hσ.apply_mem_signedIrr hχ)) ?_).symm
  intro v hv
  rw [Pi.mul_apply, hσ.apply_eq_of_mem_cyclicTIDiff hW χ hv, classFun.resMul_apply]

end IsCyclicTIIsometry

end CFSG.FeitThompson
