module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.LayerData
public import CFSG.LargeExtraspecial.AS35WQP45W2Data
public import Certificates.Certificate21297
public import CFSG.LargeExtraspecial.AS35WSp4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2U42

public section

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.LargeExtraspecial.AS35W

theorem exists_W2_QP45
    (s : CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45.originalSubgroup)
    (hs : s * s = 1) (hs1 : s ≠ 1) :
    ∃ y₁ y₂ : CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45.originalSubgroup,
      y₁ * s = s * y₁ ∧ y₂ * s = s * y₂ ∧ y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ (y₁ * y₂) ^ 3 ≠ 1 := by
  have hchk := Certificates.certificate21297
  unfold qp45W2Check qp45W2CheckL at hchk
  have hs2 : (s : Equiv.Perm (Fin 45)) * (s : Equiv.Perm (Fin 45)) = 1 := by
    simpa using congrArg (Subtype.val) hs
  have hs1' : (s : Equiv.Perm (Fin 45)) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hinv : invA45 (toA (s : Equiv.Perm (Fin 45))) = true := by
    unfold invA45
    rw [Bool.and_eq_true, eqA_iff (rep_compA (rep_toA _) (rep_toA _)) (rep_idA (n := 45)),
      Bool.not_eq_true', Bool.eq_false_iff, Ne, eqA_iff (rep_toA _) (rep_idA (n := 45))]
    exact ⟨hs2, hs1'⟩
  have h1 := List.all_eq_true.1 hchk (toA (s : Equiv.Perm (Fin 45))) (toA_mem_enumA s.2)
  rw [hinv, Bool.not_true, Bool.false_or] at h1
  dsimp only at h1
  obtain ⟨y₁A, hy₁A, h2⟩ := List.any_eq_true.1 h1
  obtain ⟨y₂A, hy₂A, h3⟩ := List.any_eq_true.1 h2
  rw [List.mem_filter] at hy₁A hy₂A
  obtain ⟨hy₁L, hy₁C⟩ := hy₁A
  obtain ⟨hy₂L, hy₂C⟩ := hy₂A
  rw [List.mem_filter] at hy₁L hy₂L
  obtain ⟨hy₁M, hy₁3A⟩ := hy₁L
  obtain ⟨hy₂M, hy₂3A⟩ := hy₂L
  obtain ⟨y₁, hy₁Q, hy₁eq⟩ := eq_toA_of_mem_enumA hy₁M
  obtain ⟨y₂, hy₂Q, hy₂eq⟩ := eq_toA_of_mem_enumA hy₂M
  subst hy₁eq
  subst hy₂eq
  unfold cube1A45 at hy₁3A hy₂3A
  rw [Bool.not_eq_true'] at h3
  have hcomm₁ : (⟨y₁, hy₁Q⟩ : QP45.originalSubgroup) * s = s * ⟨y₁, hy₁Q⟩ := by
    exact Subtype.ext ((eqA_iff (rep_compA (rep_toA y₁) (rep_toA (s : Equiv.Perm (Fin 45))))
      (rep_compA (rep_toA (s : Equiv.Perm (Fin 45))) (rep_toA y₁))).1 hy₁C)
  have hcomm₂ : (⟨y₂, hy₂Q⟩ : QP45.originalSubgroup) * s = s * ⟨y₂, hy₂Q⟩ := by
    exact Subtype.ext ((eqA_iff (rep_compA (rep_toA y₂) (rep_toA (s : Equiv.Perm (Fin 45))))
      (rep_compA (rep_toA (s : Equiv.Perm (Fin 45))) (rep_toA y₂))).1 hy₂C)
  have hy₁3 : (⟨y₁, hy₁Q⟩ : QP45.originalSubgroup) ^ 3 = 1 := by
    refine Subtype.ext ?_
    have h := (eqA_iff (rep_compA (rep_toA y₁) (rep_compA (rep_toA y₁) (rep_toA y₁)))
      (rep_idA (n := 45))).1 hy₁3A
    simpa [pow_succ, pow_two, mul_assoc] using h
  have hy₂3 : (⟨y₂, hy₂Q⟩ : QP45.originalSubgroup) ^ 3 = 1 := by
    refine Subtype.ext ?_
    have h := (eqA_iff (rep_compA (rep_toA y₂) (rep_compA (rep_toA y₂) (rep_toA y₂)))
      (rep_idA (n := 45))).1 hy₂3A
    simpa [pow_succ, pow_two, mul_assoc] using h
  have hyne : ((⟨y₁, hy₁Q⟩ : QP45.originalSubgroup) * ⟨y₂, hy₂Q⟩) ^ 3 ≠ 1 := by
    intro hcube
    have hc : Rep 45 (compA 45 (toA y₁) (toA y₂))
        ((y₁ : Equiv.Perm (Fin 45)) * (y₂ : Equiv.Perm (Fin 45))) :=
      rep_compA (rep_toA y₁) (rep_toA y₂)
    have hfalse : eqA 45 (compA 45 (compA 45 (toA y₁) (toA y₂))
        (compA 45 (compA 45 (toA y₁) (toA y₂)) (compA 45 (toA y₁) (toA y₂))))
        (idA 45) = false := by
      simpa [cube1A45] using h3
    have hnot : eqA 45 (compA 45 (compA 45 (toA y₁) (toA y₂))
        (compA 45 (compA 45 (toA y₁) (toA y₂)) (compA 45 (toA y₁) (toA y₂))))
        (idA 45) ≠ true := by
      rw [hfalse]
      simp
    refine hnot ((eqA_iff (rep_compA hc (rep_compA hc hc)) (rep_idA (n := 45))).2 ?_)
    simpa [pow_succ, pow_two, mul_assoc] using congrArg (Subtype.val) hcube
  exact ⟨⟨y₁, hy₁Q⟩, ⟨y₂, hy₂Q⟩, hcomm₁, hcomm₂, hy₁3, hy₂3, hyne⟩

variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {τ : MulAut X}
  {B : Subgroup X}

theorem false_of_u42
    (D : LayerData X A τ B) (h : CFSG.Blueprint.LieModel X .PSp 2 3 1) : False := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsSmall.PSp43.equiv_of_lieModel h
  have hcard : Nat.card X = 25920 := by
    rw [Nat.card_congr e.toEquiv, CFSG.HardMathSupport.Dickson.I271.card_QP45_eq]
  obtain ⟨x, hx⟩ := D.inner (by rw [hcard]; norm_num)
  have hx1 : x ≠ 1 := by
    intro h1
    apply D.ne_one
    rw [hx, h1]
    exact map_one (MulAut.conj : X →* MulAut X)
  have hxx_center : x * x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hconj : MulAut.conj (x * x) = 1 := by
      rw [map_mul, ← hx, D.sq_A τ D.mem_A]
    have h := congrArg (fun f : MulAut X => f g) hconj
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * (x * x) = ((x * x) * g * (x * x)⁻¹) * (x * x) := by rw [h]
      _ = (x * x) * g := by group
  have hZ : Subgroup.center X = ⊥ := by
    haveI : IsSimpleGroup X :=
      CFSG.HardMathSupport.Dickson.I271.isSimpleGroup_of_equiv_QP45 e
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with htop | htop
    · exact htop
    · exfalso
      obtain ⟨a, b, hab⟩ :=
        CFSG.HardMathSupport.Dickson.I271.nonabelian_of_equiv_QP45 e
      exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a)
  have hxx : x * x = 1 := by
    have hmem : x * x ∈ (⊥ : Subgroup X) := by
      rw [← hZ]
      exact hxx_center
    simpa using hmem
  have hex : e x * e x = 1 := by
    rw [← map_mul, hxx, map_one]
  have hex1 : e x ≠ 1 := fun h1 => hx1 (e.injective (by rw [h1, map_one]))
  obtain ⟨y₁, y₂, hy₁s, hy₂s, hy₁3, hy₂3, hyne⟩ := exists_W2_QP45 (e x) hex hex1
  have hfix₁ : τ (e.symm y₁) = e.symm y₁ := by
    rw [hx, MulAut.conj_apply]
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    calc e x * y₁ * (e x)⁻¹ = y₁ * (e x) * (e x)⁻¹ := by rw [← hy₁s]
      _ = y₁ := by group
  have hfix₂ : τ (e.symm y₂) = e.symm y₂ := by
    rw [hx, MulAut.conj_apply]
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    calc e x * y₂ * (e x)⁻¹ = y₂ * (e x) * (e x)⁻¹ := by rw [← hy₂s]
      _ = y₂ := by group
  have hy₁3' : (e.symm y₁) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, e.apply_symm_apply, hy₁3, map_one]
  have hy₂3' : (e.symm y₂) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, e.apply_symm_apply, hy₂3, map_one]
  have hyne' : (e.symm y₁ * e.symm y₂) ^ 3 ≠ 1 := by
    intro h1
    apply hyne
    have := congrArg e h1
    simpa [map_pow, map_mul] using this
  exact D.false_of_W2 hfix₁ hfix₂ hy₁3' hy₂3' hyne'

end CFSG.GF2Type.Smith1979.OmegaPlus
