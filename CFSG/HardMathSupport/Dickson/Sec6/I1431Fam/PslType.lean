module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Descend
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transfer
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne.Sec66T
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem isTypeL2_congr_of_central {r : ℕ} {Y Y' : Type} [Group Y] [Group Y']
    (hY : Group.IsPerfect Y) (f : Y →* Y') (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center Y) : IsTypeL2 r Y ↔ IsTypeL2 r Y' := by
  have e := centerQuotEquiv hY f hf hker
  constructor
  · rintro ⟨F, hF, hFin, hcard, ⟨g⟩⟩
    exact ⟨F, hF, hFin, hcard, ⟨e.symm.trans g⟩⟩
  · rintro ⟨F, hF, hFin, hcard, ⟨g⟩⟩
    exact ⟨F, hF, hFin, hcard, ⟨e.trans g⟩⟩

theorem not_isTypeL2_specialLinear (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {m : ℕ} (hm : 3 ≤ m) {E : Type} [Field E] [Finite E] {r : ℕ} (hr : 10 ≤ r) :
    ¬ IsTypeL2 r (Matrix.SpecialLinearGroup (Fin m) E) := by
  intro hT
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) E) :=
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (K := E) hm).1
  have h1 : IsTypeL2 r (projectiveSL m E) :=
    (isTypeL2_congr_of_central hperf (proj m E) (proj_surjective m E)
      (by rw [ker_proj]; exact scalars_le_center m E)).1 hT
  have h2 : IsTypeL2 r (StatedProj (StatedSL m E)) :=
    p6_isTypeL2_of_equiv (CFSG.ComponentClassification.RankTwoClassical.statedProjEquiv m E).symm h1
  have := Fintype.ofFinite E
  obtain ⟨f, hℓ, hE⟩ := FiniteField.card E (ringChar E)
  have hcard : Nat.card E = ringChar E ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hE]
  have hadm : StatedLieAdmissible .PSL m (ringChar E) f :=
    ⟨hℓ, f.pos, by omega, fun hc => by have := (Prod.mk.inj hc).1; omega,
      fun hc => by have := (Prod.mk.inj hc).1; omega⟩
  have hmodel : LieModel (StatedProj (StatedSL m E)) .PSL m (ringChar E) f :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, E, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩
  haveI hsP : IsSimpleGroup (projectiveSL m E) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL hm
  haveI hs : IsSimpleGroup (StatedProj (StatedSL m E)) :=
    (CFSG.ComponentClassification.RankTwoClassical.statedProjEquiv m E).isSimpleGroup
  have hnab : ∃ a b : StatedProj (StatedSL m E), a * b ≠ b * a := by
    have h3 := CFSG.RankThree.PartOne.KCLinearSubfield.not_commutative_projectiveSL (n := m)
      (K := E) hm
    push Not at h3
    obtain ⟨a, b, hab⟩ := h3
    refine ⟨(CFSG.ComponentClassification.RankTwoClassical.statedProjEquiv m E).symm a,
      (CFSG.ComponentClassification.RankTwoClassical.statedProjEquiv m E).symm b, fun h => hab ?_⟩
    have := congrArg (CFSG.ComponentClassification.RankTwoClassical.statedProjEquiv m E) h
    simpa using this
  exact not_typeL2_of_lieModel hO hadm hmodel (by decide) (by simp; omega)
    (center_eq_bot_of_simple hnab) hr h2

section Block

open Polynomial Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.CALinearPrimary

variable {n : ℕ} {K : Type} [Field K] [Finite K] {a : SpecialLinearGroup (Fin n) K}

theorem pslBlock_multiplicity_eq_two (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hpk : (3 : K) ≠ 0) (hap : a ^ 3 = 1) {h : K[X]}
    (hh : h ∈ primaryFactors ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (hgood : 3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) h ∨
      (2 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) h ∧ 4 ≤ Nat.card (AdjoinRoot h)))
    {r : ℕ} (hr : 10 ≤ r) (hT : IsTypeL2 r (pslBlock a h)) :
    primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) h = 2 := by
  by_contra hne
  have hm3 : 3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) h := by
    rcases hgood with h3 | ⟨h2, -⟩
    · exact h3
    · omega
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hsq := squarefree_minpoly_slGL hpk hap
  set F' := (linearSpecialBlock (slGL n K a) h).comap (slGL n K) with hF'
  obtain ⟨eF⟩ := comap_linearSpecialBlock_mulEquiv hsq hh
  have hFq : CFSG.IsQuasisimple F' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eF.symm (isQuasisimple_linearSpecialBlock hsq hh hgood)
  have h1 : IsTypeL2 r F' := by
    refine (isTypeL2_congr_of_central hFq.1 ((proj n K).subgroupMap F')
      ((proj n K).subgroupMap_surjective F') ?_).2 hT
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : proj n K (x : SpecialLinearGroup (Fin n) K) = 1 := congrArg Subtype.val hx
    have hxc : (x : SpecialLinearGroup (Fin n) K) ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
      scalars_le_center n K (proj_eq_one_iff.mp hx1)
    rw [Subgroup.mem_center_iff]
    intro g'
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hxc) g')
  have h2 : IsTypeL2 r (linearSpecialBlock (slGL n K a) h) := p6_isTypeL2_of_equiv eF h1
  let b : Module.Basis (Fin (primaryMultiplicity ((slGL n K a :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) h)) (AdjoinRoot h)
      (primaryComponent ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : linearSpecialBlock (slGL n K a) h ≃*
      _root_.SpecialLinearGroup (AdjoinRoot h) (primaryComponent ((slGL n K a :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) h) :=
    MulEquiv.ofBijective (linearSpecialBlockRestrict (slGL n K a) h)
      ⟨linearSpecialBlockRestrict_injective hsq, linearSpecialBlockRestrict_surjective hsq hh⟩
  have h3 := p6_isTypeL2_of_equiv ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm).symm h2
  exact not_isTypeL2_specialLinear hO hm3 hr h3

end Block

section BarX

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem nontrivial_of_isQuasisimple' {Y : Type*} [Group Y] (hY : Open.IsQuasisimple Y) :
    Nontrivial Y := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hs2 : Subsingleton (Y ⧸ Subgroup.center Y) :=
    (QuotientGroup.mk'_surjective (Subgroup.center Y)).subsingleton
  exact (not_nontrivial_iff_subsingleton.2 hs2) hY.2.toNontrivial

theorem isTypeL2_of_barX_eq {X J N : Subgroup G} (hJ : GLAPComponent 3 X J) (hNX : N ≤ X)
    (hNn : ∀ c ∈ X, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hNq : CFSG.IsQuasisimple N)
    (hbar : barX 3 X J = barX 3 X N) {q : ℕ} (hq : IsTypeL2 q (barOf 3 J)) :
    IsTypeL2 q N := by
  have hNsub : IsSubnormal N X := by
    refine IsSubnormal.step hNX ?_ (IsSubnormal.refl X)
    rw [Subgroup.normal_subgroupOf_iff hNX]
    exact fun x c hx hc => hNn c hc x hx
  have hJQ : Open.IsQuasisimple (barOf 3 J) :=
    isQuasisimple_quotient_of_glaPComponent hJ
  have h1 : IsTypeL2 q ↥(barX 3 X J) :=
    p6_isTypeL2_of_equiv (barXEquiv Nat.prime_three hJ.2.1) hq
  have h2 : IsTypeL2 q ↥(barX 3 X N) := by
    rw [← hbar]
    exact h1
  have hnt : Nontrivial ↥(barX 3 X N) := by
    rw [← hbar]
    exact nontrivial_of_isQuasisimple' ((isQuasisimple_barX_iff Nat.prime_three hJ.2.1).2 hJQ)
  have hρs : Function.Surjective (barXHom 3 hNX) := barXHom_surjective 3 hNX
  have hcentral : (barXHom 3 hNX).ker ≤ Subgroup.center ↥N := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hNq (barXHom 3 hNX).normal_ker with h | h
    · exfalso
      have hsub : Subsingleton ↥(barX 3 X N) := ⟨fun u v => by
        obtain ⟨u', rfl⟩ := hρs u
        obtain ⟨v', rfl⟩ := hρs v
        have hu : u' ∈ (barXHom 3 hNX).ker := by rw [h]; exact Subgroup.mem_top u'
        have hv : v' ∈ (barXHom 3 hNX).ker := by rw [h]; exact Subgroup.mem_top v'
        rw [MonoidHom.mem_ker] at hu hv
        rw [hu, hv]⟩
      exact (not_nontrivial_iff_subsingleton.2 hsub) hnt
    · exact h
  exact (isTypeL2_congr_of_central hNq.1 (barXHom 3 hNX) hρs hcentral).2 h2

end BarX

end CFSG.HardMathSupport.Dickson.Sec6.I1431
