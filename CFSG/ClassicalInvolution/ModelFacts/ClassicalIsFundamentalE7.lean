module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectStd
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {p f : ℕ} [Fact p.Prime]

theorem exists_conj_eq_rootGroup_sup_of_isClassicalMember_e7 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {L : Subgroup ↥(adjointGroup .E7 (GaloisField p f))}
    {z : ↥(adjointGroup .E7 (GaloisField p f))} (h : IsClassicalMember p f L z) :
    ∃ (g : ↥(adjointGroup .E7 (GaloisField p f))) (b : Fin Tag.E7.rank → (GaloisField p f)ˣ)
      (γ : Fin Tag.E7.rank → ℤ) (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      L = (rootGroup (rootOperatorFamily .E7) (GaloisField p f) γ ⊔
          rootGroup (rootOperatorFamily .E7) (GaloisField p f) (-γ)).map
          (MulAut.conj g⁻¹).toMonoidHom ∧
        componentRootSpan (GaloisField p f) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
          rootSubgroup .E7 (GaloisField p f) γ ⊔ rootSubgroup .E7 (GaloisField p f) (-γ) := by
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have : Finite (ModGL .E7 (GaloisField p f)) := finite_modGL
  obtain ⟨g, b, hb, hgz⟩ := e7_exists_conj_eq_rootDiagUnit_of_isClassicalMember hp2 hq h
  have hL' := isClassicalMember_map_conj hodd h g
  obtain ⟨γ, hγ, h1, h2⟩ := exists_eq_rankOne_of_isClassicalMember_toral hp2 hq b hb hgz hL'
  refine ⟨g, b, γ, hγ, ?_, h2⟩
  have hL'eq := eq_rootGroup_sup_of_map_eq (rootOperatorFamily .E7) hγ.1 (h1.trans h2)
  rw [← hL'eq, Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply]
  constructor
  · intro hx
    exact ⟨x, hx, by group⟩
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    group

theorem e7_mem_fundamentalSubgroups (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .E7 0 p f)
    [Finite ↥(e7Data_valid.minGroup (GaloisField p f))]
    {L : Subgroup ↥(e7Data_valid.minGroup (GaloisField p f))}
    {z : ↥(e7Data_valid.minGroup (GaloisField p f))} (hL : IsClassicalMember p f L z) :
    L ∈ fundamentalSubgroups .E7 (e7Datum (GaloisField p f)) := by
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hq4 : 4 ≤ p ^ f := by omega
  have hqs := isQuasisimple_e7 (GaloisField p f)
  have hθ := e7Isogeny_surjective (GaloisField p f)
  have hker : (e7Isogeny (GaloisField p f)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (exists_e7Isogeny_ne_one (GaloisField p f))
  have hz : e7Isogeny (GaloisField p f) z ≠ 1 := by
    intro h1
    have hzc : z ∈ Subgroup.center _ := hker (MonoidHom.mem_ker.2 h1)
    obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := exists_two_involutions_minGroup e7Data_valid
      (GaloisField p f) (two_ne_zero_galoisField f hp2) (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩)
      (by simp)
    by_cases h : y₁ = z
    · exact false_of_isClassicalMember_of_central (open_isQuasisimple hqs) hodd hL hzc hy₂
        (fun h' => hne (h.trans h'.symm))
    · exact false_of_isClassicalMember_of_central (open_isQuasisimple hqs) hodd hL hzc hy₁ h
  have hL' := isClassicalMember_map_central (e7Isogeny (GaloisField p f)) hθ hker hodd hL hz
  obtain ⟨g, b, γ, hγ, hLeq, -⟩ := exists_conj_eq_rootGroup_sup_of_isClassicalMember_e7 hp2 hq hL'
  have hlong := isLongestRoot_single .E7 0 p f Fact.out trivial hadm
  have hlongγ : IsLongestRoot (e7Datum (GaloisField p f)) γ :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p f)).2 hγ.1)
  set R := (e7Datum (GaloisField p f)).rootGroup γ ⊔ (e7Datum (GaloisField p f)).rootGroup (-γ)
    with hR
  have hRmem : R ∈ fundamentalSubgroups .E7 (e7Datum (GaloisField p f)) :=
    ⟨1, γ, Or.inl hlongγ, (map_conj_one R).symm⟩
  have hRperf : ⁅R, R⁆ = R :=
    le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl)
      (fundPerfect_E7 p f hq4 hadm R hRmem)
  have hRmap : R.map (e7Isogeny (GaloisField p f)) =
      rootGroup (rootOperatorFamily .E7) (GaloisField p f) γ ⊔
        rootGroup (rootOperatorFamily .E7) (GaloisField p f) (-γ) := by
    rw [hR, Subgroup.map_sup, map_e7Isogeny_rootGroup _ hγ.1,
      map_e7Isogeny_rootGroup _ (IsRoot.neg hγ.1)]
  obtain ⟨g', -, hLR⟩ := eq_map_conj_of_map_eq_central (e7Isogeny (GaloisField p f)) hθ hker hRperf
    (Subgroup.isPerfect_iff.1 hL.perfect) (c := g⁻¹) (by rw [hLeq, hRmap])
  exact ⟨g', γ, Or.inl hlongγ, hLR⟩

theorem classicalMembersFundamental_e7 {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .E7 n p f) : ClassicalMembersFundamental p f .E7 n f hp := by
  obtain rfl : n = 0 := hadm.2.2
  have hfin : Finite (Generic.modelUniv .E7 0 p f hp).K :=
    finite_modelUniv hp2 hp trivial hadm
  have : Finite ↥(e7Data_valid.minGroup (GaloisField p f)) := hfin
  intro L z hL
  exact e7_mem_fundamentalSubgroups hp2 hq hadm hL

end CFSG.ClassicalInvolution.ModelFacts
