module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectStd
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime]

theorem e6_mem_fundamentalSubgroups (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .E6 0 p f)
    [Finite ↥(e6Data_valid.minGroup (GaloisField p f))]
    {L : Subgroup ↥(e6Data_valid.minGroup (GaloisField p f))}
    {z : ↥(e6Data_valid.minGroup (GaloisField p f))} (hL : IsClassicalMember p f L z) :
    L ∈ fundamentalSubgroups .E6 (e6Datum (GaloisField p f)) := by
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hq4 : 4 ≤ p ^ f := by omega
  have hqs := isQuasisimple_e6 (GaloisField p f)
  have hθ := e6Isogeny_surjective (GaloisField p f)
  have hker : (e6Isogeny (GaloisField p f)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (e6Isogeny_ne_one (GaloisField p f))
  have hz : e6Isogeny (GaloisField p f) z ≠ 1 := by
    intro h1
    have hzc : z ∈ Subgroup.center _ := hker (MonoidHom.mem_ker.2 h1)
    obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := exists_two_involutions_minGroup e6Data_valid
      (GaloisField p f) (two_ne_zero_galoisField f hp2) (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩)
      (by simp)
    by_cases h : y₁ = z
    · exact false_of_isClassicalMember_of_central (open_isQuasisimple hqs) hodd hL hzc hy₂
        (fun h' => hne (h.trans h'.symm))
    · exact false_of_isClassicalMember_of_central (open_isQuasisimple hqs) hodd hL hzc hy₁ h
  have hL' := isClassicalMember_map_central (e6Isogeny (GaloisField p f)) hθ hker hodd hL hz
  obtain ⟨g, b, γ, hγ, hLeq, -⟩ := exists_conj_eq_rootGroup_sup_of_isClassicalMember
    (τ := .E6) (Or.inr (Or.inr (Or.inl rfl))) hp2 hq hL'
  have hlong := isLongestRoot_single .E6 0 p f Fact.out trivial hadm
  have hlongγ : IsLongestRoot (e6Datum (GaloisField p f)) γ :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField p f)).2 hγ.1)
  set R := (e6Datum (GaloisField p f)).rootGroup γ ⊔ (e6Datum (GaloisField p f)).rootGroup (-γ)
    with hR
  have hRmem : R ∈ fundamentalSubgroups .E6 (e6Datum (GaloisField p f)) :=
    ⟨1, γ, Or.inl hlongγ, (map_conj_one R).symm⟩
  have hRperf : ⁅R, R⁆ = R :=
    le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl)
      (fundPerfect_E6 p f hq4 hadm R hRmem)
  have hRmap : R.map (e6Isogeny (GaloisField p f)) =
      rootGroup (rootOperatorFamily .E6) (GaloisField p f) γ ⊔
        rootGroup (rootOperatorFamily .E6) (GaloisField p f) (-γ) := by
    rw [hR, Subgroup.map_sup, map_e6Isogeny_rootGroup _ hγ.1,
      map_e6Isogeny_rootGroup _ (IsRoot.neg hγ.1)]
  obtain ⟨g', -, hLR⟩ := eq_map_conj_of_map_eq_central (e6Isogeny (GaloisField p f)) hθ hker hRperf
    (Subgroup.isPerfect_iff.1 hL.perfect) (c := g⁻¹) (by rw [hLeq, hRmap])
  exact ⟨g', γ, Or.inl hlongγ, hLR⟩

theorem classicalMembersFundamental_e6 {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .E6 n p f) : ClassicalMembersFundamental p f .E6 n f hp := by
  obtain rfl : n = 0 := hadm.2.2
  have hfin : Finite (Generic.modelUniv .E6 0 p f hp).K :=
    finite_modelUniv hp2 hp trivial hadm
  have : Finite ↥(e6Data_valid.minGroup (GaloisField p f)) := hfin
  intro L z hL
  exact e6_mem_fundamentalSubgroups hp2 hq hadm hL

end CFSG.ClassicalInvolution.ModelFacts
