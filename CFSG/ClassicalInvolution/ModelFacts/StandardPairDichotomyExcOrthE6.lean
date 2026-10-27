module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAdj
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Main
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Models.SymplecticPairs

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Levi

variable {p e : ℕ} [Fact p.Prime]

theorem map_stdRankOne_excEmbed_e6 [NeZero e] :
    (stdRankOne (Generic.modelUniv .E6 0 p e Fact.out).D thetaE6).map (excEmbed .E6 p e) =
      rootRankOneGroup .E6 (GaloisField p e) thetaE6 := by
  have hmap := map_stdRankOne_e6 (p := p) (e := e)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : e6Isogeny (GaloisField p e) x ∈
        stdRankOne (e6AdjDatum (GaloisField p e)) thetaE6 := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨A, hA⟩ := (mem_stdRankOne_e6_iff _).1 hx'
    exact ⟨A, hA.symm⟩
  · rintro ⟨A, rfl⟩
    have hx' : (⟨rootSL2 .E6 (GaloisField p e) thetaE6 A, rootSL2_mem_adjointGroup _ _⟩ :
        ↥(adjointGroup .E6 (GaloisField p e))) ∈
          stdRankOne (e6AdjDatum (GaloisField p e)) thetaE6 :=
      (mem_stdRankOne_e6_iff _).2 ⟨A, rfl⟩
    rw [← hmap] at hx'
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hx'
    exact ⟨x, hx, congrArg Subtype.val hxy⟩

theorem orthBranch_e6 (hadm : StatedLieAdmissible .E6 0 p e) : OrthBranch p .E6 0 e := by
  intro hp2 hq
  have : NeZero e := ⟨by rintro rfl; simp at hq⟩
  have hlong := isLongestRoot_single .E6 0 p e Fact.out trivial hadm
  have hθ : Generic.IsLongestRoot (Generic.modelUniv .E6 0 p e Fact.out).D thetaE6 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField p e)).2
        isRoot_thetaE6)
  refine (orthBranch_of_adjointEmbedding (t := .E6) hp2 hq trivial (by decide) (by decide) hadm
    (excEmbed .E6 p e) (fun x => (e6Isogeny (GaloisField p e) x).2) ?_ (excSignGroup .E6 p e)
    (fun c hc => mem_excSignGroup.1 hc) (pairFrame_e6 hp2 hadm)
    (fundamentalSingleClass .E6 0 p e Fact.out trivial hadm (by decide) (by decide))
    (Rθ := stdRankOne (Generic.modelUniv .E6 0 p e Fact.out).D thetaE6)
    ⟨1, thetaE6, Or.inl hθ, (Generic.conjSub_one _).symm⟩
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inl rfl) isRoot_thetaE6) map_stdRankOne_excEmbed_e6
    fun _ γ hγ _ => isLongRoot_of_isRoot_of_simplyLaced (Or.inl rfl) hγ.1) hp2 hq
  intro x hx
  have h1 : ((e6Isogeny (GaloisField p e) x : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e)) = 1 := MonoidHom.mem_ker.1 hx
  exact (ker_le_center_of_isQuasisimple (isQuasisimple_e6 (GaloisField p e))
    (e6Isogeny_ne_one (GaloisField p e))) (MonoidHom.mem_ker.2 (Subtype.ext h1))

end CFSG.ClassicalInvolution.ModelFacts
