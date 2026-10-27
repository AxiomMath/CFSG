module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyLift
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryE7Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2InterfaceE7
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts

variable {p e : ℕ} [Fact p.Prime]

theorem e7Isogeny_ker_sq (x : E7sc p e) (hx : x ∈ (e7Isogeny (GaloisField p e)).ker) :
    x * x = 1 := by
  have := A2Isogeny.center_pow_two_e7 (GaloisField p e)
    (ChevAut.e7Isogeny_ker_le_center (GaloisField p e) hx)
  rwa [pow_two] at this

theorem a2UnitaryE7 : A2UnitaryE7 p e := by
  intro hadm hp2 hq R₂ c₂ hR₂ hc₂ ho _ _ hv
  have hne : NeZero e := ⟨by rintro rfl; simp at hq⟩
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hcard : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  have hR₁ := stdRankOne_mem_longestFundamental_E7 (p := p) (e := e) hadm isRoot_thetaE7
  have : Finite (E7sc p e) := ChevAut.finite_minGroup e7Data_valid (GaloisField p e)
  exact exists_uni_of_map hp2 hcard hq (e7Isogeny (GaloisField p e))
    (ChevAut.e7Isogeny_ker_le_center (GaloisField p e)) e7Isogeny_ker_sq
    (commutator_eq_of_mem_longestFundamental (t := .E7) hp2 hq trivial hadm hR₁)
    (commutator_eq_of_mem_longestFundamental (t := .E7) hp2 hq trivial hadm hR₂)
    (a2UnitaryImageE7 hadm hp2 hq hR₂ hc₂ ho hv)

end CFSG.ClassicalInvolution.ModelFacts.Levi
