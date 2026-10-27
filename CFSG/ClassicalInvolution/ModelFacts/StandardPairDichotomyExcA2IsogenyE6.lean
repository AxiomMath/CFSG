module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyLift
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryE6Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2InterfaceE6
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate120
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts

variable {p e : ℕ} [Fact p.Prime]

theorem e6Isogeny_ker_odd : Odd (Nat.card (e6Isogeny (GaloisField p e)).ker) := by
  have : Finite (E6sc p e) := ChevAut.finite_minGroup e6Data_valid (GaloisField p e)
  by_contra hodd
  have h2 : 2 ∣ Nat.card (e6Isogeny (GaloisField p e)).ker :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have h3 : (x : E6sc p e) ^ 3 = 1 :=
    A2Isogeny.center_pow_three_e6 (GaloisField p e)
      (ChevAut.e6Isogeny_ker_le_center (GaloisField p e) x.2)
  have h4 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext h3)
  rw [hx] at h4
  omega

theorem a2UnitaryE6 : A2UnitaryE6 p e := by
  intro hadm hp2 hq R₂ c₂ hR₂ hc₂ ho _ _ hv
  have hne : NeZero e := ⟨by rintro rfl; simp at hq⟩
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hcard : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  have hR₁ := stdRankOne_mem_longestFundamental_E6 (p := p) (e := e) hadm isRoot_thetaE6
  have : Finite (E6sc p e) := ChevAut.finite_minGroup e6Data_valid (GaloisField p e)
  exact exists_uni_of_map_odd hp2 hcard hq (e6Isogeny (GaloisField p e))
    (ChevAut.e6Isogeny_ker_le_center (GaloisField p e)) e6Isogeny_ker_odd
    (commutator_eq_of_mem_longestFundamental (t := .E6) hp2 hq trivial hadm hR₁)
    (commutator_eq_of_mem_longestFundamental (t := .E6) hp2 hq trivial hadm hR₂)
    (a2UnitaryImageE6 hadm hp2 hq hR₂ hc₂ ho hv)

end CFSG.ClassicalInvolution.ModelFacts.Levi
