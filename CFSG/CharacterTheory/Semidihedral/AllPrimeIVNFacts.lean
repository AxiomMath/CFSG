module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeNbarFacts
public import CFSG.CharacterTheory.Semidihedral.AllPrimeII42
public import CFSG.CharacterTheory.Semidihedral.AllPrimeTorusFacts
public import CFSG.LocalAnalysis.ABGTheoremB.IVNFacts

public section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion

theorem frontier_ivNFacts {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).IVNFacts where
  L_normal := frontier_L_normal hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  C_odd_le_oddCore := frontier_C_odd hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
  C_le_oddCore_sup_D := frontier_C_le n hn S fS t ht p f
  N_mod_L_cyclic := frontier_N_mod_L_cyclic hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd
    hf hq hmodel
  C_inf_L_commutator := frontier_C_inf_L_commutator hGnonab n hn S fS t ht hnonab hcentral hnc p f
    hp hpodd hf hq hmodel
  exists_inverting_D_L₀ := frontier_II42i hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  C_inf_L₀_commutator := frontier_II42ii hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  center_le_L_or_inf_L_le := frontier_II42v hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd
    hf hq hmodel
  centralizer_SL2_section := frontier_II42vi hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd
    hf hq hmodel
  L_centralizer_D_odd_le := frontier_II43iii hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd
    hf hq hmodel
  frobenius_section := frontier_II43 hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
  oddCore_C_inf_L₀_cyclic := frontier_V3_cyclic hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel
  oddCore_C_inf_L₀_coprime := frontier_V3_order hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel
  oddCore_C_inf_L₀_centralized := frontier_V3_centralized hGnonab n hn S fS t ht hnonab hcentral hnc
    p f hp hpodd hf hq hmodel
  oddCore_C_inf_L₀_inverted := frontier_V3_inverted hGnonab n hn S fS t ht hnonab hcentral hnc p f
    hp hpodd hf hq hmodel
  sylow_quaternion_element := frontier_quaternion_element_of_le n hn S fS t ht p f
  propIV51 := Setting.propIV51_of_height_eq_one _ rfl

end CFSG.Semidihedral.AllPrime
