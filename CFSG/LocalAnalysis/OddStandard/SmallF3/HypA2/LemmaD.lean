module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaDAlpha
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaDBeta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaDSetup

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem false_of_noncentralDatum (hI : Phase1Inputs) (hA7 : TwoA7RankOne) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Catalog G → ¬ Catalog G →
    (∀ z : G, orderOf z = 2 → oddCore ↥(centralizer ({z} : Set G)) = ⊥) →
    ∀ (y : G) (K : Subgroup G), orderOf y = 2 →
      Omega.IsComponentIn K (centralizer ({y} : Set G)) → NoncentralDatum ↥K → False := by
  intro G _ _ _ hnonab hKP hcat hbal y K hy hK hd
  obtain ⟨z, T, N, q₀, h⟩ := exists_ncData_of_noncentralDatum hy hK hd
  obtain ⟨M, hM, hcase⟩ := pump_of_ncData h (hbal z h.oz)
  rcases hcase with ⟨hMy, hTM⟩ | ⟨hne, hcomm, φ, hφ, hTφ, hker⟩
  · exact false_of_pump_vertical hI hA7 hnonab hKP hcat h hM hMy hTM
  · exact false_of_pump_diagonal hI hA7 hnonab hKP hcat h (hbal z h.oz) hM hne hcomm φ hφ hTφ hker

theorem false_of_centralDatum (hI : Phase1Inputs) (hA7 : TwoA7RankOne) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Catalog G → ¬ Catalog G →
    ∀ (y : G) (K : Subgroup G), orderOf y = 2 →
      Omega.IsComponentIn K (centralizer ({y} : Set G)) → CentralDatum ↥K → False := by
  intro G _ _ _ hnonab hKP hcat y K hy hK hd
  obtain ⟨q₀, N, z, hq, h5, hz2, hzc, hzN, hSL, hTU⟩ := hd
  have hc : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz2
  have hcN' : (z : G) ∈ N.map K.subtype := Subgroup.mem_map_of_mem K.subtype hzN
  have hcK : (z : G) ∈ (center ↥K).map K.subtype := Subgroup.mem_map_of_mem K.subtype hzc
  have hN'K : N.map K.subtype ≤ K := Subgroup.map_subtype_le N
  have hSL' : HarrisLit.IsSLTwoOver q₀ ↥(N.map K.subtype) := by
    obtain ⟨F, hF, hFint, hcard, ⟨eF⟩⟩ := hSL
    exact ⟨F, hF, hFint, hcard,
      ⟨(N.equivMapOfInjective K.subtype K.subtype_injective).symm.trans eF⟩⟩
  exact false_of_datum_typU hI hA7 G hnonab hKP hcat q₀ hq h5 y K (N.map K.subtype) (z : G)
    (isDatum_of_central (v := y) hy hK hN'K hq h5 hSL' hc hcN' hcK) hTU

theorem false_of_kDatum (hI : Phase1Inputs) (hA7 : TwoA7RankOne) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Catalog G → ¬ Catalog G →
    (∀ z : G, orderOf z = 2 → oddCore ↥(centralizer ({z} : Set G)) = ⊥) →
    ∀ (y : G) (K : Subgroup G), orderOf y = 2 →
      Omega.IsComponentIn K (centralizer ({y} : Set G)) → KDatum ↥K → False := by
  intro G _ _ _ hnonab hKP hcat hbal y K hy hK hd
  rcases hd with hc | hnc
  · exact false_of_centralDatum hI hA7 G hnonab hKP hcat y K hy hK hc
  · exact false_of_noncentralDatum hI hA7 G hnonab hKP hcat hbal y K hy hK hnc

end CFSG.OddStandard.SmallF3.HypA2
