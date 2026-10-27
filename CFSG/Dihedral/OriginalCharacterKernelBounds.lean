module

public import CFSG.Dihedral.OriginalPresentation
import all CFSG.Dihedral.BlueprintDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerOddPart
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenOrderThreeSubgroupCentralizerCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem R_le_fourgroup_centralizer (i : Fin 2) (hi : d.E i = d.R) :
    d.R ≤ Subgroup.centralizer (d.V i : Set G) := by
  rw [← hi]
  exact inf_le_right

theorem fourgroup_le_R_centralizer (i : Fin 2) (hi : d.E i = d.R) :
    d.V i ≤ Subgroup.centralizer (d.R : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact (Subgroup.mem_centralizer_iff.mp (d.R_le_fourgroup_centralizer i hi hr)) v hv |>.symm

theorem R_card_eq_three_of_aSeven_model
    (hn : d.n = 3) (hindex : (d.commonE.subgroupOf d.R).index = 3)
    (e : G ≃* alternatingGroup (Fin 7)) : Nat.card d.R = 3 := by
  let RA := d.R.map e.toMonoidHom
  have hcard : Nat.card RA = Nat.card d.R := Subgroup.card_map_of_injective e.injective
  have hodd : Odd (Nat.card RA) := by rw [hcard]; exact d.R_odd
  have ht : BenderSuzuki.PFAppendixIII.IsInvolution (e d.t) := by
    have h := d.t_isInvolution hn
    refine ⟨?_, ?_⟩
    · intro he
      exact h.1 (e.injective (by simpa using he))
    · simpa using congrArg e h.2
  have hcentral : RA ≤ Subgroup.centralizer ({e d.t} : Set (alternatingGroup (Fin 7))) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hrC : r ∈ Subgroup.centralizer ({d.t} : Set G) := by
      simpa only [d.centralizer, t] using d.R_le hr
    simpa using congrArg e (Subgroup.mem_centralizer_singleton_iff.mp hrC)
  have hle : Nat.card d.R ≤ 3 := by
    rw [← hcard]
    exact aSeven_odd_subgroup_centralizing_involution_card_le_three hodd ht hcentral
  have hE : d.commonE ≤ d.R := inf_le_left
  have hEcard : Nat.card (d.commonE.subgroupOf d.R) = Nat.card d.commonE :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have hmul := Subgroup.card_mul_index (d.commonE.subgroupOf d.R)
  rw [hEcard, hindex] at hmul
  have hpos : 0 < Nat.card d.commonE := Nat.card_pos
  omega

theorem normalizer_card_le_twice_centralizer_of_card_three
    (A : Subgroup G) (hcard : Nat.card A = 3) :
    Nat.card (Subgroup.normalizer (A : Set G)) ≤
      2 * Nat.card (Subgroup.centralizer (A : Set G)) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic A := isCyclic_of_prime_card hcard
  have hAut : Nat.card (MulAut A) = 2 := by
    rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime Nat.prime_three]
  let alpha := A.normalizerMonoidHom
  have hrange : Nat.card alpha.range ≤ 2 := by
    rw [← hAut]
    exact Nat.card_le_card_of_injective _ alpha.range.subtype_injective
  have hker : Nat.card alpha.ker = Nat.card (Subgroup.centralizer (A : Set G)) := by
    rw [Subgroup.normalizerMonoidHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (A : Set G))).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range alpha
  rw [hker] at hmul
  calc
    Nat.card (Subgroup.normalizer (A : Set G)) =
        Nat.card (Subgroup.centralizer (A : Set G)) * Nat.card alpha.range := hmul.symm
    _ ≤ Nat.card (Subgroup.centralizer (A : Set G)) * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card (Subgroup.centralizer (A : Set G)) := Nat.mul_comm _ _

theorem N_card_le_seventy_two_of_aSeven_model
    (hn : d.n = 3) (hindex : (d.commonE.subgroupOf d.R).index = 3)
    (i : Fin 2) (hi : d.E i = d.R) (e : G ≃* alternatingGroup (Fin 7)) :
    Nat.card d.N ≤ 72 := by
  let RA := d.R.map e.toMonoidHom
  let VA := (d.V i).map e.toMonoidHom
  have hRA : Nat.card RA = 3 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact d.R_card_eq_three_of_aSeven_model hn hindex e
  have hVA : IsKleinFour VA :=
    isKleinFour_map_mulEquiv_cross (d.V i) (d.V_isKleinFour hn i) e
  have hcent : VA ≤ Subgroup.centralizer (RA : Set (alternatingGroup (Fin 7))) :=
    centralizer_map_le_of_mulEquiv e d.R (d.V i) (d.fourgroup_le_R_centralizer i hi)
  have hcentcard : Nat.card (Subgroup.centralizer (RA : Set (alternatingGroup (Fin 7)))) = 36 :=
    aSeven_order_three_subgroup_centralizer_card_eq_thirty_six RA VA hRA hVA hcent
  have hbound := normalizer_card_le_twice_centralizer_of_card_three RA hRA
  rw [hcentcard] at hbound
  have hNmap : d.N.map e.toMonoidHom = Subgroup.normalizer (RA : Set (alternatingGroup (Fin 7))) :=
    Subgroup.map_normalizer_eq_of_bijective d.R e.bijective
  have hNcard : Nat.card d.N = Nat.card (Subgroup.normalizer (RA : Set (alternatingGroup (Fin 7)))) := by
    rw [← hNmap, Subgroup.card_map_of_injective e.injective]
  rwa [hNcard]

theorem quotient_card_eq_one_hundred_twenty_of_pure_coordinates
    (hp : d.PureProjectiveNormalizer)
    (w : CoordinateWitness (d.N ⧸ Assembly.oddCore d.N)) (hq : Nat.card w.K = 5) :
    Nat.card (d.N ⧸ Assembly.oddCore d.N) = 120 := by
  have hrange : w.rho.range = pGammaL2PGLRange w.K := (hp.2.2.2.1 w).1
  let e := (MonoidHom.ofInjective w.injective).trans
    (MulEquiv.subgroupCongr hrange) |>.trans (pGammaL2PGLRangeEquiv w.K).symm
  calc
    Nat.card (d.N ⧸ Assembly.oddCore d.N) = Nat.card (PGL2 w.K) := Nat.card_congr e.toEquiv
    _ = 120 := by rw [pgl2_card_formula, hq]; norm_num

end CFSG.DihedralBlueprint.OriginalData
