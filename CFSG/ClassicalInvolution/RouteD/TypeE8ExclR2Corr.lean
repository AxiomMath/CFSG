module

public import CFSG.ClassicalInvolution.RouteD.TypeE8Excl
public import CFSG.ClassicalInvolution.RouteD.NonClassicalShape
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
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

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}
  {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)} {i : Fin D.card}

section Involutions

variable [Finite G]

theorem corr_exists_involution (hMFZ : FundNoncentral p)
    (hA1 : ¬ (D.tag i = .PSL ∧ D.rank i = 2)) {L : Subgroup G}
    {R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hL : Corr Ω x D i L R) {w : G} (hw : IsClassicalMember p f L w) :
    ∃ r, InvOf R r ∧ D.hom i r = locElt Ω x w (le_centralizingLayer hL.1 hw.mem) := by
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hL.1 hw.mem
  have hmem : locElt Ω x w hwx ∈ R.map (D.hom i) :=
    hL.2.2 ▸ locElt_mem_locImg (le_centralizingLayer hL.1) hw.mem
  obtain ⟨r, hrR, hr⟩ := hmem
  have h2 : orderOf (D.hom i r) = 2 := by
    rw [hr]
    exact orderOf_locElt hwx hw.orderOf_eq_two
  have hsq : r * r = 1 := by
    have h1 : D.hom i (r * r) = 1 := by
      rw [map_mul]
      have := pow_orderOf_eq_one (D.hom i r)
      rwa [h2, pow_two] at this
    have hc : r * r ∈ Subgroup.center (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K :=
      D.ker_le_center i h1
    exact hMFZ (D.tag i) (D.rank i) (D.exp i) (D.isFundTag i) (D.admissible i) hA1 R hL.2.1
      (r * r) (R.mul_mem hrR hrR) fun y => by
        have h3 := Subgroup.mem_center_iff.mp hc y
        have e : r * r * y * (r * r)⁻¹ * y⁻¹ = 1 := by
          rw [← h3]
          group
        rw [e]
        exact Subgroup.one_mem _
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, map_one] at h2
    simp at h2
  exact ⟨r, ⟨hrR, orderOf_eq_prime (by rw [pow_two]; exact hsq) hr1⟩, hr⟩

theorem corr_modelInvComm (hMFZ : FundNoncentral p) (hA1 : ¬ (D.tag i = .PSL ∧ D.rank i = 2))
    {L L' : Subgroup G}
    {R R' : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hL : Corr Ω x D i L R) (hL' : Corr Ω x D i L' R') {w w' : G}
    (hw : IsClassicalMember p f L w) (hw' : IsClassicalMember p f L' w') (hc : Commute w w') :
    ∃ r r', InvOf R r ∧ InvOf R' r' ∧
      ⁅r, r'⁆ ∈ Subgroup.center (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K ∧
      D.hom i r = locElt Ω x w (le_centralizingLayer hL.1 hw.mem) ∧
      D.hom i r' = locElt Ω x w' (le_centralizingLayer hL'.1 hw'.mem) := by
  obtain ⟨r, hr, hψr⟩ := corr_exists_involution hMFZ hA1 hL hw
  obtain ⟨r', hr', hψr'⟩ := corr_exists_involution hMFZ hA1 hL' hw'
  refine ⟨r, r', hr, hr', D.ker_le_center i ?_, hψr, hψr'⟩
  have hcomm : D.hom i r * D.hom i r' = D.hom i r' * D.hom i r := by
    rw [hψr, hψr', locElt_mul, locElt_mul]
    congr 1
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

omit [Finite G] in
theorem corr_normalizes
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {L : Subgroup G} {R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hL : Corr Ω x D i L R) {w' : G} (hwx : w' ∈ locLayer Ω x)
    {r' : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hr : D.hom i r' = locElt Ω x w' hwx) (hN : conjSub w' L = L) :
    ∀ y ∈ R, r' * y * r'⁻¹ ∈ R := by
  refine conj_mem_of_perfect (hperf R hL.2.1) r' fun y hy => ?_
  have hmem : D.hom i (r' * y * r'⁻¹) ∈ R.map (D.hom i) := by
    have h1 : D.hom i y ∈ locImg Ω x L := by
      rw [hL.2.2]
      exact ⟨y, hy, rfl⟩
    have h2 : D.hom i (r' * y * r'⁻¹) ∈ locImg Ω x (conjSub w' L) := by
      have := locImg_conjSub_layer (Ω := Ω) (x := x) L ⟨w', hwx⟩
      rw [this]
      refine ⟨D.hom i y, h1, ?_⟩
      simp only [map_mul, map_inv, hr]
      rfl
    rwa [hN, hL.2.2] at h2
  obtain ⟨y', hy', hy'e⟩ := hmem
  refine ⟨y', hy', y'⁻¹ * (r' * y * r'⁻¹), D.ker_le_center i ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hy'e, inv_mul_cancel]

theorem corr_modelAdj (hMFZ : FundNoncentral p) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x})
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hA1 : ¬ (D.tag i = .PSL ∧ D.rank i = 2)) {L L' : Subgroup G}
    {R R' : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hL : Corr Ω x D i L R) (hL' : Corr Ω x D i L' R') {w w' : G}
    (hw : IsClassicalMember p f L w) (hw' : IsClassicalMember p f L' w') (hne : L ≠ L')
    (hnc : ¬ Commutes L L') (hc : Commute w w') (hN : conjSub w' L = L) :
    ModelAdj (Subgroup.center (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K) R R' := by
  obtain ⟨r, r', hr, hr', hcen, hψr, hψr'⟩ := corr_modelInvComm hMFZ hA1 hL hL' hw hw' hc
  refine ⟨fun h => hne (corr_unique_right hΩ hP1 hL (h ▸ hL')), ?_, r, r', hr, hr', hcen, ?_⟩
  · intro h
    exact hnc ((corr_commutes hΩ hP1 hperf hL hL').mpr h)
  · exact corr_normalizes hperf hL (le_centralizingLayer hL'.1 hw'.mem) hψr' hN

end Involutions

end CFSG.ClassicalInvolution.RouteD.NonClassical

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

theorem false_of_three_pairs (hD8 : D8NoThreeAdjPairs p .POmegaPlus 8 f) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {X : Type} [Group X] {t : StatedLieTag} {n e : ℕ} (ht : t = .POmegaPlus)
    (hn : n = 8) (he : e = f) (φ : (modelUniv t n p e Fact.out).K →* X)
    (hker : φ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K)
    (R : Fin 3 → Fin 2 → Subgroup (modelUniv t n p e Fact.out).K)
    (hfund : ∀ i j, R i j ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hadj : ∀ i, ModelAdj (Subgroup.center (modelUniv t n p e Fact.out).K) (R i 0) (R i 1))
    (hstd : ∀ i, ∃ W, LinearBlockStandardPair (GaloisField p f) W ((R i 0).map φ)
      ((R i 1).map φ))
    (hcomm : ∀ i i', i ≠ i' → ∀ j j', Commutes (R i j) (R i' j')) : False := by
  subst ht hn he
  have hF := orthFacts_plus (m := 8) hp2 (by norm_num) hq
  refine hD8 R hfund (fun i => ⟨hadj i, ?_⟩) hcomm
  exact hF.lift φ hker _ (hfund i 0) _ (hfund i 1) (hstd i)

theorem false_of_six (hD8 : D8NoThreeAdjPairs p .POmegaPlus 8 f) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {X : Type} [Group X] {t : StatedLieTag} {n e : ℕ} (ht : t = .POmegaPlus)
    (hn : n = 8) (he : e = f) (φ : (modelUniv t n p e Fact.out).K →* X)
    (hker : φ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K)
    {Ra Rb Rc Rd Re Rf : Subgroup (modelUniv t n p e Fact.out).K}
    (hfa : Ra ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hfb : Rb ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hfc : Rc ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hfd : Rd ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hfe : Re ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hff : Rf ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hab : ModelAdj (Subgroup.center (modelUniv t n p e Fact.out).K) Ra Rb)
    (hcd : ModelAdj (Subgroup.center (modelUniv t n p e Fact.out).K) Rc Rd)
    (hef : ModelAdj (Subgroup.center (modelUniv t n p e Fact.out).K) Re Rf)
    (sab : ∃ W, LinearBlockStandardPair (GaloisField p f) W (Ra.map φ) (Rb.map φ))
    (scd : ∃ W, LinearBlockStandardPair (GaloisField p f) W (Rc.map φ) (Rd.map φ))
    (sef : ∃ W, LinearBlockStandardPair (GaloisField p f) W (Re.map φ) (Rf.map φ))
    (hac : Commutes Ra Rc) (had : Commutes Ra Rd) (hbc : Commutes Rb Rc) (hbd : Commutes Rb Rd)
    (hae : Commutes Ra Re) (haf : Commutes Ra Rf) (hbe : Commutes Rb Re) (hbf : Commutes Rb Rf)
    (hce : Commutes Rc Re) (hcf : Commutes Rc Rf) (hde : Commutes Rd Re) (hdf : Commutes Rd Rf) :
    False := by
  refine false_of_three_pairs hD8 hp2 hq ht hn he φ hker ![![Ra, Rb], ![Rc, Rd], ![Re, Rf]]
    ?_ ?_ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> assumption
  · intro i
    fin_cases i
    · exact hab
    · exact hcd
    · exact hef
  · intro i
    fin_cases i
    · exact sab
    · exact scd
    · exact sef
  · intro i i' hii' j j'
    fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;>
      first
      | exact absurd rfl hii'
      | assumption
      | exact commutes_symm ‹_›

end CFSG.ClassicalInvolution.RouteD.TypeE8
