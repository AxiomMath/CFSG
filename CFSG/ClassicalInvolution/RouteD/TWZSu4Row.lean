module

public import CFSG.ClassicalInvolution.RouteD.TWZSu4V
public import CFSG.ClassicalInvolution.RouteD.TWZLinkSu4
public import CFSG.ClassicalInvolution.RouteD.TWSReduce
public import CFSG.ClassicalInvolution.RouteD.TWYSp2
public import CFSG.ClassicalInvolution.RouteD.TWZSmall
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

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Visible

variable {p f : ℕ} [Fact p.Prime]


theorem exists_twin_visible_psu4 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hmod : (p ^ f) % 4 = 1) {K : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) (hrow : TwinRow .PSU 4)
    (hshape : LocalShapeT p f 2 .PSU 4 (𝒞 K) z) {T : Subgroup G}
    (hT : IsTwinAt (𝒞 K) K T z) (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) :
    ∃ J J₂ : Subgroup G, J ∈ centralizingMembers (𝒞 K) {e.u} ∧
      J₂ ∈ centralizingMembers (𝒞 K) {e.u} ∧ Commutes J₂ J ∧ J₂ ≠ J ∧
      ∀ N ∈ centralizingMembers (𝒞 K) {e.u}, Commutes N J → N = J₂ := by
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, -, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  have hJKc : Commutes J K := (hT.comm_K J hJ hJK).symm
  have hJTc : Commutes J T := (hT.comm_T J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  have hJ₂u : A.J₂ ∈ centralizingMembers (𝒞 K) {e.u} :=
    e.mem_centralizingMembers_u A.hJ₂t.1 (hT.comm_K A.J₂ A.hJ₂z A.hJ₂K).symm
      (hT.comm_T A.J₂ A.hJ₂z A.hJ₂T).symm
  refine ⟨J, A.J₂, hJu, hJ₂u, A.hJ₂iso J A.hJt A.hJ₂J.symm, A.hJ₂J, ?_⟩
  intro N hN hNJ
  by_contra hne
  have hMt : N ∈ centralizingMembers (𝒞 K) {t} :=
    ⟨hN.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hNJ y hy t hJt.mem)⟩
  have hNJne : N ≠ J := fun h => hncs J hJ.1 (by rw [h] at hNJ; exact hNJ)
  obtain ⟨RM, hRM, hMR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
    A.hJiso A.hJ₂iso hMt hNJne hne
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts A e
  have hcommM : ∀ s ∈ RM, (ã * ã') * s = s * (ã * ã') := by
    have h1 : locImg (𝒞 K) t N ≤ Subgroup.centralizer ({locMk (𝒞 K) t ⟨e.u, huY⟩} : Set _) :=
      (le_centralizer_iff_locImg S.inClass A.hP1 hMt ⟨e.u, huY⟩).mp hN.2
    have h2 : RM ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv .PSU 4 p f Fact.out).K) :=
      (le_centralizer_iff_map A.d.ψ A.d.ker_le (A.rf.perf RM hRM) (ã * ã')).mpr (by
        rw [hψu, ← hMR]
        exact h1)
    intro s hs
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hs)).symm
  exact twinMFNotCentralizing_psu4 S.odd S.five hmod A.hdat.toOn hãR hã'R hsq hsq' hRM hcommM

end Visible

section NoCentral

variable {p f : ℕ} [Fact p.Prime]


theorem twinYNoCentralOn_psu4 (hmod : (p ^ f) % 4 = 1) :
    TwinYNoCentralOn p f fun t n => t = .PSU ∧ n = 4 := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e M hM
  obtain ⟨rfl, rfl⟩ := hP
  by_contra hno
  push Not at hno
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, -, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  have hMJ : Commutes M J := hno J hJ hJK hJT
  have hMJ₂ : Commutes M A.J₂ := hno A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
  have hMt : M ∈ centralizingMembers (𝒞 K) {t} :=
    ⟨hM.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hMJ y hy t hJt.mem)⟩
  have hMJne : M ≠ J := fun h => hncs J hJ.1 (by rw [h] at hMJ; exact hMJ)
  have hMJ₂ne : M ≠ A.J₂ := fun h => hncs A.J₂ A.hJ₂t.1 (by rw [h] at hMJ₂; exact hMJ₂)
  obtain ⟨RM, hRM, hMR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
    A.hJiso A.hJ₂iso hMt hMJne hMJ₂ne
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts A e
  have hcommM : ∀ s ∈ RM, (ã * ã') * s = s * (ã * ã') := by
    have h1 : locImg (𝒞 K) t M ≤ Subgroup.centralizer ({locMk (𝒞 K) t ⟨e.u, huY⟩} : Set _) :=
      (le_centralizer_iff_locImg S.inClass A.hP1 hMt ⟨e.u, huY⟩).mp hM.2
    have h2 : RM ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv .PSU 4 p f Fact.out).K) :=
      (le_centralizer_iff_map A.d.ψ A.d.ker_le (A.rf.perf RM hRM) (ã * ã')).mpr (by
        rw [hψu, ← hMR]
        exact h1)
    intro s hs
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hs)).symm
  exact twinMFNotCentralizing_psu4 S.odd S.five hmod A.hdat.toOn hãR hã'R hsq hsq' hRM hcommM

theorem twinMFCentralizing_psu4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hmod : (p ^ f) % 4 = 1) :
    TwinMFCentralizing p f .PSU 4 :=
  twinMFCentralizing_of_on fun _ _ _ _ hd _ ha _ ha' hsq hsq' _ hS hc =>
    (twinMFNotCentralizing_psu4 hp2 hq hmod hd ha ha' hsq hsq' hS hc).elim

theorem twinYVisibleOn_psu4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hmod : (p ^ f) % 4 = 1) :
    TwinYVisibleOn p f fun t n => t = .PSU ∧ n = 4 :=
  twinYVisibleOn_of_model fun t n _ hP => by
    obtain ⟨rfl, rfl⟩ := hP
    exact twinMFCentralizing_psu4 hp2 hq hmod

end NoCentral

section Rank

variable (p f : ℕ) [Fact p.Prime]


@[expose] def TwinYSu4NoOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSU 4 (𝒞 K) z →
      ∀ T : Subgroup G, IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z →
        ∀ e : TwinElt K T z, LocalOddCentral (𝒞 K) {e.u} →
          ∀ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1 →
            ∀ i : Fin D.card, (D.tag i = .POmegaOdd ∧ D.rank i = 3) → False

variable {p f}

theorem twinYRankOn_psu4_of_noOdd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hmod : (p ^ f) % 4 = 1)
    (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hNO : TwinYSu4NoOdd p f) :
    TwinYRankOn p f fun t n => t = .PSU ∧ n = 4 := by
  have hPL : ∀ t n, (t = .PSU ∧ n = 4) → ListedTwin t n := fun t n h =>
    Or.inr (Or.inr (Or.inl h))
  have hG : TwinYGenTOn p f fun t n => t = .PSU ∧ n = 4 :=
    twinYGenTOn_of_model fun t n _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact twinMFGeneration_psu4 hp2 hq
  have hV := twinYVisibleOn_psu4 hp2 hq hmod
  have hY1 := TWS.twinYP1On_of_visible_row hPL hΩall hAE hcls hP4 hH hG hV
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e D hcard i horth'
  obtain ⟨rfl, rfl⟩ := hP
  have hP1 := hY1 G hnab K z S .PSU 4 hrow ⟨rfl, rfl⟩ hshape T hT clsT e
  have hMF : TwinMFGeneration p f .PSU 4 := twinMFGeneration_psu4 S.odd S.five
  obtain ⟨d, ε, -, horth⟩ := horth'
  have hDi : D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    rcases horth with ⟨-, ht, -⟩ | ⟨-, -, ht, -⟩ | ⟨-, -, ht, -⟩ | ⟨-, -, ht, -⟩ |
      ⟨-, -, -, ht, -⟩ | ⟨-, -, -, ht, -⟩ <;> rw [ht] <;> exact ⟨by decide, by decide⟩
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hD : ∀ j, D.tag j ≠ .G2 ∧ D.tag j ≠ .trialityD4 := fun j => by
    rw [hsub.elim j i]
    exact hDi
  obtain ⟨J, J₂, hJ, hJ₂, hc, hne, hone⟩ :=
    exists_twin_visible_psu4 hnab hmod S hrow hshape hT clsT e
  obtain ⟨R₀, hR₀, hN⟩ := TWY.exists_layerOne hp2 hq S.inClass S.exact hP1 D hcard i hD hJ hJ₂ hc
    hne hone
  have hexp : D.exp i = f := (D.exp_eq i).resolve_right fun h => (hD i).2 h.1
  have hmod' : twinYModel (p ^ f) .PSU 4 = (.POmegaMinus, 4) := by simp [twinYModel, hmod]
  show D.tag i = (twinYModel (p ^ f) .PSU 4).1 ∧ D.rank i = (twinYModel (p ^ f) .PSU 4).2
  rw [hmod']
  show D.tag i = .POmegaMinus ∧ D.rank i = 4
  rcases horth with ⟨-, ht, hr⟩ | ⟨-, -, ht, hr⟩ | ⟨-, -, ht, hr⟩ | ⟨-, -, ht, -⟩ |
    ⟨-, -, -, ht, -⟩ | ⟨-, -, -, ht, -⟩
  · exact (false_of_small_component hnab S hrow hshape hT clsT e hMF hP1 D hcard i
      (Or.inl ⟨ht, hr⟩)).elim
  · exact (false_of_small_component hnab S hrow hshape hT clsT e hMF hP1 D hcard i
      (Or.inr (Or.inl ⟨ht, hr⟩))).elim
  · exact (false_of_small_component hnab S hrow hshape hT clsT e hMF hP1 D hcard i
      (Or.inr (Or.inr ⟨ht, hr⟩))).elim
  · exact (hNO G hnab K z S hshape T hT clsT e hP1 D hcard i
      ⟨ht, TWY.layerOne_odd' hp2 hq ht hexp (D.admissible i) hR₀ hN⟩).elim
  · exact (TWY.layerOne_plus' hp2 hq ht hexp (D.admissible i) hR₀ hN).elim
  · exact ⟨ht, TWY.layerOne_minus' hp2 hq ht hexp (D.admissible i) hR₀ hN⟩

theorem twinSU4Linked_of_noOdd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hmod : (p ^ f) % 4 = 1)
    (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hNO : TwinYSu4NoOdd p f) :
    TwinSU4Linked p f :=
  TWS.twinSU4Linked_of_residuals hp2 hq hΩall hAE hcls hP4 hH (twinYVisibleOn_psu4 hp2 hq hmod)
    (twinYNoCentralOn_psu4 hmod)
    (twinYRankOn_psu4_of_noOdd hp2 hq hmod hΩall hAE hcls hP4 hH hNO)
    (twinYLinkedSU4_of_mod_one p f hmod)

end Rank

end CFSG.ClassicalInvolution.RouteD.TWZ
