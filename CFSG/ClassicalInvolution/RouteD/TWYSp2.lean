module

public import CFSG.ClassicalInvolution.RouteD.TWSReduce
public import CFSG.ClassicalInvolution.RouteD.TWYBridge
public import CFSG.ClassicalInvolution.RouteD.TWYLayerOne

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

section Visible

variable {p f : ℕ} [Fact p.Prime]

theorem exists_twin_visible_psp2 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hrow : TwinRow .PSp 2) (hshape : LocalShapeT p f 2 .PSp 2 (𝒞 K) z) {T : Subgroup G}
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
    have h2 : RM ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv .PSp 2 p f Fact.out).K) :=
      (le_centralizer_iff_map A.d.ψ A.d.ker_le (A.rf.perf RM hRM) (ã * ã')).mpr (by
        rw [hψu, ← hMR]
        exact h1)
    intro s hs
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hs)).symm
  exact twinMFNotCentralizing_psp2 S.odd S.five A.hdat.toOn hãR hã'R hsq hsq' hRM hcommM

end Visible

section Reduction

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYSp2Small : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSp 2 (𝒞 K) z →
      ∀ T : Subgroup G, IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z →
        ∀ e : TwinElt K T z, LocalOddCentral (𝒞 K) {e.u} →
          ∀ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1 →
            ∀ i : Fin D.card,
              ((D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
                (D.tag i = .PSU ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4)) →
              False

variable {p f}

theorem twinYRankOn_psp2_of_small (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hSmall : TwinYSp2Small p f) :
    TwinYRankOn p f fun t n => t = .PSp ∧ n = 2 := by
  have hPL : ∀ t n, (t = .PSp ∧ n = 2) → ListedTwin t n := fun t n h => Or.inl h
  have hG : TwinYGenTOn p f fun t n => t = .PSp ∧ n = 2 :=
    twinYGenTOn_of_model fun t n _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact twinMFGeneration_psp2 hp2 (by omega)
  have hV : TwinYVisibleOn p f fun t n => t = .PSp ∧ n = 2 :=
    twinYVisibleOn_of_model fun t n _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact twinMFCentralizing_psp2 hp2 hq
  have hY1 := TWS.twinYP1On_of_visible_row hPL hΩall hAE hcls hP4 hH hG hV
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e D hcard i horth'
  obtain ⟨rfl, rfl⟩ := hP
  have hP1 := hY1 G hnab K z S .PSp 2 hrow ⟨rfl, rfl⟩ hshape T hT clsT e
  have hS' := hSmall G hnab K z S hshape T hT clsT e hP1 D hcard i
  obtain ⟨d, ε, -, horth⟩ := horth'
  have hDi : D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    rcases horth with ⟨-, ht, -⟩ | ⟨-, -, ht, -⟩ | ⟨-, -, ht, -⟩ | ⟨-, -, ht, -⟩ |
      ⟨-, -, -, ht, -⟩ | ⟨-, -, -, ht, -⟩ <;> rw [ht] <;> exact ⟨by decide, by decide⟩
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hD : ∀ j, D.tag j ≠ .G2 ∧ D.tag j ≠ .trialityD4 := fun j => by
    rw [hsub.elim j i]
    exact hDi
  obtain ⟨J, J₂, hJ, hJ₂, hc, hne, hone⟩ := exists_twin_visible_psp2 hnab S hrow hshape hT clsT e
  obtain ⟨R₀, hR₀, hN⟩ := exists_layerOne hp2 hq S.inClass S.exact hP1 D hcard i hD hJ hJ₂ hc
    hne hone
  have hexp : D.exp i = f := (D.exp_eq i).resolve_right fun h => (hD i).2 h.1
  show D.tag i = .POmegaOdd ∧ D.rank i = 2 + 1
  rcases horth with ⟨-, ht, hr⟩ | ⟨-, -, ht, hr⟩ | ⟨-, -, ht, hr⟩ | ⟨-, -, ht, -⟩ |
    ⟨-, -, -, ht, -⟩ | ⟨-, -, -, ht, -⟩
  · exact (hS' (Or.inl ⟨ht, hr⟩)).elim
  · exact (hS' (Or.inr (Or.inl ⟨ht, hr⟩))).elim
  · exact (hS' (Or.inr (Or.inr (Or.inl ⟨ht, hr⟩)))).elim
  · exact ⟨ht, layerOne_odd' hp2 hq ht hexp (D.admissible i) hR₀ hN⟩
  · exact (layerOne_plus' hp2 hq ht hexp (D.admissible i) hR₀ hN).elim
  · exact (hS' (Or.inr (Or.inr (Or.inr ⟨ht, layerOne_minus' hp2 hq ht hexp (D.admissible i)
      hR₀ hN⟩)))).elim

end Reduction

end CFSG.ClassicalInvolution.RouteD.TWY
