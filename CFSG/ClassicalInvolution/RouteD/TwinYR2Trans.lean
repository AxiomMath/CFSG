module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Cover
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Rows

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

section Statement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYXOrbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ J ∈ centralizingMembers (𝒞 K) {z}, J ≠ K → J ≠ T →
        ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
          ∃ y ∈ locLayer (𝒞 K) e.u, conjSub y J = N

@[expose] def TwinYNoCentralOn (P : StatedLieTag → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → P tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ M ∈ centralizingMembers (𝒞 K) {e.u},
        ∃ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K ∧ N ≠ T ∧ ¬ Commutes M N

end Statement

section Trans

variable {p f : ℕ} [Fact p.Prime] {P : StatedLieTag → ℕ → Prop}

theorem twinYTransitiveOn_of_p1 (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP1 : TwinYP1On p f P) (hXO : TwinYXOrbit p f) (hNC : TwinYNoCentralOn p f P) :
    TwinYTransitiveOn p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e K₁ hK₁ L hL
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := hAall G hnab S.odd S.five K z S.cls S.below
  have hP1u : LocalOddCentral (𝒞 K) {e.u} := hP1 G hnab K z S tY nY hrow hP hshape T hT clsT e
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, J', t, hJ, hJK, hJT, -, -, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hMemU : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (𝒞 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  have hJu := hMemU J hJ hJK hJT
  obtain ⟨-, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have hJΦ : locImg (𝒞 K) e.u J ∈ locFamily (𝒞 K) e.u := mem_locFamily_iff.mpr ⟨J, hJu, rfl⟩
  have key : ∀ M ∈ locFamily (𝒞 K) e.u,
      ∃ g : locQuot (𝒞 K) e.u, conjSub g (locImg (𝒞 K) e.u J) = M := by
    intro M hM
    by_contra hno
    push Not at hno
    obtain ⟨M₀, hM₀, rfl⟩ := mem_locFamily_iff.mp hM
    have hle := normalClosure_le_centralizer_of_not_conj S.odd S.five hΩ hA S.below hunc hJΦ hM hno
    obtain ⟨N, hN, hNK, hNT, hNc⟩ := hNC G hnab K z S tY nY hrow hP hshape T hT clsT e M₀ hM₀
    obtain ⟨y, hy, hyN⟩ := hXO G hnab K z S tY nY hrow hshape T hT clsT e J hJ hJK hJT N hN hNK hNT
    have hNu := hMemU N hN hNK hNT
    apply hNc
    refine commutes_of_commutes_locImg S.inClass hP1u hM₀ hNu ?_
    intro a ha b hb
    rw [← hyN, locImg_conjSub_layer J ⟨y, hy⟩] at hb
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hb
    have hbN : (MulAut.conj (locMk (𝒞 K) e.u ⟨y, hy⟩)).toMonoidHom j ∈
        Subgroup.normalClosure (locImg (𝒞 K) e.u J : Set (locQuot (𝒞 K) e.u)) :=
      (Subgroup.normalClosure_normal).conj_mem j (Subgroup.subset_normalClosure hj) _
    exact Subgroup.mem_centralizer_iff.mp (hle hbN) a ha
  obtain ⟨g₁, hg₁⟩ := key K₁ hK₁
  obtain ⟨g₂, hg₂⟩ := key L hL
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [← hg₁, ← conjSub_mul, inv_mul_cancel_right]
  exact hg₂

end Trans

section TypeOfInputs

variable {p f : ℕ} [Fact p.Prime] {P : StatedLieTag → ℕ → Prop}

theorem exists_orthLie_twinOn (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hTrans : TwinYTransitiveOn p f P) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K T : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) {tY : StatedLieTag} {nY : ℕ} (hrow : TwinRow tY nY)
    (hP : P tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) :
    ∃ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1 ∧
      ∃ i : Fin D.card, ∃ (d : ℕ) (ε : Bool), 5 ≤ d ∧ IsOrthTag d ε (D.tag i) (D.rank i) := by
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := hAall G hnab S.odd S.five K z S.cls S.below
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, hJ't, hJJ', hJ'u⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hJKc : Commutes J K := (hT.comm_K J hJ hJK).symm
  have hJTc : Commutes J T := (hT.comm_T J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  obtain ⟨-, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have htw := twin_locFamily S.inClass S.exact hJu hJ'u
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt)
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJ't) hJJ'
  exact exists_orthLie_of_trans S.odd S.five hΩ hA hP4 S.below hunc
    (hTrans G hnab K z S tY nY hrow hP hshape T hT clsT e) htw

theorem twinYTypeOn_of_inputs (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hTrans : TwinYTransitiveOn p f P) (hRank : TwinYRankOn p f P) :
    TwinYTypeOn p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e _
  obtain ⟨D, hcard, i, horth⟩ := exists_orthLie_twinOn hΩall hAall hP4 hTrans hnab S hrow hP hshape
    hT clsT e
  obtain ⟨hd, hr⟩ := hRank G hnab K z S tY nY hrow hP hshape T hT clsT e D hcard i horth
  have h := NonClassical.localShapeT_zero_of_card_eq_one D hcard i
  rwa [hd, hr] at h

theorem twinYTypeOn_of_local (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenTOn p f P)
    (hVis : TwinYVisibleOn p f P) (hXO : TwinYXOrbit p f) (hNC : TwinYNoCentralOn p f P)
    (hRank : TwinYRankOn p f P) : TwinYTypeOn p f P :=
  twinYTypeOn_of_inputs hΩall hAall hP4
    (twinYTransitiveOn_of_p1 hΩall hAall (twinYP1On_of_visible hΩall hAall hP4 hH hGenT hVis) hXO
      hNC) hRank

end TypeOfInputs

end CFSG.ClassicalInvolution.RouteD.TwinY
