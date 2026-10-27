module

public import CFSG.ClassicalInvolution.RouteD.TWSSp4V
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSu4
public import CFSG.ClassicalInvolution.RouteD.TwinYR2XO
public import CFSG.ClassicalInvolution.Asc77.WP3SCRP1Base
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.WeakCT
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

section Linked

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYLinkedSp2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSp 2 (𝒞 K) z →
      ∀ (Λ : SpLayer p f 2 (𝒞 K) z) (K₂ : Subgroup G),
        K₂ ∈ centralizingMembers (𝒞 K) {z} → locImg (𝒞 K) z K₂ ≤ (Λ.D.hom Λ.i₁).range →
        ∀ w : G, IsClassicalMember p f K₂ w →
          (∃ (T : Subgroup G) (e : TwinElt K T z), IsTwinAt (𝒞 K) K T z ∧
            IsClassicalMember p f T z ∧ LocalOddCentral (𝒞 K) {e.u} ∧
            LocalShapeT p f 0 (twinYModel (p ^ f) .PSp 2).1 (twinYModel (p ^ f) .PSp 2).2
              (𝒞 K) e.u) → LinkedAtProduct (𝒞 K) K z w

@[expose] def TwinYLinkedSU4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSU 4 (𝒞 K) z →
      ∀ (Λ : SuLayer p f 2 (𝒞 K) z) (K₂ : Subgroup G),
        K₂ ∈ centralizingMembers (𝒞 K) {z} → locImg (𝒞 K) z K₂ ≤ (Λ.D.hom Λ.i₁).range →
        ∀ w : G, IsClassicalMember p f K₂ w →
          (∃ (T : Subgroup G) (e : TwinElt K T z), IsTwinAt (𝒞 K) K T z ∧
            IsClassicalMember p f T z ∧ LocalOddCentral (𝒞 K) {e.u} ∧
            LocalShapeT p f 0 (twinYModel (p ^ f) .PSU 4).1 (twinYModel (p ^ f) .PSU 4).2
              (𝒞 K) e.u) → LinkedAtProduct (𝒞 K) K z w

end Linked

section Rows

variable {p f : ℕ} [Fact p.Prime] {P : LTag → ℕ → Prop}

theorem twinYP1On_of_visible_row (hPL : ∀ t n, P t n → ListedTwin t n)
    (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenTOn p f P)
    (hVis : TwinYVisibleOn p f P) : TwinYP1On p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M :=
    aEmpty_of_twinExact hAE hcls hnab S hrow (hPL tY nY hP) hshape
  have h7 : Thm7TypedBelow p f (Nat.card G) := thm7TypedBelow_of hP4 S.below
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, hJ't, hJJ', hJ'u⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hJKc : Commutes J K := (hKiso J hJ hJK).symm
  have hJTc : Commutes J T := (hTiso J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  obtain ⟨hu1, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have fd : TwinFrameData (𝒞 K) K T z e.u J t :=
    twinFrameData_of S hΩ e hT.mem.1 hT.ne hKT clsT hJ.1 hJ.2 hJt htz hJKc hJTc
  have hbal := rankThreeBalance_of hH S hΩ hA h7 fd
  have hframe := frameSide_of S hcen hΩ hD4 rf hshape e fd hT.mem hT.ne.symm hKiso hTiso clsT hJ
    hJK hJT hJt (hGenT G hnab K z S tY nY hrow hP hshape T hT clsT e J t hJ hJK hJT hJt)
  have hgen := rankTwoSpan_eq_top_of S hframe
  have huB : e.u ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hcov := cover_of_visible S.odd S.five hΩ S.inClass S.exact S.ih hunc huB hJu
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt)
    (hVis G hnab K z S tY nY hrow hP hshape T hT clsT e J t hJ hJK hJT hJt)
  exact (stage2_of_balanced_gen hnab S.odd S.five S.inClass S.ih hbal hJ.1 hJt htB
    (le_centralizer_frame e hJ.2 hJt hJKc hJTc) hgen).2 e.u hu1 hcov

theorem twinYTransitiveOn_of_p1_row (hPL : ∀ t n, P t n → ListedTwin t n)
    (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f)
    (hP1 : TwinYP1On p f P) (hNC : TwinYNoCentralOn p f P) : TwinYTransitiveOn p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e K₁ hK₁ L hL
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M :=
    aEmpty_of_twinExact hAE hcls hnab S hrow (hPL tY nY hP) hshape
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
    obtain ⟨y, hy, hyN⟩ :=
      twinYXOrbit p f G hnab K z S tY nY hrow hshape T hT clsT e J hJ hJK hJT N hN hNK hNT
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

theorem exists_orthLie_twinOn_row (hPL : ∀ t n, P t n → ListedTwin t n)
    (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f)
    (hP4 : Ih8G2D4 p f) (hTrans : TwinYTransitiveOn p f P) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K T : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) {tY : LTag} {nY : ℕ} (hrow : TwinRow tY nY)
    (hP : P tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) :
    ∃ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1 ∧
      ∃ i : Fin D.card, ∃ (d : ℕ) (ε : Bool), 5 ≤ d ∧ IsOrthTag d ε (D.tag i) (D.rank i) := by
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M :=
    aEmpty_of_twinExact hAE hcls hnab S hrow (hPL tY nY hP) hshape
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

theorem twinYTypeOn_of_inputs_row (hPL : ∀ t n, P t n → ListedTwin t n)
    (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f)
    (hP4 : Ih8G2D4 p f) (hTrans : TwinYTransitiveOn p f P) (hRank : TwinYRankOn p f P) :
    TwinYTypeOn p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e _
  obtain ⟨D, hcard, i, horth⟩ :=
    exists_orthLie_twinOn_row hPL hΩall hAE hcls hP4 hTrans hnab S hrow hP hshape hT clsT e
  obtain ⟨hd, hr⟩ := hRank G hnab K z S tY nY hrow hP hshape T hT clsT e D hcard i horth
  have h := NonClassical.localShapeT_zero_of_card_eq_one D hcard i
  rwa [hd, hr] at h

theorem twinYTypeOn_of_local_row (hPL : ∀ t n, P t n → ListedTwin t n)
    (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenTOn p f P)
    (hVis : TwinYVisibleOn p f P) (hNC : TwinYNoCentralOn p f P) (hRank : TwinYRankOn p f P) :
    TwinYTypeOn p f P :=
  twinYTypeOn_of_inputs_row hPL hΩall hAE hcls hP4
    (twinYTransitiveOn_of_p1_row hPL hΩall hAE hcls
      (twinYP1On_of_visible_row hPL hΩall hAE hcls hP4 hH hGenT hVis) hNC) hRank

end Rows

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem exists_twinData {tY : LTag} {nY : ℕ} (hcls : TwinInvolution p f) (hrow : TwinRow tY nY)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) :
    ∃ T : Subgroup G, IsTwinAt (𝒞 K) K T z ∧ IsClassicalMember p f T z ∧
      Nonempty (TwinElt K T z) := by
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N := fun N hN hNK =>
    (S.cp_at_member hcen (CoreAssembly.mem_conjClass_self K) S.cls hN).resolve_right hNK
  obtain ⟨T, hT, hTK, hTiso⟩ : ∃ T ∈ centralizingMembers (𝒞 K) {z}, T ≠ K ∧
      ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N := by
    obtain ⟨D, hcard, i₁, htag, hrank, hrest⟩ := hshape
    have hbig : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2) := fun ⟨h1, h2⟩ =>
      hnA1 ⟨htag.symm.trans h1, hrank.symm.trans h2⟩
    exact exists_twin_of_layer (Gaps.fundNoncentral p) S.inClass S.exact S.p1 D i₁
      (by omega) hrest hbig (CoreAssembly.mem_conjClass_self K) S.cls
  have hTwin : IsTwinAt (𝒞 K) K T z := ⟨hT, hTK, hTiso, hKiso⟩
  have clsT : IsClassicalMember p f T z := hcls G hnab K z S tY nY hrow hshape T hTwin
  obtain ⟨e⟩ := exists_twinElt S.cls clsT (S.exact K (CoreAssembly.mem_conjClass_self K))
    (S.exact T hT.1) (odd_natCard_galoisField S.odd S.five)
  exact ⟨T, hTwin, clsT, ⟨e⟩⟩

theorem twinYNoCentralOn_psp2 :
    TwinYNoCentralOn p f fun t n => t = .PSp ∧ n = 2 := by
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
    have h2 : RM ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv .PSp 2 p f Fact.out).K) :=
      (le_centralizer_iff_map A.d.ψ A.d.ker_le (A.rf.perf RM hRM) (ã * ã')).mpr (by
        rw [hψu, ← hMR]
        exact h1)
    intro s hs
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hs)).symm
  exact twinMFNotCentralizing_psp2 S.odd S.five A.hdat.toOn hãR hã'R hsq hsq' hRM hcommM

theorem twinSp2Linked_of_residuals (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hRank : TwinYRankOn p f fun t n => t = .PSp ∧ n = 2) (hL : TwinYLinkedSp2 p f) :
    TwinSp2Linked p f := by
  have hPL : ∀ t n, (t = .PSp ∧ n = 2) → ListedTwin t n := fun t n h => Or.inl h
  have hG : TwinYGenTOn p f fun t n => t = .PSp ∧ n = 2 :=
    twinYGenTOn_of_model fun t n _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact twinMFGeneration_psp2 hp2 (by omega)
  have hV : TwinYVisibleOn p f fun t n => t = .PSp ∧ n = 2 :=
    twinYVisibleOn_of_model fun t n _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact twinMFCentralizing_psp2 hp2 hq
  have hY1 := twinYP1On_of_visible_row hPL hΩall hAE hcls hP4 hH hG hV
  have hY2 := twinYTypeOn_of_local_row hPL hΩall hAE hcls hP4 hH hG hV twinYNoCentralOn_psp2 hRank
  intro G _ _ _ hnab K z S hshape Λ K₂ hK₂ hK₂Λ w hw
  have hrow : TwinRow .PSp 2 := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  obtain ⟨T, hTwin, clsT, ⟨e⟩⟩ := exists_twinData hcls hrow hnab S hshape
  have hP1 := hY1 G hnab K z S .PSp 2 hrow ⟨rfl, rfl⟩ hshape T hTwin clsT e
  have hty := hY2 G hnab K z S .PSp 2 hrow ⟨rfl, rfl⟩ hshape T hTwin clsT e hP1
  exact hL G hnab K z S hshape Λ K₂ hK₂ hK₂Λ w hw ⟨T, e, hTwin, clsT, hP1, hty⟩

theorem twinSU4Linked_of_residuals (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hV : TwinYVisibleOn p f fun t n => t = .PSU ∧ n = 4)
    (hNC : TwinYNoCentralOn p f fun t n => t = .PSU ∧ n = 4)
    (hRank : TwinYRankOn p f fun t n => t = .PSU ∧ n = 4) (hL : TwinYLinkedSU4 p f) :
    TwinSU4Linked p f := by
  have hPL : ∀ t n, (t = .PSU ∧ n = 4) → ListedTwin t n := fun t n h => Or.inr (Or.inr (Or.inl h))
  have hG : TwinYGenTOn p f fun t n => t = .PSU ∧ n = 4 :=
    twinYGenTOn_of_model fun t n _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact twinMFGeneration_psu4 hp2 hq
  have hY1 := twinYP1On_of_visible_row hPL hΩall hAE hcls hP4 hH hG hV
  have hY2 := twinYTypeOn_of_local_row hPL hΩall hAE hcls hP4 hH hG hV hNC hRank
  intro G _ _ _ hnab K z S hshape Λ K₂ hK₂ hK₂Λ w hw
  have hrow : TwinRow .PSU 4 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
  obtain ⟨T, hTwin, clsT, ⟨e⟩⟩ := exists_twinData hcls hrow hnab S hshape
  have hP1 := hY1 G hnab K z S .PSU 4 hrow ⟨rfl, rfl⟩ hshape T hTwin clsT e
  have hty := hY2 G hnab K z S .PSU 4 hrow ⟨rfl, rfl⟩ hshape T hTwin clsT e hP1
  exact hL G hnab K z S hshape Λ K₂ hK₂ hK₂Λ w hw ⟨T, e, hTwin, clsT, hP1, hty⟩

end Main

end CFSG.ClassicalInvolution.RouteD.TWS
