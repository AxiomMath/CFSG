module

public import CFSG.ClassicalInvolution.RouteD.TwinYP1Main
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Lift
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Rows

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

section Statement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYVisibleOn (P : StatedLieTag → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → P tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ (J : Subgroup G) (t : G), J ∈ centralizingMembers (𝒞 K) {z} → J ≠ K → J ≠ T →
        IsClassicalMember p f J t →
        ∀ M ∈ centralizingMembers (𝒞 K) {e.u}, M ≤ Subgroup.centralizer ({t} : Set G) → M ≠ J →
          ∃ g ∈ Subgroup.centralizer ({e.u} : Set G), conjSub g J = M

end Statement

section Comm

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem comm_mod_of_not_inCommonComponent (hp2 : p ≠ 2) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {x : G} (hxne : ¬ ({x} : Set G) ⊆ Subgroup.center G)
    {L K : Subgroup G} (hL : L ∈ centMembers Ω x) (hK : K ∈ centMembers Ω x)
    (hno : ¬ InCommonComponent x L K) :
    ∀ a ∈ L, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (centLayer Ω x) := by
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hxne
  have := memberJoin_normal (a := x) hΩ.conjInvariant
  obtain ⟨i, hi⟩ := D.exists_le _ (⟨L, hL, rfl⟩ : modOdd x L ∈ memberImages Ω x)
  obtain ⟨j, hj⟩ := D.exists_le _ (⟨K, hK, rfl⟩ : modOdd x K ∈ memberImages Ω x)
  have hij : i ≠ j := by
    rintro rfl
    exact hno ⟨D.Q i, (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i), hi, hj⟩
  intro a ha b hb
  have haY : a ∈ centLayer Ω x := le_centLayer hL ha
  have hbY : b ∈ centLayer Ω x := le_centLayer hK hb
  have hcomm : layerToOddQuot Ω x ⟨a, haY⟩ * layerToOddQuot Ω x ⟨b, hbY⟩ =
      layerToOddQuot Ω x ⟨b, hbY⟩ * layerToOddQuot Ω x ⟨a, haY⟩ :=
    D.commute i j hij _ (hi ⟨⟨a, hL.2 ha⟩, ha, rfl⟩) _ (hj ⟨⟨b, hK.2 hb⟩, hb, rfl⟩)
  have hker : (⟨a, haY⟩ * ⟨b, hbY⟩ * ⟨a, haY⟩⁻¹ * ⟨b, hbY⟩⁻¹ : ↥(centLayer Ω x)) ∈
      (layerToOddQuot Ω x).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rw [ker_layerToOddQuot hΩ.conjInvariant] at hker
  exact ⟨_, hker, rfl⟩

omit [Finite G] in
theorem inCommonComponent_symm {x : G} {K L : Subgroup G} (h : InCommonComponent x K L) :
    InCommonComponent x L K := by
  obtain ⟨Q, hQ, h1, h2⟩ := h
  exact ⟨Q, hQ, h2, h1⟩

end Comm

section Cover

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem cover_of_visible (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩm : HypOmegaMod p f Ω)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hIH : LocalLieSystems p f Ω) {u : G}
    (hunc : ¬ ({u} : Set G) ⊆ Subgroup.center G) {B : Subgroup G} (huB : u ∈ B)
    {J : Subgroup G} {t : G} (hJ : J ∈ centMembers Ω u) (hJt : IsUniqueInvolution J t)
    (hV : ∀ M ∈ centMembers Ω u, M ≤ Subgroup.centralizer ({t} : Set G) → M ≠ J →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G), conjSub g J = M) :
    ∀ M ∈ centMembers Ω u, ∃ g : G, u ∈ conjSub g B ∧ InCommonComponent u M (conjSub g J) := by
  intro M hM
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hunc (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact Subgroup.one_mem _)
  have hself : ∀ L ∈ centMembers Ω u, InCommonComponent u L L := fun L hL => by
    obtain ⟨D⟩ := lieDecomposition_memberImages hp
      CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hunc
    have := memberJoin_normal (a := u) hΩ.conjInvariant
    obtain ⟨i, hi⟩ := D.exists_le _ (⟨L, hL, rfl⟩ : modOdd u L ∈ memberImages Ω u)
    exact ⟨D.Q i, (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i), hi, hi⟩
  by_cases hcc : InCommonComponent u M J
  · exact ⟨1, by rw [conjSub_one]; exact huB, by rw [conjSub_one]; exact hcc⟩
  have hcomm := comm_mod_of_not_inCommonComponent hp hΩ hIH hunc hJ hM
    (fun h => hcc (inCommonComponent_symm h))
  have hJY : J ≤ centLayer Ω u := le_centLayer hJ
  have hMY : M ≤ centLayer Ω u := le_centLayer hM
  obtain ⟨o, hoN, hM', hJc, -⟩ := exists_conj_commutes_of_comm_mod hp hq (hΩm.toExact hex) hJ.1
    hJ.1 hM.1 hJt hJt (odd_card_oddCoreIn _) (fun x hx n hn => conj_mem_oddCoreIn (hMY hx) hn)
    (fun n hn => conj_mem_oddCoreIn (hJY hJt.mem) hn) (fun x hx => hcomm t hJt.mem x hx)
  have hoY : o ∈ centLayer Ω u := oddCoreIn_le _ hoN
  have hoC : o ∈ Subgroup.centralizer ({u} : Set G) := centLayer_le_centralizer Ω u hoY
  have hM'u : conjSub o M ≤ Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    have h1 : o⁻¹ * y * o ∈ M := mem_conjSub_iff.mp hy
    have h2 := hM.2 h1
    have e : y = o * (o⁻¹ * y * o) * o⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hoC h2) (inv_mem hoC)
  have hM'mem : conjSub o M ∈ centMembers Ω u := ⟨hM', hM'u⟩
  have hoO : o ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G)) :=
    le_oddCoreIn_of_normalizes ((oddCoreIn_le _).trans (centralizingLayer_le_centralizer Ω {u}))
      (fun n hn => mem_normalizer_oddCoreIn_centralizingLayer hΩ.conjInvariant hn)
      (odd_card_oddCoreIn _) hoN
  have himg : modOdd u (conjSub o M) = modOdd u M := modOdd_conjSub_of_mem_oddCoreIn hoO
  have hMM' : InCommonComponent u M (conjSub o M) := by
    obtain ⟨Q, hQ, h1, h2⟩ := hself M hM
    exact ⟨Q, hQ, h1, by rw [himg]; exact h2⟩
  have hcJ : Commutes J (conjSub o M) := hJc.resolve_left (fun h => hcc (h ▸ hMM'))
  have hMt : conjSub o M ≤ Subgroup.centralizer ({t} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcJ t hJt.mem y hy).symm
  have hMJ : conjSub o M ≠ J := fun h => hcc (h ▸ hMM')
  obtain ⟨g, hg, hgJ⟩ := hV _ hM'mem hMt hMJ
  refine ⟨g, ?_, by rw [hgJ]; exact hMM'⟩
  rw [mem_conjSub_iff]
  have hgu : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have e : g⁻¹ * u * g = u := by
    calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
      _ = g⁻¹ * (g * u) := by rw [hgu]
      _ = u := by group
  rw [e]
  exact huB

end Cover

section P1

variable {p f : ℕ} [Fact p.Prime]

theorem twinYP1On_of_visible {P : StatedLieTag → ℕ → Prop} (hΩall : HypOmegaModAll p f)
    (hAall : AEmptyAll p f) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hGenT : TwinYGenTOn p f P) (hVis : TwinYVisibleOn p f P) : TwinYP1On p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := hAall G hnab S.odd S.five K z S.cls S.below
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

theorem twinYP1_of_visible (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenT p f)
    (hVis : TwinYVisibleOn p f fun _ _ => True) : TwinYP1 p f :=
  (twinYP1On_of_visible hΩall hAall hP4 hH hGenT.on hVis).of_true

end P1

end CFSG.ClassicalInvolution.RouteD.TwinY
