module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameP1
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

section Quasisimple

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

omit [Fact p.Prime] [Finite G] in
theorem aux_commutator_of_commute (a b x y : G) (hax : a * x = x * a) (hay : a * y = y * a)
    (hbx : b * x = x * b) (hby : b * y = y * b) (hab : a * b = b * a) :
    (a * x) * (b * y) * (a * x)⁻¹ * (b * y)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have f1 : a * x * b * y = a * b * (x * y) :=
    calc a * x * b * y = a * (x * b) * y := by group
      _ = a * (b * x) * y := by rw [← hbx]
      _ = a * b * (x * y) := by group
  have f2 : b * y * a * x = a * b * (y * x) :=
    calc b * y * a * x = b * (y * a) * x := by group
      _ = b * (a * y) * x := by rw [← hay]
      _ = (b * a) * (y * x) := by group
      _ = a * b * (y * x) := by rw [← hab]
  have hAx : Commute (a * b) x := by
    show a * b * x = x * (a * b)
    calc a * b * x = a * (b * x) := by group
      _ = a * (x * b) := by rw [hbx]
      _ = a * x * b := by group
      _ = x * a * b := by rw [hax]
      _ = x * (a * b) := by group
  have hAy : Commute (a * b) y := by
    show a * b * y = y * (a * b)
    calc a * b * y = a * (b * y) := by group
      _ = a * (y * b) := by rw [hby]
      _ = a * y * b := by group
      _ = y * a * b := by rw [hay]
      _ = y * (a * b) := by group
  have hAw : Commute (a * b) ((x * y) * (y * x)⁻¹) :=
    (hAx.mul_right hAy).mul_right ((hAy.mul_right hAx).inv_right)
  calc (a * x) * (b * y) * (a * x)⁻¹ * (b * y)⁻¹
      = (a * x * b * y) * (b * y * a * x)⁻¹ := by group
    _ = (a * b * (x * y)) * (a * b * (y * x))⁻¹ := by rw [f1, f2]
    _ = (a * b) * ((x * y) * (y * x)⁻¹) * (a * b)⁻¹ := by group
    _ = (x * y) * (y * x)⁻¹ := by rw [hAw.eq]; group
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem le_centralizer_of_isQuasisimple_of_mem_trivialOnQuot {X : Subgroup G} {zX : G}
    (hXq : CFSG.Open.IsQuasisimple X) (hzX : IsClassicalMember p f X zX) {c : G}
    (hc : c ∈ trivialOnQuot X) : X ≤ Subgroup.centralizer ({c} : Set G) := by
  have hOnorm : ((oddCoreIn X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreIn_le X)).mpr (normalizer_oddCoreIn X)
  have hOcen : ∀ u ∈ oddCoreIn X, ∀ y ∈ X, u * y = y * u := by
    rcases Quasisimple.normal_le_center_or_eq_top hXq ((oddCoreIn X).subgroupOf X) with hle | htop
    · intro u hu y hy
      have hu' : (⟨u, oddCoreIn_le X hu⟩ : X) ∈ (oddCoreIn X).subgroupOf X := hu
      have := Subgroup.mem_center_iff.mp (hle hu') ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    · exfalso
      have hz : (⟨zX, hzX.mem⟩ : X) ∈ (oddCoreIn X).subgroupOf X := by
        rw [htop]
        exact Subgroup.mem_top _
      exact hzX.ne_one (eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn _)
        (Subgroup.mem_subgroupOf.mp hz) (sq_eq_one hzX))
  have hperf : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.mp hzX.perfect
  have hle : ⁅X, X⁆ ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have ha : c * x * c⁻¹ * x⁻¹ ∈ oddCoreIn X := hc.2 x hx
    have hb : c * y * c⁻¹ * y⁻¹ ∈ oddCoreIn X := hc.2 y hy
    obtain ⟨a, ha'⟩ : ∃ a, a = c * x * c⁻¹ * x⁻¹ := ⟨_, rfl⟩
    obtain ⟨b, hb'⟩ : ∃ b, b = c * y * c⁻¹ * y⁻¹ := ⟨_, rfl⟩
    rw [← ha'] at ha
    rw [← hb'] at hb
    have e1 : c * x * c⁻¹ = a * x := by rw [ha']; group
    have e2 : c * y * c⁻¹ = b * y := by rw [hb']; group
    have key : c * (x * y * x⁻¹ * y⁻¹) * c⁻¹ = x * y * x⁻¹ * y⁻¹ := by
      calc c * (x * y * x⁻¹ * y⁻¹) * c⁻¹
          = (c * x * c⁻¹) * (c * y * c⁻¹) * (c * x * c⁻¹)⁻¹ * (c * y * c⁻¹)⁻¹ := by group
        _ = (a * x) * (b * y) * (a * x)⁻¹ * (b * y)⁻¹ := by rw [e1, e2]
        _ = x * y * x⁻¹ * y⁻¹ :=
          aux_commutator_of_commute a b x y (hOcen a ha x hx) (hOcen a ha y hy)
            (hOcen b hb x hx) (hOcen b hb y hy) (hOcen a ha b (oddCoreIn_le X hb))
    rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
    calc x * y * x⁻¹ * y⁻¹ * c = (c * (x * y * x⁻¹ * y⁻¹) * c⁻¹) * c := by rw [key]
      _ = c * (x * y * x⁻¹ * y⁻¹) := by group
  rw [hperf] at hle
  exact hle


theorem tqMembers_eq_centMembers_of_quasisimple
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hqs : ∀ L ∈ Ω, CFSG.Open.IsQuasisimple L) : tqMembers Ω c = centMembers Ω c := by
  ext L
  refine ⟨fun hL => ⟨hL.1, ?_⟩, fun hL => ⟨hL.1, mem_trivialOnQuot_of_le_centralizer hL.2⟩⟩
  obtain ⟨zL, hzL⟩ := hcls L hL.1
  exact le_centralizer_of_isQuasisimple_of_mem_trivialOnQuot (hqs L hL.1) hzL hL.2

theorem exactFamily_eq_centMembers_of_quasisimple
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hqs : ∀ L ∈ Ω, CFSG.Open.IsQuasisimple L) : exactFamily Ω c = centMembers Ω c := by
  refine Set.Subset.antisymm ?_ (centMembers_subset_exactFamily hcls)
  rintro _ ⟨K, hK, rfl⟩
  have hK' : K ∈ centMembers Ω c := by
    rw [← tqMembers_eq_centMembers_of_quasisimple hcls hqs]
    exact hK
  have e : exactCore c K = K := exactCore_eq_self_of_mem_centMembers hcls hK'
  change exactCore c K ∈ centMembers Ω c
  rw [e]
  exact hK'

theorem localLeviComponent_of_chainShape_of_quasisimple
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hqs : ∀ L ∈ Ω, CFSG.Open.IsQuasisimple L) {z : G} (hs : ChainShape p f Ω z) :
    LocalLeviComponent p f Ω z := by
  have h : centralizingMembers (exactFamily Ω z) {z} = centralizingMembers Ω {z} :=
    (centMembers_exactFamily Ω z).trans (exactFamily_eq_centMembers_of_quasisimple hcls hqs)
  have key : ∀ S₁ S₂ : Set (Subgroup G), S₁ = S₂ →
      ∀ D : LieSystemData p f (↥(⨆ L ∈ S₁, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₁, L))
        (oddQuotientFamily (restrictFamily S₁ (⨆ L ∈ S₁, L))), ∀ i : Fin D.card,
        ((D.tag i = .PSL ∧ 3 ≤ D.rank i) ∨ D.tag i = .PSU) →
        ∃ D' : LieSystemData p f (↥(⨆ L ∈ S₂, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₂, L))
          (oddQuotientFamily (restrictFamily S₂ (⨆ L ∈ S₂, L))), ∃ i' : Fin D'.card,
          (D'.tag i' = .PSL ∧ 3 ≤ D'.rank i') ∨ D'.tag i' = .PSU ∨ D'.tag i' = .PSp ∨
            HasA2Pairs (D'.tag i') := by
    intro S₁ S₂ h D i hi
    subst h
    exact ⟨D, i, hi.elim Or.inl fun h => Or.inr (Or.inl h)⟩
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hs
  have hlev : (D.tag i₁ = .PSL ∧ 3 ≤ D.rank i₁) ∨ D.tag i₁ = .PSU := by
    rcases ht₁ with h1 | h1
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr h1
  obtain ⟨D', i', hi'⟩ := key _ _ h D i₁ hlev
  exact LocalLeviComponent.of_levi D' i' hi'

end Quasisimple


section Frames

variable {p f : ℕ} [Fact p.Prime]

theorem chainFrame_exists_on_of_lemma52 (hΩ : HypOmegaModAll p f) (hA : AEmptyAll p f)
    (hT : NoTwinsAll p f) (hGen : ChainFrameGenT p f) (h51t : ChainFrameHyp51t p f)
    (h51zt : ChainFrameHyp51zt p f) (h52 : Lemma52) :
    FrameExistsOnE p f (ChainShapePred (p := p) (f := f)) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hshape
  have hΩmod : HypOmegaMod p f (CoreAssembly.conjClass K) := hΩ G hnab hp2 hq K z hz hBelow
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hshapeC : ChainShape p f (CoreAssembly.conjClass K) z := hshape
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hshape
  have hpairD : ChainPair (fundamentalSubgroups (D.tag i₁) (compModel D i₁).D) :=
    chainPair_model hp2 (D.tag i₁) (D.rank i₁) (D.exp i₁) ht₁ (by omega) (D.admissible i₁)
  let C : ChainCtx p f (CoreAssembly.conjClass K) z :=
    { K := K, hK := CoreAssembly.mem_conjClass_self K, hKz := hKz, hΩ := hΩmod, hp := hp2,
      hq := hq, D := D, card_eq := hcard, i₀ := i₀, i₁ := i₁, ne := hne, tag₁ := ht₁,
      tag₀ := ht₀, rank₀ := hr₀, pair := hpairD }
  obtain ⟨L⟩ := C.exists_lift
  have htrans : ∀ M ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g K = M := fun M hM => hM
  have hset : ChainFrameSetting p f (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z' :=
    { odd := hp2
      five := hq
      hyp := hΩmod
      aEmpty := hA G hnab hp2 hq K z hz hBelow
      noTwins := hT G hnab hp2 hq K z hz hBelow
      trans := htrans
      below := hBelow
      shape := hshapeC
      frame := L.frameData
      symm := L.symm
      toral := L.toral }
  have hframe := L.frameSideTwoStar htrans
    (hGen G (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z' hset)
  have hH51 : Hyp51 (Subgroup.closure ({z, L.t, L.z'} : Set G)) :=
    chainFrameHyp51_of_vertices' p f h51t h51zt G (CoreAssembly.conjClass K) K L.J L.K' z
      L.t L.z' hset
  have hbal : RankThreeBalance (Subgroup.closure ({z, L.t, L.z'} : Set G)) := h52 G _ hH51
  have hΩIn : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH : LocalLieSystems p f (CoreAssembly.conjClass K) :=
    localLieSystems_of_citBelowU hΩIn hBelow
  have hcent := centralizes_of_frame hnab hp2 hq hΩIn hconn hframe hz L.z_mem_B
    (L.frameData.tq_B hp2 hq hΩmod) hbal
  have hgen := rankTwoSpan_eq_top_of_dConnected_star hp2 hq hΩIn hframe hconn
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hbal
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
    Nat.prime_two _ hbal.elem (by rw [hbal.card]; norm_num)
  have hKq : CFSG.Open.IsQuasisimple K :=
    Theorem5.isQuasisimple_of_member_of_deltaCore_eq_bot hnab hp2 hq hΩIn hIH
      (CoreAssembly.mem_conjClass_self K) hz
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hbal.elem hF₀.1)
      (hcent.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)
  have hqs : ∀ N ∈ CoreAssembly.conjClass K, CFSG.Open.IsQuasisimple N :=
    Theorem5.isQuasisimple_of_mem_of_single_class (exists_single_class K)
      (CoreAssembly.mem_conjClass_self K) hKq
  have hLevi : LocalLeviComponent p f (CoreAssembly.conjClass K) z :=
    localLeviComponent_of_chainShape_of_quasisimple hΩIn.classical hqs hshapeC
  have hKJ : ∀ a : G, IsClassicalMember p f K a → a = z := fun a ha =>
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq ha).eq hKz
  refine ⟨K, z, Subgroup.closure ({z, L.t, L.z'} : Set G), {K, L.J}, z, ?_, hH51⟩
  exact
    { mem := CoreAssembly.mem_conjClass_self K
      cls := hz
      z₀A := L.z_mem_B
      tq := L.frameData.tq_B hp2 hq hΩmod
      frame := hframe
      aA := L.z_mem_B
      a1 := hKz.ne_one
      aClassical := ⟨K, CoreAssembly.mem_conjClass_self K, hz⟩
      cover := fun M hM _ => L.cover_z htrans hM
      nine := fun _ => ⟨z, L.z_mem_B, hKz.ne_one, fun M hM => L.cover_z htrans hM, hLevi⟩ }

end Frames

end CFSG.ClassicalInvolution.Asc77
