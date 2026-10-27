module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4FCaseI
public import CFSG.ClassicalInvolution.Q3.Q3EXG2D4Model
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactMain
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)
open scoped MatrixGroups

section Defs

variable {G : Type} [Group G]

@[expose] def Cn (Ω : Set (Subgroup G)) (w : G) (N : Subgroup G) : Prop :=
  N ∈ centralizingMembers Ω {w} ∧ ∀ L ∈ centralizingMembers Ω {w}, L = N ∨ Commutes N L

@[expose] def Fb (Ω : Set (Subgroup G)) (w : G) (N : Subgroup G) : Prop :=
  N ∈ centralizingMembers Ω {w} ∧ ¬ Cn Ω w N

@[expose] def layerX (Ω : Set (Subgroup G)) (w : G) : Subgroup G :=
  ⨆ N ∈ {N | Fb Ω w N}, N

theorem fb_or_cn {Ω : Set (Subgroup G)} {w : G} {N : Subgroup G}
    (h : N ∈ centralizingMembers Ω {w}) : Cn Ω w N ∨ Fb Ω w N := by
  by_cases hc : Cn Ω w N
  · exact Or.inl hc
  · exact Or.inr ⟨h, hc⟩

theorem le_layerX {Ω : Set (Subgroup G)} {w : G} {N : Subgroup G} (h : Fb Ω w N) :
    N ≤ layerX Ω w :=
  le_iSup₂ (f := fun N (_ : N ∈ {N | Fb Ω w N}) => N) N h

theorem layerX_le_locLayer (Ω : Set (Subgroup G)) (w : G) : layerX Ω w ≤ locLayer Ω w :=
  iSup₂_le fun _ hN => le_centralizingLayer hN.1

theorem Cn.conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G) {w : G} {N : Subgroup G}
    (h : Cn Ω w N) : Cn Ω (g * w * g⁻¹) (conjSub g N) := by
  refine ⟨?_, fun L hL => ?_⟩
  · rw [centralizingMembers_conj hΩ g w]
    exact ⟨N, h.1, rfl⟩
  · rw [centralizingMembers_conj hΩ g w] at hL
    obtain ⟨L₀, hL₀, rfl⟩ := hL
    rcases h.2 L₀ hL₀ with h1 | h1
    · exact Or.inl (by rw [h1])
    · exact Or.inr (h1.conjSub g)

theorem cn_conj_iff {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G) {w : G}
    {N : Subgroup G} : Cn Ω (g * w * g⁻¹) (conjSub g N) ↔ Cn Ω w N := by
  refine ⟨fun h => ?_, Cn.conj hΩ g⟩
  have := h.conj hΩ g⁻¹
  rwa [conjSub_inv_conjSub, show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at this

theorem fb_conj_iff {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G) {w : G}
    {N : Subgroup G} : Fb Ω (g * w * g⁻¹) (conjSub g N) ↔ Fb Ω w N := by
  unfold Fb
  rw [cn_conj_iff hΩ g, centralizingMembers_conj hΩ g w]
  exact and_congr_left' ⟨fun ⟨M, hM, h⟩ => by rwa [← conjSub_injective g h], fun h => ⟨N, h, rfl⟩⟩

theorem ncard_fb_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g w : G) :
    {N | Fb Ω (g * w * g⁻¹) N}.ncard = {N | Fb Ω w N}.ncard := by
  have : {N | Fb Ω (g * w * g⁻¹) N} = conjSub g '' {N | Fb Ω w N} := by
    ext N
    constructor
    · intro hN
      refine ⟨conjSub g⁻¹ N, ?_, conjSub_conjSub_inv g N⟩
      show Fb Ω w (conjSub g⁻¹ N)
      rw [← fb_conj_iff hΩ g, conjSub_conjSub_inv]
      exact hN
    · rintro ⟨N₀, hN₀, rfl⟩
      exact (fb_conj_iff hΩ g).mpr hN₀
  rw [this, Set.ncard_image_of_injective _ (conjSub_injective g)]

theorem conjSub_layerX {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g w : G) :
    conjSub g (layerX Ω w) = layerX Ω (g * w * g⁻¹) := by
  have key : ∀ (h : G) (w' : G), conjSub h (layerX Ω w') ≤ layerX Ω (h * w' * h⁻¹) := by
    intro h w'
    have : layerX Ω w' ≤ conjSub h⁻¹ (layerX Ω (h * w' * h⁻¹)) := by
      refine iSup₂_le fun N hN => ?_
      have h1 : conjSub h N ≤ layerX Ω (h * w' * h⁻¹) := le_layerX ((fb_conj_iff hΩ h).mpr hN)
      have h2 := conjSub_mono (n := h⁻¹) h1
      rwa [conjSub_inv_conjSub] at h2
    have h3 := conjSub_mono (n := h) this
    rwa [conjSub_conjSub_inv] at h3
  refine le_antisymm (key g w) ?_
  have := conjSub_mono (n := g) (key g⁻¹ (g * w * g⁻¹))
  rw [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group, conjSub_conjSub_inv] at this
  exact this

end Defs

structure ExCtx3 (G : Type) [Group G] [Finite G] (K : Subgroup G) (z : G) (a : ℕ)
    (t : StatedLieTag) (n : ℕ) : Prop where
  setup : RouteD3Setup K z
  o3 : LocalOddThreeFree3 (conjClass3 K) z
  ht : t = .G2 ∨ t = .trialityD4
  hadm : StatedLieAdmissible t n 3 1
  loc : LocalShapeC3 a (CompData.model t n) (conjClass3 K) z

structure Pkg3 {G : Type} [Group G] (a : ℕ) (t : StatedLieTag) (n : ℕ) (Ω : Set (Subgroup G))
    (w : G) : Type 1 where
  ι : Type
  fin : Finite ι
  D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)
  i₁ : ι
  card : Nat.card ι = a + 1
  kind : D.kind i₁ = CompData.model t n
  rest : ∀ i, i ≠ i₁ → D.kind i = CompData.sl23
  p1 : LocalOddCentral Ω {w}
  o3 : LocalOddThreeFree3 Ω w

section Context

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {a : ℕ} {t : StatedLieTag}
  {n : ℕ}

theorem ExCtx3.exists_pkg (S : ExCtx3 G K z a t n) {N : Subgroup G} (hN : N ∈ conjClass3 K)
    {w : G} (hw : IsClassicalMember3 N w) : Nonempty (Pkg3 a t n (conjClass3 K) w) := by
  have hΩ := S.setup.inClass
  obtain ⟨-, hP1⟩ := S.setup.setup
  obtain ⟨g, hg⟩ := single_class3 K N hN
  have hw' : IsClassicalMember3 N (g * z * g⁻¹) := by
    rw [hg]
    exact S.setup.cls.conj g
  have hww : g * z * g⁻¹ = w := involution_unique3 hw' hw
  subst hww
  have hP1' : LocalOddCentral (conjClass3 K) {g * z * g⁻¹} :=
    RouteD.Gaps.localOddCentral_conj hΩ.conjInvariant g z hP1
  have hO3' : LocalOddThreeFree3 (conjClass3 K) (g * z * g⁻¹) :=
    localOddThreeFree3_conj hΩ.conjInvariant g z S.o3
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := S.loc
  obtain ⟨D', hD'⟩ := exists_lieSystemData3_conj hΩ.conjInvariant g z D
  exact ⟨⟨ι, hι, D', i₁, hcard, by rw [hD']; exact hk, fun i hi => by rw [hD']; exact hrest i hi,
    hP1', hO3'⟩⟩

end Context

section Package

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G} {a : ℕ}
  {t : StatedLieTag} {n : ℕ}

theorem G2D4Facts3.exists_noncomm_conj {c : CompData} (F : G2D4Facts3 c) {R : Subgroup c.G}
    (hR : R ∈ c.fund) : ∃ g : c.G, conjSub g R ≠ R ∧ ¬ Commutes R (conjSub g R) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, ⟨x, hxR, hx1, -, hxC⟩, -⟩ := F.fg0 R hR
  set C : Subgroup c.G := Subgroup.centralizer (R : Set c.G) with hC
  have hconj : ∀ g : c.G, conjSub g R ≤ R ⊔ C := by
    intro g
    by_cases h : conjSub g R = R
    · rw [h]
      exact le_sup_left
    · intro y hy
      refine Subgroup.mem_sup_right ?_
      rw [hC, Subgroup.mem_centralizer_iff]
      intro h' hh'
      exact hcon g h h' hh' y hy
  have hsimple := F.simple
  have hRbot : R ≠ ⊥ := fun h => hx1 (by rw [h] at hxR; exact Subgroup.mem_bot.mp hxR)
  have hnc : Subgroup.normalClosure (R : Set c.G) = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (R : Set c.G)) with h | h
    · exfalso
      apply hRbot
      rw [eq_bot_iff]
      intro y hy
      have : y ∈ Subgroup.normalClosure (R : Set c.G) := Subgroup.subset_normalClosure hy
      rw [h] at this
      exact this
    · exact h
  have hle : Subgroup.normalClosure (R : Set c.G) ≤ R ⊔ C := by
    rw [Subgroup.normalClosure]
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨b, hb, hbc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨g, hg⟩ := isConj_iff.mp hbc
    have : y ∈ conjSub g R := by
      rw [← hg]
      exact conj_mem_conjSub hb
    exact hconj g this
  have htop : R ⊔ C = ⊤ := eq_top_iff.mpr (hnc ▸ hle)
  have hnorm : Subgroup.normalizer (R : Set c.G) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hRn : R.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  rcases hsimple.eq_bot_or_eq_top_of_normal R with h | h
  · exact hRbot h
  · have hCbot : C = ⊥ := by
      have : C = Subgroup.center c.G := by
        rw [hC, h]
        exact Subgroup.centralizer_univ
      rw [this, F.center_bot]
    rw [hCbot, Subgroup.commutator_bot_left, Subgroup.commutator_bot_left] at hxC
    exact hx1 (Subgroup.mem_bot.mp hxC)

theorem Pkg3.facts (P : Pkg3 a t n Ω w) (F : G2D4Facts3 (CompData.model t n)) :
    G2D4Facts3 (P.D.kind P.i₁) := by
  rw [P.kind]
  exact F

theorem Pkg3.inj (P : Pkg3 a t n Ω w) (F : G2D4Facts3 (CompData.model t n)) :
    Function.Injective (P.D.hom P.i₁) := by
  have hF := P.facts F
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  exact (P.D.ker_le_center P.i₁).trans hF.center_bot.le

theorem Pkg3.fb_iff (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (F : G2D4Facts3 (CompData.model t n)) {N : Subgroup G} :
    Fb Ω w N ↔ N ∈ compMembers3 Ω w P.D P.i₁ := by
  have hF := P.facts F
  have hinj := P.inj F
  constructor
  · rintro ⟨hNw, hnc⟩
    obtain ⟨j, hj, -⟩ := exists_unique_comp3 hΩ hex P.p1 P.o3 P.D hNw
    by_cases hji : j = P.i₁
    · subst hji
      exact hj
    · exfalso
      have hA : IsA1Comp3 P.D j := P.rest j hji
      apply hnc
      refine ⟨hNw, fun L hL => ?_⟩
      obtain ⟨j', hj', -⟩ := exists_unique_comp3 hΩ hex P.p1 P.o3 P.D hL
      by_cases hjj : j' = j
      · subst hjj
        exact Or.inl (eq_of_mem_compMembers_a13 hΩ hex P.p1 P.o3 hA hj' hj)
      · exact Or.inr (commutes_of_ne_comp3 hΩ hex P.p1 P.o3 P.D (Ne.symm hjj) hj hj')
  · intro hN
    refine ⟨hN.1, fun hcn => ?_⟩
    obtain ⟨R, hR⟩ := exists_corr_left3 hΩ hex P.p1 P.o3 P.D hN
    obtain ⟨g, hg1, hg2⟩ := hF.exists_noncomm_conj hR.2.1
    obtain ⟨ĝ, hĝ⟩ := QuotientGroup.mk_surjective (P.D.hom P.i₁ g)
    have hL' : conjSub (ĝ : G) N ∈ compMembers3 Ω w P.D P.i₁ :=
      conjSub_mem_compMembers_of_mem_layer3 hΩ.conjInvariant hN ĝ.2
    have himg : locImg Ω w (conjSub (ĝ : G) N) = (conjSub g R).map (P.D.hom P.i₁) := by
      rw [Gaps.locImg_conjSub_layer N ĝ, hR.2.2, show locMk Ω w ĝ = P.D.hom P.i₁ g from hĝ]
      unfold conjSub
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext a
      simp
    rcases hcn.2 _ hL'.1 with heq | hcomm
    · apply hg1
      have h1 : locImg Ω w (conjSub (ĝ : G) N) = locImg Ω w N := by rw [heq]
      rw [himg, hR.2.2] at h1
      exact Subgroup.map_injective hinj h1
    · apply hg2
      have h2 := commutes_locImg_of_commutes (x := w) (Ω := Ω) hcomm
      rw [himg, hR.2.2] at h2
      intro a' ha' b hb
      exact hinj (by rw [map_mul, map_mul]; exact h2 _ ⟨a', ha', rfl⟩ _ ⟨b, hb, rfl⟩)

theorem Pkg3.cn_of_isClassicalMember (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) (F : G2D4Facts3 (CompData.model t n)) {N : Subgroup G}
    (hN : N ∈ Ω) (hw : IsClassicalMember3 N w) : Cn Ω w N := by
  have hNw : N ∈ centralizingMembers Ω {w} := ⟨hN, isSubnormal_le hw.subnormal⟩
  by_contra hcn
  have hcomp := (P.fb_iff hΩ hex F).mp ⟨hNw, hcn⟩
  have hF := P.facts F
  have hinj := P.inj F
  obtain ⟨R, hR⟩ := exists_corr_left3 hΩ hex P.p1 P.o3 P.D hcomp
  obtain ⟨hwY, hwm, -, hw1, -⟩ := image_involution_facts3 hNw hw
  rw [hR.2.2] at hwm
  obtain ⟨r, hrR, hr⟩ := hwm
  have hcen : ∀ q : locQuot Ω w, QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w))
      ⟨w, hwY⟩ * q = q * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w))
        ⟨w, hwY⟩ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hyc : (⟨w, hwY⟩ : ↥(locLayer Ω w)) * y = y * ⟨w, hwY⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
        (centralizingLayer_le_centralizer Ω {w} y.2)).symm
    have := congrArg (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w))) hyc
    rw [map_mul, map_mul] at this
    exact this
  have hrc : ∀ g : (P.D.kind P.i₁).G, r * g = g * r := by
    intro g
    apply hinj
    rw [map_mul, map_mul, hr]
    exact hcen _
  have hr1 : r = 1 := by
    have : r ∈ Subgroup.center (P.D.kind P.i₁).G :=
      Subgroup.mem_center_iff.mpr fun g => (hrc g).symm
    rw [hF.center_bot] at this
    exact this
  apply hw1
  rw [← hr, hr1, map_one]

theorem Pkg3.cnbhd_iff (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (F : G2D4Facts3 (CompData.model t n)) {N : Subgroup G} (hN : N ∈ Ω)
    (hw : IsClassicalMember3 N w) {L : Subgroup G} (hL : L ∈ Ω) :
    (L = N ∨ Commutes L N) ↔ L ∈ centralizingMembers Ω {w} := by
  constructor
  · rintro (rfl | h)
    · exact ⟨hN, isSubnormal_le hw.subnormal⟩
    · exact mem_centralizingMembers_of_commutes hL hw.mem h
  · intro hLw
    rcases (P.cn_of_isClassicalMember hΩ hex F hN hw).2 L hLw with h | h
    · exact Or.inl h
    · exact Or.inr h.symm

end Package

section Partners

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G} {a : ℕ}
  {t : StatedLieTag} {n : ℕ}

theorem Pkg3.partner_data (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (F : G2D4Facts3 (CompData.model t n)) {b : Subgroup G} (hb : Fb Ω w b) {w₁ : G}
    (hw₁ : IsClassicalMember3 b w₁) :
    ∃ (R : Subgroup (P.D.kind P.i₁).G) (r : (P.D.kind P.i₁).G) (hY : w₁ ∈ locLayer Ω w),
      R ∈ (P.D.kind P.i₁).fund ∧ locImg Ω w b = R.map (P.D.hom P.i₁) ∧ IsUniqueInvolution R r ∧
      P.D.hom P.i₁ r =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨w₁, hY⟩ := by
  have hinj := P.inj F
  obtain ⟨R, hR⟩ := exists_corr_left3 hΩ hex P.p1 P.o3 P.D ((P.fb_iff hΩ hex F).mp hb)
  obtain ⟨hwY, hwm, hwsq, hw1, -⟩ := image_involution_facts3 hb.1 hw₁
  have hwm' := hwm
  rw [hR.2.2] at hwm'
  obtain ⟨r, hrR, hr⟩ := hwm'
  refine ⟨R, r, hwY, hR.2.1, hR.2.2, ⟨hrR, ?_, ?_, ?_⟩, hr⟩
  · intro h
    apply hw1
    rw [← hr, h, map_one]
  · apply hinj
    rw [map_mul, hr, hwsq, map_one]
  · intro y hy hy2
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      obtain ⟨e⟩ := nonempty_mulEquiv_locImg3 hΩ hex hb.1
      have hinv : ∀ s : SL(2, ZMod 3), s * s = 1 → s ≠ 1 → s = -1 := by decide +kernel
      have hya : P.D.hom P.i₁ y ∈ locImg Ω w b := by
        rw [hR.2.2]
        exact Subgroup.mem_map_of_mem _ hy
      have h1 : e ⟨P.D.hom P.i₁ y, hya⟩ = -1 := by
        refine hinv _ ?_ ?_
        · rw [← map_mul]
          have : (⟨P.D.hom P.i₁ y, hya⟩ : locImg Ω w b) * ⟨P.D.hom P.i₁ y, hya⟩ = 1 :=
            Subtype.ext (by
              show P.D.hom P.i₁ y * P.D.hom P.i₁ y = 1
              rw [← map_mul, hy2, map_one])
          rw [this, map_one]
        · intro h
          have : (⟨P.D.hom P.i₁ y, hya⟩ : locImg Ω w b) = 1 := e.injective (h.trans e.map_one.symm)
          exact hy1 (hinj (by simpa using congrArg Subtype.val this))
      have h2 : e ⟨locMk Ω w ⟨w₁, hwY⟩, hwm⟩ = -1 := by
        refine hinv _ ?_ ?_
        · rw [← map_mul]
          have : (⟨locMk Ω w ⟨w₁, hwY⟩, hwm⟩ : locImg Ω w b) * ⟨locMk Ω w ⟨w₁, hwY⟩, hwm⟩ = 1 :=
            Subtype.ext hwsq
          rw [this, map_one]
        · intro h
          have : (⟨locMk Ω w ⟨w₁, hwY⟩, hwm⟩ : locImg Ω w b) = 1 :=
            e.injective (h.trans e.map_one.symm)
          exact hw1 (congrArg Subtype.val this)
      have h3 : (⟨P.D.hom P.i₁ y, hya⟩ : locImg Ω w b) = ⟨locMk Ω w ⟨w₁, hwY⟩, hwm⟩ :=
        e.injective (h1.trans h2.symm)
      apply hinj
      rw [hr]
      exact congrArg Subtype.val h3

theorem Pkg3.partners_commuting (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (F : G2D4Facts3 (CompData.model t n)) {b₁ b₂ : Subgroup G} (h₁ : Fb Ω w b₁)
    (h₂ : Fb Ω w b₂) {w₁ w₂ : G} (hw₁ : IsClassicalMember3 b₁ w₁)
    (hw₂ : IsClassicalMember3 b₂ w₂) (hc : Commutes b₁ b₂) :
    ∃ (R₁ R₂ : Subgroup (P.D.kind P.i₁).G) (r : (P.D.kind P.i₁).G) (hY₁ : w₁ ∈ locLayer Ω w)
      (hY₂ : w₂ ∈ locLayer Ω w), R₁ ∈ (P.D.kind P.i₁).fund ∧ R₂ ∈ (P.D.kind P.i₁).fund ∧
      locImg Ω w b₁ = R₁.map (P.D.hom P.i₁) ∧ locImg Ω w b₂ = R₂.map (P.D.hom P.i₁) ∧
      IsUniqueInvolution R₁ r ∧ IsUniqueInvolution R₂ r ∧
      P.D.hom P.i₁ r =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨w₁, hY₁⟩ ∧
      P.D.hom P.i₁ r =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨w₂, hY₂⟩ := by
  have hF := P.facts F
  have hinj := P.inj F
  obtain ⟨R₁, r₁, hY₁, hR₁, hi₁, hu₁, hr₁⟩ := P.partner_data hΩ hex F h₁ hw₁
  obtain ⟨R₂, r₂, hY₂, hR₂, hi₂, hu₂, hr₂⟩ := P.partner_data hΩ hex F h₂ hw₂
  have hcomm : ∀ s ∈ R₁, s * r₂ = r₂ * s := by
    intro s hs
    apply hinj
    rw [map_mul, map_mul]
    have hs' : P.D.hom P.i₁ s ∈ locImg Ω w b₁ := by
      rw [hi₁]
      exact Subgroup.mem_map_of_mem _ hs
    have hr' : P.D.hom P.i₁ r₂ ∈ locImg Ω w b₂ := by
      rw [hi₂]
      exact Subgroup.mem_map_of_mem _ hu₂.mem
    exact commutes_locImg_of_commutes (x := w) (Ω := Ω) hc _ hs' _ hr'
  have hrr : r₁ = r₂ := hF.shared R₁ hR₁ r₁ r₂ hu₁.sq hu₂.sq hu₁.ne_one hu₂.ne_one
    (fun s hs => (hu₁.commute_of_mem hs).symm) hcomm
  subst hrr
  exact ⟨R₁, R₂, r₁, hY₁, hY₂, hR₁, hR₂, hi₁, hi₂, hu₁, hu₂, hr₁, hr₂⟩

theorem Pkg3.eq_involution_of_commuting_pair (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) (F : G2D4Facts3 (CompData.model t n)) {b₁ b₂ : Subgroup G}
    (h₁ : Fb Ω w b₁) (h₂ : Fb Ω w b₂) {w₁ w₂ : G} (hw₁ : IsClassicalMember3 b₁ w₁)
    (hw₂ : IsClassicalMember3 b₂ w₂) (hc : Commutes b₁ b₂) : w₁ = w₂ := by
  obtain ⟨-, -, r, hY₁, hY₂, -, -, -, -, -, -, hr₁, hr₂⟩ :=
    P.partners_commuting hΩ hex F h₁ h₂ hw₁ hw₂ hc
  exact G2D4.eq_of_mk_eq_of_involutions P.p1 hY₁ hY₂
    (mul_self_eq_one_of_isClassicalMember3 hw₁) (mul_self_eq_one_of_isClassicalMember3 hw₂)
    (hr₁.symm.trans hr₂)

theorem G2D4Facts3.td4_eq {c : CompData} {n : ℕ} (hk : c = CompData.model .trialityD4 n)
    (hadm : StatedLieAdmissible .trialityD4 n 3 1) {R R' : Subgroup c.G} (hR : R ∈ c.fund)
    (hR' : R' ∈ c.fund) {r : c.G} (h : IsUniqueInvolution R r) (h' : IsUniqueInvolution R' r)
    (hcard : Nat.card R = Nat.card R') : R = R' := by
  subst hk
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  by_cases hconj : ∃ g, R' = R.map (MulAut.conj g).toMonoidHom
  · obtain ⟨g, hg⟩ := hconj
    have hnt := G2D4Models.noTwinsFund_of_td4_tag hp2 rfl hadm
    have : conjSub g R = R := hnt R hR r h g (by rw [show conjSub g R = R' from hg.symm]; exact h')
    rw [hg]
    exact this.symm
  · exact absurd hcard (Asc77.d4OrdersDiffer 3 .trialityD4 n 1 rfl hadm R hR R' hR' hconj)

theorem Pkg3.false_of_td4_pair (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (F : G2D4Facts3 (CompData.model t n)) (htd : t = .trialityD4)
    (hadm : StatedLieAdmissible t n 3 1) {b₁ b₂ : Subgroup G} (h₁ : Fb Ω w b₁)
    (h₂ : Fb Ω w b₂) (hne : b₁ ≠ b₂) {w₁ w₂ : G} (hw₁ : IsClassicalMember3 b₁ w₁)
    (hw₂ : IsClassicalMember3 b₂ w₂) (hc : Commutes b₁ b₂) : False := by
  have hinj := P.inj F
  obtain ⟨R₁, R₂, r, -, -, hR₁, hR₂, hi₁, hi₂, hu₁, hu₂, -, -⟩ :=
    P.partners_commuting hΩ hex F h₁ h₂ hw₁ hw₂ hc
  have hc₁ : Nat.card R₁ = 24 := by
    rw [← Subgroup.card_map_of_injective hinj, ← hi₁]
    exact card_locImg3 hΩ hex h₁.1
  have hc₂ : Nat.card R₂ = 24 := by
    rw [← Subgroup.card_map_of_injective hinj, ← hi₂]
    exact card_locImg3 hΩ hex h₂.1
  have hcard : Nat.card R₁ = Nat.card R₂ := hc₁.trans hc₂.symm
  subst htd
  have heq := G2D4Facts3.td4_eq P.kind hadm hR₁ hR₂ hu₁ hu₂ hcard
  apply hne
  refine locImg_injOn3 hΩ hex P.p1 P.o3 h₁.1 h₂.1 ?_
  rw [hi₁, hi₂, heq]

end Partners

section Points

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {a : ℕ} {t : StatedLieTag}
  {n : ℕ}

theorem exists_conj_point {N N' : Subgroup G} (hN : N ∈ conjClass3 K) (hN' : N' ∈ conjClass3 K)
    {x y : G} (hx : IsClassicalMember3 N x) (hy : IsClassicalMember3 N' y) :
    ∃ g : G, g * y * g⁻¹ = x := by
  obtain ⟨g₁, hg₁⟩ := single_class3 K N hN
  obtain ⟨g₂, hg₂⟩ := single_class3 K N' hN'
  have hconj : conjSub (g₁ * g₂⁻¹) N' = N := by
    rw [hg₂, hg₁, conjSub_mul, conjSub_inv_conjSub]
  have h := hy.conj (g₁ * g₂⁻¹)
  rw [hconj] at h
  exact ⟨g₁ * g₂⁻¹, involution_unique3 h hx⟩

theorem ncard_om_eq (hΩ : ConjInvariant (conjClass3 K)) {N N' : Subgroup G}
    (hN : N ∈ conjClass3 K) (hN' : N' ∈ conjClass3 K) {x y : G} (hx : IsClassicalMember3 N x)
    (hy : IsClassicalMember3 N' y) :
    (centralizingMembers (conjClass3 K) {x}).ncard =
      (centralizingMembers (conjClass3 K) {y}).ncard := by
  obtain ⟨g, hg⟩ := exists_conj_point hN hN' hx hy
  rw [← hg]
  exact ncard_centralizingMembers_conj hΩ g y

theorem fb_of_cn_of_fb (S : ExCtx3 G K z a t n) (F : G2D4Facts3 (CompData.model t n))
    {u : G} {N₀ : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K) (hu : IsClassicalMember3 N₀ u)
    {L : Subgroup G} (hL : Fb (conjClass3 K) u L) {v : G} (hv : IsClassicalMember3 L v)
    {N : Subgroup G} (hN : Cn (conjClass3 K) u N) : Fb (conjClass3 K) v N := by
  classical
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  have hLΩ : L ∈ conjClass3 K := hL.1.1
  have hNΩ : N ∈ conjClass3 K := hN.1.1
  have hLN : Commutes N L := by
    rcases hN.2 L hL.1 with h | h
    · subst h
      exact absurd hN hL.2
    · exact h
  have hNv : N ∈ centralizingMembers (conjClass3 K) {v} :=
    mem_centralizingMembers_of_commutes hNΩ hv.mem hLN
  refine ⟨hNv, fun hcn => ?_⟩
  obtain ⟨wN, hwN⟩ := hΩ.classical N hNΩ
  obtain ⟨PN⟩ := S.exists_pkg hNΩ hwN
  obtain ⟨Pv⟩ := S.exists_pkg hLΩ hv
  have hcnb := fun (L' : Subgroup G) (hL' : L' ∈ conjClass3 K) =>
    PN.cnbhd_iff hΩ hex F hNΩ hwN hL'
  have h1 : centralizingMembers (conjClass3 K) {u} ⊆ centralizingMembers (conjClass3 K) {wN} :=
    fun L' hL' => (hcnb L' hL'.1).mp (by
      rcases hN.2 L' hL' with h | h
      · exact Or.inl h
      · exact Or.inr h.symm)
  have h2 : centralizingMembers (conjClass3 K) {v} ⊆ centralizingMembers (conjClass3 K) {wN} :=
    fun L' hL' => (hcnb L' hL'.1).mp (by
      rcases hcn.2 L' hL' with h | h
      · exact Or.inl h
      · exact Or.inr h.symm)
  have e1 := ncard_om_eq hΩ.conjInvariant hN₀ hNΩ hu hwN
  have e2 := ncard_om_eq hΩ.conjInvariant hLΩ hNΩ hv hwN
  have h1' := Set.eq_of_subset_of_ncard_le h1 e1.ge (Set.toFinite _)
  have h2' := Set.eq_of_subset_of_ncard_le h2 e2.ge (Set.toFinite _)
  have hLcn := Pv.cn_of_isClassicalMember hΩ hex F hLΩ hv
  apply hL.2
  refine ⟨hL.1, fun L' hL' => hLcn.2 L' ?_⟩
  rw [h2', ← h1']
  exact hL'

theorem fb_of_cn_swap (S : ExCtx3 G K z a t n) (F : G2D4Facts3 (CompData.model t n))
    {u : G} {N₀ : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K) (hu : IsClassicalMember3 N₀ u)
    {M : Subgroup G} (hM : Fb (conjClass3 K) u M) {x : G} (hx : IsClassicalMember3 M x)
    {N : Subgroup G} (hN : Cn (conjClass3 K) x N) : Fb (conjClass3 K) u N := by
  obtain ⟨P⟩ := S.exists_pkg hN₀ hu
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  have h1 : Fb (conjClass3 K) x N₀ :=
    fb_of_cn_of_fb S F hN₀ hu hM hx (P.cn_of_isClassicalMember hΩ hex F hN₀ hu)
  exact fb_of_cn_of_fb S F hM.1.1 hx h1 hu hN

theorem cn_isClassical (S : ExCtx3 G K z a t n) (F : G2D4Facts3 (CompData.model t n))
    {N₀ : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K) {w : G} (hw : IsClassicalMember3 N₀ w)
    {N : Subgroup G} (hN : Cn (conjClass3 K) w N) : IsClassicalMember3 N w := by
  classical
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨P⟩ := S.exists_pkg hN₀ hw
  have hN₀cn := P.cn_of_isClassicalMember hΩ hex F hN₀ hw
  by_cases hNN₀ : N = N₀
  · rw [hNN₀]
    exact hw
  obtain ⟨j, hj, -⟩ := exists_unique_comp3 hΩ hex P.p1 P.o3 P.D hN.1
  obtain ⟨j₀, hj₀, -⟩ := exists_unique_comp3 hΩ hex P.p1 P.o3 P.D hN₀cn.1
  have hjne : j ≠ P.i₁ := fun h => by
    subst h
    exact ((P.fb_iff hΩ hex F).mpr hj).2 hN
  have hjj : j ≠ j₀ := fun h => by
    subst h
    exact hNN₀ (eq_of_mem_compMembers_a13 hΩ hex P.p1 P.o3 (P.rest j hjne) hj hj₀)
  have hcomm : Commutes N₀ N :=
    commutes_of_ne_comp3 hΩ hex P.p1 P.o3 P.D (Ne.symm hjj) hj₀ hj
  obtain ⟨M, hM⟩ := exists_mem_compMembers3 (D := P.D) P.i₁
  have hMfb : Fb (conjClass3 K) w M := (P.fb_iff hΩ hex F).mpr hM
  obtain ⟨x, hx⟩ := hΩ.classical M hM.1.1
  have hN₀fb : Fb (conjClass3 K) x N₀ := fb_of_cn_of_fb S F hN₀ hw hMfb hx hN₀cn
  have hNfb : Fb (conjClass3 K) x N := fb_of_cn_of_fb S F hN₀ hw hMfb hx hN
  obtain ⟨Px⟩ := S.exists_pkg hM.1.1 hx
  obtain ⟨wN, hwN⟩ := hΩ.classical N hN.1.1
  have hww : w = wN := Px.eq_involution_of_commuting_pair hΩ hex F hN₀fb hNfb hw hwN hcomm
  rw [hww]
  exact hwN

theorem exists_other_cn (S : ExCtx3 G K z a t n) (F : G2D4Facts3 (CompData.model t n))
    (ha : 2 ≤ a) {N₀ : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K) {w : G}
    (hw : IsClassicalMember3 N₀ w) : ∃ N, Cn (conjClass3 K) w N ∧ N ≠ N₀ := by
  classical
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨P⟩ := S.exists_pkg hN₀ hw
  have hN₀cn := P.cn_of_isClassicalMember hΩ hex F hN₀ hw
  obtain ⟨j₀, hj₀, -⟩ := exists_unique_comp3 hΩ hex P.p1 P.o3 P.D hN₀cn.1
  have hj₀ne : j₀ ≠ P.i₁ := fun h => by
    subst h
    exact ((P.fb_iff hΩ hex F).mpr hj₀).2 hN₀cn
  have hex' : ∃ j', j' ≠ P.i₁ ∧ j' ≠ j₀ := by
    by_contra hcon
    push Not at hcon
    have := P.fin
    have hsub : (Set.univ : Set P.ι) ⊆ {P.i₁, j₀} := fun j _ => by
      by_cases h1 : j = P.i₁
      · exact Or.inl h1
      · exact Or.inr (hcon j h1)
    have hle : (Set.univ : Set P.ι).ncard ≤ ({P.i₁, j₀} : Set P.ι).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({P.i₁, j₀} : Set P.ι).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by simp)
    rw [Set.ncard_univ, P.card] at hle
    omega
  obtain ⟨j', hj'1, hj'2⟩ := hex'
  obtain ⟨N, hN⟩ := exists_mem_compMembers3 (D := P.D) j'
  have hNcn : Cn (conjClass3 K) w N := by
    rcases fb_or_cn hN.1 with h | h
    · exact h
    · exfalso
      have hc := (P.fb_iff hΩ hex F).mp h
      obtain ⟨jj, -, huniq⟩ := exists_unique_comp3 hΩ hex P.p1 P.o3 P.D hN.1
      exact hj'1 ((huniq j' hN).trans (huniq P.i₁ hc).symm)
  refine ⟨N, hNcn, fun h => ?_⟩
  subst h
  obtain ⟨jj, -, huniq⟩ := exists_unique_comp3 hΩ hex P.p1 P.o3 P.D hN.1
  exact hj'2 ((huniq j' hN).trans (huniq j₀ hj₀).symm)

theorem false_of_td4_two (S : ExCtx3 G K z a t n) (F : G2D4Facts3 (CompData.model t n))
    (htd : t = .trialityD4) (ha : 2 ≤ a) {N₀ : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K) {w : G}
    (hw : IsClassicalMember3 N₀ w) : False := by
  classical
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨N, hN, hne⟩ := exists_other_cn S F ha hN₀ hw
  obtain ⟨P⟩ := S.exists_pkg hN₀ hw
  have hN₀cn := P.cn_of_isClassicalMember hΩ hex F hN₀ hw
  have hcomm : Commutes N₀ N := by
    rcases hN₀cn.2 N hN.1 with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨M, hM⟩ := exists_mem_compMembers3 (D := P.D) P.i₁
  have hMfb : Fb (conjClass3 K) w M := (P.fb_iff hΩ hex F).mpr hM
  obtain ⟨x, hx⟩ := hΩ.classical M hM.1.1
  have hN₀fb : Fb (conjClass3 K) x N₀ := fb_of_cn_of_fb S F hN₀ hw hMfb hx hN₀cn
  have hNfb : Fb (conjClass3 K) x N := fb_of_cn_of_fb S F hN₀ hw hMfb hx hN
  obtain ⟨Px⟩ := S.exists_pkg hM.1.1 hx
  obtain ⟨wN, hwN⟩ := hΩ.classical N hN.1.1
  exact Px.false_of_td4_pair hΩ hex F htd S.hadm hN₀fb hNfb (Ne.symm hne) hw hwN hcomm

end Points

end CFSG.ClassicalInvolution.Q3.Q3W.EX
