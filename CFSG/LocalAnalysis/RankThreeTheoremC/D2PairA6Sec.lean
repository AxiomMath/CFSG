module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Ctx
public import CFSG.RankThree.PartTwo.Sec21.Item234
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBasic
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRGN

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.McLaughlin
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

@[expose] def ThreeSections {X : Type*} [Group X] (N : Subgroup X) : Prop :=
  ∀ (H : Subgroup X) (T : Subgroup H) [T.Normal], H ≤ N → IsSimpleGroup (H ⧸ T) →
    Nat.card (H ⧸ T) = 3 ∨ Nat.Coprime 3 (Nat.card (H ⧸ T))

theorem a6s_threeSections_mono {X : Type*} [Group X] {A B : Subgroup X} (hAB : A ≤ B)
    (h : ThreeSections B) : ThreeSections A := by
  intro H T _ hHA hs
  exact h H T (hHA.trans hAB) hs

theorem a6s_threeSections_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {N : Subgroup X}
    (h : ThreeSections N) : ThreeSections (N.map f) := by
  intro Hy Ty _ hHy hs
  let Hx : Subgroup X := N ⊓ Hy.comap f
  let ψ : ↥Hx →* ↥Hy := (f.comp Hx.subtype).codRestrict Hy fun x => x.2.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨n, hn, hny⟩ := hHy hy
    exact ⟨⟨n, hn, by simpa [hny] using hy⟩, Subtype.ext hny⟩
  let q : ↥Hx →* ↥Hy ⧸ Ty := (QuotientGroup.mk' Ty).comp ψ
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective Ty).comp hψ
  let e : ↥Hx ⧸ q.ker ≃* ↥Hy ⧸ Ty := QuotientGroup.quotientKerEquivOfSurjective q hq
  have : IsSimpleGroup (↥Hx ⧸ q.ker) := MulEquiv.isSimpleGroup e
  have key := h Hx q.ker inf_le_left this
  rw [Nat.card_congr e.toEquiv] at key
  exact key

theorem a6s_threeSections_of_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {N : Subgroup X} {B : Subgroup Y} (hNB : N.map f ≤ B)
    (h : ThreeSections B) : ThreeSections N := by
  intro H T _ hHN hs
  let eH : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
  let Ty : Subgroup ↥(H.map f) := T.map eH.toMonoidHom
  have : Ty.Normal := Subgroup.Normal.map ‹T.Normal› eH.toMonoidHom eH.surjective
  let e : ↥H ⧸ T ≃* ↥(H.map f) ⧸ Ty := QuotientGroup.congr T Ty eH rfl
  have : IsSimpleGroup (↥(H.map f) ⧸ Ty) := MulEquiv.isSimpleGroup e.symm
  have key := h (H.map f) Ty ((Subgroup.map_mono hHN).trans hNB) this
  rw [← Nat.card_congr e.toEquiv] at key
  exact key

theorem a6s_isPSolvable_of_threeSections {W : Type*} [Group W] {A : Subgroup W}
    (h : ThreeSections A) : CFSG.HallHigman.IsPSolvable 3 ↥A := by
  have htop : ThreeSections (⊤ : Subgroup ↥A) :=
    a6s_threeSections_of_injective A.subtype A.subtype_injective
      (by rw [Subgroup.map_top, Subgroup.range_subtype]) h
  intro H _ T _ hs
  have key := htop H T le_top hs
  rwa [← Subgroup.index_eq_card] at key

theorem a6s_not_threeSections_of_surj {G : Type*} [Group G] {L : Subgroup G} {Q : Type*}
    [Group Q] (π : ↥L →* Q) (hπ : Function.Surjective π) (hq : Open.IsQuasisimple Q)
    (h3 : 3 ∣ Nat.card Q) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center Q)) : ¬ ThreeSections L := by
  intro h
  let ψ : ↥L →* Q ⧸ Subgroup.center Q := (QuotientGroup.mk' (Subgroup.center Q)).comp π
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hπ
  let e : ↥L ⧸ ψ.ker ≃* Q ⧸ Subgroup.center Q := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2
  have hs' : IsSimpleGroup (↥L ⧸ ψ.ker) := MulEquiv.isSimpleGroup e
  have key := h L ψ.ker le_rfl hs'
  rw [Nat.card_congr e.toEquiv] at key
  have hperf : Group.IsPerfect Q := ⟨hq.1⟩
  have hcard : 3 ∣ Nat.card (Q ⧸ Subgroup.center Q) := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q)
    rw [hmul] at h3
    exact ((Nat.Prime.dvd_mul Nat.prime_three).mp h3).resolve_right hZ
  rcases key with h1 | h1
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc := isCyclic_of_prime_card h1
    exact Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q) inferInstance
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h1 hcard

theorem a6s_not_threeSections_of_block {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hr : 2 ≤ Open.pRank 3 L)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) : ¬ ThreeSections L := by
  let π : ↥L →* ↥(barM M L) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hL.le)).codRestrict
      (barM M L) fun x => mem_barM_iff'.mpr ⟨Subgroup.inclusion hL.le x, x.2, rfl⟩
  have hπ : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨m, hmL, hmy⟩ := mem_barM_iff'.mp hy
    exact ⟨⟨(m : G), hmL⟩, Subtype.ext hmy⟩
  have hr' : Open.pRank 3 (barM M L) = Open.pRank 3 L :=
    pRank_barM_eq Nat.prime_three (by norm_num) M L hL.le
  have h3 : 3 ∣ Nat.card ↥(barM M L) := three_dvd_card_of_two_le_pRank (hr' ▸ hr)
  exact a6s_not_threeSections_of_surj π hπ hL.component.2.2 h3 hZ

section Pair

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem PairCtx3.normalizer_char_sections (hctx : PairCtx3 P M A H R)
    (hgl : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable) {T C : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTM : ¬ Subgroup.normalizer (T : Set G) ≤ M) (hC : C ≠ ⊥)
    (hCT : C ≤ T) (hNC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G)) :
    Open.pRank 3 (Subgroup.normalizer (C : Set G) ⊓ M) ≤ 2 ∧
    (2 ≤ Open.pRank 3 (Subgroup.normalizer (C : Set G) ⊓ M) →
      ThreeSections (Subgroup.normalizer (C : Set G) ⊓ M)) := by
  have hC2 : IsPGroup 2 C := by
    intro g
    obtain ⟨k, hk⟩ := hT2 ⟨(g : G), hCT g.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hNCM : ¬ Subgroup.normalizer (C : Set G) ≤ M := fun hle => hTM (hNC.trans hle)
  refine ⟨D2Escape.pRank_normalizer_inf_le_two3 hctx.esc hctx.d1At hC hC2 hNCM, fun h2 => ?_⟩
  have hNtop : Subgroup.normalizer (C : Set G) ≠ ⊤ :=
    normalizer_ne_top_of_twoGroup hctx.setting.simple hctx.setting.nonab hC hC2
  have hp : 3 ∣ Nat.card (Subgroup.normalizer (C : Set G) ⊓ M : Subgroup G) :=
    three_dvd_card_of_two_le_pRank h2
  have hstr := glbStronglyEmbedded_subgroupOf_inf hctx.strong hNCM hp
  have hK : CFSG.IsKGroup ↥(Subgroup.normalizer (C : Set G)) :=
    L34FF.isKGroup_of_catalogSimpleSections_finite
      (catalogSimpleSections_of_isKProper hctx.setting.kProper _ hNtop)
  have hrk : 2 ≤ Open.pRank 3
      ((Subgroup.normalizer (C : Set G) ⊓ M).subgroupOf (Subgroup.normalizer (C : Set G))) := by
    rw [CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three _ _
      inf_le_left]
    exact h2
  have hts := hgl _ hK _ hstr hrk
  have := a6s_threeSections_map (Subgroup.normalizer (C : Set G)).subtype hts
  rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_left] at this

end Pair

@[expose] def GNBoundS {X : Type} [Group X] [Finite X] (T : Subgroup X) : Prop :=
  ∀ T' : Subgroup X, T' ≠ ⊥ → T' ≤ T → (T'.subgroupOf T).Characteristic →
    Open.pRank 3 (Subgroup.normalizer (T' : Set X)) ≤ 2 ∧
    (2 ≤ Open.pRank 3 (Subgroup.normalizer (T' : Set X)) →
      ThreeSections (Subgroup.normalizer (T' : Set X)))

section Pair

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem gnBoundS_of_pair3 (hctx : PairCtx3 P M A H R)
    (hgl : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable) {X₀ T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTX : T ≤ X₀) (hXM : X₀ ≤ M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) : GNBoundS (T.subgroupOf X₀) := by
  intro T' hT'b hT'T hchar
  set T'' : Subgroup G := T'.map X₀.subtype with hT''
  have hT''T : T'' ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hT'T hx)
  have hT''b : T'' ≠ ⊥ := by
    intro h
    apply hT'b
    have hle := (Subgroup.map_eq_bot_iff _).mp h
    have hk : X₀.subtype.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr X₀.subtype_injective
    rw [hk] at hle
    exact le_bot_iff.mp hle
  have hchar'' : (T''.subgroupOf T).Characteristic := by
    let e := Subgroup.subgroupOfEquivOfLe hTX
    have h1 : ((T'.subgroupOf (T.subgroupOf X₀)).map e.toMonoidHom).Characteristic := by
      have := hchar
      exact characteristic_map_mulEquiv e
    have h2 : (T'.subgroupOf (T.subgroupOf X₀)).map e.toMonoidHom = T''.subgroupOf T := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine Subgroup.mem_subgroupOf.mpr ⟨(x : ↥X₀), Subgroup.mem_subgroupOf.mp hx, rfl⟩
      · intro hy
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_subgroupOf.mp hy
        refine ⟨⟨x, Subgroup.mem_subgroupOf.mpr (by
          have : (x : G) = (y : G) := hxy
          rw [this]; exact y.2)⟩, Subgroup.mem_subgroupOf.mpr hx, Subtype.ext hxy⟩
    rwa [h2] at h1
  have hNC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (T'' : Set G) := by
    have := @CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic G _ T
      (T''.subgroupOf T) hchar''
    rwa [Subgroup.map_subgroupOf_eq_of_le hT''T] at this
  obtain ⟨hr, hp⟩ := hctx.normalizer_char_sections hgl hT2 hNT hT''b hT''T hNC
  have hmap : (Subgroup.normalizer (T' : Set ↥X₀)).map X₀.subtype ≤
      Subgroup.normalizer (T'' : Set G) ⊓ M := by
    rintro _ ⟨x, hx, rfl⟩
    have hx : x ∈ Subgroup.normalizer (T' : Set ↥X₀) := hx
    refine ⟨?_, hXM x.2⟩
    show X₀.subtype x ∈ Subgroup.normalizer (T'' : Set G)
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨x * y' * x⁻¹, (hx y').mp hy', rfl⟩
    · rintro hy'
      obtain ⟨z, hz, hzy⟩ := hy'
      have hzy' : (z : G) = (x : G) * y * (x : G)⁻¹ := hzy
      have hz' : (x⁻¹ * z * x : ↥X₀) ∈ T' := by
        refine (hx (x⁻¹ * z * x)).mpr ?_
        have e1 : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
        rw [e1]
        exact hz
      refine ⟨x⁻¹ * z * x, hz', ?_⟩
      show (((x⁻¹ * z * x : ↥X₀)) : G) = y
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzy']
      group
  have hrk : Open.pRank 3 (Subgroup.normalizer (T' : Set ↥X₀)) ≤
      Open.pRank 3 (Subgroup.normalizer (T'' : Set G) ⊓ M) := by
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three
      X₀.subtype X₀.subtype_injective]
    exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hmap
  exact ⟨hrk.trans hr, fun h2 =>
    a6s_threeSections_of_injective X₀.subtype X₀.subtype_injective hmap (hp (h2.trans hrk))⟩

theorem a6s_false_of_le_gnC_one {X₀ T L : Subgroup G} (hTX : T ≤ X₀) (hT2 : IsPGroup 2 T)
    (hT0 : T ≠ ⊥) (hD : GNBoundS (T.subgroupOf X₀)) (hLX : L ≤ X₀)
    (hr : 2 ≤ Open.pRank 3 L) (hL : ¬ ThreeSections L)
    (hle : L.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀)) : False := by
  have hTh2 : IsPGroup 2 ↥(T.subgroupOf X₀) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hTh0 : T.subgroupOf X₀ ≠ ⊥ := by
    intro h
    apply hT0
    have := Subgroup.map_subgroupOf_eq_of_le hTX
    rw [h, Subgroup.map_bot] at this
    exact this.symm
  set Z : Subgroup ↥X₀ := Quasithin.omegaOneCenterOf (T.subgroupOf X₀) with hZ
  have hZb : Z ≠ ⊥ := QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hTh2 hTh0
  have hZT : Z ≤ T.subgroupOf X₀ := QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hZc : (Z.subgroupOf (T.subgroupOf X₀)).Characteristic :=
    QuasithinUnique.Setup.characteristic_omegaOneCenterOf _
  obtain ⟨-, hpf⟩ := hD Z hZb hZT hZc
  have hnorm : ∀ l ∈ gnC (T.subgroupOf X₀), l ∈ Subgroup.normalizer (Z : Set ↥X₀) := by
    intro l hl
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzV : z ∈ gnV (T.subgroupOf X₀) := Subgroup.subset_normalClosure hz
    exact Subgroup.mem_centralizer_iff.mp hl z hzV
  have hsup : L.subgroupOf X₀ ≤ Subgroup.normalizer (Z : Set ↥X₀) := fun l hl => hnorm l (hle hl)
  have hrk2 : 2 ≤ Open.pRank 3 (Subgroup.normalizer (Z : Set ↥X₀)) := by
    have h5 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hsup
    have h6 : Open.pRank 3 (L.subgroupOf X₀) = Open.pRank 3 L := by
      rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three X₀.subtype
        X₀.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hLX]
    omega
  have hts := a6s_threeSections_map X₀.subtype (a6s_threeSections_mono hsup (hpf hrk2))
  rw [Subgroup.map_subgroupOf_eq_of_le hLX] at hts
  exact hL hts

end Pair

theorem isOneImageList_of_gnS (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverOne)
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    (hC : ¬ 3 ∣ Nat.card (gnC T)) (hD : GNBoundS T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hcl : IsClassicalOverTwo (↥L ⧸ Subgroup.center ↥L)) (h3 : 3 ≤ Open.pRank 3 L)
    (hS : IsSylowTwoOf (gnImg T T ⊓ L) L) :
    IsOneImageList (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨T₁, T₂, hpair, hpar, -⟩ := hGN X T hX (hX.ne_bot_of_isComponentOf hL)
  have hT₁ : T₁ ≤ T := hpair.le_center.trans (QuasithinUnique.Setup.omegaOneCenterOf_le T)
  have hbound : ∀ Ti : Subgroup X, Ti ≠ ⊥ → Ti ≤ T → (Ti.subgroupOf T).Characteristic →
      Open.pRank 3 (gnA T Ti L) ≤ 2 ∧
        (Open.pRank 3 (gnA T Ti L) = 2 → CFSG.HallHigman.IsPSolvable 3 ↥(gnA T Ti L)) := by
    intro Ti h1 h2 h3'
    obtain ⟨hr, hp⟩ := hD Ti h1 h2 h3'
    have hle : Open.pRank 3 (gnA T Ti L) ≤ Open.pRank 3 (Subgroup.normalizer (Ti : Set X)) :=
      (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left).trans (pRank_gnImg_le T hC _)
    refine ⟨hle.trans hr, fun h2' => ?_⟩
    have h2le : 2 ≤ Open.pRank 3 (Subgroup.normalizer (Ti : Set X)) := h2' ▸ hle
    exact a6s_isPSolvable_of_threeSections
      (a6s_threeSections_mono inf_le_left
        (a6s_threeSections_map (QuotientGroup.mk' (gnC T)) (hp h2le)))
  obtain ⟨b₁, s₁⟩ := hbound T₁ hpair.ne_bot₁ hT₁ hpair.char₁
  obtain ⟨b₂, s₂⟩ := hbound T₂ hpair.ne_bot₂ hpair.le₂ hpair.char₂
  refine hCov (X ⧸ gnC T) L (gnImg T T ⊓ L) (gnA T T₁ L) (gnA T T₂ L) hL.2.2 hcl h3 hS ?_
    ⟨b₁, s₁⟩ ⟨b₂, s₂⟩
  intro P hP
  rcases hpar L hL (isChevTwo_of_classicalOverTwo hcl) P hP with h | h
  · left
    refine le_inf ?_ ((pElementSubgroup_le P).trans hP.1)
    exact h.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _))
  · right
    exact le_inf h ((pElementSubgroup_le P).trans hP.1)

end CFSG.LocalAnalysis.RankThreeTheoremC
