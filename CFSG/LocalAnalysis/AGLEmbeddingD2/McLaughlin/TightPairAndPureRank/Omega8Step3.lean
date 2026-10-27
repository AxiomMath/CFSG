module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Lift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8GN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TROne
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRMoveGen
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

@[expose] def KFactOmega8Borel : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Lb S : Subgroup X), IsOmegaEightPlus ↥Lb →
    IsSylowTwoOf S Lb → Lb ⊓ Subgroup.normalizer (S : Set X) ≤ S

theorem le_normalizer_of_characteristic' {X : Type} [Group X] {T K : Subgroup X} (hKT : K ≤ T)
    (hc : (K.subgroupOf T).Characteristic) : T ≤ Subgroup.normalizer (K : Set X) := by
  have key : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K := by
    intro t ht k hk
    have h := Subgroup.characteristic_iff_le_comap.mp hc (MulAut.conj (⟨t, ht⟩ : ↥T))
      (show (⟨k, hKT hk⟩ : ↥T) ∈ K.subgroupOf T from hk)
    have h' : (MulAut.conj (⟨t, ht⟩ : ↥T)) ⟨k, hKT hk⟩ ∈ K.subgroupOf T := h
    simpa using Subgroup.mem_subgroupOf.mp h'
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key t ht y hy, fun hy => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hy
  simpa [mul_assoc] using this

theorem isOmegaEightPlus_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsOmegaEightPlus Y) : IsOmegaEightPlus Y' := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.symm.trans f⟩⟩


section Transport

variable {G : Type} [Group G]

theorem mem_normalizer_iff_map {X₀ : Subgroup G} (K : Subgroup ↥X₀) (x : ↥X₀) :
    x ∈ Subgroup.normalizer (K : Set ↥X₀) ↔
      (x : G) ∈ Subgroup.normalizer ((K.map X₀.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨x * y' * x⁻¹, (hx y').mp hy', by simp⟩
    · rintro ⟨z, hz, hzy⟩
      have hzy' : (z : G) = (x : G) * y * (x : G)⁻¹ := hzy
      have hz' : (x⁻¹ * z * x : ↥X₀) ∈ K := by
        refine (hx (x⁻¹ * z * x)).mpr ?_
        have e1 : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
        rw [e1]
        exact hz
      refine ⟨x⁻¹ * z * x, hz', ?_⟩
      show (((x⁻¹ * z * x : ↥X₀)) : G) = y
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzy']
      group
  · intro hx y
    constructor
    · intro hy
      have h1 := (hx (y : G)).mp ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := h1
      have : z = x * y * x⁻¹ := Subtype.ext (by simpa using hzy)
      rwa [← this]
    · intro hy
      have h1 := (hx (y : G)).mpr (by
        refine ⟨x * y * x⁻¹, hy, ?_⟩
        simp)
      obtain ⟨z, hz, hzy⟩ := h1
      have : z = y := Subtype.ext hzy
      rwa [← this]

theorem map_normalizer_eq_inf {X₀ : Subgroup G} (K : Subgroup ↥X₀) :
    (Subgroup.normalizer (K : Set ↥X₀)).map X₀.subtype =
      Subgroup.normalizer ((K.map X₀.subtype : Subgroup G) : Set G) ⊓ X₀ := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(mem_normalizer_iff_map K x).mp hx, x.2⟩
  · rintro ⟨hz, hzX⟩
    exact ⟨⟨z, hzX⟩, (mem_normalizer_iff_map K ⟨z, hzX⟩).mpr hz, rfl⟩

theorem char_map_subtype {T X₀ : Subgroup G} (hTX : T ≤ X₀) {Ti : Subgroup ↥X₀} (hb : Ti ≠ ⊥)
    (hle : Ti ≤ T.subgroupOf X₀) (hc : (Ti.subgroupOf (T.subgroupOf X₀)).Characteristic) :
    Ti.map X₀.subtype ≠ ⊥ ∧ Ti.map X₀.subtype ≤ T ∧
      ((Ti.map X₀.subtype).subgroupOf T).Characteristic := by
  set T'' : Subgroup G := Ti.map X₀.subtype with hT''
  have hT''T : T'' ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hle hx)
  have hT''b : T'' ≠ ⊥ := by
    intro h
    apply hb
    have hle' := (Subgroup.map_eq_bot_iff _).mp h
    have hk : X₀.subtype.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr X₀.subtype_injective
    rw [hk] at hle'
    exact le_bot_iff.mp hle'
  refine ⟨hT''b, hT''T, ?_⟩
  let e := Subgroup.subgroupOfEquivOfLe hTX
  have h1 : ((Ti.subgroupOf (T.subgroupOf X₀)).map e.toMonoidHom).Characteristic := by
    have := hc
    exact characteristic_map_mulEquiv e
  have h2 : (Ti.subgroupOf (T.subgroupOf X₀)).map e.toMonoidHom = T''.subgroupOf T := by
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

end Transport

variable {G : Type} [Group G] [Finite G]

theorem trJ_gnC_le_pCore {M S L T X₀ J : Subgroup G} (hL : IsWeakSBlock M S L)
    (hXM : X₀ ≤ M) (hTX : T ≤ X₀) (hQT : pCoreOf 2 M ≤ T) (hLX : L ≤ X₀)
    (hbJ : barM M J = barM M L)
    (hZ1 : Subgroup.center ↥(barM M L) = ⊥)
    (hmove : ¬ L.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀))
    (x : ↥X₀) (hxJ : (x : G) ∈ J)
    (hxC : x ∈ gnC (T.subgroupOf X₀)) : (x : G) ∈ pCoreOf 2 M := by
  set C : Subgroup ↥X₀ := gnC (T.subgroupOf X₀) with hC
  have hq : Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  have hsimple : IsSimpleGroup ↥(barM M L) := by
    have := hq.2
    exact MulEquiv.isSimpleGroup
      ((QuotientGroup.quotientMulEquivOfEq hZ1).trans (QuotientGroup.quotientBot)).symm
  set ρ := rhoX M X₀ hXM with hρ
  have hLb : barM M L = (L.subgroupOf X₀).map ρ := (map_subgroupOf_rhoX hXM hLX).symm
  have hker : ρ.ker ≤ C := rhoX_ker_le hXM hTX hQT
  have hρx : ρ x ∈ barM M L := by
    rw [← hbJ]
    exact mem_barM_iff'.mpr ⟨⟨(x : G), hXM x.2⟩, hxJ, rfl⟩
  set W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := barM M L ⊓ C.map ρ with hW
  have hWn : (W.subgroupOf (barM M L)).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 ha.1) (Subgroup.inv_mem _ g.2), ?_⟩
    obtain ⟨c, hc, hca⟩ := ha.2
    have hg : (g : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ (L.subgroupOf X₀).map ρ := hLb ▸ g.2
    obtain ⟨y, hy, hyg⟩ := hg
    refine ⟨y * c * y⁻¹, (inferInstance : C.Normal).conj_mem c hc y, ?_⟩
    simp [map_mul, map_inv, hca, hyg]⟩
  haveI := hWn
  rcases hsimple.eq_bot_or_eq_top_of_normal (W.subgroupOf (barM M L)) with h | h
  · have hmem : (⟨ρ x, hρx⟩ : ↥(barM M L)) ∈ W.subgroupOf (barM M L) :=
      Subgroup.mem_subgroupOf.mpr ⟨hρx, ⟨x, hxC, rfl⟩⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : ρ x = 1 := congrArg Subtype.val hmem
    exact (mk_eq_one_iff_coe_mem_pCoreOf ⟨(x : G), hXM x.2⟩).mp h1
  · exfalso
    apply hmove
    intro l hl
    have hlb : ρ l ∈ barM M L := hLb ▸ ⟨l, hl, rfl⟩
    have hmem : (⟨ρ l, hlb⟩ : ↥(barM M L)) ∈ W.subgroupOf (barM M L) := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hcl⟩ := (Subgroup.mem_subgroupOf.mp hmem).2
    have hmk : c⁻¹ * l ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcl, inv_mul_cancel]
    have := C.mul_mem hc (hker hmk)
    simpa using this


theorem omega8_exists_Y (hD2 : D1NoXBlock) (hGN : GlaubermanNilesInput)
    (hCov : KFactParabolicCoverOmega8) (hK : KFactStrongThreeSolv)
    (hP8 : KFactOmega8Parabolic) (hBor : KFactOmega8Borel)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h2 : NineThreeTwo M (pCoreOf 2 H) L) (hr : 3 ≤ Open.pRank 3 L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hZ1 : Subgroup.center ↥(barM M L) = ⊥) (hΩ : IsOmegaEightPlus ↥(barM M L))
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hQT : pCoreOf 2 M ≤ T)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ Ti : Subgroup G, Ti ≠ ⊥ ∧ Ti ≤ T ∧ (Ti.subgroupOf T).Characteristic ∧
      ∃ Y' : Subgroup G, Y' ≤ Subgroup.normalizer (Ti : Set G) ⊓ M ∧
        IsSubnormal Y' (Subgroup.normalizer (Ti : Set G) ⊓ M) ∧
        IsLThreeTwo (↥Y' ⧸ CFSG.pCore 2 ↥Y') := by
  have hpr := hctx.pair
  have hLF' := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hLF'
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hsolv : BlockPLThreeSolv M (pCoreOf 2 H) L :=
    d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair hctx.strong
      hctx.perf L hL
  have hZ' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
    rwa [← card_inf_centralizer_eq_card_center]
  have hNH := hpr.normalizer_twoCore_H
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hT0 : T ≠ ⊥ := by
    intro h
    apply CFSG.PreuniquenessRankFour.Helpers.twoLocal_pCoreOf_ne_bot hpr.maxTwoLocal_M.1
    exact eq_bot_iff.mpr (hQT.trans h.le)
  have hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L ∨ barM M L' = barM M L := fun L' hL' => Or.inl (hk1 L' hL')
  have hN := normalizes_trJ hL hL hk2 hTM
    (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hSylT := isSylowTwoOf_trX_one hL hT2 hN hQT
    (isSylowTwoOf_barM_inf_of_parabolic hL hT hNH h2)
  have hXM : trX M L L T ≤ M := trX_le hL.le hL.le hTM
  have hTX : T ≤ trX M L L T := le_trX_right
  have hLX : L ≤ trX M L L T := le_trJ_left.trans le_trX_left
  have hD := gnBound_of_pair hctx hK hT2 hTX hXM hNT
  have h3L : 3 ∣ Nat.card L := by
    obtain ⟨E0, hE0L, -, hE0c⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) L
    have h1 : 3 ∣ Nat.card E0 := by
      rw [hE0c]
      exact dvd_pow_self 3 (by omega)
    exact h1.trans (Subgroup.card_dvd_of_le hE0L)
  have hmove : ¬ L.subgroupOf (trX M L L T) ≤ gnC (T.subgroupOf (trX M L L T)) := fun hle =>
    false_of_le_gnC_one hTX hT2 hT0 hD hLX hL.perfect h3L (by omega) hle
  have hGNS := gnSetting_trX hX hpr.maxTwoLocal_M hpr.isKGroup.1 hpr.charTwo.1 hL hL hT2 hN hTM
    hSylT
  have hC := not_three_dvd_gnC_one hL hk1 hT2 hTH hTM hQT hZ' hmove
  have hcomp := blockStar_isComponent hXM hTX hQT hL hLX hmove
  obtain ⟨-, hZdvd, ⟨e⟩, -⟩ := blockStar_facts hXM hTX hQT hL hLX hmove
  have hsyl := blockStar_sylow hXM hTX hL hLX hT2 hSylT
  set X₀ : Subgroup G := trX M L L T with hX₀
  set T₀ : Subgroup ↥X₀ := T.subgroupOf X₀ with hT₀
  set Ls : Subgroup (↥X₀ ⧸ gnC T₀) := gnImg T₀ (L.subgroupOf X₀) with hLs
  have hZs : Subgroup.center ↥Ls = ⊥ := by
    have h1 : Nat.card (Subgroup.center ↥(barM M L)) = 1 := by
      rw [hZ1]
      exact Subgroup.card_bot
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (h1 ▸ hZdvd))
  have hΩq : IsOmegaEightPlus (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    isOmegaEightPlus_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ1).trans (QuotientGroup.quotientBot)).symm hΩ
  have hΩs' : IsOmegaEightPlus (↥Ls ⧸ Subgroup.center ↥Ls) := isOmegaEightPlus_of_mulEquiv e hΩq
  have hΩs : IsOmegaEightPlus ↥Ls :=
    isOmegaEightPlus_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZs).trans (QuotientGroup.quotientBot)) hΩs'
  obtain ⟨Ti, hTiB, hTiT, hTiC, Js, hJsA, hJsp, hJs3⟩ :=
    exists_perfect_of_gn hGN hCov hGNS hC (fun T' h1 h2 h3 => (hD T' h1 h2 h3).1) hcomp hΩs' hΩs
      hsyl
  set f : ↥X₀ →* ↥X₀ ⧸ gnC T₀ := QuotientGroup.mk' (gnC T₀) with hf
  set N : Subgroup ↥X₀ := Subgroup.normalizer (Ti : Set ↥X₀) with hN₀
  set Ai : Subgroup (↥X₀ ⧸ gnC T₀) := gnA T₀ Ti Ls with hAi
  have hTiN : T₀ ≤ N :=
    le_normalizer_of_characteristic' hTiT hTiC
  have hAiN : Ai ≤ N.map f := inf_le_left
  have hAiL : Ai ≤ Ls := inf_le_right
  obtain ⟨D₁, hD₁N, hD₁p, hD₁3⟩ := exists_perfect_of_le_map f (hJsA.trans hAiN) hJsp hJs3
  obtain ⟨hNr2, hNp⟩ := hD Ti hTiB hTiT hTiC
  have hNr : Open.pRank 3 N ≤ 1 := by
    by_contra hlt
    push Not at hlt
    exact hNp hlt D₁ hD₁N hD₁p hD₁3
  have hAr : Open.pRank 3 Ai ≤ 1 :=
    ((CFSG.SectionRank.pRank_mono (by norm_num) hAiN).trans (pRank_gnImg_le T₀ hC N)).trans hNr
  have hpar : IsParabolicTwo Ls Ai := by
    refine ⟨hAiL, gnImg T₀ T₀ ⊓ Ls, hsyl, fun x hx => ?_⟩
    have hxS := hBor _ Ls _ hΩs hsyl hx
    exact ⟨Subgroup.map_mono hTiN hxS.1, hxS.2⟩
  obtain ⟨Y, hYA, hYn, hYL⟩ := (hP8 _ Ls Ai hΩs hpar).2.2.1 hAr ⟨Js, hJsA, hJsp, hJs3⟩
  have hQX : pCoreOf 2 M ≤ X₀ := hQT.trans hTX
  have hJM : trJ M L L ≤ M := sup_le (sup_le hL.le hL.le) (pCoreOf_le 2 M)
  have hJX : trJ M L L ≤ X₀ := le_trX_left
  have hbJ : barM M (trJ M L L) = barM M L := by
    rw [trJ, barM_sup_eq (sup_le hL.le hL.le) (pCoreOf_le 2 M), barM_sup_eq hL.le hL.le,
      barM_pCoreOf_eq_bot, sup_bot_eq, sup_idem]
  set Jg : Subgroup ↥X₀ := (trJ M L L).subgroupOf X₀ with hJg
  have hJgN : Jg.Normal := ⟨fun x hx g => by
    rw [hJg, Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨t, ht, j, hj, hgtj⟩ := exists_mul_of_mem_trX hN g.2
    have h1 : (g : G) * (x : G) * (g : G)⁻¹ = t * (j * (x : G) * j⁻¹) * t⁻¹ := by
      rw [hgtj]; group
    show ((g * x * g⁻¹ : ↥X₀) : G) ∈ trJ M L L
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1]
    exact hN t ht _ ((trJ M L L).mul_mem ((trJ M L L).mul_mem hj hx) ((trJ M L L).inv_mem hj))⟩
  have hJgeq : Jg = L.subgroupOf X₀ ⊔ (pCoreOf 2 M).subgroupOf X₀ := by
    apply Subgroup.map_injective X₀.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLX,
      Subgroup.map_subgroupOf_eq_of_le hQX, hJg, Subgroup.map_subgroupOf_eq_of_le hJX, trJ,
      sup_idem]
  have hQf : (pCoreOf 2 M).subgroupOf X₀ ≤ f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    exact pCoreOf_subgroupOf_le_gnC hXM hTX hQT
  have hJgf : Jg.map f = Ls := by
    rw [hJgeq, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr hQf, sup_bot_eq]
    rfl
  have hJ2 : ∀ x ∈ Jg, x ∈ f.ker → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hxJ hxC
    have hxJ' : (x : G) ∈ trJ M L L := Subgroup.mem_subgroupOf.mp hxJ
    have hxC' : x ∈ gnC T₀ := by rwa [hf, QuotientGroup.ker_mk'] at hxC
    have hxQ := trJ_gnC_le_pCore hL hXM hTX hQT hLX hbJ hZ1 hmove x hxJ' hxC'
    obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 M ⟨(x : G), hxQ⟩
    exact ⟨a, Subtype.ext (by simpa using congrArg Subtype.val ha)⟩
  have hcker : ¬ 3 ∣ Nat.card f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    exact hC
  obtain ⟨hnorm, hY₂⟩ := lift_isLThreeTwo f hcker Jg N hJgN hJ2 Y (hYA.trans hAiN)
    (by rw [hJgf]; exact hYA.trans hAiL) (by rw [hJgf]; exact hYn) hYL
  obtain ⟨hTiG_b, hTiG_T, hTiG_c⟩ := char_map_subtype hTX hTiB hTiT hTiC
  set Y₂ : Subgroup ↥X₀ := N ⊓ Jg ⊓ Y.comap f with hY₂def
  set N₁ : Subgroup ↥X₀ := N ⊓ Jg with hN₁
  have hY₂N₁ : Y₂ ≤ N₁ := fun x hx => hx.1
  have hN₁map : N₁.map X₀.subtype =
      Subgroup.normalizer ((Ti.map X₀.subtype : Subgroup G) : Set G) ⊓ trJ M L L := by
    rw [hN₁, Subgroup.map_inf _ _ X₀.subtype X₀.subtype_injective, hN₀, map_normalizer_eq_inf, hJg,
      Subgroup.map_subgroupOf_eq_of_le hJX, inf_assoc, inf_eq_right.mpr hJX]
  refine ⟨Ti.map X₀.subtype, hTiG_b, hTiG_T, hTiG_c, Y₂.map X₀.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨(mem_normalizer_iff_map Ti y).mp hy.1.1, hXM y.2⟩
  ·
    have hsubJ := isSubnormal_inf' (isSubnormal_trJ hL hL) (Subgroup.normalizer
      ((Ti.map X₀.subtype : Subgroup G) : Set G))
    rw [inf_comm (trJ M L L), inf_comm M, ← hN₁map] at hsubJ
    refine IsSubnormal.step (Subgroup.map_mono hY₂N₁) ?_ hsubJ
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨n, hn, hng⟩ : (g : G) ∈ N₁.map X₀.subtype := g.2
    have hn1 : n ∈ N₁ := hn
    have hyn : y ∈ N₁ := hY₂N₁ hy
    have := hnorm.conj_mem (⟨y, hyn⟩ : ↥N₁) (Subgroup.mem_subgroupOf.mpr hy) ⟨n, hn1⟩
    have h3 := Subgroup.mem_subgroupOf.mp this
    refine ⟨n * y * n⁻¹, h3, ?_⟩
    have hyx' : (y : G) = (x : G) := hyx
    have hng' : (n : G) = (g : G) := hng
    show (((n * y * n⁻¹ : ↥X₀)) : G) = (g : G) * (x : G) * (g : G)⁻¹
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hyx', hng']
  ·
    let e : ↥Y₂ ≃* ↥(Y₂.map X₀.subtype) := Y₂.equivMapOfInjective X₀.subtype X₀.subtype_injective
    have hmap : (CFSG.pCore 2 ↥Y₂).map e.toMonoidHom = CFSG.pCore 2 ↥(Y₂.map X₀.subtype) :=
      CFSG.pCore_map_iso 2 e
    exact IsLThreeTwo.of_mulEquiv (QuotientGroup.congr _ _ e hmap) hY₂


section Final

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSubnormal_subgroupOf_chain {A B : Subgroup G} (h : IsSubnormal A B) (K : Subgroup G) :
    IsSubnormal (A.subgroupOf K) (B.subgroupOf K) :=
  h.comap K.subtype

theorem isLThreeTwo_commutator_top {S : Type} [Group S] (h : IsLThreeTwo S) :
    ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
  have hs := isLThreeTwo_simple h
  have hn : (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆).Normal := inferInstance
  rcases hs.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) with h0 | h0
  · exfalso
    have hcomm : ∀ a b : S, a * b = b * a := by
      intro a b
      have h1 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    letI : CommGroup S := { ‹Group S› with mul_comm := hcomm }
    have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [isLThreeTwo_card_eq h]; norm_num)
    have := IsSimpleGroup.prime_card (α := S)
    rw [isLThreeTwo_card_eq h] at this
    exact absurd this (by norm_num)
  · exact h0

theorem false_of_omega8_of_sylowM (hD2 : D1NoXBlock) (hGN : GlaubermanNilesInput)
    (hCov : KFactParabolicCoverOmega8) (hK : KFactStrongThreeSolv)
    (hP8 : KFactOmega8Parabolic) (hBor : KFactOmega8Borel) (hOdd : KFactLThreeTwoOddIndex)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    (hev : PairEvenIndex M H)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h2 : NineThreeTwo M (pCoreOf 2 H) L) (hr : 3 ≤ Open.pRank 3 L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hZ1 : Subgroup.center ↥(barM M L) = ⊥) (hΩ : IsOmegaEightPlus ↥(barM M L))
    {T : Subgroup G} (hQT : pCoreOf 2 M ≤ T)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) (hT : IsSylowTwoOf T (H ⊓ M))
    (hTM : IsSylowTwoOf T M) : False := by
  have hT2 : IsPGroup 2 T := hT.2.1
  obtain ⟨Ti, hTiB, hTiT, hTiC, Y', hY'N, hY'sub, hY'L⟩ :=
    omega8_exists_Y hD2 hGN hCov hK hP8 hBor hctx hL hk1 h2 hr hZ hZ1 hΩ hT2 hQT hNT hT
  set NG : Subgroup G := Subgroup.normalizer (Ti : Set G) with hNG
  have hTi2 : IsPGroup 2 Ti :=
    IsPGroup.of_injective hT2 (Subgroup.inclusion hTiT) (Subgroup.inclusion_injective hTiT)
  have hTNG : T ≤ NG := le_normalizer_of_characteristic' hTiT hTiC
  have hNC : Subgroup.normalizer (T : Set G) ≤ NG := by
    have := @CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic G _ T
      (Ti.subgroupOf T) hTiC
    rwa [Subgroup.map_subgroupOf_eq_of_le hTiT] at this
  have hNGM : ¬ NG ≤ M := fun h => hNT (hNC.trans h)
  have hNGtop : NG ≠ ⊤ :=
    normalizer_ne_top_of_twoGroup hctx.glob.simple hctx.glob.nonab hTiB hTi2
  have hKG : Open.IsKGroup ↥NG :=
    isKGroup_of_catalogSimpleSections
      (catalogSimpleSections_of_isKProper hctx.glob.kProper NG hNGtop)
  have hcharNG : CharTwo (⊤ : Subgroup ↥NG) :=
    charTwo_top_of_le (M := NG) (X := NG) (hctx.glob.charTwo NG ⟨Ti, hTiB, hTi2, rfl⟩)
      (pCoreOf_le 2 NG) le_rfl
  have hY'3 : 3 ∣ Nat.card Y' :=
    (isLThreeTwo_three_dvd_card hY'L).trans (Subgroup.card_quotient_dvd_card _)
  have h3NM : 3 ∣ Nat.card (NG ⊓ M : Subgroup G) := hY'3.trans (Subgroup.card_dvd_of_le hY'N)
  have hstr := glbStronglyEmbedded_subgroupOf_inf hctx.strong hNGM h3NM
  obtain ⟨D, -, hDp, hD3⟩ := exists_perfect_of_le_map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y'))
    (N := ⊤) (L' := ⊤)
    (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)])
    (isLThreeTwo_commutator_top hY'L)
    (by rw [Subgroup.card_top]; exact isLThreeTwo_three_dvd_card hY'L)
  have hD'le : D.map Y'.subtype ≤ NG ⊓ M := (Subgroup.map_subtype_le D).trans hY'N
  have hD'p : ⁅D.map Y'.subtype, D.map Y'.subtype⁆ = D.map Y'.subtype := by
    rw [← Subgroup.map_commutator, hDp]
  have hD'3 : 3 ∣ Nat.card (D.map Y'.subtype) := by
    rw [Subgroup.card_map_of_injective Y'.subtype_injective]
    exact hD3
  obtain ⟨-, hnp⟩ := hctx.normalizer_char_facts hK hT2 hNT hTiB hTiT hNC
  have hrk : Open.pRank 3 (NG ⊓ M : Subgroup G) = 1 := by
    have h1 : Open.pRank 3 (NG ⊓ M : Subgroup G) ≤ 1 := by
      by_contra hlt
      push Not at hlt
      exact hnp hlt _ hD'le hD'p hD'3
    have h2' := CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd Nat.prime_three h3NM
    omega
  have hrk' : Open.pRank 3 ((NG ⊓ M).subgroupOf NG) = 1 := by
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three NG.subtype
      NG.subtype_injective, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    exact hrk
  have hY'NG : Y' ≤ NG := hY'N.trans inf_le_left
  have hYle : Y'.subgroupOf NG ≤ (NG ⊓ M).subgroupOf NG := fun x hx => hY'N hx
  have hYL : IsLThreeTwo (↥(Y'.subgroupOf NG) ⧸ CFSG.pCore 2 ↥(Y'.subgroupOf NG)) := by
    let e : ↥(Y'.subgroupOf NG) ≃* ↥Y' := Subgroup.subgroupOfEquivOfLe hY'NG
    have hmap : (CFSG.pCore 2 ↥Y').map e.symm.toMonoidHom =
        CFSG.pCore 2 ↥(Y'.subgroupOf NG) := CFSG.pCore_map_iso 2 e.symm
    exact IsLThreeTwo.of_mulEquiv (QuotientGroup.congr _ _ e.symm hmap) hY'L
  have hodd := hOdd ↥NG hKG hcharNG ((NG ⊓ M).subgroupOf NG) hstr hrk' (Y'.subgroupOf NG) hYle
    (isSubnormal_subgroupOf_chain hY'sub NG) hYL
  have hTNM : T ≤ NG ⊓ M := le_inf hTNG hTM.1
  have hrelM : ¬ 2 ∣ T.relIndex (NG ⊓ M) := fun hd =>
    hTM.2.2 (hd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T (NG ⊓ M) M hTNM inf_le_right)))
  have hrelNG : ¬ 2 ∣ T.relIndex NG := by
    rw [← Subgroup.relIndex_mul_relIndex T (NG ⊓ M) NG hTNM inf_le_left]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
    · exact hrelM h
    · exact hodd h
  have hnH : ¬ IsSylowTwoOf T H := by
    intro hS
    have h1 := Subgroup.relIndex_mul_relIndex T (H ⊓ M) H hT.1 inf_le_left
    exact hS.2.2 (hev.trans (Dvd.intro_left _ h1))
  obtain ⟨W, hTW, hWH, hW2, hne⟩ := normEsc_exists_two_group_strict (hT.1.trans inf_le_left) hT2 hnH
  obtain ⟨w, hwW, hwN, hwT⟩ := normEsc_exists_mem_normalizer_of_two_group hW2 hTW hne
  have hKW : T ⊔ Subgroup.zpowers w ≤ W := sup_le hTW (Subgroup.zpowers_le.mpr hwW)
  have hK2 : IsPGroup 2 (T ⊔ Subgroup.zpowers w : Subgroup G) :=
    hW2.of_injective (Subgroup.inclusion hKW) (Subgroup.inclusion_injective hKW)
  have hKNG : T ⊔ Subgroup.zpowers w ≤ NG := sup_le hTNG (Subgroup.zpowers_le.mpr (hNC hwN))
  have hKT := normEsc_le_of_not_two_dvd_relIndex le_sup_left hKNG hK2 hrelNG
  exact hwT (hKT (Subgroup.mem_sup_right (Subgroup.mem_zpowers w)))

end Final

end CFSG.AGLEmbeddingD2.McLaughlin
