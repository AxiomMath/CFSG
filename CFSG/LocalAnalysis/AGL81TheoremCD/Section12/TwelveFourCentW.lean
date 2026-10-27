module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourInterDPrime
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.AutThreeGroupRankTwo
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolic
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
public import CFSG.GroupTheory.LocalLift.NormalizerQuotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Reduce
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveCtxOrbit
public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
public import CFSG.GroupTheory.CatalogComponent
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {G : Type} [Group G] [Finite G]

theorem isParabolicTwo_top_subgroupOf {X : Type} [Group X] [Finite X] {K J : Subgroup X}
    (h : IsParabolicTwo K J) : IsParabolicTwo (⊤ : Subgroup ↥K) (J.subgroupOf K) := by
  obtain ⟨-, T, hT, hNT⟩ := h
  refine ⟨le_top, T.subgroupOf K, isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT, ?_⟩
  intro x hx
  refine Subgroup.mem_subgroupOf.mpr (hNT ⟨x.2, ?_⟩)
  exact coe_mem_normalizer_of_subgroupOf hT.1 (Subgroup.mem_inf.mp hx).2

private theorem mem_normalizer_of_map_conj_map_eq {H : Type} [Group H] [Finite H]
    {L P : Subgroup H} (hPL : P ≤ L) {x : H} (hx : x ∈ Subgroup.normalizer (L : Set H))
    {y : ↥L}
    (hfix : ((P.subgroupOf L).map (MulAut.conj y).toMonoidHom).map
        (L.normalizerMonoidHom ⟨x, hx⟩).toMonoidHom =
      (P.subgroupOf L).map (MulAut.conj y).toMonoidHom) :
    (y : H)⁻¹ * x * (y : H) ∈ Subgroup.normalizer (P : Set H) := by
  set z : H := (y : H)⁻¹ * x * (y : H) with hz
  have hmap_le : P.map (MulAut.conj z).toMonoidHom ≤ P := by
    rintro r ⟨p, hp, rfl⟩
    have hpL : p ∈ L := hPL hp
    have hmem : (L.normalizerMonoidHom ⟨x, hx⟩) ((MulAut.conj y) ⟨p, hpL⟩) ∈
        (P.subgroupOf L).map (MulAut.conj y).toMonoidHom := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hp)
    obtain ⟨q, hqP, hq⟩ := Subgroup.mem_map.mp hmem
    have h3 : ((MulAut.conj y) q : H) =
        x * ((MulAut.conj y) ⟨p, hpL⟩ : H) * x⁻¹ := by
      calc ((MulAut.conj y) q : H)
          = ((L.normalizerMonoidHom ⟨x, hx⟩) ((MulAut.conj y) ⟨p, hpL⟩) : H) :=
            congrArg (fun w : ↥L => (w : H)) hq
        _ = x * ((MulAut.conj y) ⟨p, hpL⟩ : H) * x⁻¹ :=
            Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hx⟩ _
    have hqeq : z * p * z⁻¹ = (q : H) := by
      rw [hz]
      calc (y : H)⁻¹ * x * (y : H) * p * ((y : H)⁻¹ * x * (y : H))⁻¹
          = (y : H)⁻¹ * (x * ((MulAut.conj y) ⟨p, hpL⟩ : H) * x⁻¹) * (y : H) := by
            simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
            group
        _ = (y : H)⁻¹ * ((MulAut.conj y) q : H) * (y : H) := by rw [h3]
        _ = (q : H) := by
            simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
            group
    have hzp : (MulAut.conj z).toMonoidHom p = (q : H) := by
      simpa [MulAut.conj_apply] using hqeq
    rw [hzp]
    exact hqP
  have hcard : Nat.card P ≤ Nat.card (P.map (MulAut.conj z).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj z).injective).ge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hmap_le hcard)

theorem exists_conj_mem_normalizer_of_not_mem_inner
    (hK5 : KFactOddAutParabolicFixPrime) {M S L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (h2 : NineThreeTwo M S L) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hdP : ¬ d ∣ Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    {x : ↥M ⧸ CFSG.pCore 2 ↥M} (hxd : x ^ d = 1)
    (hx : x ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hout : (barM M L).normalizerMonoidHom ⟨x, hx⟩ ∉ inner ↥(barM M L)) :
    ∃ y ∈ barM M L, y⁻¹ * x * y ∈ Subgroup.normalizer
      (barM M (Subgroup.normalizer (S : Set G) ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  let Hq := ↥M ⧸ CFSG.pCore 2 ↥M
  let Lb : Subgroup Hq := barM M L
  let Pb : Subgroup Hq := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  have hPL : Pb ≤ Lb := barM_mono inf_le_right
  have hcardP : ¬ d ∣ Nat.card ↥(Pb.subgroupOf Lb) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv]
    exact hdP
  let α : MulAut ↥Lb := Lb.normalizerMonoidHom ⟨x, hx⟩
  have hαd : α ^ d = 1 := by
    have hxd' : (⟨x, hx⟩ : Subgroup.normalizer (Lb : Set Hq)) ^ d = 1 := Subtype.ext hxd
    calc α ^ d = Lb.normalizerMonoidHom (⟨x, hx⟩ ^ d) := (map_pow _ _ _).symm
      _ = Lb.normalizerMonoidHom 1 := by rw [hxd']
      _ = 1 := map_one _
  have hpar : IsParabolicTwo (⊤ : Subgroup ↥Lb) (Pb.subgroupOf Lb) :=
    isParabolicTwo_top_subgroupOf h2.2.1
  obtain ⟨y, hy⟩ := hK5 ↥Lb hL.component.2.2 h2.1 (Pb.subgroupOf Lb) hpar d hd hd5 hcardP
    α hαd hout
  exact ⟨(y : Hq), y.2, mem_normalizer_of_map_conj_map_eq hPL hx hy⟩

omit [Finite G] in
theorem le_normalizer_inf_of_barM_le_normalizer {M H L B : Subgroup G}
    (hQH : CFSG.Open.pCoreOf 2 M ≤ H) (hLM : L ≤ M) (hBM : B ≤ M)
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hBP : barM M B ≤
      Subgroup.normalizer (barM M (H ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    B ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := by
  intro b hb
  have hstep : ∀ c ∈ B, ∀ x ∈ H ⊓ L, c * x * c⁻¹ ∈ H ⊓ L := by
    intro c hc x hx
    have hcM : c ∈ M := hBM hc
    have hxM : x ∈ M := hLM hx.2
    have hcxM : c * x * c⁻¹ ∈ M := M.mul_mem (M.mul_mem hcM hxM) (M.inv_mem hcM)
    have hxP : (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨x, hxM⟩ ∈ barM M (H ⊓ L) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    have hcB : (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨c, hcM⟩ ∈ barM M B :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hc)
    have hcx : (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨c, hcM⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨x, hxM⟩ *
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨c, hcM⟩)⁻¹ ∈ barM M (H ⊓ L) :=
      (Subgroup.mem_normalizer_iff.mp (hBP hcB) _).mp hxP
    have hcxP : (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨c * x * c⁻¹, hcxM⟩ ∈
        barM M (H ⊓ L) := by
      have hconj : (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨c * x * c⁻¹, hcxM⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨c, hcM⟩ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨x, hxM⟩ *
            ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨c, hcM⟩)⁻¹ := by
        rw [show (⟨c * x * c⁻¹, hcxM⟩ : ↥M) =
            ⟨c, hcM⟩ * ⟨x, hxM⟩ * ⟨c, hcM⟩⁻¹ from rfl]
        rw [map_mul, map_mul, map_inv]
      rw [hconj]
      exact hcx
    have hcxK : c * x * c⁻¹ ∈ H ⊓ L ⊔ CFSG.Open.pCoreOf 2 M :=
      coe_mem_of_mk_mem_barM (X := H ⊓ L ⊔ CFSG.Open.pCoreOf 2 M) le_sup_right
        (m := ⟨c * x * c⁻¹, hcxM⟩) ((barM_mono le_sup_left) hcxP)
    exact ⟨(sup_le inf_le_left hQH) hcxK, (Subgroup.mem_normalizer_iff.mp (hBL hc) x).mp hx.2⟩
  have hinv : b⁻¹ ∈ B := B.inv_mem hb
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact hstep b hb g hg
  · intro hg
    have h := hstep b⁻¹ hinv (b * g * b⁻¹) hg
    simpa [mul_assoc] using h

theorem two_le_pRank_closure_pair {X : Type} [Group X] [Finite X] {d : ℕ} (hd : d.Prime)
    {a b : X} (hab : a * b = b * a) (ha : a ^ d = 1) (hb : b ^ d = 1) (ha1 : a ≠ 1)
    (hba : b ∉ Subgroup.zpowers a) :
    IsPGroup d (Subgroup.closure ({a, b} : Set X)) ∧
      2 ≤ CFSG.Open.pRank d (Subgroup.closure ({a, b} : Set X)) := by
  have hb1 : b ≠ 1 := fun h1 => hba (h1 ▸ Subgroup.one_mem (Subgroup.zpowers a))
  have horda : orderOf a = d := by
    rcases (Nat.dvd_prime hd).mp (orderOf_dvd_of_pow_eq_one ha) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact h1
  have hordb : orderOf b = d := by
    rcases (Nat.dvd_prime hd).mp (orderOf_dvd_of_pow_eq_one hb) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hb1
    · exact h1
  have hPa : IsPGroup d ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, horda, pow_one])
  have hPb : IsPGroup d ↥(Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordb, pow_one])
  have hcent : a ∈ Subgroup.centralizer (Subgroup.zpowers b : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (show Commute a b from hab) n).eq.symm
  have hsup : IsPGroup d ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) :=
    hPa.to_sup_of_normal_right' hPb
      (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hcent))
  have hclosure : Subgroup.closure ({a, b} : Set X) =
      Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [show ({a, b} : Set X) = {a} ∪ {b} by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union],
      Subgroup.closure_union, Subgroup.zpowers_eq_closure a, Subgroup.zpowers_eq_closure b]
  refine ⟨?_, ?_⟩
  · rw [hclosure]
    exact hsup
  · exact two_le_pRank_of_commute_of_not_mem_zpowers hd horda hb hba
      (show Commute a b from hab) (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

theorem exists_isPGroup_barM_eq {M : Subgroup G} {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    {B' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hB' : IsPGroup d B')
    (h2 : 2 ≤ CFSG.Open.pRank d B') :
    ∃ B : Subgroup G, B ≤ M ∧ IsPGroup d B ∧ barM M B = B' ∧ 2 ≤ CFSG.Open.pRank d B := by
  let π := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have htop : (⊤ : Subgroup ↥M).map π = ⊤ := Subgroup.map_top_of_surjective π hπ
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨R, hR, -, hRmap⟩ :=
    CFSG.LocalLift.exists_isPGroup_map_eq π hπ (le_top : π.ker ≤ ⊤) hB'
      (by rw [htop]; exact le_top)
  refine ⟨R.map M.subtype, Subgroup.map_subtype_le R, hR.map M.subtype, ?_, ?_⟩
  · rw [barM_map_subtype]
    exact hRmap
  · rw [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective d hd M.subtype
      M.subtype_injective R]
    exact CFSG.LocalLift.two_le_pRank_of_map hd2 π hR (by rw [hRmap]; exact h2)

theorem exists_le_normalizer_inf_of_outer {M H L : Subgroup G}
    (hQH : CFSG.Open.pCoreOf 2 M ≤ H) (hL : IsTwoPrimeComponent M L) {d : ℕ} (hd : d.Prime)
    (hd2 : d ≠ 2) {a b : ↥M ⧸ CFSG.pCore 2 ↥M} (hab : a * b = b * a) (ha : a ^ d = 1)
    (hb : b ^ d = 1) (ha1 : a ≠ 1)
    (haL : a ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hbL : b ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hbo : (barM M L).normalizerMonoidHom ⟨b, hbL⟩ ∉ inner ↥(barM M L))
    (hbP : b ∈ Subgroup.normalizer (barM M (H ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ B : Subgroup G, B ≤ M ∧ IsPGroup d B ∧ 2 ≤ CFSG.Open.pRank d B ∧
      B ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := by
  have hba : b ∉ Subgroup.zpowers a := by
    intro hbpow
    have hbC : b ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      (Subgroup.zpowers_le.mpr haL) hbpow
    apply hbo
    have hker : (barM M L).normalizerMonoidHom ⟨b, hbL⟩ = 1 := by
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
      exact Subgroup.mem_subgroupOf.mpr hbC
    rw [hker]
    exact Subgroup.one_mem _
  have hPL : barM M (H ⊓ L) ≤ barM M L :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M inf_le_right)
  have haN : a ∈ Subgroup.normalizer (barM M (H ⊓ L) : Set _) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (fun x hx => hPL hx) haL)
  obtain ⟨hP, h2P⟩ := two_le_pRank_closure_pair hd hab ha hb ha1 hba
  obtain ⟨B, hBM, hB, hbar, hB2⟩ :=
    exists_isPGroup_barM_eq (M := M) hd hd2 hP h2P
  have hBbarN : barM M B ≤ Subgroup.normalizer (barM M L : Set _) := by
    rw [hbar]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.centralizer_le_normalizer _ haL
    · exact hbL
  have hBbarP : barM M B ≤ Subgroup.normalizer (barM M (H ⊓ L) : Set _) := by
    rw [hbar]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact haN
    · exact hbP
  exact ⟨B, hBM, hB, hB2,
    le_normalizer_inf_of_barM_le_normalizer hQH hL.le hBM
      (hL.le_normalizer hBbarN hBM) hBbarP⟩

theorem pRank_three_le_pRank_barM {M L W : Subgroup G} (hLM : L ≤ M) (hWL : W ≤ L)
    (hW : IsPGroup 3 W) : CFSG.Open.pRank 3 W ≤ CFSG.Open.pRank 3 (barM M L) := by
  have hWM : W ≤ M := hWL.trans hLM
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hj]
    exact Nat.Coprime.pow_right j (by norm_num)
  have hquot :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.pRank_map_mk_of_isPGroup
      (p := 3) (H := ↥M) (hp := Nat.prime_three) (O := CFSG.pCore 2 ↥M) hcop
      (T := W.subgroupOf M) hW.comap_subtype
  calc CFSG.Open.pRank 3 W
      = CFSG.Open.pRank 3 (W.subgroupOf M) :=
        (CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf 3 hWM).symm
    _ = CFSG.Open.pRank 3 (barM M W) := hquot.symm
    _ ≤ CFSG.Open.pRank 3 (barM M L) :=
        CFSG.SectionRank.pRank_mono (by norm_num)
          (Subgroup.map_mono (Subgroup.subgroupOf_mono M hWL))

theorem two_le_pRank_inf_centralizer_of_le_normalizer_inf {M H L W B : Subgroup G}
    (hLM : L ≤ M) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hdL : ¬ d ∣ Nat.card (H ⊓ L : Subgroup G)) (hm3L : CFSG.Open.pRank 3 (barM M L) ≤ 2)
    (hW : CFSG.ABGLocalTools.IsSylowOf 3 W (jOne H L)) (hB : IsPGroup d B) (hBM : B ≤ M)
    (hB2 : 2 ≤ CFSG.Open.pRank d B)
    (hBN : B ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G)) :
    2 ≤ CFSG.Open.pRank d (M ⊓ Subgroup.centralizer (W : Set G)) := by
  have hJle : jOne H L ≤ H ⊓ L := (jOne_le_jZero H L).trans (jZero_le H L)
  have hcard : Nat.card (jOne H L : Subgroup G) ∣ Nat.card (H ⊓ L : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (jOne H L) (H ⊓ L)
    rw [inf_eq_left.mpr hJle] at h
    exact ⟨_, h.symm.trans (Nat.mul_comm _ _)⟩
  have hK : ¬ d ∣ Nat.card (jOne H L : Subgroup G) := fun hdiv => hdL (hdiv.trans hcard)
  have hBK : B ≤ Subgroup.normalizer (jOne H L : Set G) :=
    hBN.trans (le_normalizer_jOne H L)
  obtain ⟨k, hkK, hBkW⟩ := exists_map_conj_le_normalizer_of_isSylowOf hd hB hBK hK hW
  have hkL : k ∈ L := (((jOne_le_jZero H L).trans (jZero_le H L)) hkK).2
  have hkM : k ∈ M := hLM hkL
  have hWL : W ≤ L := (hW.le.trans (jOne_le_jZero H L)).trans
    ((jZero_le H L).trans inf_le_right)
  have hWrank : CFSG.Open.pRank 3 W ≤ 2 :=
    (pRank_three_le_pRank_barM hLM hWL hW.isPGroup).trans hm3L
  have hBkC : B.map (MulAut.conj k).toMonoidHom ≤
      Subgroup.centralizer (W : Set G) :=
    le_centralizer_of_le_normalizer_of_pRank_le_two hW.isPGroup hWrank hd hd5
      (hB.map (MulAut.conj k).toMonoidHom) hBkW
  have hBkM : B.map (MulAut.conj k).toMonoidHom ≤ M := by
    rintro x ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using
      M.mul_mem (M.mul_mem hkM (hBM hy)) (M.inv_mem hkM)
  have hBkLe : B.map (MulAut.conj k).toMonoidHom ≤
      M ⊓ Subgroup.centralizer (W : Set G) := le_inf hBkM hBkC
  exact (hB2.trans (CFSG.SectionRank.pRank_le_map hd.one_lt _
    (MulAut.conj k).injective B)).trans (CFSG.SectionRank.pRank_mono hd.one_lt hBkLe)

omit [Finite G] in
private theorem exists_centralizer_elem_of_barM_zpowers_le
    {M L E : Subgroup G} {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hE : CFSG.Open.IsElemAbelian d E) (hEM : E ≤ M) {c : G} (hc : c ∈ E) (hc1 : c ≠ 1)
    (hcL : barM M (Subgroup.zpowers c) ≤
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ a : ↥M ⧸ CFSG.pCore 2 ↥M,
      a = QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c, hEM hc⟩ ∧ a ^ d = 1 ∧ a ≠ 1 ∧
      a ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have : Fact d.Prime := ⟨hd⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c, hEM hc⟩
  have hcdM : (⟨c, hEM hc⟩ : ↥M) ^ d = 1 := Subtype.ext (by simpa using hE.2 c hc)
  have ha : a ^ d = 1 := by rw [← map_pow, hcdM, map_one]
  have hac : a ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    apply hcL
    exact Subgroup.mem_map.mpr ⟨⟨c, hEM hc⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c), rfl⟩
  have ha1 : a ≠ 1 := by
    intro haeq
    have hcQ : c ∈ CFSG.Open.pCoreOf 2 M :=
      coe_mem_pCoreOf_two_of_mk_eq_one ⟨c, hEM hc⟩ haeq
    have hdisj : E ⊓ CFSG.Open.pCoreOf 2 M = ⊥ :=
      (IsPGroup.disjoint_of_ne d 2 hd2 E (CFSG.Open.pCoreOf 2 M) hE.isPGroup
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)).eq_bot
    have hmem : c ∈ E ⊓ CFSG.Open.pCoreOf 2 M := ⟨hc, hcQ⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  exact ⟨a, rfl, ha, ha1, hac⟩

omit [Finite G] in
private theorem notMem_inner_normalizerMonoidHom_conj
    {M L : Subgroup G} {x y : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hx : x ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hy : y ∈ barM M L)
    (hb : y⁻¹ * x * y ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hout : (barM M L).normalizerMonoidHom ⟨x, hx⟩ ∉ inner ↥(barM M L)) :
    (barM M L).normalizerMonoidHom ⟨y⁻¹ * x * y, hb⟩ ∉ inner ↥(barM M L) := by
  intro hβ
  apply hout
  let B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := barM M L
  have hβeq : B.normalizerMonoidHom ⟨y⁻¹ * x * y, hb⟩ =
      (MulAut.conj (⟨y, hy⟩ : B))⁻¹ * B.normalizerMonoidHom ⟨x, hx⟩ *
        MulAut.conj (⟨y, hy⟩ : B) := by
    ext w
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    group
  have hαeq : B.normalizerMonoidHom ⟨x, hx⟩ =
      MulAut.conj (⟨y, hy⟩ : B) * B.normalizerMonoidHom ⟨y⁻¹ * x * y, hb⟩ *
        (MulAut.conj (⟨y, hy⟩ : B))⁻¹ := by
    rw [hβeq]
    group
  rw [hαeq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ⟨⟨y, hy⟩, rfl⟩ hβ)
    (Subgroup.inv_mem _ ⟨⟨y, hy⟩, rfl⟩)

private theorem exists_conj_mem_normalizer_inf_of_weakBlock
    (hK5 : KFactOddAutParabolicFixPrime)
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev) {M H L : Subgroup G}
    (hphase : TwoLocalPhaseThree M H) (hL : IsWeakSBlock M (CFSG.Open.pCoreOf 2 H) L)
    (h93 : NineThreeConclusion M (CFSG.Open.pCoreOf 2 H) L) (hn1 : ¬ NineThreeOne L)
    (hm3L : CFSG.Open.pRank 3 (barM M L) ≤ 2) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hdL : ¬ d ∣ Nat.card (H ⊓ L : Subgroup G))
    {x : ↥M ⧸ CFSG.pCore 2 ↥M} (hxd : x ^ d = 1)
    (hx : x ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hout : (barM M L).normalizerMonoidHom ⟨x, hx⟩ ∉ inner ↥(barM M L)) :
    ∃ y ∈ barM M L, ∃ hbL : y⁻¹ * x * y ∈
        Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      (y⁻¹ * x * y) ^ d = 1 ∧
      (barM M L).normalizerMonoidHom ⟨y⁻¹ * x * y, hbL⟩ ∉ inner ↥(barM M L) ∧
      y⁻¹ * x * y ∈
        Subgroup.normalizer (barM M (H ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have : Fact d.Prime := ⟨hd⟩
  have hd2 : d ≠ 2 := by omega
  let S : Subgroup G := CFSG.Open.pCoreOf 2 H
  let B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := barM M L
  have hx' : x ∈ Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hx
  have hxpow : (⟨x, hx'⟩ : Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ^ d = 1 :=
    Subtype.ext hxd
  have hα : (B.normalizerMonoidHom ⟨x, hx'⟩) ^ d = 1 := by
    rw [← map_pow, hxpow, map_one]
  have h2 : NineThreeTwo M S L :=
    nineThreeTwo_of_not_mem_inner hT hL.toIsTwoPrimeComponent h93 hn1 hm3L hd hd2 hα hout
  have hdP : ¬ d ∣ Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
    intro hdiv
    rw [show Subgroup.normalizer (S : Set G) = H from hphase.normalizer_twoCore_H] at hdiv
    apply hdL
    have h1 : Nat.card (barM M (H ⊓ L)) ∣ Nat.card (H ⊓ L : Subgroup G) := by
      rw [barM, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hL.le)).toEquiv]
      exact Subgroup.card_map_dvd _ _
    exact hdiv.trans h1
  obtain ⟨y, hyB, hbN⟩ := exists_conj_mem_normalizer_of_not_mem_inner hK5
    hL.toIsTwoPrimeComponent h2 hd hd5 hdP hxd hx' hout
  have hbP : y⁻¹ * x * y ∈
      Subgroup.normalizer (barM M (H ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [show barM M (Subgroup.normalizer (S : Set G) ⊓ L) = barM M (H ⊓ L) from by
      rw [hphase.normalizer_twoCore_H]] at hbN
    exact hbN
  have hbL : y⁻¹ * x * y ∈
      Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hyB))
      hx') (Subgroup.le_normalizer hyB)
  have hbd : (y⁻¹ * x * y) ^ d = 1 := by
    rw [show y⁻¹ * x * y = y⁻¹ * x * (y⁻¹)⁻¹ from by group]
    rw [conj_pow, hxd]
    group
  exact ⟨y, hyB, hbL, hbd,
    notMem_inner_normalizerMonoidHom_conj hx' hyB hbL hout, hbP⟩

theorem exists_le_normalizer_inf_of_not_mem_inner
    (hK5 : KFactOddAutParabolicFixPrime)
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev) {M H L E : Subgroup G}
    (hphase : TwoLocalPhaseThree M H) (hL : IsWeakSBlock M (CFSG.Open.pCoreOf 2 H) L)
    (h93 : NineThreeConclusion M (CFSG.Open.pCoreOf 2 H) L) (hn1 : ¬ NineThreeOne L)
    (hm3L : CFSG.Open.pRank 3 (barM M L) ≤ 2) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hdL : ¬ d ∣ Nat.card (H ⊓ L : Subgroup G)) (hE : CFSG.Open.IsElemAbelian d E)
    (hEM : E ≤ M) {c : G} (hc : c ∈ E) (hc1 : c ≠ 1)
    (hcL : barM M (Subgroup.zpowers c) ≤
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {e : ↥M} (heE : (e : G) ∈ E)
    (he : QuotientGroup.mk' (CFSG.pCore 2 ↥M) e ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (heo : (barM M L).normalizerMonoidHom ⟨_, he⟩ ∉ inner ↥(barM M L)) :
    ∃ B : Subgroup G, B ≤ M ∧ IsPGroup d B ∧ 2 ≤ CFSG.Open.pRank d B ∧
      B ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := by
  have : Fact d.Prime := ⟨hd⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd2 : d ≠ 2 := by omega
  have hQH : CFSG.Open.pCoreOf 2 M ≤ H :=
    (hphase.twoCore_M_le hphase.twoCore_inf).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
  obtain ⟨a, haeq, ha, ha1, hac⟩ :=
    exists_centralizer_elem_of_barM_zpowers_le hd hd2 hE hEM hc hc1 hcL
  let x : ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) e
  have hxe : x ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := he
  have hedM : e ^ d = 1 := Subtype.ext (by simpa using hE.2 (e : G) heE)
  have hxd : x ^ d = 1 := by rw [← map_pow, hedM, map_one]
  obtain ⟨y, hyB, hbL, hbd, hbo, hbP⟩ :=
    exists_conj_mem_normalizer_inf_of_weakBlock hK5 hT hphase hL h93 hn1 hm3L
      hd hd5 hdL hxd hxe heo
  have hEcomm : IsMulCommutative E := hE.1
  have hccomm : Commute a x := by
    show a * x = x * a
    simp only [haeq, x, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa using congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : E) ⟨(e : G), heE⟩)
  have hcy : Commute a y := (Subgroup.mem_centralizer_iff.mp hac y hyB).symm
  have hcb : Commute a (y⁻¹ * x * y) := ((hcy.inv_right).mul_right hccomm).mul_right hcy
  exact exists_le_normalizer_inf_of_outer hQH hL.toIsTwoPrimeComponent hd hd2
    hcb.eq ha hbd ha1 hac hbL hbo hbP

theorem exists_le_normalizer_inf_of_elemAbelian
    (hK5 : KFactOddAutParabolicFixPrime)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev) {M H L E : Subgroup G}
    (hphase : TwoLocalPhaseThree M H) (hL : IsWeakSBlock M (CFSG.Open.pCoreOf 2 H) L)
    (hcat : CFSG.Open.IsCatalogGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)))
    (h93 : NineThreeConclusion M (CFSG.Open.pCoreOf 2 H) L) (hn1 : ¬ NineThreeOne L)
    (hm3L : CFSG.Open.pRank 3 (barM M L) ≤ 2) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hLd : CFSG.Open.pRank d (barM M L) ≤ 1)
    (hZ : ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)))
    (hdL : ¬ d ∣ Nat.card (H ⊓ L : Subgroup G)) (hE : CFSG.Open.IsElemAbelian d E)
    (hcard : Nat.card E = d ^ 3) (hEM : E ≤ M) (hEL : E ≤ Subgroup.normalizer (L : Set G)) :
    ∃ B : Subgroup G, B ≤ M ∧ IsPGroup d B ∧ 2 ≤ CFSG.Open.pRank d B ∧
      B ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := by
  have : Fact d.Prime := ⟨hd⟩
  have hQH : CFSG.Open.pCoreOf 2 M ≤ H :=
    (hphase.twoCore_M_le hphase.twoCore_inf).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
  rcases exists_le_centralizer_or_not_mem_inner hOut hL.toIsTwoPrimeComponent hcat hd hd5
    hLd hZ hE hcard hEM hEL with
    ⟨E₀, hE₀E, hE₀2, hE₀C⟩ | ⟨⟨c, hcE, hc1, hcC⟩, e, heE, he, heo⟩
  · refine ⟨E₀, hE₀E.trans hEM, hE.isPGroup.to_le hE₀E, hE₀2, ?_⟩
    refine le_normalizer_inf_of_barM_le_normalizer hQH hL.le (hE₀E.trans hEM)
      (hE₀E.trans hEL) ?_
    exact hE₀C.trans ((Subgroup.centralizer_le (barM_mono inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _))
  · exact exists_le_normalizer_inf_of_not_mem_inner hK5 hT hphase hL h93 hn1 hm3L
      hd hd5 hdL hE hEM hcE hc1 hcC heE he heo

theorem two_le_pRank_inf_centralizer_of_isSylowOf_jOne_of_kFacts
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (hK5 : KFactOddAutParabolicFixPrime)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev)
    {M Q H : Subgroup G} {p : ℕ} (h : TwelveCtx G M p Q H)
    (hM3 : CFSG.Open.pRank 3 M ≤ 3) {d : ℕ} (hd : d ∈ sigmaSet G M) (hd5 : 5 ≤ d)
    {L : Subgroup G} (hL : L ∈ weakBlockSet M H)
    (ht : ∃ t ∈ barM M L, orderOf t = 3 ∧
      t ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hS : ¬ CFSG.QuasithinUnique.IsSylowTwoOf (CFSG.Open.pCoreOf 2 H ⊓ L) L)
    (h93 : NineThreeConclusion M (CFSG.Open.pCoreOf 2 H) L) (hn1 : ¬ NineThreeOne L)
    (hYL : ∀ y ∈ oPPrimeHull d (H ⊓ M), ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (hm3L : CFSG.Open.pRank 3 (barM M L) ≤ 2) {W : Subgroup G}
    (hW : CFSG.ABGLocalTools.IsSylowOf 3 W (jOne H L)) :
    2 ≤ CFSG.Open.pRank d (M ⊓ Subgroup.centralizer (W : Set G)) := by
  have hdprime : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hsimple : IsSimpleGroup G := h.cstar.simple
  have hphase : TwoLocalPhaseThree M H := h.twoLocalPhaseThree
  have hL' : IsWeakSBlock M (pCoreOf 2 H) L := hL
  have hLc : IsTwoPrimeComponent M L := hL'.toIsTwoPrimeComponent
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper
      (@CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top G _ _ hsimple h.cstar.nonab
        M h.maxLocal.1)
  have hcat : CFSG.Open.IsCatalogGroup
      (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    CFSG.isCatalogGroup_of_isComponentOf (hK.quotient (CFSG.pCore 2 ↥M)) hLc.component
  obtain ⟨E, hEM, hE, hcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := d) (hp := ⟨hdprime⟩) (k := 3)
      (h.cstar.three_le_pRank_of_mem_sigmaSet h.maxLocal hd)
  have hEL : E ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_isTwoPrimeComponent_of_isPGroup hLc hM3 ht hdprime hd5
      (IsPGroup.of_card hcard) hEM
  obtain ⟨hdL, hLd, hZ⟩ :=
    not_dvd_card_inf_of_isWeakSBlock hT hdprime hd5 hphase hL' hS h93 hn1 hN1 hm3L hYL
  obtain ⟨B, hBM, hB, hB2, hBN⟩ :=
    exists_le_normalizer_inf_of_elemAbelian hK5 hOut hT hphase hL' hcat h93 hn1 hm3L
      hdprime hd5 hLd hZ hdL hE hcard hEM hEL
  exact two_le_pRank_inf_centralizer_of_le_normalizer_inf hLc.le hdprime hd5 hdL hm3L hW
    hB hBM hB2 hBN

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
