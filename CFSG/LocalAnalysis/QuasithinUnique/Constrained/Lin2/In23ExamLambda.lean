module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Syl

public section

namespace CFSG.QuasithinUnique.Lin2.Exam

open CFSG.Open CFSG.Quasithin

section Lambda

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem exam_lambda (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s x : G} (hs : s ∈ S)
    (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) (hc : centerOf L ≠ ⊥) (h4 : 4 < 2 ^ n)
    (hx : x ∈ T ⊓ Subgroup.centralizer ({s} : Set G)) (hxS : x ∉ S) {Y : Subgroup G}
    (hYT : Y ≤ T ⊓ Subgroup.centralizer ({s} : Set G))
    (hYL : L ⊓ Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (hYL' : conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x ≤
      Subgroup.normalizer (Y : Set G)) :
    Y ≤ Subgroup.zpowers s := by
  obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  obtain ⟨m, hm, hm1, hsh, hlin, hUs, hO, hRsyl⟩ := exam_block E hcfg hs hsR hs2 h4
  obtain ⟨hZs, -⟩ := exam_blockZ E hcfg hs hsR hs2 hc h4 hm hsh hUs hO
  set C := Subgroup.centralizer ({s} : Set G) with hC
  set Ls := L ⊓ C with hLs
  set R := thompsonJ S with hR
  have hRL : R ≤ L := (E.Rsyl hcfg).1
  have hRT : R ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hOU : pCoreOf 2 Ls = blockU Ls := hO.trans hUs
  have hsh' : IsShort2 (conjR Ls x) := (isShort2_conjR_iff Ls x).mpr hsh
  have hUs' : blockU (conjR Ls x) = conjR (blockU L) x ⊓ C := exam_blockU_conj hxs L hUs
  have hOU' : pCoreOf 2 (conjR Ls x) = blockU (conjR Ls x) := by
    rw [conjR_pCoreOf, hOU, blockU_conjR]
  have hZs' : blockZ (conjR Ls x) = conjR (centerOf L) x ⊓ C := exam_blockZ_conj hxs L hZs
  have hY2 : IsPGroup 2 Y := hcfg.sylowT.isPGroup.to_le (hYT.trans inf_le_left)
  have hRx : conjR R x = R := conjR_eq_of_mem_normalizer (E.TnR hcfg hxT)
  have hTL : T ⊓ L ≤ R := by
    have hRle : R ≤ T ⊓ L := le_inf hRT hRL
    exact ((E.Rsyl hcfg).eq_of_le hRle inf_le_right
      (hcfg.sylowT.isPGroup.to_le inf_le_left)).le
  have hRU : R = blockU L ⊔ conjR (blockU L) x := (E.RUU hcfg hxT hxS).1
  have hUR : blockU L ≤ R := by rw [hRU]; exact le_sup_left
  have hVR : conjR (blockU L) x ≤ R := by rw [hRU]; exact le_sup_right
  have hRsLs : R ⊓ C ≤ Ls := exam_Rs_le E hcfg
  have hRsLs' : R ⊓ C ≤ conjR Ls x := exam_Rs_le_conj E hcfg hxT hxs
  have hUsRs : blockU L ⊓ C ≤ R ⊓ C := inf_le_inf_right _ hUR
  have hUs'Rs : conjR (blockU L) x ⊓ C ≤ R ⊓ C := inf_le_inf_right _ hVR
  have hcardUs : Nat.card (conjR (blockU L) x ⊓ C : Subgroup G) =
      Nat.card (blockU L ⊓ C : Subgroup G) :=
    E.card_conjR_U_inf_centralizer hcfg hs hsR hs2 hxT
  have hne := exam_Us_ne E hcfg hs hsR hs2 hc h4 hxT hxS
  have hN1 : Ls ≤ Subgroup.normalizer ((Y ⊓ Ls : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hYL hg, Subgroup.le_normalizer hg⟩
  have hN2 : conjR Ls x ≤ Subgroup.normalizer ((Y ⊓ conjR Ls x : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hYL' hg, Subgroup.le_normalizer hg⟩
  have hA1U : Y ⊓ Ls ≤ blockU Ls := by
    have := le_pCoreOf_of_normalizes (inf_le_right : Y ⊓ Ls ≤ Ls) hN1 hY2.to_inf_left
    rwa [hOU] at this
  have hA2U : Y ⊓ conjR Ls x ≤ blockU (conjR Ls x) := by
    have := le_pCoreOf_of_normalizes (inf_le_right : Y ⊓ conjR Ls x ≤ conjR Ls x) hN2
      hY2.to_inf_left
    rwa [hOU'] at this
  have hA1Z : Y ⊓ Ls ≤ blockZ Ls := by
    rcases le_blockZ_or_eq_blockU hsh hOU hA1U hN1 with h | h
    · exact h
    · exfalso
      have hUY : blockU L ⊓ C ≤ Y := by
        have : blockU Ls ≤ Y := h ▸ inf_le_left
        rwa [← hUs] at this
      have hle : blockU L ⊓ C ≤ blockU (conjR Ls x) :=
        (le_inf hUY (hUsRs.trans hRsLs')).trans hA2U
      rw [hUs'] at hle
      exact hne (Subgroup.eq_of_le_of_card_ge hle hcardUs.le)
  have hA2Z : Y ⊓ conjR Ls x ≤ blockZ (conjR Ls x) := by
    rcases le_blockZ_or_eq_blockU hsh' hOU' hA2U hN2 with h | h
    · exact h
    · exfalso
      have hUY : conjR (blockU L) x ⊓ C ≤ Y := by
        have : blockU (conjR Ls x) ≤ Y := h ▸ inf_le_left
        rwa [hUs'] at this
      have hle : conjR (blockU L) x ⊓ C ≤ blockU Ls :=
        (le_inf hUY (hUs'Rs.trans hRsLs)).trans hA1U
      rw [← hUs] at hle
      exact hne (Subgroup.eq_of_le_of_card_ge hle hcardUs.ge).symm
  have hZinf : centerOf L ⊓ conjR (centerOf L) x = ⊥ := by
    have hz : lin2Z L (thompsonJ S) = centerOf L := by simp [lin2Z, hc]
    rcases E.Zcases hcfg (Z := lin2Z L (thompsonJ S)) rfl hxT hxS with ⟨hc0, -⟩ | ⟨-, -, hZ⟩
    · exact absurd hc0 hc
    · rwa [hz] at hZ
  have hA1R : Y ⊓ Ls ≤ R ⊓ C := by
    intro z hz
    obtain ⟨hzY, hzL⟩ := Subgroup.mem_inf.mp hz
    exact Subgroup.mem_inf.mpr ⟨hTL (Subgroup.mem_inf.mpr ⟨(hYT hzY).1, (Subgroup.mem_inf.mp hzL).1⟩),
      (Subgroup.mem_inf.mp hzL).2⟩
  have hA2R : Y ⊓ conjR Ls x ≤ R ⊓ C := by
    intro z hz
    obtain ⟨hzY, hzL⟩ := Subgroup.mem_inf.mp hz
    have hzL' : x * z * x⁻¹ ∈ Ls := mem_conjR.mp hzL
    have hzT : z ∈ T := (hYT hzY).1
    have hxzx : x * z * x⁻¹ ∈ T := T.mul_mem (T.mul_mem hxT hzT) (T.inv_mem hxT)
    have h1 : x * z * x⁻¹ ∈ R := hTL (Subgroup.mem_inf.mpr ⟨hxzx, (Subgroup.mem_inf.mp hzL').1⟩)
    have h2 : z ∈ conjR R x := mem_conjR.mpr h1
    rw [hRx] at h2
    exact Subgroup.mem_inf.mpr ⟨h2, (hYT hzY).2⟩
  have hA1bot : Y ⊓ Ls = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz1 : z ∈ blockZ Ls := hA1Z hz
    have hz2 : z ∈ blockZ (conjR Ls x) :=
      hA2Z (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).1, hRsLs' (hA1R hz)⟩)
    rw [hZs] at hz1
    rw [hZs'] at hz2
    have : z ∈ centerOf L ⊓ conjR (centerOf L) x :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz1).1, (Subgroup.mem_inf.mp hz2).1⟩
    rw [hZinf] at this
    exact this
  have hA2bot : Y ⊓ conjR Ls x = ⊥ := by
    rw [eq_bot_iff, ← hA1bot]
    intro z hz
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).1, hRsLs (hA2R hz)⟩
  have hYS : ∀ y ∈ Y, y ∈ S := by
    intro y₀ hy₀
    by_contra hy₀S
    have hy₀T : y₀ ∈ T := (hYT hy₀).1
    have hy₀C : y₀ ∈ C := (hYT hy₀).2
    have hy₀s : y₀ * s = s * y₀ := Subgroup.mem_centralizer_singleton_iff.mp hy₀C
    have hcomm : ∀ u ∈ blockU L ⊓ C, y₀ * u = u * y₀ := by
      intro u hu
      have huLs : u ∈ Ls := Subgroup.mem_inf.mpr ⟨blockU_le L hu.1, hu.2⟩
      have huR : u ∈ R := hUR hu.1
      have h1 : u * y₀ * u⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hYL huLs) y₀).mp hy₀
      have h2 : y₀ * u⁻¹ * y₀⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (E.TnR hcfg hy₀T) u⁻¹).mp (R.inv_mem huR)
      have hw : u * y₀ * u⁻¹ * y₀⁻¹ ∈ Y ⊓ Ls := by
        refine Subgroup.mem_inf.mpr ⟨Y.mul_mem h1 (Y.inv_mem hy₀), hRsLs
          (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)⟩
        · have : u * y₀ * u⁻¹ * y₀⁻¹ = u * (y₀ * u⁻¹ * y₀⁻¹) := by group
          rw [this]
          exact R.mul_mem huR h2
        · refine C.mul_mem (C.mul_mem (C.mul_mem hu.2 hy₀C) (C.inv_mem hu.2)) (C.inv_mem hy₀C)
      rw [hA1bot, Subgroup.mem_bot] at hw
      have : u * y₀ = y₀ * u := by
        calc u * y₀ = (u * y₀ * u⁻¹ * y₀⁻¹) * (y₀ * u) := by group
          _ = y₀ * u := by rw [hw, one_mul]
      exact this.symm
    have hnorm : y₀ ∈ Subgroup.normalizer ((blockU L ⊓ C : Subgroup G) : Set G) := by
      have hle := Lin2.le_normalizer_of_commute (A := blockU L ⊓ C) (B := Subgroup.zpowers y₀)
        (fun a ha b hb => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact ((Commute.zpow_right (show Commute a y₀ from (hcomm a ha).symm) k)).eq)
      exact hle (Subgroup.mem_zpowers y₀)
    have hconj : conjR (blockU L ⊓ C) y₀ = blockU L ⊓ C := conjR_eq_of_mem_normalizer hnorm
    have hσS : y₀ * x⁻¹ ∈ S := Five.mul_inv_mem_S E hcfg hxT hxS hy₀T hy₀S
    have hxs' : x⁻¹ * s = s * x⁻¹ := Five.comm_inv_of_comm hxs
    have hσs : (y₀ * x⁻¹) * s = s * (y₀ * x⁻¹) := by
      calc y₀ * x⁻¹ * s = y₀ * (x⁻¹ * s) := by group
        _ = y₀ * (s * x⁻¹) := by rw [hxs']
        _ = (y₀ * s) * x⁻¹ := by group
        _ = (s * y₀) * x⁻¹ := by rw [hy₀s]
        _ = s * (y₀ * x⁻¹) := by group
    have hσUs : conjR (blockU L ⊓ C) (y₀ * x⁻¹) = blockU L ⊓ C := by
      rw [conjR_inf, conjR_eq_of_mem_normalizer (E.S_le_normalizer_U hcfg hσS),
        conjR_centralizer_of_comm hσs]
    have hy₀eq : y₀ = (y₀ * x⁻¹) * x := by group
    have : conjR (blockU L ⊓ C) y₀ = conjR (blockU L) x ⊓ C := by
      calc conjR (blockU L ⊓ C) y₀ = conjR (blockU L ⊓ C) ((y₀ * x⁻¹) * x) := by
            rw [inv_mul_cancel_right]
        _ = conjR (conjR (blockU L ⊓ C) (y₀ * x⁻¹)) x := (conjR_conjR _ _ _).symm
        _ = conjR (blockU L ⊓ C) x := by rw [hσUs]
        _ = conjR (blockU L) x ⊓ C := conjR_inf_centralizer_of_comm _ hxs
    exact hne (hconj.symm.trans this)
  intro y hy
  have hyS := hYS y hy
  have hyT : y ∈ T := (hYT hy).1
  have hyC : y ∈ C := (hYT hy).2
  have hys : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
  have hyN : y ∈ Subgroup.normalizer ((Ls : Subgroup G) : Set G) :=
    exam_Ss_le_normalizer_Ls hcfg hyS hys
  have hyN' : y ∈ Subgroup.normalizer ((conjR Ls x : Subgroup G) : Set G) :=
    conjR_eq_self_iff.mp (exam_conjR_Lsx_of_mem E hcfg hxT hxs hyS hys)
  have hcL : ∀ ℓ ∈ Ls, ℓ * y = y * ℓ := by
    intro ℓ hℓ
    have h1 : y * ℓ * y⁻¹ ∈ Ls := (Subgroup.mem_normalizer_iff.mp hyN ℓ).mp hℓ
    have h2 : ℓ * y⁻¹ * ℓ⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hYL hℓ) y⁻¹).mp (Y.inv_mem hy)
    have hw : y * ℓ * y⁻¹ * ℓ⁻¹ ∈ Y ⊓ Ls :=
      Subgroup.mem_inf.mpr ⟨by
        have : y * ℓ * y⁻¹ * ℓ⁻¹ = y * (ℓ * y⁻¹ * ℓ⁻¹) := by group
        rw [this]; exact Y.mul_mem hy h2, Ls.mul_mem h1 (Ls.inv_mem hℓ)⟩
    rw [hA1bot, Subgroup.mem_bot] at hw
    calc ℓ * y = (y * ℓ * y⁻¹ * ℓ⁻¹)⁻¹ * (y * ℓ) := by group
      _ = y * ℓ := by rw [hw, inv_one, one_mul]
  have hcL' : ∀ ℓ ∈ conjR Ls x, ℓ * y = y * ℓ := by
    intro ℓ hℓ
    have h1 : y * ℓ * y⁻¹ ∈ conjR Ls x := (Subgroup.mem_normalizer_iff.mp hyN' ℓ).mp hℓ
    have h2 : ℓ * y⁻¹ * ℓ⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hYL' hℓ) y⁻¹).mp (Y.inv_mem hy)
    have hw : y * ℓ * y⁻¹ * ℓ⁻¹ ∈ Y ⊓ conjR Ls x :=
      Subgroup.mem_inf.mpr ⟨by
        have : y * ℓ * y⁻¹ * ℓ⁻¹ = y * (ℓ * y⁻¹ * ℓ⁻¹) := by group
        rw [this]; exact Y.mul_mem hy h2, (conjR Ls x).mul_mem h1 ((conjR Ls x).inv_mem hℓ)⟩
    rw [hA2bot, Subgroup.mem_bot] at hw
    calc ℓ * y = (y * ℓ * y⁻¹ * ℓ⁻¹)⁻¹ * (y * ℓ) := by group
      _ = y * ℓ := by rw [hw, inv_one, one_mul]
  have hKy : Ls ⊔ conjR Ls x ≤ Subgroup.centralizer ({y} : Set G) :=
    sup_le (fun ℓ hℓ => Subgroup.mem_centralizer_singleton_iff.mpr (hcL ℓ hℓ))
      (fun ℓ hℓ => Subgroup.mem_centralizer_singleton_iff.mpr (hcL' ℓ hℓ))
  have hyK : y ∈ Subgroup.centralizer ((Ls ⊔ conjR Ls x : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)
  have hmem : y ∈ T ⊓ C ⊓ Subgroup.centralizer ((Ls ⊔ conjR Ls x : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hyT, hyC⟩, hyK⟩
  rwa [Five.centralizer_Ks E hcfg hs hsR hs2 hc h4 hx hxS] at hmem

theorem exam_pCore_centralizer_le (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s x : G}
    (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) (hc : centerOf L ≠ ⊥)
    (h4 : 4 < 2 ^ n) (hx : x ∈ T ⊓ Subgroup.centralizer ({s} : Set G)) (hxS : x ∉ S) :
    pCoreOf 2 (Subgroup.centralizer ({s} : Set G)) ≤ Subgroup.zpowers s := by
  obtain ⟨m, hm, hm1, hsh, hlin, hUs, hO, hRsyl⟩ := exam_block E hcfg hs hsR hs2 h4
  have hTs : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({s} : Set G))
      (Subgroup.centralizer ({s} : Set G)) :=
    E.T_s_sylow hcfg hs hsR hs2 hO hRsyl.card_eq.symm
  have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  have hYC : pCoreOf 2 (Subgroup.centralizer ({s} : Set G)) ≤ Subgroup.centralizer ({s} : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _
  have hYn : Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.centralizer ({s} : Set G)) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  have hYT : pCoreOf 2 (Subgroup.centralizer ({s} : Set G)) ≤
      T ⊓ Subgroup.centralizer ({s} : Set G) :=
    hTs.le_of_normalizes hYC hYn (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  refine exam_lambda E hcfg hs hsR hs2 hc h4 hx hxS hYT
    (inf_le_right.trans hYn) ?_
  refine (conjR_mono inf_le_right x).trans ?_
  rw [conjR_centralizer_of_comm hxs]
  exact hYn

end Lambda

end CFSG.QuasithinUnique.Lin2.Exam
