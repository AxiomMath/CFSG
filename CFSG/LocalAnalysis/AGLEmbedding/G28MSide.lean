module

public import CFSG.LocalAnalysis.AGLEmbedding.G28SmallClose
public import CFSG.LocalAnalysis.AGLEmbedding.G28PieceOrbit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section CaseOneClose

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G} {z : G}

theorem D1G28Data.barM_Pi_le (h : D1G28Data P M H R z) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hb : StmtBlockInnerNormalizer) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (horb : ∀ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L) :
    barM M ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) ≤ blockParabolic M (pCoreOf 2 H) L := by
  have h3 := h.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have hBC : blockClosure M (H ⊓ M) L ≤ preM M (barM M L) := by
    refine sup_le (fun q hq => ?_) (iSup_le fun k => iSup_le fun hk => ?_)
    · refine (mem_preM ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M) hq)).mpr ?_
      rw [(mk_eq_one_iff_coe_mem_pCoreOf _).mpr hq]
      exact Subgroup.one_mem _
    · exact le_preM (hL.toIsTwoPrimeComponent.map_conj hk.2).le (horb k hk).le
  rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
  have hx' := Subgroup.mem_subgroupOf.mp hx
  have hxL := (mem_preM hxM).mp (hBC hx'.2)
  have hxS : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := (hKeq ▸ hx'.1).2
  have hxN := mem_normalizer_barM hxM hxS
  refine hb h3 h84 h86 hD2 hL _ hxL fun s hs => ⟨_ * s * _⁻¹,
    (Subgroup.mem_normalizer_iff.mp hxN s).mp hs, fun w hw => rfl⟩

theorem barM_sup_eq {M H V Pi : Subgroup G} (hVPi : V ≤ Pi) (hPiH : Pi ≤ H) (hPiM : Pi ≤ M) :
    barM M V ⊔ barM M (Pi ⊓ GLBPrimeCore 3 H) = barM M (Pi ⊓ (V ⊔ GLBPrimeCore 3 H)) := by
  apply le_antisymm
  · exact sup_le (Subgroup.map_mono (Subgroup.comap_mono (le_inf hVPi le_sup_left)))
      (Subgroup.map_mono (Subgroup.comap_mono (inf_le_inf_left _ le_sup_right)))
  · rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    have hx2 : x ∈ Pi ⊓ (V ⊔ GLBPrimeCore 3 H) := Subgroup.mem_subgroupOf.mp hx
    have hxPi : x ∈ Pi := hx2.1
    have hxVN : x ∈ V ⊔ GLBPrimeCore 3 H := hx2.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right V (GLBPrimeCore 3 H)
      ((hVPi.trans hPiH).trans (le_normalizer_glbPrimeCore 3 H))] at hxVN
    obtain ⟨v, hv, n, hn, hvn⟩ := hxVN
    subst hvn
    have hvM : v ∈ M := hPiM (hVPi hv)
    have hnPi : n ∈ Pi := by
      have : n = v⁻¹ * (v * n) := by group
      rw [this]
      exact Pi.mul_mem (Pi.inv_mem (hVPi hv)) hxPi
    have hnM : n ∈ M := hPiM hnPi
    have e : (⟨v * n, hxM⟩ : M) = ⟨v, hvM⟩ * ⟨n, hnM⟩ := rfl
    rw [e, map_mul]
    exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv))
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hnPi, hn⟩))

theorem D1G28Data.false_of_piece (h : D1G28Data P M H R z) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hB3 : StmtBlockThree) (hb : StmtBlockInnerNormalizer) (hSU : KFactBlockNoSU38)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {V : Subgroup G}
    (hVPi : V ≤ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L)
    (hV : SU38Piece (H ⊓ M) (GLBPrimeCore 3 H) z V) : False := by
  have h3 := h.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have horb := fun k (hk : k ∈ H ⊓ M) => h.barM_conj_eq_of_piece hB3 hL hVPi hV hk
  obtain ⟨hVV, hVK, -, hKVN, ⟨d, ψ, hd, hψ⟩, -, -⟩ := hV
  set N := GLBPrimeCore 3 H with hN
  set Pi := (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L with hPi
  have hPiK : Pi ≤ H ⊓ M := inf_le_left
  have hPiH : Pi ≤ H := hPiK.trans inf_le_left
  have hPiM : Pi ≤ M := hPiK.trans inf_le_right
  have hPiPL := h.barM_Pi_le h84 h86 hD2 hb hL horb
  have hPLPi := blockParabolic_le_barM hKeq hL.le (le_rfl : Pi ≤ Pi)
  have hPiNPi : ∀ x ∈ Pi, x ∈ Subgroup.normalizer ((Pi ⊓ N : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      le_normalizer_glbPrimeCore 3 H (hPiH hx)⟩
  have hPiNV : ∀ x ∈ Pi, x ∈ Subgroup.normalizer ((Pi ⊓ (V ⊔ N) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      hKVN (hPiK hx)⟩
  have hPLnorm : ∀ Y : Subgroup G, (∀ x ∈ Pi, x ∈ Subgroup.normalizer (Y : Set G)) →
      blockParabolic M (pCoreOf 2 H) L ≤
        Subgroup.normalizer (barM M Y : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro Y hY
    refine hPLPi.trans ?_
    rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    exact mem_normalizer_barM hxM (hY x (Subgroup.mem_subgroupOf.mp hx))
  have h37 := hSU G M (pCoreOf 2 H) L h3.isKGroup.1 h3.asc81bHyp hL (h3.nineThree h93 hL)
    (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL)
    (fun l hl hcond => hb h3 h84 h86 hD2 hL l hl hcond) (barM M (Pi ⊓ N)) V
    (hVPi.trans hPiM) ((Subgroup.map_mono (Subgroup.comap_mono inf_le_left)).trans hPiPL)
    ((Subgroup.map_mono (Subgroup.comap_mono hVPi)).trans hPiPL) (hPLnorm _ hPiNPi)
    (Nat.Coprime.coprime_dvd_right ((card_barM_dvd (inf_le_left.trans hPiM)).trans
      (Subgroup.card_dvd_of_le inf_le_right)) (glbPrimeCore_coprime 3 H))
    (by rw [barM_sup_eq hVPi hPiH hPiM]; exact hPLnorm _ hPiNV) hVV d ψ hd hψ
  have hdvdH : 3 ^ 7 ∣ Nat.card H := h37.trans ((Subgroup.card_dvd_of_le hPLPi).trans
    ((card_barM_dvd hPiM).trans (Subgroup.card_dvd_of_le hPiH)))
  have hRH : CFSG.ABGLocalTools.IsSylowOf 3 R H := h3.isSylow
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hRH
  obtain ⟨hRle, -, hidx⟩ := hRH
  have hmul := Subgroup.relIndex_mul_relIndex ⊥ R H bot_le hRle
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, h.card_R] at hmul
  rw [← hmul] at hdvdH
  have hc : Nat.Coprime (3 ^ 7) (R.relIndex H) :=
    Nat.Coprime.pow_left 7 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx)
  have := Nat.le_of_dvd (by norm_num) (hc.dvd_of_dvd_mul_right hdvdH)
  norm_num at this

end CaseOneClose

theorem stmtG28MSide_of (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (hOut : KFactBlockThreeOut) (hSU : KFactBlockNoSU38) :
    StmtG28MSide := by
  intro G _ _ P M H R z h
  have h3 := h.ph3
  obtain ⟨L, hL⟩ := h3.exists_weakSBlock h84 hD2
  obtain ⟨hNPi, y, hyL, hy3, ⟨l, hl, hyl⟩, hyPi⟩ := h.mem_Pi hB3 hL
  rcases h.dichotomy _ inf_le_left hNPi with hPiN | hPiT | ⟨V, hVPi, hV⟩
  ·
    have hyN := hPiN hyPi
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hyl
      simp
    obtain ⟨a, ha⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
    have hya : y ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hcop : Nat.Coprime (3 ^ a) (Nat.card (GLBPrimeCore 3 H)) :=
      Nat.Coprime.pow_left a (glbPrimeCore_coprime 3 H)
    exact hy1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hya) (Subgroup.orderOf_dvd_natCard _ hyN)))
  · exact h.false_of_le_zpowers_sup h84 h85 h86 h93 hD2 hB3 hb hOut hL hPiT
  · exact h.false_of_piece h84 h85 h86 h93 hD2 hB3 hb hSU hL hVPi hV

end CFSG.AGLEmbedding
