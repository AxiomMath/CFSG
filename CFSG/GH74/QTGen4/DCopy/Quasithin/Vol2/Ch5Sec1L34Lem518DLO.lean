module

public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Vol2.Ch5Sec1L34F112Four
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem516
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518DL
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518DLOS331
public import CFSG.Quasithin.Background.C2PushY
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParFact

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.GH74.QTGen4.DSGen4

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem false_of_outer_F4 (hPF : L34ParabolicFact) (hTA : L34TwoAutFact)
    (h5114 : Stmt5_1_14_first_F4) (h432 : Stmt4_3_2_F4) (h331 : Stmt3_3_1_F4) (h510 : Stmt5_1_10_F4)
    (hR : L2RankOneSylowFact) (hDSA : DSALoc_F4)
    (hPC : L34ParabolicChiefFact) (hD : D ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    {d₀ : G} (hd₀D : d₀ ∈ D) (hd₀3 : d₀ ^ 3 = 1)
    (hd₀ : ∀ k ∈ oTwoUpper H, d₀ * k⁻¹ ∉ centralizerModO2 (oTwoUpper H)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨hST, hTLS, hTKS, hOMS, hOMpS, hSN⟩ := h.S_facts_F4 h510 h331 hR hD
  have hS2 : IsPGroup 2 (pCoreOf 2 (D ⊔ B ⊔ T)) := pCoreOf_isPGroup 2 _
  have hTK := h.isSylowTwoOf_inf_K
  have hTMp := h.T_le_Mp
  have hBK : B ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    h.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))
  have hSMp : pCoreOf 2 (D ⊔ B ⊔ T) ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hST.trans hTMp
  obtain ⟨U, hOU, hUTK, hUcomm, hUsq, hUcard, hUN, φ, hφs, hφk⟩ :=
    h.exists_parabolic_F4 hPF hTA h510 h331 hR hD hd₀D hd₀3 hd₀
  have hUK : U ≤ oTwoUpper H := hUTK.trans inf_le_right
  have hTKN : T ⊓ oTwoUpper H ≤ Subgroup.normalizer (U : Set G) :=
    hTKS.trans (le_sup_right.trans hUN)
  obtain ⟨hL2K₂, hnsK₂, h5K₂, hTK₂, hBorK₂⟩ :=
    oTwoUpper_parabolic_facts rfl hTK hUTK hTKN φ hφs hφk
  set K₂ := oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) with hK₂def
  have hK₂K : K₂ ≤ oTwoUpper H := (oTwoUpper_le _).trans inf_le_left

  have hDK₂ : D ≤ Subgroup.normalizer (K₂ : Set G) := fun x hx =>
    mem_normalizer_oTwoUpper_inf (hD hx) (hUN (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)))
  have hSK₂ : pCoreOf 2 (D ⊔ B ⊔ T) ≤ Subgroup.normalizer (K₂ : Set G) := fun x hx =>
    mem_normalizer_oTwoUpper_inf (hSMp hx) (hUN (Subgroup.mem_sup_right hx))

  have hSK₂eq : pCoreOf 2 (D ⊔ B ⊔ T) ⊓ K₂ = T ⊓ K₂ :=
    le_antisymm (inf_le_inf_right _ hST)
      (le_inf ((inf_le_inf_left T hK₂K).trans hTKS) inf_le_right)
  have hSLeq : pCoreOf 2 (D ⊔ B ⊔ T) ⊓ L = T ⊓ L :=
    le_antisymm (inf_le_inf_right _ hST) (le_inf hTLS inf_le_right)

  have hBorL : borelOf L (pCoreOf 2 (D ⊔ B ⊔ T)) = D ⊔ (T ⊓ L) := by
    rw [hh.borelL_eq_sup h.notation59.2.1]
    show L ⊓ Subgroup.normalizer ((pCoreOf 2 (D ⊔ B ⊔ T) ⊓ L : Subgroup G) : Set G) = _
    rw [hSLeq]
  obtain ⟨-, -, hBorel, -⟩ := h510 G T M L H B D n h.hyp h.notation59
  have hMK := h.hyp.borel_eq hBorel
  have hBorK₂M : borelOf K₂ (pCoreOf 2 (D ⊔ B ⊔ T)) ≤ M := by
    intro x hx
    have hx' : x ∈ K₂ ⊓ Subgroup.normalizer ((T ⊓ K₂ : Subgroup G) : Set G) := by
      have hx2 := hx.2
      rw [hSK₂eq] at hx2
      exact ⟨hx.1, hx2⟩
    have hxMK : x ∈ M ⊓ oTwoUpper H := by
      rw [hMK]
      exact ⟨hK₂K hx.1, hBorK₂ hx'⟩
    exact hxMK.1

  have hcharM : CharTwo M :=
    charTwo_of_inH' hh.qtke hh.sylow ⟨hh.T_le, pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1⟩
  have hcharMp := h.charTwo_Mp_F4 h5114
  have hDMp : D ⊔ (T ⊓ L) ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    sup_le hD (inf_le_left.trans hTMp)
  have hc1 : CharTwo (K₂ ⊔ pCoreOf 2 (D ⊔ B ⊔ T) ⊔ borelOf L (pCoreOf 2 (D ⊔ B ⊔ T))) := by
    refine C2Push.charTwo_of_pCoreOf_le hcharMp (hOMpS.trans (le_sup_right.trans le_sup_left)) ?_
    rw [hBorL]
    exact sup_le (sup_le (hK₂K.trans Subgroup.le_normalizer) hSMp) hDMp
  have hc2 : CharTwo (L ⊔ pCoreOf 2 (D ⊔ B ⊔ T) ⊔ borelOf K₂ (pCoreOf 2 (D ⊔ B ⊔ T))) :=
    C2Push.charTwo_of_pCoreOf_le hcharM (hOMS.trans (le_sup_right.trans le_sup_left))
      (sup_le (sup_le hh.L_le (hST.trans hh.T_le)) hBorK₂M)

  have hK₂M : ¬ K₂ ≤ M := by
    intro hle
    have hMH : K₂ ≤ M ⊓ H := le_inf hle (hK₂K.trans (oTwoUpper_le H))
    have h1 : 5 ∣ Nat.card ↥(M ⊓ H) := h5K₂.trans (Subgroup.card_dvd_of_le hMH)
    rw [h.hyp.card_inf_eq h.notation59, h.card_B_eq_three_F4 h510] at h1
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hh.sylow.1
    rw [hm] at h1
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h1 with h2 | h2
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h2) (by norm_num)
    · exact absurd h2 (by norm_num)
  have hO2 : pCoreOf 2 (K₂ ⊔ L ⊔ pCoreOf 2 (D ⊔ B ⊔ T)) = ⊥ := by
    by_contra hne
    have hloc : IsTwoLocal (Subgroup.normalizer
        (pCoreOf 2 (K₂ ⊔ L ⊔ pCoreOf 2 (D ⊔ B ⊔ T)) : Set G)) :=
      ⟨_, hne, pCoreOf_isPGroup 2 _, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hsup : K₂ ⊔ L ⊔ pCoreOf 2 (D ⊔ B ⊔ T) ≤ M' := (le_normalizer_pCoreOf 2 _).trans hle
    have hM'eq : M' = M :=
      (h432 G T M L hh.simple hh.nonabelian hh.qtke hh.sylow hh.maxTwoLocal hh.T_le hh.maximal
        hh.faithful hh.L_le hh.normal ⟨n, hh.two_le, hh.lie⟩).1 M' hM'
        (le_sup_right.trans (le_sup_left.trans hsup))
    exact hK₂M (hM'eq ▸ le_sup_left.trans (le_sup_left.trans hsup))

  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left hh.sup_le_normalizer
  have eL : O2Q L ≃* oTwoQuot ↥L := QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥L 2)
  have hlistL : IsRankOneListed (oTwoQuot ↥L) :=
    (isRankOneListed_of_lieModel (by have := hh.two_le; omega) hh.lie).of_mulEquiv eL
  have hlistK₂ : IsRankOneListed (oTwoQuot ↥K₂) := Or.inl ⟨2, by norm_num, hL2K₂⟩
  have hhyp : Hyp111 K₂ L (pCoreOf 2 (D ⊔ B ⊔ T)) := by
    refine ⟨⟨inferInstance, hS2, hSK₂, by rw [hSK₂eq]; exact hTK₂, hlistK₂, ?_, hc1⟩,
      ⟨inferInstance, hS2, hST.trans (hh.T_le.trans hh.normal), by rw [hSLeq]; exact hTL,
        hlistL, hBorK₂M.trans hh.normal, hc2⟩, hO2⟩
    rw [hBorL]
    exact sup_le hDK₂ (hTLS.trans hSK₂)
  have hqt : IsQuasithinSub (K₂ ⊔ L ⊔ pCoreOf 2 (D ⊔ B ⊔ T)) := by
    intro p hp hp2 R _ hR' hR2
    exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
      (pRank_le_two_of_isTwoLocal hh.qtke hp hp2 ⟨R, hR', hR2, rfl⟩)
  have hnorm : ((pCoreOf 2 (D ⊔ B ⊔ T)).subgroupOf
      (pCoreOf 2 (D ⊔ B ⊔ T) ⊔ borelOf L (pCoreOf 2 (D ⊔ B ⊔ T)))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr ?_
    rw [hBorL]
    exact sup_le Subgroup.le_normalizer
      (sup_le (fun x hx => hSN (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)))
        (hTLS.trans Subgroup.le_normalizer))
  have hLns : ¬ Group.IsSolvable ↥L := by
    rw [isSolvable_iff_perfectCore_eq_bot, perfectCore_eq_self_of_perfect hh.commutator_eq]
    intro hL
    have := hh.isSimple
    have hnt : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := IsSimpleGroup.toNontrivial
    obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
    apply hxy
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        have hall : ∀ z : ↥L, z = 1 := fun z => Subtype.ext (by
          have h1 : (z : G) ∈ (⊥ : Subgroup G) := by rw [← hL]; exact z.2
          exact Subgroup.mem_bot.mp h1)
        rw [hall x, hall y]
  obtain ⟨⟨hB₂, -⟩, -⟩ :=
    hDSA G K₂ L (pCoreOf 2 (D ⊔ B ⊔ T)) hhyp hqt (Or.inr hnorm) hnsK₂ hLns
  obtain ⟨m, hm⟩ := D15Proof.exists_isChiefSeriesFrom (H := K₂) (U := pCoreOf 2 K₂)
    (pCoreOf 2 K₂) ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K₂ hg) x).mp hx⟩
  have hle2 : m ≤ 2 := (le_one_of_isShort2 hB₂.1 hm).trans (by norm_num)
  have hcharK : CharTwo (oTwoUpper H) :=
    CharTwo.of_normal (charTwo_of_inH' hh.qtke hh.sylow h.hyp.hStar.1) (oTwoUpper_le H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
        (le_normalizer_oTwoUpper H))
  have hge3 := hPC G (oTwoUpper H) U h.l34 hcharK hOU hUK hUcomm hUsq hUcard m hm
  omega

end Hyp5_1_14

end Setting

theorem stmt5_1_18_DL_outer_of_inputs_F4 (hPF : L34ParabolicFact) (hTA : L34TwoAutFact)
    (h5114 : Stmt5_1_14_first_F4) (h432 : Stmt4_3_2_F4) (h331 : Stmt3_3_1_F4) (h510 : Stmt5_1_10_F4)
    (hR : L2RankOneSylowFact) (hDSA : DSALoc_F4)
    (hPC : L34ParabolicChiefFact) : Stmt5_1_18_DL_outer_F4 := by
  intro G _ _ T M L V H B D n h _ D₃ hD₃ h3 _ hout hD
  obtain ⟨d, hd, hdout⟩ := hout
  have hd3 : d ^ 3 = 1 := by
    have h' := pow_card_eq_one' (G := ↥D₃) (x := ⟨d, hd⟩)
    rw [h3] at h'
    exact congrArg Subtype.val h'
  exact h.false_of_outer_F4 hPF hTA h5114 h432 h331 h510 hR hDSA hPC hD (hD₃ hd) hd3 hdout

theorem stmt5_1_18_DL_outer_of_F4 (h5114 : Stmt5_1_14_first_F4) (h432 : Stmt4_3_2_F4)
    (h331 : Stmt3_3_1_F4) (h510 : Stmt5_1_10_F4) (hR : L2RankOneSylowFact) (hDSA : DSALoc_F4)
    (hPC : L34ParabolicChiefFact) : Stmt5_1_18_DL_outer_F4 :=
  stmt5_1_18_DL_outer_of_inputs_F4 l34ParabolicFact l34TwoAutFact h5114 h432 h331 h510 hR hDSA hPC

theorem stmt5_1_18_of_reduced_outer_F4 (hT : L2TorusFact) (h510 : Stmt5_1_10_F4)
    (h515 : Stmt5_1_15_F4) (h516 : Stmt5_1_16_F4) (h5114 : Stmt5_1_14_first_F4) (h517 : Stmt5_1_17_F4)
    (h432 : Stmt4_3_2_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hDSA : DSALoc_F4)
    (hPC : L34ParabolicChiefFact) (hD5 : Stmt5_1_18_D5_F4) :
    Stmt5_1_18_F4 :=
  stmt5_1_18_of_reduced_F4 hT h510 h515 h516 h5114 h517
    (stmt5_1_18_DL_outer_of_F4 h5114 h432 h331 h510 hR hDSA hPC) hD5

end CFSG.Quasithin.H13
