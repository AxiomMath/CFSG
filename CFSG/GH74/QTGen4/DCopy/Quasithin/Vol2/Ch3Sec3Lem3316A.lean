module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316A

public section
namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Step3_3_16SL3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K], 1 < n → Nat.card K = 2 ^ n →
      Nonempty (↥(autOn L (vPlus L T)) ≃* ↥(StatedSL 3 K)) →
      (∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
        Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) → False

@[expose] def Step3_3_16Sp4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
      Nonempty (↥(autOn L (vPlus L T)) ≃* ↥(StatedSp 2 K)) → IsSp4Block L → False

theorem stmt3_3_16_of_F4 (h6 : Stmt3_3_6) (h14 : Stmt3_3_14_F4) (hC32 : ASInputs.AS_C_1_32_F4)
    (hG2 : FactG2Cayley) (hSL : Step3_3_16SL3_F4) (hSp : Step3_3_16Sp4_F4) : Stmt3_3_16_F4 := by
  intro G _ _ T M L D h n K _ _ hn hK
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans (h14 G T M L D h).2
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hker : pCoreOf 2 L ≤ Subgroup.centralizer (vPlus L T : Set G) := hOQ.trans hQV
  have hq := h.Lq
  have hc132 := fun (hr : IsRankTwoLie2Derived
      ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) =>
    hC32 G (L ⊔ T) T L (((h6 G T M L D h).2.2.2 hr).2 hTL) h.toSetup331.mem_cComp
      (Subgroup.coe_mul_of_right_le_normalizer_left L T hTL)
  have hdvd := L3316.card_dvd hLV hker
  have hsp4 : IsSp4Block L → Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 979200 := fun hb => by
    obtain ⟨-, F, _, _, hF, α, hαs, hαk, -⟩ := hb
    obtain ⟨e'⟩ := Obs3324.nonempty_quot_equiv α hαs hαk
    have hF' : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
    rw [Nat.card_congr e'.toEquiv, L3316.card_sp4 hF']
    norm_num
  have hsl3 : ∀ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ m → IsModO2Surj L α → ¬ L ≤ Subgroup.centralizer (vPlus L T : Set G) →
      1 ≤ m ∧ ∃ c : ℕ, (c = 1 ∨ c = 3) ∧ c * Nat.card ↥(autOn L (vPlus L T)) =
        2 ^ (m * 3) * ((2 ^ (m * 2) - 1) * (2 ^ (m * 3) - 1)) := by
    intro m F _ _ α hF hmod hnt
    obtain ⟨e'⟩ := Obs3324.nonempty_quot_equiv α hmod.1 hmod.2
    have hF' : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, hF]
    have hm : 1 ≤ m := by
      by_contra hm0
      have h1 : 1 < Fintype.card F := Fintype.one_lt_card
      rw [hF, show m = 0 by omega] at h1
      norm_num at h1
    obtain ⟨c, hc, hcm⟩ := L3316.exists_mul_card_sl3 hLV hker hnt hq e'
    exact ⟨hm, c, hc, by rw [hcm, L3316.card_sl3 hF']⟩
  refine ⟨⟨fun e => ?_⟩, ⟨fun e => ?_⟩, ⟨fun e => ?_⟩⟩
  ·
    have hcard : Nat.card ↥(autOn L (vPlus L T)) =
        2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
      rw [Nat.card_congr e.toEquiv, L3316.card_sl3 hK]
    have hge := L3316.sl3_ge (n := n) (by omega)
    have hnt := L3316.not_le_centralizer_of_one_lt hLV (by omega)
    obtain ⟨⟨cq⟩, hle⟩ := Obs3324.quot_data hLV hker hnt hq
    have hr : IsRankTwoLie2Derived
        ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      Or.inl ⟨n, L3316.isPSL3_of_cover (SzN15.isQuasisimple_of_equiv_sl3 e) cq (by omega) hK e⟩
    rcases hc132 hr with hb | hb | hb | hb | ⟨m, F, _, _, α, hF, hmod⟩
    · have := L3316.card_le_of_small_block (L := L) (Or.inl hb); omega
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inl hb)); omega
    · rw [hcard, hsp4 hb] at hdvd
      have h3 := L3316.le_eight_of_dvd ((Dvd.intro _ rfl).trans hdvd)
      obtain rfl : n = 2 := by omega
      norm_num at hdvd
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inr hb)); omega
    · obtain ⟨hm, c, hc, hcm⟩ := hsl3 m F inferInstance inferInstance α hF hmod hnt
      rw [hcard] at hcm
      have he := L3316.exp_eq_of_mul hc
        ((L3316.odd_two_pow_mul_sub_one (by omega) (by norm_num)).mul
          (L3316.odd_two_pow_mul_sub_one (by omega) (by norm_num)))
        ((L3316.odd_two_pow_mul_sub_one hm (by norm_num)).mul
          (L3316.odd_two_pow_mul_sub_one hm (by norm_num))) hcm
      obtain rfl : m = n := by omega
      exact hSL G T M L D h m K hn hK ⟨e⟩ ⟨F, inferInstance, inferInstance, α, hF, hmod⟩
  ·
    have hcard : Nat.card ↥(autOn L (vPlus L T)) =
        2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) := by
      rw [Nat.card_congr e.toEquiv, L3316.card_sp4 hK]
    have hge := L3316.sp4_ge (n := n) (by omega)
    have hnt := L3316.not_le_centralizer_of_one_lt hLV (by omega)
    obtain ⟨⟨cq⟩, hle⟩ := Obs3324.quot_data hLV hker hnt hq
    have h4K : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hY : CFSG.IsQuasisimple ↥(autOn L (vPlus L T)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num) (Or.inl (Or.inr h4K)))
    have hr : IsRankTwoLie2Derived
        ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      Or.inr (Or.inr (Or.inr (Or.inl ⟨n, L3316.isPSp4_of_cover hY cq (by omega) hK e⟩)))
    rcases hc132 hr with hb | hb | hb | hb | ⟨m, F, _, _, α, hF, hmod⟩
    · have := L3316.card_le_of_small_block (L := L) (Or.inl hb); omega
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inl hb)); omega
    · have hdvd' := hdvd
      rw [hcard, hsp4 hb] at hdvd'
      have h3 := L3316.le_eight_of_dvd ((Dvd.intro _ rfl).trans hdvd')
      obtain rfl : n = 2 := by omega
      exact hSp G T M L D h K (by rw [hK]; norm_num) ⟨e⟩ hb
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inr hb)); omega
    · obtain ⟨hm, c, hc, hcm⟩ := hsl3 m F inferInstance inferInstance α hF hmod hnt
      rw [hcard] at hcm
      exact L3316.sp4_ne_sl3 (by omega) hm hc hcm
  ·
    have hcard : Nat.card ↥(autOn L (vPlus L T)) =
        2 ^ (n * 6) * ((2 ^ (n * 6) - 1) * (2 ^ (n * 2) - 1)) := by
      rw [Nat.card_congr e.toEquiv, L3316.card_g2 (by omega) hK]
    have hge := L3316.g2_ge (n := n) (by omega)
    have hnt := L3316.not_le_centralizer_of_one_lt hLV (by omega)
    obtain ⟨⟨cq⟩, hle⟩ := Obs3324.quot_data hLV hker hnt hq
    have eZ : ↥(quasithinG2 K) ⧸ Subgroup.center ↥(quasithinG2 K) ≃*
        (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (QuotientGroup.congr (Subgroup.center ↥(autOn L (vPlus L T)))
        (Subgroup.center ↥(quasithinG2 K)) e (Subgroup.map_center_eq e)).symm.trans cq.symm
    have hr : IsRankTwoLie2Derived
        ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, IsG2.of_mulEquiv eZ (hG2 K n (by omega) hK)⟩)))))
    rcases hc132 hr with hb | hb | hb | hb | ⟨m, F, _, _, α, hF, hmod⟩
    · have := L3316.card_le_of_small_block (L := L) (Or.inl hb); omega
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inl hb)); omega
    · rw [hcard, hsp4 hb] at hdvd
      have h3 := L3316.le_eight_of_dvd ((Dvd.intro _ rfl).trans hdvd)
      omega
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inr hb)); omega
    · obtain ⟨hm, c, hc, hcm⟩ := hsl3 m F inferInstance inferInstance α hF hmod hnt
      rw [hcard] at hcm
      exact L3316.g2_ne_sl3 (by omega) hm hc hcm

end CFSG.Quasithin.H13
