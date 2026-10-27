module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a
public import CFSG.Walter.W67.W1Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem mem_twoCoreIn_iff {X : Subgroup G} {x : G} (hx : x ∈ X) :
    x ∈ twoCoreIn X ↔ (⟨x, hx⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by
  unfold twoCoreIn CFSG.inSubgroup
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem twoCoreIn_le (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem twoCoreIn_normal_in (X : Subgroup G) : (twoCoreIn X).subgroupOf X |>.Normal := by
  rw [Subgroup.normal_subgroupOf_iff (twoCoreIn_le X)]
  intro h k hh hk
  unfold twoCoreIn CFSG.inSubgroup at hh ⊢
  obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hh
  refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * h' * ⟨k, hk⟩⁻¹, ?_, ?_⟩
  · exact (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem h' hh' ⟨k, hk⟩
  · simp

private theorem map_pCore_mem {X : Subgroup G} (e : ↥X ≃* SL23) {x : ↥X}
    (hx : x ∈ CFSG.pCore 2 ↥X) : e x ∈ CFSG.pCore 2 SL23 := by
  rw [← CFSG.pCore_map_iso 2 e]
  exact Subgroup.mem_map_of_mem e.toMonoidHom hx

private theorem card_twoCoreIn (X : Subgroup G) (e : ↥X ≃* SL23) : Nat.card (twoCoreIn X) = 8 := by
  unfold twoCoreIn CFSG.inSubgroup
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  calc Nat.card (CFSG.pCore 2 ↥X)
      = Nat.card ((CFSG.pCore 2 ↥X).map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ = Nat.card (CFSG.pCore 2 SL23) := by rw [CFSG.pCore_map_iso 2 e]
    _ = 8 := sl23_card_pCore

private theorem map_w_eq_neg_one {X : Subgroup G} (e : ↥X ≃* SL23) {w : G} (hw : w ∈ X)
    (hw2 : orderOf w = 2) : e ⟨w, hw⟩ = -1 := by
  have hsq : (⟨w, hw⟩ : ↥X) * ⟨w, hw⟩ = 1 := by
    apply Subtype.ext
    change (w : G) * w = 1
    have h := pow_orderOf_eq_one w
    rw [hw2] at h
    simpa [pow_two] using h
  have hsq' : e ⟨w, hw⟩ * e ⟨w, hw⟩ = 1 := by
    rw [← map_mul, hsq, map_one]
  rcases sl23_unique_involution _ hsq' with h | h
  · exfalso
    have hw1 : (⟨w, hw⟩ : ↥X) = 1 := by
      apply e.injective
      rw [h, map_one]
    have hwG : w = 1 := by simpa using congrArg Subtype.val hw1
    have : orderOf w = 1 := by rw [hwG]; exact orderOf_one
    omega
  · exact h

private theorem sl23_transfer {X : Subgroup G} (e : ↥X ≃* SL23) {w : G} (hw : w ∈ X)
    (hew : e ⟨w, hw⟩ = -1) :
    ∀ a ∈ twoCoreIn X, ∀ b ∈ twoCoreIn X,
      a * b * a⁻¹ * b⁻¹ ∈ zpowers w ∧ a * a ∈ zpowers w := by
  intro a ha b hb
  have haX : a ∈ X := twoCoreIn_le X ha
  have hbX : b ∈ X := twoCoreIn_le X hb
  have haP : (⟨a, haX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := (mem_twoCoreIn_iff haX).mp ha
  have hbP : (⟨b, hbX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := (mem_twoCoreIn_iff hbX).mp hb
  have h4a : (e ⟨a, haX⟩) ^ 4 = 1 := by
    have h := map_pCore_mem e haP
    rwa [sl23_pCore_eq_Q8, mem_sl23Q8] at h
  have h4b : (e ⟨b, hbX⟩) ^ 4 = 1 := by
    have h := map_pCore_mem e hbP
    rwa [sl23_pCore_eq_Q8, mem_sl23Q8] at h
  have hq := sl23_q8_comm_sq (e ⟨a, haX⟩) (e ⟨b, hbX⟩) h4a h4b
  constructor
  · let c : ↥X := ⟨a, haX⟩ * ⟨b, hbX⟩ * ⟨a, haX⟩⁻¹ * ⟨b, hbX⟩⁻¹
    have hcval : (c : G) = a * b * a⁻¹ * b⁻¹ := by simp [c]
    have hec : e c = e ⟨a, haX⟩ * e ⟨b, hbX⟩ * (e ⟨a, haX⟩)⁻¹ * (e ⟨b, hbX⟩)⁻¹ := by
      simp only [c, map_mul, map_inv]
    rw [← hcval]
    rcases hq.1 with h | h
    · have hc1 : c = 1 := by
        apply e.injective
        rw [hec, h, map_one]
      rw [hc1]
      exact Subgroup.one_mem _
    · have hcw : c = ⟨w, hw⟩ := by
        apply e.injective
        rw [hec, h, hew]
      rw [hcw]
      exact Subgroup.mem_zpowers w
  · let d : ↥X := ⟨a, haX⟩ * ⟨a, haX⟩
    have hdval : (d : G) = a * a := by simp [d]
    have hed : e d = e ⟨a, haX⟩ * e ⟨a, haX⟩ := by simp only [d, map_mul]
    rw [← hdval]
    rcases hq.2 with h | h
    · have hd1 : d = 1 := by
        apply e.injective
        rw [hed, h, map_one]
      rw [hd1]
      exact Subgroup.one_mem _
    · have hdw : d = ⟨w, hw⟩ := by
        apply e.injective
        rw [hed, h, hew]
      rw [hdw]
      exact Subgroup.mem_zpowers w

private theorem commutator_prod_of_commute {Q1 Q2 : Subgroup G}
    (hc : ∀ a ∈ Q1, ∀ b ∈ Q2, a * b = b * a)
    {a1 b1 a2 b2 : G} (ha1 : a1 ∈ Q1) (hb1 : b1 ∈ Q1) (ha2 : a2 ∈ Q2) (hb2 : b2 ∈ Q2) :
    ⁅a1 * a2, b1 * b2⁆ = ⁅a1, b1⁆ * ⁅a2, b2⁆ := by
  have h21 : ⁅a2, b1⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc b1 hb1 a2 ha2).symm
  have h12 : ⁅a1, b2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc a1 ha1 b2 hb2)
  have hX : ⁅a2, b2⁆ ∈ Q2 :=
    Subgroup.commutator_le_self Q2 (Subgroup.commutator_mem_commutator ha2 hb2)
  have haX : a1 * ⁅a2, b2⁆ * a1⁻¹ = ⁅a2, b2⁆ := by
    rw [hc a1 ha1 ⁅a2, b2⁆ hX, mul_assoc, mul_inv_cancel, mul_one]
  have hbX : b1 * ⁅a2, b2⁆ * b1⁻¹ = ⁅a2, b2⁆ := by
    rw [hc b1 hb1 ⁅a2, b2⁆ hX, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅a1 * a2, b1 * b2⁆
      = (a1 * ⁅a2, b1⁆ * a1⁻¹ * ⁅a1, b1⁆) * b1 *
          (a1 * ⁅a2, b2⁆ * a1⁻¹ * ⁅a1, b2⁆) * b1⁻¹ := by
        rw [commutatorElement_mul_right_eq_mul_conj,
            commutatorElement_mul_left_eq_conj_mul,
            commutatorElement_mul_left_eq_conj_mul]
    _ = ⁅a1, b1⁆ * b1 * (a1 * ⁅a2, b2⁆ * a1⁻¹) * b1⁻¹ := by
        rw [h21, h12]
        group
    _ = ⁅a1, b1⁆ * b1 * ⁅a2, b2⁆ * b1⁻¹ := by rw [haX]
    _ = ⁅a1, b1⁆ * (b1 * ⁅a2, b2⁆ * b1⁻¹) := by group
    _ = ⁅a1, b1⁆ * ⁅a2, b2⁆ := by rw [hbX]

private theorem square_prod_of_commute {Q1 Q2 : Subgroup G}
    (hc : ∀ a ∈ Q1, ∀ b ∈ Q2, a * b = b * a)
    {a1 a2 : G} (ha1 : a1 ∈ Q1) (ha2 : a2 ∈ Q2) :
    (a1 * a2) * (a1 * a2) = (a1 * a1) * (a2 * a2) := by
  calc (a1 * a2) * (a1 * a2) = a1 * (a2 * a1) * a2 := by group
    _ = a1 * (a1 * a2) * a2 := by rw [(hc a1 ha1 a2 ha2).symm]
    _ = (a1 * a1) * (a2 * a2) := by group

theorem sec10KS_Qi_elem [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ a ∈ twoCoreIn K1, ∀ b ∈ twoCoreIn K1,
      a * b * a⁻¹ * b⁻¹ ∈ zpowers z ∧ a * a ∈ zpowers z := by
  obtain ⟨e⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  have hw2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  exact sl23_transfer e hzK1 (map_w_eq_neg_one e hzK1 hw2)

theorem sec10KS_twoCore_sup [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    secQ K1 K2 = twoCoreIn K1 ⊔ twoCoreIn K2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  obtain ⟨e2⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).2
  set Q1 : Subgroup G := twoCoreIn K1 with hQ1
  set Q2 : Subgroup G := twoCoreIn K2 with hQ2
  set P : Subgroup G := Q1 ⊔ Q2 with hP
  set K : Subgroup G := K1 ⊔ K2 with hK
  have hw2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  have hzK2 : z ∈ K2 := hctx.pocket2.1
  have hcomm : ∀ a ∈ Q1, ∀ b ∈ Q2, a * b = b * a := by
    intro a ha b hb
    exact sec10Z_comm hP5 hpsp hctx a (twoCoreIn_le K1 (hQ1 ▸ ha)) b (twoCoreIn_le K2 (hQ2 ▸ hb))
  have hcardQ1 : Nat.card Q1 = 8 := hQ1 ▸ card_twoCoreIn K1 e1
  have hcardQ2 : Nat.card Q2 = 8 := hQ2 ▸ card_twoCoreIn K2 e2
  have hzQ1 : z ∈ Q1 := by
    rw [hQ1, mem_twoCoreIn_iff hzK1]
    have hmem : e1 ⟨z, hzK1⟩ ∈ CFSG.pCore 2 SL23 := by
      rw [map_w_eq_neg_one e1 hzK1 hw2]
      exact sl23_neg_one_mem_pCore
    have hmap := CFSG.pCore_map_iso 2 e1
    rw [← hmap] at hmem
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
    have hy' : y = ⟨z, hzK1⟩ := e1.injective hye
    rwa [hy'] at hy
  have hzQ2 : z ∈ Q2 := by
    rw [hQ2, mem_twoCoreIn_iff hzK2]
    have hmem : e2 ⟨z, hzK2⟩ ∈ CFSG.pCore 2 SL23 := by
      rw [map_w_eq_neg_one e2 hzK2 hw2]
      exact sl23_neg_one_mem_pCore
    have hmap := CFSG.pCore_map_iso 2 e2
    rw [← hmap] at hmem
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
    have hy' : y = ⟨z, hzK2⟩ := e2.injective hye
    rwa [hy'] at hy
  have hinf : Q1 ⊓ Q2 = zpowers z := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hzQ1, hzQ2⟩)
    calc Q1 ⊓ Q2 ≤ K1 ⊓ K2 := inf_le_inf (hQ1 ▸ twoCoreIn_le K1) (hQ2 ▸ twoCoreIn_le K2)
      _ = zpowers z := (sec10KS_main hP5 hC5 hpsp hctx).2.2
  have hcardP : Nat.card P = 32 := by
    have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute Q1 Q2 hcomm).1
    rw [hinf, Nat.card_zpowers, hw2, hcardQ1, hcardQ2] at h
    rw [hP]
    omega
  have hP2 : IsPGroup 2 P := by
    apply IsPGroup.of_card (n := 5)
    rw [hcardP]
    norm_num
  have hPK : P ≤ K := by
    rw [hP, hK]
    exact sup_le ((hQ1 ▸ twoCoreIn_le K1).trans le_sup_left)
      ((hQ2 ▸ twoCoreIn_le K2).trans le_sup_right)
  have hK1Q1 : K1 ≤ normalizer (Q1 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hQ1 ▸ twoCoreIn_le K1)).mp
      (hQ1 ▸ twoCoreIn_normal_in K1)
  have hK1cen : K1 ≤ centralizer (Q2 : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (sec10Z_comm hP5 hpsp hctx k hk q (twoCoreIn_le K2 (hQ2 ▸ hq))).symm
  have hK1Q2 : K1 ≤ normalizer (Q2 : Set G) :=
    hK1cen.trans (Subgroup.centralizer_le_normalizer (Q2 : Set G))
  have hK2Q2 : K2 ≤ normalizer (Q2 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hQ2 ▸ twoCoreIn_le K2)).mp
      (hQ2 ▸ twoCoreIn_normal_in K2)
  have hK2cen : K2 ≤ centralizer (Q1 : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact sec10Z_comm hP5 hpsp hctx q (twoCoreIn_le K1 (hQ1 ▸ hq)) k hk
  have hK2Q1 : K2 ≤ normalizer (Q1 : Set G) :=
    hK2cen.trans (Subgroup.centralizer_le_normalizer (Q1 : Set G))
  have hK1P : K1 ≤ normalizer (P : Set G) := by
    rw [hP]
    exact (le_inf hK1Q1 hK1Q2).trans (Subgroup.inf_normalizer_le_normalizer_sup Q1 Q2)
  have hK2P : K2 ≤ normalizer (P : Set G) := by
    rw [hP]
    exact (le_inf hK2Q1 hK2Q2).trans (Subgroup.inf_normalizer_le_normalizer_sup Q1 Q2)
  have hPnorm : (P.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr (by rw [hK]; exact sup_le hK1P hK2P)
  have hPle : P ≤ secQ K1 K2 := by
    have hP2' : IsPGroup 2 (P.subgroupOf K) := hP2.comap_subtype
    have hle : P.subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hPnorm, hP2'⟩
    calc P = (P.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hPK).symm
      _ ≤ (CFSG.pCore 2 ↥K).map K.subtype := Subgroup.map_mono hle
      _ = secQ K1 K2 := by rw [secQ, twoCoreIn, CFSG.inSubgroup, hK]
  have hRle : secQ K1 K2 ≤ P := by
    have hR2 : IsPGroup 2 (twoCoreIn K) := by
      rw [hK]
      unfold twoCoreIn CFSG.inSubgroup
      exact (CFSG.pCore_isPGroup (G := ↥(K1 ⊔ K2)) (p := 2)).map (K1 ⊔ K2).subtype
    have hR2' : IsPGroup 2 ((twoCoreIn K).subgroupOf K) := hR2.comap_subtype
    haveI : ((twoCoreIn K).subgroupOf K).Normal := twoCoreIn_normal_in K
    have hP2' : IsPGroup 2 (P.subgroupOf K) := hP2.comap_subtype
    have hKcard : Nat.card ↥K = 288 := sec10KS_card_sup hP5 hC5 hpsp hctx
    have hindex : (P.subgroupOf K).index = 9 := by
      have h := (P.subgroupOf K).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hcardP, hKcard] at h
      omega
    have hnotdvd : ¬ 2 ∣ (P.subgroupOf K).index := by
      rw [hindex]
      norm_num
    let S : Sylow 2 ↥K := hP2'.toSylow hnotdvd
    have hScoe : (S : Subgroup ↥K) = P.subgroupOf K := IsPGroup.toSylow_coe hP2' hnotdvd
    have hleR : (twoCoreIn K).subgroupOf K ≤ (S : Subgroup ↥K) := hR2'.le_sylow_of_normal S
    intro x hx
    have hxR : (⟨x, twoCoreIn_le K hx⟩ : ↥K) ∈ (twoCoreIn K).subgroupOf K := hx
    have hxS : (⟨x, twoCoreIn_le K hx⟩ : ↥K) ∈ (S : Subgroup ↥K) := hleR hxR
    rw [hScoe] at hxS
    exact hxS
  exact le_antisymm hRle hPle

theorem sec10KS_Q_elem [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    z ∈ secQ K1 K2 ∧ ∀ a ∈ secQ K1 K2, ∀ b ∈ secQ K1 K2,
      a * b * a⁻¹ * b⁻¹ ∈ zpowers z ∧ a * a ∈ zpowers z := by
  have hQ1 := sec10KS_Qi_elem hP5 hC5 hpsp hctx
  have hQ2 := sec10KS_Qi_elem hP5 hC5 hpsp hctx.swap
  have hcomm : ∀ a ∈ twoCoreIn K1, ∀ b ∈ twoCoreIn K2, a * b = b * a := by
    intro a ha b hb
    exact sec10Z_comm hP5 hpsp hctx a (twoCoreIn_le K1 ha) b (twoCoreIn_le K2 hb)
  have hw2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  have hzQ1 : z ∈ twoCoreIn K1 := by
    obtain ⟨e1⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
    rw [mem_twoCoreIn_iff hzK1]
    have hmem : e1 ⟨z, hzK1⟩ ∈ CFSG.pCore 2 SL23 := by
      rw [map_w_eq_neg_one e1 hzK1 hw2]
      exact sl23_neg_one_mem_pCore
    have hmap := CFSG.pCore_map_iso 2 e1
    rw [← hmap] at hmem
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
    have hy' : y = ⟨z, hzK1⟩ := e1.injective hye
    rwa [hy'] at hy
  rw [sec10KS_twoCore_sup hP5 hC5 hpsp hctx]
  refine ⟨Subgroup.mem_sup_left hzQ1, ?_⟩
  intro a ha b hb
  obtain ⟨a1, ha1, a2, ha2, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm ha
  obtain ⟨b1, hb1, b2, hb2, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hb
  constructor
  · rw [← commutatorElement_def,
      commutator_prod_of_commute hcomm ha1 hb1 ha2 hb2,
      commutatorElement_def, commutatorElement_def]
    exact Subgroup.mul_mem _ (hQ1 a1 ha1 b1 hb1).1 (hQ2 a2 ha2 b2 hb2).1
  · rw [square_prod_of_commute hcomm ha1 ha2]
    exact Subgroup.mul_mem _ (hQ1 a1 ha1 a1 ha1).2 (hQ2 a2 ha2 a2 ha2).2

end CFSG.OddStandard.SmallF3.Omega
