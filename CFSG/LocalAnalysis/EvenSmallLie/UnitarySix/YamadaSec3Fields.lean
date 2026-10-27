module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Objects

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (conjR mem_conjR conjR_inf conjR_sup)

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

@[expose] noncomputable def tw (w : List ℕ) (hw : ∀ k ∈ w, k < 18) : T46 :=
  ⟨wP w, wP_mem_T46 w hw⟩

theorem psiT_yamGen {k : ℕ} (hk : k < 18) :
    psiT (yamGen k) = tw [k] (by simpa using hk) :=
  Subtype.ext (by rw [coe_psiT, psi0_yamGen hk]; simp [tw, wP])

theorem psiT_yamWord : ∀ (w : List ℕ) (hw : ∀ k ∈ w, k < 18), psiT (yamWord w) = tw w hw
  | [], _ => by simp [yamWord, tw, wP]; rfl
  | k :: w, hw => by
    have hk := hw k List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 18 := fun j hj => hw j (List.mem_cons_of_mem k hj)
    rw [yamWord, List.map_cons, List.prod_cons, map_mul, psiT_yamGen hk]
    have := psiT_yamWord w hw'
    rw [yamWord] at this
    rw [this]
    apply Subtype.ext
    simp [tw, wP]

theorem tw_mul (a b : List ℕ) (ha : ∀ k ∈ a, k < 18) (hb : ∀ k ∈ b, k < 18) :
    tw a ha * tw b hb = tw (a ++ b) (fun k hk => (List.mem_append.1 hk).elim (ha k) (hb k)) :=
  Subtype.ext (by simp [tw, wP, List.map_append, List.prod_append])

theorem sw_eq (i : ℕ) (hi : i < 3) : sw e i = iotaG e (tw [15 + i] (by simp; omega)) := by
  rw [sw, phiG_apply, psiT_yamGen (by omega)]

theorem sw0 : sw e 0 = iotaG e (tw [15] (by decide)) := sw_eq 0 (by norm_num)

theorem sw1 : sw e 1 = iotaG e (tw [16] (by decide)) := sw_eq 1 (by norm_num)

theorem sw2 : sw e 2 = iotaG e (tw [17] (by decide)) := sw_eq 2 (by norm_num)

theorem iotaG_tw_mul (a b : List ℕ) (ha : ∀ k ∈ a, k < 18) (hb : ∀ k ∈ b, k < 18) :
    iotaG e (tw a ha) * iotaG e (tw b hb) =
      iotaG e (tw (a ++ b) (fun k hk => (List.mem_append.1 hk).elim (ha k) (hb k))) := by
  rw [← map_mul, tw_mul]

theorem u₁_eq : sw e 0 * sw e 1 * sw e 2 * sw e 1 * sw e 0 =
    iotaG e (tw [15, 16, 17, 16, 15] (by decide)) := by
  simp only [sw0, sw1, sw2, iotaG_tw_mul]
  rfl

theorem u₂_eq : sw e 2 * sw e 1 * sw e 2 * sw e 0 * sw e 1 * sw e 2 =
    iotaG e (tw [17, 16, 17, 15, 16, 17] (by decide)) := by
  simp only [sw0, sw1, sw2, iotaG_tw_mul]
  rfl

theorem w₀_eq : (sw e 0 * sw e 1 * sw e 2) ^ 3 =
    iotaG e (tw [15, 16, 17, 15, 16, 17, 15, 16, 17] (by decide)) := by
  simp only [pow_succ, pow_zero, one_mul, sw0, sw1, sw2, iotaG_tw_mul]
  rfl

theorem ab_eq : sw e 0 * sw e 1 = iotaG e (tw [15, 16] (by decide)) := by
  simp only [sw0, sw1, iotaG_tw_mul]
  rfl

theorem ba_eq : sw e 1 * sw e 0 = iotaG e (tw [16, 15] (by decide)) := by
  simp only [sw0, sw1, iotaG_tw_mul]
  rfl

theorem aba_eq : sw e 0 * sw e 1 * sw e 0 = iotaG e (tw [15, 16, 15] (by decide)) := by
  simp only [sw0, sw1, iotaG_tw_mul]
  rfl

theorem bcb_eq : sw e 1 * sw e 2 * sw e 1 = iotaG e (tw [16, 17, 16] (by decide)) := by
  simp only [sw1, sw2, iotaG_tw_mul]
  rfl

theorem card_sS : Nat.card (sS e) = 2 ^ 15 := by
  rw [sS, card_toG (grp_le_T46 gensOK_chS), card_chS]
  norm_num

theorem sS_le_L : sS e ≤ L := toG_le_L _

theorem card_sX₁ : Nat.card (sX₁ e) = 4 := by
  rw [sX₁, card_toG (grp_le_T46 gensOK_chX1), card_chX1]

theorem card_sX₂ : Nat.card (sX₂ e) = 4 := by
  rw [sX₂, card_toG (grp_le_T46 gensOK_chX2), card_chX2]

theorem card_sX₃ : Nat.card (sX₃ e) = 2 := by
  rw [sX₃, card_toG (grp_le_T46 gensOK_chX3), card_chX3]

theorem card_L (e : L ≃* T46) : Nat.card L = 9196830720 := by
  rw [Nat.card_congr e.toEquiv, card_T46]

theorem isSylowOf_sS [Finite G] : CFSG.ABGLocalTools.IsSylowOf 2 (sS e) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨sS_le_L, IsPGroup.of_card card_sS, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := sS e) (K := L)
  rw [inf_eq_left.2 sS_le_L, card_sS, card_L e] at h
  have h' : (sS e).relIndex L = 280665 := by omega
  rw [h']
  decide

theorem card_normalizer_sS : Nat.card (normalizer (sS e : Set G) ⊓ L : Subgroup G) = 2 ^ 15 * 3 := by
  rw [sS, normalizer_toG (grp_le_T46 gensOK_chS), normalizer_S_eq,
    card_toG (grp_le_T46 gensOK_chSJ), card_chSJ]
  norm_num

theorem sA₁_le : sA₁ e ≤ sS e := toG_mono chA1_le_chS

theorem sA₂_le : sA₂ e ≤ sS e := toG_mono chA2_le_chS

theorem sK₁_le : sK₁ e ≤ L := toG_le_L _

theorem sK₂_le : sK₂ e ≤ L := toG_le_L _

theorem sK₁_inf_sA₁ : sK₁ e ⊓ sA₁ e = ⊥ := by
  rw [sK₁, sA₁, ← toG_inf, K1_inf_A1, toG_bot]

theorem sK₂_inf_sA₂ : sK₂ e ⊓ sA₂ e = ⊥ := by
  rw [sK₂, sA₂, ← toG_inf, K2_inf_A2, toG_bot]

theorem KA₁_eq : (sK₁ e ⊔ sA₁ e) ⊓ conjR (sK₁ e ⊔ sA₁ e)
    (sw e 0 * sw e 1 * sw e 2 * sw e 1 * sw e 0) = sK₁ e := by
  rw [sK₁, sA₁, ← toG_sup (grp_le_T46 gensOK_chK1) (grp_le_T46 gensOK_chA1), u₁_eq, conjR_toG,
    ← toG_inf]
  exact congrArg (toG e) KA1_inf

theorem KA₂_eq : (sK₂ e ⊔ sA₂ e) ⊓ conjR (sK₂ e ⊔ sA₂ e)
    (sw e 2 * sw e 1 * sw e 2 * sw e 0 * sw e 1 * sw e 2) = sK₂ e := by
  rw [sK₂, sA₂, ← toG_sup (grp_le_T46 gensOK_chK2) (grp_le_T46 gensOK_chA2), u₂_eq, conjR_toG,
    ← toG_inf]
  exact congrArg (toG e) KA2_inf

theorem S_w₀_eq : sS e ⊓ conjR (sS e) ((sw e 0 * sw e 1 * sw e 2) ^ 3) = ⊥ := by
  rw [sS, w₀_eq, conjR_toG, ← toG_inf]
  rw [show (tw [15, 16, 17, 15, 16, 17, 15, 16, 17] (by decide) : Equiv.Perm (Fin 693)) = pw₀
    from rfl, S_inf_w₀, toG_bot]

theorem S_u₂_eq : sS e ⊓ conjR (sS e) (sw e 2 * sw e 1 * sw e 2 * sw e 0 * sw e 1 * sw e 2) =
    toG e chT2.grp := by
  rw [sS, u₂_eq, conjR_toG, ← toG_inf]
  exact congrArg (toG e) S_inf_u₂

theorem S_u₁_eq : sS e ⊓ conjR (sS e) (sw e 0 * sw e 1 * sw e 2 * sw e 1 * sw e 0) =
    toG e chT1.grp := by
  rw [sS, u₁_eq, conjR_toG, ← toG_inf]
  exact congrArg (toG e) S_inf_u₁

theorem S_a_eq : toG e chT2.grp ⊓ conjR (toG e chT2.grp) (sw e 0 * sw e 1) = sX₁ e := by
  rw [ab_eq, conjR_toG, ← toG_inf]
  exact congrArg (toG e) T2_inf_ab

theorem S_b_eq : toG e chT2.grp ⊓ conjR (toG e chT2.grp) (sw e 1 * sw e 0) = sX₂ e := by
  rw [ba_eq, conjR_toG, ← toG_inf]
  exact congrArg (toG e) T2_inf_ba

theorem S_aba_eq : toG e chT2.grp ⊓ conjR (toG e chT2.grp) (sw e 0 * sw e 1 * sw e 0) = ⊥ := by
  rw [aba_eq, conjR_toG, ← toG_inf]
  rw [show (tw [15, 16, 15] (by decide) : Equiv.Perm (Fin 693)) = paba from rfl, T2_inf_aba,
    toG_bot]

theorem S_c_eq : toG e chT1.grp ⊓ conjR (toG e chT1.grp) (sw e 1 * sw e 2 * sw e 1) = sX₃ e := by
  rw [bcb_eq, conjR_toG, ← toG_inf]
  exact congrArg (toG e) T1_inf_bcb

theorem card_T2 : Nat.card (toG e chT2.grp) = 2 ^ 6 := by
  rw [card_toG (grp_le_T46 gensOK_chT2), card_chT2]
  norm_num

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
