module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerCliff
public import CFSG.RankThree.FFModules.Offenders

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules Module

section Absorb

variable {K : Type*} [Group K] {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z] {L B : Subgroup K}

theorem InnerCtx.invariant_of_stab (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    {Y : Submodule (ZMod 2) Z} (hL : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y)
    (hB : ∀ b ∈ B, ∀ y ∈ Y, κ b y ∈ Y) : ∀ k : K, ∀ y ∈ Y, κ k y ∈ Y := by
  haveI := h.normal_L
  intro k y hy
  have hk : k ∈ L ⊔ B := by rw [h.top]; exact Subgroup.mem_top k
  obtain ⟨l, hl, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk
  rw [repMulApply]
  exact hL l hl _ (hB b hb y hy)

theorem LMin.eq_top_of_stab (h : InnerCtx L B) {κ : Representation (ZMod 2) K Z}
    (hd : ChiefData L B κ) {Y : Submodule (ZMod 2) Z} (hY : LMin L κ Y)
    (hB : ∀ b ∈ B, b ∈ stabIn h κ Y) : Y = ⊤ :=
  (hd.irr Y (h.invariant_of_stab κ hY.inv fun b hb => (hB b hb).2)).resolve_left hY.ne_bot

theorem finrank_absorb [Finite Z] (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    {Y : Submodule (ZMod 2) Z} (hY : LMin L κ Y) {a : K} (ha : a ∈ B)
    (hna : a ∉ stabIn h κ Y) :
    finrank (ZMod 2) ↥(fixSub κ B) + 2 * finrank (ZMod 2) ↥Y ≤
      finrank (ZMod 2) Z + finrank (ZMod 2) ↥(fixSub κ (stabIn h κ Y) ⊓ Y) := by
  haveI : Module.Finite (ZMod 2) Z := Module.Finite.of_finite
  have hbot := inf_translate_eq_bot h κ hY ha hna
  have hinvol : ∀ z, κ a (κ a z) = z := fun z => by
    rw [← repMulApply, h.sq a ha, map_one]
    rfl
  have hinj : Function.Injective (κ a) := fun x y hxy => by
    rw [← hinvol x, ← hinvol y, hxy]
  have hdim' : finrank (ZMod 2) ↥(Y.map (κ a)) = finrank (ZMod 2) ↥Y :=
    (Submodule.equivMapOfInjective (κ a) hinj Y).finrank_eq.symm
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Y (Y.map (κ a))
  rw [hbot, finrank_bot, add_zero, hdim'] at hsum
  have hsum2 := Submodule.finrank_sup_add_finrank_inf_eq (fixSub κ B) (Y ⊔ Y.map (κ a))
  have hle1 : finrank (ZMod 2) ↥(fixSub κ B ⊔ (Y ⊔ Y.map (κ a))) ≤ finrank (ZMod 2) Z :=
    Submodule.finrank_le _
  have hsub : fixSub κ B ⊓ (Y ⊔ Y.map (κ a)) ≤
      (fixSub κ (stabIn h κ Y) ⊓ Y).map (LinearMap.id + κ a) := by
    rintro w ⟨hwB, hwT⟩
    obtain ⟨y, hy, _, ⟨y'', hy'', rfl⟩, rfl⟩ := Submodule.mem_sup.mp hwT
    have hfix : κ a (y + κ a y'') = y + κ a y'' := mem_fixSub.mp hwB a ha
    rw [map_add, hinvol] at hfix
    have hd : κ a (y - y'') = y - y'' := by
      rw [map_sub]
      exact (sub_eq_sub_iff_add_eq_add).mpr hfix
    have hd0 : y - y'' = 0 := by
      have hm : y - y'' ∈ Y ⊓ Y.map (κ a) :=
        ⟨Y.sub_mem hy hy'', ⟨y - y'', Y.sub_mem hy hy'', hd⟩⟩
      rw [hbot] at hm
      exact (Submodule.mem_bot _).mp hm
    have hyy : y'' = y := (sub_eq_zero.mp hd0).symm
    rw [hyy] at hwB ⊢
    refine ⟨y, ⟨mem_fixSub.mpr fun b hb => ?_, hy⟩, rfl⟩
    have hwb : κ b (y + κ a y) = y + κ a y := mem_fixSub.mp hwB b hb.1
    have hcomm : κ b (κ a y) = κ a (κ b y) := by
      rw [← repMulApply, ← repMulApply, h.comm b hb.1 a ha]
    rw [map_add, hcomm] at hwb
    have he : (κ b y - y) + κ a (κ b y - y) = 0 := by
      have h1 : (κ b y - y) + κ a (κ b y - y) =
          (κ b y + κ a (κ b y)) - (y + κ a y) := by
        rw [map_sub]
        abel
      rw [h1, hwb, sub_self]
    have hemem : κ b y - y ∈ Y := Y.sub_mem (hb.2 y hy) hy
    have hae : κ a (κ b y - y) = -(κ b y - y) := eq_neg_of_add_eq_zero_right he
    have hem : κ b y - y ∈ Y ⊓ Y.map (κ a) :=
      ⟨hemem, ⟨-(κ b y - y), Y.neg_mem hemem, by rw [map_neg, hae, neg_neg]⟩⟩
    rw [hbot] at hem
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp hem)
  have hle2 : finrank (ZMod 2) ↥(fixSub κ B ⊓ (Y ⊔ Y.map (κ a))) ≤
      finrank (ZMod 2) ↥(fixSub κ (stabIn h κ Y) ⊓ Y) :=
    (Submodule.finrank_mono hsub).trans (Submodule.finrank_map_le _ _)
  omega

theorem card_absorb [Finite Z] (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    {Y : Submodule (ZMod 2) Z} (hY : LMin L κ Y) {a : K} (ha : a ∈ B)
    (hna : a ∉ stabIn h κ Y) :
    Nat.card ↥(fixSub κ B) * Nat.card ↥Y ^ 2 ≤
      Nat.card Z * Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) := by
  have hfr := finrank_absorb h κ hY ha hna
  rw [card_eq_two_pow_finrank (fixSub κ B), card_eq_two_pow_finrank Y, card_eq_two_pow_finrank',
    card_eq_two_pow_finrank (fixSub κ (stabIn h κ Y) ⊓ Y), ← pow_mul, ← pow_add, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_inner_sq_le [Finite Z] (h : InnerCtx L B) {κ : Representation (ZMod 2) K Z}
    (hd : ChiefData L B κ) {Y : Submodule (ZMod 2) Z} (hY : LMin L κ Y) {a : K} (ha : a ∈ B)
    (hna : a ∉ stabIn h κ Y) :
    Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥Y ^ 2 ≤
      Nat.card ↥B * Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) := by
  haveI := hd.nontrivial
  have hbud := hd.budget
  have hfix : Nat.card {z : Z // ∀ b ∈ B, κ b z = z} = Nat.card ↥(fixSub κ B) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z => mem_fixSub.symm)
  rw [hfix] at hbud
  have habs := card_absorb h κ hY ha hna
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hZpos
  calc Nat.card Z * (Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥Y ^ 2)
      = (Nat.card Z * Nat.card ↥(B ⊓ MonoidHom.ker κ)) * Nat.card ↥Y ^ 2 := by ring
    _ ≤ (Nat.card ↥B * Nat.card ↥(fixSub κ B)) * Nat.card ↥Y ^ 2 :=
        Nat.mul_le_mul_right _ hbud
    _ = Nat.card ↥B * (Nat.card ↥(fixSub κ B) * Nat.card ↥Y ^ 2) := by ring
    _ ≤ Nat.card ↥B * (Nat.card Z * Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y)) :=
        Nat.mul_le_mul_left _ habs
    _ = Nat.card Z * (Nat.card ↥B * Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y)) := by ring

end Absorb

end CFSG.LocalAnalysis.RankThreeUC.S15
