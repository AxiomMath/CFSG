module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerConcl
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Rep
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Out
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Natural
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Linear
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Count

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThree.FFModules

theorem core_inner_sp4 {K : Type} [Group K] [Finite K]
    {L B : Subgroup K} (h : InnerCtx L B)
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (e : ↥L ≃* StatedSp 2 F) {Z : Type} [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]
    {κ : Representation (ZMod 2) K Z} (hd : ChiefData L B κ) :
    ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l := by
  classical
  have := hd.nontrivial
  have hNatF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hNatF
  have hq4 : 4 ≤ Nat.card F := by
    rw [hNatF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hperf : commutator ↥L = ⊤ := h.quasi.1
  obtain ⟨Y, hY⟩ := exists_lMin L κ
  have hnt := hY.nontriv h hd
  have hY4 : 4 < Nat.card ↥Y := inner_four_lt_card hperf hY.inv hnt
  have hBN : B ≤ Subgroup.normalizer (L : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_L]
    exact le_top
  have hrel := relIndex_innerPart_le_two_sp4 L B hn hNatF e hBN h.sq
  have hinn : innerPart L B ≤ stabIn h κ Y := innerPart_le_stab h κ hd.irr hY.inv
  have hrel' : Nat.card ↥(innerPart L B) * (innerPart L B).relIndex B = Nat.card ↥B := by
    have h1 := Subgroup.card_mul_index ((innerPart L B).subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (innerPart_le L B)).toEquiv] at h1
    exact h1
  have hcardle : Nat.card ↥(innerPart L B) ≤ Nat.card ↥(stabIn h κ Y) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hinn) (Subgroup.inclusion_injective hinn)
  have hB2 : Nat.card ↥B ≤ 2 * Nat.card ↥(stabIn h κ Y) := by
    rw [← hrel']
    calc Nat.card ↥(innerPart L B) * (innerPart L B).relIndex B
        ≤ Nat.card ↥(innerPart L B) * 2 := Nat.mul_le_mul_left _ hrel
      _ ≤ Nat.card ↥(stabIn h κ Y) * 2 := Nat.mul_le_mul_right _ hcardle
      _ = 2 * Nat.card ↥(stabIn h κ Y) := by ring
  have hcard := card_stabIn h hd hY hnt
  have hfixcard := card_fix_stabImage h κ Y
  have hNpos : 0 < Nat.card ↥(B ⊓ MonoidHom.ker κ) := Nat.card_pos
  have hπinj := rhoYSp_injective h e hY.inv hnt
  have hirr := rhoYSp_irr e hY
  have hnorm := stabImage_normalizes_rhoYSp h e κ Y hY.inv
  have hAe : CFSG.IsElementaryAbelian 2 ↥(stabImage h κ Y) :=
    CFSG.IsElementaryAbelian.two_of_forall_mul_self (stabImage_comm h κ Y) (stabImage_sq h κ Y)
  have hYnt : Nontrivial ↥Y := Submodule.nontrivial_iff_ne_bot.mpr hY.ne_bot
  by_cases hall : ∀ b ∈ B, b ∈ stabIn h κ Y
  ·
    have hYtop : Y = ⊤ := hY.eq_top_of_stab h hd hall
    have hB1 : stabIn h κ Y = B := le_antisymm (stabIn_le h κ Y) hall
    have hBcard : Nat.card ↥B = Nat.card ↥(stabIn h κ Y) := by rw [hB1]
    have hYZ : Nat.card ↥Y = Nat.card Z := by
      rw [hYtop]
      exact Nat.card_congr Submodule.topEquiv.toEquiv
    have hzY : ∀ z : Z, z ∈ Y := fun z => by rw [hYtop]; exact Submodule.mem_top
    have hfixZ : Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) =
        Nat.card {z : Z // ∀ b ∈ B, κ b z = z} :=
      Nat.card_congr
        { toFun := fun w => ⟨w.1, fun b hb => mem_fixSub.mp w.2.1 b (hall b hb)⟩
          invFun := fun z => ⟨z.1, mem_fixSub.mpr fun b hb => z.2 b hb.1, hzY z.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have e1 : Nat.card Z * Nat.card ↥(B ⊓ MonoidHom.ker κ) ≤
        (Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥(stabImage h κ Y)) *
          Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} := by
      have hb := hd.budget
      rw [hBcard, hcard, ← hfixZ, ← hfixcard] at hb
      exact hb
    have hoff : Nat.card ↥Y ≤ Nat.card ↥(stabImage h κ Y) *
        Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} := by
      refine Nat.le_of_mul_le_mul_left ?_ hNpos
      calc Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥Y
          = Nat.card Z * Nat.card ↥(B ⊓ MonoidHom.ker κ) := by rw [hYZ, mul_comm]
        _ ≤ (Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥(stabImage h κ Y)) *
            Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} := e1
        _ = Nat.card ↥(B ⊓ MonoidHom.ker κ) * (Nat.card ↥(stabImage h κ Y) *
            Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y}) := by ring
    by_cases hA0 : stabImage h κ Y = ⊥
    ·
      intro b hb
      refine ⟨1, L.one_mem, h.conjAgree_of_kappa_eq κ hd.hL fun z => ?_⟩
      have hmem : repGL (stabRep h κ Y) ⟨b, hall b hb⟩ ∈ stabImage h κ Y :=
        ⟨⟨b, hall b hb⟩, rfl⟩
      rw [hA0, Subgroup.mem_bot] at hmem
      have h1 := congrArg (fun a : ↥Y ≃ₗ[ZMod 2] ↥Y => ((a ⟨z, hzY z⟩ : ↥Y) : Z)) hmem
      rw [map_one]
      exact h1
    ·
      obtain ⟨α, φ, hφ⟩ := exists_natural_statedSp_of_offender hn hNatF
        (rhoYSp e κ Y hY.inv) hπinj hYnt hirr (stabImage h κ Y) hnorm hAe hA0 hoff
      have hrep := eq_rep_of_offender_of_natural_sp4 hn hNatF (rhoYSp e κ Y hY.inv) α φ hφ
        (stabImage h κ Y) hnorm hAe hoff
      intro b hb
      obtain ⟨x, hx⟩ := hrep (repGL (stabRep h κ Y) ⟨b, hall b hb⟩) ⟨⟨b, hall b hb⟩, rfl⟩
      refine ⟨((e.symm x : ↥L) : K), (e.symm x).2, h.conjAgree_of_kappa_eq κ hd.hL fun z => ?_⟩
      have h1 := congrArg Subtype.val (hx ⟨z, hzY z⟩)
      exact h1
  ·
    push Not at hall
    obtain ⟨a, ha, hna⟩ := hall
    exfalso
    have hsq2 := card_inner_sq_le h hd hY ha hna
    have hmain : Nat.card ↥Y * Nat.card ↥Y ≤ 2 * (Nat.card ↥(stabImage h κ Y) *
        Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y}) := by
      refine Nat.le_of_mul_le_mul_left ?_ hNpos
      calc Nat.card ↥(B ⊓ MonoidHom.ker κ) * (Nat.card ↥Y * Nat.card ↥Y)
          = Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥Y ^ 2 := by ring
        _ ≤ Nat.card ↥B * Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) := hsq2
        _ ≤ (2 * Nat.card ↥(stabIn h κ Y)) * Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) :=
            Nat.mul_le_mul_right _ hB2
        _ = Nat.card ↥(B ⊓ MonoidHom.ker κ) * (2 * (Nat.card ↥(stabImage h κ Y) *
            Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y})) := by
            rw [hcard, ← hfixcard]
            ring
    by_cases hA0 : stabImage h κ Y = ⊥
    · have h1 : Nat.card ↥(stabImage h κ Y) = 1 := by rw [hA0]; exact Subgroup.card_bot
      have h2 : Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} = Nat.card ↥Y :=
        Nat.card_congr (Equiv.subtypeUnivEquiv fun y a ha => by
          rw [hA0, Subgroup.mem_bot] at ha
          rw [ha]
          rfl)
      rw [h1, h2] at hmain
      have h5 : Nat.card ↥Y * 5 ≤ Nat.card ↥Y * Nat.card ↥Y := Nat.mul_le_mul_left _ hY4
      omega
    · have hoff1 : Nat.card ↥Y ≤ Nat.card ↥(stabImage h κ Y) *
          Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} := by
        by_contra hlt
        push Not at hlt
        nlinarith
      obtain ⟨α, φ, hφ⟩ := exists_natural_statedSp_of_offender hn hNatF
        (rhoYSp e κ Y hY.inv) hπinj hYnt hirr (stabImage h κ Y) hnorm hAe hA0 hoff1
      have hrep := eq_rep_of_offender_of_natural_sp4 hn hNatF (rhoYSp e κ Y hY.inv) α φ hφ
        (stabImage h κ Y) hnorm hAe hoff1
      have hcnt := card_mul_card_fix_le_of_natural_sp4 (rhoYSp e κ Y hY.inv) α φ hφ
        (stabImage h κ Y) hrep (stabImage_sq h κ Y)
      have hYcard : Nat.card ↥Y = Nat.card F ^ 4 := by
        rw [Nat.card_congr φ.toEquiv, Nat.card_fun]
        simp
      rw [hYcard] at hmain
      have h8 : Nat.card F ^ 5 * Nat.card F ^ 3 ≤ Nat.card F ^ 5 * 2 := by
        calc Nat.card F ^ 5 * Nat.card F ^ 3 = Nat.card F ^ 4 * Nat.card F ^ 4 := by ring
          _ ≤ 2 * (Nat.card ↥(stabImage h κ Y) *
              Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y}) := hmain
          _ ≤ 2 * Nat.card F ^ 5 := Nat.mul_le_mul_left _ hcnt
          _ = Nat.card F ^ 5 * 2 := by ring
      have hpos : 0 < Nat.card F ^ 5 := pow_pos (by omega) 5
      have h3 : Nat.card F ^ 3 ≤ 2 := Nat.le_of_mul_le_mul_left h8 hpos
      have h64 : 64 ≤ Nat.card F ^ 3 :=
        calc 64 = 4 ^ 3 := by norm_num
          _ ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hq4 3
      omega

end CFSG.LocalAnalysis.RankThreeUC.S15

end
