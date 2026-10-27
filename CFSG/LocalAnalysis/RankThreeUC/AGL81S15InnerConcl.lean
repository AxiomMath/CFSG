module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerNat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerOut
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerSemi
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerField
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerAbsorb

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Matrix CFSG.RankThree.FFModules
open scoped MatrixGroups

section YLevel

open CFSG.QuasithinUnique.Setup.X7a (Intertwines tauSL tauSL_tauSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (scalars)

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
  (hF : Fintype.card F = 2 ^ n) {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]
  (ρ : Representation (ZMod 2) SL(3, F) Y) (hirr : ρ.IsIrreducible)
  (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F) (A : Subgroup (Y ≃ₗ[ZMod 2] Y))
  (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
  (h2 : ∀ a ∈ A, a * a = 1) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
  (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w) (hA1 : A ≠ ⊥)

include hn hF hirr hker hA h2 hc hquad hA1

theorem inner_natural_semilinear
    (hoff : Nat.card Y ≤ Nat.card ↥A * Nat.card {y : Y // ∀ a ∈ A, a y = y}) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ x, ∃ g, ψ g = x) ∧ ∃ E : Y ≃+ (Fin 3 → F),
      (∀ g u, E (ρ g u) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E u) ∧
      ∀ a ∈ A, ∃ μ : F ≃+* F, ∀ (c : F) (y : Y),
        E (a (E.symm (c • E y))) = μ c • E (a y) := by
  haveI : CFSG.IsElementaryAbelian 2 ↥A := CFSG.IsElementaryAbelian.two_of_forall_mul_self hc h2
  obtain ⟨ψ, hψ, E, hE⟩ := CFSG.Quasithin.H13.L32A.C.SL3N.natural_of_offender' ρ hker A hA hn hF
    hirr hA1 hquad hoff
  have hsurj : ∀ x, ∃ g, ψ g = x := by
    rcases hψ with rfl | rfl
    · exact fun x => ⟨x, rfl⟩
    · exact fun x => ⟨tauSL F x, tauSL_tauSL x⟩
  refine ⟨ψ, hsurj, E, hE, fun a ha => ?_⟩
  let a' : (Fin 3 → F) ≃+ (Fin 3 → F) := E.symm.trans (a.toAddEquiv.trans E)
  have hnorm : ∀ g : SL(3, F), ∃ g' : SL(3, F), ∀ v : Fin 3 → F,
      a' ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (g' : Matrix (Fin 3) (Fin 3) F) *ᵥ a' v := by
    intro g
    obtain ⟨x, hx⟩ := hsurj g
    obtain ⟨y, hy⟩ := hA a ha x
    refine ⟨ψ y, fun v => ?_⟩
    obtain ⟨u, rfl⟩ := E.surjective v
    show E (a (E.symm ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ E u))) =
      ((ψ y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E (a (E.symm (E u)))
    rw [← hx, ← hE x u, E.symm_apply_apply, hy u, hE, E.symm_apply_apply]
  obtain ⟨μ, hμ⟩ := semilinear_of_normalizes hn hF a' hnorm
  refine ⟨μ, fun c y => ?_⟩
  have h1 : E (a (E.symm (c • E y))) = μ c • E (a (E.symm (E y))) := hμ c (E y)
  rw [E.symm_apply_apply] at h1
  exact h1

theorem inner_eq_rep_of_offender
    (hoff : Nat.card Y ≤ Nat.card ↥A * Nat.card {y : Y // ∀ a ∈ A, a y = y}) :
    ∀ a ∈ A, ∃ x : SL(3, F), ∀ y, a y = ρ x y := by
  obtain ⟨ψ, hsurj, E, hE, hsemi⟩ :=
    inner_natural_semilinear hn hF ρ hirr hker A hA h2 hc hquad hA1 hoff
  have hlin : ∀ a ∈ A, ∀ (c : F) (y : Y), E (a (E.symm (c • E y))) = c • E (a y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, c, y, hne⟩ := hcon
    have hlt := card_mul_card_fix_lt hn hF E A h2 hc hsemi ⟨a, ha, c, y, hne⟩
    rw [(Nat.card_congr E.toEquiv).trans InnerCount.card_fin3_fun] at hoff
    exact absurd hoff (not_le.mpr hlt)
  intro a ha
  obtain ⟨g, hg⟩ := exists_matrix_of_linear hn hF E A h2 hc hsemi a ha (hlin a ha)
  obtain ⟨x, hx⟩ := hsurj g
  refine ⟨x, fun y => E.injective ?_⟩
  rw [hg y, hE x y, hx]

theorem inner_false_of_two (h4 : 4 ≤ Nat.card Y)
    (hoff : Nat.card Y * Nat.card Y ≤
      4 * (Nat.card ↥A * Nat.card {y : Y // ∀ a ∈ A, a y = y})) : False := by
  have hoff1 : Nat.card Y ≤ Nat.card ↥A * Nat.card {y : Y // ∀ a ∈ A, a y = y} := by
    by_contra hlt
    push Not at hlt
    nlinarith
  obtain ⟨ψ, -, E, -, hsemi⟩ :=
    inner_natural_semilinear hn hF ρ hirr hker A hA h2 hc hquad hA1 hoff1
  have hAcard := card_le_two_mul_sq hn hF E A h2 hc hsemi
  have hfix := card_fix_le_sq hn hF E A h2 hc hsemi hA1
  have hYcard : Nat.card Y = Fintype.card F ^ 3 :=
    (Nat.card_congr E.toEquiv).trans InnerCount.card_fin3_fun
  have hAF := Nat.mul_le_mul hAcard hfix
  rw [hYcard] at hoff
  have hq4 : 4 ≤ Fintype.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set q := Fintype.card F with hq
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have hq4pos : 0 < q ^ 4 := by positivity
  have h6 : q ^ 3 * q ^ 3 = q ^ 4 * q ^ 2 := by ring
  have h8 : 2 * q ^ 2 * q ^ 2 = 2 * q ^ 4 := by ring
  have h16 : q ^ 4 * 16 ≤ q ^ 4 * q ^ 2 := Nat.mul_le_mul_left _ hq2
  nlinarith

end YLevel

section KLevel

theorem inner_four_lt_card {K : Type*} [Group K] {Z : Type*} [AddCommGroup Z]
    [Module (ZMod 2) Z] [Finite Z] {L : Subgroup K} (hperf : commutator ↥L = ⊤)
    {κ : Representation (ZMod 2) K Z} {Y : Submodule (ZMod 2) Z}
    (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) (hnt : ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y) :
    4 < Nat.card ↥Y := by
  by_contra hle
  push Not at hle
  haveI : Group.IsSolvable (Equiv.Perm ↥Y) := Equiv.Perm.isSolvable hle
  haveI : Group.IsPerfect ↥L := ⟨hperf⟩
  let φ : ↥L →* Equiv.Perm ↥Y :=
    (MulAction.toPermHom (↥Y ≃ₗ[ZMod 2] ↥Y) ↥Y).comp
      (repGL (⟨Y, fun g _ hv => hY g g.2 _ hv⟩ :
        Subrepresentation (κ.comp L.subtype)).toRepresentation)
  have hφ : ∀ x : ↥L, φ x = 1 := by
    intro x
    have hP : ∀ k, derivedSeries ↥L k = ⊤ := by
      intro k
      induction k with
      | zero => exact derivedSeries_zero _
      | succ k ih =>
        rw [derivedSeries_succ, ih]
        exact Group.IsPerfect.commutator_eq_top
    obtain ⟨m, hm⟩ := (inferInstance : Group.IsSolvable (Equiv.Perm ↥Y)).solvable
    have h1 := map_derivedSeries_le_derivedSeries φ m
    rw [hP m, hm, Subgroup.map_top, le_bot_iff] at h1
    exact Subgroup.mem_bot.mp (h1 ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  obtain ⟨l, hl, y, hy, hne⟩ := hnt
  apply hne
  have h1 := congrArg (fun σ : Equiv.Perm ↥Y => ((σ ⟨y, hy⟩ : ↥Y) : Z)) (hφ ⟨l, hl⟩)
  exact h1

theorem core_inner {K : Type} [Group K] [Finite K] {L B : Subgroup K} (h : InnerCtx L B)
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (e : ↥L ≃* SL(3, F)) {Z : Type} [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]
    {κ : Representation (ZMod 2) K Z} (hd : ChiefData L B κ) :
    ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l := by
  classical
  haveI := hd.nontrivial
  have hNatF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hNatF
  have hperf : commutator ↥L = ⊤ := h.quasi.1
  obtain ⟨Y, hY⟩ := exists_lMin L κ
  have hnt := hY.nontriv h hd
  have hY4 : 4 < Nat.card ↥Y := inner_four_lt_card hperf hY.inv hnt
  have hBN : B ≤ Subgroup.normalizer (L : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_L]
    exact le_top
  have hrel := relIndex_innerPart_le L B hn hNatF e hperf hBN h.sq
  have hinn : innerPart L B ≤ stabIn h κ Y := innerPart_le_stab h κ hd.irr hY.inv
  have hrel' : Nat.card ↥(innerPart L B) * (innerPart L B).relIndex B = Nat.card ↥B := by
    have h1 := Subgroup.card_mul_index ((innerPart L B).subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (innerPart_le L B)).toEquiv] at h1
    exact h1
  have hcardle : Nat.card ↥(innerPart L B) ≤ Nat.card ↥(stabIn h κ Y) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hinn) (Subgroup.inclusion_injective hinn)
  have hB4 : Nat.card ↥B ≤ 4 * Nat.card ↥(stabIn h κ Y) := by
    rw [← hrel']
    calc Nat.card ↥(innerPart L B) * (innerPart L B).relIndex B
        ≤ Nat.card ↥(innerPart L B) * 4 := Nat.mul_le_mul_left _ hrel
      _ ≤ Nat.card ↥(stabIn h κ Y) * 4 := Nat.mul_le_mul_right _ hcardle
      _ = 4 * Nat.card ↥(stabIn h κ Y) := by ring
  have hcard := card_stabIn h hd hY hnt
  have hfixcard := card_fix_stabImage h κ Y
  have hNpos : 0 < Nat.card ↥(B ⊓ MonoidHom.ker κ) := Nat.card_pos
  have hAint := stabImage_intertwines h e κ Y hY.inv
  have hker := rhoY_ker e hY.inv hnt
  have hirr := rhoY_irreducible e hY
  have hsq := stabImage_sq h κ Y
  have hcomm := stabImage_comm h κ Y
  have hquad := stabImage_quad h hd Y
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
      have hrep := inner_eq_rep_of_offender hn hF (rhoY e κ Y hY.inv) hirr hker
        (stabImage h κ Y) hAint hsq hcomm hquad hA0 hoff
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
    have hmain : Nat.card ↥Y * Nat.card ↥Y ≤ 4 * (Nat.card ↥(stabImage h κ Y) *
        Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y}) := by
      refine Nat.le_of_mul_le_mul_left ?_ hNpos
      calc Nat.card ↥(B ⊓ MonoidHom.ker κ) * (Nat.card ↥Y * Nat.card ↥Y)
          = Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥Y ^ 2 := by ring
        _ ≤ Nat.card ↥B * Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) := hsq2
        _ ≤ (4 * Nat.card ↥(stabIn h κ Y)) * Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) :=
            Nat.mul_le_mul_right _ hB4
        _ = Nat.card ↥(B ⊓ MonoidHom.ker κ) * (4 * (Nat.card ↥(stabImage h κ Y) *
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
    · exact inner_false_of_two hn hF (rhoY e κ Y hY.inv) hirr hker (stabImage h κ Y) hAint hsq
        hcomm hquad hA0 hY4.le hmain

end KLevel

end CFSG.LocalAnalysis.RankThreeUC.S15
