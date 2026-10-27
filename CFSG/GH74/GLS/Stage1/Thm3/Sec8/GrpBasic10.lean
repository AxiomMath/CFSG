module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

section Abstract

variable {R : Type*} [Group R]

@[expose] def cycNorm (hc : ∀ a b : R, a * b = b * a) (sg : R →* R) : R →* R :=
  MonoidHom.mk' (fun r => r * sg r * sg (sg r)) (fun a b => by
    have : Std.Commutative (α := R) (· * ·) := ⟨hc⟩
    simp only [map_mul]
    ac_rfl)

theorem cycNorm_apply (hc : ∀ a b : R, a * b = b * a) (sg : R →* R) (r : R) :
    cycNorm hc sg r = r * sg r * sg (sg r) := rfl

theorem sg_cycNorm (hc : ∀ a b : R, a * b = b * a) (sg : R →* R) (h3 : ∀ r : R, sg (sg (sg r)) = r)
    (r : R) : sg (cycNorm hc sg r) = cycNorm hc sg r := by
  have : Std.Commutative (α := R) (· * ·) := ⟨hc⟩
  rw [cycNorm_apply, map_mul, map_mul, h3]
  ac_rfl

theorem cycNorm_sg (hc : ∀ a b : R, a * b = b * a) (sg : R →* R) (h3 : ∀ r : R, sg (sg (sg r)) = r)
    (r : R) : cycNorm hc sg (sg r) = cycNorm hc sg r := by
  have : Std.Commutative (α := R) (· * ·) := ⟨hc⟩
  rw [cycNorm_apply, cycNorm_apply, h3]
  ac_rfl

theorem cycNorm_cycNorm (hc : ∀ a b : R, a * b = b * a) (sg : R →* R) (h2 : ∀ r : R, r * r = 1)
    (h3 : ∀ r : R, sg (sg (sg r)) = r) (r : R) :
    cycNorm hc sg (cycNorm hc sg r) = cycNorm hc sg r := by
  have hfix := sg_cycNorm hc sg h3 r
  rw [cycNorm_apply _ _ (cycNorm hc sg r), hfix, hfix, h2, one_mul]

theorem exists_normKer [Finite R] (hc : ∀ a b : R, a * b = b * a) (sg : R →* R)
    (h2 : ∀ r : R, r * r = 1) (h3 : ∀ r : R, sg (sg (sg r)) = r) (hne : ∃ r, sg r ≠ r)
    (hcard : Nat.card R ≤ 8) :
    ∃ K : Subgroup R, Nat.card K = 4 ∧ (∀ r ∈ K, sg r ∈ K) ∧ (∀ r ∈ K, sg r = r → r = 1) ∧
      (∀ r : R, ∃ k ∈ K, ∃ c : R, sg c = c ∧ r = k * c) ∧
      (∀ tau : R →* R,
        ((∀ r, tau (sg r) = sg (tau r)) ∨ (∀ r, tau (sg r) = sg (sg (tau r)))) →
        ∀ k ∈ K, tau k ∈ K) := by
  classical
  have : Std.Commutative (α := R) (· * ·) := ⟨hc⟩
  set T := cycNorm hc sg with hT
  have hTapply : ∀ r, T r = r * sg r * sg (sg r) := fun r => rfl
  have hTfix : ∀ r, sg (T r) = T r := sg_cycNorm hc sg h3
  have hTsg : ∀ r, T (sg r) = T r := cycNorm_sg hc sg h3
  have hTT : ∀ r, T (T r) = T r := cycNorm_cycNorm hc sg h2 h3
  have hKmem : ∀ r, r ∈ T.ker ↔ T r = 1 := fun r => MonoidHom.mem_ker
  have hKsg : ∀ r ∈ T.ker, sg r ∈ T.ker := by
    intro r hr
    rw [hKmem] at hr ⊢
    rw [hTsg, hr]
  have hKfix : ∀ r ∈ T.ker, sg r = r → r = 1 := by
    intro r hr hfix
    rw [hKmem] at hr
    have hTr : T r = r := by
      simp only [hTapply, hfix, h2, one_mul]
    rw [← hTr]
    exact hr
  have hKdec : ∀ r : R, ∃ k ∈ T.ker, ∃ c : R, sg c = c ∧ r = k * c := by
    intro r
    refine ⟨r * T r, ?_, T r, hTfix r, ?_⟩
    · rw [hKmem, map_mul, hTT, h2]
    · rw [mul_assoc, h2, mul_one]
  have hKne : ∃ k ∈ T.ker, k ≠ 1 := by
    obtain ⟨r, hr⟩ := hne
    refine ⟨r * T r, ?_, ?_⟩
    · rw [hKmem, map_mul, hTT, h2]
    · intro h1
      apply hr
      have hrT : r = T r := by
        have := congrArg (· * T r) h1
        simpa [mul_assoc, h2] using this
      calc sg r = sg (T r) := by rw [← hrT]
        _ = T r := hTfix r
        _ = r := hrT.symm
  have hK2 : IsPGroup 2 T.ker := fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (h2 g)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hK2
  have hmod : Nat.card T.ker ≡ 1 [MOD 3] := by
    have : Fintype T.ker := Fintype.ofFinite _
    let f : Function.End T.ker := fun k => ⟨sg k, hKsg k k.2⟩
    have hf : f ^ 3 ^ 1 = 1 := by
      funext k
      show f^[3] k = k
      exact Subtype.ext (h3 k)
    have key := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
    have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, ?_⟩, ?_⟩
      · show f 1 = 1
        exact Subtype.ext (map_one sg)
      · rintro ⟨k, hk⟩
        apply Subtype.ext
        apply Subtype.ext
        exact hKfix k k.2 (congrArg Subtype.val hk)
    rwa [hfix, ← Nat.card_eq_fintype_card] at key
  have hcardK : Nat.card T.ker ≤ 8 := (Subgroup.card_le_card_group _).trans hcard
  have hK1 : Nat.card T.ker ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    obtain ⟨k, hk, hk1⟩ := hKne
    exact hk1 (by simpa [h1] using hk)
  have hK4 : Nat.card T.ker = 4 := by
    have hn4 : n < 4 := by
      by_contra hn4
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2n : Nat.card T.ker = 1 ∨ Nat.card T.ker = 2 ∨ Nat.card T.ker = 4 ∨
        Nat.card T.ker = 8 := by
      rw [hn]
      interval_cases n <;> simp
    unfold Nat.ModEq at hmod
    omega
  have htau : ∀ tau : R →* R,
      ((∀ r, tau (sg r) = sg (tau r)) ∨ (∀ r, tau (sg r) = sg (sg (tau r)))) →
      ∀ k ∈ T.ker, tau k ∈ T.ker := by
    intro tau hτ k hk
    rw [hKmem] at hk ⊢
    have hcomm' : T (tau k) = tau (T k) := by
      rcases hτ with hτ | hτ
      · simp only [hTapply, map_mul, hτ]
      · simp only [hTapply, map_mul, hτ, h3]
        ac_rfl
    rw [hcomm', hk, map_one]
  exact ⟨T.ker, hK4, hKsg, hKfix, hKdec, htau⟩

end Abstract

section Transport

variable {G : Type*} [Group G]

theorem subgroupOf_normal_of_conj_mem (W A : Subgroup G)
    (hAn : ∀ w ∈ W, ∀ a ∈ A, w * a * w⁻¹ ∈ A) : (A.subgroupOf W).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hAn g g.2 n hn⟩

theorem exists_conjQ (W A : Subgroup G) [(A.subgroupOf W).Normal] (c d : G) (hcd : c * d = 1)
    (hW : ∀ w ∈ W, c * w * d ∈ W) (hA : ∀ a ∈ A, c * a * d ∈ A) :
    ∃ f : (↥W ⧸ A.subgroupOf W) →* (↥W ⧸ A.subgroupOf W),
      ∀ w w' : ↥W, (w' : G) = c * w * d →
        f (QuotientGroup.mk w) = QuotientGroup.mk w' := by
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥W →* ↥W, ∀ w : ↥W, ((σ w : ↥W) : G) = c * w * d := by
    have hd : d = c⁻¹ := eq_inv_of_mul_eq_one_right hcd
    refine ⟨{ toFun := fun w => ⟨c * w * d, hW w w.2⟩
              map_one' := Subtype.ext (by simpa using hcd)
              map_mul' := fun a b => Subtype.ext (by
                subst hd
                simp only [Subgroup.coe_mul]
                group) }, fun w => rfl⟩
  refine ⟨QuotientGroup.map _ _ σ (fun a ha => ?_), fun w w' hw' => ?_⟩
  · show ((σ a : ↥W) : G) ∈ A
    rw [hσ]
    exact hA a ha
  · have : w' = σ w := Subtype.ext (by rw [hσ]; exact hw')
    rw [this]
    rfl

theorem card_map_comap_quot [Finite G] (W A : Subgroup G) [(A.subgroupOf W).Normal] (hAW : A ≤ W)
    (K : Subgroup (↥W ⧸ A.subgroupOf W)) :
    Nat.card ((K.comap (QuotientGroup.mk' (A.subgroupOf W))).map W.subtype) =
      Nat.card K * Nat.card A := by
  have hπ : Function.Surjective (QuotientGroup.mk' (A.subgroupOf W)) :=
    QuotientGroup.mk'_surjective _
  have h1 : Nat.card ((K.comap (QuotientGroup.mk' (A.subgroupOf W))).map W.subtype) =
      Nat.card (K.comap (QuotientGroup.mk' (A.subgroupOf W))) :=
    Subgroup.card_map_of_injective W.subtype_injective
  have h2 := Subgroup.card_mul_index (K.comap (QuotientGroup.mk' (A.subgroupOf W)))
  rw [Subgroup.index_comap_of_surjective K hπ] at h2
  have h3 := Subgroup.card_mul_index K
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf W)
  have h5 : Nat.card ↥(A.subgroupOf W) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv
  have hi : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [h1]
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
  rw [h2, h4, h5, ← h3]
  ring

end Transport

section Main

theorem exists_norm_kernel {G : Type*} [Group G] [Finite G] (W A : Subgroup G) (h : G)
    (hAW : A ≤ W)
    (hAn : ∀ w ∈ W, ∀ a ∈ A, w * a * w⁻¹ ∈ A)
    (hcomm : ∀ w ∈ W, ∀ w' ∈ W, w * w' * w⁻¹ * w'⁻¹ ∈ A)
    (hsq : ∀ w ∈ W, w * w ∈ A)
    (hhW : ∀ w ∈ W, h⁻¹ * w * h ∈ W) (hhA : ∀ a ∈ A, h⁻¹ * a * h ∈ A)
    (hh3 : ∀ w ∈ W, h ^ 3 * w = w * h ^ 3)
    (hnt : ∃ w ∈ W, w * h * w⁻¹ * h⁻¹ ∉ A)
    (hcard : Nat.card ↥W ≤ 8 * Nat.card ↥A) :
    ∃ Y : Subgroup G, A ≤ Y ∧ Y ≤ W ∧ Nat.card ↥Y = 4 * Nat.card ↥A ∧
      (∀ y ∈ Y, h⁻¹ * y * h ∈ Y) ∧ (∀ y ∈ Y, h * y = y * h → y ∈ A) ∧
      (∀ w ∈ W, ∃ y ∈ Y, ∃ c ∈ W, (h⁻¹ * c * h) * c⁻¹ ∈ A ∧ w = y * c) ∧
      (∀ g : G, (g * h * g⁻¹ = h ∨ g * h * g⁻¹ = h⁻¹) → (∀ w ∈ W, g * w * g⁻¹ ∈ W) →
        (∀ a ∈ A, g * a * g⁻¹ ∈ A) → ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) := by
  have hN : (A.subgroupOf W).Normal := subgroupOf_normal_of_conj_mem W A hAn
  have hh3' : ∀ x ∈ W, h * h * h * x = x * (h * h * h) := by
    intro x hx
    have hx3 := hh3 x hx
    rwa [pow_succ, pow_two] at hx3
  have hσ3 : ∀ x ∈ W, h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h = x := by
    intro x hx
    calc h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h = (h * h * h)⁻¹ * (x * (h * h * h)) := by group
      _ = (h * h * h)⁻¹ * (h * h * h * x) := by rw [hh3' x hx]
      _ = x := inv_mul_cancel_left _ _
  have hconj : ∀ x ∈ W, h * x * h⁻¹ = h⁻¹ * (h⁻¹ * x * h) * h := by
    intro x hx
    calc h * x * h⁻¹ = h⁻¹ * h⁻¹ * (h * h * h * x) * h⁻¹ := by group
      _ = h⁻¹ * h⁻¹ * (x * (h * h * h)) * h⁻¹ := by rw [hh3' x hx]
      _ = h⁻¹ * (h⁻¹ * x * h) * h := by group
  have hconjA : ∀ a ∈ A, h * a * h⁻¹ ∈ A := by
    intro a ha
    rw [hconj a (hAW ha)]
    exact hhA _ (hhA a ha)
  obtain ⟨sg, hsg⟩ := exists_conjQ W A h⁻¹ h (inv_mul_cancel h) hhW hhA
  have hsgW : ∀ x : ↥W, sg (QuotientGroup.mk x) =
      (QuotientGroup.mk ⟨h⁻¹ * x * h, hhW x x.2⟩ : ↥W ⧸ A.subgroupOf W) :=
    fun x => hsg x _ rfl
  have hc : ∀ a b : ↥W ⧸ A.subgroupOf W, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have := hcomm (y : G)⁻¹ (inv_mem y.2) (x : G)⁻¹ (inv_mem x.2)
    simpa [mul_assoc] using this
  have h2 : ∀ r : ↥W ⧸ A.subgroupOf W, r * r = 1 := by
    intro r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq x x.2
  have h3 : ∀ r : ↥W ⧸ A.subgroupOf W, sg (sg (sg r)) = r := by
    intro r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
    rw [hsgW, hsgW, hsgW]
    congr 1
    exact Subtype.ext (hσ3 x x.2)
  have hne : ∃ r : ↥W ⧸ A.subgroupOf W, sg r ≠ r := by
    obtain ⟨w, hw, hwA⟩ := hnt
    by_contra hcon
    push Not at hcon
    have h1 := hcon (QuotientGroup.mk ⟨w⁻¹, inv_mem hw⟩)
    rw [hsgW, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    apply hwA
    have h2' : h⁻¹ * w * h * w⁻¹ ∈ A := by simpa [mul_assoc] using h1
    have h4 := hconjA _ h2'
    have e : w * h * w⁻¹ * h⁻¹ = h * (h⁻¹ * w * h * w⁻¹) * h⁻¹ := by group
    rwa [e]
  have hcardR : Nat.card (↥W ⧸ A.subgroupOf W) ≤ 8 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf W)
    have h5 : Nat.card ↥(A.subgroupOf W) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv
    have hApos : 0 < Nat.card ↥A := Nat.card_pos
    rw [h5] at h1
    refine Nat.le_of_mul_le_mul_right ?_ hApos
    rw [← h1]
    exact hcard
  obtain ⟨K, hK4, hKsg, hKfix, hKdec, hKtau⟩ := exists_normKer hc sg h2 h3 hne hcardR
  have hmemY : ∀ y : G,
      y ∈ (K.comap (QuotientGroup.mk' (A.subgroupOf W))).map W.subtype ↔
        ∃ hy : y ∈ W, (QuotientGroup.mk ⟨y, hy⟩ : ↥W ⧸ A.subgroupOf W) ∈ K := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hy, hyK⟩
      exact ⟨⟨y, hy⟩, hyK, rfl⟩
  refine ⟨(K.comap (QuotientGroup.mk' (A.subgroupOf W))).map W.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hmemY]
    refine ⟨hAW ha, ?_⟩
    have h1 : (QuotientGroup.mk ⟨a, hAW ha⟩ : ↥W ⧸ A.subgroupOf W) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact ha
    rw [h1]
    exact one_mem K
  · exact Subgroup.map_subtype_le _
  · rw [card_map_comap_quot W A hAW K, hK4]
  · intro y hy
    obtain ⟨hyW, hyK⟩ := (hmemY y).1 hy
    refine (hmemY _).2 ⟨hhW y hyW, ?_⟩
    have h1 := hKsg _ hyK
    rwa [hsgW] at h1
  · intro y hy hyc
    obtain ⟨hyW, hyK⟩ := (hmemY y).1 hy
    have hfixed : sg (QuotientGroup.mk ⟨y, hyW⟩) =
        (QuotientGroup.mk ⟨y, hyW⟩ : ↥W ⧸ A.subgroupOf W) := by
      rw [hsgW]
      congr 1
      apply Subtype.ext
      show h⁻¹ * y * h = y
      rw [mul_assoc, ← hyc, inv_mul_cancel_left]
    have h1 := hKfix _ hyK hfixed
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro w hw
    obtain ⟨k, hk, c, hcfix, hrkc⟩ := hKdec (QuotientGroup.mk ⟨w, hw⟩)
    obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨w * (c' : G)⁻¹, (hmemY _).2 ⟨mul_mem hw (inv_mem c'.2), ?_⟩, c', c'.2, ?_, by group⟩
    · have e : (QuotientGroup.mk ⟨w * (c' : G)⁻¹, mul_mem hw (inv_mem c'.2)⟩ :
          ↥W ⧸ A.subgroupOf W) = QuotientGroup.mk ⟨w, hw⟩ * (QuotientGroup.mk c')⁻¹ := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      rw [e, hrkc, mul_inv_cancel_right]
      exact hk
    · rw [hsgW, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at hcfix
      simpa [div_eq_mul_inv] using hcfix
  · intro g hg hgW hgA y hy
    obtain ⟨hyW, hyK⟩ := (hmemY y).1 hy
    obtain ⟨tau, htau⟩ := exists_conjQ W A g g⁻¹ (mul_inv_cancel g) hgW hgA
    have htauW : ∀ x : ↥W, tau (QuotientGroup.mk x) =
        (QuotientGroup.mk ⟨g * x * g⁻¹, hgW x x.2⟩ : ↥W ⧸ A.subgroupOf W) :=
      fun x => htau x _ rfl
    refine (hmemY _).2 ⟨hgW y hyW, ?_⟩
    have hcomm' : (∀ r, tau (sg r) = sg (tau r)) ∨ (∀ r, tau (sg r) = sg (sg (tau r))) := by
      rcases hg with hg | hg
      · left
        intro r
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
        rw [hsgW, htauW, htauW, hsgW]
        congr 1
        apply Subtype.ext
        show g * (h⁻¹ * x * h) * g⁻¹ = h⁻¹ * (g * x * g⁻¹) * h
        have hg' : g * h⁻¹ * g⁻¹ = h⁻¹ := by
          calc g * h⁻¹ * g⁻¹ = (g * h * g⁻¹)⁻¹ := by group
            _ = h⁻¹ := by rw [hg]
        calc g * (h⁻¹ * x * h) * g⁻¹
            = (g * h⁻¹ * g⁻¹) * (g * x * g⁻¹) * (g * h * g⁻¹) := by group
          _ = h⁻¹ * (g * x * g⁻¹) * h := by rw [hg', hg]
      · right
        intro r
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
        rw [hsgW, htauW, htauW, hsgW, hsgW]
        congr 1
        apply Subtype.ext
        show g * (h⁻¹ * x * h) * g⁻¹ = h⁻¹ * (h⁻¹ * (g * x * g⁻¹) * h) * h
        have hg' : g * h⁻¹ * g⁻¹ = h := by
          calc g * h⁻¹ * g⁻¹ = (g * h * g⁻¹)⁻¹ := by group
            _ = h := by rw [hg, inv_inv]
        calc g * (h⁻¹ * x * h) * g⁻¹
            = (g * h⁻¹ * g⁻¹) * (g * x * g⁻¹) * (g * h * g⁻¹) := by group
          _ = h * (g * x * g⁻¹) * h⁻¹ := by rw [hg', hg]
          _ = h⁻¹ * (h⁻¹ * (g * x * g⁻¹) * h) * h := hconj _ (hgW x x.2)
    have key := hKtau tau hcomm' _ hyK
    rwa [htauW] at key

end Main

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
