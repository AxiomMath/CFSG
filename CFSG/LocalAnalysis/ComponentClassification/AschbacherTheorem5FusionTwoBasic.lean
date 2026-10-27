module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionBasic

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace FusionTwo

open SectionSix Involution Fusion

theorem exists_commuting_involutions {Q : Type} [Group Q] [Finite Q] {X Y Z : Subgroup Q}
    (hXp : Group.IsPerfect X) (hX : X ≠ ⊥) (hYp : Group.IsPerfect Y) (hY : Y ≠ ⊥)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hXZ : X ≤ Subgroup.centralizer (Z : Set Q)) (hYZ : Y ≤ Subgroup.centralizer (Z : Set Q)) :
    ∃ x y : Q, orderOf x = 2 ∧ orderOf y = 2 ∧ x * y = y * x ∧ x ≠ y ∧
      x ∈ Subgroup.centralizer (Z : Set Q) ∧ y ∈ Subgroup.centralizer (Z : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ W : Subgroup Q, Group.IsPerfect W → W ≠ ⊥ → ∃ w ∈ W, orderOf w = 2 := by
    intro W hWp hW
    have : Nontrivial W := W.nontrivial_iff_ne_bot.mpr hW
    have heven : Even (Nat.card W) := even_card_of_perfect
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 (even_iff_two_dvd.mp heven)
    exact ⟨w, w.2, by rw [Subgroup.orderOf_coe, hw]⟩
  obtain ⟨a, haX, ha2⟩ := hinv X hXp hX
  obtain ⟨b, hbY, hb2⟩ := hinv Y hYp hY
  by_cases hpair : ∃ x ∈ X, ∃ y ∈ Y, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y
  · obtain ⟨x, hx, y, hy, hx2, hy2, hne⟩ := hpair
    exact ⟨x, y, hx2, hy2, hXY x hx y hy, hne, hXZ hx, hYZ hy⟩
  push Not at hpair
  have hab : a = b := hpair a haX b hbY ha2 hb2
  have huX : ∀ x ∈ X, orderOf x = 2 → x = a := fun x hx hx2 =>
    (hpair x hx b hbY hx2 hb2).trans hab.symm
  have huY : ∀ y ∈ Y, orderOf y = 2 → y = a := fun y hy hy2 =>
    (hpair a haX y hy ha2 hy2).symm
  have haY : a ∈ Y := hab ▸ hbY
  obtain ⟨x₀, hx₀, hx₀4⟩ := exists_orderOf_four_mem hXp hX huX
  obtain ⟨y₀, hy₀, hy₀4⟩ := exists_orderOf_four_mem hYp hY huY
  have hsq : ∀ w : Q, orderOf w = 4 → orderOf (w ^ 2) = 2 := by
    intro w hw
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hw]; norm_num), hw]
  have hx₀sq : x₀ ^ 2 = a := huX _ (X.pow_mem hx₀ 2) (hsq x₀ hx₀4)
  have hy₀sq : y₀ ^ 2 = a := huY _ (Y.pow_mem hy₀ 2) (hsq y₀ hy₀4)
  have hxy : x₀ * y₀ = y₀ * x₀ := hXY x₀ hx₀ y₀ hy₀
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hy₀X : ∀ w ∈ X, y₀ ≠ w := by
    intro w hw heq
    apply not_mem_centralizer_of_orderOf_four hYp hY huY hy₀ hy₀4
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [heq]
    exact (hXY w hw y hy).symm
  refine ⟨x₀ * y₀, a, ?_, ha2, ?_, ?_, Subgroup.mul_mem _ (hXZ hx₀) (hYZ hy₀), hXZ haX⟩
  · apply orderOf_eq_prime
    · rw [Commute.mul_pow hxy 2, hx₀sq, hy₀sq, haa]
    · intro h
      exact hy₀X x₀⁻¹ (X.inv_mem hx₀) (eq_inv_of_mul_eq_one_right h)
  · have h1 : x₀ * a = a * x₀ := hXY x₀ hx₀ a haY
    have h2 : a * y₀ = y₀ * a := hXY a haX y₀ hy₀
    calc x₀ * y₀ * a = x₀ * (y₀ * a) := by group
      _ = (x₀ * a) * y₀ := by rw [← h2]; group
      _ = a * (x₀ * y₀) := by rw [h1]; group
  · intro h
    apply hy₀X (x₀⁻¹ * a) (X.mul_mem (X.inv_mem hx₀) haX)
    rw [← h]
    group

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem three_le (hC : Counterexample G D r Abar) (hr : r ≠ 2) : 3 ≤ r := by
  have h1 := hC.hyp.hr
  have hne1 : r ≠ 1 := fun h => hC.fails (Or.inl h)
  omega

theorem mem_of_conj_mem (hin : SectionSevenBase) (hC : Counterexample G D r Abar) (hr : r ≠ 2)
    {a : G} (ha2 : orderOf a = 2)
    (haC : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (D : Set G)) {g : G}
    (hag : g⁻¹ * a * g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer (D : Set G) := by
  by_contra hg
  exact hr (r_eq_two_and_rank hin hC (hyp71_of_conj hC ha2 haC hg hag)).1

theorem mem_rightConjugate_iff_of_ne_two (hin : SectionSevenBase)
    (hC : Counterexample G D r Abar) (hr : r ≠ 2) {a : G} (ha2 : orderOf a = 2)
    (haC : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (D : Set G)) (g : G) :
    a ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g ↔
      g ∈ Subgroup.normalizer (D : Set G) := by
  have haH : a ∈ Subgroup.normalizer (D : Set G) :=
    haC (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  rw [mem_rightConjugate_iff]
  constructor
  · intro h
    have hg := mem_of_conj_mem hin hC hr ha2 haC (g := g⁻¹) (by rwa [inv_inv])
    simpa using (Subgroup.normalizer (D : Set G)).inv_mem hg
  · intro hg
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg haH) (Subgroup.inv_mem _ hg)

theorem exists_good_pair (hC : Counterexample G D r Abar) (hr : 3 ≤ r) :
    ∃ u v : G, orderOf u = 2 ∧ orderOf v = 2 ∧ u * v = v * u ∧ u ≠ v ∧
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (D : Set G) ∧
      Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (D : Set G) ∧
      Subgroup.centralizer ({u * v} : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  have hyp := hC.hyp
  obtain ⟨i₀, i₁, i₂, h01, h02, h12⟩ : ∃ i₀ i₁ i₂ : Fin r, i₀ ≠ i₁ ∧ i₀ ≠ i₂ ∧ i₁ ≠ i₂ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff]⟩
  have hcz : ∀ i, i ≠ i₂ → Abar i ≤ Subgroup.centralizer (Abar i₂ : Set _) := by
    intro i hi x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hyp.hcomm i i₂ hi x hx y hy).symm
  obtain ⟨x, y, hx2, hy2, hxy, hne, hxc, hyc⟩ := exists_commuting_involutions
    (semisimple_perfect _ (hyp.hsemisimple i₀)) (semisimple_ne_bot _ (hyp.hsemisimple i₀))
    (semisimple_perfect _ (hyp.hsemisimple i₁)) (semisimple_ne_bot _ (hyp.hsemisimple i₁))
    (hyp.hcomm i₀ i₁ h01) (hcz i₀ h02) (hcz i₁ h12)
  obtain ⟨W, -, hW4, hWV⟩ := exists_fourGroup_lift (aschbacherThm5OddCore D) (oddCore_odd D)
    (C := ⊤) (isFourGroup_fourGroupOfPair hx2 hy2 hxy hne) (by
      intro v _
      obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) v
      exact ⟨d, Subgroup.mem_top d, rfl⟩)
  have hxW : x ∈ W.map (QuotientGroup.mk' (aschbacherThm5OddCore D)) := by
    rw [hWV]
    exact Or.inr (Or.inl rfl)
  have hyW : y ∈ W.map (QuotientGroup.mk' (aschbacherThm5OddCore D)) := by
    rw [hWV]
    exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨w₁, hw₁, hw₁x⟩ := hxW
  obtain ⟨w₂, hw₂, hw₂y⟩ := hyW
  have hWc := hW4.1.1
  have hw12 : w₁ * w₂ = w₂ * w₁ := congrArg Subtype.val (mul_comm' (⟨w₁, hw₁⟩ : W) ⟨w₂, hw₂⟩)
  have horder : ∀ w ∈ W, ∀ q : D ⧸ aschbacherThm5OddCore D,
      QuotientGroup.mk' (aschbacherThm5OddCore D) w = q → orderOf q = 2 →
      orderOf (w : G) = 2 := by
    intro w hw q hwq hq2
    rw [Subgroup.orderOf_coe]
    apply orderOf_eq_prime (hW4.1.2 w hw)
    rintro rfl
    rw [map_one] at hwq
    rw [← hwq, orderOf_one] at hq2
    omega
  have hu2 : orderOf (w₁ : G) = 2 := horder w₁ hw₁ x hw₁x hx2
  have hv2 : orderOf (w₂ : G) = 2 := horder w₂ hw₂ y hw₂y hy2
  have huv : (w₁ : G) * w₂ = w₂ * w₁ := congrArg Subtype.val hw12
  have hne' : (w₁ : G) ≠ w₂ := by
    intro heq
    apply hne
    rw [← hw₁x, ← hw₂y]
    exact congrArg _ (Subtype.ext heq)
  have hcent : ∀ d : D, QuotientGroup.mk' (aschbacherThm5OddCore D) d ∈
      Subgroup.centralizer (Abar i₂ : Set _) → (d : G) ≠ 1 → (d : G) ^ 2 = 1 →
      Subgroup.centralizer ({(d : G)} : Set G) ≤ Subgroup.normalizer (D : Set G) := by
    intro d hd hd1 hd2
    exact centralizer_le_of_centralizes hC i₂ (two_power_of_sq hd2) hd1
      ((centralizes_iff_mem_centralizer_quotient (Abar i₂) d).mpr hd)
  have hsq : ∀ w : G, orderOf w = 2 → w ^ 2 = 1 := fun w hw => by
    rw [← hw, pow_orderOf_eq_one]
  have hne1 : ∀ w : G, orderOf w = 2 → w ≠ 1 := fun w hw h => by
    rw [h, orderOf_one] at hw
    omega
  refine ⟨w₁, w₂, hu2, hv2, huv, hne', hcent w₁ (by rw [hw₁x]; exact hxc) (hne1 _ hu2)
    (hsq _ hu2), hcent w₂ (by rw [hw₂y]; exact hyc) (hne1 _ hv2) (hsq _ hv2), ?_⟩
  have hprod := hcent (w₁ * w₂) (by rw [map_mul, hw₁x, hw₂y]; exact Subgroup.mul_mem _ hxc hyc)
    (by
      change (w₁ : G) * w₂ ≠ 1
      intro h
      apply hne'
      have hinv : (w₂ : G)⁻¹ = w₂ := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, hsq _ hv2]
      rw [← hinv]
      exact eq_inv_of_mul_eq_one_left h)
    (by
      change ((w₁ : G) * w₂) ^ 2 = 1
      rw [Commute.mul_pow huv 2, hsq _ hu2, hsq _ hv2, one_mul])
  exact hprod

theorem normal_odd_le {M : Subgroup G} {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huv : u * v = v * u) (hne : u ≠ v) (huC : Subgroup.centralizer ({u} : Set G) ≤ M)
    (hvC : Subgroup.centralizer ({v} : Set G) ≤ M)
    (huvC : Subgroup.centralizer ({u * v} : Set G) ≤ M) {N : Subgroup G} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ M := by
  have hgen :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.four_group_odd_centralizer_generation
      N u v hu hv huv hne hodd (by
        rw [Subgroup.normalizer_eq_top_iff.mpr hN]
        exact le_top)
  rw [hgen]
  exact sup_le (sup_le (inf_le_right.trans huC) (inf_le_right.trans hvC))
    (inf_le_right.trans huvC)

theorem zStar_factor {X : Type} [Group X] [Finite X] {w : X} (hw2 : orderOf w = 2)
    (hiso : ∀ g : X, (g * w * g⁻¹) * w = w * (g * w * g⁻¹) → g * w * g⁻¹ = w) (x : X) :
    ∃ c ∈ Subgroup.centralizer ({w} : Set X), ∃ k ∈ CFSG.oddCore X, x = c * k := by
  let : Fintype X := Fintype.ofFinite X
  have hww : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw2
    omega
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar X w hw1 hww hiso
  have hNK : N ≤ CFSG.oddCore X := le_sSup ⟨hNn, hNodd⟩
  have hcen : (QuotientGroup.mk w : X ⧸ CFSG.oddCore X) ∈
      Subgroup.center (X ⧸ CFSG.oddCore X) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 := hNK (hN g⁻¹)
    rw [inv_inv, ← QuotientGroup.eq_one_iff] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [mul_inv_eq_one] at h1
    calc (QuotientGroup.mk g : X ⧸ CFSG.oddCore X) * QuotientGroup.mk w
        = QuotientGroup.mk g * ((QuotientGroup.mk g)⁻¹ * QuotientGroup.mk w *
            QuotientGroup.mk g) := by rw [h1]
      _ = QuotientGroup.mk w * QuotientGroup.mk g := by group
  exact CFSG.Adapters.eq_centralizer_mul_oddCore hww hcen x

theorem oddCore_le_pPrimeCore (X : Type) [Group X] [Finite X] :
    CFSG.oddCore X ≤ CFSG.pPrimeCore 2 X :=
  sSup_le fun _ hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩

end FusionTwo

end CFSG.ComponentClassification.AschbacherTheorem5
