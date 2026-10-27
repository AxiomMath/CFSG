module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieSL2Inner
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b CFSG.ClassicalInvolution
  CFSG.ComponentClassification.AschbacherKnownGroup
open scoped MatrixGroups commutatorElement

theorem isQuasisimple_psl2 {K : Type*} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    Open.IsQuasisimple PSL(2, K) := by
  have : IsSimpleGroup PSL(2, K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have : Group.IsPerfect SL(2, K) := sl2_isPerfect h4
  have : Group.IsPerfect PSL(2, K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact CFSG.ComponentClassification.Quasisimple.simple_of_perfect _

theorem mem_five_seven_nine {q : ℕ} (hq5 : 5 ≤ q) (hqo : Odd q) (h : q * (q ^ 2 - 1) / 2 ≤ 360) :
    q ∈ ({5, 7, 9} : Finset ℕ) := by
  have hq9 : q ≤ 9 := by
    by_contra hcon
    push Not at hcon
    have hc : 10 ≤ q := hcon
    have h1 : 10 * (10 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hc (Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1)
    omega
  obtain ⟨a, rfl⟩ := hqo
  have ha2 : 2 ≤ a := by omega
  have ha4 : a ≤ 4 := by omega
  interval_cases a <;> decide

theorem card_psl2_ne_2520 {q : ℕ} (hq5 : 5 ≤ q) (hqo : Odd q) : q * (q ^ 2 - 1) / 2 ≠ 2520 := by
  intro h
  have hq17 : q ≤ 17 := by
    by_contra hcon
    push Not at hcon
    have hc : 18 ≤ q := hcon
    have h1 : 18 * (18 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hc (Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1)
    omega
  obtain ⟨a, rfl⟩ := hqo
  have ha8 : a ≤ 8 := by omega
  interval_cases a <;> norm_num at h

private theorem dihedral4_central_aux :
    ∀ x : DihedralGroup 4, (∀ y : DihedralGroup 4, x * y = y * x) →
      x = 1 ∨ x = DihedralGroup.r 2 := by
  decide

private theorem dihedral4_commutator_aux :
    ∀ v : DihedralGroup 4, v ^ 2 = 1 → (∃ y : DihedralGroup 4, v * y ≠ y * v) →
      ∃ c : DihedralGroup 4, c * v * c⁻¹ * v⁻¹ = DihedralGroup.r 2 := by
  decide

variable {H : Type} [Group H] {B T X : Subgroup H}

theorem exists_mul_of_mem_sup_centralizer {B : Subgroup H} {x : H}
    (hx : x ∈ B ⊔ centralizer (B : Set H)) :
    ∃ b ∈ B, ∃ c ∈ centralizer (B : Set H), x = b * c := by
  have hBC : B ≤ normalizer (centralizer (B : Set H) : Set H) := fun b hb => by
    rw [mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [mem_centralizer_iff] at hc ⊢
      intro y hy
      have h2 := hc (b⁻¹ * y * b) (B.mul_mem (B.mul_mem (B.inv_mem hb) hy) hb)
      calc y * (b * c * b⁻¹) = b * ((b⁻¹ * y * b) * c) * b⁻¹ := by group
        _ = b * (c * (b⁻¹ * y * b)) * b⁻¹ := by rw [h2]
        _ = b * c * b⁻¹ * y := by group
    · intro hc
      rw [mem_centralizer_iff] at hc ⊢
      intro y hy
      have h2 := hc (b * y * b⁻¹) (B.mul_mem (B.mul_mem hb hy) (B.inv_mem hb))
      calc y * c = b⁻¹ * ((b * y * b⁻¹) * (b * c * b⁻¹)) * b := by group
        _ = b⁻¹ * ((b * c * b⁻¹) * (b * y * b⁻¹)) * b := by rw [h2]
        _ = c * y := by group
  have := coe_mul_of_left_le_normalizer_right B (centralizer (B : Set H)) hBC
  have hx' : x ∈ ((B ⊔ centralizer (B : Set H) : Subgroup H) : Set H) := hx
  rw [this] at hx'
  obtain ⟨b, hb, c, hc, rfl⟩ := hx'
  exact ⟨b, hb, c, hc, rfl⟩

theorem center_eq_bot_of_psl2 {B : Type*} [Group B] {K : Type*} [Field K] [Finite K]
    (h4 : 4 ≤ Nat.card K) (e : B ≃* PSL(2, K)) : center B = ⊥ := by
  have : IsSimpleGroup PSL(2, K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hsB : IsSimpleGroup B := e.isSimpleGroup
  have hq := isQuasisimple_of_mulEquiv e.symm (isQuasisimple_psl2 h4)
  rcases hsB.eq_bot_or_eq_top_of_normal (center B) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨y, hy⟩ := _root_.exists_ne (1 : B)
    have hcomm : commutator B = ⊥ := by
      rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      have : g₁ ∈ center B := h1 ▸ Subgroup.mem_top g₁
      rw [Subgroup.mem_center_iff] at this
      rw [commutatorElement_def, ← this g₂, mul_inv_cancel_right, mul_inv_cancel,
        Subgroup.mem_bot]
    have : y ∈ commutator B := hq.1 ▸ Subgroup.mem_top y
    rw [hcomm, Subgroup.mem_bot] at this
    exact hy this

theorem Hyp46.le_of_psl2_seven_nine [Finite H] (h : Hyp46 B T X) {p f : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hf : 1 ≤ f) (hq : p ^ f = 7 ∨ p ^ f = 9) (e : B ≃* PSL(2, GaloisField p f))
    (hBq : Open.IsQuasisimple B) (hBeven : Even (Nat.card B))
    (hinner : T ≤ B ⊔ centralizer (B : Set H)) : T ≤ B := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hZ : center B = ⊥ := center_eq_bot_of_psl2 (by rw [hK]; omega) e
  have hBC : ∀ y ∈ B, y ∈ centralizer (B : Set H) → y = 1 := by
    intro y hy hyc
    have : (⟨y, hy⟩ : B) ∈ center B := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((mem_centralizer_iff.mp hyc) g g.2)
    rw [hZ, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hdec : ∀ t ∈ T, t ≠ 1 → ∃ b ∈ B, ∃ c ∈ centralizer (B : Set H), t = b * c ∧
      b ≠ 1 ∧ b ^ 2 = 1 ∧ c ^ 2 = 1 ∧ b * c = c * b := by
    intro t ht ht1
    obtain ⟨b, hb, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer (hinner ht)
    have hbc : b * c = c * b := (mem_centralizer_iff.mp hc) b hb
    have hsq : b ^ 2 * c ^ 2 = 1 := by rw [← Commute.mul_pow hbc 2]; exact h.elem.2 _ ht
    have hb2 : b ^ 2 = 1 := by
      refine hBC _ (pow_mem hb 2) ?_
      rw [eq_inv_of_mul_eq_one_left hsq]
      exact inv_mem (pow_mem hc 2)
    refine ⟨b, hb, c, hc, rfl, ?_, hb2, by rwa [hb2, one_mul] at hsq, hbc⟩
    rintro rfl
    apply ht1
    rw [one_mul] at ht ⊢
    have : c ∈ T ⊓ centralizer (B : Set H) := Subgroup.mem_inf.mpr ⟨ht, hc⟩
    rwa [h.faithful, Subgroup.mem_bot] at this
  intro t ht
  by_cases ht1 : t = 1
  · rw [ht1]; exact one_mem _
  obtain ⟨b, hb, c, hc, rfl, hb1, hb2, hc2, hbc⟩ := hdec t ht ht1
  obtain ⟨s, hs, hs1, hst⟩ := h.exists_ne ht
  obtain ⟨b', hb', c', hc', rfl, hb'1, hb'2, -, hb'c'⟩ := hdec s hs hs1
  have hcb' : c * b' = b' * c := ((mem_centralizer_iff.mp hc) b' hb').symm
  have hc'b : c' * b = b * c' := ((mem_centralizer_iff.mp hc') b hb).symm
  have hcomm : b * b' = b' * b := by
    have h1 : b * c * (b' * c') = b' * c' * (b * c) :=
      congrArg Subtype.val (h.elem.1.is_comm.comm ⟨_, ht⟩ ⟨_, hs⟩)
    have h2 : b * c * (b' * c') = b * b' * (c * c') := by
      rw [mul_assoc b c, ← mul_assoc c b', hcb', mul_assoc b', ← mul_assoc]
    have h3 : b' * c' * (b * c) = b' * b * (c' * c) := by
      rw [mul_assoc b' c', ← mul_assoc c' b, hc'b, mul_assoc b, ← mul_assoc]
    rw [h2, h3] at h1
    have h4 : (b' * b)⁻¹ * (b * b') = (c' * c) * (c * c')⁻¹ := by
      calc (b' * b)⁻¹ * (b * b') = (b' * b)⁻¹ * (b * b' * (c * c')) * (c * c')⁻¹ := by group
        _ = (b' * b)⁻¹ * (b' * b * (c' * c)) * (c * c')⁻¹ := by rw [h1]
        _ = (c' * c) * (c * c')⁻¹ := by group
    have h5 : (b' * b)⁻¹ * (b * b') = 1 := by
      refine hBC _ (mul_mem (inv_mem (mul_mem hb' hb)) (mul_mem hb hb')) ?_
      rw [h4]
      exact mul_mem (mul_mem hc' hc) (inv_mem (mul_mem hc hc'))
    exact (inv_mul_eq_one.mp h5).symm
  have hbb' : b' ≠ b := by
    intro heq
    apply hst
    have h1 : (b' * c')⁻¹ * (b * c) ∈ T ⊓ centralizer (B : Set H) := by
      refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.inv_mem hs) ht, ?_⟩
      have : (b' * c')⁻¹ * (b * c) = c'⁻¹ * c := by rw [heq]; group
      rw [this]
      exact mul_mem (inv_mem hc') hc
    rw [h.faithful, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  set β := e ⟨b, hb⟩ with hβdef
  set β' := e ⟨b', hb'⟩ with hβ'def
  have hβ2 : orderOf β = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (Subtype.ext (by simpa using hb2)) (fun h1 =>
      hb1 (congrArg Subtype.val h1))
  have hb'2' : (⟨b', hb'⟩ : B) ^ 2 = 1 := Subtype.ext (by simpa using hb'2)
  have hβ'2 : β' ^ 2 = 1 := by rw [hβ'def, ← map_pow, hb'2', map_one]
  have hβ'C : β' ∈ centralizer ({β} : Set PSL(2, GaloisField p f)) := by
    rw [mem_centralizer_singleton_iff, hβdef, hβ'def, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hcomm.symm)
  have hβ'Z : β' ∉ zpowers β := by
    intro hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    rw [← zpow_mod_orderOf, hβ2] at hk
    have hk2 : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
    rcases hk2 with h0 | h1
    · rw [h0, zpow_zero] at hk
      apply hb'1
      have := congrArg (fun x => (e.symm x : H)) hk
      simpa [hβ'def] using this.symm
    · rw [h1, zpow_one] at hk
      apply hbb'
      have := congrArg (fun x => (e.symm x : H)) hk
      simpa [hβdef, hβ'def] using this.symm
  have hq7 : 7 ≤ p ^ f := by omega
  have hZC := CFSG.Walter.psl2_odd_center_centralizer_involution hpodd (by omega) hq7 hβ2
  obtain ⟨ε⟩ : Nonempty (centralizer ({β} : Set PSL(2, GaloisField p f)) ≃*
      DihedralGroup 4) := by
    have hC := CFSG.Walter.psl2_odd_centralizer_involution hpodd (by omega) hβ2
    rcases hq with h7 | h9
    · obtain ⟨-, hD⟩ := hC.2 (by omega)
      rwa [show (p ^ f + 1) / 2 = 4 by omega] at hD
    · obtain ⟨-, hD⟩ := hC.1 (by omega)
      rwa [show (p ^ f - 1) / 2 = 4 by omega] at hD
  have hβC : β ∈ centralizer ({β} : Set PSL(2, GaloisField p f)) :=
    mem_centralizer_singleton_iff.mpr rfl
  have hcentral : ∀ y : DihedralGroup 4, ε ⟨β, hβC⟩ * y = y * ε ⟨β, hβC⟩ := by
    intro y
    obtain ⟨y, rfl⟩ := ε.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp y.2).symm
  have hεβ : ε ⟨β, hβC⟩ = DihedralGroup.r 2 := by
    rcases dihedral4_central_aux _ hcentral with h1 | h1
    · exfalso
      have h2 : ε ⟨β, hβC⟩ = ε 1 := by rw [h1, map_one]
      have h3 : β = 1 := congrArg Subtype.val (ε.injective h2)
      rw [h3, orderOf_one] at hβ2
      omega
    · exact h1
  have hnc : ∃ y : DihedralGroup 4, ε ⟨β', hβ'C⟩ * y ≠ y * ε ⟨β', hβ'C⟩ := by
    by_contra hcon
    push Not at hcon
    apply hβ'Z
    rw [← hZC]
    refine ⟨⟨β', hβ'C⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    apply ε.injective
    rw [map_mul, map_mul]
    exact (hcon (ε g)).symm
  have hsq' : (⟨β', hβ'C⟩ : centralizer ({β} : Set PSL(2, GaloisField p f))) ^ 2 = 1 :=
    Subtype.ext (by simpa using hβ'2)
  obtain ⟨c₀, hc₀⟩ := dihedral4_commutator_aux (ε ⟨β', hβ'C⟩)
    (by rw [← map_pow, hsq', map_one]) hnc
  set c₁ := ε.symm c₀ with hc₁def
  have hc₁ : (c₁ : PSL(2, GaloisField p f)) * β' * (c₁ : PSL(2, GaloisField p f))⁻¹ * β'⁻¹ =
      β := by
    have h1 : ε (c₁ * ⟨β', hβ'C⟩ * c₁⁻¹ * (⟨β', hβ'C⟩)⁻¹) = ε ⟨β, hβC⟩ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc₁def, MulEquiv.apply_symm_apply, hc₀,
        hεβ]
    have h2 := congrArg Subtype.val (ε.injective h1)
    simpa using h2
  have hc₁β : (c₁ : PSL(2, GaloisField p f)) * β = β * c₁ :=
    mem_centralizer_singleton_iff.mp c₁.2
  set c₂ : B := e.symm c₁ with hc₂def
  have keyβ : e.symm β = ⟨b, hb⟩ := by rw [hβdef, MulEquiv.symm_apply_apply]
  have keyβ' : e.symm β' = ⟨b', hb'⟩ := by rw [hβ'def, MulEquiv.symm_apply_apply]
  have hc₂b : (c₂ : H) * b = b * c₂ := by
    have h1 : e.symm (c₁ * β) = e.symm (β * c₁) := by rw [hc₁β]
    rw [map_mul, map_mul, keyβ] at h1
    exact congrArg Subtype.val h1
  have hc₂ : (c₂ : H) * b' * (c₂ : H)⁻¹ * b'⁻¹ = b := by
    have h1 := congrArg e.symm hc₁
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, keyβ', keyβ] at h1
    exact congrArg Subtype.val h1
  have hc₂N : (c₂ : H) ∈ normalizer (X : Set H) := by
    refine h.inf_centralizer_le_of_mem ht ht1
      (Subgroup.mem_inf.mpr ⟨mem_sup_right c₂.2, ?_⟩)
    rw [mem_centralizer_singleton_iff]
    have hcc₂ : (c₂ : H) * c = c * c₂ := (mem_centralizer_iff.mp hc) c₂ c₂.2
    calc (c₂ : H) * (b * c) = (c₂ * b) * c := by group
      _ = (b * c₂) * c := by rw [hc₂b]
      _ = b * (c₂ * c) := by group
      _ = b * (c * c₂) := by rw [hcc₂]
      _ = b * c * c₂ := by group
  have hbX : b ∈ X := by
    have h1 : (c₂ : H) * (b' * c') * (c₂ : H)⁻¹ * (b' * c')⁻¹ ∈ X :=
      X.mul_mem ((mem_normalizer_iff.mp hc₂N _).mp (h.le_X hs)) (X.inv_mem (h.le_X hs))
    have hc'c₂ : (c₂ : H) * c' = c' * c₂ := (mem_centralizer_iff.mp hc') c₂ c₂.2
    have hc'c₂' : c' * (c₂ : H)⁻¹ = (c₂ : H)⁻¹ * c' := by
      calc c' * (c₂ : H)⁻¹ = (c₂ : H)⁻¹ * ((c₂ : H) * c') * (c₂ : H)⁻¹ := by group
        _ = (c₂ : H)⁻¹ * (c' * c₂) * (c₂ : H)⁻¹ := by rw [hc'c₂]
        _ = (c₂ : H)⁻¹ * c' := by group
    have h2 : (c₂ : H) * (b' * c') * (c₂ : H)⁻¹ * (b' * c')⁻¹ =
        (c₂ : H) * b' * (c₂ : H)⁻¹ * b'⁻¹ := by
      calc (c₂ : H) * (b' * c') * (c₂ : H)⁻¹ * (b' * c')⁻¹
          = (c₂ : H) * b' * (c' * (c₂ : H)⁻¹) * c'⁻¹ * b'⁻¹ := by group
        _ = (c₂ : H) * b' * ((c₂ : H)⁻¹ * c') * c'⁻¹ * b'⁻¹ := by rw [hc'c₂']
        _ = (c₂ : H) * b' * (c₂ : H)⁻¹ * b'⁻¹ := by group
    rwa [h2, hc₂] at h1
  have hcX : c ∈ X := by
    have := X.mul_mem (X.inv_mem hbX) (h.le_X ht)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  by_cases hc1 : c = 1
  · rw [hc1, mul_one]; exact hb
  · exfalso
    have hBX : B ≤ normalizer (X : Set H) := fun y hy =>
      h.inf_centralizer_le hcX hc1 1 (by simpa using hc2)
        (Subgroup.mem_inf.mpr ⟨mem_sup_right hy, by
          rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_iff.mp hc) y hy⟩)
    exact h.false_of_le_normalizer hBq hBeven hBX


theorem Hyp46.as76b_4_10_psl2 [Finite H] (h : Hyp46 B T X) {p f : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (e : B ≃* PSL(2, GaloisField p f)) :
    p ^ f ∈ ({5, 7, 9} : Finset ℕ) ∧ T ≤ B ⊔ centralizer (B : Set H) ∧
      (p ^ f ≠ 5 → T ≤ B) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hKodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, hpodd, hf, hK⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hK]; omega
  have hBq : Open.IsQuasisimple B := isQuasisimple_of_mulEquiv e.symm (isQuasisimple_psl2 h4)
  have hcardP : Nat.card PSL(2, GaloisField p f) = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
    rw [CFSG.GorensteinWalter.psl2_card_formula _ hKodd, hK]
  have hdP : HasDihedralSylowTwo PSL(2, GaloisField p f) :=
    hasDihedralSylowTwo_of_gw (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model _ hKodd)
  have hBeven : Even (Nat.card B) := by
    obtain ⟨S, n, hn, ⟨eS⟩⟩ := hdP
    have h1 : 2 ∣ Nat.card (S : Subgroup PSL(2, GaloisField p f)) := by
      rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
      exact dvd_mul_right 2 _
    rw [Nat.card_congr e.toEquiv]
    exact even_iff_two_dvd.mpr (h1.trans (Subgroup.card_subgroup_dvd_card _))
  have hZ : center B = ⊥ := center_eq_bot_of_psl2 h4 e
  set eQ : B ⧸ center B ≃* PSL(2, GaloisField p f) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  have hd : HasDihedralSylowTwo (B ⧸ center B) := hasDihedralSylowTwo_of_mulEquiv' eQ.symm hdP
  have hz : (Nat.card (center B)).factorization 2 ≤ 1 := by
    rw [hZ, Subgroup.card_bot, Nat.factorization_one]
    simp
  have hBX : ¬ B ≤ normalizer (X : Set H) := fun hBX => h.false_of_le_normalizer hBq hBeven hBX
  have hfour : ∀ U : Subgroup H, U ≤ T → IsFourGroup U →
      IsSmallDihedralSimple (B ⧸ center B) ∧ U ≤ B ⊔ centralizer (B : Set H) :=
    fun U hUT hU => FactsL2.dihedral_cover_generation_holds H B U hBq hd hz
      (hUT.trans h.le_normalizer) hU (h.not_le_centralizerJoin hBX hUT)
  have hinner : T ≤ B ⊔ centralizer (B : Set H) := by
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]; exact one_mem _
    obtain ⟨U, hUT, hU, htU⟩ := h.exists_isFourGroup_mem ht ht1
    exact (hfour U hUT hU).2 htU
  have hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ) := by
    obtain ⟨⟨t, ht⟩, ht1⟩ : ∃ t : T, t ≠ 1 := by
      have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by linarith [h.four_le])
      exact _root_.exists_ne 1
    obtain ⟨U, hUT, hU, -⟩ := h.exists_isFourGroup_mem ht (fun h1 => ht1 (Subtype.ext h1))
    have hsmall := (hfour U hUT hU).1
    have hcardQ : Nat.card (B ⧸ center B) = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr eQ.toEquiv, hcardP]
    rcases hsmall with ⟨⟨eA⟩⟩ | ⟨p', f', hq', hmodel⟩
    · exfalso
      have h1 := Nat.card_congr eA.toEquiv
      rw [hcardQ, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
      exact card_psl2_ne_2520 h5 hqodd (by rw [h1]; decide)
    · have : Fact p'.Prime := ⟨hmodel.1.1⟩
      obtain ⟨e'⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField _ 2 p'
        f' hmodel
      have hf' : f' ≠ 0 := by have := hmodel.1.2.1; omega
      have hp'odd : Odd p' := by
        refine (Fact.out : p'.Prime).odd_of_ne_two fun h2 => ?_
        subst h2
        have hev : Even (2 ^ f') := (Nat.even_pow.mpr ⟨even_two, hf'⟩)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
        rcases hq' with h1 | h1 | h1 <;> rw [h1] at hev <;> exact absurd hev (by decide)
      have hK' : Nat.card (GaloisField p' f') = p' ^ f' := GaloisField.card p' f' hf'
      have hcard' : Nat.card (B ⧸ center B) = p' ^ f' * ((p' ^ f') ^ 2 - 1) / 2 := by
        rw [Nat.card_congr e'.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _
          ⟨p', f', Fact.out, hp'odd, by omega, hK'⟩, hK']
      refine mem_five_seven_nine h5 hqodd ?_
      rw [← hcardQ, hcard']
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
      rcases hq' with h1 | h1 | h1 <;> rw [h1] <;> norm_num
  refine ⟨hq, hinner, fun hq5 => ?_⟩
  have hq79 : p ^ f = 7 ∨ p ^ f = 9 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    omega
  exact h.le_of_psl2_seven_nine hp hf hq79 e hBq hBeven hinner

end CFSG.ComponentClassification.RankTwoOddLie
