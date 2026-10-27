module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCases
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveLocal

public section

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoClassical CFSG.ComponentClassification.Asc75Lemma31

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G]

@[expose] def transvGroup (V V₀ : Subgroup G) : Subgroup G where
  carrier := {n | n ∈ normalizer (V : Set G) ∧ n ∈ centralizer (V₀ : Set G) ∧
    ∀ v ∈ V, v⁻¹ * (n * v * n⁻¹) ∈ V₀}
  mul_mem' := by
    rintro n m ⟨hnN, hnC, hn⟩ ⟨hmN, hmC, hm⟩
    refine ⟨mul_mem hnN hmN, mul_mem hnC hmC, fun v hv => ?_⟩
    have hw := hm v hv
    have hnw : n * (v⁻¹ * (m * v * m⁻¹)) * n⁻¹ = v⁻¹ * (m * v * m⁻¹) := by
      have := mem_centralizer_iff.mp hnC _ hw
      calc n * (v⁻¹ * (m * v * m⁻¹)) * n⁻¹ = v⁻¹ * (m * v * m⁻¹) * n * n⁻¹ := by
            rw [← this]
        _ = v⁻¹ * (m * v * m⁻¹) := by group
    have h1 : v⁻¹ * (n * m * v * (n * m)⁻¹) =
        (v⁻¹ * (n * v * n⁻¹)) * (n * (v⁻¹ * (m * v * m⁻¹)) * n⁻¹) := by group
    rw [h1, hnw]
    exact mul_mem (hn v hv) hw
  one_mem' := ⟨one_mem _, one_mem _, fun v hv => by simp⟩
  inv_mem' := by
    rintro n ⟨hnN, hnC, hn⟩
    refine ⟨inv_mem hnN, inv_mem hnC, fun v hv => ?_⟩
    have hu : n⁻¹ * v * n⁻¹⁻¹ ∈ V := (mem_normalizer_iff.mp (inv_mem hnN) v).mp hv
    have h1 := hn _ hu
    have h2 : n * (n⁻¹ * v * n⁻¹⁻¹) * n⁻¹ = v := by group
    rw [h2] at h1
    have h3 : v⁻¹ * (n⁻¹ * v * n⁻¹⁻¹) = (( n⁻¹ * v * n⁻¹⁻¹)⁻¹ * v)⁻¹ := by group
    rw [h3]
    exact inv_mem h1

theorem mem_transvGroup {V V₀ : Subgroup G} {n : G} : n ∈ transvGroup V V₀ ↔
    n ∈ normalizer (V : Set G) ∧ n ∈ centralizer (V₀ : Set G) ∧
      ∀ v ∈ V, v⁻¹ * (n * v * n⁻¹) ∈ V₀ := Iff.rfl

theorem mem_four {E : Subgroup G} [Finite G] (hE : Nat.card E = 4) (hE2 : ∀ x ∈ E, x * x = 1)
    {a b : G} (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) {w : G}
    (hw : w ∈ E) : w = 1 ∨ w = a ∨ w = b ∨ w = a * b := by
  classical
  have hab1 : a * b ≠ 1 := fun h1 => hab (by
    calc a = a * (b * b) := by rw [hE2 b hb, mul_one]
      _ = (a * b) * b := by group
      _ = b := by rw [h1, one_mul])
  have haba : a * b ≠ a := fun h1 => hb1 (by
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h1, inv_mul_cancel])
  have habb : a * b ≠ b := fun h1 => ha1 (by
    calc a = (a * b) * b⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel])
  set s : Finset G := {1, a, b, a * b} with hs
  have hcard : s.card = 4 := by
    rw [hs, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair habb.symm]
    · simp [hab, haba.symm]
    · simp [ha1.symm, hb1.symm, hab1.symm]
  have hsub : (s : Set G) ⊆ (E : Set G) := by
    intro x hx
    simp only [hs, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem E
    · exact ha
    · exact hb
    · exact mul_mem ha hb
  have heq : (s : Set G) = (E : Set G) := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [Set.ncard_coe_finset, hcard, ← hE]
    exact (Nat.card_coe_set_eq _).ge
  have hw' : w ∈ (s : Set G) := heq ▸ hw
  simpa [hs] using hw'

theorem exists_ne_one_ne {E : Subgroup G} [Finite G] (hE : Nat.card E = 4)
    (hE2 : ∀ x ∈ E, x * x = 1) {z : G} (hz : z ∈ E) : ∃ c ∈ E, c ≠ 1 ∧ c ≠ z := by
  by_contra hc
  push Not at hc
  have hle : E ≤ zpowers z := fun w hw => by
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    · rw [hc w hw hw1]
      exact mem_zpowers z
  have h1 := Subgroup.card_le_of_le hle
  rw [hE, Nat.card_zpowers] at h1
  have h2 : orderOf z ≤ 2 := orderOf_le_of_pow_eq_one two_pos (by rw [sq]; exact hE2 z hz)
  omega

theorem conj_ne_of_trans {E : Subgroup G} [Finite G] (hE : Nat.card E = 4)
    (hE2 : ∀ x ∈ E, x * x = 1) {y : G}
    (htr : ∀ b ∈ E, ∀ c ∈ E, b ≠ 1 → c ≠ 1 → ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c) {z : G}
    (hz : z ∈ E) (hz1 : z ≠ 1) : y⁻¹ * z * y ≠ z := by
  intro hfix
  obtain ⟨c, hc, hc1, hcz⟩ := exists_ne_one_ne hE hE2 hz
  obtain ⟨k, hk⟩ := htr z hz c hc hz1 hc1
  have hpow : ∀ k : ℕ, (y ^ k)⁻¹ * z * y ^ k = z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (y ^ (k + 1))⁻¹ * z * y ^ (k + 1) = y⁻¹ * ((y ^ k)⁻¹ * z * y ^ k) * y := by group
        _ = z := by rw [ih, hfix]
  exact hcz (hk ▸ hpow k)

theorem conj_conj_eq_mul {E : Subgroup G} [Finite G] (hE : Nat.card E = 4)
    (hE2 : ∀ x ∈ E, x * x = 1) {c : G} (hcN : c ∈ normalizer (E : Set G)) (hc3 : c ^ 3 = 1)
    (hcf : ∀ x ∈ E, x ≠ 1 → c⁻¹ * x * c ≠ x) {z : G} (hz : z ∈ E) (hz1 : z ≠ 1) :
    c⁻¹ * (c⁻¹ * z * c) * c = z * (c⁻¹ * z * c) := by
  have hcE : ∀ x ∈ E, c⁻¹ * x * c ∈ E := fun x hx => by
    simpa using (mem_normalizer_iff.mp (inv_mem hcN) x).mp hx
  have hne1 : ∀ {x : G}, x ≠ 1 → c⁻¹ * x * c ≠ 1 := fun {x} hx h1 => hx (by
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, c⁻¹ * z * c = z₁ := ⟨_, rfl⟩
  have hz₁E : z₁ ∈ E := hz₁ ▸ hcE z hz
  have hz₁1 : z₁ ≠ 1 := hz₁ ▸ hne1 hz1
  have hz₁z : z₁ ≠ z := hz₁ ▸ hcf z hz hz1
  have hcube : c⁻¹ * (c⁻¹ * (c⁻¹ * z * c) * c) * c = z := by
    have hy' : c * c * c = 1 := by
      rw [pow_succ, pow_succ, pow_one] at hc3
      exact hc3
    calc c⁻¹ * (c⁻¹ * (c⁻¹ * z * c) * c) * c = (c * c * c)⁻¹ * z * (c * c * c) := by group
      _ = z := by rw [hy']; group
  have hw := hcE z₁ hz₁E
  have hw1 : c⁻¹ * z₁ * c ≠ 1 := hne1 hz₁1
  have hwz₁ : c⁻¹ * z₁ * c ≠ z₁ := hcf z₁ hz₁E hz₁1
  have hwz : c⁻¹ * z₁ * c ≠ z := fun h1 => hz₁z (by
    rw [hz₁, h1, hz₁] at hcube
    exact hcube)
  rw [hz₁]
  rcases mem_four hE hE2 hz hz₁E hz1 hz₁1 hz₁z.symm hw with h1 | h1 | h1 | h1
  · exact absurd h1 hw1
  · exact absurd h1 hwz
  · exact absurd h1 hwz₁
  · exact h1

theorem conj_eq_of_eq_at {E : Subgroup G} [Finite G] (hE : Nat.card E = 4)
    (hE2 : ∀ x ∈ E, x * x = 1) {c d : G} (hcN : c ∈ normalizer (E : Set G))
    (hdN : d ∈ normalizer (E : Set G)) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcf : ∀ x ∈ E, x ≠ 1 → c⁻¹ * x * c ≠ x) (hdf : ∀ x ∈ E, x ≠ 1 → d⁻¹ * x * d ≠ x)
    {z : G} (hz : z ∈ E) (hz1 : z ≠ 1) (heq : d⁻¹ * z * d = c⁻¹ * z * c) :
    ∀ x ∈ E, d⁻¹ * x * d = c⁻¹ * x * c := by
  have hcE : ∀ x ∈ E, c⁻¹ * x * c ∈ E := fun x hx => by
    simpa using (mem_normalizer_iff.mp (inv_mem hcN) x).mp hx
  have hdE : ∀ x ∈ E, d⁻¹ * x * d ∈ E := fun x hx => by
    simpa using (mem_normalizer_iff.mp (inv_mem hdN) x).mp hx
  have hne1 : ∀ (y : G) {x : G}, x ≠ 1 → y⁻¹ * x * y ≠ 1 := fun y x hx h1 => hx (by
    calc x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, c⁻¹ * z * c = z₁ := ⟨_, rfl⟩
  rw [hz₁] at heq
  have hz₁E : z₁ ∈ E := hz₁ ▸ hcE z hz
  have hz₁1 : z₁ ≠ 1 := hz₁ ▸ hne1 c hz1
  have hz₁z : z₁ ≠ z := hz₁ ▸ hcf z hz hz1
  have hcube : ∀ (y : G), y ^ 3 = 1 → y⁻¹ * (y⁻¹ * (y⁻¹ * z * y) * y) * y = z := by
    intro y hy
    have hy' : y * y * y = 1 := by
      rw [pow_succ, pow_succ, pow_one] at hy
      exact hy
    calc y⁻¹ * (y⁻¹ * (y⁻¹ * z * y) * y) * y = (y * y * y)⁻¹ * z * (y * y * y) := by group
      _ = z := by rw [hy']; group
  have hz₂ : c⁻¹ * z₁ * c = z * z₁ := by
    have hw := hcE z₁ hz₁E
    have hw1 : c⁻¹ * z₁ * c ≠ 1 := hne1 c hz₁1
    have hwz₁ : c⁻¹ * z₁ * c ≠ z₁ := hcf z₁ hz₁E hz₁1
    have hwz : c⁻¹ * z₁ * c ≠ z := fun h1 => hz₁z (by
      have h2 := hcube c hc3
      rw [hz₁, h1, hz₁] at h2
      exact h2)
    rcases mem_four hE hE2 hz hz₁E hz1 hz₁1 hz₁z.symm hw with h1 | h1 | h1 | h1
    · exact absurd h1 hw1
    · exact absurd h1 hwz
    · exact absurd h1 hwz₁
    · exact h1
  have hdz₁ : d⁻¹ * z₁ * d = z * z₁ := by
    have hw := hdE z₁ hz₁E
    have hw1 : d⁻¹ * z₁ * d ≠ 1 := hne1 d hz₁1
    have hwz₁ : d⁻¹ * z₁ * d ≠ z₁ := hdf z₁ hz₁E hz₁1
    have hwz : d⁻¹ * z₁ * d ≠ z := fun h1 => hz₁z (by
      have h2 := hcube d hd3
      rw [heq, h1, heq] at h2
      exact h2)
    rcases mem_four hE hE2 hz hz₁E hz1 hz₁1 hz₁z.symm hw with h1 | h1 | h1 | h1
    · exact absurd h1 hw1
    · exact absurd h1 hwz
    · exact absurd h1 hwz₁
    · exact h1
  intro x hx
  rcases mem_four hE hE2 hz hz₁E hz1 hz₁1 hz₁z.symm hx with rfl | rfl | rfl | rfl
  · group
  · rw [heq, hz₁]
  · rw [hdz₁, hz₂]
  · calc d⁻¹ * (z * z₁) * d = (d⁻¹ * z * d) * (d⁻¹ * z₁ * d) := by group
      _ = (c⁻¹ * z * c) * (c⁻¹ * z₁ * c) := by rw [heq, hdz₁, hz₂, hz₁]
      _ = c⁻¹ * (z * z₁) * c := by group

@[expose] def transvHom {R T V₀ : Subgroup G} {r₀ : G} (hr₀ : r₀ ∈ R) :
    ↥(transvGroup (R ⊔ T) V₀) →* ↥V₀ where
  toFun n := ⟨r₀⁻¹ * (n * r₀ * (n : G)⁻¹), n.2.2.2 r₀ (mem_sup_left hr₀)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' n m := by
    apply Subtype.ext
    have hm := m.2.2.2 r₀ (mem_sup_left hr₀)
    have hnc := mem_centralizer_iff.mp n.2.2.1 _ hm
    simp only [coe_mul]
    calc r₀⁻¹ * ((n : G) * m * r₀ * ((n : G) * m)⁻¹) =
        r₀⁻¹ * ((n : G) * r₀ * (n : G)⁻¹) *
          ((n : G) * (r₀⁻¹ * ((m : G) * r₀ * (m : G)⁻¹)) * (n : G)⁻¹) := by group
      _ = r₀⁻¹ * ((n : G) * r₀ * (n : G)⁻¹) * (r₀⁻¹ * ((m : G) * r₀ * (m : G)⁻¹)) := by
        rw [← hnc]
        group

namespace Setting310

variable [Finite G] {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

theorem V₀_le : V₀ ≤ R ⊔ T := h.loc.inf_A ▸ inf_le_left

theorem V₀_le_A : V₀ ≤ A := h.loc.inf_A ▸ inf_le_right

theorem comm {a b : G} (ha : a ∈ R ⊔ T) (hb : b ∈ R ⊔ T) : a * b = b * a :=
  congrArg Subtype.val (h.loc.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem mul_self {v : G} (hv : v ∈ R ⊔ T) : v * v = 1 := by
  rw [← sq]
  exact h.loc.elem.2 v hv

theorem inf_R_V₀ : R ⊓ V₀ = ⊥ := by
  have h1 := h.loc.spread 1 (by rw [rightConjugate_one]; exact le_sup_left)
  rwa [rightConjugate_one] at h1

theorem sup_R_V₀ : R ⊔ V₀ = R ⊔ T := by
  have hV₀N : V₀ ≤ normalizer (R : Set G) :=
    (h.V₀_le_A.trans (le_centralizer_iff.mp h.sylowR.le)).trans (centralizer_le_normalizer _)
  have hc := card_sup_eq_mul hV₀N h.inf_R_V₀
  rw [h.cardR, h.card_V₀] at hc
  exact eq_of_le_of_card_ge (sup_le le_sup_left h.V₀_le) (by rw [hc, h.loc.card])

theorem exists_mul {v : G} (hv : v ∈ R ⊔ T) : ∃ r ∈ R, ∃ w ∈ V₀, v = r * w := by
  have hV₀N : V₀ ≤ normalizer (R : Set G) :=
    (h.V₀_le_A.trans (le_centralizer_iff.mp h.sylowR.le)).trans (centralizer_le_normalizer _)
  rw [← h.sup_R_V₀] at hv
  obtain ⟨r, hr, w, hw, hrw⟩ := exists_mul_of_mem_sup_of_le_normalizer hV₀N hv
  exact ⟨r, hr, w, hw, hrw⟩

theorem inf_K : (R ⊔ T) ⊓ centralizer (A : Set G) = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥((R ⊔ T) ⊓ centralizer (A : Set G)) :=
    (IsPGroup.of_card (n := 4) (by rw [h.loc.card]; rfl)).to_le inf_le_left
  exact h.sylowR.eq_of_le (le_inf le_sup_left h.sylowR.le) inf_le_right hp

theorem inf_eq_bot_of_ne {x : G} (hx : rightConjugate R x ≤ R ⊔ T)
    (hne : rightConjugate R x ≠ R) : rightConjugate R x ⊓ R = ⊥ := by
  have hKte := tightlyEmbedded_centralizer h.hyp.standard
  have hxK : x ∉ normalizer (centralizer (A : Set G) : Set G) := by
    intro hxN
    apply hne
    have h1 : rightConjugate R x ≤ R := by
      have h2 := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) h.sylowR.le
      change rightConjugate R x ≤ rightConjugate (centralizer (A : Set G)) x at h2
      rw [(rightConjugate_eq_self_iff _ x).mpr hxN] at h2
      have h3 : rightConjugate R x ≤ (R ⊔ T) ⊓ centralizer (A : Set G) := le_inf hx h2
      rwa [h.inf_K] at h3
    exact eq_of_le_of_card_ge h1 (by rw [rightConjugate_card])
  have h1 := two_subgroup_inf_conjugate_eq_bot _ _ hKte (h.sylowR.isPGroup.map _) x hxK
    (map_mono h.sylowR.le)
  rw [eq_bot_iff, ← h1]
  exact inf_le_inf_left _ h.sylowR.le

theorem centralizer_le_transvGroup :
    centralizer ((R ⊔ T : Subgroup G) : Set G) ≤ transvGroup (R ⊔ T) V₀ := by
  intro n hn
  refine ⟨centralizer_le_normalizer _ hn, centralizer_le (fun v hv => h.V₀_le hv) hn,
    fun v hv => ?_⟩
  have h1 : n * v * n⁻¹ = v := by
    rw [← mem_centralizer_iff.mp hn v hv]
    group
  rw [h1, inv_mul_cancel]
  exact one_mem _

theorem mem_centralizer_of_transv_of_eq {n : G} (hn : n ∈ transvGroup (R ⊔ T) V₀)
    (hR : rightConjugate R n⁻¹ = R) : n ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  obtain ⟨hnN, hnC, hnV⟩ := hn
  have hr : ∀ r ∈ R, n * r * n⁻¹ = r := by
    intro r hr
    have h1 : n * r * n⁻¹ ∈ R := by
      rw [← hR, mem_rightConjugate_iff, inv_inv]
      convert hr using 1
      group
    have h2 : r⁻¹ * (n * r * n⁻¹) ∈ R ⊓ V₀ :=
      mem_inf.mpr ⟨mul_mem (inv_mem hr) h1, hnV r (mem_sup_left hr)⟩
    rw [h.inf_R_V₀, mem_bot] at h2
    calc n * r * n⁻¹ = r * (r⁻¹ * (n * r * n⁻¹)) := by group
      _ = r := by rw [h2, mul_one]
  rw [mem_centralizer_iff]
  intro v hv
  obtain ⟨r, hr', w, hw, rfl⟩ := h.exists_mul hv
  have hw' : n * w * n⁻¹ = w := by
    rw [← mem_centralizer_iff.mp hnC w hw]
    group
  calc r * w * n = n * (n⁻¹ * (r * w) * n) := by group
    _ = n * (r * w) := by
      congr 1
      have h1 : n⁻¹ * r * n = r := by
        have := hr r hr'
        calc n⁻¹ * r * n = n⁻¹ * (n * r * n⁻¹) * n := by rw [this]
          _ = r := by group
      have h2 : n⁻¹ * w * n = w := by
        calc n⁻¹ * w * n = n⁻¹ * (n * w * n⁻¹) * n := by rw [hw']
          _ = w := by group
      calc n⁻¹ * (r * w) * n = (n⁻¹ * r * n) * (n⁻¹ * w * n) := by group
        _ = r * w := by rw [h1, h2]

theorem mem_V₀_of_fixed {n : G} (hn : n ∈ transvGroup (R ⊔ T) V₀)
    (hnC : n ∉ centralizer ((R ⊔ T : Subgroup G) : Set G)) {v : G} (hv : v ∈ R ⊔ T)
    (hfix : n * v * n⁻¹ = v) : v ∈ V₀ := by
  obtain ⟨hnN, hnC₀, hnV⟩ := hn
  obtain ⟨r, hr, w, hw, rfl⟩ := h.exists_mul hv
  have hw' : n * w * n⁻¹ = w := by
    rw [← mem_centralizer_iff.mp hnC₀ w hw]
    group
  have hrr : n * r * n⁻¹ = r := by
    have h1 : n * (r * w) * n⁻¹ = (n * r * n⁻¹) * (n * w * n⁻¹) := by group
    rw [h1, hw'] at hfix
    exact mul_right_cancel hfix
  have hne : rightConjugate R n⁻¹ ≠ R := fun hR =>
    hnC (h.mem_centralizer_of_transv_of_eq ⟨hnN, hnC₀, hnV⟩ hR)
  have hle : rightConjugate R n⁻¹ ≤ R ⊔ T :=
    Lemma36.rightConjugate_le le_sup_left (inv_mem hnN)
  have h1 : r ∈ rightConjugate R n⁻¹ ⊓ R := by
    refine mem_inf.mpr ⟨?_, hr⟩
    rw [mem_rightConjugate_iff, inv_inv]
    have h2 : n⁻¹ * r * n = r := by
      calc n⁻¹ * r * n = n⁻¹ * (n * r * n⁻¹) * n := by rw [hrr]
        _ = r := by group
    rw [h2]
    exact hr
  rw [h.inf_eq_bot_of_ne hle hne, mem_bot] at h1
  rw [h1, one_mul]
  exact hw

theorem mul_self_mem_centralizer {n : G} (hn : n ∈ transvGroup (R ⊔ T) V₀) :
    n * n ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  obtain ⟨hnN, hnC₀, hnV⟩ := hn
  rw [mem_centralizer_iff]
  intro v hv
  set c := v⁻¹ * (n * v * n⁻¹) with hc
  have hcV₀ : c ∈ V₀ := hnV v hv
  have h1 : n * v * n⁻¹ = v * c := by rw [hc]; group
  have h2 : n * c * n⁻¹ = c := by
    rw [← mem_centralizer_iff.mp hnC₀ c hcV₀]
    group
  have h3 : n * n * v * (n * n)⁻¹ = v := by
    calc n * n * v * (n * n)⁻¹ = n * (n * v * n⁻¹) * n⁻¹ := by group
      _ = n * (v * c) * n⁻¹ := by rw [h1]
      _ = (n * v * n⁻¹) * (n * c * n⁻¹) := by group
      _ = v * c * c := by rw [h1, h2]
      _ = v := by rw [mul_assoc, h.mul_self (h.V₀_le hcV₀), mul_one]
  calc v * (n * n) = n * n * v * (n * n)⁻¹ * (n * n) := by rw [h3]
    _ = n * n * v := by group

theorem commutator_mem_centralizer {n m : G} (hn : n ∈ transvGroup (R ⊔ T) V₀)
    (hm : m ∈ transvGroup (R ⊔ T) V₀) :
    n * m * n⁻¹ * m⁻¹ ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  obtain ⟨hnN, hnC₀, hnV⟩ := hn
  obtain ⟨hmN, hmC₀, hmV⟩ := hm
  have hnm : ∀ v ∈ R ⊔ T, n * m * v * (n * m)⁻¹ = m * n * v * (m * n)⁻¹ := by
    intro v hv
    obtain ⟨c, hc⟩ : ∃ c, v⁻¹ * (n * v * n⁻¹) = c := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, v⁻¹ * (m * v * m⁻¹) = d := ⟨_, rfl⟩
    have hcV₀ : c ∈ V₀ := hc ▸ hnV v hv
    have hdV₀ : d ∈ V₀ := hd ▸ hmV v hv
    have h1 : n * v * n⁻¹ = v * c := by rw [← hc]; group
    have h2 : m * v * m⁻¹ = v * d := by rw [← hd]; group
    have hnd : n * d * n⁻¹ = d := by
      rw [← mem_centralizer_iff.mp hnC₀ d hdV₀]
      group
    have hmc : m * c * m⁻¹ = c := by
      rw [← mem_centralizer_iff.mp hmC₀ c hcV₀]
      group
    calc n * m * v * (n * m)⁻¹ = n * (m * v * m⁻¹) * n⁻¹ := by group
      _ = n * (v * d) * n⁻¹ := by rw [h2]
      _ = (n * v * n⁻¹) * (n * d * n⁻¹) := by group
      _ = v * c * d := by rw [h1, hnd]
      _ = v * d * c := by
        rw [mul_assoc, mul_assoc, h.comm (h.V₀_le hcV₀) (h.V₀_le hdV₀)]
      _ = (m * v * m⁻¹) * (m * c * m⁻¹) := by rw [h2, hmc]
      _ = m * (v * c) * m⁻¹ := by group
      _ = m * (n * v * n⁻¹) * m⁻¹ := by rw [h1]
      _ = m * n * v * (m * n)⁻¹ := by group
  rw [mem_centralizer_iff]
  intro v hv
  have hu : (m * n)⁻¹ * v * (m * n) ∈ R ⊔ T := by
    have := (mem_normalizer_iff.mp (inv_mem (mul_mem hmN hnN)) v).mp hv
    simpa [mul_assoc] using this
  have h1 := hnm _ hu
  have h2 : m * n * ((m * n)⁻¹ * v * (m * n)) * (m * n)⁻¹ = v := by group
  rw [h2] at h1
  have h3 : n * m * n⁻¹ * m⁻¹ * v * (n * m * n⁻¹ * m⁻¹)⁻¹ = v := by
    calc n * m * n⁻¹ * m⁻¹ * v * (n * m * n⁻¹ * m⁻¹)⁻¹ =
        n * m * ((m * n)⁻¹ * v * (m * n)) * (n * m)⁻¹ := by group
      _ = v := h1
  calc v * (n * m * n⁻¹ * m⁻¹) =
      n * m * n⁻¹ * m⁻¹ * v * (n * m * n⁻¹ * m⁻¹)⁻¹ * (n * m * n⁻¹ * m⁻¹) := by rw [h3]
    _ = n * m * n⁻¹ * m⁻¹ * v := by group

theorem sup_T_V₀ : T ⊓ V₀ = ⊥ ∧ T ⊔ V₀ = R ⊔ T := by
  obtain ⟨xT, hTx, -⟩ := Lemma36.exists_conj_eq h.sylowR h.loc.sylowT
  have hTV : T ≤ R ⊔ T := le_sup_right
  have hTV₀ : T ⊓ V₀ = ⊥ := by
    have h1 := h.loc.spread xT (hTx ▸ hTV)
    rwa [← hTx] at h1
  refine ⟨hTV₀, ?_⟩
  have hV₀N : V₀ ≤ normalizer (T : Set G) := le_normalizer_of_le h.loc.elem hTV h.V₀_le
  have hc := card_sup_eq_mul hV₀N hTV₀
  rw [hTx, rightConjugate_card, h.cardR, h.card_V₀] at hc
  rw [← hTx] at hc
  exact eq_of_le_of_card_ge (sup_le hTV h.V₀_le) (by rw [hc, h.loc.card])

theorem exists_mul_T {v : G} (hv : v ∈ R ⊔ T) : ∃ t ∈ T, ∃ w ∈ V₀, v = t * w := by
  have hV₀N : V₀ ≤ normalizer (T : Set G) := le_normalizer_of_le h.loc.elem le_sup_right h.V₀_le
  rw [← h.sup_T_V₀.2] at hv
  obtain ⟨t, ht, w, hw, htw⟩ := exists_mul_of_mem_sup_of_le_normalizer hV₀N hv
  exact ⟨t, ht, w, hw, htw⟩

omit [Finite G] h in
theorem mod_triv_of_centralizer {Q : Subgroup G} (hQ : ∀ v ∈ R ⊔ T, ∃ q ∈ Q, ∃ w ∈ V₀, v = q * w)
    {b : G} (hbQ : b ∈ centralizer (Q : Set G)) (hbN : b ∈ normalizer (V₀ : Set G)) {v : G}
    (hv : v ∈ R ⊔ T) : v⁻¹ * (b * v * b⁻¹) ∈ V₀ := by
  obtain ⟨q, hq, w, hw, rfl⟩ := hQ v hv
  have h1 : b * q * b⁻¹ = q := by rw [← mem_centralizer_iff.mp hbQ q hq]; group
  have h2 : b * w * b⁻¹ ∈ V₀ := (mem_normalizer_iff.mp hbN w).mp hw
  have h3 : (q * w)⁻¹ * (b * (q * w) * b⁻¹) = w⁻¹ * (b * w * b⁻¹) := by
    calc (q * w)⁻¹ * (b * (q * w) * b⁻¹) = w⁻¹ * q⁻¹ * ((b * q * b⁻¹) * (b * w * b⁻¹)) := by
          group
      _ = w⁻¹ * (b * w * b⁻¹) := by rw [h1]; group
  rw [h3]
  exact mul_mem (inv_mem hw) h2

omit [Finite G] h in
theorem mod_triv_mul {b c : G} (hcN : c ∈ normalizer ((R ⊔ T : Subgroup G) : Set G))
    (hb : ∀ v ∈ R ⊔ T, v⁻¹ * (b * v * b⁻¹) ∈ V₀) (hc : ∀ v ∈ R ⊔ T, v⁻¹ * (c * v * c⁻¹) ∈ V₀)
    {v : G} (hv : v ∈ R ⊔ T) : v⁻¹ * (b * c * v * (b * c)⁻¹) ∈ V₀ := by
  have hcv : c * v * c⁻¹ ∈ R ⊔ T := (mem_normalizer_iff.mp hcN v).mp hv
  have h1 : v⁻¹ * (b * c * v * (b * c)⁻¹) =
      (v⁻¹ * (c * v * c⁻¹)) * ((c * v * c⁻¹)⁻¹ * (b * (c * v * c⁻¹) * b⁻¹)) := by group
  rw [h1]
  exact mul_mem (hc v hv) (hb _ hcv)

theorem exists_transv : ∃ u ∈ transvGroup (R ⊔ T) V₀,
    u ∉ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  obtain ⟨eA⟩ := h.equiv
  have hV₀2 : ∀ x ∈ V₀, x * x = 1 := fun x hx => h.mul_self (h.V₀_le hx)
  obtain ⟨b₀, hb₀A, hb₀N, hb₀3, hb₀tr, -⟩ := exists_klein_three eA h.V₀_le_A h.card_V₀
  obtain ⟨b₁, hb₁A, hb₁N, hb₁3, hb₁tr, -⟩ :=
    exists_klein_three ((conjEquiv A g).trans eA) h.loc.V₀_le h.card_V₀
  have hb₀R : b₀ ∈ centralizer (R : Set G) := le_centralizer_iff.mp h.sylowR.le hb₀A
  have hb₁T : b₁ ∈ centralizer (T : Set G) := by
    have hTK : T ≤ centralizer (rightConjugate A g : Set G) := by
      rw [centralizer_rightConjugate]
      exact h.loc.sylowT.le
    exact le_centralizer_iff.mp hTK hb₁A
  have hb₀f : ∀ x ∈ V₀, x ≠ 1 → b₀⁻¹ * x * b₀ ≠ x := fun x hx hx1 =>
    conj_ne_of_trans h.card_V₀ hV₀2 hb₀tr hx hx1
  have hb₁f : ∀ x ∈ V₀, x ≠ 1 → b₁⁻¹ * x * b₁ ≠ x := fun x hx hx1 =>
    conj_ne_of_trans h.card_V₀ hV₀2 hb₁tr hx hx1
  have hb₀3' : b₀ ^ 3 = 1 := hb₀3 ▸ pow_orderOf_eq_one b₀
  have hb₁3' : b₁ ^ 3 = 1 := hb₁3 ▸ pow_orderOf_eq_one b₁
  have hb₀sq3 : (b₀ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hb₀3', one_pow]
  have hb₀sqf : ∀ x ∈ V₀, x ≠ 1 → (b₀ ^ 2)⁻¹ * x * b₀ ^ 2 ≠ x := by
    intro x hx hx1 hfix
    apply hb₀f x hx hx1
    have h4 : b₀ ^ 4 = b₀ := by
      rw [show 4 = 3 + 1 by rfl, pow_succ, hb₀3', one_mul]
    calc b₀⁻¹ * x * b₀ = (b₀ ^ 4)⁻¹ * x * b₀ ^ 4 := by rw [h4]
      _ = (b₀ ^ 2)⁻¹ * ((b₀ ^ 2)⁻¹ * x * b₀ ^ 2) * b₀ ^ 2 := by group
      _ = x := by rw [hfix, hfix]
  obtain ⟨z, hz, hz1, -⟩ := exists_ne_one_ne h.card_V₀ hV₀2 (one_mem V₀)
  have hcE : ∀ (y : G), y ∈ normalizer (V₀ : Set G) → ∀ x ∈ V₀, y⁻¹ * x * y ∈ V₀ :=
    fun y hy x hx => by simpa using (mem_normalizer_iff.mp (inv_mem hy) x).mp hx
  have hne1 : ∀ (y : G) {x : G}, x ≠ 1 → y⁻¹ * x * y ≠ 1 := fun y x hx h1 => hx (by
    calc x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨c, hcN, hcA, hcf, hceq⟩ : ∃ c : G, c ∈ normalizer (V₀ : Set G) ∧ c ∈ A ∧
      (∀ x ∈ V₀, x ≠ 1 → c⁻¹ * x * c ≠ x) ∧ ∀ x ∈ V₀, b₁⁻¹ * x * b₁ = c⁻¹ * x * c := by
    have hw := hcE b₁ hb₁N z hz
    have hz₁ := hcE b₀ hb₀N z hz
    rcases mem_four h.card_V₀ hV₀2 hz hz₁ hz1 (hne1 b₀ hz1) (hb₀f z hz hz1).symm hw with
      h1 | h1 | h1 | h1
    · exact absurd h1 (hne1 b₁ hz1)
    · exact absurd h1 (hb₁f z hz hz1)
    · exact ⟨b₀, hb₀N, hb₀A, hb₀f, conj_eq_of_eq_at h.card_V₀ hV₀2 hb₀N hb₁N hb₀3' hb₁3'
        hb₀f hb₁f hz hz1 h1⟩
    · refine ⟨b₀ ^ 2, pow_mem hb₀N 2, pow_mem hb₀A 2, hb₀sqf, conj_eq_of_eq_at h.card_V₀ hV₀2
        (pow_mem hb₀N 2) hb₁N hb₀sq3 hb₁3' hb₀sqf hb₁f hz hz1 ?_⟩
      rw [h1, pow_two, mul_inv_rev]
      have h2 := conj_conj_eq_mul h.card_V₀ hV₀2 hb₀N hb₀3' hb₀f hz hz1
      rw [← h2]
      group
  have hcR : c ∈ centralizer (R : Set G) := le_centralizer_iff.mp h.sylowR.le hcA
  have hRV₀ : ∀ v ∈ R ⊔ T, ∃ q ∈ R, ∃ w ∈ V₀, v = q * w := fun v hv => h.exists_mul hv
  have hTV₀ : ∀ v ∈ R ⊔ T, ∃ q ∈ T, ∃ w ∈ V₀, v = q * w := fun v hv => h.exists_mul_T hv
  have hcV : c ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := by
    rw [← h.sup_R_V₀]
    exact mem_normalizer_sup (centralizer_le_normalizer _ hcR) hcN
  have hb₁V : b₁ ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := by
    rw [← h.sup_T_V₀.2]
    exact mem_normalizer_sup (centralizer_le_normalizer _ hb₁T) hb₁N
  refine ⟨c * b₁⁻¹, ⟨mul_mem hcV (inv_mem hb₁V), ?_, fun v hv => ?_⟩, fun hu => ?_⟩
  ·
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := hceq x hx
    calc x * (c * b₁⁻¹) = c * (c⁻¹ * x * c) * b₁⁻¹ := by group
      _ = c * (b₁⁻¹ * x * b₁) * b₁⁻¹ := by rw [h1]
      _ = c * b₁⁻¹ * x := by group
  ·
    exact mod_triv_mul (inv_mem hb₁V)
      (fun v hv => mod_triv_of_centralizer hRV₀ hcR hcN hv)
      (fun v hv => mod_triv_of_centralizer hTV₀ (inv_mem hb₁T) (inv_mem hb₁N) hv) hv
  ·
    have hcT : c ∈ centralizer (T : Set G) := by
      rw [mem_centralizer_iff]
      intro t ht
      have h1 := mem_centralizer_iff.mp hu t (mem_sup_right ht)
      have h2 := mem_centralizer_iff.mp hb₁T t ht
      calc t * c = t * (c * b₁⁻¹) * b₁ := by group
        _ = c * b₁⁻¹ * t * b₁ := by rw [h1]
        _ = c * b₁⁻¹ * (t * b₁) := by group
        _ = c * b₁⁻¹ * (b₁ * t) := by rw [h2]
        _ = c * t := by group
    have hcVc : c ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
      have h1 : zpowers c ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
        rw [le_centralizer_iff]
        exact sup_le (le_centralizer_iff.mp (zpowers_le.mpr hcR))
          (le_centralizer_iff.mp (zpowers_le.mpr hcT))
      exact h1 (mem_zpowers c)
    apply hcf z hz hz1
    have h1 := mem_centralizer_iff.mp hcVc z (h.V₀_le hz)
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [h1]
      _ = z := by group

omit [Finite G] h in
theorem transvGroup_normal {n : G} (hnN : n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G))
    (hnN₀ : n ∈ normalizer (V₀ : Set G)) {u : G} (hu : u ∈ transvGroup (R ⊔ T) V₀) :
    n * u * n⁻¹ ∈ transvGroup (R ⊔ T) V₀ := by
  obtain ⟨huN, huC, huV⟩ := hu
  refine ⟨mul_mem (mul_mem hnN huN) (inv_mem hnN), ?_, fun v hv => ?_⟩
  · rw [mem_centralizer_iff]
    intro w hw
    have hw' : n⁻¹ * w * n ∈ V₀ := by
      simpa using (mem_normalizer_iff.mp (inv_mem hnN₀) w).mp hw
    have h1 := mem_centralizer_iff.mp huC _ hw'
    calc w * (n * u * n⁻¹) = n * ((n⁻¹ * w * n) * u) * n⁻¹ := by group
      _ = n * (u * (n⁻¹ * w * n)) * n⁻¹ := by rw [h1]
      _ = n * u * n⁻¹ * w := by group
  · have hv' : n⁻¹ * v * n ∈ R ⊔ T := by
      simpa using (mem_normalizer_iff.mp (inv_mem hnN) v).mp hv
    have h1 := huV _ hv'
    have h2 : v⁻¹ * (n * u * n⁻¹ * v * (n * u * n⁻¹)⁻¹) =
        n * ((n⁻¹ * v * n)⁻¹ * (u * (n⁻¹ * v * n) * u⁻¹)) * n⁻¹ := by group
    rw [h2]
    exact (mem_normalizer_iff.mp hnN₀ _).mp h1

theorem normalizer_le_normalizer_V₀ :
    normalizer ((R ⊔ T : Subgroup G) : Set G) ≤ normalizer (V₀ : Set G) := by
  have key : ∀ n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G), ∀ w ∈ V₀, n * w * n⁻¹ ∈ V₀ := by
    intro n hn w hw
    have hwV : n * w * n⁻¹ ∈ R ⊔ T := (mem_normalizer_iff.mp hn w).mp (h.V₀_le hw)
    by_contra hnot
    obtain ⟨x, hxV, hwx⟩ := h.loc.cover _ hwV hnot
    have hle : rightConjugate R (x * n) ≤ R ⊔ T := by
      rw [← rightConjugate_mul]
      exact Lemma36.rightConjugate_le hxV hn
    have hw' : w ∈ rightConjugate R (x * n) ⊓ V₀ := by
      refine mem_inf.mpr ⟨?_, hw⟩
      rw [← rightConjugate_mul, mem_rightConjugate_iff]
      exact hwx
    rw [h.loc.spread _ hle, mem_bot] at hw'
    apply hnot
    rw [hw']
    simp
  intro n hn
  rw [mem_normalizer_iff]
  intro w
  refine ⟨key n hn w, fun hw => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hw
  simpa [mul_assoc] using this

theorem ker_transvHom {r₀ : G} (hr₀ : r₀ ∈ R) (hr₀1 : r₀ ≠ 1) :
    (transvHom (T := T) (V₀ := V₀) hr₀).ker =
      (centralizer ((R ⊔ T : Subgroup G) : Set G)).subgroupOf (transvGroup (R ⊔ T) V₀) := by
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro hn
    by_contra hnC
    have h1 : (n : G) * r₀ * (n : G)⁻¹ = r₀ := by
      have h2 := congrArg Subtype.val hn
      change r₀⁻¹ * ((n : G) * r₀ * (n : G)⁻¹) = 1 at h2
      calc (n : G) * r₀ * (n : G)⁻¹ = r₀ * (r₀⁻¹ * ((n : G) * r₀ * (n : G)⁻¹)) := by group
        _ = r₀ := by rw [h2, mul_one]
    have h3 := h.mem_V₀_of_fixed n.2 hnC (mem_sup_left hr₀) h1
    have h4 : r₀ ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr₀, h3⟩
    rw [h.inf_R_V₀, mem_bot] at h4
    exact hr₀1 h4
  · intro hn
    apply Subtype.ext
    change r₀⁻¹ * ((n : G) * r₀ * (n : G)⁻¹) = 1
    rw [← mem_centralizer_iff.mp hn r₀ (mem_sup_left hr₀)]
    group

theorem exists_third {Q₁ : Subgroup G} (hQ₁ : Nat.card Q₁ = 4) :
    ∃ x : G, rightConjugate R x ≤ R ⊔ T ∧ rightConjugate R x ≠ R ∧ rightConjugate R x ≠ Q₁ := by
  have hv : ∃ v ∈ R ⊔ T, v ∉ V₀ ∧ v ∉ R ∧ v ∉ Q₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : ((R ⊔ T : Subgroup G) : Set G) ⊆ (V₀ : Set G) ∪ (R : Set G) ∪ (Q₁ : Set G) := by
      intro v hv
      by_cases h0 : v ∈ V₀
      · exact Or.inl (Or.inl h0)
      by_cases h1 : v ∈ R
      · exact Or.inl (Or.inr h1)
      exact Or.inr (hcon v hv h0 h1)
    have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hu1 := Set.ncard_union_le ((V₀ : Set G) ∪ (R : Set G)) (Q₁ : Set G)
    have hu2 := Set.ncard_union_le (V₀ : Set G) (R : Set G)
    have e1 : ((R ⊔ T : Subgroup G) : Set G).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]; exact h.loc.card
    have e2 : (V₀ : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact h.card_V₀
    have e3 : (R : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact h.cardR
    have e4 : (Q₁ : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hQ₁
    omega
  obtain ⟨v, hvV, hv0, hvR, hvQ⟩ := hv
  obtain ⟨x, hxV, hvx⟩ := h.loc.cover v hvV hv0
  exact ⟨x, hxV, fun he => hvR (he ▸ hvx), fun he => hvQ (he ▸ hvx)⟩

theorem relIndex_transv :
    (centralizer ((R ⊔ T : Subgroup G) : Set G)).relIndex (transvGroup (R ⊔ T) V₀) = 4 := by
  classical
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  obtain ⟨r₀, hr₀, hr₀1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  set f := transvHom (T := T) (V₀ := V₀) hr₀ with hf
  have hker := h.ker_transvHom hr₀ hr₀1
  have hrel : (centralizer ((R ⊔ T : Subgroup G) : Set G)).relIndex
      (transvGroup (R ⊔ T) V₀) = Nat.card f.range := by
    rw [relIndex, index, ← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hrel]
  have hdvd : Nat.card f.range ∣ 4 := by
    have := Subgroup.card_subgroup_dvd_card f.range
    rwa [h.card_V₀] at this
  obtain ⟨u, hu, huC⟩ := h.exists_transv
  have huN : u ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := hu.1
  have hQ₁V : rightConjugate R u⁻¹ ≤ R ⊔ T := Lemma36.rightConjugate_le le_sup_left (inv_mem huN)
  have hQ₁R : rightConjugate R u⁻¹ ≠ R := fun he => huC (h.mem_centralizer_of_transv_of_eq hu he)
  obtain ⟨x, hxV, hxR, hxQ⟩ := h.exists_third (Q₁ := rightConjugate R u⁻¹)
    (by rw [rightConjugate_card, h.cardR])
  have hR1 : rightConjugate R 1 = R := rightConjugate_one R
  have hR1V : rightConjugate R 1 ≤ R ⊔ T := by rw [hR1]; exact le_sup_left
  obtain ⟨n, hnV, hn1, hn2⟩ := h.loc.trans2 1 u⁻¹ 1 x hR1V hQ₁V hR1V hxV
    (by rw [hR1]; exact hQ₁R.symm) (by rw [hR1]; exact hxR.symm)
  rw [hR1] at hn1
  have hnR : n ∈ normalizer (R : Set G) := (rightConjugate_eq_self_iff R n).mp hn1
  have hnR' : rightConjugate R n⁻¹ = R := (rightConjugate_eq_self_iff R n⁻¹).mpr (inv_mem hnR)
  have hu' : n⁻¹ * u * n ∈ transvGroup (R ⊔ T) V₀ := by
    have := transvGroup_normal (inv_mem hnV) (h.normalizer_le_normalizer_V₀ (inv_mem hnV)) hu
    simpa using this
  have hQ₂ : rightConjugate R (n⁻¹ * u * n)⁻¹ = rightConjugate R x := by
    have : (n⁻¹ * u * n)⁻¹ = n⁻¹ * u⁻¹ * n := by group
    rw [this, ← rightConjugate_mul, ← rightConjugate_mul, hnR', hn2]
  have hCR : ∀ c ∈ centralizer ((R ⊔ T : Subgroup G) : Set G), rightConjugate R c = R :=
    fun c hc => (rightConjugate_eq_self_iff R c).mpr
      (centralizer_le_normalizer _ (centralizer_le (fun r hr => mem_sup_left hr) hc))
  have hu'C : n⁻¹ * u * n ∉ centralizer ((R ⊔ T : Subgroup G) : Set G) := fun hc => hxR (by
    rw [← hQ₂]
    exact hCR _ (inv_mem hc))
  have hne1 : ∀ (w : ↥(transvGroup (R ⊔ T) V₀)),
      (w : G) ∉ centralizer ((R ⊔ T : Subgroup G) : Set G) → f w ≠ 1 := fun w hw h1 =>
    hw (mem_subgroupOf.mp (hker ▸ (MonoidHom.mem_ker.mpr h1)))
  have hneq : f ⟨u, hu⟩ ≠ f ⟨n⁻¹ * u * n, hu'⟩ := by
    intro he
    have h1 : f (⟨n⁻¹ * u * n, hu'⟩⁻¹ * ⟨u, hu⟩) = 1 := by
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have h2 := mem_subgroupOf.mp (hker ▸ (MonoidHom.mem_ker.mpr h1))
    simp only [coe_mul, InvMemClass.coe_inv] at h2
    apply hxQ
    rw [← hQ₂]
    have h3 : u⁻¹ = ((n⁻¹ * u * n)⁻¹ * u)⁻¹ * (n⁻¹ * u * n)⁻¹ := by group
    rw [h3, ← rightConjugate_mul, hCR _ (inv_mem h2)]
  have h3 : 3 ≤ Nat.card f.range := by
    have : Fintype ↥f.range := Fintype.ofFinite _
    let a : ↥f.range := ⟨f ⟨u, hu⟩, ⟨_, rfl⟩⟩
    let b : ↥f.range := ⟨f ⟨n⁻¹ * u * n, hu'⟩, ⟨_, rfl⟩⟩
    have ha1 : a ≠ 1 := fun he => hne1 ⟨u, hu⟩ huC (congrArg Subtype.val he)
    have hb1 : b ≠ 1 := fun he => hne1 ⟨_, hu'⟩ hu'C (congrArg Subtype.val he)
    have hab : a ≠ b := fun he => hneq (congrArg Subtype.val he)
    have hs : ({1, a, b} : Finset ↥f.range).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
      simp [ha1.symm, hb1.symm]
    rw [Nat.card_eq_fintype_card, ← hs]
    exact Finset.card_le_univ _
  have h4 : Nat.card f.range ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hc : Nat.card f.range
  · norm_num at hdvd
  · rfl

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
