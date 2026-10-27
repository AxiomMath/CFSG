module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTrans
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Setup

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

private lemma pow_eq_one_or_self {G : Type*} [Group G] {x : G} (hx : x ^ 2 = 1) (n : ℕ) :
    x ^ n = 1 ∨ x ^ n = x := by
  rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
  · left; rw [hm, pow_mul, hx, one_pow]
  · right; rw [hm, pow_succ, pow_mul, hx, one_pow, one_mul]

private lemma sq_pow_eq {G : Type*} [Monoid G] (x : G) (n : ℕ) : (x ^ n) ^ 2 = (x ^ 2) ^ n := by
  rw [pow_two, ← pow_add, ← two_mul, pow_mul]

structure L2Iota {X : Type} [Group X] (Z : Subgroup X) (ι : X) : Prop where
  mem : ι ∈ Z
  order : orderOf ι = 2
  unique : ∀ z ∈ Z, z ^ 2 = 1 → z = 1 ∨ z = ι
  sq : ∀ z ∈ Z, z ^ 2 = 1 ∨ z ^ 2 = ι

variable {X : Type} [Group X] [Finite X] {Z A : Subgroup X} [Z.Normal]

theorem l2_iota (h : LitCtx Z A) (h4 : ∃ z ∈ Z, orderOf z = 4) : ∃ ι : X, L2Iota Z ι := by
  obtain ⟨z0, hz0Z, hz0ord⟩ := h4
  have hcardZpow : Nat.card (Subgroup.zpowers z0) = orderOf z0 := Nat.card_zpowers z0
  have hZp : Subgroup.zpowers z0 = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz0Z) ?_
    rw [h.card_Z, hcardZpow, hz0ord]
  have hmemZp : ∀ z ∈ Z, ∃ n : ℕ, z0 ^ n = z := by
    intro z hz
    have hz' : z ∈ Subgroup.zpowers z0 := by rw [hZp]; exact hz
    have hz'' : z ∈ Submonoid.powers z0 := mem_powers_iff_mem_zpowers.mpr hz'
    exact (Submonoid.mem_powers_iff z z0).mp hz''
  have h2dvd : 2 ∣ orderOf z0 := by rw [hz0ord]; norm_num
  have hord : orderOf (z0 ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (x := z0) (n := 2) (by norm_num) h2dvd, hz0ord]
  have hι2 : (z0 ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, ← hz0ord]
    exact pow_orderOf_eq_one z0
  refine ⟨z0 ^ 2, Z.pow_mem hz0Z 2, hord, ?_, ?_⟩
  · intro z hz hz2
    obtain ⟨n, hn⟩ := hmemZp z hz
    have hzn : (z0 ^ 2) ^ n = 1 := by
      rw [← sq_pow_eq z0 n, hn, hz2]
    have h2dvd_n : 2 ∣ n := by
      have := (orderOf_dvd_iff_pow_eq_one (x := z0 ^ 2)).mpr hzn
      rwa [hord] at this
    obtain ⟨m, hm⟩ := h2dvd_n
    have hz_eq : (z0 ^ 2) ^ m = z := by
      rw [← pow_mul, ← hm, hn]
    rcases pow_eq_one_or_self hι2 m with h1 | h1
    · left; rw [← hz_eq]; exact h1
    · right; rw [← hz_eq]; exact h1
  · intro z hz
    obtain ⟨n, hn⟩ := hmemZp z hz
    have hzsq : z ^ 2 = (z0 ^ 2) ^ n := by
      rw [← hn, sq_pow_eq]
    rcases pow_eq_one_or_self hι2 n with h1 | h1
    · left; rw [hzsq, h1]
    · right; rw [hzsq, h1]

theorem l2_form_comm (h : LitCtx Z A) {ι : X} (hι : L2Iota Z ι) :
    ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = ι := by
  intro a ha b hb
  have hcZ : ⁅a, b⁆ ∈ Z := h.comm_mem a ha b hb
  have h1 : ⁅a, b⁆ ^ 2 = 1 := by
    have hcomm : Commute a ⁅a, b⁆ :=
      (commute_iff_eq a ⁅a, b⁆).mpr (h.central ⁅a, b⁆ hcZ a).symm
    rw [hcomm.commutatorElement_pow_left 2]
    exact Commute.commutator_eq
      ((commute_iff_eq (a ^ 2) b).mpr (h.central (a ^ 2) (h.sq_mem a ha) b))
  exact hι.unique ⁅a, b⁆ hcZ h1

theorem l2_form_nondeg (h : LitCtx Z A) (hnab : ¬ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (φ : ↥(normalizer (A : Set X)) →* Equiv.Perm (Fin 6)) (hφs : Function.Surjective φ)
    (hφk : ∀ g : ↥(normalizer (A : Set X)), φ g = 1 ↔ ∀ a ∈ A, ⁅a, (g : X)⁆ ∈ Z) {ι : X}
    (hι : L2Iota Z ι) : ∀ a ∈ A, a ∉ Z → ∃ b ∈ A, ⁅a, b⁆ = ι := by
  intro a ha haZ
  by_contra hno
  have hno' : ∀ b ∈ A, ⁅a, b⁆ ≠ ι := by
    intro b hb h1
    exact hno ⟨b, hb, h1⟩
  have hrad : ∀ b ∈ A, a * b = b * a := by
    intro b hb
    rcases l2_form_comm h hι a ha b hb with h1 | h1
    · exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · exact absurd h1 (hno' b hb)
  apply hnab
  intro c hc b hb
  by_cases hcZ : c ∈ Z
  · exact h.central c hcZ b
  · obtain ⟨n, hn, z, hzZ, hcz⟩ := lit_transitive h φ hφs hφk ha hc haZ hcZ
    have hxA : n⁻¹ * b * n ∈ A :=
      (((Subgroup.mem_normalizer_iff'' (H := A)).mp hn) b).mp hb
    have hax : a * (n⁻¹ * b * n) = (n⁻¹ * b * n) * a := hrad _ hxA
    have hconj : (n * a * n⁻¹) * b = b * (n * a * n⁻¹) := by
      have h2 := congrArg (fun t => n * t * n⁻¹) hax
      have hxeq : n * (n⁻¹ * b * n) * n⁻¹ = b := by group
      calc
        (n * a * n⁻¹) * b = (n * a * n⁻¹) * (n * (n⁻¹ * b * n) * n⁻¹) := by rw [hxeq]
        _ = n * (a * (n⁻¹ * b * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * b * n) * a) * n⁻¹ := h2
        _ = (n * (n⁻¹ * b * n) * n⁻¹) * (n * a * n⁻¹) := by group
        _ = b * (n * a * n⁻¹) := by rw [hxeq]
    have hcz_comm : (c * z) * b = b * (c * z) := by
      rw [← hcz]
      exact hconj
    have hcb : c * b = b * c := by
      have hz_comm : z * b = b * z := h.central z hzZ b
      have e1 : (c * z) * b = (c * b) * z := by rw [mul_assoc, hz_comm, ← mul_assoc]
      have e2 : b * (c * z) = (b * c) * z := by rw [← mul_assoc]
      have e : (c * b) * z = (b * c) * z := by rw [← e1, hcz_comm, e2]
      exact (mul_right_cancel_iff).mp e
    exact hcb

theorem l2_form_sq (h : LitCtx Z A)
    (φ : ↥(normalizer (A : Set X)) →* Equiv.Perm (Fin 6)) (hφs : Function.Surjective φ)
    (hφk : ∀ g : ↥(normalizer (A : Set X)), φ g = 1 ↔ ∀ a ∈ A, ⁅a, (g : X)⁆ ∈ Z) {ι : X}
    (hι : L2Iota Z ι) : ∀ a ∈ A, a ^ 2 = 1 ∨ a ^ 2 = ι := by
  intro a ha
  by_cases haZ : a ∈ Z
  · exact hι.sq a haZ
  · by_contra hcon
    rw [not_or] at hcon
    have hι2' : ι ^ 2 = 1 := by
      have := pow_orderOf_eq_one ι
      rwa [hι.order] at this
    have hιι : ι * ι = 1 := by simpa [pow_two] using hι2'
    have stepA : ∀ c ∈ A, c ∉ Z → c ^ 2 ≠ 1 ∧ c ^ 2 ≠ ι := by
      intro c hc hcZ
      obtain ⟨n, hn, z, hzZ, hcz⟩ := lit_transitive h φ hφs hφk ha hc haZ hcZ
      have h1 : (n * a * n⁻¹) ^ 2 = a ^ 2 := by
        rw [show (n * a * n⁻¹) ^ 2 = n * a ^ 2 * n⁻¹ by simp only [pow_two]; group]
        rw [← h.central (a ^ 2) (h.sq_mem a ha) n]
        group
      have h2 : (c * z) ^ 2 = c ^ 2 * z ^ 2 := by
        rw [show (c * z) ^ 2 = c * (z * c) * z by simp only [pow_two]; group]
        rw [h.central z hzZ c]
        simp only [pow_two]
        group
      have heq : a ^ 2 = c ^ 2 * z ^ 2 := by
        rw [← h1, hcz, h2]
      constructor
      · intro hc1
        rcases hι.sq z hzZ with hz | hz
        · rw [hc1, hz, one_mul] at heq; exact hcon.1 heq
        · rw [hc1, hz, one_mul] at heq; exact hcon.2 heq
      · intro hc1
        rcases hι.sq z hzZ with hz | hz
        · rw [hc1, hz, mul_one] at heq; exact hcon.2 heq
        · rw [hc1, hz, hιι] at heq; exact hcon.1 heq
    have hc_exists : ∃ c, c ∈ A ∧ c ∉ Z ∧ a * c ∉ Z := by
      by_contra hnex
      have h' : ∀ c, c ∈ A → c ∈ Z ∨ a * c ∈ Z := by
        intro c hc
        by_contra hcZ'
        rw [not_or] at hcZ'
        exact hnex ⟨c, hc, hcZ'.1, hcZ'.2⟩
      have hsub : (A : Set X) ⊆ (Z : Set X) ∪ (fun z => a⁻¹ * z) '' (Z : Set X) := by
        intro c hc
        rcases h' c hc with hcZ | hacZ
        · exact Or.inl hcZ
        · exact Or.inr ⟨a * c, hacZ, by group⟩
      have hZcard : (Z : Set X).ncard = 4 :=
        (Nat.card_coe_set_eq (Z : Set X)).symm.trans h.card_Z
      have hAcard : (A : Set X).ncard = 64 :=
        (Nat.card_coe_set_eq (A : Set X)).symm.trans h.card_A
      have hle8 : (A : Set X).ncard ≤ 8 := by
        calc
          (A : Set X).ncard ≤ ((Z : Set X) ∪ (fun z => a⁻¹ * z) '' (Z : Set X)).ncard :=
            Set.ncard_le_ncard hsub
          _ ≤ (Z : Set X).ncard + ((fun z => a⁻¹ * z) '' (Z : Set X)).ncard :=
            Set.ncard_union_le _ _
          _ ≤ (Z : Set X).ncard + (Z : Set X).ncard :=
            Nat.add_le_add_left Set.ncard_image_le _
          _ = 8 := by rw [hZcard]
      omega
    obtain ⟨c, hcA, hcZ, hacZ⟩ := hc_exists
    have hbad_c := stepA c hcA hcZ
    have hbad_ac := stepA (a * c) (A.mul_mem ha hcA) hacZ
    have hia : (a ^ 2) ^ 2 = ι := by
      rcases hι.sq (a ^ 2) (h.sq_mem a ha) with hh | hh
      · rcases hι.unique (a ^ 2) (h.sq_mem a ha) hh with h1 | h1
        · exact absurd h1 hcon.1
        · exact absurd h1 hcon.2
      · exact hh
    have hic : (c ^ 2) ^ 2 = ι := by
      rcases hι.sq (c ^ 2) (h.sq_mem c hcA) with hh | hh
      · rcases hι.unique (c ^ 2) (h.sq_mem c hcA) hh with h1 | h1
        · exact absurd h1 hbad_c.1
        · exact absurd h1 hbad_c.2
      · exact hh
    have hpZ : a ^ 2 * c ^ 2 ∈ Z := Z.mul_mem (h.sq_mem a ha) (h.sq_mem c hcA)
    have hcomm_ac : Commute (a ^ 2) (c ^ 2) :=
      (commute_iff_eq (a ^ 2) (c ^ 2)).mpr (h.central (c ^ 2) (h.sq_mem c hcA) (a ^ 2)).symm
    have hp2 : (a ^ 2 * c ^ 2) ^ 2 = 1 := by
      rw [hcomm_ac.mul_pow 2, hia, hic, hιι]
    have hp : a ^ 2 * c ^ 2 = 1 ∨ a ^ 2 * c ^ 2 = ι := hι.unique (a ^ 2 * c ^ 2) hpZ hp2
    let w := ⁅c, a⁆
    have hwZ : w ∈ Z := h.comm_mem c hcA a ha
    have hwcomm : w = 1 ∨ w = ι := l2_form_comm h hι c hcA a ha
    have hca : c * a = w * a * c := by
      dsimp only [w]
      rw [commutatorElement_def]
      group
    have hwa : a * w = w * a := (h.central w hwZ a).symm
    have hac_sq : (a * c) ^ 2 = w * (a ^ 2 * c ^ 2) := by
      calc
        (a * c) ^ 2 = a * (c * a) * c := by simp only [pow_two]; group
        _ = a * (w * a * c) * c := by rw [hca]
        _ = (a * w) * a * c * c := by group
        _ = (w * a) * a * c * c := by rw [hwa]
        _ = w * (a ^ 2 * c ^ 2) := by simp only [pow_two]; group
    have hac_sq_mem : (a * c) ^ 2 = 1 ∨ (a * c) ^ 2 = ι := by
      rw [hac_sq]
      rcases hwcomm with hw | hw <;> rcases hp with hp | hp
      · left; rw [hw, hp, one_mul]
      · right; rw [hw, hp, one_mul]
      · right; rw [hw, hp, mul_one]
      · left; rw [hw, hp, hιι]
    rcases hac_sq_mem with hh | hh
    · exact hbad_ac.1 hh
    · exact hbad_ac.2 hh

theorem l2_form (h : LitCtx Z A) (hnab : ¬ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (φ : ↥(normalizer (A : Set X)) →* Equiv.Perm (Fin 6)) (hφs : Function.Surjective φ)
    (hφk : ∀ g : ↥(normalizer (A : Set X)), φ g = 1 ↔ ∀ a ∈ A, ⁅a, (g : X)⁆ ∈ Z)
    (h4 : ∃ z ∈ Z, orderOf z = 4) : L2Form Z A := by
  obtain ⟨ι, hι⟩ := l2_iota h h4
  exact ⟨ι, hι.mem, hι.order, l2_form_sq h φ hφs hφk hι, l2_form_comm h hι,
    l2_form_nondeg h hnab φ hφs hφk hι⟩

end CFSG.OddStandard.HigherRank.YamadaG23
