module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Mod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec1011Core {A : Type} [Group A] (B : Subgroup A) (t : A) (K : Subgroup (MulAut A))
    (φ : (Fin 5 → ZMod 2) → A) : Prop where
  comm : ∀ a b : A, a * b = b * a
  t_sq : t * t = 1
  t_not_mem : t ∉ B
  split : ∀ a : A, a ∈ B ∨ t * a ∈ B
  hom : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w
  inj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w
  mem_B : ∀ x : A, x ∈ B ↔ ∃ v, IsEvenVec v ∧ φ v = x
  B_inv : ∀ α ∈ K, ∀ b ∈ B, α b ∈ B
  coset_inv : ∀ α ∈ K, t⁻¹ * α t ∈ B
  N_act : ∀ σ ∈ alternatingGroup (Fin 5), ∃ α ∈ K, α t = t ∧
    ∀ v, IsEvenVec v → α (φ v) = φ (permVec σ v)
  tz_mem : ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ ∃ α ∈ K, α t = t * φ v

@[expose] def sec1011_orb {A : Type} [Group A] (K : Subgroup (MulAut A)) (t : A) : Set A :=
  {a | ∃ α ∈ K, a = α t}

variable {A : Type} [Group A] {B : Subgroup A} {t : A} {K : Subgroup (MulAut A)}
  {φ : (Fin 5 → ZMod 2) → A}

private instance instDecidableIsEvenVec5 (v : Fin 5 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private lemma sec1011_wfour_ne_zero (i : Fin 5) : sec1011_wfour i ≠ 0 := by
  intro h
  have hw := sec1011_wfour_weight i
  rw [h] at hw
  simpa [vecWeight] using hw

private lemma sec1011_orb_smul {K : Subgroup (MulAut A)} {t : A} {α : MulAut A}
    (hα : α ∈ K) {a : A} (ha : a ∈ sec1011_orb K t) : α a ∈ sec1011_orb K t := by
  obtain ⟨γ, hγ, rfl⟩ := ha
  exact ⟨α * γ, K.mul_mem hα hγ, by simp⟩

theorem Sec1011Core.map_zero (h : Sec1011Core B t K φ) : φ 0 = 1 := by
  have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have hmul : φ 0 * φ 0 = φ 0 := by
    rw [← h.hom 0 0 h0 h0]
    simp
  exact mul_eq_right.mp hmul

theorem Sec1011Core.mem (h : Sec1011Core B t K φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    φ v ∈ B :=
  (h.mem_B (φ v)).2 ⟨v, hv, rfl⟩

theorem Sec1011Core.sq (h : Sec1011Core B t K φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    φ v * φ v = 1 := by
  rw [← h.hom v v hv hv, sec1011_vec_add_self v, h.map_zero]

theorem Sec1011Core.ne_one (h : Sec1011Core B t K φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v)
    (hv0 : v ≠ 0) : φ v ≠ 1 := by
  intro h1
  exact hv0 (h.inj v 0 hv (by simp [IsEvenVec]) (by rw [h1, h.map_zero]))

theorem Sec1011Core.card_B (h : Sec1011Core B t K φ) : Nat.card B = 16 := by
  let f : {v : Fin 5 → ZMod 2 // IsEvenVec v} → B :=
    fun v => ⟨φ v.1, (h.mem_B (φ v.1)).2 ⟨v.1, v.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      exact Subtype.ext (h.inj u.1 v.1 u.2 v.2 (congrArg Subtype.val huv))
    · rintro ⟨x, hx⟩
      obtain ⟨v, hv, hφv⟩ := (h.mem_B x).1 hx
      exact ⟨⟨v, hv⟩, Subtype.ext hφv⟩
  have hc : Nat.card {v : Fin 5 → ZMod 2 // IsEvenVec v} = Nat.card B :=
    Nat.card_congr (Equiv.ofBijective f hf)
  rw [← hc, Nat.card_eq_fintype_card]
  decide +kernel

theorem Sec1011Core.orb_sub (h : Sec1011Core B t K φ) :
    sec1011_orb K t ⊆ {a | ∃ b ∈ B, a = t * b} := by
  rintro a ⟨α, hα, rfl⟩
  exact ⟨t⁻¹ * α t, h.coset_inv α hα, by group⟩

theorem Sec1011Core.orb_weight_four (h : Sec1011Core B t K φ) {v : Fin 5 → ZMod 2}
    (hv : IsEvenVec v) (hw : vecWeight v = 4) : t * φ v ∈ sec1011_orb K t := by
  obtain ⟨v0, hv0, hv0w, β, hβK, hβt⟩ := h.tz_mem
  obtain ⟨σ, hσ, hσv⟩ := exists_alt_permVec_weight_four v0 v hv0w hw
  obtain ⟨α, hαK, hαt, hα⟩ := h.N_act σ hσ
  refine ⟨α * β, K.mul_mem hαK hβK, ?_⟩
  rw [MulAut.mul_apply, hβt, map_mul, hαt, hα v0 hv0, hσv]

theorem sec1011_core_dichotomy (h : Sec1011Core B t K φ) :
    sec1011_orb K t =
        {a | a = t ∨ ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ a = t * φ v} ∨
      sec1011_orb K t = {a | ∃ b ∈ B, a = t * b} := by
  let D : Set (Fin 5 → ZMod 2) := {v | IsEvenVec v ∧ t * φ v ∈ sec1011_orb K t}
  have hD0 : (0 : Fin 5 → ZMod 2) ∈ D := by
    refine ⟨by simp [IsEvenVec], ?_⟩
    rw [h.map_zero, mul_one]
    exact ⟨1, K.one_mem, by simp⟩
  have hD4 : ∀ v, IsEvenVec v → vecWeight v = 4 → v ∈ D :=
    fun v hv hw => ⟨hv, h.orb_weight_four hv hw⟩
  have hDstable : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v ∈ D, permVec σ v ∈ D := by
    intro σ hσ v hvD
    obtain ⟨hv, htv⟩ := hvD
    obtain ⟨n, hnK, hnt, hn⟩ := h.N_act σ hσ
    refine ⟨isEvenVec_permVec σ hv, ?_⟩
    have heq : n (t * φ v) = t * φ (permVec σ v) := by
      rw [map_mul, hnt, hn v hv]
    rw [← heq]
    exact sec1011_orb_smul hnK htv
  by_cases hcase : ∃ w, w ∈ D ∧ vecWeight w = 2
  · right
    have hD2 : ∀ u, vecWeight u = 2 → u ∈ D := by
      intro u hu
      obtain ⟨w, hwD, hw2⟩ := hcase
      obtain ⟨σ, hσ, hσw⟩ := sec1011_alt_weight_two w u hw2 hu
      rw [← hσw]
      exact hDstable σ hσ w hwD
    have hDall : ∀ v, IsEvenVec v → v ∈ D := by
      intro v hv
      rcases even_weight_cases_five v hv with h0 | h2 | h4
      · rw [h0]; exact hD0
      · exact hD2 v h2
      · exact hD4 v hv h4
    ext a
    constructor
    · intro ha
      exact h.orb_sub ha
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨v, hv, rfl⟩ := (h.mem_B b).1 hb
      exact (hDall v hv).2
  · left
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb, rfl⟩ := h.orb_sub ha
      obtain ⟨v, hv, rfl⟩ := (h.mem_B b).1 hb
      have hvD : v ∈ D := ⟨hv, ha⟩
      rcases even_weight_cases_five v hv with h0 | h2 | h4
      · left; rw [h0, h.map_zero, mul_one]
      · exact absurd ⟨v, hvD, h2⟩ hcase
      · right; exact ⟨v, hv, h4, rfl⟩
    · rintro (rfl | ⟨v, hv, h4, rfl⟩)
      · exact ⟨1, K.one_mem, by simp⟩
      · exact h.orb_weight_four hv h4

theorem sec1011_core_ncard_six (h : Sec1011Core B t K φ)
    (h6 : sec1011_orb K t =
      {a | a = t ∨ ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ a = t * φ v}) :
    (sec1011_orb K t).ncard = 6 := by
  let f : Fin 6 → A := Fin.cons t (fun i : Fin 5 => t * φ (sec1011_wfour i))
  have hrange : {a : A | a = t ∨ ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ a = t * φ v}
      = Set.range f := by
    ext a
    constructor
    · rintro (rfl | ⟨v, hv, hw, rfl⟩)
      · exact ⟨0, by simp [f]⟩
      · obtain ⟨i, rfl⟩ := sec1011_exists_wfour v hw
        exact ⟨i.succ, by simp [f]⟩
    · rintro ⟨k, rfl⟩
      cases k using Fin.cases with
      | zero => left; simp [f]
      | succ i =>
          right
          exact ⟨sec1011_wfour i, sec1011_wfour_even i, sec1011_wfour_weight i, by simp [f]⟩
  have hfinj : Function.Injective f := by
    intro k l hkl
    cases k using Fin.cases with
    | zero =>
        cases l using Fin.cases with
        | zero => rfl
        | succ j =>
            exfalso
            have h1 : t = t * φ (sec1011_wfour j) := by simpa [f] using hkl
            exact (h.ne_one (sec1011_wfour_even j) (sec1011_wfour_ne_zero j))
              (mul_eq_left.mp h1.symm)
    | succ i =>
        cases l using Fin.cases with
        | zero =>
            exfalso
            have h1 : t * φ (sec1011_wfour i) = t := by simpa [f] using hkl
            exact (h.ne_one (sec1011_wfour_even i) (sec1011_wfour_ne_zero i))
              (mul_eq_left.mp h1)
        | succ j =>
            have h1 : t * φ (sec1011_wfour i) = t * φ (sec1011_wfour j) := by
              simpa [f] using hkl
            have h2 : φ (sec1011_wfour i) = φ (sec1011_wfour j) := mul_left_cancel h1
            have h3 : sec1011_wfour i = sec1011_wfour j :=
              h.inj _ _ (sec1011_wfour_even i) (sec1011_wfour_even j) h2
            exact congrArg Fin.succ (sec1011_wfour_injective h3)
  rw [h6, hrange, Set.ncard_range_of_injective hfinj, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end CFSG.OddStandard.SmallF3.Omega
