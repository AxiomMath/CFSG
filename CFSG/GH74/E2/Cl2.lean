module

public import CFSG.GH74.E2.Cl2Main

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

namespace Wrap

theorem exists_gens {B : Type*} [Group B] [Finite B] (hcomm : ∀ a b : B, a * b = b * a)
    (hpow : ∀ a : B, a ^ 3 = 1) (hcard : Nat.card B = 9) :
    ∃ a₀ b₀ : B, a₀ ≠ 1 ∧ b₀ ≠ 1 ∧ a₀ ≠ b₀ ∧ a₀ ≠ b₀⁻¹ ∧
      ∀ g : B, ∃ i j : ℕ, g = a₀ ^ i * b₀ ^ j := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnt : Nontrivial B := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : B)
  have ha₀o : orderOf a₀ = 3 := orderOf_eq_prime (hpow a₀) ha₀
  have hH : Nat.card (zpowers a₀) = 3 := by rw [Nat.card_zpowers, ha₀o]
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : B, b₀ ∉ zpowers a₀ := by
    by_contra h
    have htop : zpowers a₀ = ⊤ := eq_top_iff.2 fun x _ => by
      by_contra hx
      exact h ⟨x, hx⟩
    have := hH
    rw [htop, Subgroup.card_top, hcard] at this
    omega
  have hb₀1 : b₀ ≠ 1 := fun h => hb₀ (h ▸ one_mem _)
  have hb₀o : orderOf b₀ = 3 := orderOf_eq_prime (hpow b₀) hb₀1
  have hK : Nat.card (zpowers b₀) = 3 := by rw [Nat.card_zpowers, hb₀o]
  have hsup : zpowers a₀ ⊔ zpowers b₀ = ⊤ := by
    set S : Subgroup B := zpowers a₀ ⊔ zpowers b₀ with hSdef
    have hdvd : Nat.card S ∣ 9 := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    have hdvd3 : 3 ∣ Nat.card S := by
      rw [← hH]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h9 : Nat.card S = 9 := by
      by_contra hne
      obtain ⟨k, hk⟩ := hdvd3
      have hk3 : k ∣ 3 := by
        obtain ⟨l, hl⟩ := hdvd
        refine ⟨l, ?_⟩
        nlinarith
      have hk' : k = 1 ∨ k = 3 := (Nat.dvd_prime Nat.prime_three).1 hk3
      rcases hk' with rfl | rfl
      · have h3 : Nat.card S = 3 := by omega
        have heq : zpowers a₀ = S :=
          Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hH, h3])
        exact hb₀ (heq ▸ (le_sup_right : zpowers b₀ ≤ S) (Subgroup.mem_zpowers b₀))
      · exact hne (by omega)
    exact Subgroup.eq_top_of_card_eq _ (by rw [h9, hcard])
  let _ : CommGroup B := { ‹Group B› with mul_comm := hcomm }
  refine ⟨a₀, b₀, ha₀, hb₀1, ?_, ?_, ?_⟩
  · intro h
    exact hb₀ (h ▸ Subgroup.mem_zpowers a₀)
  · intro h
    apply hb₀
    have : b₀ = a₀⁻¹ := by rw [h, inv_inv]
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a₀)
  · intro g
    have hg : g ∈ zpowers a₀ ⊔ zpowers b₀ := hsup ▸ Subgroup.mem_top g
    obtain ⟨h, hh, k, hk, rfl⟩ := Subgroup.mem_sup.1 hg
    obtain ⟨i, rfl⟩ := (mem_powers_iff_mem_zpowers).2 hh
    obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers).2 hk
    exact ⟨i, j, rfl⟩

theorem fourGen_of_rank {X : Type*} [Group X] [Finite X]
    (hP : ∀ P : Subgroup X, Group.rank ↥P ≤ 4) : FourGen X := by
  classical
  intro H
  obtain ⟨S, hS, hcl⟩ := Group.rank_spec ↥H
  refine ⟨S.image Subtype.val, ?_, ?_⟩
  · exact Finset.card_image_le.trans (hS ▸ hP H)
  · have h1 : (Subgroup.closure (S : Set H)).map H.subtype =
        Subgroup.closure (H.subtype '' (S : Set H)) := MonoidHom.map_closure _ _
    rw [hcl, Subgroup.map_top, Subgroup.range_subtype] at h1
    rw [Finset.coe_image]
    exact h1.symm

section Action

variable {X B : Type*} [Group X] [Finite X] [Group B]

omit [Finite X] in
theorem pow3_of {φ : B →* MulAut X} (hpow : ∀ a : B, a ^ 3 = 1) (g : B) : (φ g) ^ 3 = 1 := by
  rw [← map_pow, hpow g, map_one]

@[expose] noncomputable def actV (φ : B →* MulAut X) (hpow : ∀ a : B, a ^ 3 = 1) :
    B →* MulAut (X ⧸ frattini X) where
  toFun g := aV (φ g) (pow3_of hpow g)
  map_one' := by
    refine MulEquiv.ext fun z => ?_
    induction z using QuotientGroup.induction_on with
    | H x => simp [aV, quotAut_mk]
  map_mul' g h := by
    refine MulEquiv.ext fun z => ?_
    induction z using QuotientGroup.induction_on with
    | H x => simp [aV, quotAut_mk, MulAut.mul_apply]

omit [Finite X] in
theorem actV_mk (φ : B →* MulAut X) (hpow : ∀ a : B, a ^ 3 = 1) (g : B) (x : X) :
    actV φ hpow g (x : X ⧸ frattini X) = ((φ g x : X) : X ⧸ frattini X) := by
  simp [actV, aV, quotAut_mk]

theorem V_sq (hX : IsPGroup 2 X) (v : X ⧸ frattini X) : v * v = 1 := by
  induction v using QuotientGroup.induction_on with
  | H g =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact mul_self_mem_frattini hX g

theorem V_comm (hX : IsPGroup 2 X) (v w : X ⧸ frattini X) : v * w = w * v := by
  have hi : ∀ z : X ⧸ frattini X, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (V_sq hX z)
  calc v * w = (v * w)⁻¹ := (hi (v * w)).symm
    _ = w⁻¹ * v⁻¹ := mul_inv_rev v w
    _ = w * v := by rw [hi v, hi w]

theorem card_V_le (hX : IsPGroup 2 X) (h4 : FourGen X) : Nat.card (X ⧸ frattini X) ≤ 16 := by
  have h := FourGen.relIndex_le h4 (H := ⊤) (R := frattini X)
    (fun h _ r hr => (inferInstance : (frattini X).Normal).conj_mem r hr h)
    (fun h _ => mul_self_mem_frattini hX h)
  rwa [Subgroup.relIndex_top_right] at h

theorem eq_one_of_actV_eq_one {φ : B →* MulAut X} (hX : IsPGroup 2 X)
    (hpow : ∀ a : B, a ^ 3 = 1) (g : B) (hg : actV φ hpow g = 1) : φ g = 1 := by
  have h3 := pow3_of (φ := φ) hpow g
  have hN := frattini_inv_iff h3
  have hsup : fixSub (φ g) ⊔ frattini X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x⁻¹ * (φ g) x ∈ frattini X := by
      have := congrArg (fun f : MulAut (X ⧸ frattini X) => f (x : X ⧸ frattini X)) hg
      simp only [actV_mk, MulAut.one_apply] at this
      exact QuotientGroup.eq.1 this.symm
    obtain ⟨n, hn, hfix⟩ := exists_fixed_mul_mem hX h3 hN hx
    have hxn : x * n ∈ fixSub (φ g) := hfix
    have hxe : x = (x * n) * n⁻¹ := by group
    rw [hxe]
    exact Subgroup.mul_mem_sup hxn (Subgroup.inv_mem _ hn)
  have htop := frattini_nongenerating hsup
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ fixSub (φ g) := by rw [htop]; trivial
  exact hx

end Action

section Weights

theorem six_patterns (A B C D : Prop) (h3 : ¬ (A ∧ B ∧ C) ∧ ¬ (A ∧ B ∧ D) ∧ ¬ (A ∧ C ∧ D) ∧
    ¬ (B ∧ C ∧ D)) (h2 : (A ∧ B) ∨ (A ∧ C) ∨ (A ∧ D) ∨ (B ∧ C) ∨ (B ∧ D) ∨ (C ∧ D)) :
    (A ∧ B ∧ ¬ C ∧ ¬ D) ∨ (A ∧ C ∧ ¬ B ∧ ¬ D) ∨ (A ∧ D ∧ ¬ B ∧ ¬ C) ∨
      (B ∧ C ∧ ¬ A ∧ ¬ D) ∨ (B ∧ D ∧ ¬ A ∧ ¬ C) ∨ (C ∧ D ∧ ¬ A ∧ ¬ B) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D <;> simp_all

theorem prod64 (a b c d : ℕ) (ha : 4 ≤ a) (hb : 4 ≤ b) (hc : 4 ≤ c) (hd : 1 ≤ d) :
    64 ≤ a * b * c * d :=
  calc 64 = 4 * 4 * 4 * 1 := by norm_num
    _ ≤ a * b * c * d := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc) hd

theorem exists_pair_aux {P : Type*} [Group P] (W : Wt → Subgroup P) (hW0 : W .w0 = ⊥)
    (hproper : ∀ w, w ≠ Wt.w0 → W w ≠ ⊤)
    (hdec : ∀ x : P, ∃ xa ∈ W .wa, ∃ xb ∈ W .wb, ∃ xp ∈ W .wp, ∃ xm ∈ W .wm,
      x = xa * xb * xp * xm)
    (hcard : Nat.card (W .wa) * Nat.card (W .wb) * Nat.card (W .wp) * Nat.card (W .wm) ≤ 16)
    (h4 : ∀ w, w ≠ Wt.w0 → W w ≠ ⊥ → 4 ≤ Nat.card (W w)) (hpos : ∀ w, 1 ≤ Nat.card (W w)) :
    ∃ w₁ w₂ : Wt, w₁ ≠ w₂ ∧ w₁ ≠ .w0 ∧ w₂ ≠ .w0 ∧ W w₁ ≠ ⊥ ∧ W w₂ ≠ ⊥ ∧
      ∀ w, w ≠ w₁ → w ≠ w₂ → W w = ⊥ := by
  have top_of : ∀ w, w ≠ Wt.w0 → (∀ w', w' ≠ Wt.w0 → w' ≠ w → W w' = ⊥) → W w = ⊤ := by
    intro w hw hother
    rw [eq_top_iff]
    intro x _
    obtain ⟨xa, hxa, xb, hxb, xp, hxp, xm, hxm, rfl⟩ := hdec x
    have hb : ∀ w', w' ≠ Wt.w0 → w' ≠ w → ∀ y ∈ W w', y = 1 := fun w' h1 h2 y hy => by
      have := hother w' h1 h2
      rw [this] at hy
      exact Subgroup.mem_bot.1 hy
    cases w with
    | w0 => exact absurd rfl hw
    | wa =>
      have e2 := hb .wb (by decide) (by decide) xb hxb
      have e3 := hb .wp (by decide) (by decide) xp hxp
      have e4 := hb .wm (by decide) (by decide) xm hxm
      simp only [e2, e3, e4, mul_one]
      exact hxa
    | wb =>
      have e1 := hb .wa (by decide) (by decide) xa hxa
      have e3 := hb .wp (by decide) (by decide) xp hxp
      have e4 := hb .wm (by decide) (by decide) xm hxm
      simp only [e1, e3, e4, mul_one, one_mul]
      exact hxb
    | wp =>
      have e1 := hb .wa (by decide) (by decide) xa hxa
      have e2 := hb .wb (by decide) (by decide) xb hxb
      have e4 := hb .wm (by decide) (by decide) xm hxm
      simp only [e1, e2, e4, mul_one, one_mul]
      exact hxp
    | wm =>
      have e1 := hb .wa (by decide) (by decide) xa hxa
      have e2 := hb .wb (by decide) (by decide) xb hxb
      have e3 := hb .wp (by decide) (by decide) xp hxp
      simp only [e1, e2, e3, mul_one, one_mul]
      exact hxm
  have h3 : ¬ (W .wa ≠ ⊥ ∧ W .wb ≠ ⊥ ∧ W .wp ≠ ⊥) ∧ ¬ (W .wa ≠ ⊥ ∧ W .wb ≠ ⊥ ∧ W .wm ≠ ⊥) ∧
      ¬ (W .wa ≠ ⊥ ∧ W .wp ≠ ⊥ ∧ W .wm ≠ ⊥) ∧ ¬ (W .wb ≠ ⊥ ∧ W .wp ≠ ⊥ ∧ W .wm ≠ ⊥) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨ha, hb, hp⟩
      have := prod64 _ _ _ _ (h4 _ (by decide) ha) (h4 _ (by decide) hb) (h4 _ (by decide) hp)
        (hpos .wm)
      omega
    · rintro ⟨ha, hb, hm⟩
      have := prod64 _ _ _ _ (h4 _ (by decide) ha) (h4 _ (by decide) hb) (h4 _ (by decide) hm)
        (hpos .wp)
      have e : Nat.card (W .wa) * Nat.card (W .wb) * Nat.card (W .wm) * Nat.card (W .wp) =
          Nat.card (W .wa) * Nat.card (W .wb) * Nat.card (W .wp) * Nat.card (W .wm) := by ring
      omega
    · rintro ⟨ha, hp, hm⟩
      have := prod64 _ _ _ _ (h4 _ (by decide) ha) (h4 _ (by decide) hp) (h4 _ (by decide) hm)
        (hpos .wb)
      have e : Nat.card (W .wa) * Nat.card (W .wp) * Nat.card (W .wm) * Nat.card (W .wb) =
          Nat.card (W .wa) * Nat.card (W .wb) * Nat.card (W .wp) * Nat.card (W .wm) := by ring
      omega
    · rintro ⟨hb, hp, hm⟩
      have := prod64 _ _ _ _ (h4 _ (by decide) hb) (h4 _ (by decide) hp) (h4 _ (by decide) hm)
        (hpos .wa)
      have e : Nat.card (W .wb) * Nat.card (W .wp) * Nat.card (W .wm) * Nat.card (W .wa) =
          Nat.card (W .wa) * Nat.card (W .wb) * Nat.card (W .wp) * Nat.card (W .wm) := by ring
      omega
  have h2 : (W .wa ≠ ⊥ ∧ W .wb ≠ ⊥) ∨ (W .wa ≠ ⊥ ∧ W .wp ≠ ⊥) ∨ (W .wa ≠ ⊥ ∧ W .wm ≠ ⊥) ∨
      (W .wb ≠ ⊥ ∧ W .wp ≠ ⊥) ∨ (W .wb ≠ ⊥ ∧ W .wm ≠ ⊥) ∨ (W .wp ≠ ⊥ ∧ W .wm ≠ ⊥) := by
    by_contra hcon
    have c1 : ¬ (W .wa ≠ ⊥ ∧ W .wb ≠ ⊥) := fun h => hcon (Or.inl h)
    have c2 : ¬ (W .wa ≠ ⊥ ∧ W .wp ≠ ⊥) := fun h => hcon (Or.inr (Or.inl h))
    have c3 : ¬ (W .wa ≠ ⊥ ∧ W .wm ≠ ⊥) := fun h => hcon (Or.inr (Or.inr (Or.inl h)))
    have c4 : ¬ (W .wb ≠ ⊥ ∧ W .wp ≠ ⊥) := fun h => hcon (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have c5 : ¬ (W .wb ≠ ⊥ ∧ W .wm ≠ ⊥) := fun h =>
      hcon (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    have c6 : ¬ (W .wp ≠ ⊥ ∧ W .wm ≠ ⊥) := fun h =>
      hcon (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    by_cases ha : W .wa = ⊥
    · by_cases hb : W .wb = ⊥
      · by_cases hp : W .wp = ⊥
        · by_cases hm : W .wm = ⊥
          · refine hproper .wa (by decide) (top_of .wa (by decide) ?_)
            intro w' h1 h2
            cases w' with
            | w0 => exact absurd rfl h1
            | wa => exact absurd rfl h2
            | wb => exact hb
            | wp => exact hp
            | wm => exact hm
          · refine hproper .wm (by decide) (top_of .wm (by decide) ?_)
            intro w' h1 h2
            cases w' with
            | w0 => exact absurd rfl h1
            | wa => exact ha
            | wb => exact hb
            | wp => exact hp
            | wm => exact absurd rfl h2
        · have hm : W .wm = ⊥ := by
            by_contra hm
            exact c6 ⟨hp, hm⟩
          refine hproper .wp (by decide) (top_of .wp (by decide) ?_)
          intro w' h1 h2
          cases w' with
          | w0 => exact absurd rfl h1
          | wa => exact ha
          | wb => exact hb
          | wp => exact absurd rfl h2
          | wm => exact hm
      · have hp : W .wp = ⊥ := by
          by_contra hp
          exact c4 ⟨hb, hp⟩
        have hm : W .wm = ⊥ := by
          by_contra hm
          exact c5 ⟨hb, hm⟩
        refine hproper .wb (by decide) (top_of .wb (by decide) ?_)
        intro w' h1 h2
        cases w' with
        | w0 => exact absurd rfl h1
        | wa => exact ha
        | wb => exact absurd rfl h2
        | wp => exact hp
        | wm => exact hm
    · have hb : W .wb = ⊥ := by
        by_contra hb
        exact c1 ⟨ha, hb⟩
      have hp : W .wp = ⊥ := by
        by_contra hp
        exact c2 ⟨ha, hp⟩
      have hm : W .wm = ⊥ := by
        by_contra hm
        exact c3 ⟨ha, hm⟩
      refine hproper .wa (by decide) (top_of .wa (by decide) ?_)
      intro w' h1 h2
      cases w' with
      | w0 => exact absurd rfl h1
      | wa => exact absurd rfl h2
      | wb => exact hb
      | wp => exact hp
      | wm => exact hm
  rcases six_patterns _ _ _ _ h3 h2 with
    ⟨ha, hb, hp, hm⟩ | ⟨ha, hp, hb, hm⟩ | ⟨ha, hm, hb, hp⟩ | ⟨hb, hp, ha, hm⟩ |
      ⟨hb, hm, ha, hp⟩ | ⟨hp, hm, ha, hb⟩
  · refine ⟨.wa, .wb, by decide, by decide, by decide, ha, hb, ?_⟩
    intro w h1 h2
    cases w with
    | w0 => exact hW0
    | wa => exact absurd rfl h1
    | wb => exact absurd rfl h2
    | wp => exact not_not.1 hp
    | wm => exact not_not.1 hm
  · refine ⟨.wa, .wp, by decide, by decide, by decide, ha, hp, ?_⟩
    intro w h1 h2
    cases w with
    | w0 => exact hW0
    | wa => exact absurd rfl h1
    | wb => exact not_not.1 hb
    | wp => exact absurd rfl h2
    | wm => exact not_not.1 hm
  · refine ⟨.wa, .wm, by decide, by decide, by decide, ha, hm, ?_⟩
    intro w h1 h2
    cases w with
    | w0 => exact hW0
    | wa => exact absurd rfl h1
    | wb => exact not_not.1 hb
    | wp => exact not_not.1 hp
    | wm => exact absurd rfl h2
  · refine ⟨.wb, .wp, by decide, by decide, by decide, hb, hp, ?_⟩
    intro w h1 h2
    cases w with
    | w0 => exact hW0
    | wa => exact not_not.1 ha
    | wb => exact absurd rfl h1
    | wp => exact absurd rfl h2
    | wm => exact not_not.1 hm
  · refine ⟨.wb, .wm, by decide, by decide, by decide, hb, hm, ?_⟩
    intro w h1 h2
    cases w with
    | w0 => exact hW0
    | wa => exact not_not.1 ha
    | wb => exact absurd rfl h1
    | wp => exact not_not.1 hp
    | wm => exact absurd rfl h2
  · refine ⟨.wp, .wm, by decide, by decide, by decide, hp, hm, ?_⟩
    intro w h1 h2
    cases w with
    | w0 => exact hW0
    | wa => exact not_not.1 ha
    | wb => exact not_not.1 hb
    | wp => exact absurd rfl h1
    | wm => exact absurd rfl h2

theorem indep_pair {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) {α β : MulAut P}
    (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) (hab : α * β = β * α) (hA : AbInv2 α β (⊤ : Subgroup P))
    {w w' : Wt} (hne : w ≠ w') {x : P} (hx : x ∈ wsub α β ⊤ hA w)
    (hx' : x ∈ wsub α β ⊤ hA w') : x = 1 := by
  have i01 : ∀ x, x ∈ wsub α β ⊤ hA .w0 → x ∈ wsub α β ⊤ hA .wa → x = 1 := by
    intro x hx hx'
    have h := wsub_indep hP hα hβ hab hA (x0 := x) (xa := x⁻¹) (xb := 1) (xp := 1) (xm := 1) hx (Subgroup.inv_mem _ hx') (Subgroup.one_mem _) (Subgroup.one_mem _) (Subgroup.one_mem _) (by simp)
    exact h.1
  have i02 : ∀ x, x ∈ wsub α β ⊤ hA .w0 → x ∈ wsub α β ⊤ hA .wb → x = 1 := by
    intro x hx hx'
    have h := wsub_indep hP hα hβ hab hA (x0 := x) (xa := 1) (xb := x⁻¹) (xp := 1) (xm := 1) hx (Subgroup.one_mem _) (Subgroup.inv_mem _ hx') (Subgroup.one_mem _) (Subgroup.one_mem _) (by simp)
    exact h.1
  have i03 : ∀ x, x ∈ wsub α β ⊤ hA .w0 → x ∈ wsub α β ⊤ hA .wp → x = 1 := by
    intro x hx hx'
    have h := wsub_indep hP hα hβ hab hA (x0 := x) (xa := 1) (xb := 1) (xp := x⁻¹) (xm := 1) hx (Subgroup.one_mem _) (Subgroup.one_mem _) (Subgroup.inv_mem _ hx') (Subgroup.one_mem _) (by simp)
    exact h.1
  have i04 : ∀ x, x ∈ wsub α β ⊤ hA .w0 → x ∈ wsub α β ⊤ hA .wm → x = 1 := by
    intro x hx hx'
    have h := wsub_indep hP hα hβ hab hA (x0 := x) (xa := 1) (xb := 1) (xp := 1) (xm := x⁻¹) hx (Subgroup.one_mem _) (Subgroup.one_mem _) (Subgroup.one_mem _) (Subgroup.inv_mem _ hx') (by simp)
    exact h.1
  have i12 : ∀ x, x ∈ wsub α β ⊤ hA .wa → x ∈ wsub α β ⊤ hA .wb → x = 1 := by
    intro x hx hx'
    have h := wsub_indep hP hα hβ hab hA (x0 := 1) (xa := x) (xb := x⁻¹) (xp := 1) (xm := 1) (Subgroup.one_mem _) hx (Subgroup.inv_mem _ hx') (Subgroup.one_mem _) (Subgroup.one_mem _) (by simp)
    exact h.2.1
  have i13 : ∀ x, x ∈ wsub α β ⊤ hA .wa → x ∈ wsub α β ⊤ hA .wp → x = 1 := by
    intro x hx hx'
    have h := wsub_indep hP hα hβ hab hA (x0 := 1) (xa := x) (xb := 1) (xp := x⁻¹) (xm := 1) (Subgroup.one_mem _) hx (Subgroup.one_mem _) (Subgroup.inv_mem _ hx') (Subgroup.one_mem _) (by simp)
    exact h.2.1
  have i14 : ∀ x, x ∈ wsub α β ⊤ hA .wa → x ∈ wsub α β ⊤ hA .wm → x = 1 := by
    intro x hx hx'
    have h := wsub_indep hP hα hβ hab hA (x0 := 1) (xa := x) (xb := 1) (xp := 1) (xm := x⁻¹) (Subgroup.one_mem _) hx (Subgroup.one_mem _) (Subgroup.one_mem _) (Subgroup.inv_mem _ hx') (by simp)
    exact h.2.1
  have i23 : ∀ x, x ∈ wsub α β ⊤ hA .wb → x ∈ wsub α β ⊤ hA .wp → x = 1 := by
    intro x hx hx'
    have h := wsub_indep hP hα hβ hab hA (x0 := 1) (xa := 1) (xb := x) (xp := x⁻¹) (xm := 1) (Subgroup.one_mem _) (Subgroup.one_mem _) hx (Subgroup.inv_mem _ hx') (Subgroup.one_mem _) (by simp)
    exact h.2.2.1
  have i24 : ∀ x, x ∈ wsub α β ⊤ hA .wb → x ∈ wsub α β ⊤ hA .wm → x = 1 := by
    intro x hx hx'
    have h := wsub_indep hP hα hβ hab hA (x0 := 1) (xa := 1) (xb := x) (xp := 1) (xm := x⁻¹) (Subgroup.one_mem _) (Subgroup.one_mem _) hx (Subgroup.one_mem _) (Subgroup.inv_mem _ hx') (by simp)
    exact h.2.2.1
  have i34 : ∀ x, x ∈ wsub α β ⊤ hA .wp → x ∈ wsub α β ⊤ hA .wm → x = 1 := by
    intro x hx hx'
    have h := wsub_indep hP hα hβ hab hA (x0 := 1) (xa := 1) (xb := 1) (xp := x) (xm := x⁻¹) (Subgroup.one_mem _) (Subgroup.one_mem _) (Subgroup.one_mem _) hx (Subgroup.inv_mem _ hx') (by simp)
    exact h.2.2.2.1
  match w, w' with
    | .w0, .w0 => exact absurd rfl hne
    | .w0, .wa => exact i01 x hx hx'
    | .w0, .wb => exact i02 x hx hx'
    | .w0, .wp => exact i03 x hx hx'
    | .w0, .wm => exact i04 x hx hx'
    | .wa, .w0 => exact i01 x hx' hx
    | .wa, .wa => exact absurd rfl hne
    | .wa, .wb => exact i12 x hx hx'
    | .wa, .wp => exact i13 x hx hx'
    | .wa, .wm => exact i14 x hx hx'
    | .wb, .w0 => exact i02 x hx' hx
    | .wb, .wa => exact i12 x hx' hx
    | .wb, .wb => exact absurd rfl hne
    | .wb, .wp => exact i23 x hx hx'
    | .wb, .wm => exact i24 x hx hx'
    | .wp, .w0 => exact i03 x hx' hx
    | .wp, .wa => exact i13 x hx' hx
    | .wp, .wb => exact i23 x hx' hx
    | .wp, .wp => exact absurd rfl hne
    | .wp, .wm => exact i34 x hx hx'
    | .wm, .w0 => exact i04 x hx' hx
    | .wm, .wa => exact i14 x hx' hx
    | .wm, .wb => exact i24 x hx' hx
    | .wm, .wp => exact i34 x hx' hx
    | .wm, .wm => exact absurd rfl hne

@[expose] def gAut {P : Type*} [Group P] (α β : MulAut P) : Wt → MulAut P
  | .w0 => 1
  | .wa => β
  | .wb => α
  | .wp => α * β⁻¹
  | .wm => α * β

theorem fixSub_gAut {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) {α β : MulAut P}
    (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) (hab : α * β = β * α) (hA : AbInv2 α β (⊤ : Subgroup P))
    (hW0 : wsub α β ⊤ hA .w0 = ⊥) (w : Wt) (hw : w ≠ .w0) :
    fixSub (gAut α β w) = wsub α β ⊤ hA w := by
  have hcomm : ∀ x, α (β x) = β (α x) := fun x => by
    have := congrArg (fun f : MulAut P => f x) hab
    simpa [MulAut.mul_apply] using this
  have hnz : ∀ y ∈ wsub α β ⊤ hA .w0, y = 1 := fun y hy => by
    rw [hW0] at hy
    exact Subgroup.mem_bot.1 hy
  ext x
  cases w with
  | w0 => exact absurd rfl hw
  | wa =>
    rw [gAut, mem_fixSub]
    constructor
    · intro hx
      obtain ⟨x0, hx0, xa, hxa, hx'⟩ := fix_b_decomp hP hα hβ hab hA (Subgroup.mem_top x) hx
      rw [hnz x0 hx0, one_mul] at hx'
      rw [hx']
      exact hxa
    · intro hx
      exact ((mem_wsub_wa hA).1 hx).2.1
  | wb =>
    rw [gAut, mem_fixSub]
    constructor
    · intro hx
      obtain ⟨x0, hx0, xb, hxb, hx'⟩ := fix_a_decomp hP hα hβ hab hA (Subgroup.mem_top x) hx
      rw [hnz x0 hx0, one_mul] at hx'
      rw [hx']
      exact hxb
    · intro hx
      exact ((mem_wsub_wb hA).1 hx).2.1
  | wp =>
    rw [gAut, mem_fixSub]
    constructor
    · intro hx
      have h0 : α (β⁻¹ x) = x := hx
      have h1 : α x = β x :=
        calc α x = α (β (β⁻¹ x)) := by rw [MulAut.apply_inv_self]
          _ = β (α (β⁻¹ x)) := hcomm _
          _ = β x := by rw [h0]
      obtain ⟨x0, hx0, xp, hxp, hx'⟩ :=
        fix_ab_inv_decomp hP hα hβ hab hA (Subgroup.mem_top x) h1
      rw [hnz x0 hx0, one_mul] at hx'
      rw [hx']
      exact hxp
    · intro hx
      have h1 : α x = β x := ((mem_wsub_wp hA).1 hx).2.1
      show α (β⁻¹ x) = x
      calc α (β⁻¹ x) = β⁻¹ (β (α (β⁻¹ x))) := by rw [MulAut.inv_apply_self]
        _ = β⁻¹ (α (β (β⁻¹ x))) := by rw [hcomm]
        _ = β⁻¹ (α x) := by rw [MulAut.apply_inv_self]
        _ = β⁻¹ (β x) := by rw [h1]
        _ = x := MulAut.inv_apply_self _ _ x
  | wm =>
    rw [gAut, mem_fixSub, MulAut.mul_apply]
    constructor
    · intro hx
      obtain ⟨x0, hx0, xm, hxm, hx'⟩ := fix_ab_decomp hP hα hβ hab hA (Subgroup.mem_top x) hx
      rw [hnz x0 hx0, one_mul] at hx'
      rw [hx']
      exact hxm
    · intro hx
      exact ((mem_wsub_wm hA).1 hx).2.1

end Weights

section Main

variable {X B : Type*} [Group X] [Finite X] [Group B]

theorem abInv2_top (hX : IsPGroup 2 X) (α β : MulAut (X ⧸ frattini X)) :
    AbInv2 α β (⊤ : Subgroup (X ⧸ frattini X)) :=
  ⟨fun x _ y _ => V_comm hX x y, fun _ _ => Subgroup.mem_top _, fun _ _ => Subgroup.mem_top _⟩

omit [Finite X] in
theorem actV_pow3 (φ : B →* MulAut X) (hpow : ∀ a : B, a ^ 3 = 1) (g : B) :
    actV φ hpow g ^ 3 = 1 := by
  rw [← map_pow, hpow g, map_one]

@[expose] def gW (a₀ b₀ : B) : Wt → B
  | .w0 => 1
  | .wa => b₀
  | .wb => a₀
  | .wp => a₀ * b₀⁻¹
  | .wm => a₀ * b₀

omit [Finite X] in
theorem actV_gW (φ : B →* MulAut X) (hpow : ∀ a : B, a ^ 3 = 1) (a₀ b₀ : B) (w : Wt) :
    actV φ hpow (gW a₀ b₀ w) = gAut (actV φ hpow a₀) (actV φ hpow b₀) w := by
  cases w <;> simp [gW, gAut, map_mul, map_inv]

theorem fix_pow {P : Type*} [Group P] (f : MulAut P) {v : P} (h : f v = v) (n : ℕ) :
    (f ^ n) v = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem wsub_w0_eq_bot (hX : IsPGroup 2 X) {φ : B →* MulAut X} (hpow : ∀ a : B, a ^ 3 = 1)
    (hfix : ∀ x : X, (∀ b : B, (φ b x) * x⁻¹ ∈ frattini X) → x ∈ frattini X) (a₀ b₀ : B)
    (hgen : ∀ g : B, ∃ i j : ℕ, g = a₀ ^ i * b₀ ^ j) :
    wsub (actV φ hpow a₀) (actV φ hpow b₀) ⊤ (abInv2_top hX _ _) .w0 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨-, hva, hvb⟩ := (mem_wsub_w0 (abInv2_top hX _ _)).1 hv
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  have hall : ∀ g : B, actV φ hpow g (x : X ⧸ frattini X) = x := by
    intro g
    obtain ⟨i, j, rfl⟩ := hgen g
    rw [map_mul, MulAut.mul_apply, map_pow, map_pow, fix_pow _ hvb j, fix_pow _ hva i]
  have hx : x ∈ frattini X := by
    refine hfix x fun g => ?_
    have h := hall g
    rw [actV_mk] at h
    have := QuotientGroup.eq_iff_div_mem.1 h
    simpa [div_eq_mul_inv] using this
  exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff x).2 hx)

theorem wsub_ne_top (hX : IsPGroup 2 X) {φ : B →* MulAut X} (hpow : ∀ a : B, a ^ 3 = 1)
    (hinj : Function.Injective φ) (hcomm : ∀ a b : B, a * b = b * a) (a₀ b₀ : B)
    (ha₀ : a₀ ≠ 1) (hb₀ : b₀ ≠ 1) (hab : a₀ ≠ b₀) (hab' : a₀ ≠ b₀⁻¹)
    (hW0 : wsub (actV φ hpow a₀) (actV φ hpow b₀) ⊤ (abInv2_top hX _ _) .w0 = ⊥) (w : Wt)
    (hw : w ≠ .w0) :
    wsub (actV φ hpow a₀) (actV φ hpow b₀) ⊤ (abInv2_top hX _ _) w ≠ ⊤ := by
  intro htop
  have hP : IsPGroup 2 (X ⧸ frattini X) := hX.to_quotient _
  have hαβ : actV φ hpow a₀ * actV φ hpow b₀ = actV φ hpow b₀ * actV φ hpow a₀ := by
    rw [← map_mul, ← map_mul, hcomm a₀ b₀]
  have hfixS := fixSub_gAut hP (actV_pow3 φ hpow a₀) (actV_pow3 φ hpow b₀) hαβ
    (abInv2_top hX _ _) hW0 w hw
  rw [htop] at hfixS
  have h1 : actV φ hpow (gW a₀ b₀ w) = 1 := by
    rw [actV_gW]
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.one_apply]
    exact (mem_fixSub _ _).1 (by rw [hfixS]; trivial)
  have h2 := eq_one_of_actV_eq_one hX hpow _ h1
  have h3 : gW a₀ b₀ w = 1 := hinj (by rw [h2, map_one])
  cases w with
  | w0 => exact hw rfl
  | wa => exact hb₀ h3
  | wb => exact ha₀ h3
  | wp => exact hab (mul_inv_eq_one.1 h3)
  | wm => exact hab' (mul_eq_one_iff_eq_inv.1 h3)

theorem sup_frattini_eq_comap (hX : IsPGroup 2 X) {g : MulAut X} (hg : g ^ 3 = 1) :
    fixSub g ⊔ frattini X = (fixSub (aV g hg)).comap (QuotientGroup.mk' (frattini X)) := by
  rw [aV, fixSub_quotAut hX hg, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem bpair_of_V (hX : IsPGroup 2 X) {a b : MulAut X} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (hsup : fixSub (aV a ha) ⊔ fixSub (aV b hb) = ⊤)
    (hinf : fixSub (aV a ha) ⊓ fixSub (aV b hb) = ⊥) (hane : fixSub (aV a ha) ≠ ⊤)
    (hbne : fixSub (aV b hb) ≠ ⊤) : BPair X a b := by
  have hr : (QuotientGroup.mk' (frattini X)).range = ⊤ :=
    MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)
  have hcomap : ∀ H : Subgroup (X ⧸ frattini X),
      H.comap (QuotientGroup.mk' (frattini X)) = ⊤ → H = ⊤ := by
    intro H h
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have : x ∈ H.comap (QuotientGroup.mk' (frattini X)) := by rw [h]; trivial
    exact this
  refine ⟨ha, hb, hab, ?_, ?_, ?_, ?_⟩
  · rw [sup_frattini_eq_comap hX ha, sup_frattini_eq_comap hX hb,
      Subgroup.comap_sup_eq_of_le_range _ (hr ▸ le_top) (hr ▸ le_top), hsup, Subgroup.comap_top]
  · have h : (fixSub (aV a ha) ⊓ fixSub (aV b hb)).comap (QuotientGroup.mk' (frattini X)) =
        frattini X := by
      rw [hinf, MonoidHom.comap_bot, QuotientGroup.ker_mk']
    rw [sup_frattini_eq_comap hX ha, sup_frattini_eq_comap hX hb, ← Subgroup.comap_inf]
    exact h.le
  · intro h
    rw [sup_frattini_eq_comap hX ha] at h
    exact hane (hcomap _ h)
  · intro h
    rw [sup_frattini_eq_comap hX hb] at h
    exact hbne (hcomap _ h)

theorem exists_bpair (hX : IsPGroup 2 X) (h4 : FourGen X) {φ : B →* MulAut X} [Finite B]
    (hinj : Function.Injective φ) (hcomm : ∀ a b : B, a * b = b * a)
    (hpow : ∀ a : B, a ^ 3 = 1) (hcard : Nat.card B = 9)
    (hfix : ∀ x : X, (∀ b : B, (φ b x) * x⁻¹ ∈ frattini X) → x ∈ frattini X) :
    ∃ a b : MulAut X, BPair X a b := by
  obtain ⟨a₀, b₀, ha₀, hb₀, hab, hab', hgen⟩ := exists_gens hcomm hpow hcard
  have hP : IsPGroup 2 (X ⧸ frattini X) := hX.to_quotient _
  have hα3 := actV_pow3 φ hpow a₀
  have hβ3 := actV_pow3 φ hpow b₀
  have hαβ : actV φ hpow a₀ * actV φ hpow b₀ = actV φ hpow b₀ * actV φ hpow a₀ := by
    rw [← map_mul, ← map_mul, hcomm a₀ b₀]
  have hA := abInv2_top hX (actV φ hpow a₀) (actV φ hpow b₀)
  have hW0 := wsub_w0_eq_bot hX hpow hfix a₀ b₀ hgen
  have hproper := fun w hw =>
    wsub_ne_top hX hpow hinj hcomm a₀ b₀ ha₀ hb₀ hab hab' hW0 w hw
  have hVcard := card_V_le hX h4
  obtain ⟨w₁, w₂, h12, h1, h2, hne1, hne2, hother⟩ := exists_pair_aux
    (wsub (actV φ hpow a₀) (actV φ hpow b₀) ⊤ hA) hW0 hproper
    (by
      intro x
      obtain ⟨x0, hx0, xa, hxa, xb, hxb, xp, hxp, xm, hxm, rfl⟩ :=
        wsub_decomp hP hα3 hβ3 hαβ hA (Subgroup.mem_top x)
      have : x0 = 1 := by
        rw [hW0] at hx0
        exact Subgroup.mem_bot.1 hx0
      subst this
      exact ⟨xa, hxa, xb, hxb, xp, hxp, xm, hxm, by simp⟩)
    (by
      have h := wsub_card hP hα3 hβ3 hαβ hA
      rw [Subgroup.card_top, hW0, Subgroup.card_bot, one_mul] at h
      omega)
    (fun w hw hb => wsub_card_ge_four hP hα3 hβ3 hαβ hA (fun x _ => V_sq hX x) hw hb)
    (fun w => Nat.card_pos)
  have h3a := pow3_of (φ := φ) hpow (gW a₀ b₀ w₂)
  have h3b := pow3_of (φ := φ) hpow (gW a₀ b₀ w₁)
  have hfa : fixSub (aV (φ (gW a₀ b₀ w₂)) h3a) =
      wsub (actV φ hpow a₀) (actV φ hpow b₀) ⊤ hA w₂ := by
    have := fixSub_gAut hP hα3 hβ3 hαβ hA hW0 w₂ h2
    rw [← this, ← actV_gW]
    rfl
  have hfb : fixSub (aV (φ (gW a₀ b₀ w₁)) h3b) =
      wsub (actV φ hpow a₀) (actV φ hpow b₀) ⊤ hA w₁ := by
    have := fixSub_gAut hP hα3 hβ3 hαβ hA hW0 w₁ h1
    rw [← this, ← actV_gW]
    rfl
  have hcomp : ∀ w, ∀ y ∈ wsub (actV φ hpow a₀) (actV φ hpow b₀) ⊤ hA w,
      y ∈ wsub (actV φ hpow a₀) (actV φ hpow b₀) ⊤ hA w₂ ⊔
        wsub (actV φ hpow a₀) (actV φ hpow b₀) ⊤ hA w₁ := by
    intro w y hy
    by_cases hw2 : w = w₂
    · subst hw2
      exact Subgroup.mem_sup_left hy
    by_cases hw1 : w = w₁
    · subst hw1
      exact Subgroup.mem_sup_right hy
    · have := hother w hw1 hw2
      rw [this] at hy
      rw [Subgroup.mem_bot.1 hy]
      exact Subgroup.one_mem _
  refine ⟨φ (gW a₀ b₀ w₂), φ (gW a₀ b₀ w₁), bpair_of_V hX h3a h3b ?_ ?_ ?_ ?_ ?_⟩
  · rw [← map_mul, ← map_mul, hcomm]
  · rw [hfa, hfb, eq_top_iff]
    intro x _
    obtain ⟨x0, hx0, xa, hxa, xb, hxb, xp, hxp, xm, hxm, rfl⟩ :=
      wsub_decomp hP hα3 hβ3 hαβ hA (Subgroup.mem_top x)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hcomp _ _ hx0) (hcomp _ _ hxa)) (hcomp _ _ hxb)) (hcomp _ _ hxp)) (hcomp _ _ hxm)
  · rw [hfa, hfb, eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (indep_pair hP hα3 hβ3 hαβ hA h12.symm hx.1 hx.2)
  · rw [hfa]
    exact hproper w₂ h2
  · rw [hfb]
    exact hproper w₁ h1

end Main

end Wrap

theorem gen4_bgroup_class_le_two {X B : Type*} [Group X] [Finite X] [Group B] [Finite B]
    (φ : B →* MulAut X) (hX : IsPGroup 2 X) (hP : ∀ P : Subgroup X, Group.rank ↥P ≤ 4)
    (hinj : Function.Injective φ) (hcomm : ∀ a b : B, a * b = b * a)
    (hpow : ∀ a : B, a ^ 3 = 1) (hcard : Nat.card B = 9)
    (hfix : ∀ x : X, (∀ b : B, (φ b x) * x⁻¹ ∈ frattini X) → x ∈ frattini X) :
    ∀ x y z : X, ⁅⁅x, y⁆, z⁆ = 1 := by
  have h4 := Wrap.fourGen_of_rank hP
  obtain ⟨a, b, hab⟩ := Wrap.exists_bpair hX h4 hinj hcomm hpow hcard hfix
  have hcore := cl2_core hX h4 hab
  intro x y z
  have h1 : ⁅x, y⁆ ∈ dsub X :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have h2 := Subgroup.commutator_mem_commutator h1 (Subgroup.mem_top z)
  rw [hcore] at h2
  exact Subgroup.mem_bot.1 h2

end CFSG.GH74.E2
