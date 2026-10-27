
module

public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitInputs
public import CFSG.GF2Type.Smith1979.GammaU.Enum

@[expose] public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour.Orb

theorem orbitList_spec {gs : List (Array ℕ)} (hgs : GensOK gs) (v : ℕ) :
    ∀ n ∈ orbitList gs v, ∃ U ∈ genGrp gs, vecOf n = U (vecOf v) := by
  unfold orbitList
  refine bfsClosure_inv id (gs.map appN)
    (P := fun n => ∃ U ∈ genGrp gs, vecOf n = U (vecOf v)) ?_ 4096 [v] _ [] ?_ (by simp)
  · intro f hf n ⟨U, hU, hn⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact ⟨eqvOf g (invR g) (hgs g hg).2.2.1 (hgs g hg).2.2.2 * U,
      mul_mem (gen_mem hgs hg) hU, by rw [vecOf_appN, hn]; rfl⟩
  · simp only [List.mem_singleton, forall_eq]
    exact ⟨1, one_mem _, rfl⟩

theorem invariant_of_gens {gs : List (Array ℕ)} (hgs : GensOK gs) {P : ℕ → Bool}
    (h : ∀ n < 4096, P n = true → ∀ g ∈ gs, P (appN g n) = true) :
    ∀ U ∈ genGrp gs, ∀ n < 4096, P n = true → P (codeOf (U (vecOf n))) = true := by
  intro U hU
  have hU' : U ∈ Submonoid.closure (GenSet gs) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hU
  refine Submonoid.closure_induction_left (s := GenSet gs)
    (motive := fun (U : V12 ≃ₗ[ZMod 2] V12) _ =>
      ∀ n < 4096, P n = true → P (codeOf (U (vecOf n))) = true) ?_ ?_ hU'
  · intro n hn hP
    have h1 : ((1 : V12 ≃ₗ[ZMod 2] V12)) (vecOf n) = vecOf n := rfl
    rw [h1, codeOf_vecOf hn]
    exact hP
  · rintro x ⟨r, hr, hx⟩ y _ ihy n hn hP
    have hm := ihy n hn hP
    have hlt : codeOf (y (vecOf n)) < 4096 := codeOf_lt _
    have hr' := okRows_spec (hgs r hr).1
    have e1 : (x * y) (vecOf n) = x (vecOf (codeOf (y (vecOf n)))) := by
      rw [LinearEquiv.mul_apply, vecOf_codeOf]
    have e2 : x (vecOf (codeOf (y (vecOf n)))) = vecOf (appN r (codeOf (y (vecOf n)))) := by
      rw [hx, ← vecOf_appN]
    rw [e1, e2, codeOf_vecOf (appN_lt hr'.2 _)]
    exact h _ hlt hm r hr

theorem exists_of_reach {gs : List (Array ℕ)} (hgs : GensOK gs) {P : ℕ → Bool} {v : ℕ}
    (hreach : ∀ n < 4096, P n = true → n ∈ orbitList gs v) {a b : V12}
    (ha : P (codeOf a) = true) (hb : P (codeOf b) = true) : ∃ U ∈ genGrp gs, U a = b := by
  obtain ⟨U₁, hU₁, h₁⟩ := orbitList_spec hgs v _ (hreach _ (codeOf_lt a) ha)
  obtain ⟨U₂, hU₂, h₂⟩ := orbitList_spec hgs v _ (hreach _ (codeOf_lt b) hb)
  rw [vecOf_codeOf] at h₁ h₂
  refine ⟨U₂ * U₁⁻¹, mul_mem hU₂ (inv_mem hU₁), ?_⟩
  rw [LinearEquiv.mul_apply, h₁, inv_apply_apply]
  exact h₂.symm

theorem forall_lt_4096 {p : ℕ → Bool} (h : (List.range 4096).all p = true) :
    ∀ n < 4096, p n = true := fun n hn => List.all_eq_true.1 h n (List.mem_range.2 hn)

@[expose] def inO378 (v : V12) : Prop := inO378b (codeOf v) = true

@[expose] def inO1701 (v : V12) : Prop := inO1701b (codeOf v) = true

instance : DecidablePred inO378 := fun v => instDecidableEqBool _ _

instance : DecidablePred inO1701 := fun v => instDecidableEqBool _ _

theorem code_singular_cases : ∀ n < 4096, n ≠ 0 → q0b n = false →
    (inO378b n = true ∨ inO1701b n = true) ∧ ¬(inO378b n = true ∧ inO1701b n = true) := by
  have h : (List.range 4096).all
      (fun n => n == 0 || q0b n || (inO378b n != inO1701b n)) = true := by decide +kernel
  intro n hn hn0 hq
  have := forall_lt_4096 h n hn
  simp only [Bool.or_eq_true, beq_iff_eq, hn0, hq, bne_iff_ne, ne_eq] at this
  cases h1 : inO378b n <;> cases h2 : inO1701b n <;> simp_all

theorem code_singular_of_inO378 : ∀ n < 4096, inO378b n = true → n ≠ 0 ∧ q0b n = false := by
  have h : (List.range 4096).all (fun n => !inO378b n || (n != 0 && !q0b n)) = true := by
    decide +kernel
  intro n hn hP
  have := forall_lt_4096 h n hn
  simpa [hP] using this

theorem code_singular_of_inO1701 : ∀ n < 4096, inO1701b n = true → n ≠ 0 ∧ q0b n = false := by
  have h : (List.range 4096).all (fun n => !inO1701b n || (n != 0 && !q0b n)) = true := by
    decide +kernel
  intro n hn hP
  have := forall_lt_4096 h n hn
  simpa [hP] using this

theorem singular_cases {v : V12} (hv : v ≠ 0) (hq : q0 v = 0) :
    (inO378 v ∨ inO1701 v) ∧ ¬(inO378 v ∧ inO1701 v) := by
  have hq' : q0b (codeOf v) = false := by
    have := q0_vecOf (codeOf v)
    rw [vecOf_codeOf, hq] at this
    cases h : q0b (codeOf v)
    · rfl
    · simp [h] at this
  have hn0 : codeOf v ≠ 0 := fun h => hv (by rw [← vecOf_codeOf v, h, vecOf_zero])
  exact code_singular_cases _ (codeOf_lt v) hn0 hq'

theorem ne_zero_of_inO378 {v : V12} (hv : inO378 v) : v ≠ 0 ∧ q0 v = 0 := by
  have h := code_singular_of_inO378 _ (codeOf_lt v) hv
  refine ⟨fun h0 => h.1 (by rw [h0]; simp [codeOf]), ?_⟩
  have := q0_vecOf (codeOf v)
  rw [vecOf_codeOf, h.2] at this
  simpa using this

theorem ne_zero_of_inO1701 {v : V12} (hv : inO1701 v) : v ≠ 0 ∧ q0 v = 0 := by
  have h := code_singular_of_inO1701 _ (codeOf_lt v) hv
  refine ⟨fun h0 => h.1 (by rw [h0]; simp [codeOf]), ?_⟩
  have := q0_vecOf (codeOf v)
  rw [vecOf_codeOf, h.2] at this
  simpa using this

@[expose] def codeEquiv : V12 ≃ Fin 4096 where
  toFun v := ⟨codeOf v, codeOf_lt v⟩
  invFun n := vecOf n
  left_inv v := vecOf_codeOf v
  right_inv n := Fin.ext (codeOf_vecOf n.2)

theorem card_inO378 : Nat.card {v : V12 // inO378 v} = 378 := by
  have e : {v : V12 // inO378 v} ≃ {n : Fin 4096 // inO378b n = true} :=
    codeEquiv.subtypeEquiv (fun v => Iff.rfl)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_inO1701 : Nat.card {v : V12 // inO1701 v} = 1701 := by
  have e : {v : V12 // inO1701 v} ≃ {n : Fin 4096 // inO1701b n = true} :=
    codeEquiv.subtypeEquiv (fun v => Iff.rfl)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem orbitSetOK_spec {gs : List (Array ℕ)} {v : ℕ} {P : ℕ → Bool}
    (h : orbitSetOK gs v P = true) :
    P v = true ∧ ∀ n < 4096, P n = true → n ∈ orbitList gs v ∧ ∀ g ∈ gs, P (appN g n) = true := by
  simp only [orbitSetOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  refine ⟨h.1, fun n hn hP => ?_⟩
  have := h.2 n (List.mem_range.2 hn)
  rcases this with hP' | ⟨hc, hg⟩
  · rw [hP] at hP'
    exact absurd hP' (by simp)
  · refine ⟨?_, fun g hg' => by simpa using hg g hg'⟩
    rw [Std.HashSet.contains_ofList, List.contains_iff_mem] at hc
    exact hc

theorem exists_E0_of_images {c v w : V12} (hv : ∃ U ∈ E0, U c = v) (hw : ∃ U ∈ E0, U c = w) :
    ∃ U ∈ E0, U v = w := by
  obtain ⟨A, hA, rfl⟩ := hv
  obtain ⟨B, hB, rfl⟩ := hw
  refine ⟨B * A⁻¹, mul_mem hB (inv_mem hA), ?_⟩
  rw [LinearEquiv.mul_apply, inv_apply_apply]

end CFSG.GF2Type.Smith1979.IdxFour
