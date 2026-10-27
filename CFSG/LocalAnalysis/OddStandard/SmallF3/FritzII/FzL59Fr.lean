module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Dict

import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59R6

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal CFSG.GH74.GLS.Bg.TwoGroups

variable {G : Type} [Group G]

theorem fz59f_z4z4_gen : ∀ U V W : Z4Z4, U ^ 2 ≠ 1 → V ^ 2 ≠ 1 → U ^ 2 ≠ V ^ 2 →
    ∃ m n : Fin 4, W = U ^ (m : ℕ) * V ^ (n : ℕ) := by
  decide +kernel

section Str

variable {t tau lam rho : G} {Z E W Q R T : Subgroup G}

theorem fz59f_rho_mul3 (h : FzStr t tau lam rho Z E W Q R T) : rho * rho * rho = 1 := by
  have h3 := h.rho_ord
  rwa [pow_succ, pow_succ, pow_one] at h3

theorem fz59f_comm_E (h : FzStr t tau lam rho Z E W Q R T) {a b : G} (ha : a ∈ E) (hb : b ∈ E) :
    Commute a b :=
  h.W_comm a (h.EW ha) b (h.EW hb)

theorem fz59f_fix_one (h : FzStr t tau lam rho Z E W Q R T) :
    ∀ e ∈ E, rho * e * rho⁻¹ = e → e = 1 := by
  intro e he hfix
  have hsq : e ^ 2 = 1 := by
    by_contra hne
    have hz : e ^ 2 ∈ Z := h.E_sq e he
    refine h.rho_Z _ hz hne ?_
    rw [← conj_pow, hfix]
  by_contra hne
  exact h.rho_Z e (h.E_invol e he hsq) hne hfix

theorem fz59f_norm_one (h : FzStr t tau lam rho Z E W Q R T) :
    ∀ e ∈ E, e * (rho * e * rho⁻¹) * (rho * (rho * e * rho⁻¹) * rho⁻¹) = 1 := by
  intro e he
  have he₁ : rho * e * rho⁻¹ ∈ E := h.rho_nrm_E e he
  have he₂ : rho * (rho * e * rho⁻¹) * rho⁻¹ ∈ E := h.rho_nrm_E _ he₁
  have h3 : rho * (rho * (rho * e * rho⁻¹) * rho⁻¹) * rho⁻¹ = e := by
    have h3' : rho * (rho * (rho * e * rho⁻¹) * rho⁻¹) * rho⁻¹ =
        (rho * rho * rho) * e * (rho * rho * rho)⁻¹ := by group
    rw [h3', fz59f_rho_mul3 h]
    group
  generalize he₁d : rho * e * rho⁻¹ = e₁ at he₁ he₂ h3 ⊢
  generalize he₂d : rho * e₁ * rho⁻¹ = e₂ at he₂ h3 ⊢
  apply fz59f_fix_one h _ (E.mul_mem (E.mul_mem he he₁) he₂)
  have hN : rho * (e * e₁ * e₂) * rho⁻¹ =
      (rho * e * rho⁻¹) * (rho * e₁ * rho⁻¹) * (rho * e₂ * rho⁻¹) := by group
  rw [hN, he₁d, he₂d, h3, (fz59f_comm_E h (E.mul_mem he₁ he₂) he).eq, mul_assoc]

theorem fz59f_comm_t (h : FzStr t tau lam rho Z E W Q R T) {e : G} (he : e ∈ E) :
    Commute e t :=
  h.W_comm e (h.EW he) t h.t_mem

theorem fz59f_sq_mul_t (h : FzStr t tau lam rho Z E W Q R T) {e : G} (he : e ∈ E) :
    (e * t) ^ 2 = e ^ 2 := by
  rw [(fz59f_comm_t h he).mul_pow, h.t_sq, mul_one]

theorem fz59f_rho_mul_t (h : FzStr t tau lam rho Z E W Q R T) (e : G) :
    rho * (e * t) * rho⁻¹ = rho * e * rho⁻¹ * t := by
  calc rho * (e * t) * rho⁻¹ = (rho * e * rho⁻¹) * (rho * t * rho⁻¹) := by group
    _ = rho * e * rho⁻¹ * t := by rw [h.rho_t]

theorem fz59f_sq_of_norm (h : FzStr t tau lam rho Z E W Q R T) {e₀ e₁ e₂ : G} (h₀ : e₀ ∈ E)
    (h₁ : e₁ ∈ E) (h₂ : e₂ ∈ E) (hn : e₀ * e₁ * e₂ = 1) : e₀ ^ 2 = e₁ ^ 2 * e₂ ^ 2 := by
  have hsq : e₀ ^ 2 * (e₁ ^ 2 * e₂ ^ 2) = 1 := by
    have : (e₀ * e₁ * e₂) ^ 2 = e₀ ^ 2 * (e₁ ^ 2 * e₂ ^ 2) := by
      rw [(fz59f_comm_E h (E.mul_mem h₀ h₁) h₂).mul_pow, (fz59f_comm_E h h₀ h₁).mul_pow,
        mul_assoc]
    rw [← this, hn, one_pow]
  have hz : e₁ ^ 2 * e₂ ^ 2 ∈ Z := Z.mul_mem (h.E_sq _ h₁) (h.E_sq _ h₂)
  have hz2 : (e₁ ^ 2 * e₂ ^ 2) * (e₁ ^ 2 * e₂ ^ 2) = 1 := by
    rw [← pow_two]
    exact h.Z_sq _ hz
  exact mul_right_cancel (b := e₁ ^ 2 * e₂ ^ 2) (hsq.trans hz2.symm)

theorem fz59f_sq_eq (h : FzStr t tau lam rho Z E W Q R T) {c : G} (hc : c ∈ E) :
    (c * t) ^ 2 = (rho * (c * t) * rho⁻¹) ^ 2 *
      (rho * (rho * (c * t) * rho⁻¹) * rho⁻¹) ^ 2 := by
  have he₁ : rho * c * rho⁻¹ ∈ E := h.rho_nrm_E c hc
  have he₂ : rho * (rho * c * rho⁻¹) * rho⁻¹ ∈ E := h.rho_nrm_E _ he₁
  rw [fz59f_rho_mul_t h c, fz59f_rho_mul_t h (rho * c * rho⁻¹), fz59f_sq_mul_t h hc,
    fz59f_sq_mul_t h he₁, fz59f_sq_mul_t h he₂]
  exact fz59f_sq_of_norm h hc he₁ he₂ (fz59f_norm_one h c hc)

theorem fz59f_t_eq (h : FzStr t tau lam rho Z E W Q R T) {c : G} (hc : c ∈ E) :
    t = rho * (c * t) * rho⁻¹ * (rho * (rho * (c * t) * rho⁻¹) * rho⁻¹) * (c * t) := by
  have he₁ : rho * c * rho⁻¹ ∈ E := h.rho_nrm_E c hc
  have he₂ : rho * (rho * c * rho⁻¹) * rho⁻¹ ∈ E := h.rho_nrm_E _ he₁
  have hn := fz59f_norm_one h c hc
  rw [fz59f_rho_mul_t h c, fz59f_rho_mul_t h (rho * c * rho⁻¹)]
  have ht : t * t = 1 := by rw [← pow_two]; exact h.t_sq
  have c₂ := fz59f_comm_t h he₂
  have hc₁₂ : Commute c (rho * c * rho⁻¹ * (rho * (rho * c * rho⁻¹) * rho⁻¹)) :=
    (fz59f_comm_E h hc he₁).mul_right (fz59f_comm_E h hc he₂)
  generalize rho * c * rho⁻¹ = e₁ at he₁ he₂ hn c₂ hc₁₂ ⊢
  generalize rho * e₁ * rho⁻¹ = e₂ at he₂ hn c₂ hc₁₂ ⊢
  have hec : e₁ * e₂ * c = 1 := by rw [← hc₁₂.eq, ← mul_assoc]; exact hn
  rw [c₂.symm.mul_mul_mul_comm e₁ t, ht, mul_one, ← mul_assoc, hec, one_mul]

theorem fz59f_E_gen (h : FzStr t tau lam rho Z E W Q R T) {u v : G} (hu : u ∈ E) (hv : v ∈ E)
    (hu2 : u ^ 2 ≠ 1) (hv2 : v ^ 2 ≠ 1) (huv : u ^ 2 ≠ v ^ 2) : closure {u, v} = E := by
  obtain ⟨g⟩ := h.E_equiv
  have inj2 : ∀ x : E, (g x) ^ 2 = 1 → (x : G) ^ 2 = 1 := by
    intro x hx
    have : x ^ 2 = 1 := g.injective (by rw [map_pow, hx, map_one])
    simpa using congrArg Subtype.val this
  have inj3 : ∀ x y : E, (g x) ^ 2 = (g y) ^ 2 → (x : G) ^ 2 = (y : G) ^ 2 := by
    intro x y hxy
    have : x ^ 2 = y ^ 2 := g.injective (by rw [map_pow, map_pow, hxy])
    simpa using congrArg Subtype.val this
  apply le_antisymm
  · rw [closure_le]
    rintro _ (rfl | rfl)
    · exact hu
    · exact hv
  · intro w hw
    obtain ⟨m, n, hmn⟩ := fz59f_z4z4_gen (g ⟨u, hu⟩) (g ⟨v, hv⟩) (g ⟨w, hw⟩)
      (fun h1 => hu2 (inj2 ⟨u, hu⟩ h1)) (fun h1 => hv2 (inj2 ⟨v, hv⟩ h1))
      (fun h1 => huv (inj3 ⟨u, hu⟩ ⟨v, hv⟩ h1))
    have hw' : (⟨w, hw⟩ : E) = ⟨u, hu⟩ ^ (m : ℕ) * ⟨v, hv⟩ ^ (n : ℕ) :=
      g.injective (by rw [map_mul, map_pow, map_pow]; exact hmn)
    have hw'' : w = u ^ (m : ℕ) * v ^ (n : ℕ) := by simpa using congrArg Subtype.val hw'
    rw [hw'']
    exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)

end Str

@[expose] def fz59fFrame {G : Type} [Group G] (rho a0 a1 : G) : Fin 3 → Fin 2 → G :=
  ![![rho * a0 * rho⁻¹, rho * a1 * rho⁻¹],
    ![rho * (rho * a0 * rho⁻¹) * rho⁻¹, rho * (rho * a1 * rho⁻¹) * rho⁻¹], ![a0, a1]]

section Abstract

variable {rho a0 a1 : G}

private theorem fz59f_conj2 (h : rho * rho * rho = 1) (a : G) :
    rho * (rho * a * rho⁻¹) * rho⁻¹ = rho⁻¹ * a * rho := by
  have e : rho⁻¹ = rho * rho := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact h)
  have e' : rho⁻¹ * rho⁻¹ = rho := by rw [← mul_inv_rev, inv_eq_of_mul_eq_one_right h]
  calc rho * (rho * a * rho⁻¹) * rho⁻¹ = (rho * rho) * a * (rho⁻¹ * rho⁻¹) := by group
    _ = rho⁻¹ * a * (rho⁻¹ * rho⁻¹) := by rw [← e]
    _ = rho⁻¹ * a * rho := by rw [e']

private theorem fz59f_conj3 (h : rho * rho * rho = 1) (a : G) :
    rho * (rho * (rho * a * rho⁻¹) * rho⁻¹) * rho⁻¹ = a := by
  calc rho * (rho * (rho * a * rho⁻¹) * rho⁻¹) * rho⁻¹
      = (rho * rho * rho) * a * (rho * rho * rho)⁻¹ := by group
    _ = a := by rw [h]; group

theorem fz59f_rho_b (h : rho * rho * rho = 1) (i : Fin 3) (k : Fin 2) :
    rho * fz59fFrame rho a0 a1 i k * rho⁻¹ = fz59fFrame rho a0 a1 (i + 1) k := by
  fin_cases i <;> fin_cases k
  · rfl
  · rfl
  · exact fz59f_conj3 h a0
  · exact fz59f_conj3 h a1
  · rfl
  · rfl

theorem fz59fFrame_mem {K : Subgroup G} (hρ : ∀ r ∈ K, rho * r * rho⁻¹ ∈ K)
    (h0 : a0 ∈ K) (h1 : a1 ∈ K) (i : Fin 3) (k : Fin 2) : fz59fFrame rho a0 a1 i k ∈ K := by
  fin_cases i <;> fin_cases k
  · exact hρ a0 h0
  · exact hρ a1 h1
  · exact hρ _ (hρ a0 h0)
  · exact hρ _ (hρ a1 h1)
  · exact h0
  · exact h1

theorem fz59f_rows (hq : IsQ8Pair a0 a1) (hρ : rho * rho * rho = 1)
    (hsq : a0 ^ 2 = (rho * a0 * rho⁻¹) ^ 2 * (rho * (rho * a0 * rho⁻¹) * rho⁻¹) ^ 2)
    (hc : ∀ x ∈ ({a0, a1} : Set G), ∀ y ∈ ({a0, a1} : Set G), Commute (rho * x * rho⁻¹) y) :
    Fz59Rows (fz59fFrame rho a0 a1) := by
  have h1 : IsQ8Pair (rho * a0 * rho⁻¹) (rho * a1 * rho⁻¹) :=
    hq.map (MulAut.conj rho).toMonoidHom (MulAut.conj rho).injective
  have h2 : IsQ8Pair (rho * (rho * a0 * rho⁻¹) * rho⁻¹) (rho * (rho * a1 * rho⁻¹) * rho⁻¹) :=
    h1.map (MulAut.conj rho).toMonoidHom (MulAut.conj rho).injective
  have hc02 : ∀ k l : Fin 2, Commute (fz59fFrame rho a0 a1 0 k) (fz59fFrame rho a0 a1 2 l) := by
    intro k l
    fin_cases k <;> fin_cases l
    · exact hc a0 (by simp) a0 (by simp)
    · exact hc a0 (by simp) a1 (by simp)
    · exact hc a1 (by simp) a0 (by simp)
    · exact hc a1 (by simp) a1 (by simp)
  have hc10 : ∀ k l : Fin 2, Commute (fz59fFrame rho a0 a1 1 k) (fz59fFrame rho a0 a1 0 l) := by
    intro k l
    have := (hc02 k l).map (MulAut.conj rho).toMonoidHom
    have e1 : (MulAut.conj rho).toMonoidHom (fz59fFrame rho a0 a1 0 k) =
        fz59fFrame rho a0 a1 1 k := fz59f_rho_b hρ 0 k
    have e2 : (MulAut.conj rho).toMonoidHom (fz59fFrame rho a0 a1 2 l) =
        fz59fFrame rho a0 a1 0 l := fz59f_rho_b hρ 2 l
    rwa [e1, e2] at this
  have hc21 : ∀ k l : Fin 2, Commute (fz59fFrame rho a0 a1 2 k) (fz59fFrame rho a0 a1 1 l) := by
    intro k l
    have := (hc10 k l).map (MulAut.conj rho).toMonoidHom
    have e1 : (MulAut.conj rho).toMonoidHom (fz59fFrame rho a0 a1 1 k) =
        fz59fFrame rho a0 a1 2 k := fz59f_rho_b hρ 1 k
    have e2 : (MulAut.conj rho).toMonoidHom (fz59fFrame rho a0 a1 0 l) =
        fz59fFrame rho a0 a1 1 l := fz59f_rho_b hρ 0 l
    rwa [e1, e2] at this
  refine ⟨fun i => ?_, hsq, fun i j hij k l => ?_⟩
  · fin_cases i
    · exact h1
    · exact h2
    · exact hq
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact (hc10 l k).symm
    · exact hc02 k l
    · exact hc10 k l
    · exact absurd rfl hij
    · exact (hc21 l k).symm
    · exact (hc02 l k).symm
    · exact hc21 k l
    · exact absurd rfl hij

theorem fz59f_grid {t s lam : G} (hq : IsQ8Pair a0 a1) (hρ : rho * rho * rho = 1)
    (hρ' : rho ^ 3 = 1)
    (hsq : a0 ^ 2 = (rho * a0 * rho⁻¹) ^ 2 * (rho * (rho * a0 * rho⁻¹) * rho⁻¹) ^ 2)
    (hc : ∀ x ∈ ({a0, a1} : Set G), ∀ y ∈ ({a0, a1} : Set G), Commute (rho * x * rho⁻¹) y)
    (ht : t = rho * a0 * rho⁻¹ * (rho * (rho * a0 * rho⁻¹) * rho⁻¹) * a0)
    (hs : s = rho * a1 * rho⁻¹ * (rho * (rho * a1 * rho⁻¹) * rho⁻¹) * a1)
    (hlam : lam ^ 2 = 1) (hl0 : lam * a0 * lam⁻¹ = a0) (hl1 : lam * a1 * lam⁻¹ = a1)
    (hlr : lam * rho * lam⁻¹ = rho⁻¹) : Fz59Grid t s lam rho (fz59fFrame rho a0 a1) := by
  have hr := fz59f_rows hq hρ hsq hc
  have key : ∀ a : G, lam * a * lam⁻¹ = a →
      lam * (rho * a * rho⁻¹) * lam⁻¹ = rho * (rho * a * rho⁻¹) * rho⁻¹ := by
    intro a ha
    calc lam * (rho * a * rho⁻¹) * lam⁻¹
        = (lam * rho * lam⁻¹) * (lam * a * lam⁻¹) * (lam * rho * lam⁻¹)⁻¹ := by group
      _ = rho⁻¹ * a * rho := by rw [hlr, ha, inv_inv]
      _ = rho * (rho * a * rho⁻¹) * rho⁻¹ := (fz59f_conj2 hρ a).symm
  refine ⟨hr.quat, hr.sq_eq, hr.comm, ht, hs, hlam, fun k => ?_, fun k => ?_, hρ',
    fz59f_rho_b hρ, hlr⟩
  · fin_cases k
    · exact key a0 hl0
    · exact key a1 hl1
  · fin_cases k
    · exact hl0
    · exact hl1

theorem fz59f_commute_of_comm {r y : G} (h : r * y * r⁻¹ * y⁻¹ = 1) : Commute r y :=
  mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)

theorem fz59f_comm_one {r y : G} (h : Commute r y) : r * y * r⁻¹ * y⁻¹ = 1 := by
  rw [h.eq]
  group

theorem fz59f_Q8_comm (hq : IsQ8Pair a0 a1) :
    ∀ g ∈ ({a0, a1} : Set G), ∀ y ∈ ({a0, a1} : Set G),
      g * y * g⁻¹ * y⁻¹ = 1 ∨ g * y * g⁻¹ * y⁻¹ = a0 ^ 2 := by
  have h1 : a1 * a0 * a1⁻¹ = a0⁻¹ := hq.2.2.1
  have hzz : a0 ^ 2 * a0 ^ 2 = 1 := hq.sq_mul_sq
  have hb : a1 * a0⁻¹ * a1⁻¹ = a0 := by
    have := congrArg (fun x => x⁻¹) h1
    simpa [mul_assoc] using this
  intro g hg y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hy
  rcases hg with hg | hg <;> rcases hy with hy | hy <;> rw [hg, hy]
  · left
    group
  · right
    calc a0 * a1 * a0⁻¹ * a1⁻¹ = a0 * (a1 * a0⁻¹ * a1⁻¹) := by group
      _ = a0 ^ 2 := by rw [hb, pow_two]
  · right
    rw [h1, ← mul_inv_rev, ← pow_two, inv_eq_of_mul_eq_one_right hzz]
  · left
    group

theorem fz59f_F1 {S : Set G} {K : Subgroup G} (hq : IsQ8Pair a0 a1)
    (hK : ∀ r ∈ K, r * a0 ^ 2 * r⁻¹ = a0 ^ 2) (hSK : S ⊆ K)
    (hS : ∀ g ∈ S, ∀ y ∈ ({a0, a1} : Set G),
      g * y * g⁻¹ * y⁻¹ = 1 ∨ g * y * g⁻¹ * y⁻¹ = a0 ^ 2) :
    ∀ r ∈ closure S, ∀ y ∈ ({a0, a1} : Set G),
      r * y * r⁻¹ * y⁻¹ = 1 ∨ r * y * r⁻¹ * y⁻¹ = a0 ^ 2 := by
  have hle : closure S ≤ K := (closure_le K).mpr hSK
  have hzz : a0 ^ 2 * a0 ^ 2 = 1 := hq.sq_mul_sq
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one =>
    intro y _
    left
    group
  | mul x y hx hy ihx ihy =>
    intro w hw
    have hxz : x * a0 ^ 2 * x⁻¹ = a0 ^ 2 := hK x (hle hx)
    have e : x * y * w * (x * y)⁻¹ * w⁻¹ =
        x * (y * w * y⁻¹ * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * w⁻¹) := by group
    rw [e]
    rcases ihy w hw with h1 | h1 <;> rcases ihx w hw with h2 | h2
    · left
      rw [h1, h2]
      group
    · right
      rw [h1, h2]
      group
    · right
      rw [h1, h2, mul_one, hxz]
    · left
      rw [h1, h2, hxz, hzz]
  | inv x hx ih =>
    intro w hw
    have hxz : x⁻¹ * a0 ^ 2 * x = a0 ^ 2 := by
      have := hK x⁻¹ (K.inv_mem (hle hx))
      rwa [inv_inv] at this
    have e : x⁻¹ * w * x⁻¹⁻¹ * w⁻¹ = x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ * x := by group
    rw [e]
    rcases ih w hw with h1 | h1
    · left
      rw [h1]
      group
    · right
      rw [h1, inv_eq_of_mul_eq_one_right hzz, hxz]

theorem fz59f_F2 {R : Subgroup G} (hq : IsQ8Pair a0 a1)
    (hR : ∀ r ∈ R, rho * r * rho⁻¹ ∈ R) (hR' : ∀ r ∈ R, rho⁻¹ * r * rho ∈ R)
    (ha : ∀ y ∈ ({a0, a1} : Set G), y ∈ R)
    (hF1 : ∀ r ∈ R, ∀ y ∈ ({a0, a1} : Set G),
      r * y * r⁻¹ * y⁻¹ = 1 ∨ r * y * r⁻¹ * y⁻¹ = a0 ^ 2)
    (hz : rho * a0 ^ 2 * rho⁻¹ ≠ a0 ^ 2) :
    ∀ x ∈ ({a0, a1} : Set G), ∀ y ∈ ({a0, a1} : Set G), Commute (rho * x * rho⁻¹) y := by
  have hzz : a0 ^ 2 * a0 ^ 2 = 1 := hq.sq_mul_sq
  intro x hx y hy
  apply fz59f_commute_of_comm
  rcases hF1 _ (hR x (ha x hx)) y hy with h1 | h1
  · exact h1
  · exfalso
    have e : rho * x * rho⁻¹ * y * (rho * x * rho⁻¹)⁻¹ * y⁻¹ =
        rho * ((rho⁻¹ * y * rho * x * (rho⁻¹ * y * rho)⁻¹ * x⁻¹)⁻¹) * rho⁻¹ := by group
    rw [e] at h1
    rcases hF1 _ (hR' y (ha y hy)) x hx with h2 | h2
    · rw [h2, inv_one, mul_one, mul_inv_cancel] at h1
      exact hq.2.2.2 h1.symm
    · rw [h2, inv_eq_of_mul_eq_one_right hzz] at h1
      exact hz h1

end Abstract

section Base

variable [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ : G} {T₂ : Subgroup G}

theorem fz59f_c_mem (x₁ x₂ : G) : (x₁ * x₂)⁻¹ ∈ baseGrp x₁ x₂ :=
  (baseGrp x₁ x₂).inv_mem ((baseGrp x₁ x₂).mul_mem (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)))

theorem fz59f_gen_mem_R (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) :
    ∀ g ∈ ({x₁ * t, a₁₂, x₂ * t, a₂₂, (x₁ * x₂)⁻¹ * t, a₃₂} : Set G), g ∈ fzR t x₁ x₂ :=
  fun _ hg => fzl59f_R6_le hB.str hB.shape (Subgroup.subset_closure hg)

theorem fz59f_grid_of_base (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) :
    Fz59Grid t (rho * a₃₂ * rho⁻¹ * (rho * (rho * a₃₂ * rho⁻¹) * rho⁻¹) * a₃₂) lam rho
      (fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂) := by
  have h := hB.str
  have hsh := hB.shape
  have hcE := fz59f_c_mem x₁ x₂
  have hq : IsQ8Pair ((x₁ * x₂)⁻¹ * t) a₃₂ := hsh.quat₃
  have hz3 : ((x₁ * x₂)⁻¹ * t) ^ 2 ∈ fourGrp x₁ x₂ := by
    rw [fz59f_sq_mul_t h hcE]
    exact h.E_sq _ hcE
  have hRR6 := (fzl59f_R_eq_R6_of_str h hsh).1
  have hgenR := fz59f_gen_mem_R hB
  have hF1 : ∀ r ∈ fzR t x₁ x₂, ∀ y ∈ ({(x₁ * x₂)⁻¹ * t, a₃₂} : Set G),
      r * y * r⁻¹ * y⁻¹ = 1 ∨ r * y * r⁻¹ * y⁻¹ = ((x₁ * x₂)⁻¹ * t) ^ 2 := by
    intro r hr
    rw [hRR6] at hr
    refine fz59f_F1 hq (K := fzR t x₁ x₂) (fun r hr => h.R_Z r hr _ hz3) hgenR ?_ r hr
    intro g hg y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg | hg | hg | hg
    · rw [hg]
      exact Or.inl (fz59f_comm_one (hsh.comm₁₃ _ (by simp) y hy))
    · rw [hg]
      exact Or.inl (fz59f_comm_one (hsh.comm₁₃ _ (by simp) y hy))
    · rw [hg]
      exact Or.inl (fz59f_comm_one (hsh.comm₂₃ _ (by simp) y hy))
    · rw [hg]
      exact Or.inl (fz59f_comm_one (hsh.comm₂₃ _ (by simp) y hy))
    · exact fz59f_Q8_comm hq g (by rw [hg]; simp) y hy
    · exact fz59f_Q8_comm hq g (by rw [hg]; simp) y hy
  have hRρ : ∀ r ∈ fzR t x₁ x₂, rho * r * rho⁻¹ ∈ fzR t x₁ x₂ :=
    fun r hr => hB.N2_nrm_R rho hB.rho_N2 r hr
  have hRρ' : ∀ r ∈ fzR t x₁ x₂, rho⁻¹ * r * rho ∈ fzR t x₁ x₂ := fun r hr => by
    simpa using hB.N2_nrm_R rho⁻¹ ((fzN2 t x₁ x₂).inv_mem hB.rho_N2) r hr
  have ha : ∀ y ∈ ({(x₁ * x₂)⁻¹ * t, a₃₂} : Set G), y ∈ fzR t x₁ x₂ := fun y hy =>
    hgenR y (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢; tauto)
  have hz : rho * ((x₁ * x₂)⁻¹ * t) ^ 2 * rho⁻¹ ≠ ((x₁ * x₂)⁻¹ * t) ^ 2 :=
    h.rho_Z _ hz3 hq.2.2.2
  exact fz59f_grid hq (fz59f_rho_mul3 h) h.rho_ord (fz59f_sq_eq h hcE)
    (fz59f_F2 hq hRρ hRρ' ha hF1 hz) (fz59f_t_eq h hcE) rfl hsh.lam_sq
    hsh.lam_comm₃.1.mul_inv_cancel hsh.lam_comm₃.2.mul_inv_cancel h.lam_rho

theorem fz59f_b_eq {Z E W Q R T : Subgroup G} (h : FzStr t tau lam rho Z E W Q R T) (c a1 : G) :
    fz59fFrame rho (c * t) a1 0 0 = rho * c * rho⁻¹ * t ∧
    fz59fFrame rho (c * t) a1 1 0 = rho * (rho * c * rho⁻¹) * rho⁻¹ * t ∧
    fz59fFrame rho (c * t) a1 2 0 = c * t := by
  have e1 := fz59f_rho_mul_t h c
  have e2 := fz59f_rho_mul_t h (rho * c * rho⁻¹)
  refine ⟨?_, ?_, rfl⟩
  · show rho * (c * t) * rho⁻¹ = _
    rw [e1]
  · show rho * (rho * (c * t) * rho⁻¹) * rho⁻¹ = _
    rw [e1, e2]

theorem fz59f_b_mul_t {Z E W Q R T : Subgroup G} (h : FzStr t tau lam rho Z E W Q R T)
    (c a1 : G) :
    fz59fFrame rho (c * t) a1 0 0 * t = rho * c * rho⁻¹ ∧
    fz59fFrame rho (c * t) a1 1 0 * t = rho * (rho * c * rho⁻¹) * rho⁻¹ ∧
    fz59fFrame rho (c * t) a1 2 0 * t = c := by
  have ht : t * t = 1 := by rw [← pow_two]; exact h.t_sq
  obtain ⟨e0, e1, e2⟩ := fz59f_b_eq h c a1
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, mul_assoc, ht, mul_one]
  · rw [e1, mul_assoc, ht, mul_one]
  · rw [e2, mul_assoc, ht, mul_one]

theorem fz59f_b_mul_t_mem (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) (i : Fin 3) :
    fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂ i 0 * t ∈ baseGrp x₁ x₂ := by
  have h := hB.str
  have hcE := fz59f_c_mem x₁ x₂
  have he₁ : rho * (x₁ * x₂)⁻¹ * rho⁻¹ ∈ baseGrp x₁ x₂ := h.rho_nrm_E _ hcE
  have he₂ : rho * (rho * (x₁ * x₂)⁻¹ * rho⁻¹) * rho⁻¹ ∈ baseGrp x₁ x₂ := h.rho_nrm_E _ he₁
  obtain ⟨hb0, hb1, hb2⟩ := fz59f_b_mul_t h (x₁ * x₂)⁻¹ a₃₂
  fin_cases i
  · show fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂ 0 0 * t ∈ baseGrp x₁ x₂
    rw [hb0]
    exact he₁
  · show fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂ 1 0 * t ∈ baseGrp x₁ x₂
    rw [hb1]
    exact he₂
  · show fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂ 2 0 * t ∈ baseGrp x₁ x₂
    rw [hb2]
    exact hcE

theorem fz59f_hR (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) :
    fzR t x₁ x₂ = fz59R (fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂) := by
  have h := hB.str
  have hgrid := fz59f_grid_of_base hB
  have hgenR := fz59f_gen_mem_R hB
  have hbR := fz59fFrame_mem (rho := rho) (fun r hr => hB.N2_nrm_R rho hB.rho_N2 r hr)
    (hgenR ((x₁ * x₂)⁻¹ * t) (by simp)) (hgenR a₃₂ (by simp))
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [fz59R, closure_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    exact hbR i k
  · rw [h.card_R, fz59_card_R hgrid.rows]
    norm_num

theorem fz59f_hZ (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) :
    fourGrp x₁ x₂ = fz59Z (fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂) := by
  have h := hB.str
  have hcE := fz59f_c_mem x₁ x₂
  have hgrid := fz59f_grid_of_base hB
  have he₁ : rho * (x₁ * x₂)⁻¹ * rho⁻¹ ∈ baseGrp x₁ x₂ := h.rho_nrm_E _ hcE
  have he₂ : rho * (rho * (x₁ * x₂)⁻¹ * rho⁻¹) * rho⁻¹ ∈ baseGrp x₁ x₂ := h.rho_nrm_E _ he₁
  obtain ⟨hb0, hb1, -⟩ := fz59f_b_eq h (x₁ * x₂)⁻¹ a₃₂
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [fz59Z, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg, hb0, fz59f_sq_mul_t h he₁]
      exact h.E_sq _ he₁
    · rw [hg, hb1, fz59f_sq_mul_t h he₂]
      exact h.E_sq _ he₂
  · rw [h.card_Z, fz59_card_Z hgrid.rows]

theorem fz59f_z3 (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) :
    fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂ 2 0 ^ 2 = (x₁ * x₂) ^ 2 := by
  have h := hB.str
  have hcE := fz59f_c_mem x₁ x₂
  have hx : x₁ * x₂ ∈ baseGrp x₁ x₂ := by simpa using (baseGrp x₁ x₂).inv_mem hcE
  show ((x₁ * x₂)⁻¹ * t) ^ 2 = _
  rw [fz59f_sq_mul_t h hcE, inv_pow]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add]
  exact h.E_exp _ hx

theorem fz59f_hE (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) :
    baseGrp x₁ x₂ =
      closure (Set.range fun i => fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂ i 0 * t) := by
  have h := hB.str
  have hcE := fz59f_c_mem x₁ x₂
  have hq : IsQ8Pair ((x₁ * x₂)⁻¹ * t) a₃₂ := hB.shape.quat₃
  have he₁ : rho * (x₁ * x₂)⁻¹ * rho⁻¹ ∈ baseGrp x₁ x₂ := h.rho_nrm_E _ hcE
  obtain ⟨hb0, -, hb2⟩ := fz59f_b_mul_t h (x₁ * x₂)⁻¹ a₃₂
  have hz : ((x₁ * x₂)⁻¹) ^ 2 ≠ 1 := by
    rw [← fz59f_sq_mul_t h hcE]
    exact hq.2.2.2
  have hρz := h.rho_Z _ (h.E_sq _ hcE) hz
  have hsq : (rho * (x₁ * x₂)⁻¹ * rho⁻¹) ^ 2 = rho * ((x₁ * x₂)⁻¹ ^ 2) * rho⁻¹ := conj_pow
  have hgen := fz59f_E_gen h hcE he₁ hz
    (by
      rw [hsq]
      intro h1
      apply hz
      calc ((x₁ * x₂)⁻¹) ^ 2 = rho⁻¹ * (rho * ((x₁ * x₂)⁻¹ ^ 2) * rho⁻¹) * rho := by group
        _ = 1 := by rw [h1]; group)
    (by
      rw [hsq]
      exact fun h1 => hρz h1.symm)
  apply le_antisymm
  · rw [← hgen, closure_le]
    rintro g (rfl | rfl)
    · exact Subgroup.subset_closure ⟨2, hb2⟩
    · exact Subgroup.subset_closure ⟨0, hb0⟩
  · rw [closure_le]
    rintro _ ⟨i, rfl⟩
    exact fz59f_b_mul_t_mem hB i

theorem fz59f_hW (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) :
    ctxW t x₁ x₂ = closure (Set.range fun i => fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂ i 0) := by
  have h := hB.str
  have hgrid := fz59f_grid_of_base hB
  have hE := fz59f_hE hB
  have hmem := fz59f_b_mul_t_mem hB
  generalize fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂ = b at hgrid hE hmem
  have hbW : ∀ i, b i 0 ∈ closure (Set.range fun i => b i 0) := fun i =>
    Subgroup.subset_closure ⟨i, rfl⟩
  have htW : t ∈ closure (Set.range fun i => b i 0) := by
    have := (closure (Set.range fun i => b i 0)).mul_mem
      ((closure (Set.range fun i => b i 0)).mul_mem (hbW 0) (hbW 1)) (hbW 2)
    rwa [← hgrid.t_eq] at this
  have hEW : baseGrp x₁ x₂ ≤ closure (Set.range fun i => b i 0) := by
    rw [hE, closure_le]
    rintro _ ⟨i, rfl⟩
    exact (closure (Set.range fun i => b i 0)).mul_mem (hbW i) htW
  apply le_antisymm
  · intro w hw
    rcases h.W_split w hw with hwE | hwE
    · exact hEW hwE
    · have := (closure (Set.range fun i => b i 0)).mul_mem
        ((closure (Set.range fun i => b i 0)).inv_mem htW) (hEW hwE)
      simpa using this
  · rw [closure_le]
    rintro _ ⟨i, rfl⟩
    have := (ctxW t x₁ x₂).mul_mem (h.EW (hmem i)) ((ctxW t x₁ x₂).inv_mem h.t_mem)
    simpa using this

theorem fz59f_s_cases (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) :
    rho * a₃₂ * rho⁻¹ * (rho * (rho * a₃₂ * rho⁻¹) * rho⁻¹) * a₃₂ = tau ∨
      rho * a₃₂ * rho⁻¹ * (rho * (rho * a₃₂ * rho⁻¹) * rho⁻¹) * a₃₂ = t * tau := by
  have h := hB.str
  have hgrid := fz59f_grid_of_base hB
  have hτ : tau ∈ fz59R (fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂) := by
    rw [← fz59f_hR hB]
    exact h.tau_R
  have hfix : rho * tau * rho⁻¹ = tau := by
    rw [← h.tau_rho]
    group
  have ht : t * t = 1 := by rw [← pow_two]; exact h.t_sq
  generalize rho * a₃₂ * rho⁻¹ * (rho * (rho * a₃₂ * rho⁻¹) * rho⁻¹) * a₃₂ = s at hgrid hτ ⊢
  rcases fz59_cent_rho hgrid tau hτ hfix with h1 | h1 | h1 | h1
  · exfalso
    apply h.tau_notin_Q
    rw [h1]
    exact one_mem _
  · exfalso
    apply h.tau_notin_Q
    rw [h1]
    exact h.WQ h.t_mem
  · exact Or.inl h1.symm
  · right
    rw [h1, ← mul_assoc, ht, one_mul]

end Base

theorem fz59_frame [Finite G] {t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ : G} {T₂ : Subgroup G}
    (hB : Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂) :
    ∃ (s : G) (b : Fin 3 → Fin 2 → G), Fz59Frame t tau lam rho x₁ x₂ s b :=
  ⟨_, fz59fFrame rho ((x₁ * x₂)⁻¹ * t) a₃₂, fz59f_grid_of_base hB, fz59f_s_cases hB,
    fz59f_hR hB, fz59f_hZ hB, fz59f_z3 hB, fz59f_hW hB, fz59f_hE hB⟩

end CFSG.OddStandard.SmallF3.FritzII
