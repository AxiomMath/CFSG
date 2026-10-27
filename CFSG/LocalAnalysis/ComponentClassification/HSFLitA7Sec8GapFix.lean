module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapNH

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

open Sec7

namespace GapFix

theorem vec_cases : ∀ y : Fin 3 → ZMod 2, y 2 = 1 →
    y = ![0, 0, 1] ∨ y = ![1, 0, 1] ∨ y = ![0, 1, 1] ∨ y = ![1, 1, 1] := by
  intro y hy
  have e : y = ![y 0, y 1, y 2] := by funext i; fin_cases i <;> rfl
  rw [e, hy]
  generalize y 0 = a
  generalize y 1 = b
  revert a b
  decide

theorem four_nsmul (v : Fin 3 → ZMod 2) : (4 : ℕ) • v = 0 := by
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  generalize v i = a
  revert a
  decide

theorem neg_vec (v : Fin 3 → ZMod 2) : -v = v := by
  funext i
  simp only [Pi.neg_apply]
  generalize v i = a
  revert a
  decide

theorem sum_affine {O : Finset (Fin 3 → ZMod 2)} {M : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    {p : Fin 3 → ZMod 2} (hinj : Function.Injective (M *ᵥ ·)) (hO : ∀ x ∈ O, M *ᵥ x + p ∈ O) :
    ∑ x ∈ O, x = M *ᵥ (∑ x ∈ O, x) + O.card • p := by
  classical
  have hinj' : Set.InjOn (fun x => M *ᵥ x + p) O := fun x _ y _ h => hinj (add_right_cancel h)
  have himg : O.image (fun x => M *ᵥ x + p) = O := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_)
      (by rw [Finset.card_image_of_injOn hinj'])
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hO x hx
  calc ∑ x ∈ O, x = ∑ y ∈ O.image (fun x => M *ᵥ x + p), y := by rw [himg]
    _ = ∑ x ∈ O, (M *ᵥ x + p) := Finset.sum_image hinj'
    _ = M *ᵥ (∑ x ∈ O, x) + O.card • p := by
        rw [Finset.sum_add_distrib, Matrix.mulVec_sum, Finset.sum_const]

theorem orbit (Rl : (Fin 3 → ZMod 2) → Prop)
    (Aff : Matrix (Fin 3) (Fin 3) (ZMod 2) → (Fin 3 → ZMod 2) → Prop)
    {Kb : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hKb : Kb = blk 0 1 1 1 ∨ Kb = blk 1 1 1 0)
    (h0 : Rl 0) (h1 : ∀ x, Rl x → x = 0 ∨ x 2 = 1) (hK : ∀ x, Rl x → Rl (Kb *ᵥ x))
    (hAff : ∀ M p, Aff M p → ∀ x, Rl x → Rl (M *ᵥ x + p))
    (hinj : ∀ M p, Aff M p → Function.Injective (M *ᵥ ·))
    (hreal : ∀ x, Rl x → ∃ M, Aff M x)
    (hfix : ∀ M, Aff M 0 → M *ᵥ ![0, 0, 1] = ![0, 0, 1]) :
    ∀ M p, Aff M p → M *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
  classical
  intro M p hMp
  have hp : Rl p := by
    have := hAff M p hMp 0 h0
    rwa [Matrix.mulVec_zero, zero_add] at this
  have h12 : Rl ![1, 0, 1] ↔ Rl ![0, 1, 1] := by
    rcases hKb with rfl | rfl
    · constructor
      · intro h; have := hK _ h; rwa [show blk 0 1 1 1 *ᵥ ![1, 0, 1] = ![0, 1, 1] by decide] at this
      · intro h
        have := hK _ (hK _ h)
        rwa [show blk 0 1 1 1 *ᵥ (blk 0 1 1 1 *ᵥ ![0, 1, 1]) = ![1, 0, 1] by decide] at this
    · constructor
      · intro h
        have := hK _ (hK _ h)
        rwa [show blk 1 1 1 0 *ᵥ (blk 1 1 1 0 *ᵥ ![1, 0, 1]) = ![0, 1, 1] by decide] at this
      · intro h; have := hK _ h; rwa [show blk 1 1 1 0 *ᵥ ![0, 1, 1] = ![1, 0, 1] by decide] at this
  have h13 : Rl ![1, 0, 1] ↔ Rl ![1, 1, 1] := by
    rcases hKb with rfl | rfl
    · constructor
      · intro h
        have := hK _ (hK _ h)
        rwa [show blk 0 1 1 1 *ᵥ (blk 0 1 1 1 *ᵥ ![1, 0, 1]) = ![1, 1, 1] by decide] at this
      · intro h; have := hK _ h; rwa [show blk 0 1 1 1 *ᵥ ![1, 1, 1] = ![1, 0, 1] by decide] at this
    · constructor
      · intro h; have := hK _ h; rwa [show blk 1 1 1 0 *ᵥ ![1, 0, 1] = ![1, 1, 1] by decide] at this
      · intro h
        have := hK _ (hK _ h)
        rwa [show blk 1 1 1 0 *ᵥ (blk 1 1 1 0 *ᵥ ![1, 1, 1]) = ![1, 0, 1] by decide] at this
  have hshape : ∀ y, Rl y → y = 0 ∨ y = ![0, 0, 1] ∨
      ((y = ![1, 0, 1] ∨ y = ![0, 1, 1] ∨ y = ![1, 1, 1]) ∧ Rl ![1, 0, 1]) := by
    intro y hy
    rcases h1 y hy with h | h
    · exact Or.inl h
    · rcases vec_cases y h with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨Or.inl rfl, hy⟩)
      · exact Or.inr (Or.inr ⟨Or.inr (Or.inl rfl), h12.mpr hy⟩)
      · exact Or.inr (Or.inr ⟨Or.inr (Or.inr rfl), h13.mpr hy⟩)
  by_cases hp0 : p = 0
  · subst hp0
    exact hfix M hMp
  by_cases hr : Rl ![1, 0, 1]
  · by_cases hc : Rl ![0, 0, 1]
    ·
      exfalso
      obtain ⟨M', hM'⟩ := hreal _ hc
      let O : Finset (Fin 3 → ZMod 2) := {0, ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]}
      have hOR : ∀ y, Rl y ↔ y ∈ O := by
        intro y
        constructor
        · intro hy
          simp only [O, Finset.mem_insert, Finset.mem_singleton]
          rcases hshape y hy with h | h | ⟨h | h | h, -⟩ <;> simp [h]
        · intro hy
          simp only [O, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl
          · exact h0
          · exact hc
          · exact hr
          · exact h12.mp hr
          · exact h13.mp hr
      have hsum := sum_affine (hinj M' _ hM') fun x hx =>
        (hOR _).mp (hAff M' _ hM' x ((hOR x).mpr hx))
      rw [show ∑ x ∈ O, x = 0 by decide, show O.card = 5 by decide, Matrix.mulVec_zero,
        zero_add] at hsum
      exact absurd hsum.symm (by decide)
    ·
      let O : Finset (Fin 3 → ZMod 2) := {0, ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]}
      have hOR : ∀ y, Rl y ↔ y ∈ O := by
        intro y
        constructor
        · intro hy
          simp only [O, Finset.mem_insert, Finset.mem_singleton]
          rcases hshape y hy with h | h | ⟨h | h | h, -⟩
          · simp [h]
          · exact absurd (h ▸ hy) hc
          · simp [h]
          · simp [h]
          · simp [h]
        · intro hy
          simp only [O, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl | rfl
          · exact h0
          · exact hr
          · exact h12.mp hr
          · exact h13.mp hr
      have hsum := sum_affine (hinj M p hMp) fun x hx =>
        (hOR _).mp (hAff M p hMp x ((hOR x).mpr hx))
      rw [show ∑ x ∈ O, x = ![0, 0, 1] by decide, show O.card = 4 by decide, four_nsmul,
        add_zero] at hsum
      exact hsum.symm
  ·
    have hpc : p = ![0, 0, 1] := by
      rcases hshape p hp with h | h | ⟨-, h⟩
      · exact absurd h hp0
      · exact h
      · exact absurd h hr
    subst hpc
    rcases hshape _ (hAff M _ hMp _ hp) with h | h | ⟨-, h⟩
    · have := eq_neg_of_add_eq_zero_left h
      rwa [neg_vec] at this
    · exfalso
      have h2 : M *ᵥ ![0, 0, 1] = M *ᵥ 0 := by
        rw [Matrix.mulVec_zero]
        exact add_right_cancel (h.trans (zero_add _).symm)
      exact absurd (hinj M _ hMp h2) (by decide)
    · exact absurd h hr

theorem mem_normalizer_of_map {X : Type} [Group X] {H : Subgroup X} {g : X}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set X) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx; rw [← h]; exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨x', hx', hxx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxx
    have : x' = x := by
      have := congrArg (fun y => g⁻¹ * y * g) hxx
      simpa [mul_assoc] using this
    rwa [← this]

end GapFix

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace BData

variable (A : BData S F T₁)

theorem conj_mem_C {n : X} (hn : n ∈ A.NA) {g : X} (hg : g ∈ centralizer (A.AA : Set X)) :
    n * g * n⁻¹ ∈ centralizer (A.AA : Set X) := by
  rw [mem_centralizer_iff] at hg ⊢
  intro a ha
  have ha' : n⁻¹ * a * n ∈ A.AA := by
    have := A.conj_mem_AA (inv_mem hn) ha
    rwa [inv_inv] at this
  have := hg _ ha'
  calc a * (n * g * n⁻¹) = n * ((n⁻¹ * a * n) * g) * n⁻¹ := by group
    _ = n * (g * (n⁻¹ * a * n)) * n⁻¹ := by rw [this]
    _ = n * g * n⁻¹ * a := by group

theorem C_le_NA : centralizer (A.AA : Set X) ≤ A.NA := centralizer_le_normalizer _

@[expose] noncomputable def Lt : Subgroup X := centralizer (A.AA : Set X) ⊔ zpowers S.t

theorem Lt_le_NA : A.Lt ≤ A.NA := sup_le A.C_le_NA (zpowers_le.mpr A.t_mem_NA)

theorem mat_t_inv : A.mat ⟨S.t, A.t_mem_NA⟩⁻¹ = -1 := A.mat_inv _ A.mat_t (by simp)

theorem redM_of_mem_Lt {x : X} (hx : x ∈ A.Lt) : redM (A.mat ⟨x, A.Lt_le_NA hx⟩) = 1 := by
  have htt : S.t * S.t = 1 := t_mul_t
  rcases mem_or_mem_of_mem_sup (by rw [htt]; exact one_mem _)
    (fun h hh => A.conj_mem_C A.t_mem_NA hh) hx with h | h
  · rw [(A.mat_eq_one_iff _).mpr h, redM_one]
  · have e : (⟨x, A.Lt_le_NA hx⟩ : A.NA) = ⟨S.t, A.t_mem_NA⟩ * ⟨S.t⁻¹ * x, A.C_le_NA h⟩ :=
      Subtype.ext (by simp)
    rw [e, A.mat_mul, A.mat_t, (A.mat_eq_one_iff _).mpr h, mul_one]
    decide

theorem mat_conj_t (n : A.NA) : A.mat (n * ⟨S.t, A.t_mem_NA⟩ * n⁻¹) = -1 := by
  rw [A.mat_mul, A.mat_mul, A.mat_t, mul_neg, mul_one, neg_mul, A.mat_mul_inv]

theorem conj_t_mem_Lt (n : A.NA) : (n : X) * S.t * (n : X)⁻¹ ∈ A.Lt := by
  have hc : S.t⁻¹ * ((n : X) * S.t * (n : X)⁻¹) ∈ centralizer (A.AA : Set X) :=
    (A.mat_eq_one_iff ((⟨S.t, A.t_mem_NA⟩ : A.NA)⁻¹ * (n * ⟨S.t, A.t_mem_NA⟩ * n⁻¹))).mp (by
      rw [A.mat_mul, A.mat_t_inv, A.mat_conj_t, neg_one_mul, neg_neg])
  have := mul_mem (mem_sup_right (mem_zpowers S.t) : S.t ∈ A.Lt) (mem_sup_left hc : _ ∈ A.Lt)
  rwa [mul_inv_cancel_left] at this

@[expose] def Rl (x : Fin 3 → ZMod 2) : Prop :=
  ∃ n : A.NA, ∃ a : Fin 3 → ZMod 4, (n : X) * S.t * (n : X)⁻¹ = S.t * A.Φ a ∧ redV a = x

theorem Rl_zero : A.Rl 0 :=
  ⟨1, 0, by simp [A.Φ_zero], funext fun i => map_zero r2⟩

theorem Rl_cases (hnc : ¬ SubConj F.E₁ F.E₂) {x : Fin 3 → ZMod 2} (hx : A.Rl x) :
    x = 0 ∨ x 2 = 1 := by
  obtain ⟨n, a, ha, rfl⟩ := hx
  by_contra h
  push Not at h
  have h2 : 2 * a 2 = 0 := by
    have h' : r2 (a 2) ≠ 1 := h.2
    have : r2 (a 2) = 0 := by
      generalize r2 (a 2) = y at h'
      revert y
      decide
    exact (r2_eq_zero_iff _).mp this
  refine A.not_conj_E0t hnc h2 ?_ (A.map_E₁ n ha)
  rintro ⟨h0, h1⟩
  apply h.1
  funext i
  fin_cases i
  · exact (r2_eq_zero_iff _).mpr h0
  · exact (r2_eq_zero_iff _).mpr h1
  · exact (r2_eq_zero_iff _).mpr h2

theorem Rl_aff {x : Fin 3 → ZMod 2} (hx : A.Rl x) (n₁ : A.NA) {a₁ : Fin 3 → ZMod 4}
    (h₁ : (n₁ : X) * S.t * (n₁ : X)⁻¹ = S.t * A.Φ a₁) :
    A.Rl (redM (A.mat n₁) *ᵥ x + redV a₁) := by
  obtain ⟨n, a, ha, rfl⟩ := hx
  refine ⟨n₁ * n, a₁ + A.mat n₁ *ᵥ a, ?_, ?_⟩
  · rw [A.Φ_add, ← A.conj_Φ]
    calc ((n₁ * n : A.NA) : X) * S.t * ((n₁ * n : A.NA) : X)⁻¹ =
        (n₁ : X) * ((n : X) * S.t * (n : X)⁻¹) * (n₁ : X)⁻¹ := by
          simp only [Subgroup.coe_mul]; group
      _ = ((n₁ : X) * S.t * (n₁ : X)⁻¹) * ((n₁ : X) * A.Φ a * (n₁ : X)⁻¹) := by rw [ha]; group
      _ = S.t * (A.Φ a₁ * ((n₁ : X) * A.Φ a * (n₁ : X)⁻¹)) := by rw [h₁]; group
  · rw [redV_add, redV_mulVec, add_comm]

theorem Rl_K {δ : X} (hδ : δ ∈ A.D₁.D₁₁) {x : Fin 3 → ZMod 2} (hx : A.Rl x) :
    A.Rl (redM (A.mat ⟨δ, A.D₁₁_le_NA hδ⟩) *ᵥ x) := by
  have := A.Rl_aff hx ⟨δ, A.D₁₁_le_NA hδ⟩ (a₁ := 0)
    (by rw [A.Φ_zero, mul_one, A.D₁₁_comm_t hδ, mul_inv_cancel_right])
  rwa [show redV (0 : Fin 3 → ZMod 4) = 0 from funext fun i => map_zero r2, add_zero] at this

theorem kF_fixed_of_redV {n : A.NA} {a : Fin 3 → ZMod 4}
    (ha : (n : X) * S.t * (n : X)⁻¹ = S.t * A.Φ a) (h0 : redV a = 0) :
    (n : X) * F.kF * (n : X)⁻¹ = F.kF := by
  have hev := (redV_eq_zero_iff a).mp h0
  choose s hs using fun i => GapNH.exists_add_self (a i) (hev i)
  have has : a = s + s := funext fun i => hs i
  set b := A.Φ s with hb
  have ht' : S.t⁻¹ = S.t := by rw [inv_eq_iff_mul_eq_one, t_mul_t]
  have hbt : b * S.t * b⁻¹ = S.t * A.Φ (-(s + s)) := by
    have h1 : S.t⁻¹ * b * S.t = A.Φ (-s) := by
      have := A.t_conj_Φ s
      rw [ht'] at this ⊢
      exact this
    calc b * S.t * b⁻¹ = S.t * (S.t⁻¹ * b * S.t) * b⁻¹ := by group
      _ = S.t * A.Φ (-s) * A.Φ (-s) := by rw [h1, hb, A.Φ_neg]
      _ = S.t * A.Φ (-(s + s)) := by rw [mul_assoc, ← A.Φ_add, neg_add]
  have hmt : (b * n) * S.t * (b * n)⁻¹ = S.t := by
    have hc : b * A.Φ a = A.Φ a * b := A.Φ_comm s a
    calc (b * n) * S.t * (b * n)⁻¹ = b * ((n : X) * S.t * (n : X)⁻¹) * b⁻¹ := by group
      _ = b * S.t * b⁻¹ * (b * A.Φ a * b⁻¹) := by rw [ha]; group
      _ = S.t * A.Φ (-(s + s)) * A.Φ a := by rw [hbt, hc, mul_inv_cancel_right]
      _ = S.t := by rw [mul_assoc, ← A.Φ_add, has, neg_add_cancel, A.Φ_zero, mul_one]
  have hmN : b * n ∈ A.NA := mul_mem (A.AA_le_NA (A.Φ_mem s)) n.2
  have hmap := A.map_E₁ ⟨b * n, hmN⟩ (a := 1) (by rw [mul_one]; exact hmt)
  rw [← A.E₁_eq_E0t] at hmap
  have hk := F.kF_fixed (b * n) ⟨GapFix.mem_normalizer_of_map hmap,
    mem_centralizer_singleton_iff.mpr (by
      calc b * n * S.t = (b * n) * S.t * (b * n)⁻¹ * (b * n) := by group
        _ = S.t * (b * n) := by rw [hmt])⟩
  have hbk : b * F.kF = F.kF * b := A.AA_comm (A.Φ_mem s) (A.Φ_k ▸ A.Φ_mem _)
  calc (n : X) * F.kF * (n : X)⁻¹ = b⁻¹ * ((b * n) * F.kF * (b * n)⁻¹) * b := by group
    _ = F.kF := by rw [hk, mul_assoc, ← hbk, ← mul_assoc, inv_mul_cancel, one_mul]

theorem kF_conj_iff (n : A.NA) :
    (n : X) * F.kF * (n : X)⁻¹ = F.kF ↔ redM (A.mat n) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
  rw [← A.Φ_k, A.conj_Φ]
  have hcol : ∀ (M : Matrix (Fin 3) (Fin 3) (ZMod 4)) i, (M *ᵥ ![0, 0, 2]) i = M i 2 * 2 := by
    intro M i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hcol' : ∀ (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) i, (M *ᵥ ![0, 0, 1]) i = M i 2 := by
    intro M i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have key : ∀ i, (A.mat n *ᵥ ![0, 0, 2]) i = ![0, 0, 2] i ↔
      (redM (A.mat n) *ᵥ ![0, 0, 1]) i = ![0, 0, 1] i := by
    intro i
    rw [hcol, hcol', show redM (A.mat n) i 2 = r2 (A.mat n i 2) from rfl]
    generalize A.mat n i 2 = m
    fin_cases i <;> revert m <;> decide
  constructor
  · intro h
    funext i
    exact (key i).mp (congrFun (A.Φ_injective h) i)
  · intro h
    congr 1
    funext i
    exact (key i).mpr (congrFun h i)

theorem conj_mem_Lt {n : X} (hn : n ∈ A.NA) {g : X} (hg : g ∈ A.Lt) : n * g * n⁻¹ ∈ A.Lt := by
  have hle : A.Lt ≤ A.Lt.comap (MulAut.conj n).toMonoidHom := by
    refine sup_le (fun c hc => ?_) (zpowers_le.mpr ?_)
    · exact mem_sup_left (A.conj_mem_C hn hc)
    · exact A.conj_t_mem_Lt ⟨n, hn⟩
  exact hle hg

theorem kF_fixed_of_mem_Lt {c : X} (hc : c ∈ A.Lt) : c * F.kF * c⁻¹ = F.kF :=
  (A.kF_conj_iff ⟨c, A.Lt_le_NA hc⟩).mpr (by rw [A.redM_of_mem_Lt hc, Matrix.one_mulVec])

theorem redM_mulVec_injective (n : A.NA) : Function.Injective (redM (A.mat n) *ᵥ ·) := by
  intro x y h
  have h1 : redM (A.mat n⁻¹) * redM (A.mat n) = 1 := by rw [← redM_mul, A.mat_inv_mul, redM_one]
  have := congrArg (redM (A.mat n⁻¹) *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this

theorem kF_fixed_of_conj_t (hnc : ¬ SubConj F.E₁ F.E₂) {m : A.NA} {a : Fin 3 → ZMod 4}
    (ha : (m : X) * S.t * (m : X)⁻¹ = S.t * A.Φ a) : (m : X) * F.kF * (m : X)⁻¹ = F.kF := by
  obtain ⟨δ, hδ, hz⟩ := A.exists_kappa
  rw [A.kF_conj_iff]
  refine GapFix.orbit A.Rl
    (fun M p => ∃ m : A.NA, ∃ a : Fin 3 → ZMod 4,
      (m : X) * S.t * (m : X)⁻¹ = S.t * A.Φ a ∧ redV a = p ∧ redM (A.mat m) = M)
    (A.kbar_cases hδ hz) A.Rl_zero (fun x hx => A.Rl_cases hnc hx) (fun x hx => A.Rl_K hδ hx)
    ?_ ?_ ?_ ?_ _ _ ⟨m, a, ha, rfl, rfl⟩
  · rintro M p ⟨m₁, a₁, h₁, rfl, rfl⟩ x hx
    exact A.Rl_aff hx m₁ h₁
  · rintro M p ⟨m₁, a₁, -, -, rfl⟩
    exact A.redM_mulVec_injective m₁
  · rintro x ⟨n, b, hb, rfl⟩
    exact ⟨_, n, b, hb, rfl, rfl⟩
  · rintro M ⟨m₁, a₁, h₁, h0, rfl⟩
    exact (A.kF_conj_iff m₁).mp (A.kF_fixed_of_redV h₁ h0)

end BData

namespace BData.Syl

variable {A : BData S F T₁} (Y : A.Syl)

theorem max_of_normal {K : Subgroup X} (hKN : K ≤ A.NA)
    (hK : ∀ n ∈ A.NA, ∀ g ∈ K, n * g * n⁻¹ ∈ K) {R : Subgroup X} (hR : IsPGroup 2 R)
    (hle : Y.P ⊓ K ≤ R) (hRK : R ≤ K) : R = Y.P ⊓ K := by
  obtain ⟨g, hg, hgR⟩ := GapNH.exists_conj_le_of_max Y.le_NA (hRK.trans hKN) Y.isPGroup hR
    Y.maximal
  have hmap : R.map (MulAut.conj g⁻¹).toMonoidHom ≤ Y.P ⊓ K := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hK _ (inv_mem hg) x (hRK hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [inv_inv] at h1 ⊢
    exact mem_inf.mpr ⟨hgR x hx, h1⟩
  have hcard : Nat.card R ≤ Nat.card (Y.P ⊓ K : Subgroup X) := by
    rw [← card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective]
    exact card_le_of_le hmap
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem exists_conj_normal {K : Subgroup X} (hKN : K ≤ A.NA)
    (hK : ∀ n ∈ A.NA, ∀ g ∈ K, n * g * n⁻¹ ∈ K) {n : X} (hn : n ∈ A.NA) :
    ∃ c ∈ K, ∀ x ∈ Y.P ⊓ K, c⁻¹ * (n * x * n⁻¹) * c ∈ Y.P ⊓ K := by
  have hP : IsPGroup 2 (Y.P ⊓ K : Subgroup X) := Y.isPGroup.to_le inf_le_left
  obtain ⟨c, hc, hcQ⟩ := exists_conj_of_max (K := K) (P := Y.P ⊓ K)
    (Q := (Y.P ⊓ K).map (MulAut.conj n).toMonoidHom) inf_le_right
    (by rintro _ ⟨g, hg, rfl⟩; exact hK n hn g (mem_inf.mp hg).2) hP (hP.map _)
    (fun R hR hle hRK => Y.max_of_normal hKN hK hR hle hRK)
    (card_map_of_injective (MulAut.conj n).injective)
  exact ⟨c, hc, fun x hx => (hcQ _).mp ⟨x, hx, by simp⟩⟩

theorem Q_le_Lt : Y.Q ≤ A.Lt := fun _ hq => mem_sup_left (mem_inf.mp hq).2

theorem t_mem_P_Lt : S.t ∈ Y.P ⊓ A.Lt := mem_inf.mpr ⟨Y.t_mem, mem_sup_right (mem_zpowers _)⟩

theorem conj_t_of_sq (hnc : ¬ SubConj F.E₁ F.E₂) {q : X} (hq : q ∈ Y.Q) (hq2 : q ^ 2 ∈ A.AA) :
    ∃ v, q * S.t * q⁻¹ = S.t * A.Φ v := by
  have ht' : S.t⁻¹ = S.t := by rw [inv_eq_iff_mul_eq_one, t_mul_t]
  have he := A.E0_le_AA (Y.psi_mem_E0 hnc hq)
  obtain ⟨v, hv⟩ := A.mem_AA.mp (mul_mem he (inv_mem hq2))
  refine ⟨v, ?_⟩
  rw [hv, pow_two]
  calc q * S.t * q⁻¹ = S.t * (S.t⁻¹ * q * S.t) * q⁻¹ := by group
    _ = S.t * (S.t * q * S.t⁻¹ * q * (q * q)⁻¹) := by rw [ht']; group

theorem pow_four_eq (hnc : ¬ SubConj F.E₁ F.E₂) {q : X} (hq : q ∈ Y.Q) (hqA : q ∉ A.AA)
    (hq2 : q ^ 2 ∈ A.AA) : q ^ 4 = F.kF := by
  obtain ⟨v, hv⟩ := Y.conj_t_of_sq hnc hq hq2
  exact (Y.pow_four hnc hq hqA hv).2

theorem exists_sq_mem {q : X} (hq : q ∈ Y.Q) (hqA : q ∉ A.AA) :
    ∃ r ∈ Y.Q, r ∉ A.AA ∧ r ^ 2 ∈ A.AA := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := Y.isPGroup ⟨q, (mem_inf.mp hq).1⟩
  have hex : ∃ j, q ^ 2 ^ j ∈ A.AA := ⟨m, by
    have := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [this]; exact one_mem _⟩
  set j := Nat.find hex with hj
  have hj0 : j ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [← hj, h, pow_zero, pow_one] at this
    exact hqA this
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨q ^ 2 ^ i, pow_mem hq _, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, show i + 1 = j by omega]
  exact Nat.find_spec hex

theorem kF_fixed_of_lt (hnc : ¬ SubConj F.E₁ F.E₂) {q : X} (hq : q ∈ Y.Q) (hqA : q ∉ A.AA)
    {n : X} (hn : n ∈ A.NA) : n * F.kF * n⁻¹ = F.kF := by
  obtain ⟨r, hr, hrA, hr2⟩ := Y.exists_sq_mem hq hqA
  obtain ⟨c, hc, hcP⟩ := Y.exists_conj_normal A.Lt_le_NA (fun n hn g hg => A.conj_mem_Lt hn hg) hn
  set m := c⁻¹ * n with hm
  have hmN : m ∈ A.NA := mul_mem (inv_mem (A.Lt_le_NA hc)) hn
  have hmr : m * r * m⁻¹ ∈ Y.Q := by
    have h1 := (mem_inf.mp (hcP r (mem_inf.mpr ⟨(mem_inf.mp hr).1, Y.Q_le_Lt hr⟩))).1
    rw [show c⁻¹ * (n * r * n⁻¹) * c = m * r * m⁻¹ by rw [hm]; group] at h1
    exact mem_inf.mpr ⟨h1, A.conj_mem_C hmN (mem_inf.mp hr).2⟩
  have hmrA : m * r * m⁻¹ ∉ A.AA := by
    intro h
    apply hrA
    have := A.conj_mem_AA (inv_mem hmN) h
    rwa [show m⁻¹ * (m * r * m⁻¹) * m⁻¹⁻¹ = r by group] at this
  have hconj : ∀ k : ℕ, (m * r * m⁻¹) ^ k = m * r ^ k * m⁻¹ := fun k => by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_pow]
  have hmr2 : (m * r * m⁻¹) ^ 2 ∈ A.AA := by rw [hconj]; exact A.conj_mem_AA hmN hr2
  have h4 := Y.pow_four_eq hnc hmr hmrA hmr2
  rw [hconj, Y.pow_four_eq hnc hr hrA hr2] at h4
  calc n * F.kF * n⁻¹ = c * (m * F.kF * m⁻¹) * c⁻¹ := by rw [hm]; group
    _ = F.kF := by rw [h4, A.kF_fixed_of_mem_Lt hc]

theorem kF_fixed_of_eq (hnc : ¬ SubConj F.E₁ F.E₂) (hQ : ∀ q ∈ Y.Q, q ∈ A.AA) {n : X}
    (hn : n ∈ A.NA) : n * F.kF * n⁻¹ = F.kF := by
  obtain ⟨c, hc, hcP⟩ := Y.exists_conj_normal A.Lt_le_NA (fun n hn g hg => A.conj_mem_Lt hn hg) hn
  set m := c⁻¹ * n with hm
  have hmN : m ∈ A.NA := mul_mem (inv_mem (A.Lt_le_NA hc)) hn
  have hmt : m * S.t * m⁻¹ ∈ Y.P := by
    have h1 := (mem_inf.mp (hcP S.t Y.t_mem_P_Lt)).1
    rwa [show c⁻¹ * (n * S.t * n⁻¹) * c = m * S.t * m⁻¹ by rw [hm]; group] at h1
  have hC : S.t⁻¹ * (m * S.t * m⁻¹) ∈ centralizer (A.AA : Set X) :=
    (A.mat_eq_one_iff ((⟨S.t, A.t_mem_NA⟩ : A.NA)⁻¹ * (⟨m, hmN⟩ * ⟨S.t, A.t_mem_NA⟩ *
      ⟨m, hmN⟩⁻¹))).mp (by rw [A.mat_mul, A.mat_t_inv, A.mat_conj_t, neg_one_mul, neg_neg])
  have hQm : S.t⁻¹ * (m * S.t * m⁻¹) ∈ Y.Q := mem_inf.mpr ⟨mul_mem (inv_mem Y.t_mem) hmt, hC⟩
  obtain ⟨a, ha⟩ := A.mem_AA.mp (hQ _ hQm)
  have hk := A.kF_fixed_of_conj_t hnc (m := ⟨m, hmN⟩) (a := a) (by
    change m * S.t * m⁻¹ = S.t * A.Φ a
    rw [ha]; group)
  calc n * F.kF * n⁻¹ = c * (m * F.kF * m⁻¹) * c⁻¹ := by rw [hm]; group
    _ = F.kF := by rw [hk, A.kF_fixed_of_mem_Lt hc]

end BData.Syl

namespace BData

variable (A : BData S F T₁)

theorem kF_fixed (hnc : ¬ SubConj F.E₁ F.E₂) {n : X} (hn : n ∈ A.NA) :
    n * F.kF * n⁻¹ = F.kF := by
  obtain ⟨Y⟩ := A.exists_syl
  by_cases hQ : ∀ q ∈ Y.Q, q ∈ A.AA
  · exact Y.kF_fixed_of_eq hnc hQ hn
  · push Not at hQ
    obtain ⟨q, hq, hqA⟩ := hQ
    exact Y.kF_fixed_of_lt hnc hq hqA hn

theorem mulVec_c (hnc : ¬ SubConj F.E₁ F.E₂) (n : A.NA) :
    redM (A.mat n) *ᵥ ![0, 0, 1] = ![0, 0, 1] :=
  (A.kF_conj_iff n).mp (A.kF_fixed hnc n.2)

end BData

end Sec8

end CFSG.ComponentClassification.HSFLit
