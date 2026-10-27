module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankB

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary Matrix
open CFSG.LieType.Universal.Unitary (SUid)

section Bounds

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem exists_fix_of_invariant {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hFev : Even (Nat.card F)) (T : Submodule F (Fin 4 → F))
    (hT : ∀ a ∈ E, ∀ y ∈ T, a • y ∈ T) (hT0 : T ≠ ⊥) :
    ∃ y ∈ T, y ≠ 0 ∧ y ∈ fixSp E := by
  have hP : IsPGroup 2 ↥E := fun a => ⟨1, Subtype.ext (by simpa [pow_two] using hE2 a.1 a.2)⟩
  letI : MulAction ↥E ↥T :=
    { smul := fun a y => ⟨(a : SUid σ 4) • (y : Fin 4 → F), hT a a.2 y y.2⟩
      one_smul := fun y => Subtype.ext (one_smul _ _)
      mul_smul := fun a b y => Subtype.ext (mul_smul (a : SUid σ 4) (b : SUid σ 4) _) }
  have hev : Even (Nat.card ↥T) := by
    haveI : Nontrivial ↥T := Submodule.nontrivial_iff_ne_bot.mpr hT0
    have hpos : 0 < Module.finrank F ↥T := Module.finrank_pos
    rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥T)]
    exact Nat.even_pow.mpr ⟨hFev, by omega⟩
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_fixed hP hev (MulAction.toPermHom ↥E ↥T)
    (fun a => Subtype.ext (smul_zero (a : SUid σ 4)))
  refine ⟨y, y.2, fun h => hy0 (Subtype.ext h), mem_fixSp.mpr fun a ha => ?_⟩
  exact congrArg Subtype.val (hy ⟨a, ha⟩)

theorem orbit_span_eq_top (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) (hFev : Even (Nat.card F)) (t : Fin 4 → F)
    (ht : Submodule.span F {t} ⊔ commSp E = ⊤) :
    Submodule.span F {y | ∃ a ∈ E, y = a • t} = ⊤ := by
  set W' := Submodule.span F {y | ∃ a ∈ E, y = a • t} with hW'
  by_contra hne
  have htW : t ∈ W' := Submodule.subset_span ⟨1, E.one_mem, (one_smul _ _).symm⟩
  have hWinv : ∀ a ∈ E, ∀ y ∈ W', a • y ∈ W' := by
    intro a ha y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, rfl⟩ := hz
      exact Submodule.subset_span ⟨a * b, E.mul_mem ha hb, (mul_smul _ _ _).symm⟩
    | zero => rw [smul_zero]; exact W'.zero_mem
    | add y y' _ _ h1 h2 => rw [smul_add]; exact W'.add_mem h1 h2
    | smul c y _ h1 => rw [smul_comm]; exact W'.smul_mem c h1
  have hTne : horth σ W' ≠ ⊥ := by
    intro h
    have hcard := card_mul_card_horth hσ W'
    have e1 : Nat.card ↥W' = Nat.card F ^ Module.finrank F ↥W' := Module.natCard_eq_pow_finrank
    have e2 : Nat.card (Fin 4 → F) = Nat.card F ^ Module.finrank F (Fin 4 → F) :=
      Module.natCard_eq_pow_finrank
    have e3 : Nat.card ↥(horth σ W') = Nat.card F ^ Module.finrank F ↥(horth σ W') :=
      Module.natCard_eq_pow_finrank
    have e3' : Nat.card ↥(horth σ W') = 1 := by rw [e3, h, finrank_bot, pow_zero]
    rw [e1, e3', e2, mul_one] at hcard
    have hF : 1 < Nat.card F := Finite.one_lt_card
    have := Nat.pow_right_injective hF hcard
    exact hne (Submodule.eq_top_of_finrank_eq this)
  have hTinv : ∀ a ∈ E, ∀ y ∈ horth σ W', a • y ∈ horth σ W' := by
    intro a ha y hy
    refine mem_horth.mpr fun w hw => ?_
    have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hE2 a ha)
    have h2 : herm σ w (a • y) = herm σ (a • w) y := by
      have := herm_inv_smul_left a w y
      rw [h1] at this
      exact this.symm
    rw [h2]
    exact mem_horth.mp hy _ (hWinv a ha w hw)
  obtain ⟨y, hyT, hy0, hyfix⟩ := exists_fix_of_invariant hE2 hFev _ hTinv hTne
  apply hy0
  apply eq_zero_of_herm σ
  intro w
  rw [herm_conj σ hσ.invol w y]
  have hw : w ∈ Submodule.span F {t} ⊔ commSp E := by rw [ht]; trivial
  obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  rw [herm_add_left, herm_smul_left, mem_horth.mp hyT t htW, mul_zero, zero_add]
  have hyh : y ∈ horth σ (commSp E) := by
    rw [← fixSp_eq_horth hσ hE2]; exact hyfix
  rw [mem_horth.mp hyh u hu, map_zero]

theorem JJ_eq_zero_of_orbit {E : Subgroup (SUid σ 4)} (t : Fin 4 → F)
    (ht : Submodule.span F {y | ∃ a ∈ E, y = a • t} = ⊤) {g : Module.End F (Fin 4 → F)}
    (hg : g ∈ JJ E) (h0 : g t = 0) : g = 0 := by
  have h1 : ∀ s ∈ Submodule.span F {y | ∃ a ∈ E, y = a • t}, g s = 0 := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hg.2.2 a ha t, h0, smul_zero]
    | zero => exact map_zero g
    | add y y' _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
    | smul c y _ h1 => rw [map_smul, h1, smul_zero]
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ Submodule.span F {y | ∃ a ∈ E, y = a • t} := by rw [ht]; trivial
  rw [h1 x hx]
  rfl

instance : Finite (Module.End F (Fin 4 → F)) :=
  Finite.of_injective (fun f : Module.End F (Fin 4 → F) => (f : (Fin 4 → F) → (Fin 4 → F)))
    DFunLike.coe_injective

theorem card_sq_le_general (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    Nat.card ↥E * Nat.card ↥E ≤
      Nat.card ↥(commSp E) ^ Module.finrank F ((Fin 4 → F) ⧸ fixSp E) := by
  obtain ⟨ω, hω⟩ := hσ.exists_ne
  obtain ⟨t, ht⟩ := exists_family (fixSp E)
  have h := card_sq_le_of_separating hω hσ.invol t (commSp E) (SS E) (fun f hf => hf.2)
    (fun f hf i => hf.1.1 _) (fun f₁ hf₁ f₂ hf₂ h0 =>
      JJ_eq_zero_of_family t ht (add_mem hf₁.1 (Submodule.smul_mem _ ω hf₂.1)) h0)
  exact (Nat.mul_le_mul (card_le_card_SS hE2 hEc) (card_le_card_SS hE2 hEc)).trans h

theorem card_sq_le_of_finrank_eq_three (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hFev : Even (Nat.card F)) (h3 : Module.finrank F ↥(commSp E) = 3) :
    Nat.card ↥E * Nat.card ↥E ≤ Nat.card ↥(commSp E) := by
  obtain ⟨ω, hω⟩ := hσ.exists_ne
  have hne : commSp E ≠ ⊤ := by
    intro h
    have : Module.finrank F ↥(commSp E) = 4 := by
      rw [h, finrank_top, Module.finrank_fin_fun]
    omega
  obtain ⟨t, htmem⟩ : ∃ t, t ∉ commSp E := by
    by_contra h
    push_neg at h
    exact hne (eq_top_iff.mpr fun x _ => h x)
  have hsup : Submodule.span F {t} ⊔ commSp E = ⊤ := by
    have hlt : commSp E < Submodule.span F {t} ⊔ commSp E := by
      refine lt_of_le_of_ne le_sup_right fun h => htmem ?_
      rw [h]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self t)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_le (Submodule.span F {t} ⊔ commSp E)
    rw [Module.finrank_fin_fun] at h2
    exact Submodule.eq_top_of_finrank_eq (by simp only [Module.finrank_fin_fun]; omega)
  have horb := orbit_span_eq_top hσ hE2 hFev t hsup
  have h := card_sq_le_of_separating (r := 1) hω hσ.invol (fun _ => t) (commSp E) (SS E)
    (fun f hf => hf.2) (fun f hf i => hf.1.1 _) (fun f₁ hf₁ f₂ hf₂ h0 =>
      JJ_eq_zero_of_orbit t horb (add_mem hf₁.1 (Submodule.smul_mem _ ω hf₂.1)) (h0 0))
  simpa only [pow_one] using
    (Nat.mul_le_mul (card_le_card_SS hE2 hEc) (card_le_card_SS hE2 hEc)).trans h

theorem card_cases (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    (Module.finrank F ↥(commSp E) = 0 ∧ Nat.card ↥E ≤ 1) ∨
    (Module.finrank F ↥(commSp E) = 1 ∧ Nat.card ↥E ≤ 2 ^ n) ∨
    (Module.finrank F ↥(commSp E) = 2 ∧ Nat.card ↥E ≤ 2 ^ (4 * n)) ∨
    (Module.finrank F ↥(commSp E) = 3 ∧ Nat.card ↥E ≤ 2 ^ (3 * n)) := by
  have hFev : Even (Nat.card F) := by
    rw [hF]
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
  have hev4 : Even (Nat.card (Fin 4 → F)) := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.even_pow.mpr ⟨hFev, by norm_num⟩
  obtain ⟨x, hxfix, hx0⟩ := exists_ne_zero_mem_fixSp hE2 hev4
  have hk : 1 ≤ Module.finrank F ↥(fixSp E) := by
    have : Nontrivial ↥(fixSp E) := ⟨⟨⟨x, hxfix⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  have hsum := finrank_commSp_add_finrank_fixSp hσ hE2
  have hr : Module.finrank F ((Fin 4 → F) ⧸ fixSp E) = Module.finrank F ↥(commSp E) := by
    have := Submodule.finrank_quotient_add_finrank (fixSp E)
    rw [Module.finrank_fin_fun] at this
    omega
  have hcard : Nat.card ↥(commSp E) = Nat.card F ^ Module.finrank F ↥(commSp E) :=
    Module.natCard_eq_pow_finrank
  have hu3 : Module.finrank F ↥(commSp E) ≤ 3 := by omega
  have hsq : ∀ a b : ℕ, a * a ≤ b * b → a ≤ b := fun a b h => Nat.mul_self_le_mul_self_iff.mp h
  have hgen := card_sq_le_general hσ hE2 hEc
  rw [hr, hcard] at hgen
  interval_cases hu : Module.finrank F ↥(commSp E)
  · left
    refine ⟨rfl, ?_⟩
    simpa using hgen
  · right; left
    refine ⟨rfl, hsq _ _ ?_⟩
    rw [hF] at hgen
    calc Nat.card ↥E * Nat.card ↥E ≤ ((2 ^ n) ^ 2) ^ 1 ^ 1 := by simpa using hgen
      _ = 2 ^ n * 2 ^ n := by ring
  · right; right; left
    refine ⟨rfl, hsq _ _ ?_⟩
    rw [hF] at hgen
    calc Nat.card ↥E * Nat.card ↥E ≤ (((2 ^ n) ^ 2) ^ 2) ^ 2 := hgen
      _ = 2 ^ (4 * n) * 2 ^ (4 * n) := by ring
  · right; right; right
    refine ⟨rfl, hsq _ _ ?_⟩
    have h3 := card_sq_le_of_finrank_eq_three hσ hE2 hEc hFev hu
    rw [hcard, hF] at h3
    calc Nat.card ↥E * Nat.card ↥E ≤ ((2 ^ n) ^ 2) ^ 3 := h3
      _ = 2 ^ (3 * n) * 2 ^ (3 * n) := by ring

end Bounds

end CFSG.LocalAnalysis.RankThreeUC
