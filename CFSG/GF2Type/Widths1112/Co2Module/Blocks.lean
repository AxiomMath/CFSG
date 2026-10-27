module

public import CFSG.GF2Type.Widths1112.Co2Module.Idempotents
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

public section

namespace CFSG.GF2Type.Widths1112.Co2Module

open Finset

theorem finiteDimensional_of_finrank_eq_22 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 22) : FiniteDimensional (ZMod 2) V :=
  Module.finite_of_finrank_pos (by omega)

section Counting

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) Γ V) (ι : AddChar F3Vec Γ)

theorem piH_zero : piH ρ ι 0 = piE ρ ι := by
  rw [piH_def, piE_def, hyp_zero]

theorem finrank_range_piE_lt [FiniteDimensional (ZMod 2) V] (hnt : ∃ v, ρ (ι v) ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (piE ρ ι)) < Module.finrank (ZMod 2) V := by
  refine lt_of_le_of_ne (Submodule.finrank_le _) fun h => ?_
  have htop : LinearMap.range (piE ρ ι) = ⊤ := Submodule.eq_top_of_finrank_eq h
  obtain ⟨v, hv⟩ := hnt
  apply hv
  ext x
  have hx : x ∈ LinearMap.range (piH ρ ι 0) := by rw [piH_zero, htop]; trivial
  rw [range_piH] at hx
  simpa using hx v (zero_dotProduct v)

theorem counting_arith22 {c a b : ℕ} (ha : Even a) (hb : Even b) (hb0 : b ≠ 0)
    (h : c + 30 * a + 10 * b = 22) : c = 2 ∧ a = 0 ∧ b = 2 := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  omega

theorem finrank_piE_and_eK22 [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 22) {R : Finset F3Vec} (hR : IsLineReps R)
    (cls : F3Vec → Fin 2) (h0 : (R.filter fun w => cls w = 0).card = 30)
    (h1 : (R.filter fun w => cls w = 1).card = 10)
    (hconst : ∀ w ∈ R, ∀ w' ∈ R, cls w = cls w' →
      Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
        Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w')))
    (hnt : ∃ v, ρ (ι v) ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (piE ρ ι)) = 2 ∧
      ∀ w ∈ R, Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
        if cls w = 1 then 2 else 0 := by
  obtain ⟨d, hd⟩ : ∃ d : F3Vec → ℕ, ∀ w : F3Vec,
      d w = Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) :=
    ⟨fun w => Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)), fun _ => rfl⟩
  have heven : ∀ w ∈ R, Even (d w) := fun w hw => by
    obtain ⟨v₀, hv₀⟩ := exists_dot_ne_zero (hR.ne_zero w hw)
    rw [hd w]
    exact even_finrank_range_eK ρ ι hv₀
  have hval : ∀ w ∈ R, ∀ (k : Fin 2) (w' : F3Vec), w' ∈ R → cls w' = k → cls w = k →
      d w = d w' :=
    fun w hw k w' hw' hk' hk => by
      rw [hd w, hd w']
      exact hconst w hw w' hw' (hk.trans hk'.symm)
  have hex : ∀ k : Fin 2, (R.filter fun w => cls w = k).card ≠ 0 → ∃ w ∈ R, cls w = k :=
    fun k hk => by
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hk)
      exact ⟨w, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩
  obtain ⟨w0, hw0R, hw0c⟩ := hex 0 (by omega)
  obtain ⟨w1, hw1R, hw1c⟩ := hex 1 (by omega)
  have hsplit : ∑ w ∈ R, d w = 30 * d w0 + 10 * d w1 := by
    rw [← Finset.sum_fiberwise R cls d, Fin.sum_univ_two]
    have hk : ∀ (k : Fin 2) (w' : F3Vec), w' ∈ R → cls w' = k →
        ∑ w ∈ R.filter (fun w => cls w = k), d w = (R.filter fun w => cls w = k).card * d w' := by
      intro k w' hw' hk'
      rw [Finset.sum_congr rfl (g := fun _ => d w')
        (fun w hw => hval w (Finset.mem_filter.mp hw).1 k w' hw' hk' (Finset.mem_filter.mp hw).2),
        Finset.sum_const, smul_eq_mul]
    rw [hk 0 w0 hw0R hw0c, hk 1 w1 hw1R hw1c, h0, h1]
  have hdec : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (LinearMap.range (piE ρ ι)) + ∑ w ∈ R, d w := by
    rw [finrank_eq_finrank_range_piE_add_sum ρ ι hR]
    simp only [hd]
  have hlt := finrank_range_piE_lt ρ ι hnt
  rw [hV] at hlt
  rw [hV, hsplit] at hdec
  have hb0 : d w1 ≠ 0 := by
    intro hb
    obtain ⟨a', ha'⟩ := heven w0 hw0R
    omega
  obtain ⟨hc2, ha0, hb2⟩ := counting_arith22
    (c := Module.finrank (ZMod 2) (LinearMap.range (piE ρ ι)))
    (heven w0 hw0R) (heven w1 hw1R) hb0 (by omega)
  refine ⟨hc2, fun w hw => ?_⟩
  have hcls : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  rw [← hd w]
  rcases hcls (cls w) with hk | hk
  · have hne : ¬ (cls w = 1) := by
      rw [hk]
      decide
    rw [if_neg hne, hval w hw 0 w0 hw0R hw0c hk, ha0]
  · rw [if_pos hk, hval w hw 1 w1 hw1R hw1c hk, hb2]

end Counting

section Basis

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Γ V) (ι : AddChar F3Vec Γ)

theorem exists_coeffs_of_mem_range_eK {w₁ v₀ : F3Vec}
    (hdim : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w₁)) = 2) (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0)
    {x : V} (hx : x ∈ LinearMap.range (eK ρ ι w₁)) (hx0 : x ≠ 0) {y : V}
    (hy : y ∈ LinearMap.range (eK ρ ι w₁)) :
    ∃ a b : ZMod 2, y = a • x + b • ρ (ι v₀) x := by
  have hTx : ρ (ι v₀) x ∈ LinearMap.range (eK ρ ι w₁) := apply_mem_range_eK ρ ι w₁ v₀ hx
  let bx : LinearMap.range (eK ρ ι w₁) := ⟨x, hx⟩
  let bTx : LinearMap.range (eK ρ ι w₁) := ⟨ρ (ι v₀) x, hTx⟩
  have hbx0 : bx ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hli : LinearIndependent (ZMod 2) ![bx, bTx] := by
    rw [LinearIndependent.pair_iff' hbx0]
    intro a ha
    have ha' : a • x = ρ (ι v₀) x := congrArg Subtype.val ha
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hcases a with rfl | rfl
    · rw [zero_smul] at ha'
      have h3 := apply_cube ρ ι v₀ x
      rw [← ha', map_zero, map_zero] at h3
      exact hx0 h3.symm
    · rw [one_smul] at ha'
      exact hx0 (eq_zero_of_apply_eq_self ρ ι hv₀ hx ha'.symm)
  have hcard : Fintype.card (Fin 2) = Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w₁)) := by
    simp [hdim]
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hy' : (⟨y, hy⟩ : LinearMap.range (eK ρ ι w₁)) ∈
      Submodule.span (ZMod 2) (Set.range ![bx, bTx]) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hy'
  refine ⟨c 0, c 1, ?_⟩
  have := congrArg Subtype.val hc
  simpa [Fin.sum_univ_two, bx, bTx] using this.symm

theorem sum_eK_add_piE_of_zero {R : Finset F3Vec} (hR : IsLineReps R) {S : Finset F3Vec}
    (hS : S ⊆ R) (hzero : ∀ w ∈ R, w ∉ S → eK ρ ι w = 0) :
    ∑ w ∈ S, eK ρ ι w + piE ρ ι = 1 := by
  have h := sum_eK_add_piE ρ ι hR
  rw [Finset.sum_subset hS hzero]
  exact h

theorem exists_basis_of_blocks22 (hV : Module.finrank (ZMod 2) V = 22) {R : Finset F3Vec}
    (hR : IsLineReps R) (w : Fin 10 → F3Vec) (hinj : Function.Injective w)
    (hwR : ∀ i, w i ∈ R) (hzero : ∀ w' ∈ R, (∀ i, w i ≠ w') → eK ρ ι w' = 0)
    {w₁ v₀ : F3Vec} (hdim : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w₁)) = 2)
    (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {x : V} (hx : x ∈ LinearMap.range (eK ρ ι w₁)) (hx0 : x ≠ 0)
    (r : Fin 10 → Γ) (A : Fin 10 → Matrix (Fin 4) (Fin 4) (ZMod 3)) (c : Fin 10 → ZMod 3)
    (hr : ∀ i, ConjAct ι (r i) (A i)) (hc : ∀ i, c i ≠ 0)
    (hwA : ∀ i, Matrix.vecMul (w i) (A i) = c i • w₁)
    (v0 : Module.Basis (Fin 2) (ZMod 2) (LinearMap.range (piE ρ ι))) :
    ∃ b : Module.Basis (Fin 2 ⊕ (Fin 10 × Fin 2)) (ZMod 2) V,
      (∀ a, b (Sum.inl a) = ((v0 a : LinearMap.range (piE ρ ι)) : V)) ∧
      ∀ i j, b (Sum.inr (i, j)) = ρ (r i) ((ρ (ι v₀) ^ (j : ℕ)) x) := by
  classical
  have hsum : ∑ i, eK ρ ι (w i) + piE ρ ι = 1 := by
    have h := sum_eK_add_piE_of_zero ρ ι hR (S := Finset.univ.image w)
      (fun w' hw' => by
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw'
        exact hwR i)
      (fun w' hw'R hw'S =>
        hzero w' hw'R fun i hi => hw'S (Finset.mem_image.mpr ⟨i, mem_univ _, hi⟩))
    rwa [Finset.sum_image (fun i _ j _ hij => hinj hij)] at h
  let bfam : Fin 2 ⊕ (Fin 10 × Fin 2) → V := Sum.elim
    (fun a => ((v0 a : LinearMap.range (piE ρ ι)) : V))
    (fun p => ρ (r p.1) ((ρ (ι v₀) ^ (p.2 : ℕ)) x))
  have hrange : ∀ y : LinearMap.range (piE ρ ι),
      (y : V) ∈ Submodule.span (ZMod 2) (Set.range bfam) := by
    intro y
    have hy := congrArg Subtype.val (v0.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hy
    rw [← hy]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl a, by simp [bfam]⟩)
  have hkey : ∀ i, ∀ v : V, eK ρ ι (w i) v ∈ Submodule.span (ZMod 2) (Set.range bfam) := by
    intro i v
    have hmem : eK ρ ι (w i) v ∈ LinearMap.range (eK ρ ι (w i)) := ⟨v, rfl⟩
    rw [range_eK_eq_map ρ (hr i) (hc i) (hwA i)] at hmem
    obtain ⟨y, hy, hyv⟩ := hmem
    obtain ⟨a, b, rfl⟩ := exists_coeffs_of_mem_range_eK ρ ι hdim hv₀ hx hx0 hy
    rw [← hyv, map_add, map_smul, map_smul]
    refine Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (i, 0), ?_⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (i, 1), ?_⟩))
    · simp [bfam]
    · simp [bfam]
  have hspan : ⊤ ≤ Submodule.span (ZMod 2) (Set.range bfam) := by
    intro v _
    have hv : v = piE ρ ι v + ∑ i, eK ρ ι (w i) v := by
      have h := LinearMap.congr_fun hsum v
      simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.one_apply] at h
      rw [add_comm]
      exact h.symm
    rw [hv]
    exact Submodule.add_mem _ (hrange ⟨piE ρ ι v, v, rfl⟩)
      (Submodule.sum_mem _ fun i _ => hkey i v)
  have hcard : Fintype.card (Fin 2 ⊕ (Fin 10 × Fin 2)) = Module.finrank (ZMod 2) V := by
    simp [hV]
  refine ⟨basisOfTopLeSpanOfCardEqFinrank bfam hspan hcard, fun a => ?_, fun i j => ?_⟩
  · simp [bfam]
  · simp [bfam]

theorem eK_eq_zero_of_finrank_eq_zero {w : F3Vec}
    (h : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) = 0) : eK ρ ι w = 0 :=
  LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)

theorem exists_basis_of_orbits22 (hV : Module.finrank (ZMod 2) V = 22)
    {R : Finset F3Vec} (hR : IsLineReps R) (cls : F3Vec → Fin 2)
    (h0 : (R.filter fun w => cls w = 0).card = 30)
    (h1 : (R.filter fun w => cls w = 1).card = 10)
    (hconst : ∀ w ∈ R, ∀ w' ∈ R, cls w = cls w' →
      Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
        Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w')))
    (hnt : ∃ v, ρ (ι v) ≠ 1) (w : Fin 10 → F3Vec) (hinj : Function.Injective w)
    (hwR : ∀ i, w i ∈ R) (hwcls : ∀ i, cls (w i) = 1) {w₁ v₀ : F3Vec} (hw₁R : w₁ ∈ R)
    (hw₁cls : cls w₁ = 1) (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {x : V} (hx : x ∈ LinearMap.range (eK ρ ι w₁))
    (hx0 : x ≠ 0) (r : Fin 10 → Γ) (A : Fin 10 → Matrix (Fin 4) (Fin 4) (ZMod 3))
    (c : Fin 10 → ZMod 3) (hr : ∀ i, ConjAct ι (r i) (A i)) (hc : ∀ i, c i ≠ 0)
    (hwA : ∀ i, Matrix.vecMul (w i) (A i) = c i • w₁)
    (v0 : Module.Basis (Fin 2) (ZMod 2) (LinearMap.range (piE ρ ι))) :
    ∃ b : Module.Basis (Fin 2 ⊕ (Fin 10 × Fin 2)) (ZMod 2) V,
      (∀ a, b (Sum.inl a) = ((v0 a : LinearMap.range (piE ρ ι)) : V)) ∧
      ∀ i j, b (Sum.inr (i, j)) = ρ (r i) ((ρ (ι v₀) ^ (j : ℕ)) x) := by
  classical
  obtain ⟨_, hd⟩ := finrank_piE_and_eK22 ρ ι hV hR cls h0 h1 hconst hnt
  have himg : Finset.univ.image w ⊆ R.filter (fun w' => cls w' = 1) := by
    intro w' hw'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw'
    exact Finset.mem_filter.mpr ⟨hwR i, hwcls i⟩
  have hcardimg : (Finset.univ.image w).card = 10 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have heq : Finset.univ.image w = R.filter (fun w' => cls w' = 1) :=
    Finset.eq_of_subset_of_card_le himg (by rw [h1, hcardimg])
  have hzero : ∀ w' ∈ R, (∀ i, w i ≠ w') → eK ρ ι w' = 0 := by
    intro w' hw'R hw'
    apply eK_eq_zero_of_finrank_eq_zero
    rw [hd w' hw'R]
    have hne : cls w' ≠ 1 := fun hc1 => by
      have hmem : w' ∈ Finset.univ.image w := by
        rw [heq]
        exact Finset.mem_filter.mpr ⟨hw'R, hc1⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      exact hw' i hi
    simp [hne]
  have hdimw₁ : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w₁)) = 2 := by
    rw [hd w₁ hw₁R, if_pos hw₁cls]
  exact exists_basis_of_blocks22 ρ ι hV hR w hinj hwR hzero hdimw₁ hv₀ hx hx0 r A c hr hc hwA v0

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_fixed_mem_range_eK {g : Γ} {A : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (h : ConjAct ι g A) (hg2 : g * g = 1) {w : F3Vec} {c : ZMod 3} (hc : c ≠ 0)
    (hw : Matrix.vecMul w A = c • w) (hne : LinearMap.range (eK ρ ι w) ≠ ⊥) :
    ∃ x ∈ LinearMap.range (eK ρ ι w), x ≠ 0 ∧ ρ g x = x := by
  have hinv : ∀ y ∈ LinearMap.range (eK ρ ι w), ρ g y ∈ LinearMap.range (eK ρ ι w) := by
    intro y hy
    have := range_eK_eq_map ρ h hc hw
    rw [this]
    exact Submodule.mem_map_of_mem hy
  have hT2 : ∀ y : V, ρ g (ρ g y) = y := fun y => by
    have : ρ g * ρ g = 1 := by rw [← map_mul, hg2, map_one]
    simpa using LinearMap.congr_fun this y
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  by_cases hx : y + ρ g y = 0
  · refine ⟨y, hy, hy0, ?_⟩
    have h2 := add_self_eq_zero_of_zmod2 y
    exact add_left_cancel (hx.trans h2.symm)
  · refine ⟨y + ρ g y, Submodule.add_mem _ hy (hinv y hy), hx, ?_⟩
    rw [map_add, hT2, add_comm]

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_sq_of_mem_range_eK {w v₀ : F3Vec} (hv₀ : w ⬝ᵥ v₀ ≠ 0) {y : V}
    (hy : y ∈ LinearMap.range (eK ρ ι w)) :
    ρ (ι v₀) (ρ (ι v₀) y) = y + ρ (ι v₀) y := by
  have h := one_add_apply_eq_zero ρ ι hv₀ hy
  have h2 := add_self_eq_zero_of_zmod2 (y + ρ (ι v₀) y)
  exact add_left_cancel (h.trans h2.symm)

end Basis

end CFSG.GF2Type.Widths1112.Co2Module
