
module

public import Certificates.Data.Kernel.L34Mod
public import CFSG.Quasithin.Recognition.L34AmalgamIsoGLBase

public section

namespace CFSG.KC.L34Mod

open CFSG.Quasithin.L34Amalgam

theorem eq_lin_of_additive (f : Fin 16 → Fin 16) (hf : ∀ x y, f (bxor x y) = bxor (f x) (f y))
    (x : Fin 16) : f x = lin (fun i => f (basisVec i)) x := by
  have h0 : f 0 = 0 := by
    have h := hf 0 0
    rw [bxor_self] at h
    rw [h]
    exact bxor_self _
  have hs : ∀ (b : Bool) (m : Fin 16), f (sel b m) = sel b (f m) := by
    intro b m
    cases b <;> simp [sel, h0]
  conv_lhs => rw [← eq_lin_basis x]
  simp only [lin, hf, hs]
  rfl

theorem lin_injective_of_ne_zero {m : Fin 4 → Fin 16} (h : ∀ x, x ≠ 0 → lin m x ≠ 0) :
    Function.Injective (lin m) := by
  intro x y hxy
  by_contra hne
  have h0 : bxor x y ≠ 0 := by
    intro h'
    apply hne
    have := congrArg (bxor · y) h'
    simp only [bxor_assoc, bxor_self, bxor_zero, zero_bxor] at this
    exact this
  apply h _ h0
  rw [lin_bxor, hxy, bxor_self]

theorem lin_comm_of_basis {T A B : Fin 4 → Fin 16} (h : ∀ i, lin T (A i) = lin B (T i))
    (x : Fin 16) : lin T (lin A x) = lin B (lin T x) := by
  rw [lin_comp, lin_comp B]
  congr 1
  funext i
  exact h i

theorem exists_conj_of_s1 (h1 : ∀ t, t < 65536 → s1 t = true) (v : Fin 4 → Fin 16)
    (hv : ∀ x, lin v (lin v (lin v x)) = x) (hfpf : ∀ x, x ≠ 0 → lin v x ≠ x) :
    ∃ g : Fin 4 → Fin 16, Function.Injective (lin g) ∧
      ∀ x, lin g (lin refB x) = lin v (lin g x) := by
  have h := h1 (toCode v) (toCode_lt v)
  have ho : ord3B v = true := by
    simp [ord3B, hv]
  have hf : fpfB v = true := by
    simp only [fpfB, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq]
    intro x
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr (hfpf x hx)
  simp only [s1, ofCode_toCode, ho, hf, Bool.and_self, Bool.not_true, Bool.false_or,
    List.any_eq_true, List.mem_finRange, true_and] at h
  obtain ⟨b, hb⟩ := h
  simp only [conjB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hb
  obtain ⟨hinj, hc⟩ := hb
  exact ⟨gOf v b, lin_injective_of_ne_zero fun x hx => (hinj x).resolve_left hx,
    lin_comm_of_basis hc⟩

theorem checkPair_of_s2 (h2 : ∀ t, t < 65536 → s2 t = true) (u : Fin 4 → Fin 16)
    (hu : ∀ x, lin u (lin u x) = x) : checkPair u refB = true := by
  have h := h2 (toCode u) (toCode_lt u)
  have hi : invB u = true := by
    simp [invB, hu]
  simpa only [s2, ofCode_toCode, hi, Bool.not_true, Bool.false_or] using h

theorem module_unique_of_scans (h1 : ∀ t, t < 65536 → s1 t = true)
    (h2 : ∀ t, t < 65536 → s2 t = true) (u : Fin 4 → Fin 16)
    (hu : ∀ x, lin u (lin u x) = x)
    (v : Fin 4 → Fin 16) (hv : ∀ x, lin v (lin v (lin v x)) = x)
    (hfpf : ∀ x, x ≠ 0 → lin v x ≠ x) (h5 : ∀ x, (lin u ∘ lin v)^[5] x = x) :
    ∃ w : Fin 16, (∀ x y, lin (conjMap u v w) x = lin (conjMap u v w) y → x = y) ∧
      (∀ x, lin (conjMap u v w) (lin refA x) = lin u (lin (conjMap u v w) x)) ∧
      ∀ x, lin (conjMap u v w) (lin refB x) = lin v (lin (conjMap u v w) x) := by
  obtain ⟨g, hg, hgB⟩ := exists_conj_of_s1 h1 v hv hfpf
  have hsurj : Function.Surjective (lin g) := Finite.surjective_of_injective hg
  obtain ⟨e, he⟩ : ∃ e : Fin 16 → Fin 16, ∀ x, lin g (e x) = x :=
    ⟨Function.surjInv hsurj, Function.surjInv_eq hsurj⟩
  have hadd : ∀ x y, e (lin u (lin g (bxor x y))) =
      bxor (e (lin u (lin g x))) (e (lin u (lin g y))) := by
    intro x y
    apply hg
    rw [he, lin_bxor g, lin_bxor g, he, he, lin_bxor u]
  obtain ⟨u', hu'⟩ : ∃ u' : Fin 4 → Fin 16, ∀ x, lin u' x = e (lin u (lin g x)) :=
    ⟨_, fun x => (eq_lin_of_additive _ hadd x).symm⟩
  have hgu : ∀ x, lin g (lin u' x) = lin u (lin g x) := by
    intro x
    rw [hu', he]
  have hu2 : ∀ x, lin u' (lin u' x) = x := by
    intro x
    apply hg
    rw [hgu, hgu, hu]
  have hsc : Function.Semiconj (lin g) (lin u' ∘ lin refB) (lin u ∘ lin v) := by
    intro x
    simp only [Function.comp_apply]
    rw [hgu, hgB]
  have h5' : ∀ x, (lin u' ∘ lin refB)^[5] x = x := by
    intro x
    apply hg
    rw [hsc.iterate_right 5 x, h5]
  obtain ⟨w', hinj, hA, hB⟩ := exists_of_checkPair (checkPair_of_s2 h2 u' hu2) fun i => h5' _
  have hcol : conjMap u v (lin g w') = fun i => lin g (conjMap u' refB w' i) := by
    funext i
    fin_cases i <;> simp [conjMap, hgu, hgB]
  have hT : ∀ x, lin (conjMap u v (lin g w')) x = lin g (lin (conjMap u' refB w') x) := by
    intro x
    rw [hcol, lin_comp]
  refine ⟨lin g w', fun x y hxy => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hT, hT] at hxy
    exact lin_injective_of_ne_zero hinj (hg hxy)
  · rw [hT, hT, lin_comm_of_basis hA, hgu]
  · rw [hT, hT, lin_comm_of_basis hB, hgB]

end CFSG.KC.L34Mod
