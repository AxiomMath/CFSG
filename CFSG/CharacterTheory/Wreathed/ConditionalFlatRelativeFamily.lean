module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatRelativeRows

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatRelative

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.FlatComplete

structure Support {ι : Type*} (BB : Finset ι) (m M : ℕ) (V : Finset (ZMod m × ZMod m))
    (X : ZMod m → ι → ℂ) (c : ZMod m → ZMod m → ι → ℂ) (δ₀ δ₁ δ₂ δ₃ δ₄ α γ : ℤ)
    (χ₀ χ₁ χ₂ χ₃ χ₄ : ι) (ξ : ℕ → ι) (P Q : ℕ → Fin 2 → ι) (ψ : ZMod m × ZMod m → ι)
    (er : ℕ → Fin 2) : Prop where
  hm : m = 2 * M
  hM : 2 ≤ M
  hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup m) I).ncard = 6
  inj : Function.Injective ![χ₀, χ₁, χ₂, χ₃, χ₄]
  ξinj : Set.InjOn ξ ((Finset.Ico 1 m).filter Odd)
  PQinj : ∀ r ∈ Finset.Ico 1 M, ∀ r' ∈ Finset.Ico 1 M, ∀ e e' : Fin 2,
    (P r e = P r' e' → r = r' ∧ e = e') ∧ (Q r e = Q r' e' → r = r' ∧ e = e') ∧ P r e ≠ Q r' e'
  ψinj : Set.InjOn ψ V
  ξcore : ∀ h ∈ (Finset.Ico 1 m).filter Odd, ξ h ∉ ({χ₀, χ₁, χ₂, χ₃, χ₄} : Finset ι)
  PQcore : ∀ r ∈ Finset.Ico 1 M, ∀ e, P r e ∉ ({χ₀, χ₁, χ₂, χ₃, χ₄} : Finset ι) ∧
    Q r e ∉ ({χ₀, χ₁, χ₂, χ₃, χ₄} : Finset ι) ∧ P r e ∉ ((Finset.Ico 1 m).filter Odd).image ξ ∧
    Q r e ∉ ((Finset.Ico 1 m).filter Odd).image ξ
  ψcore : ∀ I ∈ V, ψ I ∉ ({χ₀, χ₁, χ₂, χ₃, χ₄} : Finset ι) ∧
    ψ I ∉ ((Finset.Ico 1 m).filter Odd).image ξ ∧
    ψ I ∉ ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
      ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)
  Xodd : ∀ h ∈ (Finset.Ico 1 m).filter Odd, ∀ χ ∈ BB, X h χ =
    ((Pi.single χ₀ δ₀ + Pi.single χ₁ δ₁ + Pi.single χ₂ δ₂ + Pi.single χ₃ δ₃ +
      Pi.single (ξ h) (2 * α) : ι → ℤ) χ : ℂ)
  cMM : ∀ χ ∈ BB, c M M χ =
    ((Pi.single χ₀ δ₀ - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄) +
      Pi.single χ₂ δ₂ - Pi.single χ₃ δ₃ : ι → ℤ) χ : ℂ)
  Xeven : ∀ r ∈ Finset.Ico 1 M, ∀ χ ∈ BB, X (-(2 * (r : ZMod m))) χ =
    ((Pi.single χ₀ δ₀ + Pi.single χ₁ δ₁ + Pi.single χ₂ δ₂ + Pi.single χ₃ δ₃ -
      Pi.single (P r 0) δ₂ - Pi.single (P r 1) δ₂ - Pi.single (Q r 0) δ₃ -
      Pi.single (Q r 1) δ₃ : ι → ℤ) χ : ℂ)
  diag : ∀ r ∈ Finset.Ico 1 M, (∀ χ ∈ BB, c r r χ =
      ((Pi.single χ₀ δ₀ - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄) +
        Pi.single (P r (er r)) δ₂ - Pi.single (Q r (er r)) δ₃ : ι → ℤ) χ : ℂ)) ∧
    ∀ χ ∈ BB, c (r + M) (r + M) χ =
      ((Pi.single χ₀ δ₀ - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄) +
        Pi.single (P r (1 - er r)) δ₂ - Pi.single (Q r (1 - er r)) δ₃ : ι → ℤ) χ : ℂ)
  gen : ∀ I ∈ V, ∀ χ ∈ BB, c I.1 I.2 χ =
    ((Pi.single χ₀ δ₀ - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄) +
      Pi.single (ψ I) γ : ι → ℤ) χ : ℂ)
  c00 : ∀ χ ∈ BB, c 0 0 χ = 0
  inv : ∀ I I' : ZMod m × ZMod m, I' ∈ MulAction.orbit (dualGroup m) I → ∀ χ ∈ BB,
    c I'.1 I'.2 χ = c I.1 I.2 χ
  cov : ∀ I : ZMod m × ZMod m, I = (0, 0) ∨
    I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ∨
    (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m), (r : ZMod m)) ∨
      I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m) + M, (r : ZMod m) + M)) ∨
    ∃ I' ∈ V, I ∈ MulAction.orbit (dualGroup m) I'
  memχ₀ : χ₀ ∈ BB
  memχ₁ : χ₁ ∈ BB
  memχ₂ : χ₂ ∈ BB
  memχ₃ : χ₃ ∈ BB
  memχ₄ : χ₄ ∈ BB
  memξ : ∀ h ∈ (Finset.Ico 1 m).filter Odd, ξ h ∈ BB
  memPQ : ∀ r ∈ Finset.Ico 1 M, ∀ e, P r e ∈ BB ∧ Q r e ∈ BB

theorem signs_of_forall_mem {δ₀ δ₁ δ₂ δ₃ δ₄ α β γ : ℤ}
    (h : ∀ sgn ∈ [δ₀, δ₁, δ₂, δ₃, δ₄, α, β, γ], sgn = 1 ∨ sgn = -1) :
    (δ₀ = 1 ∨ δ₀ = -1) ∧ (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) ∧
      (δ₄ = 1 ∨ δ₄ = -1) ∧ (α = 1 ∨ α = -1) ∧ (β = 1 ∨ β = -1) ∧ (γ = 1 ∨ γ = -1) :=
  ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp),
    h _ (by simp), h _ (by simp)⟩

theorem mem_of_eq_union {ι : Type*} {BB : Finset ι} {m M : ℕ} {V : Finset (ZMod m × ZMod m)}
    {χ₀ χ₁ χ₂ χ₃ χ₄ : ι} {ξ : ℕ → ι} {P Q : ℕ → Fin 2 → ι} {ψ : ZMod m × ZMod m → ι}
    (hBB : BB = {χ₀, χ₁, χ₂, χ₃, χ₄} ∪ ((Finset.Ico 1 m).filter Odd).image ξ ∪
      (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)) ∪
      V.image ψ) :
    (χ₀ ∈ BB ∧ χ₁ ∈ BB ∧ χ₂ ∈ BB ∧ χ₃ ∈ BB ∧ χ₄ ∈ BB) ∧
      (∀ h ∈ (Finset.Ico 1 m).filter Odd, ξ h ∈ BB) ∧
      ∀ r ∈ Finset.Ico 1 M, ∀ e, P r e ∈ BB ∧ Q r e ∈ BB := by
  subst hBB
  refine ⟨by simp, fun h hh => ?_, fun r hr e => ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem ξ hh)))
  · have hre : (r, e) ∈ Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2)) :=
      Finset.mem_product.mpr ⟨hr, Finset.mem_univ e⟩
    exact ⟨Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem (fun x => P x.1 x.2) hre))),
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem (fun x => Q x.1 x.2) hre)))⟩

namespace Support

variable {ι : Type*} {BB : Finset ι} {m M : ℕ} {V : Finset (ZMod m × ZMod m)}
  {X : ZMod m → ι → ℂ} {c : ZMod m → ZMod m → ι → ℂ} {δ₀ δ₁ δ₂ δ₃ δ₄ α γ : ℤ}
  {χ₀ χ₁ χ₂ χ₃ χ₄ : ι} {ξ : ℕ → ι} {P Q : ℕ → Fin 2 → ι} {ψ : ZMod m × ZMod m → ι}
  {er : ℕ → Fin 2}
  (hS : Support BB m M V X c δ₀ δ₁ δ₂ δ₃ δ₄ α γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ er)
include hS

theorem core_ne : χ₀ ≠ χ₁ ∧ χ₀ ≠ χ₂ ∧ χ₀ ≠ χ₃ ∧ χ₀ ≠ χ₄ ∧ χ₁ ≠ χ₂ ∧ χ₁ ≠ χ₃ ∧ χ₁ ≠ χ₄ ∧
    χ₂ ≠ χ₃ ∧ χ₂ ≠ χ₄ ∧ χ₃ ≠ χ₄ := by
  have key : ∀ a b : Fin 5, a ≠ b → ![χ₀, χ₁, χ₂, χ₃, χ₄] a ≠ ![χ₀, χ₁, χ₂, χ₃, χ₄] b :=
    fun a b hab h => hab (hS.inj h)
  exact ⟨key 0 1 (by decide), key 0 2 (by decide), key 0 3 (by decide), key 0 4 (by decide),
    key 1 2 (by decide), key 1 3 (by decide), key 1 4 (by decide), key 2 3 (by decide),
    key 2 4 (by decide), key 3 4 (by decide)⟩

theorem odd_ne {h : ℕ} (hh : h ∈ (Finset.Ico 1 m).filter Odd) :
    ξ h ≠ χ₀ ∧ ξ h ≠ χ₁ ∧ ξ h ≠ χ₂ ∧ ξ h ≠ χ₃ ∧ ξ h ≠ χ₄ := by
  have h' := hS.ξcore h hh
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h'
  exact h'

theorem even_ne {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) :
    (P r e ≠ χ₀ ∧ P r e ≠ χ₁ ∧ P r e ≠ χ₂ ∧ P r e ≠ χ₃ ∧ P r e ≠ χ₄) ∧
    (Q r e ≠ χ₀ ∧ Q r e ≠ χ₁ ∧ Q r e ≠ χ₂ ∧ Q r e ≠ χ₃ ∧ Q r e ≠ χ₄) ∧
    (∀ h ∈ (Finset.Ico 1 m).filter Odd, P r e ≠ ξ h ∧ Q r e ≠ ξ h) := by
  obtain ⟨hP, hQ, hPξ, hQξ⟩ := hS.PQcore r hr e
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hP hQ
  refine ⟨hP, hQ, fun h hh => ⟨fun he => hPξ (Finset.mem_image.mpr ⟨h, hh, he.symm⟩),
    fun he => hQξ (Finset.mem_image.mpr ⟨h, hh, he.symm⟩)⟩⟩

theorem gen_ne {I : ZMod m × ZMod m} (hI : I ∈ V) :
    (ψ I ≠ χ₀ ∧ ψ I ≠ χ₁ ∧ ψ I ≠ χ₂ ∧ ψ I ≠ χ₃ ∧ ψ I ≠ χ₄) ∧
    (∀ h ∈ (Finset.Ico 1 m).filter Odd, ψ I ≠ ξ h) ∧
    (∀ r ∈ Finset.Ico 1 M, ∀ e, ψ I ≠ P r e ∧ ψ I ≠ Q r e) := by
  obtain ⟨hc, hξ, hPQ⟩ := hS.ψcore I hI
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  refine ⟨hc, fun h hh he => hξ (Finset.mem_image.mpr ⟨h, hh, he.symm⟩),
    fun r hr e => ⟨fun he => hPQ (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
      ⟨(r, e), Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩, he.symm⟩))),
      fun he => hPQ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨(r, e), Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩, he.symm⟩)))⟩⟩

theorem x_core : ∀ j ∈ Finset.Ico 1 m, X j χ₀ = δ₀ ∧ X j χ₁ = δ₁ ∧ X j χ₂ = δ₂ ∧
    X j χ₃ = δ₃ ∧ X j χ₄ = 0 := by
  obtain ⟨n01, n02, n03, n04, n12, n13, n14, n23, n24, n34⟩ := hS.core_ne
  have hrow : ∀ χ ∈ BB, ∀ x : ℂ, (∀ h ∈ (Finset.Ico 1 m).filter Odd, ξ h ≠ χ) →
      (∀ r ∈ Finset.Ico 1 M, ∀ e, P r e ≠ χ ∧ Q r e ≠ χ) →
      ((Pi.single χ₀ δ₀ + Pi.single χ₁ δ₁ + Pi.single χ₂ δ₂ +
        Pi.single χ₃ δ₃ : ι → ℤ) χ : ℂ) = x → ∀ j ∈ Finset.Ico 1 m, X j χ = x := by
    intro χ hχ x hξ hPQ hA
    refine x_row_eq (X := fun j => X j χ) hS.hm (fun _ => x) (fun h hh => ?_) (fun r hr => ?_)
    · rw [hS.Xodd h hh χ hχ, ← hA, Pi.add_apply, Pi.single_eq_of_ne (hξ h hh).symm, add_zero]
    · rw [hS.Xeven r hr χ hχ, ← hA]
      simp only [Pi.sub_apply, Pi.single_eq_of_ne (hPQ r hr 0).1.symm,
        Pi.single_eq_of_ne (hPQ r hr 1).1.symm, Pi.single_eq_of_ne (hPQ r hr 0).2.symm,
        Pi.single_eq_of_ne (hPQ r hr 1).2.symm, sub_zero]
  intro j hj
  refine ⟨hrow χ₀ hS.memχ₀ _ (fun h hh => (hS.odd_ne hh).1)
      (fun r hr e => ⟨(hS.even_ne hr e).1.1, (hS.even_ne hr e).2.1.1⟩) ?_ j hj,
    hrow χ₁ hS.memχ₁ _ (fun h hh => (hS.odd_ne hh).2.1)
      (fun r hr e => ⟨(hS.even_ne hr e).1.2.1, (hS.even_ne hr e).2.1.2.1⟩) ?_ j hj,
    hrow χ₂ hS.memχ₂ _ (fun h hh => (hS.odd_ne hh).2.2.1)
      (fun r hr e => ⟨(hS.even_ne hr e).1.2.2.1, (hS.even_ne hr e).2.1.2.2.1⟩) ?_ j hj,
    hrow χ₃ hS.memχ₃ _ (fun h hh => (hS.odd_ne hh).2.2.2.1)
      (fun r hr e => ⟨(hS.even_ne hr e).1.2.2.2.1, (hS.even_ne hr e).2.1.2.2.2.1⟩) ?_ j hj,
    hrow χ₄ hS.memχ₄ _ (fun h hh => (hS.odd_ne hh).2.2.2.2)
      (fun r hr e => ⟨(hS.even_ne hr e).1.2.2.2.2, (hS.even_ne hr e).2.1.2.2.2.2⟩) ?_ j hj⟩
  · simp [n01.symm, n02.symm, n03.symm]
  · simp [n01, n12.symm, n13.symm]
  · simp [n02, n12, n23.symm]
  · simp [n03, n13, n23]
  · simp [n04.symm, n14.symm, n24.symm, n34.symm]

theorem x_odd {h : ℕ} (hh : h ∈ (Finset.Ico 1 m).filter Odd) :
    ∀ j ∈ Finset.Ico 1 m, X j (ξ h) = if j = h then 2 * (α : ℂ) else 0 := by
  obtain ⟨n0, n1, n2, n3, -⟩ := hS.odd_ne hh
  have hB := hS.memξ h hh
  refine x_row_eq (X := fun j => X j (ξ h)) hS.hm _ (fun h' hh' => ?_) (fun r hr => ?_)
  · rw [hS.Xodd h' hh' _ hB]
    by_cases hhh : h' = h
    · subst hhh
      simp [n0, n1, n2, n3]
    · have hne : ξ h ≠ ξ h' := fun he => hhh (hS.ξinj hh' hh he.symm)
      simp [n0, n1, n2, n3, hne, hhh]
  · have hne : m - 2 * r ≠ h := by
      intro he
      have hodd := (Finset.mem_filter.mp hh).2
      rw [← he] at hodd
      obtain ⟨t, ht⟩ := hodd
      have := hS.hm
      omega
    rw [hS.Xeven r hr _ hB, ite_eq_right hne]
    have hPQ := (hS.even_ne hr 0).2.2 h hh
    have hPQ' := (hS.even_ne hr 1).2.2 h hh
    simp [n0, n1, n2, n3, hPQ.1.symm, hPQ.2.symm, hPQ'.1.symm, hPQ'.2.symm]

theorem x_even {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) :
    ∀ j ∈ Finset.Ico 1 m, X j (P r e) = (if j = m - 2 * r then -(δ₂ : ℂ) else 0) ∧
      X j (Q r e) = (if j = m - 2 * r then -(δ₃ : ℂ) else 0) := by
  have h01 : ∀ e : Fin 2, e = 0 ∨ e = 1 := by decide
  obtain ⟨⟨p0, p1, p2, p3, -⟩, ⟨q0, q1, q2, q3, -⟩, hξ⟩ := hS.even_ne hr e
  obtain ⟨hPB, hQB⟩ := hS.memPQ r hr e
  have hr₁ := Finset.mem_Ico.mp hr
  have hm := hS.hm
  have hodd : ∀ h' ∈ (Finset.Ico 1 m).filter Odd, h' ≠ m - 2 * r := by
    intro h' hh' he
    obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hh').2
    omega
  have heven : ∀ r' ∈ Finset.Ico 1 M, (m - 2 * r' = m - 2 * r ↔ r' = r) := by
    intro r' hr'
    have := Finset.mem_Ico.mp hr'
    omega
  have hP : ∀ r' ∈ Finset.Ico 1 M, ∀ e', (P r e = P r' e' ↔ r' = r ∧ e' = e) := by
    intro r' hr' e'
    constructor
    · intro he
      obtain ⟨h1, h2⟩ := (hS.PQinj r hr r' hr' e e').1 he
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hQ : ∀ r' ∈ Finset.Ico 1 M, ∀ e', (Q r e = Q r' e' ↔ r' = r ∧ e' = e) := by
    intro r' hr' e'
    constructor
    · intro he
      obtain ⟨h1, h2⟩ := (hS.PQinj r hr r' hr' e e').2.1 he
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hPQ : ∀ r' ∈ Finset.Ico 1 M, ∀ e', P r e ≠ Q r' e' ∧ Q r e ≠ P r' e' :=
    fun r' hr' e' => ⟨(hS.PQinj r hr r' hr' e e').2.2,
      fun he => (hS.PQinj r' hr' r hr e' e).2.2 he.symm⟩
  intro j hj
  constructor
  · refine x_row_eq (X := fun j => X j (P r e)) hm
      (fun j => if j = m - 2 * r then -(δ₂ : ℂ) else 0) (fun h' hh' => ?_)
      (fun r' hr' => ?_) j hj
    · rw [hS.Xodd h' hh' _ hPB, ite_eq_right (hodd h' hh')]
      simp [p0, p1, p2, p3, (hξ h' hh').1]
    · rw [hS.Xeven r' hr' _ hPB]
      by_cases hrr : r' = r
      · subst hrr
        rw [ite_eq_left rfl]
        rcases h01 e with rfl | rfl <;>
          simp [p0, p1, p2, p3, hP r' hr', (hPQ r' hr' 0).1, (hPQ r' hr' 1).1]
      · rw [ite_eq_right fun h => hrr ((heven r' hr').mp h)]
        simp [p0, p1, p2, p3, hP r' hr', (hPQ r' hr' 0).1, (hPQ r' hr' 1).1,
          hrr]
  · refine x_row_eq (X := fun j => X j (Q r e)) hm
      (fun j => if j = m - 2 * r then -(δ₃ : ℂ) else 0) (fun h' hh' => ?_)
      (fun r' hr' => ?_) j hj
    · rw [hS.Xodd h' hh' _ hQB, ite_eq_right (hodd h' hh')]
      simp [q0, q1, q2, q3, (hξ h' hh').2]
    · rw [hS.Xeven r' hr' _ hQB]
      by_cases hrr : r' = r
      · subst hrr
        rw [ite_eq_left rfl]
        rcases h01 e with rfl | rfl <;>
          simp [q0, q1, q2, q3, hQ r' hr', (hPQ r' hr' 0).2, (hPQ r' hr' 1).2]
      · rw [ite_eq_right fun h => hrr ((heven r' hr').mp h)]
        simp [q0, q1, q2, q3, hQ r' hr', (hPQ r' hr' 0).2, (hPQ r' hr' 1).2,
          hrr]

theorem c_row_const {χ : ι} (hχ : χ ∈ BB) (κ : ℂ)
    (hmid : ((Pi.single χ₀ δ₀ - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄) +
      Pi.single χ₂ δ₂ - Pi.single χ₃ δ₃ : ι → ℤ) χ : ℂ) = κ)
    (hdiag : ∀ r ∈ Finset.Ico 1 M, ∀ e : Fin 2,
      ((Pi.single χ₀ δ₀ - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄) +
        Pi.single (P r e) δ₂ - Pi.single (Q r e) δ₃ : ι → ℤ) χ : ℂ) = κ)
    (hgen : ∀ I ∈ V, ((Pi.single χ₀ δ₀ - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄) +
      Pi.single (ψ I) γ : ι → ℤ) χ : ℂ) = κ) (I : ZMod m × ZMod m) :
    c I.1 I.2 χ = if I = (0, 0) then 0 else κ :=
  pair_row_const (f := fun I => c I.1 I.2 χ) hS.hm (by have := hS.hM; omega) hS.hV6
    (fun I I' h => hS.inv I I' h χ hχ) hS.cov κ (hS.c00 χ hχ) (by rw [← hmid]; exact hS.cMM χ hχ)
    (fun r hr => by rw [← hdiag r hr (er r)]; exact (hS.diag r hr).1 χ hχ)
    (fun r hr => by rw [← hdiag r hr (1 - er r)]; exact (hS.diag r hr).2 χ hχ)
    (fun I hI => by rw [← hgen I hI]; exact hS.gen I hI χ hχ) I

theorem c_core (I : ZMod m × ZMod m) :
    c I.1 I.2 χ₀ = (if I = (0, 0) then 0 else (δ₀ : ℂ)) ∧
    c I.1 I.2 χ₁ = (if I = (0, 0) then 0 else -(δ₁ : ℂ)) ∧
    c I.1 I.2 χ₄ = (if I = (0, 0) then 0 else 2 * (δ₄ : ℂ)) := by
  obtain ⟨n01, n02, n03, n04, n12, n13, n14, n23, n24, n34⟩ := hS.core_ne
  refine ⟨hS.c_row_const hS.memχ₀ _ ?_ (fun r hr e => ?_) (fun I hI => ?_) I,
    hS.c_row_const hS.memχ₁ _ ?_ (fun r hr e => ?_) (fun I hI => ?_) I,
    hS.c_row_const hS.memχ₄ _ ?_ (fun r hr e => ?_) (fun I hI => ?_) I⟩
  · simp [n01.symm, n02.symm, n03.symm, n04.symm]
  · obtain ⟨⟨p0, -, -, -, -⟩, ⟨q0, -, -, -, -⟩, -⟩ := hS.even_ne hr e
    simp [n01.symm, n04.symm, p0, q0]
  · obtain ⟨⟨g0, -, -, -, -⟩, -, -⟩ := hS.gen_ne hI
    simp [n01.symm, n04.symm, g0]
  · simp [n01, n12.symm, n13.symm, n14.symm]
  · obtain ⟨⟨-, p1, -, -, -⟩, ⟨-, q1, -, -, -⟩, -⟩ := hS.even_ne hr e
    simp [n01, n14.symm, p1, q1]
  · obtain ⟨⟨-, g1, -, -, -⟩, -, -⟩ := hS.gen_ne hI
    simp [n01, n14.symm, g1]
  · simp [n04, n14, n24, n34]
  · obtain ⟨⟨-, -, -, -, p4⟩, ⟨-, -, -, -, q4⟩, -⟩ := hS.even_ne hr e
    simp [n04, n14, p4, q4]
  · obtain ⟨⟨-, -, -, -, g4⟩, -, -⟩ := hS.gen_ne hI
    simp [n04, n14, g4]

theorem c_mid (I : ZMod m × ZMod m) :
    c I.1 I.2 χ₂ = (if I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m))
      then (δ₂ : ℂ) else 0) ∧
    c I.1 I.2 χ₃ = (if I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m))
      then -(δ₃ : ℂ) else 0) := by
  obtain ⟨n01, n02, n03, n04, n12, n13, n14, n23, n24, n34⟩ := hS.core_ne
  have hm := hS.hm
  have hM0 : (M : ZMod m) ≠ 0 := ConditionalCompleteBase.natCast_half_ne_zero hm
    (by have := hS.hM; omega)
  have hrM : ∀ r ∈ Finset.Ico 1 M, (r : ZMod m) ≠ M ∧ (r : ZMod m) + M ≠ M := by
    intro r hr
    have hr₁ := Finset.mem_Ico.mp hr
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := natCast_inj_of_lt (by omega) (by omega) h
      omega
    · have h' : (r : ZMod m) = 0 := by linear_combination h
      exact natCast_ne_zero_of_lt (by omega) (by omega) h'
  have hrow : ∀ χ ∈ BB, ∀ κ : ℂ, χ ≠ χ₀ → χ ≠ χ₁ → χ ≠ χ₄ →
      ((Pi.single χ₂ δ₂ - Pi.single χ₃ δ₃ : ι → ℤ) χ : ℂ) = κ →
      (∀ r ∈ Finset.Ico 1 M, ∀ e, χ ≠ P r e ∧ χ ≠ Q r e) → (∀ I ∈ V, χ ≠ ψ I) →
      ∀ I : ZMod m × ZMod m, c I.1 I.2 χ =
        if I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) then κ else 0 := by
    intro χ hχ κ h0 h1 h4 hκ hPQ hψ I
    refine pair_row_diag (f := fun I => c I.1 I.2 χ) hS.hV6 (fun I I' h => hS.inv I I' h χ hχ)
      hS.cov (M : ZMod m) κ ?_ ?_ (fun r hr => ?_) (fun r hr => ?_) (fun I hI => ?_) I
    · rw [ite_eq_right fun h => hM0 h.symm]
      exact hS.c00 χ hχ
    · rw [ite_eq_left rfl, ← hκ]
      exact (hS.cMM χ hχ).trans (by simp [h0, h1, h4])
    · rw [ite_eq_right (hrM r hr).1]
      exact ((hS.diag r hr).1 χ hχ).trans
        (by simp [h0, h1, h4, (hPQ r hr _).1, (hPQ r hr _).2])
    · rw [ite_eq_right (hrM r hr).2]
      exact ((hS.diag r hr).2 χ hχ).trans
        (by simp [h0, h1, h4, (hPQ r hr _).1, (hPQ r hr _).2])
    · exact (hS.gen I hI χ hχ).trans (by simp [h0, h1, h4, hψ I hI])
  refine ⟨hrow χ₂ hS.memχ₂ _ n02.symm n12.symm n24 (by simp [n23]) (fun r hr e => ?_)
      (fun I hI => ?_) I,
    hrow χ₃ hS.memχ₃ _ n03.symm n13.symm n34 (by simp [n23.symm]) (fun r hr e => ?_)
      (fun I hI => ?_) I⟩
  · obtain ⟨⟨-, -, p2, -, -⟩, ⟨-, -, q2, -, -⟩, -⟩ := hS.even_ne hr e
    exact ⟨p2.symm, q2.symm⟩
  · exact (hS.gen_ne hI).1.2.2.1.symm
  · obtain ⟨⟨-, -, -, p3, -⟩, ⟨-, -, -, q3, -⟩, -⟩ := hS.even_ne hr e
    exact ⟨p3.symm, q3.symm⟩
  · exact (hS.gen_ne hI).1.2.2.2.1.symm

theorem c_odd {h : ℕ} (hh : h ∈ (Finset.Ico 1 m).filter Odd) (I : ZMod m × ZMod m) :
    c I.1 I.2 (ξ h) = 0 := by
  obtain ⟨n0, n1, n2, n3, n4⟩ := hS.odd_ne hh
  have h' := hS.c_row_const (hS.memξ h hh) 0 (by simp [n0, n1, n2, n3, n4])
    (fun r hr e => by simp [n0, n1, n4, ((hS.even_ne hr e).2.2 h hh).1.symm,
      ((hS.even_ne hr e).2.2 h hh).2.symm])
    (fun I hI => by simp [n0, n1, n4, ((hS.gen_ne hI).2.1 h hh).symm]) I
  rw [h', ite_self]

theorem c_diagRep {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) {χ : ι} (hχ : χ ∈ BB) :
    c (if e = er r then (r : ZMod m) else (r : ZMod m) + M)
      (if e = er r then (r : ZMod m) else (r : ZMod m) + M) χ =
      ((Pi.single χ₀ δ₀ - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄) +
        Pi.single (P r e) δ₂ - Pi.single (Q r e) δ₃ : ι → ℤ) χ : ℂ) := by
  by_cases he : e = er r
  · rw [ite_eq_left he]
    subst he
    exact (hS.diag r hr).1 χ hχ
  · rw [ite_eq_right he, eq_one_sub_of_ne he]
    exact (hS.diag r hr).2 χ hχ

theorem c_even {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) (I : ZMod m × ZMod m) :
    c I.1 I.2 (P r e) = (if I ∈ MulAction.orbit (dualGroup m)
      (if e = er r then (r : ZMod m) else (r : ZMod m) + M,
        if e = er r then (r : ZMod m) else (r : ZMod m) + M) then (δ₂ : ℂ) else 0) ∧
    c I.1 I.2 (Q r e) = (if I ∈ MulAction.orbit (dualGroup m)
      (if e = er r then (r : ZMod m) else (r : ZMod m) + M,
        if e = er r then (r : ZMod m) else (r : ZMod m) + M) then -(δ₃ : ℂ) else 0) := by
  obtain ⟨⟨p0, p1, p2, p3, p4⟩, ⟨q0, q1, q2, q3, q4⟩, -⟩ := hS.even_ne hr e
  obtain ⟨hPB, hQB⟩ := hS.memPQ r hr e
  have hP : ∀ r' ∈ Finset.Ico 1 M, ∀ e', (P r e = P r' e' ↔ r' = r ∧ e' = e) := by
    intro r' hr' e'
    constructor
    · intro he
      obtain ⟨h1, h2⟩ := (hS.PQinj r hr r' hr' e e').1 he
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hQ : ∀ r' ∈ Finset.Ico 1 M, ∀ e', (Q r e = Q r' e' ↔ r' = r ∧ e' = e) := by
    intro r' hr' e'
    constructor
    · intro he
      obtain ⟨h1, h2⟩ := (hS.PQinj r hr r' hr' e e').2.1 he
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hPQ : ∀ r' ∈ Finset.Ico 1 M, ∀ e', P r e ≠ Q r' e' ∧ Q r e ≠ P r' e' :=
    fun r' hr' e' => ⟨(hS.PQinj r hr r' hr' e e').2.2,
      fun he => (hS.PQinj r' hr' r hr e' e).2.2 he.symm⟩
  have hMM : ∀ χ, χ ≠ χ₀ → χ ≠ χ₁ → χ ≠ χ₂ → χ ≠ χ₃ → χ ≠ χ₄ →
      ((Pi.single χ₀ δ₀ - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄) +
        Pi.single χ₂ δ₂ - Pi.single χ₃ δ₃ : ι → ℤ) χ : ℂ) = 0 := by
    intro χ h0 h1 h2 h3 h4
    simp [h0, h1, h2, h3, h4]
  constructor
  · refine pair_row_single (f := fun I => c I.1 I.2 (P r e)) hS.hm hS.hV6
      (fun I I' h => hS.inv I I' h _ hPB) hS.cov er hr e (δ₂ : ℂ) (hS.c00 _ hPB)
      ((hS.cMM _ hPB).trans (hMM _ p0 p1 p2 p3 p4)) (fun r' hr' e' => ?_) (fun I hI => ?_) I
    · refine (hS.c_diagRep hr' e' hPB).trans ?_
      by_cases hc : r' = r ∧ e' = e
      · obtain ⟨rfl, rfl⟩ := hc
        rw [ite_eq_left ⟨rfl, rfl⟩]
        simp [p0, p1, p4, (hPQ _ hr' _).1]
      · have hne : P r e ≠ P r' e' := fun h => hc ((hP r' hr' e').mp h)
        rw [ite_eq_right hc]
        simp [p0, p1, p4, hne, (hPQ r' hr' e').1]
    · obtain ⟨-, -, hψ⟩ := hS.gen_ne hI
      exact (hS.gen I hI _ hPB).trans (by simp [p0, p1, p4, (hψ r hr e).1.symm])
  · refine pair_row_single (f := fun I => c I.1 I.2 (Q r e)) hS.hm hS.hV6
      (fun I I' h => hS.inv I I' h _ hQB) hS.cov er hr e (-(δ₃ : ℂ)) (hS.c00 _ hQB)
      ((hS.cMM _ hQB).trans (hMM _ q0 q1 q2 q3 q4)) (fun r' hr' e' => ?_) (fun I hI => ?_) I
    · refine (hS.c_diagRep hr' e' hQB).trans ?_
      by_cases hc : r' = r ∧ e' = e
      · obtain ⟨rfl, rfl⟩ := hc
        rw [ite_eq_left ⟨rfl, rfl⟩]
        simp [q0, q1, q4, (hPQ _ hr' _).2]
      · have hne : Q r e ≠ Q r' e' := fun h => hc ((hQ r' hr' e').mp h)
        rw [ite_eq_right hc]
        simp [q0, q1, q4, hne, (hPQ r' hr' e').2]
    · obtain ⟨-, -, hψ⟩ := hS.gen_ne hI
      exact (hS.gen I hI _ hQB).trans (by simp [q0, q1, q4, (hψ r hr e).2.symm])

theorem fs_core_one [NeZero m] (Fs : ZMod m → ι → ℂ)
    (hrecon : ∀ j : ZMod m, X j χ₁ + 2 * Fs j χ₁ =
      ∑ i : ZMod m, c i (0 - i) χ₁ - ∑ i : ZMod m, c i (-j - i) χ₁)
    (hF0 : Fs 0 χ₁ = 0) (j : ZMod m) : Fs j χ₁ = 0 := by
  by_cases hj : j = 0
  · rw [hj]
    exact hF0
  have hjv : j.val ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr
    ⟨Nat.pos_of_ne_zero fun h => hj ((ZMod.val_eq_zero j).mp h), ZMod.val_lt j⟩
  have hX : X j χ₁ = δ₁ := by
    have h := (hS.x_core j.val hjv).2.1
    rwa [ZMod.natCast_zmod_val] at h
  have hrow : ∀ l : ZMod m, ∑ i : ZMod m, c i (l - i) χ₁ =
      m * (-(δ₁ : ℂ)) - if l = 0 then -(δ₁ : ℂ) else 0 := by
    intro l
    rw [← sum_antidiag_off_zero]
    exact Finset.sum_congr rfl fun i _ => (hS.c_core (i, l - i)).2.1
  have h := hrecon j
  rw [hX, hrow, hrow, ite_eq_left rfl, ite_eq_right (neg_ne_zero.mpr hj)] at h
  linear_combination h / 2

theorem y_sum_core_one (Y : ℕ → ι → ℤ) (β : ℤ)
    (hY0 : ∀ χ ∈ BB, Y 0 χ = (β • (Pi.single χ₀ δ₀ + Pi.single χ₁ δ₁ - Pi.single χ₂ δ₂ -
      Pi.single χ₃ δ₃ : ι → ℤ)) χ)
    (hYeven : ∀ r ∈ Finset.Ico 1 M, ∀ χ ∈ BB, Y r χ = (-Pi.single (P r 0) δ₂ +
      Pi.single (P r 1) δ₂ - Pi.single (Q r 0) δ₃ + Pi.single (Q r 1) δ₃ : ι → ℤ) χ)
    (ζ : ℂ) (h : ℤ) : ∑ r ∈ Finset.range M, (Y r χ₁ : ℂ) * ζ ^ ((r : ℤ) * h) = β * δ₁ := by
  obtain ⟨n01, n02, n03, n04, n12, n13, n14, n23, n24, n34⟩ := hS.core_ne
  have hM0 : 0 < M := by have := hS.hM; omega
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hM0,
    Finset.sum_eq_zero fun r hr => ?_, add_zero, hY0 χ₁ hS.memχ₁]
  · simp [n01, n12.symm, n13.symm]
  · obtain ⟨⟨-, p1, -, -, -⟩, ⟨-, q1, -, -, -⟩, -⟩ := hS.even_ne hr 0
    obtain ⟨⟨-, p1', -, -, -⟩, ⟨-, q1', -, -, -⟩, -⟩ := hS.even_ne hr 1
    rw [hYeven r hr χ₁ hS.memχ₁]
    simp [p1.symm, q1.symm, p1'.symm, q1'.symm]

end Support

end CFSG.Wreathed.FlatRelative
