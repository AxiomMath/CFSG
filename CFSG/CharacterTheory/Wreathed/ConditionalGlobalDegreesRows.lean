module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseLabels
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseOrbits
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseFixed

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalGlobalDegrees

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalGeneralBase
  CFSG.Wreathed.ConditionalCompleteBase CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι]

structure RepColumns (B : Finset ι) (p A Bq Dq ω : ι) (σ τ₀ κ : ℤ) (m M : ℕ)
    (P Q : ℕ → Fin 2 → ι) (er : ℕ → Fin 2) (ψ : ZMod m × ZMod m → ι) (ρ₀ : ℤ)
    (V : Finset (ZMod m × ZMod m)) (Cz : ZMod m → ZMod m → ι → ℤ) : Prop where
  zero : ∀ φ ∈ B, Cz 0 0 φ = 0
  mid : ∀ φ ∈ B, Cz M M φ =
    baseFixed p A ω σ τ₀ φ - τ₀ * unitVector Bq φ - κ * unitVector Dq φ
  diag : ∀ r ∈ Finset.Ico 1 M, ∀ φ ∈ B, Cz r r φ =
    baseFixed p A ω σ τ₀ φ - τ₀ * unitVector (P r (er r)) φ - κ * unitVector (Q r (er r)) φ
  diag' : ∀ r ∈ Finset.Ico 1 M, ∀ φ ∈ B, Cz ((r + M : ℕ) : ZMod m) ((r + M : ℕ) : ZMod m) φ =
    baseFixed p A ω σ τ₀ φ - τ₀ * unitVector (P r (1 - er r)) φ -
      κ * unitVector (Q r (1 - er r)) φ
  gen : ∀ I ∈ V, ∀ φ ∈ B, Cz I.1 I.2 φ = baseFixed p A ω σ τ₀ φ + ρ₀ * unitVector (ψ I) φ
  inv : ∀ I I' : ZMod m × ZMod m, I' ∈ MulAction.orbit (dualGroup m) I → ∀ φ ∈ B,
    Cz I'.1 I'.2 φ = Cz I.1 I.2 φ
  cover : ∀ I : ZMod m × ZMod m, I = (0, 0) ∨
    I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ∨
    (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m), (r : ZMod m)) ∨
      I ∈ MulAction.orbit (dualGroup m) (((r + M : ℕ) : ZMod m), ((r + M : ℕ) : ZMod m))) ∨
    ∃ I' ∈ V, I ∈ MulAction.orbit (dualGroup m) I'

variable {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {m M : ℕ} {P Q : ℕ → Fin 2 → ι}
  {er : ℕ → Fin 2} {ψ : ZMod m × ZMod m → ι} {ρ₀ : ℤ} {V : Finset (ZMod m × ZMod m)}
  {Cz : ZMod m → ZMod m → ι → ℤ}

theorem RepColumns.eval (hR : RepColumns B p A Bq Dq ω σ τ₀ κ m M P Q er ψ ρ₀ V Cz) {φ : ι}
    (hφ : φ ∈ B) (I : ZMod m × ZMod m) :
    (I = (0, 0) ∧ Cz I.1 I.2 φ = 0) ∨
    (I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ∧
      Cz I.1 I.2 φ = baseFixed p A ω σ τ₀ φ - τ₀ * unitVector Bq φ - κ * unitVector Dq φ) ∨
    (∃ r ∈ Finset.Ico 1 M,
      (I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m), (r : ZMod m)) ∧
        Cz I.1 I.2 φ = baseFixed p A ω σ τ₀ φ - τ₀ * unitVector (P r (er r)) φ -
          κ * unitVector (Q r (er r)) φ) ∨
      (I ∈ MulAction.orbit (dualGroup m) (((r + M : ℕ) : ZMod m), ((r + M : ℕ) : ZMod m)) ∧
        Cz I.1 I.2 φ = baseFixed p A ω σ τ₀ φ - τ₀ * unitVector (P r (1 - er r)) φ -
          κ * unitVector (Q r (1 - er r)) φ)) ∨
    ∃ I' ∈ V, I ∈ MulAction.orbit (dualGroup m) I' ∧
      Cz I.1 I.2 φ = baseFixed p A ω σ τ₀ φ + ρ₀ * unitVector (ψ I') φ := by
  rcases hR.cover I with h | h | ⟨r, hr, h | h⟩ | ⟨I', hI', h⟩
  · subst h
    exact Or.inl ⟨rfl, hR.zero φ hφ⟩
  · exact Or.inr (Or.inl ⟨h, by rw [hR.inv _ I h φ hφ]; exact hR.mid φ hφ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨r, hr, Or.inl ⟨h, by
      rw [hR.inv _ I h φ hφ]; exact hR.diag r hr φ hφ⟩⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨r, hr, Or.inr ⟨h, by
      rw [hR.inv _ I h φ hφ]; exact hR.diag' r hr φ hφ⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨I', hI', h, by
      rw [hR.inv _ I h φ hφ]; exact hR.gen I' hI' φ hφ⟩))

theorem RepColumns.row_const (hR : RepColumns B p A Bq Dq ω σ τ₀ κ m M P Q er ψ ρ₀ V Cz)
    {φ : ι} (hφ : φ ∈ B) (hB : φ ≠ Bq) (hD : φ ≠ Dq)
    (hPQ : ∀ r ∈ Finset.Ico 1 M, ∀ e, φ ≠ P r e ∧ φ ≠ Q r e) (hψ : ∀ I ∈ V, φ ≠ ψ I)
    (I : ZMod m × ZMod m) (hI : I ≠ (0, 0)) : Cz I.1 I.2 φ = baseFixed p A ω σ τ₀ φ := by
  rcases hR.eval hφ I with ⟨h, -⟩ | ⟨-, h⟩ | ⟨r, hr, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨I', hI', -, h⟩
  · exact absurd h hI
  · rw [h, unitVector_of_ne hB, unitVector_of_ne hD]
    ring
  · rw [h, unitVector_of_ne (hPQ r hr _).1, unitVector_of_ne (hPQ r hr _).2]
    ring
  · rw [h, unitVector_of_ne (hPQ r hr _).1, unitVector_of_ne (hPQ r hr _).2]
    ring
  · rw [h, unitVector_of_ne (hψ I' hI')]
    ring

theorem RepColumns.row_single (hR : RepColumns B p A Bq Dq ω σ τ₀ κ m M P Q er ψ ρ₀ V Cz)
    {φ : ι} (hφ : φ ∈ B) (hK : baseFixed p A ω σ τ₀ φ = 0) (X : ZMod m × ZMod m) (c₀ : ℤ)
    (hX : Cz X.1 X.2 φ = c₀)
    (hM : -(τ₀ * unitVector Bq φ) - κ * unitVector Dq φ ≠ 0 →
      ((M : ZMod m), (M : ZMod m)) = X)
    (hd : ∀ r ∈ Finset.Ico 1 M,
      -(τ₀ * unitVector (P r (er r)) φ) - κ * unitVector (Q r (er r)) φ ≠ 0 →
        ((r : ZMod m), (r : ZMod m)) = X)
    (hd' : ∀ r ∈ Finset.Ico 1 M,
      -(τ₀ * unitVector (P r (1 - er r)) φ) - κ * unitVector (Q r (1 - er r)) φ ≠ 0 →
        (((r + M : ℕ) : ZMod m), ((r + M : ℕ) : ZMod m)) = X)
    (hg : ∀ I' ∈ V, ρ₀ * unitVector (ψ I') φ ≠ 0 → I' = X) (I : ZMod m × ZMod m) :
    Cz I.1 I.2 φ = if I ∈ MulAction.orbit (dualGroup m) X then c₀ else 0 := by
  by_cases hI : I ∈ MulAction.orbit (dualGroup m) X
  · rw [ite_eq_left hI, hR.inv X I hI φ hφ, hX]
  rw [ite_eq_right hI]
  rcases hR.eval hφ I with ⟨-, h⟩ | ⟨hIo, h⟩ | ⟨r, hr, ⟨hIo, h⟩ | ⟨hIo, h⟩⟩ | ⟨I', hI', hIo, h⟩
  · exact h
  · rw [h, hK]
    by_contra hne
    exact hI (by rw [← hM (by intro h0; exact hne (by linarith))]; exact hIo)
  · rw [h, hK]
    by_contra hne
    exact hI (by rw [← hd r hr (by intro h0; exact hne (by linarith))]; exact hIo)
  · rw [h, hK]
    by_contra hne
    exact hI (by rw [← hd' r hr (by intro h0; exact hne (by linarith))]; exact hIo)
  · rw [h, hK]
    by_contra hne
    exact hI (by rw [← hg I' hI' (by intro h0; exact hne (by linarith))]; exact hIo)


section XRows

variable {J : Finset ℕ} {χ : ℕ → ι} {y₀ C' : ι → ℤ} {xc yc : ℕ → ι → ℤ} {γ : ℕ → Fin 4 → ι}
  {ε : ℕ → Fin 4 → ℤ}

theorem exists_even_index {m M j : ℕ} (hm : m = 2 * M) (hj : j ∈ Finset.Ico 1 m)
    (he : Even j) : ∃ r ∈ Finset.Ico 1 M, j = m - 2 * r := by
  obtain ⟨k, hk⟩ := he
  rw [Finset.mem_Ico] at hj
  exact ⟨M - k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩

theorem xrow_core (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C' xc) (hm : m = 2 * M)
    (hJ : J = (Finset.Ico 1 m).filter Odd)
    (hQ : ∀ r ∈ Finset.Ico 1 M,
      Quadruple B p A Bq Dq ω σ τ₀ κ J χ (γ r) (ε r) (xc (m - 2 * r)) (yc r))
    {φ : ι} (hφ : φ ∈ B) (hχ : ∀ j ∈ J, φ ≠ χ j) (hγ : ∀ r ∈ Finset.Ico 1 M, ∀ l, φ ≠ γ r l)
    (j : ℕ) (hj : j ∈ Finset.Ico 1 m) : xc j φ = fixedPart p A Bq Dq σ τ₀ κ φ := by
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨r, hr, rfl⟩ := exists_even_index hm hj he
    rw [(hQ r hr).hxk φ hφ, Finset.sum_eq_zero fun l _ => by
      rw [unitVector_of_ne (hγ r hr l), mul_zero], add_zero]
  · have hjJ : j ∈ J := by rw [hJ]; exact Finset.mem_filter.mpr ⟨hj, ho⟩
    rw [hS.hxj j hjJ φ hφ, unitVector_of_ne (hχ j hjJ), mul_zero, add_zero]

theorem xrow_odd (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C' xc) (hm : m = 2 * M)
    (hJ : J = (Finset.Ico 1 m).filter Odd)
    (hQ : ∀ r ∈ Finset.Ico 1 M,
      Quadruple B p A Bq Dq ω σ τ₀ κ J χ (γ r) (ε r) (xc (m - 2 * r)) (yc r))
    {h : ℕ} (hh : h ∈ J) (j : ℕ) (hj : j ∈ Finset.Ico 1 m) :
    xc j (χ h) = if j = h then 2 * σ else 0 := by
  obtain ⟨n1, n2, n3, n4, -⟩ := hS.hχcore h hh
  have hfix := fixedPart_of_ne (p := p) (A := A) (Bq := Bq) (Dq := Dq) σ τ₀ κ n1 n2 n3 n4
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨r, hr, rfl⟩ := exists_even_index hm hj he
    have hne : m - 2 * r ≠ h := by
      intro heq
      rw [hJ, Finset.mem_filter] at hh
      rw [← heq] at hh
      obtain ⟨k, hk⟩ := hh.2
      omega
    rw [(hQ r hr).hxk _ (hS.hχB h hh), hfix, Finset.sum_eq_zero fun l _ => by
      rw [unitVector_of_ne fun e => (hQ r hr).odd l h hh e.symm, mul_zero], ite_eq_right hne]
    ring
  · have hjJ : j ∈ J := by rw [hJ]; exact Finset.mem_filter.mpr ⟨hj, ho⟩
    rw [hS.hxj j hjJ _ (hS.hχB h hh), hfix]
    by_cases hjh : j = h
    · subst hjh
      rw [unitVector_self, ite_eq_left rfl]
      ring
    · rw [unitVector_of_ne fun e => hjh (hS.hχinj hh hjJ e).symm, ite_eq_right hjh]
      ring

theorem xrow_even (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C' xc) (hm : m = 2 * M)
    (hJ : J = (Finset.Ico 1 m).filter Odd)
    (hQ : ∀ r ∈ Finset.Ico 1 M,
      Quadruple B p A Bq Dq ω σ τ₀ κ J χ (γ r) (ε r) (xc (m - 2 * r)) (yc r))
    (hdisj : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, r ≠ t → ∀ l l', γ r l ≠ γ t l')
    {t : ℕ} (ht : t ∈ Finset.Ico 1 M) (l : Fin 4) (j : ℕ) (hj : j ∈ Finset.Ico 1 m) :
    xc j (γ t l) = if j = m - 2 * t then ε t l else 0 := by
  obtain ⟨n1, n2, n3, n4, -⟩ := (hQ t ht).core l
  have hfix := fixedPart_of_ne (p := p) (A := A) (Bq := Bq) (Dq := Dq) σ τ₀ κ n1 n2 n3 n4
  have hmem := (hQ t ht).mem l
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨r, hr, rfl⟩ := exists_even_index hm hj he
    rw [(hQ r hr).hxk _ hmem, hfix, zero_add]
    by_cases hrt : r = t
    · subst hrt
      rw [ite_eq_left rfl, Finset.sum_eq_single l (fun l' _ hl' => by
          rw [unitVector_of_ne fun e => hl' ((hQ r hr).inj e).symm, mul_zero])
        fun h => absurd (Finset.mem_univ l) h, unitVector_self, mul_one]
    · have hne : m - 2 * r ≠ m - 2 * t := by
        rw [Finset.mem_Ico] at hr ht
        omega
      rw [ite_eq_right hne, Finset.sum_eq_zero fun l' _ => by
        rw [unitVector_of_ne fun e => hdisj t ht r hr (Ne.symm hrt) l l' e, mul_zero]]
  · have hjJ : j ∈ J := by rw [hJ]; exact Finset.mem_filter.mpr ⟨hj, ho⟩
    have hne : j ≠ m - 2 * t := by
      intro heq
      rw [Finset.mem_Ico] at ht
      obtain ⟨k, hk⟩ := ho
      omega
    rw [hS.hxj j hjJ _ hmem, hfix, unitVector_of_ne fun e => (hQ t ht).odd l j hjJ e,
      ite_eq_right hne]
    ring

end XRows


theorem labels_of_image {X : Type*} [DecidableEq X] {γ : Fin 4 → X} (hγ : Function.Injective γ)
    {P Q : Fin 2 → X} (h : ({P 0, Q 0, P 1, Q 1} : Finset X) = Finset.univ.image γ) :
    (∀ e, (∃ l, P e = γ l) ∧ ∃ l, Q e = γ l) ∧ Function.Injective P ∧
      Function.Injective Q ∧ ∀ e e', P e ≠ Q e' := by
  have hmem : ∀ x ∈ ({P 0, Q 0, P 1, Q 1} : Finset X), ∃ l, x = γ l := fun x hx => by
    rw [h] at hx
    obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hx
    exact ⟨l, hl.symm⟩
  have hcard : ([P 0, Q 0, P 1, Q 1] : List X).toFinset.card = 4 := by
    rw [show ([P 0, Q 0, P 1, Q 1] : List X).toFinset = ({P 0, Q 0, P 1, Q 1} : Finset X) by
      simp, h, Finset.card_image_of_injective _ hγ, Finset.card_univ, Fintype.card_fin]
  have hnodup : ([P 0, Q 0, P 1, Q 1] : List X).Nodup := by
    rw [List.card_toFinset] at hcard
    have hsub := List.dedup_sublist ([P 0, Q 0, P 1, Q 1] : List X)
    have heq := hsub.eq_of_length (by rw [hcard]; rfl)
    rw [← heq]
    exact List.nodup_dedup _
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnodup
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩ := hnodup
  refine ⟨fun e => ⟨hmem _ ?_, hmem _ ?_⟩, fun e e' he => ?_, fun e e' he => ?_,
    fun e e' he => ?_⟩
  · fin_cases e <;> simp
  · fin_cases e <;> simp
  · fin_cases e <;> fin_cases e' <;> simp_all
  · fin_cases e <;> fin_cases e' <;> simp_all
  · fin_cases e <;> fin_cases e' <;> simp_all


theorem fin_two_eq_one_sub {a b : Fin 2} (h : a ≠ b) : a = 1 - b := by
  fin_cases a <;> fin_cases b <;> simp_all

theorem fin_two_one_sub_ne (b : Fin 2) : 1 - b ≠ b := by
  fin_cases b <;> decide

end CFSG.Wreathed.ConditionalGlobalDegrees
