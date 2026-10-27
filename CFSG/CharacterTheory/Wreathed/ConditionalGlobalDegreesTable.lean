module

public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesRows
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseTheorem
public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalGlobalDegrees

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalGeneralBase
  CFSG.Wreathed.ConditionalCompleteBase CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι]

theorem labels_mem {B : Finset ι} {γ : Fin 4 → ι} (hγ : ∀ l, γ l ∈ B)
    (hinj : Function.Injective γ) {P Q : Fin 2 → ι}
    (h : ({P 0, Q 0, P 1, Q 1} : Finset ι) = Finset.univ.image γ) (e : Fin 2) :
    P e ∈ B ∧ Q e ∈ B := by
  obtain ⟨⟨l, hl⟩, ⟨l', hl'⟩⟩ := (labels_of_image hinj h).1 e
  exact ⟨hl ▸ hγ l, hl' ▸ hγ l'⟩

@[expose] def labelRep (m M : ℕ) (er : ℕ → Fin 2) (t : ℕ) (e : Fin 2) : ZMod m × ZMod m :=
  if e = er t then ((t : ZMod m), (t : ZMod m))
  else (((t + M : ℕ) : ZMod m), ((t + M : ℕ) : ZMod m))

structure ColumnTable (B : Finset ι) (p A Bq Dq ω : ι) (σ τ₀ κ : ℤ) (m M : ℕ) (J : Finset ℕ)
    (χ : ℕ → ι) (γ : ℕ → Fin 4 → ι) (εs : ℕ → Fin 4 → ℤ) (P Q : ℕ → Fin 2 → ι)
    (er : ℕ → Fin 2) (ψ : ZMod m × ZMod m → ι) (ρ₀ : ℤ) (V : Finset (ZMod m × ZMod m))
    (yc cc : ℕ → ι → ℤ) (Cz : ZMod m → ZMod m → ι → ℤ) : Prop where
  hm : m = 2 * M
  hM : 2 ≤ M
  hJ : J = (Finset.Ico 1 m).filter Odd
  core : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ (yc 0) (Cz M M) cc
  quad : ∀ r ∈ Finset.Ico 1 M,
    Quadruple B p A Bq Dq ω σ τ₀ κ J χ (γ r) (εs r) (cc (m - 2 * r)) (yc r)
  disj : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, r ≠ t → ∀ l l', γ r l ≠ γ t l'
  lab : ∀ r ∈ Finset.Ico 1 M,
    ({P r 0, Q r 0, P r 1, Q r 1} : Finset ι) = Finset.univ.image (γ r)
  gen : ∀ I ∈ V, ψ I ∈ B ∧ ψ I ≠ p ∧ ψ I ≠ A ∧ ψ I ≠ Bq ∧ ψ I ≠ Dq ∧ ψ I ≠ ω ∧
    (∀ j ∈ J, ψ I ≠ χ j) ∧ ∀ r ∈ Finset.Ico 1 M, ∀ l, ψ I ≠ γ r l
  geninj : Set.InjOn ψ V
  rep : RepColumns B p A Bq Dq ω σ τ₀ κ m M P Q er ψ ρ₀ V Cz
  xpq : ∀ t ∈ Finset.Ico 1 M, ∀ φ ∈ B, cc (m - 2 * t) φ =
    fixedPart p A Bq Dq σ τ₀ κ φ + (τ₀ * unitVector (P t 0) φ + τ₀ * unitVector (P t 1) φ +
      (-κ) * unitVector (Q t 0) φ + (-κ) * unitVector (Q t 1) φ)

namespace ColumnTable

variable {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {m M : ℕ} {J : Finset ℕ} {χ : ℕ → ι}
  {γ : ℕ → Fin 4 → ι} {εs : ℕ → Fin 4 → ℤ} {P Q : ℕ → Fin 2 → ι} {er : ℕ → Fin 2}
  {ψ : ZMod m × ZMod m → ι} {ρ₀ : ℤ} {V : Finset (ZMod m × ZMod m)} {yc cc : ℕ → ι → ℤ}
  {Cz : ZMod m → ZMod m → ι → ℤ}
  (T : ColumnTable B p A Bq Dq ω σ τ₀ κ m M J χ γ εs P Q er ψ ρ₀ V yc cc Cz)
include T

theorem P_eq {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) : ∃ l, P r e = γ r l :=
  ((labels_of_image (T.quad r hr).inj (T.lab r hr)).1 e).1

theorem Q_eq {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) : ∃ l, Q r e = γ r l :=
  ((labels_of_image (T.quad r hr).inj (T.lab r hr)).1 e).2

theorem P_mem {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) : P r e ∈ B := by
  obtain ⟨l, hl⟩ := T.P_eq hr e
  rw [hl]
  exact (T.quad r hr).mem l

theorem Q_mem {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) : Q r e ∈ B := by
  obtain ⟨l, hl⟩ := T.Q_eq hr e
  rw [hl]
  exact (T.quad r hr).mem l

theorem P_inj {r t : ℕ} (hr : r ∈ Finset.Ico 1 M) (ht : t ∈ Finset.Ico 1 M) {e e' : Fin 2}
    (h : P r e = P t e') : r = t ∧ e = e' := by
  by_cases hrt : r = t
  · subst hrt
    exact ⟨rfl, (labels_of_image (T.quad r hr).inj (T.lab r hr)).2.1 h⟩
  · obtain ⟨l, hl⟩ := T.P_eq hr e
    obtain ⟨l', hl'⟩ := T.P_eq ht e'
    exact absurd (hl.symm.trans (h.trans hl')) (T.disj r hr t ht hrt l l')

theorem Q_inj {r t : ℕ} (hr : r ∈ Finset.Ico 1 M) (ht : t ∈ Finset.Ico 1 M) {e e' : Fin 2}
    (h : Q r e = Q t e') : r = t ∧ e = e' := by
  by_cases hrt : r = t
  · subst hrt
    exact ⟨rfl, (labels_of_image (T.quad r hr).inj (T.lab r hr)).2.2.1 h⟩
  · obtain ⟨l, hl⟩ := T.Q_eq hr e
    obtain ⟨l', hl'⟩ := T.Q_eq ht e'
    exact absurd (hl.symm.trans (h.trans hl')) (T.disj r hr t ht hrt l l')

theorem P_ne_Q {r t : ℕ} (hr : r ∈ Finset.Ico 1 M) (ht : t ∈ Finset.Ico 1 M) (e e' : Fin 2) :
    P r e ≠ Q t e' := by
  intro h
  by_cases hrt : r = t
  · subst hrt
    exact (labels_of_image (T.quad r hr).inj (T.lab r hr)).2.2.2 e e' h
  · obtain ⟨l, hl⟩ := T.P_eq hr e
    obtain ⟨l', hl'⟩ := T.Q_eq ht e'
    exact T.disj r hr t ht hrt l l' (hl.symm.trans (h.trans hl'))

theorem P_out {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) :
    P r e ≠ p ∧ P r e ≠ A ∧ P r e ≠ Bq ∧ P r e ≠ Dq ∧ P r e ≠ ω ∧ (∀ j ∈ J, P r e ≠ χ j) ∧
      ∀ I ∈ V, P r e ≠ ψ I := by
  obtain ⟨l, hl⟩ := T.P_eq hr e
  obtain ⟨n1, n2, n3, n4, n5⟩ := (T.quad r hr).core l
  rw [hl]
  exact ⟨n1, n2, n3, n4, n5, fun j hj => (T.quad r hr).odd l j hj,
    fun I hI h => (T.gen I hI).2.2.2.2.2.2.2 r hr l h.symm⟩

theorem Q_out {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) :
    Q r e ≠ p ∧ Q r e ≠ A ∧ Q r e ≠ Bq ∧ Q r e ≠ Dq ∧ Q r e ≠ ω ∧ (∀ j ∈ J, Q r e ≠ χ j) ∧
      ∀ I ∈ V, Q r e ≠ ψ I := by
  obtain ⟨l, hl⟩ := T.Q_eq hr e
  obtain ⟨n1, n2, n3, n4, n5⟩ := (T.quad r hr).core l
  rw [hl]
  exact ⟨n1, n2, n3, n4, n5, fun j hj => (T.quad r hr).odd l j hj,
    fun I hI h => (T.gen I hI).2.2.2.2.2.2.2 r hr l h.symm⟩

theorem rowA (I : ZMod m × ZMod m) (hI : I ≠ (0, 0)) : Cz I.1 I.2 A = -σ := by
  rw [T.rep.row_const T.core.hA T.core.hBA.symm T.core.hDA.symm
    (fun r hr e => ⟨((T.P_out hr e).2.1).symm, ((T.Q_out hr e).2.1).symm⟩)
    (fun I' hI' => ((T.gen I' hI').2.2.1).symm) I hI]
  simp [baseFixed, unitVector, T.core.hAp, T.core.hωA.symm]

theorem rowω (I : ZMod m × ZMod m) (hI : I ≠ (0, 0)) : Cz I.1 I.2 ω = 2 * τ₀ := by
  rw [T.rep.row_const T.core.hω T.core.hωB T.core.hωD
    (fun r hr e => ⟨((T.P_out hr e).2.2.2.2.1).symm, ((T.Q_out hr e).2.2.2.2.1).symm⟩)
    (fun I' hI' => ((T.gen I' hI').2.2.2.2.2.1).symm) I hI]
  simp [baseFixed, unitVector, T.core.hωp, T.core.hωA]

theorem rowB (I : ZMod m × ZMod m) : Cz I.1 I.2 Bq =
    if I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) then -τ₀ else 0 :=
  T.rep.row_single T.core.hBq
    (by simp [baseFixed, unitVector, T.core.hBp, T.core.hBA, T.core.hωB.symm])
    ((M : ZMod m), (M : ZMod m)) (-τ₀)
    (by
      rw [T.rep.mid _ T.core.hBq]
      simp [baseFixed, unitVector, T.core.hBp, T.core.hBA, T.core.hωB.symm, T.core.hDB.symm])
    (fun _ => rfl)
    (fun r hr h => absurd (by simp [unitVector, ((T.P_out hr _).2.2.1).symm,
      ((T.Q_out hr _).2.2.1).symm]) h)
    (fun r hr h => absurd (by simp [unitVector, ((T.P_out hr _).2.2.1).symm,
      ((T.Q_out hr _).2.2.1).symm]) h)
    (fun I' hI' h => absurd (by simp [unitVector, ((T.gen I' hI').2.2.2.1).symm]) h) I

theorem rowD (I : ZMod m × ZMod m) : Cz I.1 I.2 Dq =
    if I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) then -κ else 0 :=
  T.rep.row_single T.core.hDq
    (by simp [baseFixed, unitVector, T.core.hDp, T.core.hDA, T.core.hωD.symm])
    ((M : ZMod m), (M : ZMod m)) (-κ)
    (by
      rw [T.rep.mid _ T.core.hDq]
      simp [baseFixed, unitVector, T.core.hDp, T.core.hDA, T.core.hωD.symm, T.core.hDB])
    (fun _ => rfl)
    (fun r hr h => absurd (by simp [unitVector, ((T.P_out hr _).2.2.2.1).symm,
      ((T.Q_out hr _).2.2.2.1).symm]) h)
    (fun r hr h => absurd (by simp [unitVector, ((T.P_out hr _).2.2.2.1).symm,
      ((T.Q_out hr _).2.2.2.1).symm]) h)
    (fun I' hI' h => absurd (by simp [unitVector, ((T.gen I' hI').2.2.2.2.1).symm]) h) I

theorem rowχ {h : ℕ} (hh : h ∈ J) (I : ZMod m × ZMod m) : Cz I.1 I.2 (χ h) = 0 := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := T.core.hχcore h hh
  by_cases hI : I = (0, 0)
  · subst hI
    exact T.rep.zero _ (T.core.hχB h hh)
  rw [T.rep.row_const (T.core.hχB h hh) n3 n4 (fun r hr e =>
      ⟨fun e' => (T.P_out hr e).2.2.2.2.2.1 h hh e'.symm,
        fun e' => (T.Q_out hr e).2.2.2.2.2.1 h hh e'.symm⟩)
    (fun I' hI' e => (T.gen I' hI').2.2.2.2.2.2.1 h hh e.symm) I hI]
  simp [baseFixed, unitVector, n1, n2, n5]

theorem rowP {t : ℕ} (ht : t ∈ Finset.Ico 1 M) (e : Fin 2) (I : ZMod m × ZMod m) :
    Cz I.1 I.2 (P t e) =
      if I ∈ MulAction.orbit (dualGroup m) (labelRep m M er t e) then -τ₀ else 0 := by
  obtain ⟨n1, n2, n3, n4, n5, -, n7⟩ := T.P_out ht e
  have hPB := T.P_mem ht e
  refine T.rep.row_single hPB (by simp [baseFixed, unitVector, n1, n2, n5])
    (labelRep m M er t e) (-τ₀) ?_ (fun h => absurd (by simp [unitVector, n3, n4]) h)
    (fun r hr h => ?_) (fun r hr h => ?_)
    (fun I' hI' h => absurd (by simp [unitVector, n7 I' hI']) h) I
  · by_cases he : e = er t
    · simp only [labelRep, ite_eq_left he]
      rw [T.rep.diag t ht _ hPB, ← he]
      simp [baseFixed, unitVector, n1, n2, n5, T.P_ne_Q ht ht e e]
    · simp only [labelRep, ite_eq_right he]
      rw [T.rep.diag' t ht _ hPB, ← fin_two_eq_one_sub he]
      simp [baseFixed, unitVector, n1, n2, n5, T.P_ne_Q ht ht e e]
  · have hP : P t e = P r (er r) := by
      by_contra hne
      exact h (by simp [unitVector, hne, T.P_ne_Q ht hr e (er r)])
    obtain ⟨rfl, rfl⟩ := T.P_inj ht hr hP
    simp [labelRep]
  · have hP : P t e = P r (1 - er r) := by
      by_contra hne
      exact h (by simp [unitVector, hne, T.P_ne_Q ht hr e (1 - er r)])
    obtain ⟨rfl, rfl⟩ := T.P_inj ht hr hP
    simp [labelRep, ite_eq_right (fin_two_one_sub_ne (er t))]

theorem rowQ {t : ℕ} (ht : t ∈ Finset.Ico 1 M) (e : Fin 2) (I : ZMod m × ZMod m) :
    Cz I.1 I.2 (Q t e) =
      if I ∈ MulAction.orbit (dualGroup m) (labelRep m M er t e) then -κ else 0 := by
  obtain ⟨n1, n2, n3, n4, n5, -, n7⟩ := T.Q_out ht e
  have hQB := T.Q_mem ht e
  have hQP : ∀ r ∈ Finset.Ico 1 M, ∀ e', Q t e ≠ P r e' := fun r hr e' h =>
    T.P_ne_Q hr ht e' e h.symm
  refine T.rep.row_single hQB (by simp [baseFixed, unitVector, n1, n2, n5])
    (labelRep m M er t e) (-κ) ?_ (fun h => absurd (by simp [unitVector, n3, n4]) h)
    (fun r hr h => ?_) (fun r hr h => ?_)
    (fun I' hI' h => absurd (by simp [unitVector, n7 I' hI']) h) I
  · by_cases he : e = er t
    · simp only [labelRep, ite_eq_left he]
      rw [T.rep.diag t ht _ hQB, ← he]
      simp [baseFixed, unitVector, n1, n2, n5, hQP t ht e]
    · simp only [labelRep, ite_eq_right he]
      rw [T.rep.diag' t ht _ hQB, ← fin_two_eq_one_sub he]
      simp [baseFixed, unitVector, n1, n2, n5, hQP t ht e]
  · have hQ' : Q t e = Q r (er r) := by
      by_contra hne
      exact h (by simp [unitVector, hne, hQP r hr (er r)])
    obtain ⟨rfl, rfl⟩ := T.Q_inj ht hr hQ'
    simp [labelRep]
  · have hQ' : Q t e = Q r (1 - er r) := by
      by_contra hne
      exact h (by simp [unitVector, hne, hQP r hr (1 - er r)])
    obtain ⟨rfl, rfl⟩ := T.Q_inj ht hr hQ'
    simp [labelRep, ite_eq_right (fin_two_one_sub_ne (er t))]

theorem rowψ {I : ZMod m × ZMod m} (hI : I ∈ V) (I' : ZMod m × ZMod m) :
    Cz I'.1 I'.2 (ψ I) = if I' ∈ MulAction.orbit (dualGroup m) I then ρ₀ else 0 := by
  obtain ⟨hψB, n1, n2, n3, n4, n5, -, -⟩ := T.gen I hI
  refine T.rep.row_single hψB (by simp [baseFixed, unitVector, n1, n2, n5]) I ρ₀
    (by rw [T.rep.gen I hI _ hψB]; simp [baseFixed, unitVector, n1, n2, n5])
    (fun h => absurd (by simp [unitVector, n3, n4]) h)
    (fun r hr h => absurd (by simp [unitVector, (T.P_out hr _).2.2.2.2.2.2 I hI,
      (T.Q_out hr _).2.2.2.2.2.2 I hI, Ne.symm]) h)
    (fun r hr h => absurd (by simp [unitVector, (T.P_out hr _).2.2.2.2.2.2 I hI,
      (T.Q_out hr _).2.2.2.2.2.2 I hI, Ne.symm]) h)
    (fun I'' hI'' h => ?_) I'
  by_contra hne
  have hne' : ψ I ≠ ψ I'' := fun e => hne (T.geninj hI'' hI e.symm)
  exact h (by simp [unitVector, hne'])

theorem xcore {φ : ι} (hφ : φ ∈ B) (hχ : ∀ j ∈ J, φ ≠ χ j)
    (hγ : ∀ r ∈ Finset.Ico 1 M, ∀ l, φ ≠ γ r l) (j : ℕ) (hj : j ∈ Finset.Ico 1 m) :
    cc j φ = fixedPart p A Bq Dq σ τ₀ κ φ :=
  xrow_core T.core T.hm T.hJ T.quad hφ hχ hγ j hj

theorem xA (j : ℕ) (hj : j ∈ Finset.Ico 1 m) : cc j A = -σ := by
  rw [T.xcore T.core.hA (fun j hj => ((T.core.hχcore j hj).2.1).symm)
    (fun r hr l => (((T.quad r hr).core l).2.1).symm) j hj]
  simp [fixedPart, unitVector, T.core.hAp, T.core.hBA.symm, T.core.hDA.symm]

theorem xB (j : ℕ) (hj : j ∈ Finset.Ico 1 m) : cc j Bq = -τ₀ := by
  rw [T.xcore T.core.hBq (fun j hj => ((T.core.hχcore j hj).2.2.1).symm)
    (fun r hr l => (((T.quad r hr).core l).2.2.1).symm) j hj]
  simp [fixedPart, unitVector, T.core.hBp, T.core.hBA, T.core.hDB.symm]

theorem xD (j : ℕ) (hj : j ∈ Finset.Ico 1 m) : cc j Dq = κ := by
  rw [T.xcore T.core.hDq (fun j hj => ((T.core.hχcore j hj).2.2.2.1).symm)
    (fun r hr l => (((T.quad r hr).core l).2.2.2.1).symm) j hj]
  simp [fixedPart, unitVector, T.core.hDp, T.core.hDA, T.core.hDB]

theorem xω (j : ℕ) (hj : j ∈ Finset.Ico 1 m) : cc j ω = 0 := by
  rw [T.xcore T.core.hω (fun j hj => ((T.core.hχcore j hj).2.2.2.2).symm)
    (fun r hr l => (((T.quad r hr).core l).2.2.2.2).symm) j hj]
  simp [fixedPart, unitVector, T.core.hωp, T.core.hωA, T.core.hωB, T.core.hωD]

theorem xψ {I : ZMod m × ZMod m} (hI : I ∈ V) (j : ℕ) (hj : j ∈ Finset.Ico 1 m) :
    cc j (ψ I) = 0 := by
  obtain ⟨hψB, n1, n2, n3, n4, -, n6, n7⟩ := T.gen I hI
  rw [T.xcore hψB n6 n7 j hj]
  simp [fixedPart, unitVector, n1, n2, n3, n4]

theorem xP {t : ℕ} (ht : t ∈ Finset.Ico 1 M) (e : Fin 2) (j : ℕ) (hj : j ∈ Finset.Ico 1 m) :
    cc j (P t e) = if j = m - 2 * t then τ₀ else 0 := by
  obtain ⟨l, hl⟩ := T.P_eq ht e
  obtain ⟨n1, n2, n3, n4, -⟩ := (T.quad t ht).core l
  have hval : cc (m - 2 * t) (P t e) = τ₀ := by
    rw [T.xpq t ht _ (T.P_mem ht e), hl, fixedPart_of_ne σ τ₀ κ n1 n2 n3 n4, ← hl]
    have h01 : P t 0 ≠ P t 1 := fun h => absurd (T.P_inj ht ht h).2 (by decide)
    fin_cases e <;>
      simp [unitVector, h01, h01.symm, T.P_ne_Q ht ht 0 0, T.P_ne_Q ht ht 0 1,
        T.P_ne_Q ht ht 1 0, T.P_ne_Q ht ht 1 1]
  have hε : εs t l = τ₀ := by
    rw [← (T.quad t ht).xk_apply l, ← hl, hval]
  rw [hl, xrow_even T.core T.hm T.hJ T.quad T.disj ht l j hj, hε]

theorem xQ {t : ℕ} (ht : t ∈ Finset.Ico 1 M) (e : Fin 2) (j : ℕ) (hj : j ∈ Finset.Ico 1 m) :
    cc j (Q t e) = if j = m - 2 * t then -κ else 0 := by
  obtain ⟨l, hl⟩ := T.Q_eq ht e
  obtain ⟨n1, n2, n3, n4, -⟩ := (T.quad t ht).core l
  have hval : cc (m - 2 * t) (Q t e) = -κ := by
    rw [T.xpq t ht _ (T.Q_mem ht e), hl, fixedPart_of_ne σ τ₀ κ n1 n2 n3 n4, ← hl]
    have h01 : Q t 0 ≠ Q t 1 := fun h => absurd (T.Q_inj ht ht h).2 (by decide)
    have hQP : ∀ e'' e''', Q t e'' ≠ P t e''' := fun e'' e''' h =>
      T.P_ne_Q ht ht e''' e'' h.symm
    fin_cases e <;>
      simp [unitVector, h01, h01.symm, hQP 0 0, hQP 0 1, hQP 1 0, hQP 1 1]
  have hε : εs t l = -κ := by
    rw [← (T.quad t ht).xk_apply l, ← hl, hval]
  rw [hl, xrow_even T.core T.hm T.hJ T.quad T.disj ht l j hj, hε]

theorem sum_y0_mul (F : ι → ℂ) :
    ∑ φ ∈ B, (yc 0 φ : ℂ) * F φ = F p + σ * F A - τ₀ * F Bq + κ * F Dq := by
  calc ∑ φ ∈ B, (yc 0 φ : ℂ) * F φ = ∑ φ ∈ B, ((1 * unitVector p φ + σ * unitVector A φ +
        (-τ₀) * unitVector Bq φ + κ * unitVector Dq φ : ℤ) : ℂ) * F φ :=
        Finset.sum_congr rfl fun φ hφ => by rw [T.core.hy₀ φ hφ]; push_cast; ring
    _ = F p + σ * F A - τ₀ * F Bq + κ * F Dq := by
        rw [sum_cast_four_mul T.core.hp T.core.hA T.core.hBq T.core.hDq]
        push_cast
        ring

theorem sum_x_mul {t : ℕ} (ht : t ∈ Finset.Ico 1 M) (F : ι → ℂ) :
    ∑ φ ∈ B, (cc (m - 2 * t) φ : ℂ) * F φ = -F p - σ * F A - τ₀ * F Bq + κ * F Dq +
      τ₀ * (F (P t 0) + F (P t 1)) - κ * (F (Q t 0) + F (Q t 1)) := by
  rw [Finset.sum_congr rfl fun φ hφ =>
    congrArg (fun z : ℤ => (z : ℂ) * F φ) (T.xpq t ht φ hφ)]
  simp only [Int.cast_add, add_mul, Finset.sum_add_distrib]
  rw [sum_cast_fixedPart_mul T.core.hp T.core.hA T.core.hBq T.core.hDq]
  have h4 := sum_cast_four_mul (B := B) (T.P_mem ht 0) (T.P_mem ht 1) (T.Q_mem ht 0)
    (T.Q_mem ht 1) τ₀ τ₀ (-κ) (-κ) F
  simp only [Int.cast_add, add_mul, Finset.sum_add_distrib] at h4
  rw [h4]
  push_cast
  ring

end ColumnTable

end CFSG.Wreathed.ConditionalGlobalDegrees
