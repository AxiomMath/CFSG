module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCoresAbstract
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCores

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll mem_fixAll centralizerPerfectCore_eq_map_of_le)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped commutatorElement

section Supp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def IsSuppMat (S : Set ι) (M : Matrix ι ι F) : Prop :=
  ∀ a b, ¬(a ∈ S ∧ b ∈ S) → M a b = (1 : Matrix ι ι F) a b

theorem IsSuppMat.mul {S : Set ι} {M N : Matrix ι ι F} (hM : IsSuppMat S M)
    (hN : IsSuppMat S N) : IsSuppMat S (M * N) := by
  intro r t hrt
  rcases not_and_or.1 hrt with hr | ht
  · have h : ∀ u, M r u = (1 : Matrix ι ι F) r u := fun u => hM r u (fun h => hr h.1)
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [h u]), ← Matrix.mul_apply,
      Matrix.one_mul]
    exact hN r t (fun h => hr h.1)
  · have h : ∀ u, N u t = (1 : Matrix ι ι F) u t := fun u => hN u t (fun h => ht h.2)
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [h u]), ← Matrix.mul_apply,
      Matrix.mul_one]
    exact hM r t (fun h => ht h.2)

theorem IsSuppMat.of_mul_eq_one {S : Set ι} {M N : Matrix ι ι F} (hM : IsSuppMat S M)
    (hNM : N * M = 1) (hMN : M * N = 1) : IsSuppMat S N := by
  intro r t hrt
  rcases not_and_or.1 hrt with hr | ht
  · have h : ∀ u, M r u = (1 : Matrix ι ι F) r u := fun u => hM r u (fun h => hr h.1)
    have e : (M * N) r t = N r t := by
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [h u]), ← Matrix.mul_apply,
        Matrix.one_mul]
    rw [← e, hMN]
  · have h : ∀ u, M u t = (1 : Matrix ι ι F) u t := fun u => hM u t (fun h => ht h.2)
    have e : (N * M) r t = N r t := by
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [h u]), ← Matrix.mul_apply,
        Matrix.mul_one]
    rw [← e, hNM]

variable (F) in
@[expose] def suppGL (S : Set ι) : Subgroup (GL ι F) where
  carrier := {x | IsSuppMat S (x : Matrix ι ι F)}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {x y} hx hy => by
    change IsSuppMat S ((x * y : GL ι F) : Matrix ι ι F)
    rw [Units.val_mul]
    exact IsSuppMat.mul hx hy
  inv_mem' := fun {x} hx => by
    change IsSuppMat S ((x⁻¹ : GL ι F) : Matrix ι ι F)
    exact IsSuppMat.of_mul_eq_one hx (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])

theorem mem_suppGL {S : Set ι} {x : GL ι F} :
    x ∈ suppGL F S ↔ IsSuppMat S (x : Matrix ι ι F) :=
  Iff.rfl

theorem suppGL_mono {S T : Set ι} (h : S ⊆ T) : suppGL F S ≤ suppGL F T :=
  fun _ hx r t hrt => hx r t fun h' => hrt ⟨h h'.1, h h'.2⟩

end Supp

section Levi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem commutator_le_suppGL {S : Set ι} {H : Subgroup (GL ι F)}
    (hH : ∀ x ∈ H, ∀ a ∉ S, ∀ b, b ≠ a →
      (x : Matrix ι ι F) a b = 0 ∧ (x : Matrix ι ι F) b a = 0) :
    ⁅H, H⁆ ≤ suppGL F S := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hrow : ∀ x ∈ H, ∀ y : GL ι F, ∀ a ∉ S, ∀ b,
      ((x * y : GL ι F) : Matrix ι ι F) a b = (x : Matrix ι ι F) a a * (y : Matrix ι ι F) a b :=
    fun x hx y a ha b => by
      rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a
        (fun c _ hc => by rw [(hH x hx a ha c hc).1, zero_mul])
        (fun h' => absurd (Finset.mem_univ a) h')]
  have hcol : ∀ x : GL ι F, ∀ y ∈ H, ∀ a ∉ S, ∀ b,
      ((x * y : GL ι F) : Matrix ι ι F) b a = (x : Matrix ι ι F) b a * (y : Matrix ι ι F) a a :=
    fun x y hy a ha b => by
      rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a
        (fun c _ hc => by rw [(hH y hy a ha c hc).2, mul_zero])
        (fun h' => absurd (Finset.mem_univ a) h')]
  have hinv : ∀ x ∈ H, ∀ a ∉ S,
      (x : Matrix ι ι F) a a * ((x⁻¹ : GL ι F) : Matrix ι ι F) a a = 1 := fun x hx a ha => by
    rw [← hrow x hx x⁻¹ a ha a, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  have hc : ⁅g, h⁆ = g * h * g⁻¹ * h⁻¹ := commutatorElement_def g h
  have hghg : g * h * g⁻¹ ∈ H := mul_mem (mul_mem hg hh) (inv_mem hg)
  have hdiag : ∀ a ∉ S, (g : Matrix ι ι F) a a * (h : Matrix ι ι F) a a *
      ((g⁻¹ : GL ι F) : Matrix ι ι F) a a * ((h⁻¹ : GL ι F) : Matrix ι ι F) a a = 1 :=
    fun a ha => by
      calc _ = ((g : Matrix ι ι F) a a * ((g⁻¹ : GL ι F) : Matrix ι ι F) a a) *
            ((h : Matrix ι ι F) a a * ((h⁻¹ : GL ι F) : Matrix ι ι F) a a) := by ring
        _ = 1 := by rw [hinv g hg a ha, hinv h hh a ha, one_mul]
  have hr : ∀ a ∉ S, ∀ b, ((⁅g, h⁆ : GL ι F) : Matrix ι ι F) a b =
      (g : Matrix ι ι F) a a * (h : Matrix ι ι F) a a * ((g⁻¹ : GL ι F) : Matrix ι ι F) a a *
        ((h⁻¹ : GL ι F) : Matrix ι ι F) a b := fun a ha b => by
    rw [hc, hrow _ hghg _ a ha, hrow _ (mul_mem hg hh) _ a ha, hrow _ hg _ a ha]
  have hcl : ∀ a ∉ S, ∀ b, ((⁅g, h⁆ : GL ι F) : Matrix ι ι F) b a =
      (g : Matrix ι ι F) b a * (h : Matrix ι ι F) a a * ((g⁻¹ : GL ι F) : Matrix ι ι F) a a *
        ((h⁻¹ : GL ι F) : Matrix ι ι F) a a := fun a ha b => by
    rw [hc, hcol _ _ (inv_mem hh) a ha, hcol _ _ (inv_mem hg) a ha, hcol _ _ hh a ha]
  intro r t hrt
  by_cases hrS : r ∈ S
  · have htS : t ∉ S := fun htS => hrt ⟨hrS, htS⟩
    rw [hcl t htS r]
    by_cases hrt' : r = t
    · subst hrt'
      exact absurd hrS htS
    · rw [(hH g hg t htS r hrt').2, zero_mul, zero_mul, zero_mul, Matrix.one_apply_ne hrt']
  · rw [hr r hrS t]
    by_cases hrt' : t = r
    · subst hrt'
      rw [hdiag t hrS, Matrix.one_apply_eq]
    · rw [(hH _ (inv_mem hh) r hrS t hrt').1, mul_zero, Matrix.one_apply_ne (Ne.symm hrt')]

theorem commute_of_diag_iff {d : GL ι F} (hd : ∀ a b, a ≠ b → (d : Matrix ι ι F) a b = 0)
    (x : GL ι F) :
    Commute x d ↔ ∀ a b, (d : Matrix ι ι F) a a ≠ (d : Matrix ι ι F) b b →
      (x : Matrix ι ι F) a b = 0 := by
  set w : ι → F := fun a => (d : Matrix ι ι F) a a with hw
  have hdd : (d : Matrix ι ι F) = diagonal w := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [diagonal_apply_eq]
    · rw [hd a b hab, diagonal_apply_ne _ hab]
  constructor
  · intro h a b hab
    have h1 : (x : Matrix ι ι F) * (d : Matrix ι ι F) =
        (d : Matrix ι ι F) * (x : Matrix ι ι F) := by
      rw [← Units.val_mul, ← Units.val_mul, h.eq]
    rw [hdd] at h1
    exact (matrix_mul_diagonal_comm_iff _ w).1 h1 a b hab
  · intro h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hdd]
    exact (matrix_mul_diagonal_comm_iff _ w).2 h

theorem mat_eq_zero_of_mem_inf_centralizer {H : Subgroup (GL ι F)} {S T : Set ι}
    (hHT : H ≤ suppGL F T) {D : Set (GL ι F)}
    (hdiag : ∀ d ∈ D, ∀ a b, a ≠ b → (d : Matrix ι ι F) a b = 0)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (a ∉ S ∨ b ∉ S) →
      ∃ d ∈ D, (d : Matrix ι ι F) a a ≠ (d : Matrix ι ι F) b b)
    {x : GL ι F} (hx : x ∈ H ⊓ centralizer D) {a : ι} (ha : a ∉ S) {b : ι} (hba : b ≠ a) :
    (x : Matrix ι ι F) a b = 0 ∧ (x : Matrix ι ι F) b a = 0 := by
  obtain ⟨hxH, hxD⟩ := mem_inf.1 hx
  by_cases hT : a ∈ T ∧ b ∈ T
  · obtain ⟨d, hd, hne⟩ := hsep a hT.1 b hT.2 hba.symm (Or.inl ha)
    have hc : Commute x d := ((mem_centralizer_iff.1 hxD) d hd).symm
    exact ⟨(commute_of_diag_iff (hdiag d hd) x).1 hc a b hne,
      (commute_of_diag_iff (hdiag d hd) x).1 hc b a (Ne.symm hne)⟩
  · refine ⟨?_, ?_⟩
    · rw [hHT hxH a b hT, Matrix.one_apply_ne hba.symm]
    · rw [hHT hxH b a (fun h => hT ⟨h.2, h.1⟩), Matrix.one_apply_ne hba]

theorem perfectCore_inf_centralizer_eq_perfectCore_inf_suppGL [Finite F]
    {H : Subgroup (GL ι F)} {S T : Set ι} (hHT : H ≤ suppGL F T) (D : Set (GL ι F))
    (hdiag : ∀ d ∈ D, ∀ a b, a ≠ b → (d : Matrix ι ι F) a b = 0)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (a ∉ S ∨ b ∉ S) →
      ∃ d ∈ D, (d : Matrix ι ι F) a a ≠ (d : Matrix ι ι F) b b) :
    perfectCore (H ⊓ centralizer D) = perfectCore (H ⊓ suppGL F S ⊓ centralizer D) := by
  have : Finite (GL ι F) := inferInstance
  refine (LinearPilot.perfectCore_eq_of_le_of_commutator_le
    (inf_le_inf_right _ inf_le_left) ?_).trans rfl
  refine le_inf (le_inf ((commutator_le_self _).trans inf_le_left) ?_)
    ((commutator_le_self _).trans inf_le_right)
  exact commutator_le_suppGL fun x hx a ha b hba =>
    mat_eq_zero_of_mem_inf_centralizer hHT hdiag hsep hx ha hba

end Levi

end CFSG.SeitzReduction.SymplecticPilot
