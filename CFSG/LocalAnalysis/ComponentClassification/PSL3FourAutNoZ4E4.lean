module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Model
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def noZ4E4OK (TR : List ℕ) : Bool :=
  let I := TR.filter fun t => isId (psq t)
  TR.all fun y =>
    let y2 := psq y
    !(isId (psq y2) && !(isId y2)) ||
      (let Iy := I.filter fun t => commC t y
       Iy.all fun b => isId b || Nat.beq b y2 ||
         (let y2b := pcomp y2 b
          Iy.all fun c => !(commC b c) || isId c || Nat.beq c y2 || Nat.beq c b ||
            Nat.beq c y2b))

theorem noZ4E4OK_trL : noZ4E4OK (trL t0L) = true := by decide +kernel

theorem noZ4E4_TR {a b c : Equiv.Perm (Fin 42)} (ha : a ∈ TR)
    (hb : b ∈ TR) (hc : c ∈ TR) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (ha4 : a ^ 4 = 1) (hb2 : b ^ 2 = 1) (hc2 : c ^ 2 = 1) :
    a ^ 2 = 1 ∨ b = 1 ∨ b = a ^ 2 ∨ c = 1 ∨ c = a ^ 2 ∨ c = b ∨ c = a ^ 2 * b := by
  have h := noZ4E4OK_trL
  simp only [noZ4E4OK, List.all_eq_true] at h
  have haL : code a ∈ trL t0L := (mem_TR_iff_code a).1 ha
  have h1 := h (code a) haL
  have h4 : a ^ 4 = a * a * (a * a) := by
    rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul, pow_two, pow_two]
  have ha4' : a * a * (a * a) = 1 := by rw [← h4, ha4]
  have hA : isId (psq (psq (code a))) = true := by
    rw [psq_psq_code, isId_iff]; exact ha4'
  simp only [hA, Bool.true_and, Bool.not_not, Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · left
    rw [psq_code, isId_iff] at h1
    rwa [pow_two]
  · rw [List.all_eq_true] at h1
    have hb2' : b * b = 1 := by rwa [pow_two] at hb2
    have hbI : code b ∈ ((trL t0L).filter (fun t => isId (psq t))).filter
        (fun t => commC t (code a)) :=
      List.mem_filter.2 ⟨List.mem_filter.2 ⟨(mem_TR_iff_code b).1 hb, (sq_iff b).2 hb2'⟩,
        (commC_iff b a).2 hab.symm⟩
    have h2 := h1 (code b) hbI
    simp only [Bool.or_eq_true] at h2
    rcases h2 with (h2 | h2) | h2
    · right; left
      rwa [isId_iff] at h2
    · right; right; left
      rw [Nat.beq_eq, psq_code, code_inj] at h2
      rwa [pow_two]
    · rw [List.all_eq_true] at h2
      have hc2' : c * c = 1 := by rwa [pow_two] at hc2
      have hcI : code c ∈ ((trL t0L).filter (fun t => isId (psq t))).filter
          (fun t => commC t (code a)) :=
        List.mem_filter.2 ⟨List.mem_filter.2 ⟨(mem_TR_iff_code c).1 hc, (sq_iff c).2 hc2'⟩,
          (commC_iff c a).2 hac.symm⟩
      have h3 := h2 (code c) hcI
      have hbcC : commC (code b) (code c) = true := (commC_iff b c).2 hbc
      simp only [hbcC, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h3
      rcases h3 with ((h3 | h3) | h3) | h3
      · right; right; right; left
        rwa [isId_iff] at h3
      · right; right; right; right; left
        rw [Nat.beq_eq, psq_code, code_inj] at h3
        rwa [pow_two]
      · right; right; right; right; right; left
        rwa [Nat.beq_eq, code_inj] at h3
      · right; right; right; right; right; right
        rw [Nat.beq_eq, psq_code, ← code_mul, code_inj] at h3
        rwa [pow_two]

theorem noZ4E4_R
    {a b c : Equiv.Perm (Fin 42)} (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) (ha4 : a ^ 4 = 1) (hb2 : b ^ 2 = 1)
    (hc2 : c ^ 2 = 1) :
    a ^ 2 = 1 ∨ b = 1 ∨ b = a ^ 2 ∨ c = 1 ∨ c = a ^ 2 ∨ c = b ∨ c = a ^ 2 * b := by
  let X : Subgroup (Equiv.Perm (Fin 42)) :=
    Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 42)))
  have hXR : X ≤ R := by
    change Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 42))) ≤ R
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hc
  have hXc : IsMulCommutative X :=
    Subgroup.isMulCommutative_closure (k := ({a, b, c} : Set (Equiv.Perm (Fin 42)))) (by
      intro x hx y hy _
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact Commute.refl _
      · exact hab
      · exact hac
      · exact hab.symm
      · exact Commute.refl _
      · exact hbc
      · exact hac.symm
      · exact hbc.symm
      · exact Commute.refl _)
  have hb4 : b ^ 4 = 1 := by
    have h : b ^ 4 = b ^ 2 * b ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul, pow_two]
    rw [h, hb2, one_mul]
  have hc4 : c ^ 4 = 1 := by
    have h : c ^ 4 = c ^ 2 * c ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul, pow_two]
    rw [h, hc2, one_mul]
  have h4 : ∀ x ∈ X, x ^ 4 = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => y ^ 4 = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl | rfl | rfl
      · exact ha4
      · exact hb4
      · exact hc4
    · exact one_pow 4
    · intro y z hy hz ihy ihz
      have hyz : y * z = z * y :=
        Subgroup.mul_comm_of_mem_isMulCommutative (H := X) (a := y) (b := z) hy hz
      rw [Commute.mul_pow (show Commute y z from hyz) 4, ihy, ihz, one_mul]
    · intro y hy ihy
      rw [inv_pow, ihy, inv_one]
  have hX : IsPGroup 2 X := fun x => ⟨2, by
    have h := h4 (x : Equiv.Perm (Fin 42)) x.2
    rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]
    exact Subtype.ext (by simpa using h)⟩
  obtain ⟨g, -, hg⟩ := exists_conj_mem_TR hXR hX
  have haX : a ∈ X := Subgroup.subset_closure (by simp)
  have hbX : b ∈ X := Subgroup.subset_closure (by simp)
  have hcX : c ∈ X := Subgroup.subset_closure (by simp)
  have h := noZ4E4_TR (a := MulAut.conj g a) (b := MulAut.conj g b) (c := MulAut.conj g c)
    (by simpa [MulAut.conj_apply] using hg a haX)
    (by simpa [MulAut.conj_apply] using hg b hbX)
    (by simpa [MulAut.conj_apply] using hg c hcX)
    (by rw [← map_mul (MulAut.conj g) a b, ← map_mul (MulAut.conj g) b a, hab])
    (by rw [← map_mul (MulAut.conj g) a c, ← map_mul (MulAut.conj g) c a, hac])
    (by rw [← map_mul (MulAut.conj g) b c, ← map_mul (MulAut.conj g) c b, hbc])
    (by rw [← map_pow (MulAut.conj g) a 4, ha4, map_one (MulAut.conj g)])
    (by rw [← map_pow (MulAut.conj g) b 2, hb2, map_one (MulAut.conj g)])
    (by rw [← map_pow (MulAut.conj g) c 2, hc2, map_one (MulAut.conj g)])
  rcases h with h | h | h | h | h | h | h
  · left
    apply MulEquiv.injective (MulAut.conj g)
    rw [map_pow, map_one]
    exact h
  · right; left
    apply MulEquiv.injective (MulAut.conj g)
    rw [map_one]
    exact h
  · right; right; left
    apply MulEquiv.injective (MulAut.conj g)
    rw [map_pow]
    exact h
  · right; right; right; left
    apply MulEquiv.injective (MulAut.conj g)
    rw [map_one]
    exact h
  · right; right; right; right; left
    apply MulEquiv.injective (MulAut.conj g)
    rw [map_pow]
    exact h
  · right; right; right; right; right; left
    exact MulEquiv.injective (MulAut.conj g) h
  · right; right; right; right; right; right
    apply MulEquiv.injective (MulAut.conj g)
    rw [map_mul, map_pow]
    exact h

end CFSG.ComponentClassification.HSFLit.AutL34

namespace CFSG.ComponentClassification.PSL3Four

theorem mulAut_noZ4E4
    {X : Type*} [Group X] (eX : X ≃* S) {a b c : MulAut X} (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) (ha4 : a ^ 4 = 1) (hb2 : b ^ 2 = 1)
    (hc2 : c ^ 2 = 1) :
    a ^ 2 = 1 ∨ b = 1 ∨ b = a ^ 2 ∨ c = 1 ∨ c = a ^ 2 ∨ c = b ∨ c = a ^ 2 * b := by
  obtain ⟨e, -, -⟩ := full_automorphism_action
  let ψ : MulAut X ≃* R := (MulAut.congr eX).trans e.symm
  let φ : MulAut X →* Equiv.Perm (Fin 42) := R.subtype.comp ψ.toMonoidHom
  have hinj : Function.Injective φ := by
    intro x y h
    exact (MulEquiv.injective (MulAut.congr eX))
      ((MulEquiv.injective e.symm) ((Subgroup.subtype_injective R) h))
  have haR : φ a ∈ R := (ψ a).2
  have hbR : φ b ∈ R := (ψ b).2
  have hcR : φ c ∈ R := (ψ c).2
  have h := CFSG.ComponentClassification.HSFLit.AutL34.noZ4E4_R (a := φ a) (b := φ b)
    (c := φ c) haR hbR hcR
    (by rw [← map_mul φ a b, ← map_mul φ b a, hab])
    (by rw [← map_mul φ a c, ← map_mul φ c a, hac])
    (by rw [← map_mul φ b c, ← map_mul φ c b, hbc])
    (by rw [← map_pow φ a 4, ha4, map_one φ])
    (by rw [← map_pow φ b 2, hb2, map_one φ])
    (by rw [← map_pow φ c 2, hc2, map_one φ])
  rcases h with h | h | h | h | h | h | h
  · left
    apply hinj
    rw [map_pow, h, map_one]
  · right; left
    apply hinj
    rw [h, map_one]
  · right; right; left
    apply hinj
    rw [map_pow]
    exact h
  · right; right; right; left
    apply hinj
    rw [h, map_one]
  · right; right; right; right; left
    apply hinj
    rw [map_pow]
    exact h
  · right; right; right; right; right; left
    apply hinj
    exact h
  · right; right; right; right; right; right
    apply hinj
    rw [map_mul, map_pow]
    exact h

end CFSG.ComponentClassification.PSL3Four
