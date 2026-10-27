module

public import CFSG.HardMathSupport.U4FF.ClassDatumOpp
public import CFSG.LieType.Universal.Unitary.Roots.Generation
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.HardMathSupport.U4FF.ClassDatumRank

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU rootHom longRootHom rootMatrix
  longRootMatrix traceZero mem_traceZero coe_rootHom coe_longRootHom eq_top_of_rootElements_le)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)

namespace Datum

section Generation

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem rootMatrix_entries_upper : ∀ i j a b : Fin 4, i < j → b < a →
    a ≠ b ∧ ¬(i = a ∧ j = b) ∧ ¬(Fin.rev j = a ∧ Fin.rev i = b) := by decide

theorem rootMatrix_diag_upper : ∀ i j a : Fin 4, i < j →
    ¬(i = a ∧ j = a) ∧ ¬(Fin.rev j = a ∧ Fin.rev i = a) := by decide

theorem rootMatrix_entries_lower : ∀ i j a b : Fin 4, j < i → a < b →
    a ≠ b ∧ ¬(i = a ∧ j = b) ∧ ¬(Fin.rev j = a ∧ Fin.rev i = b) := by decide

theorem rootMatrix_diag_lower : ∀ i j a : Fin 4, j < i →
    ¬(i = a ∧ j = a) ∧ ¬(Fin.rev j = a ∧ Fin.rev i = a) := by decide

theorem isUpperUni_rootMatrix {i j : Fin 4} (hij : i < j) (c : K) :
    IsUpperUni (rootMatrix (unitaryInvolution K 2 n) i j c) := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := rootMatrix_entries_upper i j a b hij hba
    simp only [rootMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.single_apply, if_neg h1, if_neg h2, if_neg h3]
    simp
  · obtain ⟨h2, h3⟩ := rootMatrix_diag_upper i j a hij
    simp only [rootMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.single_apply, if_neg h2, if_neg h3]
    simp

theorem isLowerUni_rootMatrix {i j : Fin 4} (hij : j < i) (c : K) :
    IsLowerUni (rootMatrix (unitaryInvolution K 2 n) i j c) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := rootMatrix_entries_lower i j a b hij hab
    simp only [rootMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.single_apply, if_neg h1, if_neg h2, if_neg h3]
    simp
  · obtain ⟨h2, h3⟩ := rootMatrix_diag_lower i j a hij
    simp only [rootMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.single_apply, if_neg h2, if_neg h3]
    simp

theorem longRootMatrix_entries_upper : ∀ i a b : Fin 4, i < Fin.rev i → b < a →
    ¬(i = a ∧ Fin.rev i = b) ∧ a ≠ b := by decide

theorem longRootMatrix_entries_lower : ∀ i a b : Fin 4, Fin.rev i < i → a < b →
    ¬(i = a ∧ Fin.rev i = b) ∧ a ≠ b := by decide

theorem isUpperUni_longRootMatrix {i : Fin 4} (hi : i < Fin.rev i) (c : K) :
    IsUpperUni (longRootMatrix i c : Matrix (Fin 4) (Fin 4) K) := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · obtain ⟨h2, h1⟩ := longRootMatrix_entries_upper i a b hi hba
    simp only [longRootMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_neg h1,
      if_neg h2]
    simp
  · have h2 : ¬(i = a ∧ Fin.rev i = a) := by
      rintro ⟨h, h'⟩
      rw [← h] at h'
      exact absurd h' (ne_of_gt hi)
    simp only [longRootMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_neg h2]
    simp

theorem isLowerUni_longRootMatrix {i : Fin 4} (hi : Fin.rev i < i) (c : K) :
    IsLowerUni (longRootMatrix i c : Matrix (Fin 4) (Fin 4) K) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · obtain ⟨h2, h1⟩ := longRootMatrix_entries_lower i a b hi hab
    simp only [longRootMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_neg h1,
      if_neg h2]
    simp
  · have h2 : ¬(i = a ∧ Fin.rev i = a) := by
      rintro ⟨h, h'⟩
      rw [← h] at h'
      exact absurd h' (ne_of_lt hi)
    simp only [longRootMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_neg h2]
    simp

theorem exists_norm_of_fixed (hK : Nat.card K = (2 ^ n) ^ 2) {x : K}
    (hx : unitaryInvolution K 2 n x = x) : ∃ a : K, unitaryInvolution K 2 n a * a = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [h0, map_zero, zero_mul]⟩
  · exact CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hK hx h0

theorem upperU_sup_lowerU_eq_top (hK : Nat.card K = (2 ^ n) ^ 2) :
    UpperU K n ⊔ LowerU K n = ⊤ := by
  have hσ := unitaryInvolution_involutive hK
  refine eq_top_of_rootElements_le (σ := unitaryInvolution K 2 n) hσ
    ⟨1, one_ne_zero, ?_⟩ (fun x hx => CFSG.LieType.BorelTits.exists_add_unitaryInvolution_eq hK hx)
    (fun x hx => exists_norm_of_fixed hK hx) (by norm_num) (UpperU K n ⊔ LowerU K n) ?_ ?_ ?_
  · rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  · intro i j hij hi hj hji c
    rcases lt_or_gt_of_ne hij with h | h
    · refine Subgroup.mem_sup_left (mem_UpperU'.mpr ?_)
      show IsUpperUni (rootMatrix (unitaryInvolution K 2 n) i j c.toAdd)
      exact isUpperUni_rootMatrix h _
    · refine Subgroup.mem_sup_right (mem_LowerU'.mpr ?_)
      show IsLowerUni (rootMatrix (unitaryInvolution K 2 n) i j c.toAdd)
      exact isLowerUni_rootMatrix h _
  · intro i hi c
    rcases lt_or_gt_of_ne hi with h | h
    · refine Subgroup.mem_sup_left (mem_UpperU'.mpr ?_)
      show IsUpperUni (longRootMatrix i ((c.toAdd : traceZero (unitaryInvolution K 2 n)) : K))
      exact isUpperUni_longRootMatrix h _
    · refine Subgroup.mem_sup_right (mem_LowerU'.mpr ?_)
      show IsLowerUni (longRootMatrix i ((c.toAdd : traceZero (unitaryInvolution K 2 n)) : K))
      exact isLowerUni_longRootMatrix h _
  · intro i k hi hik hk
    exfalso
    revert hk
    fin_cases k <;> decide

end Generation

section Facts

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem nHom_normH (w : WB) {h : G4 K n} (hh : h ∈ Hd K n) :
    (nHom K n w)⁻¹ * h * nHom K n w ∈ Hd K n := by
  intro i j hij
  rw [gm_nHom_conj_inv]
  exact mem_Hd.mp hh _ _ (fun e => hij ((permOf w).injective e))

theorem nHom_normH' (w : WB) {h : G4 K n} (hh : h ∈ Hd K n) :
    nHom K n w * h * (nHom K n w)⁻¹ ∈ Hd K n := by
  have := nHom_normH w⁻¹ hh
  rwa [← nHom_inv, inv_inv] at this

theorem nSimple_sq (s : Fin 2) : nSimple K n s * nSimple K n s = 1 := by
  rw [nSimple, ← map_mul, csB.simple_mul_simple_self, map_one]

theorem nSimple_inv (s : Fin 2) : (nSimple K n s)⁻¹ = nSimple K n s :=
  inv_eq_of_mul_eq_one_right (nSimple_sq s)

theorem Xs_le_U (s : Fin 2) : Xs K n s ≤ UpperU K n := by
  fin_cases s
  · exact X0_le_U n
  · exact X1_le_U n

theorem Uss_le_U (s : Fin 2) : Uss K n s ≤ UpperU K n := by
  fin_cases s
  · exact Us0_le_U n
  · exact Us1_le_U n

theorem exists_unit_X0 (hK : Nat.card K = (2 ^ n) ^ 2) {x : G4 K n} (hx : x ∈ X0 K n)
    (hx1 : x ≠ 1) : ∃ u : Kˣ, x = x0 hK (u : K) := by
  obtain ⟨c, hc⟩ := mem_X0.mp hx
  have hx' : x = x0 hK c := eq_of_gm_eq (by rw [hc, gm_x0 hK])
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx1
    rw [hx']
    exact eq_of_gm_eq (by rw [gm_x0 hK, x0Mat_zero, gm_one])
  exact ⟨Units.mk0 c hc0, hx'⟩

theorem exists_unit_X1 (hK : Nat.card K = (2 ^ n) ^ 2) {x : G4 K n} (hx : x ∈ X1 K n)
    (hx1 : x ≠ 1) : ∃ u : (Fq K n)ˣ, x = x1 hK (u : Fq K n) := by
  obtain ⟨c, hcq, hc⟩ := mem_X1.mp hx
  have hx' : x = x1 hK ⟨c, hcq⟩ := eq_of_gm_eq (by rw [hc, gm_x1 hK])
  have hc0 : (⟨c, hcq⟩ : Fq K n) ≠ 0 := by
    intro h
    apply hx1
    rw [hx', h]
    exact eq_of_gm_eq (by rw [gm_x1 hK]; show x1Mat ((0 : Fq K n) : K) = _; rw [gm_one]; exact x1Mat_zero)
  exact ⟨Units.mk0 _ hc0, hx'⟩

theorem psi_form (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) {x : G4 K n} (hx : x ∈ Xs K n s)
    (hx1 : x ≠ 1) : ∃ a ∈ Xs K n s, ∃ h ∈ Hd K n,
      nSimple K n s * x * nSimple K n s = a * nSimple K n s * h * a := by
  fin_cases s
  · obtain ⟨u, rfl⟩ := exists_unit_X0 hK hx hx1
    exact ⟨x0 hK ((u⁻¹ : Kˣ) : K), x0_mem_X0 hK _, hTor0 hK u, hTor0_mem hK u, rank0_psi hK u⟩
  · obtain ⟨u, rfl⟩ := exists_unit_X1 hK hx hx1
    exact ⟨x1 hK ((u⁻¹ : (Fq K n)ˣ) : Fq K n), x1_mem_X1 hK _, hTor1 hK u, hTor1_mem hK u,
      rank1_psi hK u⟩

end Facts

section BruhatSection

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def bruhatSet (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    Set (G4 K n) :=
  {g | ∃ u ∈ UpperU K n, ∃ w : WB, ∃ h ∈ Hd K n, ∃ u' ∈ UpperU K n,
    g = u * nHom K n w * (h * u')}

theorem one_mem_bruhatSet : (1 : G4 K n) ∈ bruhatSet K n :=
  ⟨1, one_mem _, 1, 1, one_mem _, 1, one_mem _, by simp⟩

theorem U_mul_mem_bruhatSet {x g : G4 K n} (hx : x ∈ UpperU K n) (hg : g ∈ bruhatSet K n) :
    x * g ∈ bruhatSet K n := by
  obtain ⟨u, hu, w, h, hh, u', hu', rfl⟩ := hg
  exact ⟨x * u, mul_mem hx hu, w, h, hh, u', hu', by group⟩

theorem n_mul_mem_bruhatSet_of (s : Fin 2)
    (F1 : ∀ u ∈ UpperU K n, ∃ x ∈ Xs K n s, ∃ v ∈ Uss K n s, u = x * v)
    (F2 : ∀ x ∈ Xs K n s, ∀ v ∈ Uss K n s, x * v * x⁻¹ ∈ Uss K n s)
    (F3 : ∀ v ∈ Uss K n s, nSimple K n s * v * (nSimple K n s)⁻¹ ∈ Uss K n s)
    (F4 : ∀ x ∈ Xs K n s, x ≠ 1 → ∃ a ∈ Xs K n s, ∃ h ∈ Hd K n,
      nSimple K n s * x * nSimple K n s = a * nSimple K n s * h * a)
    {g : G4 K n} (hg : g ∈ bruhatSet K n) : nSimple K n s * g ∈ bruhatSet K n := by
  obtain ⟨u, hu, v, h, hh, u', hu', rfl⟩ := hg
  obtain ⟨x, hx, vs, hvs, hu_eq⟩ := F1 u hu
  have hus : x * vs * x⁻¹ ∈ Uss K n s := F2 x hx vs hvs
  have hu_eq' : u = (x * vs * x⁻¹) * x := by rw [hu_eq]; group
  have key : nSimple K n s * (u * nHom K n v * (h * u')) =
      (nSimple K n s * (x * vs * x⁻¹) * (nSimple K n s)⁻¹) *
        (nSimple K n s * x * nHom K n v * (h * u')) := by
    rw [hu_eq']; group
  have hus' : nSimple K n s * (x * vs * x⁻¹) * (nSimple K n s)⁻¹ ∈ UpperU K n :=
    Uss_le_U s (F3 _ hus)
  rw [key]
  refine U_mul_mem_bruhatSet hus' ?_
  have hsq : nSimple K n s * nSimple K n s = 1 := nSimple_sq s
  rcases csB.length_simple_mul v s with hlen | hlen
  ·
    have hconj := nW_conj_all v s hlen x hx
    refine ⟨1, one_mem _, csB.simple s * v, h, hh,
      (h⁻¹ * ((nHom K n v)⁻¹ * x * nHom K n v) * h) * u',
      mul_mem (H_normU' hh hconj) hu', ?_⟩
    have e : nHom K n (csB.simple s * v) = nSimple K n s * nHom K n v := by
      rw [map_mul]; rfl
    rw [e]
    group
  ·
    set v' := csB.simple s * v with hv'def
    have hv' : v = csB.simple s * v' := by
      rw [hv'def, ← mul_assoc, csB.simple_mul_simple_self, one_mul]
    have hlen' : csB.length (csB.simple s * v') = csB.length v' + 1 := by
      rw [← hv']
      omega
    have hNv : nHom K n v = nSimple K n s * nHom K n v' := by
      conv_lhs => rw [hv']
      rw [map_mul]
      rfl
    by_cases hx1 : x = 1
    · subst hx1
      refine ⟨1, one_mem _, v', h, hh, u', hu', ?_⟩
      rw [hNv]
      calc nSimple K n s * 1 * (nSimple K n s * nHom K n v') * (h * u')
          = (nSimple K n s * nSimple K n s) * nHom K n v' * (h * u') := by group
        _ = 1 * nHom K n v' * (h * u') := by rw [hsq]
    · obtain ⟨a, ha, h₁, hh₁, hψ⟩ := F4 x hx hx1
      have hconj := nW_conj_all v' s hlen' a ha
      set u₃ := (nHom K n v')⁻¹ * a * nHom K n v' with hu₃
      set h₄ := (nHom K n v')⁻¹ * h₁ * nHom K n v' with hh₄
      have hh₄mem : h₄ ∈ Hd K n := nHom_normH v' hh₁
      refine ⟨a, Xs_le_U s ha, v, h₄ * h, mul_mem hh₄mem hh, (h⁻¹ * u₃ * h) * u',
        mul_mem (H_normU' hh hconj) hu', ?_⟩
      have e1 : nSimple K n s * x * nHom K n v = a * nSimple K n s * h₁ * a * nHom K n v' := by
        rw [hNv, ← hψ]
        group
      have e2 : a * nHom K n v' = nHom K n v' * u₃ := by rw [hu₃]; group
      have e3 : h₁ * nHom K n v' = nHom K n v' * h₄ := by rw [hh₄]; group
      calc nSimple K n s * x * nHom K n v * (h * u')
          = a * nSimple K n s * h₁ * a * nHom K n v' * (h * u') := by rw [e1]
        _ = a * nSimple K n s * h₁ * (a * nHom K n v') * (h * u') := by group
        _ = a * nSimple K n s * (h₁ * nHom K n v') * u₃ * (h * u') := by rw [e2]; group
        _ = a * nSimple K n s * (nHom K n v' * h₄) * u₃ * (h * u') := by rw [e3]
        _ = a * (nSimple K n s * nHom K n v') * h₄ * u₃ * (h * u') := by group
        _ = a * nHom K n v * ((h₄ * h) * ((h⁻¹ * u₃ * h) * u')) := by rw [← hNv]; group

theorem n_mul_mem_bruhatSet (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) {g : G4 K n}
    (hg : g ∈ bruhatSet K n) : nSimple K n s * g ∈ bruhatSet K n := by
  refine n_mul_mem_bruhatSet_of s ?_ ?_ ?_ (fun x hx hx1 => psi_form hK s hx hx1) hg
  · fin_cases s
    · exact fun u hu => U_eq0 hK hu
    · exact fun u hu => U_eq1 hK hu
  · fin_cases s
    · exact fun x hx v hv => X0_normUs0 hx hv
    · exact fun x hx v hv => X1_normUs1 hx hv
  · fin_cases s
    · exact fun v hv => n0_normUs0 hv
    · exact fun v hv => n1_normUs1 hv

theorem bruhatSet_eq_univ (hK : Nat.card K = (2 ^ n) ^ 2) (g : G4 K n) : g ∈ bruhatSet K n := by
  let T : Subgroup (G4 K n) :=
    { carrier := {x | ∀ g ∈ bruhatSet K n, x * g ∈ bruhatSet K n ∧ x⁻¹ * g ∈ bruhatSet K n}
      one_mem' := fun g hg => ⟨by simpa using hg, by simpa using hg⟩
      mul_mem' := by
        intro a b ha hb g hg
        refine ⟨?_, ?_⟩
        · rw [mul_assoc]
          exact (ha _ ((hb g hg).1)).1
        · rw [_root_.mul_inv_rev, mul_assoc]
          exact (hb _ ((ha g hg).2)).2
      inv_mem' := by
        intro x hx g hg
        exact ⟨(hx g hg).2, by simpa using (hx g hg).1⟩ }
  have hU : UpperU K n ≤ T := fun x hx g hg =>
    ⟨U_mul_mem_bruhatSet hx hg, U_mul_mem_bruhatSet (inv_mem hx) hg⟩
  have hnS : ∀ s, nSimple K n s ∈ T := fun s g hg =>
    ⟨n_mul_mem_bruhatSet hK s hg, by rw [nSimple_inv]; exact n_mul_mem_bruhatSet hK s hg⟩
  have hJ : jSU K n ∈ T := by
    have e : jSU K n = nSimple K n 0 * nSimple K n 1 * nSimple K n 0 * nSimple K n 1 := by
      rw [← nHom_w0]
      show nHom K n (s0 * s1 * s0 * s1) = _
      simp only [map_mul]
      rfl
    rw [e]
    exact mul_mem (mul_mem (mul_mem (hnS 0) (hnS 1)) (hnS 0)) (hnS 1)
  have hL : LowerU K n ≤ T := by
    intro l hl
    have hu := jconj_mem_U hl
    have : l = jSU K n * (jSU K n * l * jSU K n) * jSU K n := (jconj_jconj l).symm
    rw [this]
    exact mul_mem (mul_mem hJ (hU hu)) hJ
  have hT : UpperU K n ⊔ LowerU K n ≤ T := sup_le hU hL
  rw [upperU_sup_lowerU_eq_top hK] at hT
  have := (hT (Subgroup.mem_top g) 1 one_mem_bruhatSet).1
  simpa using this

theorem cover_G4 (hK : Nat.card K = (2 ^ n) ^ 2) (g : G4 K n) :
    ∃ l ∈ LowerU K n, ∃ w : WB, ∃ h ∈ Hd K n, ∃ u ∈ UpperU K n,
      g = l * nHom K n w * (h * u) := by
  obtain ⟨u₁, hu₁, v, h, hh, u₂, hu₂, e⟩ := bruhatSet_eq_univ hK (jSU K n * g)
  have hl : jSU K n * u₁ * jSU K n ∈ LowerU K n := by
    refine mem_LowerU_of_conj_mem_UpperU ?_
    rw [jSU_inv, jconj_jconj]
    exact hu₁
  refine ⟨jSU K n * u₁ * jSU K n, hl, w0 * v, h, hh, u₂, hu₂, ?_⟩
  have hJ : jSU K n = nHom K n w0 := nHom_w0.symm
  have hJJ := jSU_mul_self (K := K) (n := n)
  have e2 : (jSU K n * u₁ * jSU K n) * (jSU K n * nHom K n v) * (h * u₂) =
      jSU K n * (u₁ * nHom K n v * (h * u₂)) := by
    calc _ = jSU K n * u₁ * (jSU K n * jSU K n) * nHom K n v * (h * u₂) := by group
      _ = _ := by rw [hJJ]; group
  have e3 : nHom K n (w0 * v) = jSU K n * nHom K n v := by rw [map_mul, ← hJ]
  rw [e3, e2, ← e, ← mul_assoc, hJJ, one_mul]

end BruhatSection

end Datum

end CFSG.HardMathSupport.U4FF
