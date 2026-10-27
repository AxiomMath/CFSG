module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourModel
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.QuasithinUnique.K1

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour

variable {K : Type} [Field K]

theorem tauS_injective {b c d b' c' d' : K} (h : tauS b c d = tauS b' c' d') :
    b = b' ∧ c = c' ∧ d = d' := by
  have h1 := tau_injective (sym2_transpose b c d) (sym2_transpose b' c' d') h
  have e00 := congrFun₂ h1 0 0
  have e01 := congrFun₂ h1 0 1
  have e11 := congrFun₂ h1 1 1
  simp [sym2] at e00 e01 e11
  exact ⟨e00, e01, e11⟩

section CharTwo

variable [CharP K 2]

theorem key_conjugation (c : K) :
    weylA K * tauS 0 0 1 * (tauS 0 c 0 * lam c) = tauS (c ^ 2) c 0 * (weylA K * tauS 0 0 1) := by
  apply SymplecticTorusWeyl.statedSp_ext
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : (-c : K) = c := CharTwo.neg_eq c
  simp only [Subgroup.coe_mul, Units.val_mul, coe_tauS, coe_lam]
  change weylAMat K * _ * (_ * _) = _ * (weylAMat K * _)
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [weylAMat, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply, unitri, sym2,
      h1] <;>
    first | linear_combination (c) * h2 | ring

end CharTwo

theorem StronglyClosedWitness.conj_mem_unipotent {A : Subgroup (StatedSp 2 K)}
    (hW : StronglyClosedWitness (StatedSp 2 K) (unipotent 2 K) A) {a p : StatedSp 2 K}
    (ha : a ∈ A) (hp : p ∈ unipotent 2 K) : p * a * p⁻¹ ∈ A := by
  have h := hW.closed a ha p⁻¹ (by
    rw [inv_inv]
    exact (unipotent 2 K).mul_mem ((unipotent 2 K).mul_mem hp (hW.le ha))
      ((unipotent 2 K).inv_mem hp))
  rwa [inv_inv] at h

theorem StronglyClosedWitness.conj_mem_of_mem_unipotent {A : Subgroup (StatedSp 2 K)}
    (hW : StronglyClosedWitness (StatedSp 2 K) (unipotent 2 K) A) {a g : StatedSp 2 K}
    (ha : a ∈ A) (hg : g * a * g⁻¹ ∈ unipotent 2 K) : g * a * g⁻¹ ∈ A := by
  have h := hW.closed a ha g⁻¹ (by rwa [inv_inv])
  rwa [inv_inv] at h

private theorem exists_ne_zero_one [Finite K] (hK : 4 ≤ Nat.card K) : ∃ s : K, s ≠ 0 ∧ s ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite K
  classical
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [hcon x hx]
  have h2 : Fintype.card K ≤ 2 :=
    (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Nat.card_eq_fintype_card] at hK
  omega

section Witness

variable [CharP K 2] [Finite K] {A : Subgroup (StatedSp 2 K)}
  (hW : StronglyClosedWitness (StatedSp 2 K) (unipotent 2 K) A)

include hW

omit [Finite K] in
theorem lam_mem_of_tauS_second {a : K} (h : tauS 0 a 0 ∈ A) : lam a ∈ A := by
  have h1 : (weylA K)⁻¹ * tauS 0 a 0 * ((weylA K)⁻¹)⁻¹ = lam a := by
    rw [inv_inv]
    calc (weylA K)⁻¹ * tauS 0 a 0 * weylA K = (weylA K)⁻¹ * (tauS 0 a 0 * weylA K) := by
          rw [mul_assoc]
      _ = (weylA K)⁻¹ * (weylA K * lam a) := by rw [weylA_mul_lam]
      _ = lam a := by group
  have := hW.conj_mem_of_mem_unipotent h (g := (weylA K)⁻¹) (by
    rw [h1]
    exact lam_mem_unipotent a)
  rwa [h1] at this

omit [CharP K 2] [Finite K] in
theorem tauS_third_of_tauS_first {d : K} (h : tauS d 0 0 ∈ A) : tauS 0 0 d ∈ A := by
  have h1 : (weylD K)⁻¹ * tauS d 0 0 * ((weylD K)⁻¹)⁻¹ = tauS 0 0 d := by
    rw [inv_inv]
    calc (weylD K)⁻¹ * tauS d 0 0 * weylD K = (weylD K)⁻¹ * (tauS d 0 0 * weylD K) := by
          rw [mul_assoc]
      _ = (weylD K)⁻¹ * (weylD K * tauS 0 0 d) := by rw [weylD_mul_tauS]
      _ = tauS 0 0 d := by group
  have := hW.conj_mem_of_mem_unipotent h (g := (weylD K)⁻¹) (by
    rw [h1]
    exact tauS_mem_unipotent _ _ _)
  rwa [h1] at this

omit [CharP K 2] [Finite K] in
theorem tauS_mem_torus {b c d : K} (s : Fin 2 → Kˣ) (h : tauS b c d ∈ A) :
    tauS ((s 0 : K) ^ 2 * b) ((s 0 : K) * (s 1 : K) * c) ((s 1 : K) ^ 2 * d) ∈ A := by
  have h1 : SymplecticTorusWeyl.torusHom s * tauS b c d * (SymplecticTorusWeyl.torusHom s)⁻¹ =
      tauS ((s 0 : K) ^ 2 * b) ((s 0 : K) * (s 1 : K) * c) ((s 1 : K) ^ 2 * d) := by
    rw [mul_inv_eq_iff_eq_mul, torusHom_mul_tauS]
  have := hW.conj_mem_of_mem_unipotent h (g := SymplecticTorusWeyl.torusHom s) (by
    rw [h1]
    exact tauS_mem_unipotent _ _ _)
  rwa [h1] at this

theorem false_of_tauS_first {b : K} (hb : b ≠ 0) (h : tauS b 0 0 ∈ A) : False := by
  have hring : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hring b⁻¹
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hb (inv_eq_zero.mp hr)
  have h1 : tauS (1 : K) 0 0 ∈ A := by
    have h' := tauS_mem_torus hW ![Units.mk0 r hr0, 1] h
    have e : r ^ 2 * b = 1 := by rw [sq, ← hr, inv_mul_cancel₀ hb]
    simpa [e] using h'
  have h2 : tauS (0 : K) 0 1 ∈ A := tauS_third_of_tauS_first hW h1
  have hconj : lam (1 : K) * tauS (0 : K) 0 1 * (lam (1 : K))⁻¹ = tauS (1 : K) 1 1 := by
    rw [lam_mul_tauS_mul_inv]
    simp
  have h3 : tauS (1 : K) 1 1 ∈ A := by
    have := hW.conj_mem_unipotent h2 (lam_mem_unipotent (1 : K))
    rwa [hconj] at this
  have hone : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero (1 : K)
  have e4 : tauS (1 : K) 1 1 * tauS (1 : K) 0 0 * tauS (0 : K) 0 1 = tauS (0 : K) 1 0 := by
    rw [tauS_mul_tauS, tauS_mul_tauS]
    simp [hone]
  have h4 : tauS (0 : K) 1 0 ∈ A := by
    rw [← e4]
    exact A.mul_mem (A.mul_mem h3 h1) h2
  have h5 : lam (1 : K) ∈ A := lam_mem_of_tauS_second hW h4
  have hc := hW.elem.1.is_comm.comm ⟨lam (1 : K), h5⟩ ⟨tauS (0 : K) 0 1, h2⟩
  have hc' : lam (1 : K) * tauS (0 : K) 0 1 = tauS (0 : K) 0 1 * lam (1 : K) :=
    congrArg Subtype.val hc
  have h6 : tauS (1 : K) 1 1 = tauS (0 : K) 0 1 := by
    rw [← hconj, hc', mul_inv_cancel_right]
  exact one_ne_zero (tauS_injective h6).1

theorem exists_tauS_first_of_ne (hK : 4 ≤ Nat.card K) {b c : K} (hb : b ≠ 0) (hc : c ≠ 0)
    (h : tauS b c 0 ∈ A) : ∃ b' : K, b' ≠ 0 ∧ tauS b' 0 0 ∈ A := by
  obtain ⟨s₁, hs0, hs1⟩ := exists_ne_zero_one hK
  have hconj := tauS_mem_torus hW ![Units.mk0 s₁ hs0, (Units.mk0 s₁ hs0)⁻¹] h
  have e1 : s₁ * s₁⁻¹ * c = c := by field_simp
  have hconj' : tauS (s₁ ^ 2 * b) c 0 ∈ A := by
    simpa [e1] using hconj
  have h2 : (c + c : K) = 0 := CharTwo.add_self_eq_zero c
  have hs : (1 + s₁ : K) ≠ 0 := fun h0 =>
    hs1 (by linear_combination h0 - CharP.cast_eq_zero K 2)
  refine ⟨b + s₁ ^ 2 * b, ?_, ?_⟩
  · have e2 : b + s₁ ^ 2 * b = b * (1 + s₁) ^ 2 := by
      linear_combination (-(b * s₁)) * CharP.cast_eq_zero K 2
    rw [e2]
    exact mul_ne_zero hb (pow_ne_zero 2 hs)
  · have := A.mul_mem h hconj'
    rwa [tauS_mul_tauS, h2, add_zero] at this

omit [Finite K] in
theorem tauS_sq_mem_of_tauS_second {c : K} (h : tauS 0 c 0 ∈ A) : tauS (c ^ 2) c 0 ∈ A := by
  have hlam : lam c ∈ A := lam_mem_of_tauS_second hW h
  have ht : tauS 0 c 0 * lam c ∈ A := A.mul_mem h hlam
  have hconj : (weylA K * tauS 0 0 1) * (tauS 0 c 0 * lam c) * (weylA K * tauS 0 0 1)⁻¹ =
      tauS (c ^ 2) c 0 := by
    rw [mul_inv_eq_iff_eq_mul]
    exact key_conjugation c
  have := hW.conj_mem_of_mem_unipotent ht (g := weylA K * tauS 0 0 1) (by
    rw [hconj]
    exact tauS_mem_unipotent _ _ _)
  rwa [hconj] at this

end Witness

theorem noStronglyClosed_statedSp [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    NoStronglyClosedElemAbelian (StatedSp 2 K) := by
  obtain ⟨-, ⟨S, hS⟩, -, -, -, -, -, hcenter, -⟩ :=
    unique_symplectic_four_Sylow_center (K := K) (Nat.card K) rfl
  have hQ₀ : IsSylowTwoOf (unipotent 2 K) ⊤ := by
    rw [← hS]
    exact isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  refine noStronglyClosedElemAbelian_of_sylow _ hQ₀ fun A hW => ?_
  by_contra hne
  have hAn : ∀ a ∈ A, ∀ q ∈ unipotent 2 K, q⁻¹ * a * q ∈ A := fun a ha q hq => by
    have := hW.conj_mem_unipotent ha ((unipotent 2 K).inv_mem hq)
    simpa using this
  obtain ⟨z, hzA, hz1, hzc⟩ := exists_ne_one_mem_centralizer hW.sylow.2.1 hW.le hAn hne
  have hzcen : (⟨z, hW.le hzA⟩ : unipotent 2 K) ∈ Subgroup.center (unipotent 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  obtain ⟨b, c, hbc⟩ := (hcenter _).mp hzcen
  have hz : z = tauS b c 0 := hbc
  rw [hz] at hzA hz1
  by_cases hc : c = 0
  · subst hc
    by_cases hb : b = 0
    · subst hb
      exact hz1 tauS_zero
    · exact false_of_tauS_first hW hb hzA
  · by_cases hb : b = 0
    · subst hb
      have h1 := tauS_sq_mem_of_tauS_second hW hzA
      obtain ⟨b', hb', h2⟩ := exists_tauS_first_of_ne hW hK (pow_ne_zero 2 hc) hc h1
      exact false_of_tauS_first hW hb' h2
    · obtain ⟨b', hb', h2⟩ := exists_tauS_first_of_ne hW hK hb hc hzA
      exact false_of_tauS_first hW hb' h2

end CFSG.QuasithinUnique.K1
