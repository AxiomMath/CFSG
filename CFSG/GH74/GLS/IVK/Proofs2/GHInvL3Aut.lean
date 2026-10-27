module

public import CFSG.RankThree.PartOne.S15K.LinAutRank
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem pow_apply_eq_pow_of_frobenius {F : Type} [Field F] {p : ℕ} {σ : F ≃+* F}
    (hσ : ∀ a, σ a = a ^ p) (k : ℕ) (a : F) : (σ ^ k) a = a ^ (p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, RingAut.mul_apply, hσ, map_pow, ih, ← pow_mul, ← pow_succ]

theorem exists_preimages_of_card_eq_four {G Θ : Type*} [Group G] [Group Θ] (π : G →* Θ)
    (E : Subgroup G) (hE4 : Nat.card E = 4) (hinj : ∀ e ∈ E, π e = 1 → e = 1) {w v : Θ}
    (hvv : v * v = 1) (hmem : ∀ e ∈ E, π e = 1 ∨ π e = w ∨ π e = v ∨ π e = w * v) :
    (∃ s ∈ E, π s = w) ∧ (∃ e ∈ E, π e = v) ∧ w ≠ 1 ∧ v ≠ 1 ∧ w ≠ v := by
  classical
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE4]; norm_num)
  let _ : Fintype E := Fintype.ofFinite E
  set S : Finset Θ := {1, w, v, w * v} with hS
  let g : E → Θ := fun e => π e
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : π ((a : G) * (b : G)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.2 hab
    exact Subtype.ext (mul_inv_eq_one.1 (hinj _ (E.mul_mem a.2 (E.inv_mem b.2)) h1))
  have hT : (Finset.univ.image g).card = 4 := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, ← Nat.card_eq_fintype_card, hE4]
  have hTS : Finset.univ.image g ⊆ S := by
    intro y hy
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hy
    simp only [hS, Finset.mem_insert, Finset.mem_singleton]
    exact hmem e e.2
  have hTeq : Finset.univ.image g = S :=
    Finset.eq_of_subset_of_card_le hTS (by rw [hT]; exact Finset.card_le_four)
  have hsmall : ∀ x : Θ, S ⊆ {1, x} → False := by
    intro x hx
    have h1 := Finset.card_le_card hx
    have h2 := Finset.card_le_two (a := (1 : Θ)) (b := x)
    rw [← hTeq, hT] at h1
    omega
  have hpre : ∀ x ∈ S, ∃ e ∈ E, π e = x := by
    intro x hx
    rw [← hTeq] at hx
    obtain ⟨e, -, he⟩ := Finset.mem_image.1 hx
    exact ⟨e, e.2, he⟩
  refine ⟨hpre w (by simp [hS]), hpre v (by simp [hS]), fun h => hsmall v ?_,
    fun h => hsmall w ?_, fun h => hsmall v ?_⟩ <;>
  · intro y hy
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl <;> simp [h, hvv]

theorem exists_field_graph_pair {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hFc : Nat.card F = p ^ f) (hfe : Even f) (hf0 : f ≠ 0)
    (E : Subgroup (MulAut (projectiveSL 3 F))) (hE2 : ∀ e ∈ E, e * e = 1) (hE4 : Nat.card E = 4)
    (hD : ∀ e ∈ E, e ∈ (conjAut 3 F).range → e = 1) :
    ∃ σ : F ≃+* F, (∀ a, σ a = a ^ (p ^ (f / 2))) ∧ ∃ s ∈ E, ∃ e₂ ∈ E, ∃ A C : GL (Fin 3) F,
      (C : Matrix (Fin 3) (Fin 3) F)ᵀ = C ∧ s ≠ 1 ∧ e₂ ≠ 1 ∧ s ≠ e₂ ∧
      s = conjAut 3 F A * fieldAut 3 F σ ∧ e₂ = conjAut 3 F C * dualAut 3 F := by
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.2 hf0
  obtain ⟨σp, hσp, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf1 hFc
  obtain ⟨m, hm⟩ := hfe
  have hm2 : f / 2 = m := by omega
  have hN : (conjAut 3 F).range.Normal := CFSG.RankThree.PartOne.S15K.conjAut_range_normal le_rfl
  set D := (conjAut 3 F).range
  set π := QuotientGroup.mk' D
  have hπ1 : ∀ x, π x = 1 ↔ x ∈ D := fun x => QuotientGroup.eq_one_iff x
  obtain ⟨-, -, -, hδδ, -, -, -⟩ := standard_automorphism_transport (n := 3) (K := F)
  set u := π (fieldAut 3 F σp) with hu
  set v := π (dualAut 3 F) with hv
  set w := u ^ m
  have hfD : ∀ τ : F ≃+* F, fieldAut 3 F τ ∈ D → τ = 1 := by
    rintro τ ⟨B, hB⟩
    refine (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl B⁻¹ τ ?_).1
    rw [← hB, ← map_mul, inv_mul_cancel, map_one]
  have hupow : ∀ k : ℕ, π (fieldAut 3 F (σp ^ k)) = u ^ k := fun k => by
    rw [map_pow, map_pow]
  have huf : u ^ f = 1 := by
    rw [← hupow, ← hord, pow_orderOf_eq_one, map_one, map_one]
  have hudvd : ∀ k : ℕ, u ^ k = 1 → f ∣ k := fun k hk => by
    rw [← hupow, hπ1] at hk
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (hfD _ hk)
  have hvv : v * v = 1 := by rw [hv, ← map_mul, hδδ, map_one]
  have huv : Commute u v := by
    show u * v = v * u
    rw [hu, hv, ← map_mul, ← map_mul, dualAut_mul_fieldAut]
  have hmem : ∀ e ∈ E, π e = 1 ∨ π e = w ∨ π e = v ∨ π e = w * v := by
    intro e he
    obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
    obtain ⟨A, τ, ε, hε, rfl⟩ := hform e
    have hτ : τ ∈ Submonoid.powers σp := by
      rw [(orderOf_pos_iff.1 (by omega)).mem_powers_iff_mem_zpowers, hzp]
      exact Subgroup.mem_top τ
    obtain ⟨k, rfl⟩ := hτ
    have hπe : π (conjAut 3 F A * fieldAut 3 F (σp ^ k) * dualAut 3 F ^ ε) = u ^ k * v ^ ε := by
      rw [map_mul, map_mul, (hπ1 _).2 ⟨A, rfl⟩, one_mul, hupow, map_pow]
    have h2 : (u ^ k * v ^ ε) * (u ^ k * v ^ ε) = 1 := by
      rw [← hπe, ← map_mul, hE2 _ he, map_one]
    have hvε : v ^ ε * v ^ ε = 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
      · simp
      · simpa using hvv
    have hu2k : u ^ (k + k) = 1 := by
      rw [((huv.pow_pow k ε).symm).mul_mul_mul_comm, hvε, mul_one, ← pow_add] at h2
      exact h2
    have hmk : m ∣ k := by
      have h := hudvd _ hu2k
      rw [hm, ← two_mul, ← two_mul] at h
      exact Nat.dvd_of_mul_dvd_mul_left two_pos h
    obtain ⟨j, rfl⟩ := hmk
    have huk : u ^ (m * j) = 1 ∨ u ^ (m * j) = w := by
      rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · left
        rw [← two_mul, ← mul_assoc, mul_comm m 2, two_mul, ← hm, pow_mul, huf, one_pow]
      · right
        rw [mul_add, mul_one, ← mul_assoc, mul_comm m 2, two_mul, ← hm, pow_add, pow_mul, huf,
          one_pow, one_mul]
    rw [hπe]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl <;> rcases huk with h | h <;>
      simp [h]
  obtain ⟨⟨s, hsE, hs⟩, ⟨e₂, he₂E, he₂⟩, hw1, hv1, hwv⟩ :=
    exists_preimages_of_card_eq_four π E hE4 (fun e he h1 => hD e he ((hπ1 e).1 h1)) hvv hmem
  obtain ⟨A, hA⟩ : s * (fieldAut 3 F (σp ^ m))⁻¹ ∈ D := by
    rw [← hπ1, map_mul, map_inv, hupow, hs, mul_inv_cancel]
  obtain ⟨C, hC⟩ : e₂ * (dualAut 3 F)⁻¹ ∈ D := by
    rw [← hπ1, map_mul, map_inv, he₂, mul_inv_cancel]
  have hsA : s = conjAut 3 F A * fieldAut 3 F (σp ^ m) := mul_inv_eq_iff_eq_mul.1 hA.symm
  have he₂C : e₂ = conjAut 3 F C * dualAut 3 F := mul_inv_eq_iff_eq_mul.1 hC.symm
  have h2 : (2 : F) ≠ 0 := by
    have : CharP F p := finite_field_prime_power_characteristic hp hf1 hFc
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hCsymm : (C : Matrix (Fin 3) (Fin 3) F)ᵀ = C := by
    have hsq : (conjAut 3 F C * dualAut 3 F) ^ 2 = 1 := by
      rw [sq, ← he₂C]
      exact hE2 e₂ he₂E
    rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut le_rfl C hsq with h | h
    · exact h
    · exfalso
      have hdet := congrArg Matrix.det h
      rw [Matrix.det_transpose, Matrix.det_neg] at hdet
      have hd0 : (C : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit C)).ne_zero
      simp only [Fintype.card_fin] at hdet
      apply hd0
      have h22 : (2 : F) * (C : Matrix (Fin 3) (Fin 3) F).det = 0 := by
        linear_combination hdet
      exact (mul_eq_zero.1 h22).resolve_left h2
  refine ⟨σp ^ m, fun a => ?_, s, hsE, e₂, he₂E, A, C, hCsymm, ?_, ?_, ?_, hsA, he₂C⟩
  · rw [hm2]
    exact pow_apply_eq_pow_of_frobenius hσp m a
  · rintro rfl
    exact hw1 (by rw [← hs, map_one])
  · rintro rfl
    exact hv1 (by rw [← he₂, map_one])
  · rintro rfl
    exact hwv (by rw [← hs, he₂])

end CFSG.GH74.GLS.IVK.GHInv
