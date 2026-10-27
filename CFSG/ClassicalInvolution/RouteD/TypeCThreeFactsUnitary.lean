module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeBridgeFacts

public section

namespace CFSG.ClassicalInvolution.RouteD.LieBridge

open CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Generic
open Matrix

section Matrices

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def weylSU : SUid σ 2 :=
  ⟨⟨!![0, -1; 1, 0], !![0, 1; -1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩,
   mem_SUid.mpr ⟨by simp [Matrix.det_fin_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two]⟩⟩

theorem coe_weylSU : (((weylSU σ : SUid σ 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![0, -1; 1, 0] := rfl

theorem entry01_of_B12_normalizes (A B : SUid σ 2)
    (h : embSUid σ 0 B * embSUid σ 2 A = embSUid σ 2 A * embSUid σ 0 (weylSU σ)) :
    ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
  have h' := congrArg (fun g : SUid σ 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_weylSU] at h'
  have := congrFun (congrFun h' 0) 1
  simpa [embPair, Matrix.mul_apply, Fin.sum_univ_three] using this

theorem entry01_of_B23_normalizes (A B : SUid σ 2)
    (h : embSUid σ 2 B * embSUid σ 0 A = embSUid σ 0 A * embSUid σ 2 (weylSU σ)) :
    ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
  have h' := congrArg (fun g : SUid σ 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_weylSU] at h'
  have h01 := congrFun (congrFun h' 0) 1
  have h02 := congrFun (congrFun h' 0) 2
  simp [embPair, Matrix.mul_apply, Fin.sum_univ_three] at h01 h02
  rcases h02 with h | h
  · rw [h, zero_mul] at h01
    exact absurd h01 (by simp)
  · exact h

theorem diag_of_entry01 (A : SUid σ 2)
    (h01 : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) :
    ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      σ (((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) *
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 ∧
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 *
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
  have hA := mem_SUid.mp A.2
  have hdet := hA.1
  have hun := hA.2
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
  have e00 := congrFun (congrFun hun 0) 0
  have e01 := congrFun (congrFun hun 0) 1
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, h01] at e00 e01
  have h11 : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact zero_ne_one hdet
  have h10 : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := e01.resolve_right h11
  refine ⟨h10, ?_, hdet⟩
  simpa [h10] using e00

theorem pow_eq_one_of_entry01 [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (A : SUid (unitaryInvolution K p f) 2)
    (h01 : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) : A ^ (p ^ f + 1) = 1 := by
  obtain ⟨h10, hn, hd⟩ := diag_of_entry01 _ A h01
  set a : K := ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set d : K := ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 with hd'
  have hmat : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![a, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, ha, hd']
  have ha1 : a ^ (p ^ f + 1) = 1 := by
    rw [pow_succ, ← unitaryInvolution_apply K p f]
    exact hn
  have hd1 : d ^ (p ^ f + 1) = 1 := by
    have h2 : (a * d) ^ (p ^ f + 1) = 1 := by rw [hd, one_pow]
    rw [mul_pow, ha1, one_mul] at h2
    exact h2
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hmat, Matrix.diagonal_pow]
  have : (![a, d] ^ (p ^ f + 1) : Fin 2 → K) = fun _ => 1 := by
    funext i
    fin_cases i <;> simp [ha1, hd1]
  rw [this]
  exact Matrix.diagonal_one

end Matrices

section Blocks

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem pow_eq_one_of_normalizes_B12 {b : Su K p f 3} (hb : b ∈ B12 K p f)
    (h : ∀ x ∈ B23 K p f, b * x * b⁻¹ ∈ B23 K p f) : b ^ (p ^ f + 1) = 1 := by
  obtain ⟨A, rfl⟩ := hb
  obtain ⟨B, hB⟩ := h _ (show embSUid (unitaryInvolution K p f) 0
    (weylSU (unitaryInvolution K p f)) ∈ B23 K p f from ⟨_, rfl⟩)
  have hrel : embSUid (unitaryInvolution K p f) 0 B * embSUid (unitaryInvolution K p f) 2 A =
      embSUid (unitaryInvolution K p f) 2 A *
        embSUid (unitaryInvolution K p f) 0 (weylSU (unitaryInvolution K p f)) := by
    rw [hB, inv_mul_cancel_right]
  have h01 := entry01_of_B12_normalizes _ A B hrel
  rw [← map_pow, pow_eq_one_of_entry01 A h01, map_one]

theorem pow_eq_one_of_normalizes_B23 {b : Su K p f 3} (hb : b ∈ B23 K p f)
    (h : ∀ x ∈ B12 K p f, b * x * b⁻¹ ∈ B12 K p f) : b ^ (p ^ f + 1) = 1 := by
  obtain ⟨A, rfl⟩ := hb
  obtain ⟨B, hB⟩ := h _ (show embSUid (unitaryInvolution K p f) 2
    (weylSU (unitaryInvolution K p f)) ∈ B12 K p f from ⟨_, rfl⟩)
  have hrel : embSUid (unitaryInvolution K p f) 2 B * embSUid (unitaryInvolution K p f) 0 A =
      embSUid (unitaryInvolution K p f) 0 A *
        embSUid (unitaryInvolution K p f) 2 (weylSU (unitaryInvolution K p f)) := by
    rw [hB, inv_mul_cancel_right]
  have h01 := entry01_of_B23_normalizes _ A B hrel
  rw [← map_pow, pow_eq_one_of_entry01 A h01, map_one]

end Blocks

section Transfer

variable {Y X : Type*} [Group Y] [Group X]

theorem normalizes_of_map_normalizes (θ : Y →* X) (hker : θ.ker ≤ Subgroup.center Y)
    {V : Subgroup Y} (hV : V ≤ ⁅V, V⁆) {y : Y}
    (h : conjSub (θ y) (V.map θ) = V.map θ) : ∀ v ∈ V, y * v * y⁻¹ ∈ V := by
  have hA : conjSub y V ≤ ⁅conjSub y V, conjSub y V⁆ := by
    unfold conjSub
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hV
  have hle : conjSub y V ≤ V ⊔ θ.ker := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 : θ ((MulAut.conj y).toMonoidHom v) ∈ V.map θ := by
      have := conj_mem_conjSub (n := θ y) (K := V.map θ) (Subgroup.mem_map_of_mem θ hv)
      rw [h] at this
      simpa [MulAut.conj_apply] using this
    obtain ⟨v', hv', hθ⟩ := h1
    have hk : v'⁻¹ * (MulAut.conj y).toMonoidHom v ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, inv_mul_cancel]
    have : (MulAut.conj y).toMonoidHom v = v' * (v'⁻¹ * (MulAut.conj y).toMonoidHom v) := by
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv') (Subgroup.mem_sup_right hk)
  have hsub := le_of_perfect_of_le_sup_center hker hA hle
  intro v hv
  exact hsub (conj_mem_conjSub hv)

end Transfer

section Main

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type*} [Group X]

theorem pow_eq_one_of_normalizes_conj (θ : Su K p f 3 →* X)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) (c : Su K p f 3) {P Q : Subgroup (Su K p f 3)}
    (hPQ : ∀ b ∈ P, (∀ x ∈ Q, b * x * b⁻¹ ∈ Q) → b ^ (p ^ f + 1) = 1) (hQ : Q ≤ ⁅Q, Q⁆) {a : X}
    (haP : a ∈ (P.map (MulAut.conj c⁻¹).toMonoidHom).map θ)
    (hnorm : conjSub a ((Q.map (MulAut.conj c⁻¹).toMonoidHom).map θ) =
      (Q.map (MulAut.conj c⁻¹).toMonoidHom).map θ) : a ^ (p ^ f + 1) = 1 := by
  obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := haP
  have hQ' : Q.map (MulAut.conj c⁻¹).toMonoidHom ≤ ⁅Q.map (MulAut.conj c⁻¹).toMonoidHom,
      Q.map (MulAut.conj c⁻¹).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hQ
  have hn := normalizes_of_map_normalizes θ hker hQ' hnorm
  have hb' : (∀ x ∈ Q, b * x * b⁻¹ ∈ Q) := by
    intro x hx
    have := hn ((MulAut.conj c⁻¹).toMonoidHom x) (Subgroup.mem_map_of_mem _ hx)
    obtain ⟨x', hx', hxx⟩ := this
    have e : x' = b * x * b⁻¹ := by
      apply (MulAut.conj c⁻¹).injective
      simp only [MulEquiv.coe_toMonoidHom] at hxx ⊢
      rw [hxx]
      simp
      group
    rwa [← e]
  have hpow := hPQ b hb hb'
  rw [← map_pow, ← map_pow, hpow, map_one, map_one]

end Main

theorem unitaryPairNoSplitNormalizer (p : ℕ) [Fact p.Prime] : UnitaryPairNoSplitNormalizer p := by
  intro e hq X _ W U V hpair hex
  obtain ⟨a, haU, hao, hanorm⟩ := hex
  have hf : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨θ, c, -, hker, hcases⟩ := hpair
  have hpow : a ^ (p ^ e + 1) = 1 := by
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact pow_eq_one_of_normalizes_conj θ hker c
        (fun b hb h => pow_eq_one_of_normalizes_B12 hb h) (B23_perfect_su hK hq) haU hanorm
    · exact pow_eq_one_of_normalizes_conj θ hker c
        (fun b hb h => pow_eq_one_of_normalizes_B23 hb h) (B12_perfect_su hK hq) haU hanorm
  have hdvd : p ^ e - 1 ∣ p ^ e + 1 := hao ▸ orderOf_dvd_of_pow_eq_one hpow
  have h2 : p ^ e - 1 ∣ 2 := by
    have := Nat.dvd_sub hdvd (dvd_refl (p ^ e - 1))
    have e2 : p ^ e + 1 - (p ^ e - 1) = 2 := by omega
    rwa [e2] at this
  have := Nat.le_of_dvd (by norm_num) h2
  omega

end CFSG.ClassicalInvolution.RouteD.LieBridge
