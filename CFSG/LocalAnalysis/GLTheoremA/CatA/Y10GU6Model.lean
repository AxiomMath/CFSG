module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU6Diag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU6Burg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GU6

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA.SFM12

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

theorem model_fix [Finite F] (hF : Nat.card F = (2 ^ 2) ^ 2) {g : ↥(StatedSU 6 (2 ^ 2) F)}
    (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1)
    {J : Subgroup ↥(StatedSU 6 (2 ^ 2) F)} (hJq : CFSG.Open.IsQuasisimple J)
    (hJC : J ≤ Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)))
    (hnorm : ∀ c ∈ Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)), ∀ j ∈ J,
      c * j * c⁻¹ ∈ J)
    (h41 : 41 ∣ Nat.card J)
    (α : MulAut ↥(StatedSU 6 (2 ^ 2) F)) (hαJ : ∀ j ∈ J, α j = j) :
    ∃ j : ℕ, ∀ s : ↥(StatedSU 6 (2 ^ 2) F), α s = g ^ j * s * (g ^ j)⁻¹ := by
  classical
  have hR := unitaryDiagFact_holds
  unfold UnitaryDiagFact at hR
  obtain ⟨P, d, hPd⟩ := hR F hF g hg5
  set g' : ↥(StatedSU 6 (2 ^ 2) F) := P * g * P⁻¹ with hg'def
  have hg'5 : g' ^ 5 = 1 := by
    have h1 : (MulAut.conj P g) ^ 5 = 1 := by rw [← map_pow, hg5, map_one]
    simpa [MulAut.conj_apply, hg'def, mul_assoc] using h1
  have hg'1 : g' ≠ 1 := by
    intro h
    apply hg1
    have h2 : P * g = P := by
      have := congrArg (· * P) h
      simpa [hg'def, mul_assoc] using this
    exact mul_left_cancel (h2.trans (mul_one P).symm)
  have hgd : (g' : GL (Fin 6) F).val = Matrix.diagonal d := hPd
  have hd5 : ∀ k, d k ^ 5 = 1 := by
    have h5 := congrArg (fun x : ↥(StatedSU 6 (2 ^ 2) F) => ((x : GL (Fin 6) F).val)) hg'5
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hgd, Units.val_one, one_pow] at h5
    intro k
    have h6 := congrFun (congrFun h5 k) k
    rw [Matrix.diagonal_pow] at h6
    simpa [Matrix.diagonal_apply] using h6
  have hcentr : ∀ (h x : ↥(StatedSU 6 (2 ^ 2) F)),
      x ∈ Subgroup.centralizer ({h} : Set ↥(StatedSU 6 (2 ^ 2) F)) ↔ h * x = x * h := by
    intro h x
    rw [Subgroup.mem_centralizer_iff]
    simp
  have hKq : CFSG.Open.IsQuasisimple (J.map (MulAut.conj P).toMonoidHom) :=
    hJq.of_mulEquiv (Subgroup.equivMapOfInjective J _ (MulAut.conj P).injective).symm
  have h41K : 41 ∣ Nat.card (J.map (MulAut.conj P).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj P).injective]
    exact h41
  have hKC : J.map (MulAut.conj P).toMonoidHom ≤
      Subgroup.centralizer ({g'} : Set ↥(StatedSU 6 (2 ^ 2) F)) := by
    intro x hx
    rw [mem_conj_map'] at hx
    rw [hcentr]
    have hx' : x = P * (P⁻¹ * x * P) * P⁻¹ := by group
    rw [hx']
    have hk := hJC hx
    rw [hcentr] at hk
    calc g' * (P * (P⁻¹ * x * P) * P⁻¹)
        = P * (g * (P⁻¹ * x * P)) * P⁻¹ := by rw [hg'def]; group
      _ = P * ((P⁻¹ * x * P) * g) * P⁻¹ := by rw [hk]
      _ = P * (P⁻¹ * x * P) * P⁻¹ * g' := by rw [hg'def]; group
  have hnorm' : ∀ c ∈ Subgroup.centralizer ({g'} : Set ↥(StatedSU 6 (2 ^ 2) F)),
      ∀ j ∈ J.map (MulAut.conj P).toMonoidHom,
        c * j * c⁻¹ ∈ J.map (MulAut.conj P).toMonoidHom := by
    intro c hc j hj
    rw [hcentr] at hc
    rw [mem_conj_map'] at hj ⊢
    have hc0 : P⁻¹ * c * P ∈ Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)) := by
      rw [hcentr]
      have h1 : c * g' = g' * c := hc.symm
      calc g * (P⁻¹ * c * P) = P⁻¹ * (P * g * P⁻¹) * c * P := by group
        _ = P⁻¹ * (c * (P * g * P⁻¹)) * P := by rw [← hg'def, h1]; group
        _ = P⁻¹ * c * P * g := by group
    have e : P⁻¹ * (c * j * c⁻¹) * P = (P⁻¹ * c * P) * (P⁻¹ * j * P) * (P⁻¹ * c * P)⁻¹ := by
      group
    rw [e]
    exact hnorm _ hc0 _ hj
  obtain ⟨l0, hW, hUg⟩ := block_card_five hF hgd hd5 hg'1 hKq hKC hnorm' h41K
  have hdet : ∏ k, d k = 1 := by
    rw [← Matrix.det_diagonal, ← hgd]
    exact ((mem_SU_iff hF (g' : GL (Fin 6) F)).1 g'.2).1
  have hl0 : l0 ≠ 1 := by
    intro h1
    apply hg'1
    have hall : ∀ k, d k = 1 := by
      intro k
      by_cases hk : d k = l0
      · rw [hk, h1]
      · exact compl_eq_one hW hd5 hdet k hk
    apply Subtype.ext
    apply Units.ext
    show (g' : GL (Fin 6) F).val = 1
    rw [hgd]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, hall]
  have hl5 : l0 ^ 5 = 1 := by
    obtain ⟨k1, hk1⟩ := Finset.card_pos.1 (by omega : 0 < (Eset d l0).card)
    rw [← (mem_Eset' d l0 k1).1 hk1]
    exact hd5 k1
  let αP : MulAut ↥(StatedSU 6 (2 ^ 2) F) := MulAut.conj P * α * MulAut.conj P⁻¹
  have hfix : ∀ x : ↥(StatedSU 6 (2 ^ 2) F), x ∈ Ug d l0 → αP x = x := by
    intro x hx
    have hxK : x ∈ J.map (MulAut.conj P).toMonoidHom := hUg hx
    rw [mem_conj_map'] at hxK
    have h1 := hαJ _ hxK
    show P * α (P⁻¹ * x * P⁻¹⁻¹) * P⁻¹ = x
    rw [inv_inv, h1]
    group
  obtain ⟨A, hAuni, φ, hAφ⟩ := transport_fix hF αP
  have hrel : ∀ x : ↥(StatedSU 6 (2 ^ 2) F), x ∈ Ug d l0 →
      (A : Matrix (Fin 6) (Fin 6) F) * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map φ =
        ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (A : Matrix (Fin 6) (Fin 6) F) := by
    intro x hx
    have e := hAφ x
    have ex : ((αP x : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) = (x : GL (Fin 6) F) :=
      congrArg Subtype.val (hfix x hx)
    rw [ex] at e
    have hBA : ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (A : Matrix (Fin 6) (Fin 6) F) = 1 :=
      Units.inv_mul A
    conv_rhs => rw [e]
    simp only [Matrix.mul_assoc, hBA, Matrix.mul_one]
  obtain ⟨j, b, hb0, hAeq, hφid⟩ := diag_fix hF hl0 hl5 hW hd5 hdet A hAuni φ hrel
  have hDu : ((g' ^ j : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F).val =
      Matrix.diagonal (fun k => d k ^ j) := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hgd, Matrix.diagonal_pow]
    rfl
  let z : GL (Fin 6) F := Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 b hb0)
  have hzval : (z : Matrix (Fin 6) (Fin 6) F) = Matrix.scalar (Fin 6) b := by
    simp [z, Matrix.GeneralLinearGroup.coe_scalar]
  have hzc : ∀ X : GL (Fin 6) F, z * X = X * z := by
    intro X
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hzval]
    exact Matrix.scalar_commute b (fun r' => mul_comm b r') _
  have hconj : ∀ X : GL (Fin 6) F, z * X * z⁻¹ = X := fun X => by
    rw [hzc X, mul_assoc, mul_inv_cancel, mul_one]
  let Du : GL (Fin 6) F := ((g' ^ j : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F)
  have hAGL : (A : GL (Fin 6) F) = z * Du := by
    apply Units.ext
    rw [Units.val_mul, hzval]
    exact hAeq.trans (by rw [hDu])
  have hconjA : ∀ s : GL (Fin 6) F, (A : GL (Fin 6) F) * s * (A⁻¹ : GL (Fin 6) F) =
      Du * s * Du⁻¹ := by
    intro s
    rw [hAGL]
    calc z * Du * s * (z * Du)⁻¹ = z * (Du * s * Du⁻¹) * z⁻¹ := by group
      _ = Du * s * Du⁻¹ := hconj _
  have hmapid : ∀ M : Matrix (Fin 6) (Fin 6) F, M.map φ = M := fun M => by
    ext r s
    simp [hφid]
  have hαs : ∀ s : ↥(StatedSU 6 (2 ^ 2) F), αP s = g' ^ j * s * (g' ^ j)⁻¹ := by
    intro s
    apply Subtype.ext
    apply Units.ext
    have h1 := hAφ s
    rw [hmapid] at h1
    have h2 := congrArg Units.val (hconjA (s : GL (Fin 6) F))
    simp only [Units.val_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h2 ⊢
    exact h1.trans h2
  have hαP_apply : ∀ y : ↥(StatedSU 6 (2 ^ 2) F), αP (P * y * P⁻¹) = P * α y * P⁻¹ := by
    intro y
    show P * α (P⁻¹ * (P * y * P⁻¹) * P⁻¹⁻¹) * P⁻¹ = P * α y * P⁻¹
    have e : P⁻¹ * (P * y * P⁻¹) * P⁻¹⁻¹ = y := by group
    rw [e]
  refine ⟨j, fun y => ?_⟩
  have hPy := hαs (P * y * P⁻¹)
  rw [hαP_apply] at hPy
  have hgj : g' ^ j = P * g ^ j * P⁻¹ := by
    rw [hg'def, conj_pow]
  rw [hgj] at hPy
  calc α y = P⁻¹ * (P * α y * P⁻¹) * P := by group
    _ = P⁻¹ * (P * g ^ j * P⁻¹ * (P * y * P⁻¹) * (P * g ^ j * P⁻¹)⁻¹) * P := by rw [hPy]
    _ = g ^ j * y * (g ^ j)⁻¹ := by group

end CFSG.LocalAnalysis.GLTheoremA.Y10GU6
