module

public import CFSG.LocalAnalysis.SectionRank.OddCover.UnitaryThree
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Class2

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open Matrix CFSG.LieType.Universal.Unitary CFSG.SectionRank.OddCover
open scoped commutatorElement

structure SUInv {K : Type} [Field K] (σ : K ≃+* K) : Prop where
  invol : ∀ c, σ (σ c) = c
  two_ne_zero : (2 : K) ≠ 0

section Heisenberg

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def b0 (σ : K ≃+* K) (a : K) : K := -(σ a * a) / 2

theorem b0_rel (H : SUInv σ) (a : K) : b0 σ a + σ (b0 σ a) + σ a * a = 0 := by
  have h2 := H.two_ne_zero
  have := H.invol a
  simp only [b0, map_div₀, map_neg, map_mul, map_ofNat, this]
  field_simp
  ring

@[expose] noncomputable def xSU (H : SUInv σ) (a : K) : SU σ 3 :=
  heisSU H.invol a (b0 σ a) (b0_rel H a)

theorem zrel (β : traceZero σ) : (β : K) + σ (β : K) + σ 0 * 0 = 0 := by
  have := β.2
  simpa [traceZero] using this

@[expose] noncomputable def zSU (H : SUInv σ) (β : traceZero σ) : SU σ 3 :=
  heisSU H.invol 0 β (zrel β)

theorem coe_xSU (H : SUInv σ) (a : K) :
    (((xSU H a : SU σ 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      heisenbergMatrix σ (0 : Fin 3) 1 a (b0 σ a) := rfl

theorem coe_zSU (H : SUInv σ) (β : traceZero σ) :
    (((zSU H β : SU σ 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      heisenbergMatrix σ (0 : Fin 3) 1 0 (β : K) := rfl

@[expose] def gamSU (H : SUInv σ) (a a' : K) : traceZero σ :=
  ⟨(σ a * a' - a * σ a') / 2, by
    have h2 := H.two_ne_zero
    change (σ a * a' - a * σ a') / 2 + σ ((σ a * a' - a * σ a') / 2) = 0
    simp only [map_div₀, map_sub, map_mul, map_ofNat, H.invol]
    field_simp
    ring⟩

theorem coe_gamSU (H : SUInv σ) (a a' : K) :
    ((gamSU H a a' : traceZero σ) : K) = (σ a * a' - a * σ a') / 2 := rfl

theorem xSU_mul (H : SUInv σ) (a a' : K) :
    xSU H a * xSU H a' = xSU H (a + a') * zSU H (gamSU H a a') := by
  have h2 := H.two_ne_zero
  apply SU_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_xSU, coe_xSU, coe_xSU, coe_zSU, heis_mul, heis_mul]
  congr 1
  · simp
  · simp only [b0, map_add, coe_gamSU, map_zero, mul_zero, sub_zero]
    field_simp
    ring

theorem zSU_mul (H : SUInv σ) (β β' : traceZero σ) :
    zSU H β * zSU H β' = zSU H (β + β') := by
  apply SU_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_zSU, coe_zSU, coe_zSU, heis_mul]
  simp

theorem zSU_zero (H : SUInv σ) : zSU H 0 = 1 := by
  apply SU_ext
  rw [coe_zSU]
  simp [heisenbergMatrix_zero]

theorem xSU_zero (H : SUInv σ) : xSU H 0 = 1 := by
  apply SU_ext
  rw [coe_xSU]
  simp [b0, heisenbergMatrix_zero]

theorem zSU_inv (H : SUInv σ) (β : traceZero σ) : (zSU H β)⁻¹ = zSU H (-β) := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [zSU_mul, add_neg_cancel, zSU_zero]

theorem zSU_mul_comm (H : SUInv σ) (β β' : traceZero σ) :
    zSU H β * zSU H β' = zSU H β' * zSU H β := by
  rw [zSU_mul, zSU_mul, add_comm]

theorem zSU_commute_xSU (H : SUInv σ) (β : traceZero σ) (a : K) :
    Commute (zSU H β) (xSU H a) :=
  commute_heisSU_zero (σ := σ) H.invol β a (b0 σ a) (zrel β) (b0_rel H a)

end Heisenberg

section Torus

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] noncomputable def dMatSU (σ : K ≃+* K) (t : Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  diagonal ![(t : K), σ t / t, (σ t)⁻¹]

theorem dMatSU_mul (t t' : Kˣ) : dMatSU σ t * dMatSU σ t' = dMatSU σ (t * t') := by
  have h1 : (t : K) ≠ 0 := t.ne_zero
  have h2 : (t' : K) ≠ 0 := t'.ne_zero
  have h3 : σ (t : K) ≠ 0 := by simp
  have h4 : σ (t' : K) ≠ 0 := by simp
  simp only [dMatSU, diagonal_mul_diagonal, Units.val_mul, map_mul]
  congr 1
  funext i
  fin_cases i <;> simp <;> field_simp

theorem dMatSU_one : dMatSU σ (1 : Kˣ) = 1 := by
  simp only [dMatSU, Units.val_one, map_one, div_one, inv_one]
  rw [← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem det_dMatSU (t : Kˣ) : (dMatSU σ t).det = 1 := by
  have h1 : (t : K) ≠ 0 := t.ne_zero
  have h3 : σ (t : K) ≠ 0 := by simp
  simp only [dMatSU, det_diagonal, Fin.prod_univ_three]
  simp
  field_simp

theorem conjTr_dMatSU (hσ : ∀ c, σ (σ c) = c) (t : Kˣ) :
    conjTr σ (dMatSU σ t) * antidiag 3 * dMatSU σ t = antidiag 3 := by
  have h1 : (t : K) ≠ 0 := t.ne_zero
  have h3 : σ (t : K) ≠ 0 := by simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, dMatSU, antidiag, Matrix.mul_apply, Fin.sum_univ_three, diagonal, Fin.rev, hσ]

@[expose] noncomputable def dSU (H : SUInv σ) : Kˣ →* SU σ 3 where
  toFun t := ⟨⟨dMatSU σ t, dMatSU σ t⁻¹, by rw [dMatSU_mul, mul_inv_cancel, dMatSU_one],
    by rw [dMatSU_mul, inv_mul_cancel, dMatSU_one]⟩, det_dMatSU t, conjTr_dMatSU H.invol t⟩
  map_one' := by
    apply SU_ext
    change dMatSU σ (1 : Kˣ) = 1
    exact dMatSU_one
  map_mul' t t' := by
    apply SU_ext
    change dMatSU σ (t * t') = dMatSU σ t * dMatSU σ t'
    rw [dMatSU_mul]

theorem coe_dSU (H : SUInv σ) (t : Kˣ) :
    (((dSU H t : SU σ 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = dMatSU σ t := rfl

theorem dMatSU_mul_heis (hσ : ∀ c, σ (σ c) = c) (t : Kˣ) (a b : K) :
    dMatSU σ t * heisenbergMatrix σ (0 : Fin 3) 1 a b =
      heisenbergMatrix σ (0 : Fin 3) 1 ((t : K) ^ 2 / σ t * a) ((t : K) * σ t * b) *
        dMatSU σ t := by
  have h1 : (t : K) ≠ 0 := t.ne_zero
  have h3 : σ (t : K) ≠ 0 := by simp
  rw [CFSG.LieType.Steinberg.heisenbergMatrix_three, CFSG.LieType.Steinberg.heisenbergMatrix_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMatSU, Matrix.mul_apply, diagonal, hσ] <;> field_simp

@[expose] def nrmSU (H : SUInv σ) (t : Kˣ) (β : traceZero σ) : traceZero σ :=
  ⟨(t : K) * σ t * β, by
    have h : (β : K) + σ (β : K) = 0 := β.2
    change (t : K) * σ t * β + σ ((t : K) * σ t * β) = 0
    rw [map_mul, map_mul, H.invol]
    have hσβ : σ (β : K) = -β := by linear_combination h
    rw [hσβ]
    ring⟩

theorem coe_nrmSU (H : SUInv σ) (t : Kˣ) (β : traceZero σ) :
    ((nrmSU H t β : traceZero σ) : K) = (t : K) * σ t * β := rfl

theorem dSU_mul_xSU (H : SUInv σ) (t : Kˣ) (a : K) :
    dSU H t * xSU H a = xSU H ((t : K) ^ 2 / σ t * a) * dSU H t := by
  have h1 : (t : K) ≠ 0 := t.ne_zero
  have h2 := H.two_ne_zero
  have h3 : σ (t : K) ≠ 0 := by simp
  apply SU_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_dSU, coe_xSU, coe_xSU, dMatSU_mul_heis H.invol]
  congr 2
  simp only [b0, map_mul, map_div₀, map_pow, H.invol]
  field_simp

theorem dSU_mul_zSU (H : SUInv σ) (t : Kˣ) (β : traceZero σ) :
    dSU H t * zSU H β = zSU H (nrmSU H t β) * dSU H t := by
  apply SU_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_dSU, coe_zSU, coe_zSU, dMatSU_mul_heis H.invol]
  simp [coe_nrmSU]

end Torus

section Subgroups

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem xSU_mul_zSU_comm (H : SUInv σ) (a : K) (β : traceZero σ) :
    xSU H a * zSU H β = zSU H β * xSU H a := ((zSU_commute_xSU H β a).eq).symm

theorem xSU_neg_mul (H : SUInv σ) (a : K) :
    xSU H a * xSU H (-a) = zSU H (gamSU H a (-a)) := by
  rw [xSU_mul, add_neg_cancel, xSU_zero, one_mul]

theorem zSU_mul_assoc_comm (H : SUInv σ) (a : K) (β β' : traceZero σ) :
    xSU H a * zSU H β * zSU H β' = xSU H a * zSU H (β + β') := by
  rw [mul_assoc, zSU_mul]

@[expose] def Usu (H : SUInv σ) : Subgroup (SU σ 3) where
  carrier := {g | ∃ (a : K) (β : traceZero σ), g = xSU H a * zSU H β}
  one_mem' := ⟨0, 0, by rw [xSU_zero, zSU_zero, one_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨a, β, rfl⟩ ⟨a', β', rfl⟩
    refine ⟨a + a', gamSU H a a' + β + β', ?_⟩
    calc xSU H a * zSU H β * (xSU H a' * zSU H β')
        = xSU H a * (zSU H β * xSU H a') * zSU H β' := by group
      _ = xSU H a * (xSU H a' * zSU H β) * zSU H β' := by rw [← xSU_mul_zSU_comm]
      _ = (xSU H a * xSU H a') * zSU H β * zSU H β' := by group
      _ = xSU H (a + a') * (zSU H (gamSU H a a') * zSU H β * zSU H β') := by
        rw [xSU_mul]; group
      _ = xSU H (a + a') * zSU H (gamSU H a a' + β + β') := by
        rw [zSU_mul, zSU_mul]
  inv_mem' := by
    rintro _ ⟨a, β, rfl⟩
    refine ⟨-a, -gamSU H a (-a) - β, ?_⟩
    have h1 : (xSU H a)⁻¹ = xSU H (-a) * zSU H (-gamSU H a (-a)) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← mul_assoc, xSU_neg_mul, zSU_mul, add_neg_cancel, zSU_zero]
    rw [_root_.mul_inv_rev, h1, zSU_inv]
    calc zSU H (-β) * (xSU H (-a) * zSU H (-gamSU H a (-a)))
        = xSU H (-a) * (zSU H (-β) * zSU H (-gamSU H a (-a))) := by
          rw [← mul_assoc, (zSU_commute_xSU H (-β) (-a)).eq, mul_assoc]
      _ = xSU H (-a) * zSU H (-gamSU H a (-a) - β) := by
          rw [zSU_mul]
          congr 2
          abel

@[expose] def Zsu (H : SUInv σ) : Subgroup (SU σ 3) where
  carrier := {g | ∃ β : traceZero σ, g = zSU H β}
  one_mem' := ⟨0, (zSU_zero H).symm⟩
  mul_mem' := by
    rintro _ _ ⟨β, rfl⟩ ⟨β', rfl⟩
    exact ⟨β + β', zSU_mul H β β'⟩
  inv_mem' := by
    rintro _ ⟨β, rfl⟩
    exact ⟨-β, zSU_inv H β⟩

theorem mem_Usu (H : SUInv σ) {g : SU σ 3} :
    g ∈ Usu H ↔ ∃ (a : K) (β : traceZero σ), g = xSU H a * zSU H β := Iff.rfl

theorem mem_Zsu (H : SUInv σ) {g : SU σ 3} : g ∈ Zsu H ↔ ∃ β : traceZero σ, g = zSU H β :=
  Iff.rfl

theorem zSU_mem_Zsu (H : SUInv σ) (β : traceZero σ) : zSU H β ∈ Zsu H := ⟨β, rfl⟩

theorem xSU_mem_Usu (H : SUInv σ) (a : K) : xSU H a ∈ Usu H :=
  ⟨a, 0, by rw [zSU_zero, mul_one]⟩

theorem Zsu_le_Usu (H : SUInv σ) : Zsu H ≤ Usu H := by
  rintro _ ⟨β, rfl⟩
  exact ⟨0, β, by rw [xSU_zero, one_mul]⟩

theorem zSU_comm_of_mem_Usu (H : SUInv σ) {g : SU σ 3} (hg : g ∈ Usu H) (β : traceZero σ) :
    ⁅g, zSU H β⁆ = 1 := by
  obtain ⟨a, β', rfl⟩ := hg
  rw [commutatorElement_eq_one_iff_mul_comm]
  calc xSU H a * zSU H β' * zSU H β = xSU H a * (zSU H β' * zSU H β) := by rw [mul_assoc]
    _ = xSU H a * (zSU H β * zSU H β') := by rw [zSU_mul_comm]
    _ = xSU H a * zSU H β * zSU H β' := by rw [← mul_assoc]
    _ = zSU H β * xSU H a * zSU H β' := by rw [xSU_mul_zSU_comm]
    _ = zSU H β * (xSU H a * zSU H β') := by rw [mul_assoc]

theorem xSU_comm (H : SUInv σ) (a a' : K) :
    ⁅xSU H a, xSU H a'⁆ = zSU H (gamSU H a a' - gamSU H a' a) := by
  have h1 : xSU H a * xSU H a' = xSU H (a + a') * zSU H (gamSU H a a') := xSU_mul H a a'
  have h2 : xSU H a' * xSU H a = xSU H (a + a') * zSU H (gamSU H a' a) := by
    rw [xSU_mul, add_comm a' a]
  have h3 : zSU H (gamSU H a a' - gamSU H a' a) =
      zSU H (gamSU H a a') * (zSU H (gamSU H a' a))⁻¹ := by
    rw [zSU_inv, zSU_mul, sub_eq_add_neg]
  rw [commutatorElement_def, h3]
  calc xSU H a * xSU H a' * (xSU H a)⁻¹ * (xSU H a')⁻¹
      = (xSU H a * xSU H a') * (xSU H a' * xSU H a)⁻¹ := by group
    _ = _ := by
      rw [h1, h2]
      have hA : xSU H (a + a') * zSU H (gamSU H a a') = zSU H (gamSU H a a') * xSU H (a + a') :=
        xSU_mul_zSU_comm H _ _
      have hB : xSU H (a + a') * (zSU H (gamSU H a' a))⁻¹ =
          (zSU H (gamSU H a' a))⁻¹ * xSU H (a + a') :=
        ((zSU_commute_xSU H (gamSU H a' a) (a + a')).inv_left.eq).symm
      calc xSU H (a + a') * zSU H (gamSU H a a') * (xSU H (a + a') * zSU H (gamSU H a' a))⁻¹
          = (xSU H (a + a') * zSU H (gamSU H a a')) * (zSU H (gamSU H a' a))⁻¹ *
              (xSU H (a + a'))⁻¹ := by rw [_root_.mul_inv_rev]; group
        _ = (zSU H (gamSU H a a') * xSU H (a + a')) * (zSU H (gamSU H a' a))⁻¹ *
              (xSU H (a + a'))⁻¹ := by rw [hA]
        _ = zSU H (gamSU H a a') * (xSU H (a + a') * (zSU H (gamSU H a' a))⁻¹) *
              (xSU H (a + a'))⁻¹ := by group
        _ = zSU H (gamSU H a a') * ((zSU H (gamSU H a' a))⁻¹ * xSU H (a + a')) *
              (xSU H (a + a'))⁻¹ := by rw [hB]
        _ = zSU H (gamSU H a a') * (zSU H (gamSU H a' a))⁻¹ := by group

theorem comm_mem_Zsu (H : SUInv σ) {g h : SU σ 3} (hg : g ∈ Usu H) (hh : h ∈ Usu H) :
    ⁅g, h⁆ ∈ Zsu H := by
  obtain ⟨a, β, rfl⟩ := hg
  obtain ⟨a', β', rfl⟩ := hh
  have hcent : ∀ y ∈ Zsu H, ∀ g ∈ Usu H, ⁅g, y⁆ = 1 := by
    rintro _ ⟨β, rfl⟩ g hg
    exact zSU_comm_of_mem_Usu H hg β
  rw [comm_mul_mem_right hcent ⟨a, β, rfl⟩ (zSU_mem_Zsu H β'),
    comm_mul_mem_left hcent (xSU_mem_Usu H a') (zSU_mem_Zsu H β), xSU_comm]
  exact zSU_mem_Zsu H _

theorem coe_xSU_mul_zSU (H : SUInv σ) (a : K) (β : traceZero σ) :
    (((xSU H a * zSU H β : SU σ 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, a, b0 σ a + β; 0, 1, -σ a; 0, 0, 1] := by
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_xSU, coe_zSU, heis_mul, CFSG.LieType.Steinberg.heisenbergMatrix_three]
  simp

theorem xSU_mul_zSU_injective (H : SUInv σ) {a a' : K} {β β' : traceZero σ}
    (h : xSU H a * zSU H β = xSU H a' * zSU H β') : a = a' ∧ β = β' := by
  have h' := congrArg (fun g : SU σ 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
  simp only [coe_xSU_mul_zSU] at h'
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 1) h'
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) h'
  simp at h01 h02
  subst h01
  exact ⟨rfl, Subtype.ext (add_left_cancel h02)⟩

theorem card_Usu [Finite K] (H : SUInv σ) :
    Nat.card (Usu H) = Nat.card K * Nat.card (traceZero σ) := by
  let f : K × traceZero σ → Usu H := fun x => ⟨xSU H x.1 * zSU H x.2, x.1, x.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2⟩ := xSU_mul_zSU_injective H (congrArg Subtype.val h)
      exact Prod.ext h1 h2
    · obtain ⟨g, a, β, rfl⟩ := g
      exact ⟨(a, β), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem dSU_conj_xSU (H : SUInv σ) (t : Kˣ) (a : K) :
    dSU H t * xSU H a * (dSU H t)⁻¹ = xSU H ((t : K) ^ 2 / σ t * a) := by
  rw [dSU_mul_xSU, mul_inv_cancel_right]

theorem dSU_conj_zSU (H : SUInv σ) (t : Kˣ) (β : traceZero σ) :
    dSU H t * zSU H β * (dSU H t)⁻¹ = zSU H (nrmSU H t β) := by
  rw [dSU_mul_zSU, mul_inv_cancel_right]

theorem dSU_conj_zSU_of_norm_neg_one (H : SUInv σ) {t : Kˣ} (ht : σ t * t = -1)
    (β : traceZero σ) : dSU H t * zSU H β * (dSU H t)⁻¹ = zSU H (-β) := by
  rw [dSU_conj_zSU]
  congr 1
  apply Subtype.ext
  rw [coe_nrmSU]
  change (t : K) * σ t * β = -β
  linear_combination (β : K) * ht

theorem dSU_conj_zSU_of_norm_one (H : SUInv σ) {t : Kˣ} (ht : σ t * t = 1)
    (β : traceZero σ) : dSU H t * zSU H β * (dSU H t)⁻¹ = zSU H β := by
  rw [dSU_conj_zSU]
  congr 1
  apply Subtype.ext
  rw [coe_nrmSU]
  linear_combination (β : K) * ht

theorem exists_comm_eq_zSU (H : SUInv σ) (β : traceZero σ) :
    ∃ a a' : K, ⁅xSU H a, xSU H a'⁆ = zSU H β := by
  have h2 := H.two_ne_zero
  refine ⟨1, (β : K) / 2, ?_⟩
  rw [xSU_comm]
  congr 1
  apply Subtype.ext
  have hβ : σ (β : K) = -β := by
    have h : (β : K) + σ (β : K) = 0 := β.2
    linear_combination h
  simp only [AddSubgroup.coe_sub, coe_gamSU, map_one, map_div₀, map_ofNat, hβ, one_mul, mul_one]
  field_simp
  ring

theorem exists_mul_comm_eq (H : SUInv σ) {t : Kˣ} (hlam : (t : K) ^ 2 / σ t ≠ 1) (a : K)
    (β : traceZero σ) : ∃ (a₁ : K) (γ : traceZero σ),
      xSU H a * zSU H β =
        zSU H γ * (dSU H t * xSU H a₁ * (dSU H t)⁻¹ * (xSU H a₁)⁻¹) := by
  set lam : K := (t : K) ^ 2 / σ t with hlamdef
  have hlam1 : lam - 1 ≠ 0 := sub_ne_zero.2 hlam
  set a₁ : K := a / (lam - 1) with ha₁
  have hmul : (lam - 1) * a₁ = a := by rw [ha₁]; field_simp
  have hla : lam * a₁ = a + a₁ := by linear_combination hmul
  refine ⟨a₁, β + gamSU H a a₁, ?_⟩
  have hx : xSU H (a + a₁) = xSU H a * xSU H a₁ * (zSU H (gamSU H a a₁))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← xSU_mul]
  have hc : xSU H a₁ * (zSU H (gamSU H a a₁))⁻¹ = (zSU H (gamSU H a a₁))⁻¹ * xSU H a₁ :=
    ((zSU_commute_xSU H (gamSU H a a₁) a₁).inv_left.eq).symm
  have e1 : xSU H a * xSU H a₁ * (zSU H (gamSU H a a₁))⁻¹ * (xSU H a₁)⁻¹ =
      xSU H a * (zSU H (gamSU H a a₁))⁻¹ := by
    calc _ = xSU H a * (xSU H a₁ * (zSU H (gamSU H a a₁))⁻¹) * (xSU H a₁)⁻¹ := by group
      _ = xSU H a * ((zSU H (gamSU H a a₁))⁻¹ * xSU H a₁) * (xSU H a₁)⁻¹ := by rw [hc]
      _ = _ := by group
  have hconj : zSU H (gamSU H a a₁) * xSU H a * (zSU H (gamSU H a a₁))⁻¹ = xSU H a := by
    rw [(zSU_commute_xSU H (gamSU H a a₁) a).eq, mul_inv_cancel_right]
  rw [dSU_conj_xSU, ← hlamdef, hla, hx, e1, ← zSU_mul]
  calc xSU H a * zSU H β = zSU H β * xSU H a := xSU_mul_zSU_comm H a β
    _ = zSU H β * (zSU H (gamSU H a a₁) * xSU H a * (zSU H (gamSU H a a₁))⁻¹) := by rw [hconj]
    _ = zSU H β * zSU H (gamSU H a a₁) * (xSU H a * (zSU H (gamSU H a a₁))⁻¹) := by group

end Subgroups

section Unitary

open CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]

theorem suInv_unitary (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    SUInv (unitaryInvolution F p f) := by
  refine ⟨unitaryInvolution_involutive hF, fun h => ?_⟩
  have h2 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2)

theorem card_Usu_unitary (hF : Nat.card F = (p ^ f) ^ 2) (H : SUInv (unitaryInvolution F p f)) :
    Nat.card (Usu H) = (p ^ f) ^ 3 := by
  rw [card_Usu, card_traceZero hF, hF]
  ring

theorem isPGroup_Usu (hF : Nat.card F = (p ^ f) ^ 2) (H : SUInv (unitaryInvolution F p f)) :
    IsPGroup p (Usu H) := by
  apply IsPGroup.of_card (n := 3 * f)
  rw [card_Usu_unitary hF H, ← pow_mul, mul_comm]

theorem not_dvd_index_Usu (hF : Nat.card F = (p ^ f) ^ 2) (hf : 1 ≤ f)
    (H : SUInv (unitaryInvolution F p f)) : ¬ p ∣ (Usu H).index := by
  have hq : 2 ≤ p ^ f := by
    have := hp.out.two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.out.pos hf
  have h1 : (Usu H).index = ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
    have h := (Usu H).card_mul_index
    rw [card_Usu_unitary hF H, card_SU_three hF, mul_assoc] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) 3) h
  have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hp' := hp.out
  rw [h1]
  intro h
  rcases (Nat.Prime.dvd_mul hp').1 h with h2 | h2
  · have h3 : p ∣ (p ^ f) ^ 2 := dvd_pow hpq (by omega)
    have := Nat.dvd_sub h3 h2
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at this
    exact hp'.one_lt.ne' (Nat.dvd_one.1 this)
  · have h3 : p ∣ (p ^ f) ^ 3 := dvd_pow hpq (by omega)
    exact hp'.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h3).1 h2))

end Unitary

end CFSG.ClassicalInvolution.ModelFacts.OddCover
