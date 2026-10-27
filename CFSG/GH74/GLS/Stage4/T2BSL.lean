module

public import CFSG.GH74.GLS.Stage4.T2SL2C
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.L2.Lemma113

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Cent

variable {F : Type} [Field F]

@[expose] noncomputable def t2SlCent (g : GL (Fin 2) F) : Subgroup (SL2 F) :=
  (Subgroup.centralizer ({g} : Set (GL (Fin 2) F))).comap Matrix.SpecialLinearGroup.toGL

theorem mem_t2SlCent {g : GL (Fin 2) F} {M : SL2 F} :
    M ∈ t2SlCent g ↔ (M : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) := by
  rw [t2SlCent, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Units.ext_iff]
  rfl

theorem t2SlCent_cyclic [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hq : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (d : ℕ)
    (hd : (d : ℤ) = Nat.card F + ε) (g : GL (Fin 2) F)
    (hg2 : ∃ c : F, (g : Matrix (Fin 2) (Fin 2) F) * g = c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hns : ¬ ∃ s : F, (g : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F))
    (hdet : ¬ IsSquare (g : Matrix (Fin 2) (Fin 2) F).det) :
    IsCyclic ↥(t2SlCent g) ∧ Nat.card ↥(t2SlCent g) = d := by
  obtain ⟨hc, hcard⟩ := CFSG.GH74.GLS.IVK.slCentralizer_outer_involution ⟨hodd, h3⟩ ε hε hq d hd g
    hg2 hns hdet
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
  have hcent : CFSG.GH74.GLS.IVK.slCentralizer g = (t2SlCent g).map e.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv]
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [MulEquiv.symm_apply_apply]
    exact Iff.rfl
  rw [hcent] at hc hcard
  have eq1 := Subgroup.equivMapOfInjective (t2SlCent g) e.toMonoidHom e.injective
  refine ⟨eq1.isCyclic.2 hc, ?_⟩
  rw [← hcard]
  exact Nat.card_congr eq1.toEquiv

theorem t2B_exists_W [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (g : GL (Fin 2) F)
    (hsq : ∀ x : SL2 F, slConj (g * g) x = x)
    (hns : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) :
    ∃ W : SL2 F, W * W = negOne F ∧ slConj g W = W⁻¹ ∧
      (g : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F) =
        -((W : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  let α : MulAut (SL2 F) := MulEquiv.ofBijective (slConj g) ⟨slConj_injective g, slConj_surjective g⟩
  have hα : ∀ x, α x = slConj g x := fun x => rfl
  have hαα : α * α = 1 := by
    refine MulEquiv.ext fun x => ?_
    show α (α x) = x
    rw [hα, hα, ← slConj_mul]
    exact hsq x
  have hα1 : α ≠ 1 := by
    intro h1
    obtain ⟨s, hs⟩ := eq_scalar_of_slConj_eq g (fun x => by rw [← hα, h1]; rfl)
    apply hns
    refine ⟨s, ?_⟩
    have hd : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = (g : Matrix (Fin 2) (Fin 2) F).det :=
      rfl
    rw [hd, hs]
    simp [Matrix.det_one, sq]
  have hord : orderOf α = 2 := orderOf_eq_prime (by rw [pow_two]; exact hαα) hα1
  obtain ⟨W, hW4, hαW⟩ := CFSG.GH74.GLS.IVK.ivk_1_13 F hodd h3 (SL2 F)
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F) α hord
  have hWW1 : W * W ≠ 1 := by
    intro h1
    have : orderOf W ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [hW4] at this
    omega
  have hWW : (W * W) * (W * W) = 1 := by
    have : W ^ 4 = 1 := by rw [← hW4]; exact pow_orderOf_eq_one W
    calc (W * W) * (W * W) = W ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := this
  have hWWneg : W * W = negOne F := eq_negOne_of_involution h2 hWW hWW1
  refine ⟨W, hWWneg, hαW, ?_⟩
  have hWinv : (W⁻¹ : SL2 F) = W * negOne F := by
    calc W⁻¹ = W⁻¹ * (W * W) * (negOne F)⁻¹ * 1 := by
          rw [hWWneg]; group
      _ = W * negOne F := by
          have : (negOne F)⁻¹ = negOne F := inv_eq_of_mul_eq_one_right (negOne_mul_self)
          rw [this]; group
  have h1 : (slConj g W : SL2 F) = W⁻¹ := hαW
  have hmat : (g : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -(W : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun y : SL2 F => (y : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [coe_slConj] at this
    rw [this, hWinv, Matrix.SpecialLinearGroup.coe_mul, t2B_negOne_eq]
    simp
  have hgg : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
    simp
  calc (g : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F)
      = (g : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F) *
          (((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) := by
        rw [hgg, Matrix.mul_one]
    _ = ((g : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F) *
          ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * (g : Matrix (Fin 2) (Fin 2) F) := by
        simp only [Matrix.mul_assoc]
    _ = -((W : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) := by
        rw [hmat]; simp

end Cent

end CFSG.GH74.GLS.Stage4.Rest
