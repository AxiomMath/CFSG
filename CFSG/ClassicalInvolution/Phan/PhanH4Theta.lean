module

public import CFSG.ClassicalInvolution.Phan.PhanH2Neg
public import CFSG.ClassicalInvolution.Phan.PhanH3Levi

public section

namespace CFSG.ClassicalInvolution.PhanB3.H

open CliffordAlgebra QuadraticMap CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

variable {F : Type} [Field F]

variable {F : Type} [Field F]

@[expose] noncomputable def kappa :
    (Fin 2 ⊕ Fin 2 ⊕ Unit → F) →ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Unit → F) where
  toFun v := (2 * v (.inl 0)) • (Pi.single (.inl 1) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F)
    + (-(1 / 2) * v (.inr (.inl 0))) • (Pi.single (.inr (.inl 1)) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F)
    + v (.inl 1) • (Pi.single (.inl 2) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F)
    + (- v (.inr (.inl 1))) • (Pi.single (.inr (.inl 2)) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F)
    + v (.inr (.inr ())) • ((Pi.single (.inl 0) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F) -
        Pi.single (.inr (.inl 0)) 1)
  map_add' v w := by
    simp only [Pi.add_apply, mul_add, add_smul, neg_add]
    abel
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_sub, smul_smul]
    simp only [mul_neg, neg_mul, mul_left_comm c]

theorem kappa_apply (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) (s : Fin 3 ⊕ Fin 3 ⊕ Unit) :
    kappa v s = (2 * v (.inl 0)) * (Pi.single (.inl 1) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F) s
    + (-(1 / 2) * v (.inr (.inl 0))) * (Pi.single (.inr (.inl 1)) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F) s
    + v (.inl 1) * (Pi.single (.inl 2) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F) s
    + (- v (.inr (.inl 1))) * (Pi.single (.inr (.inl 2)) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F) s
    + v (.inr (.inr ())) * ((Pi.single (.inl 0) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F) s -
        (Pi.single (.inr (.inl 0)) 1 : Fin 3 ⊕ Fin 3 ⊕ Unit → F) s) := by
  simp [kappa]

theorem quad_kappa (h2 : (2 : F) ≠ 0) (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) :
    quadOdd 3 F (kappa v) = - quadOdd 2 F v := by
  rw [quadOdd_apply, quadOdd_apply]
  simp only [Fin.sum_univ_three, Fin.sum_univ_two, kappa_apply, Pi.single_apply]
  simp
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination (-(v (.inl 0) * v (.inr (.inl 0)))) * h

theorem kappa_injective (h2 : (2 : F) ≠ 0) : Function.Injective (kappa (F := F)) := by
  intro v w h
  have e1 := congrFun h (.inl 1)
  have e2 := congrFun h (.inl 2)
  have e3 := congrFun h (.inr (.inl 1))
  have e4 := congrFun h (.inr (.inl 2))
  have e5 := congrFun h (.inl 0)
  simp only [kappa_apply, Pi.single_apply] at e1 e2 e3 e4 e5
  simp at e1 e2 e3 e4 e5
  have e1' := e1.resolve_right h2
  have e3' := e3.resolve_right h2
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i
    · exact e1'
    · exact e2
  · fin_cases i
    · exact e3'
    · exact e4
  · exact e5

theorem exists_aux_kappa :
    ∃ a : Fin 3 ⊕ Fin 3 ⊕ Unit → F, IsUnit (quadOdd 3 F a) ∧
      ∀ v, polar (quadOdd 3 F) a (kappa v) = 0 := by
  refine ⟨Pi.single (.inr (.inr ())) 1, ?_, fun v => ?_⟩
  · simp [quadOdd_apply]
  · rw [polar_quadOdd]
    simp [kappa_apply, Pi.single_apply]

theorem exists_theta7 [Finite F] (hF : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) :
    ∃ (φ : StatedSp 2 F →* spinGroup (quadOdd 2 F)) (θ : StatedSp 2 F →* spinGroup (quadOdd 3 F)),
      IsLevi φ ∧ Function.Injective φ ∧ Function.Injective θ ∧
      (∀ g, (θ g : CliffordAlgebra (quadOdd 3 F)) =
        negSpinHom (quadOdd 2 F) (quadOdd 3 F) kappa (quad_kappa h2) (φ g)) ∧
      (∀ g v, spinAction (quadOdd 3 F) (θ g) (kappa v) = kappa (spinAction (quadOdd 2 F) (φ g) v)) ∧
      (∀ g (p : Fin 3 ⊕ Fin 3 ⊕ Unit → F), (∀ v, polar (quadOdd 3 F) p (kappa v) = 0) →
        spinAction (quadOdd 3 F) (θ g) p = p) ∧ LeviRoots φ := by
  obtain ⟨φ, hinj, hv, hroots⟩ := exists_levi_roots hF h2
  have hφ : IsLevi φ := hv
  have hroot : ∀ s ∈ spGens F, ∃ (w u : Fin 2 ⊕ Fin 2 ⊕ Unit → F) (c : F), quadOdd 2 F u = 0 ∧
      polar (quadOdd 2 F) u w = 0 ∧
      (φ s : CliffordAlgebra (quadOdd 2 F)) = 1 + c • (ι (quadOdd 2 F) w * ι (quadOdd 2 F) u) := by
    rintro s ⟨c, h | h | h | h⟩
    · subst h
      refine ⟨(oddFrame 2 F).z, (oddFrame 2 F).vec 1 true, c, (oddFrame 2 F).map_vec _ _, ?_, ?_⟩
      · exact (oddFrame 2 F).polar_vec_z _ _
      · rw [phi_Su hφ, OddFrame.coe_shortRoot]
    · subst h
      refine ⟨(oddFrame 2 F).z, (oddFrame 2 F).vec 1 false, -c, (oddFrame 2 F).map_vec _ _, ?_, ?_⟩
      · exact (oddFrame 2 F).polar_vec_z _ _
      · rw [phi_Sl hφ, OddFrame.coe_shortRoot]
    · subst h
      refine ⟨(oddFrame 2 F).vec 0 true, (oddFrame 2 F).vec 1 false, c, (oddFrame 2 F).map_vec _ _,
        ?_, ?_⟩
      · exact (oddFrame 2 F).polar_vec_of_ne (by decide) _ _
      · rw [phi_Lu hφ, HypFrame.coe_longRoot]
    · subst h
      refine ⟨(oddFrame 2 F).vec 1 true, (oddFrame 2 F).vec 0 false, c, (oddFrame 2 F).map_vec _ _,
        ?_, ?_⟩
      · exact (oddFrame 2 F).polar_vec_of_ne (by decide) _ _
      · rw [phi_Ll hφ, HypFrame.coe_longRoot]
  obtain ⟨θ, hcoe, hnat, hfix⟩ := exists_negTheta (quadOdd 2 F) (quadOdd 3 F) kappa
    (quad_kappa h2) φ closure_spGens hroot (exists_aux_kappa)
  refine ⟨φ, θ, hφ, hinj, ?_, hcoe, hnat, hfix, leviRoots_of_roots hroots⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : ∀ v, spinAction (quadOdd 2 F) (φ g) v = v := by
    intro v
    apply kappa_injective h2
    rw [← hnat, hg, map_one]
    rfl
  have hker := eq_one_or_eq_neg_one_of_spinAction_eq_one_odd 2 F h2 (φ g) (LinearEquiv.ext h1)
  rcases hker with h | h
  · exact hinj (by rw [map_one]; exact Subtype.ext (by rw [h]; rfl))
  · exfalso
    have hθ1 : (θ g : CliffordAlgebra (quadOdd 3 F)) = 1 := by rw [hg]; rfl
    have hev : (⟨(φ g : CliffordAlgebra (quadOdd 2 F)), spinGroup.mem_even (φ g).2⟩ :
        CliffordAlgebra.even (quadOdd 2 F)) = -1 := Subtype.ext h
    have h5 : (θ g : CliffordAlgebra (quadOdd 3 F)) = -1 := by
      rw [hcoe g, negSpinHom_apply, hev, map_neg, map_one]
    have h3 : (-1 : CliffordAlgebra (quadOdd 3 F)) = 1 := by rw [← h5, hθ1]
    have h4 : algebraMap F (CliffordAlgebra (quadOdd 3 F)) 2 = algebraMap F _ 0 := by
      rw [map_ofNat, map_zero]
      calc (2 : CliffordAlgebra (quadOdd 3 F)) = 1 + 1 := by norm_num
        _ = 1 + (-1) := by rw [h3]
        _ = 0 := by simp
    exact h2 (algebraMap_injective' (quadOdd 3 F) h4)

theorem spinAction_theta_eq {φ : StatedSp 2 F →* spinGroup (quadOdd 2 F)}
    {θ : StatedSp 2 F →* spinGroup (quadOdd 3 F)} (hφ : IsLevi φ)
    (hnat : ∀ g v, spinAction (quadOdd 3 F) (θ g) (kappa v) =
      kappa (spinAction (quadOdd 2 F) (φ g) v))
    (g : StatedSp 2 F) (v w : Fin 2 ⊕ Fin 2 ⊕ Unit → F)
    (h : iota5 w = mat 2 F g * iota5 v * (mat 2 F g).transpose) :
    spinAction (quadOdd 3 F) (θ g) (kappa v) = kappa w := by
  rw [hnat]
  congr 1
  apply iota5_injective
  rw [levi_intertwine hφ, h]

structure ThetaData (F : Type) [Field F] (h2 : (2 : F) ≠ 0) where
  φ : StatedSp 2 F →* spinGroup (quadOdd 2 F)
  θ : StatedSp 2 F →* spinGroup (quadOdd 3 F)
  isLevi : IsLevi φ
  leviRoots : LeviRoots φ
  φ_inj : Function.Injective φ
  θ_inj : Function.Injective θ
  coe_θ : ∀ g, (θ g : CliffordAlgebra (quadOdd 3 F)) =
    negSpinHom (quadOdd 2 F) (quadOdd 3 F) kappa (quad_kappa h2) (φ g)
  nat : ∀ g v, spinAction (quadOdd 3 F) (θ g) (kappa v) =
    kappa (spinAction (quadOdd 2 F) (φ g) v)
  fix : ∀ g (p : Fin 3 ⊕ Fin 3 ⊕ Unit → F), (∀ v, polar (quadOdd 3 F) p (kappa v) = 0) →
    spinAction (quadOdd 3 F) (θ g) p = p

theorem exists_thetaData [Finite F] (hF : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) :
    Nonempty (ThetaData F h2) := by
  obtain ⟨φ, θ, hφ, hφi, hθi, hcoe, hnat, hfix, hroots⟩ := exists_theta7 hF h2
  exact ⟨⟨φ, θ, hφ, hroots, hφi, hθi, hcoe, hnat, hfix⟩⟩

end CFSG.ClassicalInvolution.PhanB3.H
