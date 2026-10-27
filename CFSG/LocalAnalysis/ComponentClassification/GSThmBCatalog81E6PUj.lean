module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PUi
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.LinearGroups StabU DiagU
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem det_eq_one_of_neg {W : Submodule K (Fin 4 → K)} (hW : Module.finrank K W = 2)
    (g : LinearMap.GeneralLinearGroup K W)
    (hg : ∀ w : W, (((g : W →ₗ[K] W) w : W) : Fin 4 → K) = -(w : Fin 4 → K)) :
    LinearMap.det (g : W →ₗ[K] W) = 1 := by
  have e : (g : W →ₗ[K] W) = (-1 : K) • LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [hg]
    simp
  rw [e, LinearMap.det_smul, LinearMap.det_id, hW]
  norm_num

theorem false_of_inner_U4 (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hα : IsCU h A α) (hα1 : α ≠ 1)
    (hα2 : α ^ 2 = 1) {M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))} (hM : ⁅M, M⁆ = M)
    (hfix : ∀ x ∈ M, α x = x)
    (hM2 : 2 ^ (2 * padicValNat 2 ((p ^ f) ^ 2 - 1)) ∣ Nat.card M) : False := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hqodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
  have hq3 : 3 ≤ p ^ f := le_trans (by have := h.prime.two_le; omega)
    (Nat.le_self_pow (by have := h.one_le; omega) p)
  set C := (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype with hC
  have hMC := le_map_commutator_centralizer h hα hM hfix
  have hMS : ∀ S : Subgroup (unitarySU p f K 4), ⁅C, C⁆ ≤ S → Nat.card M ∣ Nat.card S :=
    fun S hS => (Subgroup.card_dvd_of_le (hMC.trans (Subgroup.map_mono hS))).trans
      (Subgroup.card_map_dvd _ _)
  set T := toSesqU h hα.1 with hT
  have hA2 := orderOf_mk_toSesqU h hp2 hα hα1 hα2
  have hfin4 : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  obtain ⟨l, -, -, hN, hP, hMn, hcompl, hsplit, hpair, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp2 (by omega)
      (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4) (A := T) hA2
  set Φ₀ : C →* Subgroup.centralizer {T} :=
    ((toSesq h 4).comp C.subtype).codRestrict _ (fun g => toSesq_mem_centralizer h hα.1 g.2)
    with hΦ₀
  have hΦ₀inj : Function.Injective Φ₀ := by
    intro x y hxy
    have := congrArg (fun z : Subgroup.centralizer {T} =>
      (z : sesqUnitaryGroup (stdHermForm h 4))) hxy
    exact Subtype.ext (toSesq_injective h 4 this)
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hfin4] at hsum
  have hdP : 1 ≤ Module.finrank K (eigenPlus l (unitaryOp T)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hP
  have hdM : 1 ≤ Module.finrank K (eigenMinus l (unitaryOp T)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hMn
  rcases hN with hN1 | hN1
  ·
    obtain ⟨-, hsepP, hsepM, e, he⟩ := hsplit hN1
    have hsymP := (stdHermForm_isSymm h 4).domRestrict (eigenPlus l (unitaryOp T))
    have hsymM := (stdHermForm_isSymm h 4).domRestrict (eigenMinus l (unitaryOp T))
    set D := (LinearGroups.unitaryDet ((stdHermForm h 4).domRestrict₁₂
      (eigenPlus l (unitaryOp T)) (eigenPlus l (unitaryOp T)))).prodMap
      (LinearGroups.unitaryDet ((stdHermForm h 4).domRestrict₁₂
        (eigenMinus l (unitaryOp T)) (eigenMinus l (unitaryOp T)))) with hD
    obtain ⟨S, hCS, hSD, hSmem⟩ := exists_le_of_comm_mem (e.toMonoidHom.comp Φ₀)
      (e.injective.comp hΦ₀inj) D.ker (fun x y => by
        rw [MonoidHom.mem_ker]
        simp only [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _))
    have hcardD : Nat.card D.ker =
        Nat.card (sesqSpecialUnitaryGroup ((stdHermForm h 4).domRestrict₁₂
          (eigenPlus l (unitaryOp T)) (eigenPlus l (unitaryOp T)))) *
        Nat.card (sesqSpecialUnitaryGroup ((stdHermForm h 4).domRestrict₁₂
          (eigenMinus l (unitaryOp T)) (eigenMinus l (unitaryOp T)))) := by
      rw [hD, MonoidHom.ker_prodMap, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,
        Nat.card_prod, card_ker_unitaryDet h hsymP hsepP hdP,
        card_ker_unitaryDet h hsymM hsepM hdM]
    obtain ⟨dP, hdPe⟩ : ∃ d, Module.finrank K (eigenPlus l (unitaryOp T)) = d := ⟨_, rfl⟩
    obtain ⟨dM, hdMe⟩ : ∃ d, Module.finrank K (eigenMinus l (unitaryOp T)) = d := ⟨_, rfl⟩
    rcases (show (dP = 1 ∧ dM = 3) ∨ (dP = 2 ∧ dM = 2) ∨ (dP = 3 ∧ dM = 1) by omega) with
      ⟨h1, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h3⟩
    · rw [card_sesqSU_one h hsymP hsepP (hdPe.trans h1),
        card_sesqSU_three h hsymM hsepM (hdMe.trans h3), one_mul] at hcardD
      exact not_dvd_SU3 hqodd hq3
        (hM2.trans ((hMS S hCS).trans (hSD.trans (dvd_of_eq hcardD))))
    ·
      rw [card_sesqSU_two h hsymP hsepP (hdPe.trans h1),
        card_sesqSU_two h hsymM hsepM (hdMe.trans h3)] at hcardD
      have hnegC : negOne h ∈ C := by
        rw [hC, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
        apply Units.ext
        change (-1 : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) =
          (A : Matrix (Fin 4) (Fin 4) K) * (-1)
        rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]
      have hval : ∀ v, unitaryOp ((Φ₀ ⟨negOne h, hnegC⟩ : Subgroup.centralizer {T}) :
          sesqUnitaryGroup (stdHermForm h 4)) v = -v := by
        intro v
        change (-1 : Matrix (Fin 4) (Fin 4) K) *ᵥ v = -v
        rw [Matrix.neg_mulVec, Matrix.one_mulVec]
      have hg := he (Φ₀ ⟨negOne h, hnegC⟩)
      have hneg : negOne h ∈ S := by
        refine hSmem _ hnegC ?_
        rw [MonoidHom.mem_ker]
        refine Prod.ext (Units.ext ?_) (Units.ext ?_)
        · change LinearMap.det (((e (Φ₀ ⟨negOne h, hnegC⟩)).1 :
            LinearMap.GeneralLinearGroup K (eigenPlus l (unitaryOp T))) :
              (eigenPlus l (unitaryOp T)) →ₗ[K] (eigenPlus l (unitaryOp T))) = 1
          refine det_eq_one_of_neg (hdPe.trans h1) _ fun w => ?_
          have := congrArg (fun F => F w) hg.1
          simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
          rw [this, hval]
        · change LinearMap.det (((e (Φ₀ ⟨negOne h, hnegC⟩)).2 :
            LinearMap.GeneralLinearGroup K (eigenMinus l (unitaryOp T))) :
              (eigenMinus l (unitaryOp T)) →ₗ[K] (eigenMinus l (unitaryOp T))) = 1
          refine det_eq_one_of_neg (hdMe.trans h3) _ fun w => ?_
          have := congrArg (fun F => F w) hg.2
          simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
          rw [this, hval]
      have hneg2 : orderOf (negOne h) = 2 := by
        refine orderOf_eq_prime ?_ (negOne_ne_one h h2K)
        rw [sq]
        apply ext_val
        change (-1 : Matrix (Fin 4) (Fin 4) K) * (-1) = 1
        rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.one_mul]
      have hθS := two_mul_card_map_dvd (π := thU p f K) hneg
        ((QuotientGroup.eq_one_iff _).2 (negOne_mem_scal h)) hneg2
      have h4 : 2 * Nat.card M ∣ Nat.card S := (Nat.mul_dvd_mul_left 2
        (Subgroup.card_dvd_of_le (hMC.trans (Subgroup.map_mono hCS)))).trans hθS
      have h5 : 2 ^ (2 * padicValNat 2 ((p ^ f) ^ 2 - 1) + 1) ∣ 2 * Nat.card M := by
        rw [pow_succ']
        exact Nat.mul_dvd_mul_left 2 hM2
      exact not_dvd_sq_SU2 hqodd hq3 (h5.trans (h4.trans (hSD.trans (dvd_of_eq hcardD))))
    · rw [card_sesqSU_three h hsymP hsepP (hdPe.trans h1),
        card_sesqSU_one h hsymM hsepM (hdMe.trans h3), mul_one] at hcardD
      exact not_dvd_SU3 hqodd hq3
        (hM2.trans ((hMS S hCS).trans (hSD.trans (dvd_of_eq hcardD))))
  ·
    obtain ⟨-, -, -, h2d, -, -, e, -⟩ := hpair hN1
    rw [hfin4] at h2d
    have hd2 : Module.finrank K (eigenPlus l (unitaryOp T)) = 2 := by omega
    set E := (Matrix.GeneralLinearGroup.toLin'
      (Module.finBasisOfFinrankEq K (eigenPlus l (unitaryOp T)) hd2)).symm with hE
    obtain ⟨S, hCS, hSD, -⟩ := exists_le_of_comm_mem ((E.toMonoidHom.comp e.toMonoidHom).comp Φ₀)
      ((E.injective.comp e.injective).comp hΦ₀inj)
      (Matrix.GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker (fun x y => by
        rw [MonoidHom.mem_ker]
        simp only [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _))
    have hKcard : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    have hcard : Nat.card (Matrix.GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker =
        (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
      rw [← Nat.card_congr (Matrix.SpecialLinearGroup.toGLKerEquiv).toEquiv, card_SL_two, hKcard,
        show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring]
    exact not_dvd_SL2_sq hqodd hq3
      (hM2.trans ((hMS S hCS).trans (hSD.trans (dvd_of_eq hcard))))

end CFSG.ComponentClassification.GSThmB.P211
