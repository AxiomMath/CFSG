module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Model

variable {n : ℕ} {K : Type} [Field K]

theorem card_pointRadical_inf_map_dualAut_le_two (hK : Nat.card K = 2) (c : Fin n)
    (P : SpecialLinearGroup (Fin n) K) :
    Nat.card (pointRadical (K := K) c ⊓ (pointRadical c).map
      (MulAut.conj (proj n K P) * dualAut n K).toMonoidHom : Subgroup (projectiveSL n K)) ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := SeitzQ2.charTwo_of_natCard_eq_two_pow (f := 1) (by rw [pow_one]; exact hK)
  set v : Fin n → K := fun j =>
    ((P⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) c j with hv
  set x₀ := proj n K (pointRadElem c v) with hx₀
  have hkey : ∀ x ∈ (pointRadical (K := K) c ⊓ (pointRadical c).map
      (MulAut.conj (proj n K P) * dualAut n K).toMonoidHom : Subgroup (projectiveSL n K)),
      x = 1 ∨ x = x₀ := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    obtain ⟨_, ⟨r, -, rfl⟩, rfl⟩ := hx1
    obtain ⟨_, ⟨_, ⟨s, -, rfl⟩, rfl⟩, hxy⟩ := hx2
    rw [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, dualAut_proj, MulAut.conj_apply, ← map_inv,
      ← map_mul, ← map_mul] at hxy
    have hmat := congrArg (fun A : SpecialLinearGroup (Fin n) K =>
      (A : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K))
      (proj_injective_of_natCard_eq_two hK hxy)
    have hinv : (pointRadElem c s)⁻¹ = pointRadElem c (-s) :=
      eq_inv_of_mul_eq_one_left (by rw [pointRadElem_mul, neg_add_cancel, pointRadElem_zero]) |>.symm
    simp only [Matrix.SpecialLinearGroup.coe_mul, hinv, Matrix.SpecialLinearGroup.coe_transpose,
      coe_pointRadElem] at hmat
    rw [Matrix.mul_assoc, show ((P⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = 1 by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one], Matrix.mul_one, pointRadMat, pointRadMat,
      Matrix.transpose_add, Matrix.transpose_one, transpose_vecMulVec, Matrix.mul_add,
      Matrix.mul_one, mul_vecMulVec, Matrix.add_mul, Matrix.one_mul, vecMulVec_mul] at hmat
    have hrow : ∀ j, (Function.update r c 0 ᵥ* (P : Matrix (Fin n) (Fin n) K)) j =
        (Pi.single c (((P : Matrix (Fin n) (Fin n) K) *ᵥ Function.update (-s) c 0) c) :
          Fin n → K) j := by
      intro j
      have h1 := congrFun (congrFun hmat c) j
      simp only [Matrix.add_apply, vecMulVec_apply, Pi.single_eq_same, one_mul] at h1
      rw [Pi.single_apply]
      by_cases hj : j = c
      · subst hj
        rw [ite_eq_left rfl]
        have h2 := add_left_cancel h1
        rw [Pi.single_eq_same, mul_one] at h2
        exact h2.symm
      · rw [ite_eq_right hj]
        have h2 := add_left_cancel h1
        rw [Pi.single_eq_of_ne hj, mul_zero] at h2
        exact h2.symm
    have hr' : Function.update r c 0 =
        ((P : Matrix (Fin n) (Fin n) K) *ᵥ Function.update (-s) c 0) c • v := by
      have h1 : Function.update r c 0 =
          (Function.update r c 0 ᵥ* (P : Matrix (Fin n) (Fin n) K)) ᵥ*
            ((P⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
      rw [h1, funext hrow, single_vecMul]
      rfl
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK
      (((P : Matrix (Fin n) (Fin n) K) *ᵥ Function.update (-s) c 0) c) with hu | hu
    · left
      rw [hu, zero_smul] at hr'
      have h1 : pointRadElem c r = 1 := by
        apply Subtype.ext
        rw [coe_pointRadElem, pointRadMat, hr', vecMulVec_zero, add_zero,
          Matrix.SpecialLinearGroup.coe_one]
      rw [h1, map_one]
    · right
      rw [hu, one_smul] at hr'
      have hvc : Function.update v c 0 = v := by
        rw [← hr', Function.update_idem]
      have h1 : pointRadElem c r = pointRadElem c v := by
        apply Subtype.ext
        rw [coe_pointRadElem, coe_pointRadElem, pointRadMat, pointRadMat, hr', hvc]
      rw [h1]
  have hx₀2 : x₀ * x₀ = 1 :=
    pointRadOn_mul_self c (Finset.univ : Finset (Fin n))
      ⟨pointRadElem c v, ⟨v, fun j hj => absurd (Finset.mem_univ j) hj, rfl⟩, rfl⟩
  have hle : (pointRadical (K := K) c ⊓ (pointRadical c).map
      (MulAut.conj (proj n K P) * dualAut n K).toMonoidHom : Subgroup (projectiveSL n K)) ≤
      zpowers x₀ := by
    intro x hx
    rcases hkey x hx with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  have hord : orderOf x₀ ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq, hx₀2]))
  calc Nat.card (pointRadical (K := K) c ⊓ (pointRadical c).map
        (MulAut.conj (proj n K P) * dualAut n K).toMonoidHom : Subgroup (projectiveSL n K)) ≤
        Nat.card (zpowers x₀) := Subgroup.card_le_of_le hle
    _ = orderOf x₀ := Nat.card_zpowers x₀
    _ ≤ 2 := hord

end Model

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_dualAut_of_outer (hset : SeitzSetting G L) {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {d : G}
    (hdC : d ∈ centralizer ({t} : Set G)) (hdo : ∀ l ∈ L, ∃ x ∈ L, d * x * d⁻¹ ≠ l * x * l⁻¹) :
    ∃ p : projectiveSL 5 K, ∀ x : L,
      d * (x : G) * d⁻¹ = ((e.symm ((MulAut.conj p * dualAut 5 K) (e x)) : L) : G) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hdL : d ∈ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
      hdC
  set α : MulAut (projectiveSL 5 K) := e.symm.trans ((conjAutOfMemNormalizer hdL).trans e)
    with hα
  have hαapp : ∀ x : projectiveSL 5 K, ((e.symm (α x) : L) : G) = d * (e.symm x : G) * d⁻¹ := by
    intro x
    rw [hα, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      coe_conjAutOfMemNormalizer_apply]
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) (n := 5) (by norm_num)).2 α
  rw [SeitzQ2.fieldAut_eq_one_of_card_eq_two hK σ, mul_one] at hαeq
  obtain ⟨p, hp⟩ := SeitzQ2.conjAut_mem_inner_of_card_eq_two hK A
  rw [← hp] at hαeq
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · exfalso
    rw [pow_zero, mul_one] at hαeq
    obtain ⟨x, hxL, hx⟩ := hdo (e.symm p) (e.symm p).2
    apply hx
    have h1 := hαapp (e ⟨x, hxL⟩)
    rw [hαeq, MulAut.conj_apply, MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv] at h1
    rw [← h1, MulEquiv.symm_apply_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  · refine ⟨p, fun x => ?_⟩
    rw [pow_one] at hαeq
    have h1 := hαapp (e x)
    rw [MulEquiv.symm_apply_apply, hαeq] at h1
    exact h1.symm

theorem lFiveGraphWInterInput_holds : LFiveGraphWInterInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  obtain ⟨-, -, -, -, htW₂, htW₂'⟩ := graph_swap_facts_of_sylowData htN hdata
  obtain ⟨-, -, -, -, -, hdt, -, hdo⟩ := hdata
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set W₂ := W₁.map (MulAut.conj d).toMonoidHom with hW₂def
  set Z := W₁ ⊓ W₂ with hZdef
  have hZ2 : ∀ z ∈ Z, z * z = 1 := fun z hz => hW₁2 z (mem_inf.1 hz).1
  have htZ : t ∈ normalizer (Z : Set G) := by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact mem_inf.2 ⟨(mem_normalizer_iff.1 htN z).1 (mem_inf.1 hz).1, htW₂ z (mem_inf.1 hz).2⟩
    · intro hz
      refine mem_inf.2 ⟨(mem_normalizer_iff.1 htN z).2 (mem_inf.1 hz).1, ?_⟩
      have h1 := htW₂' _ (mem_inf.1 hz).2
      rwa [show t⁻¹ * (t * z * t⁻¹) * t = z by group] at h1
  have hcent1 : centralizer ({(1 : G)} : Set G) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [mem_centralizer_singleton_iff, one_mul, mul_one]
  have hsq := card_inf_centralizer_le_sq_of_exponent_two hZ2 ht2 htZ (l := 1) (by group)
  rw [hcent1, inf_top_eq, inf_top_eq] at hsq
  obtain ⟨p, hp⟩ := exists_conj_dualAut_of_outer hset hK e ht hKt
    (mem_centralizer_singleton_iff.2 hdt) hdo
  obtain ⟨P, rfl⟩ := proj_surjective 5 K p
  have hle : Z ⊓ centralizer ({t} : Set G) ≤ modelToG e (pointRadical (K := K) c ⊓
      (pointRadical c).map (MulAut.conj (proj 5 K P) * dualAut 5 K).toMonoidHom) := by
    intro z hz
    obtain ⟨hzZ, hzt⟩ := mem_inf.1 hz
    obtain ⟨hzW₁, hzW₂⟩ := mem_inf.1 hzZ
    have hzV : z ∈ modelToG e (pointRadical (K := K) c) := by
      rw [← hW₁t]
      exact mem_inf.2 ⟨hzW₁, hzt⟩
    obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hzV
    obtain ⟨w, hw, hwz⟩ := hzW₂
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwz
    have hwt : w ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hzt ⊢
      have h1 : w = d⁻¹ * ((e.symm a : L) : G) * d := by rw [← hwz]; group
      have hc1 : Commute ((e.symm a : L) : G) t := hzt
      have hc2 : Commute d t := hdt
      rw [h1]
      exact (hc2.inv_left.mul_left hc1).mul_left hc2
    have hwV : w ∈ modelToG e (pointRadical (K := K) c) := by
      rw [← hW₁t]
      exact mem_inf.2 ⟨hw, hwt⟩
    obtain ⟨b, hb, rfl⟩ := (mem_modelToG e).1 hwV
    have hab : a = (MulAut.conj (proj 5 K P) * dualAut 5 K) b := by
      apply e.symm.injective
      apply Subtype.ext
      rw [← hwz, hp (e.symm b), MulEquiv.apply_symm_apply]
    refine (mem_modelToG e).2 ⟨a, mem_inf.2 ⟨ha, ⟨b, hb, ?_⟩⟩, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hab]
  have hcardV : Nat.card (modelToG e (pointRadical (K := K) c ⊓
      (pointRadical c).map (MulAut.conj (proj 5 K P) * dualAut 5 K).toMonoidHom)) ≤ 2 := by
    rw [modelToG, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact card_pointRadical_inf_map_dualAut_le_two hK c P
  have h1 := (Subgroup.card_le_of_le hle).trans hcardV
  calc Nat.card Z ≤ Nat.card (Z ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := hsq
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 4 := by norm_num

end Setting

end CFSG.SeitzReduction.LinearPilot
