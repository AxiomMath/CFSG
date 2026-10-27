module

public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalRegularQuasisimple
import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer
import CFSG.LieType.SeitzGeneration.OrthSingular
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal

@[expose] def CubicPair {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (L : Subgroup (W ≃ₗ[K] W)) : Prop :=
  ∃ u ∈ L, ∃ u' ∈ L, ((u : W →ₗ[K] W) - 1) ^ 3 = 0 ∧
    ∃ m : W, (u * u') m ≠ (u' * u) m ∧ (u * u') m ≠ -((u' * u) m)

section Eichler

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}

theorem eichler_sub_one_pow_three {u w : W} (hu : Q u = 0) (hw : polar Q u w = 0) :
    (((eichler Q u w : W ≃ₗ[K] W) : W →ₗ[K] W) - 1) ^ 3 = 0 := by
  set N : W →ₗ[K] W := ((eichler Q u w : W ≃ₗ[K] W) : W →ₗ[K] W) - 1 with hN
  have hNx : ∀ y, N y = polar Q y u • w - (polar Q y w + Q w * polar Q y u) • u := by
    intro y
    rw [hN, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, eichler_apply hu hw]
    abel
  have huu : polar Q u u = 0 := polar_self_eq_zero hu
  have hwu : polar Q w u = 0 := by rw [polar_comm]; exact hw
  have hNu : N u = 0 := by rw [hNx, huu, hw]; simp
  have hNN : ∀ y, N (N y) = -(polar Q y u * polar Q w w) • u := by
    intro y
    rw [hNx (N y), hNx y]
    simp only [polar_sub_left, polar_smul_left_eq, huu, hwu, hw]
    module
  ext y
  rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, hNN y, map_smul, hNu, smul_zero,
    LinearMap.zero_apply]

theorem eichler_mul_apply_ne (h2 : (2 : K) ≠ 0) (P : HypPair Q) {w : W} (hw : w ∈ P.perp)
    (hQw : Q w ≠ 0) :
    (eichler Q P.e w * eichler Q P.f w) P.e ≠ (eichler Q P.f w * eichler Q P.e w) P.e ∧
      (eichler Q P.e w * eichler Q P.f w) P.e ≠ -((eichler Q P.f w * eichler Q P.e w) P.e) := by
  obtain ⟨hew, hfw⟩ := HypPair.mem_perp.1 hw
  have hwe : polar Q w P.e = 0 := by rw [polar_comm]; exact hew
  have hwf : polar Q w P.f = 0 := by rw [polar_comm]; exact hfw
  have hww : polar Q w w = 2 * Q w := polar_self_eq_two_mul Q w
  have hEe : eichler Q P.e w P.e = P.e := eichler_apply_self P.e w
  have hEw : eichler Q P.e w w = w - (2 * Q w) • P.e := by
    rw [eichler_apply P.Q_e hew, hwe, hww]
    simp
  have hEf : eichler Q P.e w P.f = P.f + w - Q w • P.e := by
    rw [eichler_apply P.Q_e hew, P.polar_fe, hfw]
    simp
  have hE'e : eichler Q P.f w P.e = P.e + w - Q w • P.f := by
    rw [eichler_apply P.Q_f hfw, P.polar_ef, hew]
    simp
  have h1 : (eichler Q P.e w * eichler Q P.f w) P.e =
      P.e + (w - (2 * Q w) • P.e) - Q w • (P.f + w - Q w • P.e) := by
    rw [LinearEquiv.mul_apply, hE'e, map_sub, map_add, map_smul, hEe, hEw, hEf]
  have h1' : (eichler Q P.f w * eichler Q P.e w) P.e = P.e + w - Q w • P.f := by
    rw [LinearEquiv.mul_apply, hEe, hE'e]
  rw [h1, h1']
  constructor
  · intro h
    have h3 := congrArg (fun z => polar Q z w) h
    simp only [polar_add_left, polar_sub_left, polar_smul_left_eq, hew, hfw, hww] at h3
    apply hQw
    have h4 : 2 * (Q w * Q w) = 0 := by linear_combination -h3
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 h2
    · exact mul_self_eq_zero.1 h5
  · intro h
    have h3 := congrArg (fun z => polar Q z P.e) h
    simp only [polar_add_left, polar_sub_left, polar_smul_left_eq, polar_neg_left, P.polar_ee,
      hwe, P.polar_fe] at h3
    apply hQw
    have h4 : 2 * Q w = 0 := by linear_combination -h3
    exact (mul_eq_zero.1 h4).resolve_left h2

theorem cubicPair_orthDerived [Finite K] [FiniteDimensional K W]
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K W) (h2 : (2 : K) ≠ 0) :
    CubicPair ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  obtain ⟨e, -, he0, he⟩ := CFSG.LieType.SeitzGeneration.exists_singular_of_three_le_odd (Q := Q)
    h2 (S := ⊤) (by rw [finrank_top]; exact h3)
  obtain ⟨P, -⟩ := exists_hypPair hQ he he0
  obtain ⟨w, hw, hQw⟩ := CFSG.RankThree.Classical.exists_mem_perp_map_ne_zero hQ h3 P
  have h21 : (2 : K) ≠ 1 := fun h => one_ne_zero (by linear_combination h)
  obtain ⟨hew, hfw⟩ := HypPair.mem_perp.1 hw
  let P' : HypPair Q := ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩
  have hw' : w ∈ P'.perp := HypPair.mem_perp.2 ⟨hfw, hew⟩
  exact ⟨eichler Q P.e w,
    CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup h2 h21 P hw,
    eichler Q P.f w, CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup h2 h21 P' hw',
    eichler_sub_one_pow_three P.Q_e hew, P.e, eichler_mul_apply_ne h2 P hw hQw⟩

end Eichler

section Split

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial

private theorem sub_one_pow_three_of_left (ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    {u : W ≃ₗ[K] W} {M : Matrix (Fin 2) (Fin 2) K} (hu : ∀ w, u w = ψ.symm (M * ψ w))
    (hM : (M - 1) * (M - 1) = 0) : ((u : W →ₗ[K] W) - 1) ^ 3 = 0 := by
  have h1 : ∀ w, ((u : W →ₗ[K] W) - 1) w = ψ.symm ((M - 1) * ψ w) := by
    intro w
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, hu, sub_mul, one_mul,
      map_sub, LinearEquiv.symm_apply_apply]
  ext w
  simp only [pow_three, Module.End.mul_apply, h1, LinearEquiv.apply_symm_apply,
    LinearMap.zero_apply]
  rw [← mul_assoc, hM, zero_mul, map_zero]

private theorem sub_one_pow_three_of_right (ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    {u : W ≃ₗ[K] W} {M : Matrix (Fin 2) (Fin 2) K} (hu : ∀ w, u w = ψ.symm (ψ w * M))
    (hM : (M - 1) * (M - 1) = 0) : ((u : W →ₗ[K] W) - 1) ^ 3 = 0 := by
  have h1 : ∀ w, ((u : W →ₗ[K] W) - 1) w = ψ.symm (ψ w * (M - 1)) := by
    intro w
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, hu, mul_sub, mul_one,
      map_sub, LinearEquiv.symm_apply_apply]
  ext w
  simp only [pow_three, Module.End.mul_apply, h1, LinearEquiv.apply_symm_apply,
    LinearMap.zero_apply]
  rw [mul_assoc, hM, mul_zero, map_zero]

theorem cubicPair_split_factors (h2 : (2 : K) ≠ 0) (ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃* DeterminantIsometries K)
    (he : ∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : Matrix (Fin 2) (Fin 2) K),
      (e g).val X = ψ (g.val (ψ.symm X))) :
    CubicPair (((determinantLeftFactor K).map e.symm.toMonoidHom).map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype) ∧
      CubicPair (((determinantRightFactor K).map e.symm.toMonoidHom).map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype) := by
  have hact : ∀ (z : DeterminantIsometries K) (w : W),
      ((e.symm z : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) w =
        ψ.symm (z.val (ψ w)) := by
    intro z w
    have h := he (e.symm z) (ψ w)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  set M : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1] with hMdef
  set M' : Matrix (Fin 2) (Fin 2) K := !![1, 0; 1, 1] with hM'def
  have hdet : M.det = 1 := by simp [hMdef, Matrix.det_fin_two]
  have hdet' : M'.det = 1 := by simp [hM'def, Matrix.det_fin_two]
  set A : Matrix.SpecialLinearGroup (Fin 2) K := ⟨M, hdet⟩ with hA
  set A' : Matrix.SpecialLinearGroup (Fin 2) K := ⟨M', hdet'⟩ with hA'
  have hN : (M - 1) * (M - 1) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hMdef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have hN' : (M' - 1) * (M' - 1) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM'def, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have hne1 : M * M' ≠ M' * M := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [hMdef, hM'def, Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hne2 : ∀ X Y : Matrix (Fin 2) (Fin 2) K, X = M * M' ∨ X = M' * M →
      Y = M * M' ∨ Y = M' * M → X 0 1 = 1 → Y 0 1 = 1 → X ≠ -Y := by
    intro X Y _ _ hX hY h
    have h01 := congrFun (congrFun h 0) 1
    rw [Matrix.neg_apply, hX, hY] at h01
    exact h2 (by linear_combination h01)
  have h01 : (M * M') 0 1 = 1 := by simp [hMdef, hM'def, Matrix.mul_apply, Fin.sum_univ_two]
  have h01' : (M' * M) 0 1 = 1 := by simp [hMdef, hM'def, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  ·
    set u := ((e.symm (specialRho (A, 1)) : TauCeti.QuadraticMap.orthogonalGroup Q) :
      W ≃ₗ[K] W) with hu
    set u' := ((e.symm (specialRho (A', 1)) : TauCeti.QuadraticMap.orthogonalGroup Q) :
      W ≃ₗ[K] W) with hu'
    have hua : ∀ w, u w = ψ.symm (M * ψ w) := by
      intro w
      rw [hu, hact, specialRho_apply]
      simp [hA]
    have hua' : ∀ w, u' w = ψ.symm (M' * ψ w) := by
      intro w
      rw [hu', hact, specialRho_apply]
      simp [hA']
    have hmul : ∀ (a b : W ≃ₗ[K] W) (X Y : Matrix (Fin 2) (Fin 2) K),
        (∀ w, a w = ψ.symm (X * ψ w)) → (∀ w, b w = ψ.symm (Y * ψ w)) →
          (a * b) (ψ.symm 1) = ψ.symm (X * Y) := by
      intro a b X Y ha hb
      rw [LinearEquiv.mul_apply, hb, ha, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        mul_one]
    refine ⟨u, ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩, u', ⟨_, ⟨_, ⟨A', rfl⟩, rfl⟩, rfl⟩,
      sub_one_pow_three_of_left ψ hua hN, ψ.symm 1, ?_, ?_⟩
    · rw [hmul u u' M M' hua hua', hmul u' u M' M hua' hua]
      exact fun h => hne1 (ψ.symm.injective h)
    · rw [hmul u u' M M' hua hua', hmul u' u M' M hua' hua, ← map_neg]
      exact fun h => hne2 _ _ (Or.inl rfl) (Or.inr rfl) h01 h01' (ψ.symm.injective h)
  ·
    set u := ((e.symm (specialRho (1, A⁻¹)) : TauCeti.QuadraticMap.orthogonalGroup Q) :
      W ≃ₗ[K] W) with hu
    set u' := ((e.symm (specialRho (1, A'⁻¹)) : TauCeti.QuadraticMap.orthogonalGroup Q) :
      W ≃ₗ[K] W) with hu'
    have hua : ∀ w, u w = ψ.symm (ψ w * M) := by
      intro w
      rw [hu, hact, specialRho_apply, inv_inv]
      simp [hA]
    have hua' : ∀ w, u' w = ψ.symm (ψ w * M') := by
      intro w
      rw [hu', hact, specialRho_apply, inv_inv]
      simp [hA']
    have hmul : ∀ (a b : W ≃ₗ[K] W) (X Y : Matrix (Fin 2) (Fin 2) K),
        (∀ w, a w = ψ.symm (ψ w * X)) → (∀ w, b w = ψ.symm (ψ w * Y)) →
          (a * b) (ψ.symm 1) = ψ.symm (Y * X) := by
      intro a b X Y ha hb
      rw [LinearEquiv.mul_apply, hb, ha, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        one_mul]
    refine ⟨u, ⟨_, ⟨_, ⟨A⁻¹, rfl⟩, rfl⟩, rfl⟩, u', ⟨_, ⟨_, ⟨A'⁻¹, rfl⟩, rfl⟩, rfl⟩,
      sub_one_pow_three_of_right ψ hua hN, ψ.symm 1, ?_, ?_⟩
    · rw [hmul u u' M M' hua hua', hmul u' u M' M hua' hua]
      exact fun h => hne1 (ψ.symm.injective h).symm
    · rw [hmul u u' M M' hua hua', hmul u' u M' M hua' hua, ← map_neg]
      exact fun h => hne2 _ _ (Or.inr rfl) (Or.inl rfl) h01' h01 (ψ.symm.injective h)

end Split

section Normal

variable {K : Type} [Field K] [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

open CFSG.LocalAnalysis.ComponentInitial

private theorem not_isQuasisimple_of_comm {G : Type*} [Group G] (h : ∀ a b : G, a * b = b * a) :
    ¬ CFSG.IsQuasisimple G := by
  rintro ⟨-, -, a, b, hab⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem cubicPair_of_normal_quasisimple (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ finrank K W) (hnexc : ¬ SmallFixedException Q) (h2 : (2 : K) ≠ 0)
    {L : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)} (hLq : CFSG.IsQuasisimple ↥L)
    (hLle : L ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLn : (L.subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q))).Normal) :
    CubicPair (L.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype) := by
  by_cases hs : finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ y ∈ S, Q y = 0
  ·
    have hK : ¬ (Nat.card K = 2 ∨ Nat.card K = 3) := fun h => hnexc (Or.inr ⟨hs, h⟩)
    push Not at hK
    obtain ⟨ψ, e, -, he, hsup, hLq', hRq', hLn', hRn', -, -, -⟩ :=
      orthogonal_split_four_derived hK.1 hK.2 Q hQ hs.1 hs.2
    haveI : Finite W := Module.finite_of_finite K
    haveI : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W))
      fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
    set Lf := (determinantLeftFactor K).map e.symm.toMonoidHom with hLf
    set Rf := (determinantRightFactor K).map e.symm.toMonoidHom with hRf
    have hLfC : Lf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rw [hsup]
      exact le_sup_left
    have hRfC : Rf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rw [hsup]
      exact le_sup_right
    have hF : ∀ i, CFSG.Open.IsComponentOf (![Lf, Rf] i)
        (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
      intro i
      fin_cases i
      · exact ⟨hLfC, CFSG.Open.IsSubnormal.step hLfC hLn' (CFSG.Open.IsSubnormal.refl _),
          CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hLq'⟩
      · exact ⟨hRfC, CFSG.Open.IsSubnormal.step hRfC hRn' (CFSG.Open.IsSubnormal.refl _),
          CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hRq'⟩
    have hperf : ∀ P : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
        P ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) → commutator ↥P = ⊤ →
        P ≤ ⨆ i, ![Lf, Rf] i := by
      intro P hP _
      refine hP.trans (hsup.le.trans (sup_le ?_ ?_))
      · exact le_iSup (fun i => ![Lf, Rf] i) 0
      · exact le_iSup (fun i => ![Lf, Rf] i) 1
    have hLc : CFSG.Open.IsComponentOf L (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) :=
      ⟨hLle, CFSG.Open.IsSubnormal.step hLle hLn (CFSG.Open.IsSubnormal.refl _),
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hLq⟩
    obtain ⟨i, hi⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.component_mem_named_factors _ hF hperf hLc
    obtain ⟨hcL, hcR⟩ := cubicPair_split_factors h2 ψ e he
    fin_cases i
    · rw [hi]
      exact hcL
    · rw [hi]
      exact hcR
  ·
    have hC := orthogonal_regular_space_derived_quasisimple Q hQ h3 hnexc hs
    have hLC : L = commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hC hLn with h | h
      · exact le_antisymm hLle (Subgroup.subgroupOf_eq_top.1 h)
      · exfalso
        refine not_isQuasisimple_of_comm (fun a b => ?_) hLq
        have ha : (⟨a.1, hLle a.2⟩ : ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q))) ∈
            L.subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) :=
          Subgroup.mem_subgroupOf.2 a.2
        have hc := Subgroup.mem_center_iff.1 (h ha) ⟨b.1, hLle b.2⟩
        exact Subtype.ext (congrArg Subtype.val hc).symm
    rw [hLC, Subgroup.map_subtype_commutator]
    exact cubicPair_orthDerived hQ h3 h2

end Normal

section Fixed

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

open Polynomial CFSG.RankThree.PartOne.KCPrimary

theorem cubicPair_of_fixedFactor (hx : OddOrderIsometry Q p x)
    (hlist : FixedLayerListed Q x) (h2 : (2 : K) ≠ 0) {F : Subgroup (V ≃ₗ[K] V)}
    (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) : CubicPair F := by
  have hSFD : (commutator ↥(supportedBlock Q x (X - 1))).map
      (supportedBlock Q x (X - 1)).subtype = supportedFixedDerived Q x := by
    rw [Subgroup.map_subtype_commutator, hx.supportedFixedDerived_eq]
  have hFB : F ≤ supportedBlock Q x (X - 1) :=
    hFle.trans supportedFixedDerived_le_supportedBlock
  have hCB : ∀ g : ↥(supportedBlock Q x (X - 1)), (g : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x →
      g ∈ commutator ↥(supportedBlock Q x (X - 1)) := by
    intro g hg
    rw [← hSFD] at hg
    obtain ⟨g', hg', hgg⟩ := hg
    rwa [show g = g' from Subtype.ext hgg.symm]
  have hmapC : (commutator ↥(supportedBlock Q x (X - 1))).map (fixedBlockEquiv hx).toMonoidHom =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      (MonoidHom.range_eq_top (f := (fixedBlockEquiv hx).toMonoidHom)).2
        (fixedBlockEquiv hx).surjective]
  set L : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
    (F.subgroupOf (supportedBlock Q x (X - 1))).map (fixedBlockEquiv hx).toMonoidHom with hL
  have hLle : L ≤
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← hmapC]
    exact ⟨g, hCB g (hFle hg), rfl⟩
  have hLn : (L.subgroupOf (commutator
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLle]
    rintro _ k ⟨g, hg, rfl⟩ hk
    rw [← hmapC] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    refine ⟨c * g * c⁻¹, ?_, by simp⟩
    have hcS : (c : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x := hSFD ▸ ⟨c, hc, rfl⟩
    exact (Subgroup.normal_subgroupOf_iff hFle).1 hFn _ _ hg hcS
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hFB).symm.trans
      ((F.subgroupOf (supportedBlock Q x (X - 1))).equivMapOfInjective
        (fixedBlockEquiv hx).toMonoidHom (fixedBlockEquiv hx).injective)) hFq
  obtain ⟨u, hu, u', hu', hcube, m, hne1, hne2⟩ := cubicPair_of_normal_quasisimple
    hx.polarBilin_fixed_nondegenerate hlist.1 hlist.2 h2 hLq hLle hLn
  obtain ⟨_, ⟨g, hg, rfl⟩, rfl⟩ := hu
  obtain ⟨_, ⟨g', hg', rfl⟩, rfl⟩ := hu'
  have hact : ∀ (k : ↥(supportedBlock Q x (X - 1))) (w : fixedSpace x),
      (((TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype
        ((fixedBlockEquiv hx).toMonoidHom k) : fixedSpace x ≃ₗ[K] fixedSpace x) w : V) =
        (k : V ≃ₗ[K] V) w := by
    intro k w
    rw [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
    exact coe_fixedBlockEquiv hx k w
  have hNW : ∀ (k : ↥(supportedBlock Q x (X - 1))) (w : fixedSpace x),
      ((((k : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) (w : V)) =
        ((((((TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype
          ((fixedBlockEquiv hx).toMonoidHom k) : fixedSpace x ≃ₗ[K] fixedSpace x) :
            fixedSpace x →ₗ[K] fixedSpace x) - 1) w : fixedSpace x) : V) := by
    intro k w
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, Submodule.coe_sub, hact]
  have hmul : ∀ (k k' : ↥(supportedBlock Q x (X - 1))) (w : fixedSpace x),
      ((k : V ≃ₗ[K] V) * (k' : V ≃ₗ[K] V)) (w : V) =
        ((((TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype
          ((fixedBlockEquiv hx).toMonoidHom k) *
            (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype
              ((fixedBlockEquiv hx).toMonoidHom k') :
                fixedSpace x ≃ₗ[K] fixedSpace x) w : fixedSpace x) : V) := by
    intro k k' w
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hact k' w, ← hact k]
  refine ⟨g, hg, g', hg', ?_, (m : V), ?_, ?_⟩
  ·
    obtain ⟨hc, -⟩ := hx.fixed_others
    ext v
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
    have hgr : (g : V ≃ₗ[K] V) r = r := (mem_supportedBlock.mp g.2).2 r hr
    have hr0 : (((g : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) r = 0 := by
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, hgr, Module.End.one_apply, sub_self]
    have hw0 : (((((g : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) ^ 3 : V →ₗ[K] V) w) = 0 := by
      have h1 := congrArg (fun f => (f ⟨w, hw⟩ : V)) hcube
      simp only [pow_three, Module.End.mul_apply, LinearMap.zero_apply,
        Submodule.coe_zero] at h1
      rw [pow_three, Module.End.mul_apply, Module.End.mul_apply]
      change (((g : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) ((((g : V ≃ₗ[K] V) : V →ₗ[K] V) - 1)
        ((((g : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) ((⟨w, hw⟩ : fixedSpace x) : V))) = 0
      rw [hNW, hNW, hNW]
      exact h1
    rw [map_add, hw0, pow_three, Module.End.mul_apply, Module.End.mul_apply, hr0, map_zero,
      map_zero, zero_add, LinearMap.zero_apply]
  · intro h
    apply hne1
    apply Subtype.ext
    rw [← hmul g g' m, ← hmul g' g m]
    exact h
  · intro h
    apply hne2
    apply Subtype.ext
    rw [Submodule.coe_neg, ← hmul g g' m, ← hmul g' g m]
    exact h

end Fixed

end CFSG.LocalAnalysis.GLTheoremA.S2019
