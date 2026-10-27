module

public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.ElemAbelianPlaneAction
public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTensorDecomp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCommutant

public section

namespace CFSG.GroupTheory

open CFSG.Open

universe u v w

theorem end_commutative_of_pairwise_nonisomorphic_simple
    {R : Type u} [Ring R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    {S : ι → Type w} [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)]
    [∀ i, IsSimpleModule R (S i)] [∀ i, Finite (S i)]
    (h : ∀ i j, i ≠ j → ¬ Nonempty (S i ≃ₗ[R] S j)) :
    ∀ f g : Module.End R ((i : ι) → S i), f * g = g * f := by
  classical
  intro f g
  let comp (f : Module.End R ((i : ι) → S i)) (i j : ι) : S j →ₗ[R] S i :=
    (LinearMap.proj i).comp (f.comp (LinearMap.single R S j))
  have hcompZero : ∀ (f : Module.End R ((i : ι) → S i)) {i j : ι}, i ≠ j →
      comp f i j = 0 := by
    intro f i j hij
    by_contra hne
    exact h j i hij.symm ⟨LinearEquiv.ofBijective (comp f i j)
      (LinearMap.bijective_of_ne_zero hne)⟩
  have hdecomp : ∀ f : Module.End R ((i : ι) → S i),
      f = LinearMap.piMap (fun i => comp f i i) := by
    intro f
    refine LinearMap.pi_ext fun j x => ?_
    ext i
    rw [LinearMap.coe_piMap, Pi.map_apply]
    by_cases hij : i = j
    · subst hij
      simp [comp, LinearMap.proj_apply]
    · have hleft : f (Pi.single j x) i = 0 := by
        change (comp f i j) x = 0
        rw [hcompZero f hij]
        rfl
      rw [hleft]
      have harg : Pi.single j x i = 0 := Pi.single_eq_of_ne hij x
      rw [harg, map_zero]
  rw [hdecomp f, hdecomp g]
  refine LinearMap.ext fun x => ?_
  funext i
  change comp f i i (comp g i i (x i)) = comp g i i (comp f i i (x i))
  have hcomm := CFSG.QuasithinUnique.Setup.Offender.endomorphism_comm_of_simple
    (R := R) (M := S i) (comp f i i) (comp g i i)
  exact congrArg (fun e : S i →ₗ[R] S i => e (x i)) hcomm

theorem endomorphism_commutative_of_minimal_faithful_binary_representation
    {acting : Type u} {space : Type v}
    [CommGroup acting] [Finite acting] [AddCommGroup space] [Finite space]
    [Module (ZMod 2) space] [NeZero (Nat.card acting : ZMod 2)]
    (prime rank : ℕ) [Fact prime.Prime]
    (hcard : Nat.card acting = prime ^ rank)
    (rho : Representation (ZMod 2) acting space)
    (hpow : ∀ scalar : acting, scalar ^ prime = 1)
    (hfaith : Function.Injective rho)
    (hdim : Module.finrank (ZMod 2) space = orderOf (2 : ZMod prime) * rank) :
    ∀ f g : Module.End (MonoidAlgebra (ZMod 2) acting) rho.asModule, f * g = g * f := by
  classical
  let R := MonoidAlgebra (ZMod 2) acting
  let : Finite rho.asModule := Finite.of_equiv space rho.asModuleEquiv.symm.toEquiv
  obtain ⟨n, S, e, hS⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R rho.asModule
  let : ∀ i, IsSimpleModule R (S i) := hS
  let ePi : rho.asModule ≃ₗ[R] ((i : Fin n) → ↥(S i)) :=
    e.trans (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun i => ↥(S i)))
  have hpairwise : ∀ i j : Fin n, i ≠ j →
      ¬ Nonempty (↥(S i) ≃ₗ[R] ↥(S j)) := by
    intro i j hij hequiv
    obtain ⟨eij⟩ := hequiv
    let U : Submodule R ((i : Fin n) → ↥(S i)) :=
      ⨅ k ∈ ({j} : Set (Fin n)),
        LinearMap.ker (LinearMap.proj (R := R) (φ := fun i => ↥(S i)) k)
    let rhoU : Representation (ZMod 2) acting U := Representation.ofModule' U
    have hfaithU : Function.Injective rhoU := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have hact : ∀ x : U,
          MonoidAlgebra.of (ZMod 2) acting a •
            (x : (i : Fin n) → ↥(S i)) =
          (x : (i : Fin n) → ↥(S i)) := by
        intro x
        have hx := congrArg (fun f : U →ₗ[ZMod 2] U => f x) ha
        have hx' : MonoidAlgebra.of (ZMod 2) acting a • x = x := by
          change rhoU a x = x
          simpa using hx
        exact congrArg Subtype.val hx'
      have hactCoord : ∀ k : Fin n, ∀ y : ↥(S k),
          MonoidAlgebra.of (ZMod 2) acting a • y = y := by
        intro k y
        by_cases hkj : k = j
        · subst hkj
          have hi : MonoidAlgebra.of (ZMod 2) acting a • (eij.symm y) = eij.symm y := by
            let x : U := ⟨(LinearMap.single R (fun i => ↥(S i)) i
              (eij.symm y) : (i : Fin n) → ↥(S i)), by
              simp [U, LinearMap.single_apply, Pi.single_eq_of_ne (Ne.symm hij)]⟩
            have hx := congrArg (fun w : (i : Fin n) → ↥(S i) => w i) (hact x)
            simpa [x, LinearMap.single_apply, Pi.smul_apply] using hx
          calc
            MonoidAlgebra.of (ZMod 2) acting a • y
                = MonoidAlgebra.of (ZMod 2) acting a • eij (eij.symm y) := by
                  rw [eij.apply_symm_apply]
            _ = eij (MonoidAlgebra.of (ZMod 2) acting a • eij.symm y) := by
                  rw [map_smul]
            _ = eij (eij.symm y) := by rw [hi]
            _ = y := eij.apply_symm_apply y
        · let x : U := ⟨(LinearMap.single R (fun i => ↥(S i)) k y :
              (i : Fin n) → ↥(S i)), by
              simp [U, LinearMap.single_apply, Pi.single_eq_of_ne (Ne.symm hkj)]⟩
          have hx := congrArg (fun w : (i : Fin n) → ↥(S i) => w k) (hact x)
          simpa [x, LinearMap.single_apply, Pi.smul_apply] using hx
      have hactW : ∀ w : (i : Fin n) → ↥(S i),
          MonoidAlgebra.of (ZMod 2) acting a • w = w := by
        intro w
        ext k
        exact congrArg Subtype.val (hactCoord k (w k))
      have hrhoa : rho a = 1 := by
        refine LinearMap.ext fun z => ?_
        let v : rho.asModule := rho.asModuleEquiv.symm z
        have hv : MonoidAlgebra.of (ZMod 2) acting a • v = v := by
          apply ePi.injective
          rw [map_smul]
          exact hactW (ePi v)
        have h := congrArg rho.asModuleEquiv hv
        rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of] at h
        simpa [v] using h
      exact hfaith (by simpa using hrhoa)
    have hUdim : Module.finrank (ZMod 2) U =
        ∑ k : {k : Fin n // k ≠ j}, Module.finrank (ZMod 2) (S k) := by
      let eU := LinearMap.iInfKerProjEquiv (R := R) (φ := fun i => ↥(S i))
        (I := {k : Fin n | k ≠ j}) (J := {j}) (by
          rw [Set.disjoint_left]
          intro k hk hkj
          exact hk hkj) (by
          intro k _
          by_cases h : k = j
          · exact Or.inr (by simpa using h)
          · exact Or.inl h)
      calc
        Module.finrank (ZMod 2) U =
            Module.finrank (ZMod 2) ((k : {k : Fin n // k ≠ j}) → ↥(S k)) :=
          (eU.restrictScalars (ZMod 2)).finrank_eq
        _ = ∑ k : {k : Fin n // k ≠ j}, Module.finrank (ZMod 2) (S k) := by
          rw [Module.finrank_pi_fintype]
    have hWdim : Module.finrank (ZMod 2) ((i : Fin n) → ↥(S i)) =
        ∑ k : Fin n, Module.finrank (ZMod 2) (S k) := by
      rw [Module.finrank_pi_fintype]
    have hlt : Module.finrank (ZMod 2) U <
        Module.finrank (ZMod 2) ((i : Fin n) → ↥(S i)) := by
      rw [hUdim, hWdim,
        Fintype.sum_eq_add_sum_subtype_ne
          (fun k : Fin n => Module.finrank (ZMod 2) (S k)) j]
      haveI : Nontrivial ↥(S j) := IsSimpleModule.nontrivial R (S j)
      have hpos : 0 < Module.finrank (ZMod 2) (S j) := Module.finrank_pos
      omega
    have hWi : Module.finrank (ZMod 2) ((i : Fin n) → ↥(S i)) =
        Module.finrank (ZMod 2) space :=
      ((ePi.symm.restrictScalars (ZMod 2)).trans rho.asModuleEquiv).finrank_eq
    have hboundU :=
      CFSG.PreuniquenessRankFour.Helpers.faithful_binary_elementary_representation_order_dimension_bound
        (acting := acting) (space := U) prime rank hcard rhoU hpow hfaithU
    have hWeq : Module.finrank (ZMod 2) ((i : Fin n) → ↥(S i)) =
        orderOf (2 : ZMod prime) * rank := by
      rw [hWi, hdim]
    omega
  have hWcomm :=
    end_commutative_of_pairwise_nonisomorphic_simple (R := R)
      (S := fun i => ↥(S i)) hpairwise
  intro f g
  have h := hWcomm (ePi.conjRingEquiv f) (ePi.conjRingEquiv g)
  have h' := congrArg ePi.conjRingEquiv.symm h
  simpa using h'

set_option backward.isDefEq.respectTransparency false in
theorem centralizer_commutative_of_elementaryAbelian_seven
    (E : Subgroup (GL (Fin 9) (ZMod 2)))
    (hE : IsElemAbelian 7 E)
    (hcard : 7 ^ 3 ≤ Nat.card E) :
    ∀ a ∈ Subgroup.centralizer (E : Set (GL (Fin 9) (ZMod 2))),
      ∀ b ∈ Subgroup.centralizer (E : Set (GL (Fin 9) (ZMod 2))), a * b = b * a := by
  classical
  let : IsMulCommutative E := hE.1
  let : CommGroup E := IsMulCommutative.instCommGroup
  let r : ℕ := CFSG.Open.pRank 7 (G := GL (Fin 9) (ZMod 2)) E
  have hEcard : Nat.card E = 7 ^ r :=
    card_eq_pow_pRank_of_isElemAbelian (G := GL (Fin 9) (ZMod 2))
      (p := 7) (by norm_num) hE
  have hr3 : 3 ≤ r := by
    have h := hcard
    rw [hEcard] at h
    exact (pow_le_pow_iff_right₀ (by norm_num : 1 < 7)).mp h
  have hpow : ∀ scalar : E, scalar ^ 7 = 1 := by
    intro scalar
    exact Subtype.ext (hE.2 (scalar : GL (Fin 9) (ZMod 2)) scalar.2)
  have hfaith : Function.Injective (CFSG.StandardType.LayerFacts.rhoOf E) := by
    intro a b hab
    rw [CFSG.StandardType.LayerFacts.rhoOf_apply,
      CFSG.StandardType.LayerFacts.rhoOf_apply] at hab
    exact Subtype.ext (Units.ext (Matrix.toLinAlgEquiv'.injective hab))
  have hne : NeZero (Nat.card E : ZMod 2) := by
    refine ⟨?zero_ne⟩
    rw [hEcard, Nat.cast_pow]
    exact pow_ne_zero r (by decide : (7 : ZMod 2) ≠ 0)
  let : NeZero (Nat.card E : ZMod 2) := hne
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdim9 : Module.finrank (ZMod 2) (Fin 9 → ZMod 2) = 9 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hbound :=
    CFSG.PreuniquenessRankFour.Helpers.faithful_binary_elementary_representation_order_dimension_bound
      (acting := E) (space := Fin 9 → ZMod 2) 7 r hEcard
      (CFSG.StandardType.LayerFacts.rhoOf E) hpow hfaith
  have hrle : r ≤ 3 := by
    rw [CFSG.GroupTheory.PlaneAction.orderOf_two_zmod_seven] at hbound
    have hbound9 : 3 * r ≤ 9 := by
      calc
        3 * r ≤ Module.finrank (ZMod 2) (Fin 9 → ZMod 2) := hbound
        _ = 9 := hdim9
    omega
  have hr : r = 3 := le_antisymm hrle hr3
  have hdim : Module.finrank (ZMod 2) (Fin 9 → ZMod 2) =
      orderOf (2 : ZMod 7) * r := by
    calc
      Module.finrank (ZMod 2) (Fin 9 → ZMod 2) = 9 := hdim9
      _ = orderOf (2 : ZMod 7) * r := by
        rw [CFSG.GroupTheory.PlaneAction.orderOf_two_zmod_seven, hr]
  have hEnd := endomorphism_commutative_of_minimal_faithful_binary_representation
    (acting := E) (space := Fin 9 → ZMod 2) 7 r hEcard
    (CFSG.StandardType.LayerFacts.rhoOf E) hpow hfaith hdim
  intro a ha b hb
  let Xa : Module.End (ZMod 2) (Fin 9 → ZMod 2) :=
    Matrix.toLinAlgEquiv' (a : Matrix (Fin 9) (Fin 9) (ZMod 2))
  let Xb : Module.End (ZMod 2) (Fin 9 → ZMod 2) :=
    Matrix.toLinAlgEquiv' (b : Matrix (Fin 9) (Fin 9) (ZMod 2))
  have hXa : Xa ∈ Set.range (CFSG.StandardType.LayerFacts.endRestrict E) := by
    rw [CFSG.StandardType.LayerFacts.mem_range_endRestrict]
    intro g
    show Xa * CFSG.StandardType.LayerFacts.rhoOf E g =
      CFSG.StandardType.LayerFacts.rhoOf E g * Xa
    rw [show Xa = Matrix.toLinAlgEquiv' (a : Matrix (Fin 9) (Fin 9) (ZMod 2)) from rfl,
      CFSG.StandardType.LayerFacts.rhoOf_apply, ← map_mul, ← map_mul]
    congr 1
    simpa [Units.val_mul] using
      (congrArg Units.val (Subgroup.mem_centralizer_iff.mp ha g g.2)).symm
  have hXb : Xb ∈ Set.range (CFSG.StandardType.LayerFacts.endRestrict E) := by
    rw [CFSG.StandardType.LayerFacts.mem_range_endRestrict]
    intro g
    show Xb * CFSG.StandardType.LayerFacts.rhoOf E g =
      CFSG.StandardType.LayerFacts.rhoOf E g * Xb
    rw [show Xb = Matrix.toLinAlgEquiv' (b : Matrix (Fin 9) (Fin 9) (ZMod 2)) from rfl,
      CFSG.StandardType.LayerFacts.rhoOf_apply, ← map_mul, ← map_mul]
    congr 1
    simpa [Units.val_mul] using
      (congrArg Units.val (Subgroup.mem_centralizer_iff.mp hb g g.2)).symm
  obtain ⟨fa, hfa⟩ := hXa
  obtain ⟨fb, hfb⟩ := hXb
  have hXcomm : Xa * Xb = Xb * Xa := by
    rw [← hfa, ← hfb, ← map_mul, ← map_mul]
    exact congrArg (CFSG.StandardType.LayerFacts.endRestrict E) (hEnd fa fb)
  have hmat : (a : Matrix (Fin 9) (Fin 9) (ZMod 2)) * (b : Matrix (Fin 9) (Fin 9) (ZMod 2)) =
      (b : Matrix (Fin 9) (Fin 9) (ZMod 2)) * (a : Matrix (Fin 9) (Fin 9) (ZMod 2)) := by
    apply Matrix.toLinAlgEquiv'.injective
    rw [map_mul, map_mul]
    exact hXcomm
  exact Units.ext hmat

theorem centralizer_isSolvable_of_elementaryAbelian_seven
    (E : Subgroup (GL (Fin 9) (ZMod 2)))
    (hE : IsElemAbelian 7 E)
    (hcard : 7 ^ 3 ≤ Nat.card E) :
    Group.IsSolvable (Subgroup.centralizer (E : Set (GL (Fin 9) (ZMod 2)))) := by
  refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
  exact centralizer_commutative_of_elementaryAbelian_seven E hE hcard
    (a : GL (Fin 9) (ZMod 2)) a.2 (b : GL (Fin 9) (ZMod 2)) b.2

end CFSG.GroupTheory
