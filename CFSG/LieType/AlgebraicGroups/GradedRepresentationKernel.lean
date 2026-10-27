module

public import CFSG.ThirdParty.TauCeti.HopfIdealNormalRationalPoint
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic

public noncomputable section
open WithConv CategoryTheory
open scoped TensorProduct
namespace CFSG.LieType.AlgebraicGroups.GradedKernel
universe u v w

section Linear
variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

theorem isNilpotent_of_lowers_filtration (F : ℕ → Submodule k V) (d : ℕ)
    (hF0 : F 0 = ⊥) (hFd : F d = ⊤) (f : Module.End k V)
    (hf : ∀ i, ∀ v ∈ F (i + 1), f v ∈ F i) : IsNilpotent f := by
  have hpow (n i : ℕ) : ∀ v ∈ F (i + n), (f ^ n) v ∈ F i := by
    induction n generalizing i with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      have hn : (f ^ n) v ∈ F (i + 1) :=
        ih (i + 1) v (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv)
      simpa only [pow_succ', Module.End.mul_apply] using hf i ((f ^ n) v) hn
  refine ⟨d, LinearMap.ext fun v => ?_⟩
  have h := hpow d 0 v (by rw [zero_add, hFd]; exact Submodule.mem_top)
  rw [hF0, Submodule.mem_bot] at h
  exact h

variable {G : Type w} [Group G]
variable (ρ : Representation k G V) (F : ℕ → Submodule k V)
    (hstab : ∀ g i, ∀ v ∈ F i, ρ g v ∈ F i)

def pointKernel : Subgroup G where
  carrier := {g | ∀ i, ∀ v ∈ F (i + 1), ρ g v - v ∈ F i}
  one_mem' := by
    intro i v hv
    simp
  mul_mem' := by
    intro g h hg hh i v hv
    have h1 := hg i (ρ h v) (hstab h (i + 1) v hv)
    have h2 := hh i v hv
    have hsum := (F i).add_mem h1 h2
    simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using hsum
  inv_mem' := by
    intro g hg i v hv
    have h1 := hg i (ρ g⁻¹ v) (hstab g⁻¹ (i + 1) v hv)
    have he : ρ g (ρ g⁻¹ v) = v := by
      simp [← Module.End.mul_apply, ← map_mul]
    rw [he] at h1
    simpa only [neg_sub] using (F i).neg_mem h1

theorem mem_pointKernel {g : G} :
    g ∈ pointKernel ρ F hstab ↔ ∀ i, ∀ v ∈ F (i + 1), ρ g v - v ∈ F i :=
  Iff.rfl

theorem pointKernel_normal : (pointKernel ρ F hstab).Normal := by
  refine ⟨?_⟩
  intro n hn g i v hv
  have hnv := hn i (ρ g⁻¹ v) (hstab g⁻¹ (i + 1) v hv)
  have hg := hstab g i _ hnv
  have he : ρ g (ρ g⁻¹ v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  simpa only [map_mul, Module.End.mul_apply, map_sub, he] using hg

theorem pointKernel_isNilpotent_sub_one (d : ℕ) (hF0 : F 0 = ⊥) (hFd : F d = ⊤)
    (g : G) (hg : g ∈ pointKernel ρ F hstab) : IsNilpotent (ρ g - 1) := by
  apply isNilpotent_of_lowers_filtration F d hF0 hFd
  intro i v hv
  simpa using hg i v hv

theorem commutator_mem_pointKernel_of_scalar (a : G)
    (ha : ∀ i, ∃ c : k, ∀ v ∈ F (i + 1), ρ a v - c • v ∈ F i) (g : G) :
    a * g * a⁻¹ * g⁻¹ ∈ pointKernel ρ F hstab := by
  intro i v hv
  obtain ⟨c, hc⟩ := ha i
  let w := ρ a⁻¹ (ρ g⁻¹ v)
  have hw : w ∈ F (i + 1) := hstab a⁻¹ (i + 1) _ (hstab g⁻¹ (i + 1) v hv)
  have h1 := hc (ρ g w) (hstab g (i + 1) w hw)
  have h2 := hstab g i _ (hc w hw)
  have he : ρ g (ρ a w) = v := by
    have haa : ∀ x, ρ a (ρ a⁻¹ x) = x := by
      intro x
      simp [← Module.End.mul_apply, ← map_mul]
    have hgg : ρ g (ρ g⁻¹ v) = v := by
      simp [← Module.End.mul_apply, ← map_mul]
    exact (congrArg (ρ g) (haa (ρ g⁻¹ v))).trans hgg
  have hsum := (F i).sub_mem h1 h2
  have heq : ρ (a * g * a⁻¹ * g⁻¹) v - v =
      (ρ a (ρ g w) - c • ρ g w) - ρ g (ρ a w - c • w) := by
    simp only [map_mul, Module.End.mul_apply, map_sub, map_smul]
    rw [he]
    simp [w]
  rw [heq]
  exact hsum

end Linear

section Hopf
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced M]
variable (V : Type u) [AddCommGroup V] [Module k V] [TauCeti.Comodule k M V]
    [Module.Finite k V]
variable (F : ℕ → Submodule k V)
    (hstab : ∀ (g : WithConv (M →ₐ[k] k)) i, ∀ v ∈ F i,
      TauCeti.Comodule.basePointsRepresentation V g v ∈ F i)

theorem isNormal_vanishingIdeal
    (S : Subgroup (WithConv (M →ₐ[k] k))) [S.Normal] :
    (TauCeti.HopfIdeal.vanishingIdeal S).IsNormal := by
  apply CFSG.ThirdParty.TauCeti.HopfIdeal.isNormal_of_forall_le_conjugate
  intro g a ha
  rw [TauCeti.HopfIdeal.mem_conjugate, TauCeti.HopfIdeal.mem_vanishingIdeal]
  intro x
  have he : toConv (x.val.ofConv.comp (TauCeti.HopfAlgebra.pointConjugationAlgHom g)) =
      g * x.val * g⁻¹ := by
    rw [TauCeti.HopfAlgebra.comp_pointConjugationAlgHom]
    have hg : TauCeti.AlgHom.mapValue (Algebra.ofId k k) g = g := by
      apply WithConv.ofConv_injective
      ext a
      rw [TauCeti.AlgHom.mapValue_apply]
      exact (Algebra.ofId k k).commutes (g.ofConv a)
    rw [hg]
  have hmem : g * x.val * g⁻¹ ∈ S := Subgroup.Normal.conj_mem (inferInstance : S.Normal) x.val x.property g
  have h := (TauCeti.HopfIdeal.mem_vanishingIdeal S a).mp ha ⟨_, hmem⟩
  change (g * x.val * g⁻¹).ofConv a = 0 at h
  have heval := congrArg (fun p : WithConv (M →ₐ[k] k) => p.ofConv a) he
  exact heval.trans h

omit [IsAlgClosed k] [IsReduced M] [Module.Finite k V] in
theorem quotientPointsSubgroup_vanishing_pointKernel_le :
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj
      (TauCeti.HopfIdeal.vanishingIdeal
        (pointKernel (TauCeti.Comodule.basePointsRepresentation V) F hstab)) (CommAlgCat.of k k) ≤
      pointKernel (TauCeti.Comodule.basePointsRepresentation V) F hstab := by
  intro g hg i v hv
  by_contra hnot
  obtain ⟨φ,hφ,hker⟩ := Submodule.exists_le_ker_of_notMem hnot
  let a : M := TauCeti.Comodule.matrixCoefficient (R := k) (C := M) (M := V) φ v -
    algebraMap k M (φ v)
  have ha : a ∈ TauCeti.HopfIdeal.vanishingIdeal
      (pointKernel (TauCeti.Comodule.basePointsRepresentation V) F hstab) := by
    rw [TauCeti.HopfIdeal.mem_vanishingIdeal]
    intro x
    have hx := x.property i v hv
    have h0 := hker hx
    change x.val.ofConv a = 0
    simp only [a, map_sub, TauCeti.Comodule.apply_matrixCoefficient,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    simpa only [LinearMap.mem_ker, map_sub] using h0
  have hzero := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff M.obj _ _ g).mp hg a ha
  have h0 : φ (TauCeti.Comodule.basePointsRepresentation V g v - v) = 0 := by
    simpa only [a, map_sub, TauCeti.Comodule.apply_matrixCoefficient,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using hzero
  exact hφ h0

omit [IsReduced M] in
theorem isUnipotentPoint_of_isNilpotent_basePointsRepresentation_sub_one
    (hV : TauCeti.Comodule.IsFaithful (k := k) (H := M) (V := V))
    (g : WithConv (M →ₐ[k] k))
    (hg : IsNilpotent (TauCeti.Comodule.basePointsRepresentation V g - 1)) :
    TauCeti.HopfAlgebra.IsUnipotentPoint g := by
  rw [TauCeti.HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
    (TauCeti.FGComoduleCat.of (R := k) (C := M) V) hV]
  rw [LinearMap.GeneralLinearGroup.isUnipotent_def]
  have hρ : TauCeti.Comodule.basePointsRepresentation (H := M) V g =
      (TensorProduct.lid k V).conjAlgEquiv k (TauCeti.Comodule.endOfPoint V g.ofConv) := by
    ext m
    rw [LinearEquiv.conjAlgEquiv_apply, TauCeti.Comodule.basePointsRepresentation_apply]
    simp
  rw [hρ] at hg
  have hn := hg.map ((TensorProduct.lid k V).conjAlgEquiv k).symm
  rw [map_sub, map_one, AlgEquiv.symm_apply_apply] at hn
  convert hn using 2
  exact TauCeti.Comodule.pointsAction_toLinearMap (V := V) g

include hstab in
theorem exists_normal_unipotent_commutators_of_scalar_filtration
    (hV : TauCeti.Comodule.IsFaithful (k := k) (H := M) (V := V))
    (d : ℕ) (hF0 : F 0 = ⊥) (hFd : F d = ⊤)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hscalar : ∀ t : kˣ, ∀ i, ∃ c : k, ∀ v ∈ F (i + 1),
      TauCeti.Comodule.basePointsRepresentation V (TauCeti.Cocharacter.pointsHom k μ t) v -
        c • v ∈ F i) :
    ∃ J : TauCeti.HopfIdeal k M, J.IsNormal ∧
      (∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
        TauCeti.HopfAlgebra.IsUnipotentPoint x) ∧
      ∀ t : kˣ, ∀ g : WithConv (M →ₐ[k] k),
        TauCeti.Cocharacter.pointsHom k μ t * g *
          (TauCeti.Cocharacter.pointsHom k μ t)⁻¹ * g⁻¹ ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k) := by
  let S := pointKernel (TauCeti.Comodule.basePointsRepresentation V) F hstab
  let : S.Normal := pointKernel_normal (TauCeti.Comodule.basePointsRepresentation V) F hstab
  let J := TauCeti.HopfIdeal.vanishingIdeal S
  have hSJ : S ≤ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k) :=
    (TauCeti.HopfIdeal.le_vanishingIdeal_iff S J).mp le_rfl
  refine ⟨J, isNormal_vanishingIdeal M S, ?_, ?_⟩
  · intro x hx
    have hxS : x ∈ S := quotientPointsSubgroup_vanishing_pointKernel_le M V F hstab hx
    apply isUnipotentPoint_of_isNilpotent_basePointsRepresentation_sub_one M V hV x
    exact pointKernel_isNilpotent_sub_one (TauCeti.Comodule.basePointsRepresentation V)
      F hstab d hF0 hFd x hxS
  · intro t g
    apply hSJ
    exact commutator_mem_pointKernel_of_scalar (TauCeti.Comodule.basePointsRepresentation V)
      F hstab (TauCeti.Cocharacter.pointsHom k μ t) (hscalar t) g

end Hopf


end CFSG.LieType.AlgebraicGroups.GradedKernel
