module

public import CFSG.LargeExtraspecial.AS35Pre
public import CFSG.Milestones.CL_LIT_Fischer_three_transposition_theorem

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Open CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Recognition
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem exists_mem_QG_mul_ne : ∃ x ∈ S.QG, ∃ y ∈ S.QG, x * y ≠ y * x := by
  by_contra! hall
  have hzc : S.zQ ∈ _root_.commutator S.Q := by
    rw [S.extraspecial.2.1]
    exact S.zQ_mem_center
  have hbot : _root_.commutator S.Q = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subtype.ext (Subtype.ext (hall _ ⟨y, y.2, rfl⟩ _ ⟨x, x.2, rfl⟩))
  rw [hbot, Subgroup.mem_bot] at hzc
  exact S.zQ_ne_one hzc

theorem not_isComponentOf (K : Subgroup G) : ¬ IsComponentOf K S.M := fun hK =>
  SpU.not_isComponentOf hK S.QG_le_M (fun _ hc _ hx => S.conj_mem_QG hc hx)
    (fun _ hx => S.pow_four_eq_one hx)
    fun _ hc hcomm => S.pow_four_eq_one (S.mem_QG_of_commute hc hcomm)

omit [Finite G] in
theorem orderOf_of_isConj {g : G} (hg : IsConj S.z g) : orderOf g = 2 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hg
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, S.orderOf_z]

omit [Finite G] in
theorem orderOf_mul_mem_of_isConj
    (h3 : ∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ))
    {d e : G} (hd : IsConj S.z d) (he : IsConj S.z e) :
    orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨c₁, rfl⟩ := isConj_iff.mp hd
  obtain ⟨c₂, rfl⟩ := isConj_iff.mp he
  exact h3 c₁ c₂

omit [Finite G] in
theorem closure_conj_eq_top [IsSimpleGroup G] : closure {g : G | IsConj S.z g} = ⊤ := by
  have hset : {g : G | IsConj S.z g} = Group.conjugatesOfSet {S.z} := by
    ext g
    rw [Group.mem_conjugatesOfSet_iff]
    exact ⟨fun h => ⟨S.z, rfl, h⟩, fun ⟨a, ha, h⟩ => (Set.mem_singleton_iff.mp ha) ▸ h⟩
  have hN : (closure {g : G | IsConj S.z g}).Normal := by
    rw [hset]
    exact Subgroup.normalClosure_normal
  rcases hN.eq_bot_or_eq_top with h | h
  · have hz : S.z ∈ closure {g : G | IsConj S.z g} := subset_closure (IsConj.refl S.z)
    rw [h, mem_bot] at hz
    exact (S.z_ne_one hz).elim
  · exact h

include S in
omit [Finite G] in
theorem center_eq_bot [IsSimpleGroup G] : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · obtain ⟨x, y, hxy⟩ := S.exists_mul_ne_mul
    exact (hxy ((mem_center_iff.mp (h ▸ mem_top x : x ∈ center G)) y).symm).elim

include S in
omit [Finite G] in
theorem commutator_eq_top [IsSimpleGroup G] : _root_.commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator G) with h | h
  · obtain ⟨x, y, hxy⟩ := S.exists_mul_ne_mul
    have hc : ⁅x, y⁆ ∈ _root_.commutator G := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top x) (mem_top y)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact (hxy hc).elim
  · exact h

include S in
omit [Finite G] in
theorem isSimpleGroup_commutator [IsSimpleGroup G] : IsSimpleGroup (_root_.commutator G) :=
  ((MulEquiv.subgroupCongr S.commutator_eq_top).trans Subgroup.topEquiv).isSimpleGroup

include S in
omit [Finite G] in
theorem map_eq_one_of_commGroup [IsSimpleGroup G] {A : Type*} [CommGroup A] (f : G →* A)
    (g : G) : f g = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · obtain ⟨x, y, hxy⟩ := S.exists_mul_ne_mul
    refine (hxy ((MonoidHom.ker_eq_bot_iff f).mp h ?_)).elim
    rw [map_mul, map_mul, mul_comm]
  · exact (h ▸ mem_top g : g ∈ f.ker)

omit [Finite G] in
theorem false_of_perm [IsSimpleGroup G] {m : ℕ} (φ : G ≃* Equiv.Perm (Fin m))
    (hφ : (φ S.z).IsSwap) : False := by
  have h := S.map_eq_one_of_commGroup (Equiv.Perm.sign.comp φ.toMonoidHom) S.z
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hφ.sign_eq] at h
  exact absurd h (by decide)

omit [Finite G] in
theorem false_of_orthogonalGroup [IsSimpleGroup G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) (Φ : G ≃* TauCeti.QuadraticMap.orthogonalGroup Q) {v : V}
    (hv : Q v = 1)
    (hΦ : ((Φ S.z : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q v) : False := by
  have h := S.map_eq_one_of_commGroup ((dicksonHom Q hQ).comp Φ.toMonoidHom) S.z
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, dicksonHom_apply, hΦ,
    CFSG.RankThree.Literature.FSmith.finrank_commSpace_reflect hQ hv, Nat.cast_one,
    ofAdd_eq_one] at h
  exact one_ne_zero h

open Matrix in
omit [Finite G] in
theorem false_of_case3 [IsSimpleGroup G] {m : ℕ} {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (h : fischerLinearModel {g : G | IsConj S.z g}
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) : False := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨v, hv, hdv⟩ :=
    eq_orthTransvectionGL_of_mem_fischerTransvections ((hφ S.z).mp (IsConj.refl _))
  set T := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2)
  have hH : (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x).map
      (T : GL (Fin (2 * m)) (ZMod 2) →* _) = TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [fischerMatrixGroup_isometry_eq_comap]
    exact Subgroup.map_comap_eq_self_of_surjective T.surjective _
  have hnd' : (polarBilin Q).Nondegenerate := by
    refine ⟨fun x hx => hnd x fun y => ?_, fun y hy => hnd y fun x => ?_⟩
    · rw [← polarBilin_apply_apply]
      exact hx y
    · rw [polar_comm, ← polarBilin_apply_apply]
      exact hy x
  refine S.false_of_orthogonalGroup hnd' (φ.trans ((T.subgroupMap _).trans
    (MulEquiv.subgroupCongr hH))) hv ?_
  change T (φ S.z : GL (Fin (2 * m)) (ZMod 2)) = _
  rw [hdv, toLinEquiv_orthTransvectionGL]

theorem false_of_sporadic
    [IsSimpleGroup G]
    (h3 : ∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ))
    (h : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Fi22) ∨
      Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Fi23) ∨
      Nonempty (G ≃* MulAut CFSG.Blueprint.NativeSporadic.Fi24prime)) : False := by
  have hrec := CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_recognition G
    {g | IsConj S.z g} ⟨S.z, rfl⟩ (fun _ hd => S.orderOf_of_isConj hd)
    (fun _ hd _ he => S.orderOf_mul_mem_of_isConj h3 hd he) S.closure_conj_eq_top
    S.center_eq_bot S.isSimpleGroup_commutator S.z (IsConj.refl S.z)
  rcases h with h | h | h
  · obtain ⟨K, hK, -⟩ := hrec.1.mp h
    exact S.not_isComponentOf K hK
  · obtain ⟨K, hK, -⟩ := hrec.2.1.mp h
    exact S.not_isComponentOf K hK
  · obtain ⟨K, hK, -⟩ := hrec.2.2.1.mp h
    exact S.not_isComponentOf K hK

end Setting

end CFSG.LargeExtraspecial
