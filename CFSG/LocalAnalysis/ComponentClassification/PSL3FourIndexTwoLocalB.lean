module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBIndexTwoLocal
public import CFSG.Blueprint.Catalog

public noncomputable section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem quasisimple_of_pComponent_of_solvable {X : Type*} [Group X] [Finite X]
    [Group.IsSolvable X] (J : Subgroup X) (hJ : CFSG.IsPComponent 2 J) :
    CFSG.IsQuasisimple J := by
  exfalso
  have hJ' := (CatalogueBAlternating.pComponent_two_iff J).1 hJ
  have : Group.IsPerfect J := ⟨TwoComponents.perfect hJ'⟩
  have : Nontrivial J := TwoComponents.nontrivial hJ'
  exact Group.IsPerfect.not_isSolvable J inferInstance

theorem quasisimple_of_pComponent_of_simple {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (heven : Even (Nat.card X)) (J : Subgroup X) (hJ : CFSG.IsPComponent 2 J) :
    CFSG.IsQuasisimple J := by
  have hcore : componentClassificationOddCore X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (componentClassificationOddCore X) with h | h
    · exact h
    · exfalso
      have hodd := OddCore.odd_card X
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) heven
  have hJ' := (CatalogueBAlternating.pComponent_two_iff J).1 hJ
  exact CatalogueBAlternating.quasisimple_iff_native.2
    (TwoComponents.ordinary_of_corefree hcore hJ').2.2

@[expose] def SolvableOrSimpleEven (X : Type*) [Group X] : Prop :=
  Group.IsSolvable X ∨ (IsSimpleGroup X ∧ Even (Nat.card X))

theorem SolvableOrSimpleEven.of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : SolvableOrSimpleEven Y) : SolvableOrSimpleEven X := by
  rcases h with h | ⟨hs, he⟩
  · exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · refine Or.inr ⟨?_, by rwa [Nat.card_congr e.toEquiv]⟩
    have := hs
    have : Nontrivial X := e.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem SolvableOrSimpleEven.quasisimple {X : Type*} [Group X] [Finite X]
    (h : SolvableOrSimpleEven X) (J : Subgroup X) (hJ : CFSG.IsPComponent 2 J) :
    CFSG.IsQuasisimple J := by
  rcases h with h | ⟨hs, he⟩
  · exact quasisimple_of_pComponent_of_solvable J hJ
  · exact quasisimple_of_pComponent_of_simple he J hJ

@[expose] def centConjEquiv {x r : Equiv.Perm (Fin 42)} (hx : x ∈ R) :
    ↥(Subgroup.centralizer {x * r * x⁻¹} ⊓ S) ≃* ↥(Subgroup.centralizer {r} ⊓ S) where
  toFun y := ⟨x⁻¹ * y * x, by
    obtain ⟨hy, hyS⟩ := y.2
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · have h := Subgroup.mem_centralizer_singleton_iff.1 hy
      calc x⁻¹ * y * x * r = x⁻¹ * (y * (x * r * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * r * x⁻¹) * y) * x := by rw [h]
        _ = r * (x⁻¹ * y * x) := by group
    · have := conj_mem_S (R.inv_mem hx) hyS
      rwa [inv_inv] at this⟩
  invFun y := ⟨x * y * x⁻¹, by
    obtain ⟨hy, hyS⟩ := y.2
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, conj_mem_S hx hyS⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 hy
    calc x * y * x⁻¹ * (x * r * x⁻¹) = x * (y * r) * x⁻¹ := by group
      _ = x * (r * y) * x⁻¹ := by rw [h]
      _ = x * r * x⁻¹ * (x * y * x⁻¹) := by group⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' y z := Subtype.ext (by simp [mul_assoc])

theorem solvableOrSimpleEven_C₁ : SolvableOrSimpleEven C₁ := Or.inl isSolvable_C₁

theorem solvableOrSimpleEven_C₂ : SolvableOrSimpleEven C₂ :=
  Or.inr ⟨isSimpleGroup_C₂, by rw [card_C₂]; decide⟩

theorem solvableOrSimpleEven_C₃ : SolvableOrSimpleEven C₃ :=
  Or.inr ⟨isSimpleGroup_C₃, by rw [card_C₃]; decide⟩

theorem solvableOrSimpleEven_C₄ : SolvableOrSimpleEven C₄ := Or.inl isSolvable_C₄

theorem orderOf_eq_two_of_mul_self {x : R} (h1 : x ≠ 1) (h2 : x * x = 1) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h2) h1

theorem fixed_of_isConj {x r : R} (h : IsConj x r) :
    Nonempty (↥(Subgroup.centralizer {(x : Equiv.Perm (Fin 42))} ⊓ S) ≃*
      ↥(Subgroup.centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S)) := by
  obtain ⟨c, hc, he⟩ := eq_conj_of_isConj h
  rw [he]
  exact ⟨centConjEquiv hc⟩

theorem fixed_of_involution {x : R} (h1 : x ≠ 1) (h2 : x * x = 1) :
    SolvableOrSimpleEven ↥(Subgroup.centralizer {(x : Equiv.Perm (Fin 42))} ⊓ S) := by
  rcases (orderOf_eq_two_iff x).1 (orderOf_eq_two_of_mul_self h1 h2) with h | h | h | h
  · obtain ⟨e⟩ := fixed_of_isConj h
    exact solvableOrSimpleEven_C₁.of_equiv e
  · obtain ⟨e⟩ := fixed_of_isConj h
    exact solvableOrSimpleEven_C₂.of_equiv e
  · obtain ⟨e⟩ := fixed_of_isConj h
    exact solvableOrSimpleEven_C₃.of_equiv e
  · obtain ⟨e⟩ := fixed_of_isConj h
    exact solvableOrSimpleEven_C₄.of_equiv e

theorem fixed_of_inner_involution {x : R} (hxS : (x : Equiv.Perm (Fin 42)) ∈ S) (h1 : x ≠ 1)
    (h2 : x * x = 1) :
    Group.IsSolvable ↥(Subgroup.centralizer {(x : Equiv.Perm (Fin 42))} ⊓ S) := by
  rcases (orderOf_eq_two_iff x).1 (orderOf_eq_two_of_mul_self h1 h2) with h | h | h | h
  · obtain ⟨e⟩ := fixed_of_isConj h
    have : Group.IsSolvable ↥(Subgroup.centralizer {(r₁R : Equiv.Perm (Fin 42))} ⊓ S) :=
      isSolvable_C₁
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · exact (not_mem_S_of_isConj h not_mem_S_r₂ hxS).elim
  · exact (not_mem_S_of_isConj h not_mem_S_r₃ hxS).elim
  · exact (not_mem_S_of_isConj h not_mem_S_r₄ hxS).elim

section Transport

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (θ : N ≃* S)

@[expose] def fixedEquiv (t : G) (r : Equiv.Perm (Fin 42))
    (hθ : ∀ n : N, r * (θ n : Equiv.Perm (Fin 42)) * r⁻¹ =
      (θ (MulAut.conjNormal t n) : Equiv.Perm (Fin 42))) :
    (Subgroup.centralizer {t}).subgroupOf N ≃* ↥(Subgroup.centralizer {r} ⊓ S) where
  toFun n := ⟨θ n.1, by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, (θ n.1).2⟩
    have hn := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 n.2)
    have hc : MulAut.conjNormal t n.1 = n.1 := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, ← hn, mul_inv_cancel_right]
    have h := hθ n.1
    rw [hc] at h
    calc (θ n.1 : Equiv.Perm (Fin 42)) * r = r * θ n.1 * r⁻¹ * r := by rw [h]
      _ = r * θ n.1 := by group⟩
  invFun s := ⟨θ.symm ⟨s.1, s.2.2⟩, by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have hs := Subgroup.mem_centralizer_singleton_iff.1 s.2.1
    have h := hθ (θ.symm ⟨s.1, s.2.2⟩)
    rw [MulEquiv.apply_symm_apply] at h
    have h' : (θ (MulAut.conjNormal t (θ.symm ⟨s.1, s.2.2⟩)) : Equiv.Perm (Fin 42)) =
        θ (θ.symm ⟨s.1, s.2.2⟩) := by
      rw [← h, MulEquiv.apply_symm_apply]
      calc r * s.1 * r⁻¹ = s.1 * r * r⁻¹ := by rw [hs]
        _ = s.1 := by group
    have h'' := θ.injective (Subtype.ext h')
    have h3 := congrArg Subtype.val h''
    rw [MulAut.conjNormal_apply] at h3
    calc ((θ.symm ⟨s.1, s.2.2⟩ : N) : G) * t =
        t * (θ.symm ⟨s.1, s.2.2⟩ : N) * t⁻¹ * t := by rw [h3]
      _ = t * (θ.symm ⟨s.1, s.2.2⟩ : N) := by group⟩
  left_inv n := by
    apply Subtype.ext
    simp
  right_inv s := by
    apply Subtype.ext
    simp
  map_mul' n m := by
    apply Subtype.ext
    simp

end Transport


theorem index_two_local_B {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    [IsSimpleGroup N] (hmodel : CFSG.Blueprint.LieModel N .PSL 3 2 2) (hindex : N.index ≤ 2) :
    Assembly.ComponentType.LocalBProperty G ∧
      ∀ T : Subgroup G, T ≠ ⊥ → IsPGroup 2 T →
        TwoComponents.badSubgroup (Subgroup.normalizer (T : Set G)) = ⊥ := by
  have hstated : StatedClassicalModel N .PSL 3 2 2 := by
    rcases hmodel with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num)
  obtain ⟨θ⟩ := nonempty_equiv_of_stated N hstated
  obtain ⟨e, he, -⟩ := full_automorphism_action
  let ψ : G →* R :=
    e.symm.toMonoidHom.comp ((MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal)
  have hψ : ∀ (t : G) (n : N), (ψ t : Equiv.Perm (Fin 42)) * (θ n : Equiv.Perm (Fin 42)) *
      (ψ t : Equiv.Perm (Fin 42))⁻¹ = (θ (MulAut.conjNormal t n) : Equiv.Perm (Fin 42)) := by
    intro t n
    have h1 := he (ψ t) (θ n)
    have h2 : e (ψ t) = MulAut.congr θ (MulAut.conjNormal t) := e.apply_symm_apply _
    rw [h2] at h1
    rw [← Subgroup.coe_inv, ← h1]
    simp [MulAut.congr]
  have hψ2 : ∀ t : G, orderOf t = 2 → ψ t * ψ t = 1 := by
    intro t ht
    rw [← map_mul, ← pow_two, ← ht, pow_orderOf_eq_one, map_one]
  have hcardN : Nat.card N = 20160 := by rw [Nat.card_congr θ.toEquiv, card_S]
  apply CatalogueBIndexTwo.localBProperty_and_normalizer_badSubgroup_eq_bot N hindex
  · intro t ht htN
    let tN : N := ⟨t, htN⟩
    have hψS : (ψ t : Equiv.Perm (Fin 42)) = θ tN := by
      have hu : (θ tN : Equiv.Perm (Fin 42))⁻¹ * ψ t ∈
          Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
        refine ⟨Subgroup.mem_centralizer_iff.2 fun s hs => ?_,
          R.mul_mem (R.inv_mem (S_le_R (θ tN).2)) (ψ t).2⟩
        have h := hψ t (θ.symm ⟨s, hs⟩)
        rw [MulEquiv.apply_symm_apply] at h
        have hconj : MulAut.conjNormal t (θ.symm ⟨s, hs⟩) = tN * θ.symm ⟨s, hs⟩ * tN⁻¹ :=
          Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
        rw [hconj, map_mul, map_mul, map_inv] at h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.apply_symm_apply] at h
        calc s * ((θ tN : Equiv.Perm (Fin 42))⁻¹ * ψ t) =
            (θ tN : Equiv.Perm (Fin 42))⁻¹ * ((θ tN : Equiv.Perm (Fin 42)) * s *
              (θ tN : Equiv.Perm (Fin 42))⁻¹) * ψ t := by group
          _ = (θ tN : Equiv.Perm (Fin 42))⁻¹ * (ψ t * s * (ψ t : Equiv.Perm (Fin 42))⁻¹) *
              ψ t := by rw [h]
          _ = (θ tN : Equiv.Perm (Fin 42))⁻¹ * ψ t * s := by group
      rw [centralizer_S_inf_R, Subgroup.mem_bot] at hu
      exact (inv_mul_eq_one.1 hu).symm
    have h1 : ψ t ≠ 1 := by
      intro h
      have h' : (θ tN : Equiv.Perm (Fin 42)) = 1 := by rw [← hψS, h]; rfl
      have htN1 : tN = 1 := θ.injective (Subtype.ext (by rw [h', map_one, Subgroup.coe_one]))
      have : t = 1 := congrArg Subtype.val htN1
      rw [this, orderOf_one] at ht
      exact absurd ht (by norm_num)
    have hS : ((ψ t : R) : Equiv.Perm (Fin 42)) ∈ S := by rw [hψS]; exact (θ tN).2
    have := fixed_of_inner_involution hS h1 (hψ2 t ht)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (fixedEquiv N θ t (ψ t) (hψ t)).toMonoidHom) (fixedEquiv N θ t (ψ t) (hψ t)).injective
  · intro t ht htN J hJ
    have hfix : SolvableOrSimpleEven ((Subgroup.centralizer {t}).subgroupOf N) := by
      by_cases h1 : ψ t = 1
      · have e1 : ↥(Subgroup.centralizer {((ψ t : R) : Equiv.Perm (Fin 42))} ⊓ S) ≃* N :=
          (MulEquiv.subgroupCongr (inf_eq_right.2 fun x _ =>
            Subgroup.mem_centralizer_singleton_iff.2 (by rw [h1]; simp))).trans θ.symm
        refine SolvableOrSimpleEven.of_equiv ((fixedEquiv N θ t (ψ t) (hψ t)).trans e1) ?_
        exact Or.inr ⟨inferInstance, by rw [hcardN]; decide⟩
      · exact (fixed_of_involution h1 (hψ2 t ht)).of_equiv (fixedEquiv N θ t (ψ t) (hψ t))
    exact hfix.quasisimple J hJ

end CFSG.ComponentClassification.PSL3Four
