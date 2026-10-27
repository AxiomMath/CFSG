module

public import CFSG.Fischer.Classification.Orthogonal2.Symplectic
public import CFSG.Fischer.Classification.Symplectic.OrthoGenSymplectic
public import CFSG.ClassicalGroups.Orthogonal.Matrix


public section

namespace CFSG.Fischer.Classification.Orth2

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Module CFSG.LargeExtraspecial CFSG.Open Matrix CFSG.ClassicalGroups.Orthogonal

private theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

section Pairing

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}

theorem exists_apply_eq_zero_eq_one [Finite U] (hnd : f.Nondegenerate) {u w : U}
    (hw : w ∉ Submodule.span (ZMod 2) {u}) : ∃ z, f u z = 0 ∧ f w z = 1 := by
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  by_contra hall
  push Not at hall
  have hker : (⨅ _ : Unit, LinearMap.ker (f u)) ≤ LinearMap.ker (f w) := by
    intro v hv
    rw [Submodule.mem_iInf] at hv
    rw [LinearMap.mem_ker]
    rcases zmod2_cases (f w v) with h | h
    · exact h
    · exact absurd h (hall v (hv ()))
  have hmem := mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => f u) hker
  rw [Set.range_const, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  apply hw
  have h0 : w - c • u = 0 := by
    apply hnd.1
    intro v
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, ← hc]
    simp
  rw [sub_eq_zero] at h0
  rw [h0]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)

theorem eq_zero_or_eq_of_mem_span_singleton {u w : U}
    (hw : w ∈ Submodule.span (ZMod 2) {u}) : w = 0 ∨ w = u := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rcases zmod2_cases c with rfl | rfl
  · left; rw [zero_smul]
  · right; rw [one_smul]

theorem eq_zero_or_eq_of_forall_perp [Finite U] (hf : f.IsAlt) (hnd : f.Nondegenerate) {u w : U}
    (h : ∀ z, f z u = 0 → f z w = 0) : w = 0 ∨ w = u := by
  by_contra hne
  have hw : w ∉ Submodule.span (ZMod 2) {u} := fun hmem =>
    hne (eq_zero_or_eq_of_mem_span_singleton hmem)
  obtain ⟨z, hz0, hz1⟩ := exists_apply_eq_zero_eq_one hnd hw
  have h1 : f z u = 0 := by rw [OrthoF2.isAlt_symm hf]; exact hz0
  have h2 : f z w = 1 := by rw [OrthoF2.isAlt_symm hf]; exact hz1
  rw [h z h1] at h2
  exact zero_ne_one h2

theorem exists_apply_eq_one_eq_zero [Finite U] (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {v v' : U} (hv : v ≠ 0) (hne : v ≠ v') : ∃ x, f x v = 1 ∧ f x v' = 0 := by
  have hw : v ∉ Submodule.span (ZMod 2) {v'} := fun hmem => by
    rcases eq_zero_or_eq_of_mem_span_singleton hmem with h | h
    · exact hv h
    · exact hne h
  obtain ⟨z, hz0, hz1⟩ := exists_apply_eq_zero_eq_one hnd hw
  refine ⟨z, ?_, ?_⟩
  · rw [OrthoF2.isAlt_symm hf]; exact hz1
  · rw [OrthoF2.isAlt_symm hf]; exact hz0

end Pairing

section Commute

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}

theorem spT_zero (hf : f.IsAlt) : spT hf (0 : U) = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change x + f x 0 • (0 : U) = x
  rw [smul_zero, add_zero]

theorem spT_mul_comm_iff (hf : f.IsAlt) (hnd : f.Nondegenerate) {a b : U} (ha : a ≠ 0) :
    spT hf a * spT hf b = spT hf b * spT hf a ↔ f a b = 0 := by
  have hz : ∀ z : U, z + z = 0 := fun z => by
    rw [← two_smul (ZMod 2) z, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  constructor
  · intro h
    rcases zmod2_cases (f a b) with h0 | h1
    · exact h0
    · exfalso
      have e := spT_mul_spT_mul_spT hf h1
      have e' : spT hf a * spT hf b * spT hf a = spT hf b := by
        rw [h, mul_assoc, spT_mul_self, mul_one]
      rw [e'] at e
      have hab0 : a + b ≠ 0 := by
        intro h0
        have : b = a := by
          have := congrArg (· + a) h0
          simp only [zero_add] at this
          rw [add_comm a b, add_assoc, hz, add_zero] at this
          exact this
        rw [this, hf.self_eq_zero] at h1
        exact zero_ne_one h1
      have := eq_of_spT_eq hf hnd hab0 e.symm
      apply ha
      have h2 : a + b + b = b + b := by rw [this]
      rw [add_assoc, hz, add_zero] at h2
      exact h2
  · intro h0
    have hba : f b a = 0 := by rw [OrthoF2.isAlt_symm hf]; exact h0
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, spT_apply, map_add, map_smul, h0, hba,
      zero_smul, add_zero]
    abel

end Commute

section Model

variable {m : ℕ} {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}

theorem exists_mulEquiv_isometryGroup_of_fischerLinearModel {G : Type} [Group G] {D : Set G}
    (halt : ∀ x, b x x = 0)
    (hsp : fischerLinearModel D (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    ∃ Φ : G ≃* TauCeti.BilinForm.isometryGroup b,
      ∀ g, g ∈ D ↔ ∃ v, v ≠ 0 ∧ Φ g = spT (f := b) halt v := by
  obtain ⟨φ, hφ⟩ := hsp
  have hmap : (fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
      ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y).map (toLinEquiv (Fin (2 * m)) (ZMod 2)).toMonoidHom =
        TauCeti.BilinForm.isometryGroup b := by
    ext L
    rw [Subgroup.mem_map_equiv, CFSG.Fischer.Classification.mem_fischerMatrixGroup_bilin_iff,
      TauCeti.BilinForm.mem_isometryGroup_iff]
    refine forall₂_congr fun x y => ?_
    rw [← toLinEquiv_apply, ← toLinEquiv_apply, MulEquiv.apply_symm_apply]
  let Θ := ((toLinEquiv (Fin (2 * m)) (ZMod 2)).subgroupMap _).trans
    (MulEquiv.subgroupCongr hmap)
  have hΘ : ∀ A x, ((Θ A : TauCeti.BilinForm.isometryGroup b) :
      (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) x =
      ((A : GL (Fin (2 * m)) (ZMod 2)) : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2)) *ᵥ x :=
    fun _ _ => rfl
  refine ⟨φ.trans Θ, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · obtain ⟨v, hv, hgv⟩ :=
      CFSG.Fischer.Classification.eq_sympTransvectionGL_of_mem_fischerTransvections halt
        ((hφ g).mp hg)
    refine ⟨v, hv, Subtype.ext (LinearEquiv.ext fun x => ?_)⟩
    change ((Θ (φ g) : TauCeti.BilinForm.isometryGroup b) :
      (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) x = x + b x v • v
    rw [hΘ, hgv, CFSG.Fischer.Classification.sympTransvectionGL_mulVec]
  · rintro ⟨v, hv, hgv⟩
    refine (hφ g).mpr ?_
    have hmat : (φ g : GL (Fin (2 * m)) (ZMod 2)) =
        CFSG.Fischer.Classification.sympTransvectionGL b halt v := by
      apply (toLinEquiv (Fin (2 * m)) (ZMod 2)).injective
      refine LinearEquiv.ext fun x => ?_
      rw [toLinEquiv_apply, toLinEquiv_apply,
        CFSG.Fischer.Classification.sympTransvectionGL_mulVec, ← hΘ]
      change ((φ.trans Θ g : TauCeti.BilinForm.isometryGroup b) :
        (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) x = _
      rw [hgv]
      rfl
    rw [hmat]
    exact CFSG.Fischer.Classification.sympTransvectionGL_mem_fischerTransvections hv

theorem nondegenerate_of_isAlt (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    b.Nondegenerate := by
  refine ⟨fun x hx => hnd x hx, fun y hy => hnd y fun x => ?_⟩
  rw [OrthoF2.isAlt_symm (f := b) halt]
  exact hy x

theorem commutator_eq_top_of_mulEquiv_isometryGroup {K : Type} [Group K] (hm : 3 ≤ m)
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (Φ : K ≃* TauCeti.BilinForm.isometryGroup b) :
    commutator K = ⊤ := by
  have hb : b.IsAlt := halt
  have hbn := nondegenerate_of_isAlt halt hnd
  have hk : Module.finrank (ZMod 2) (Fin (2 * m) → ZMod 2) = 2 * m := Module.finrank_fin_fun _
  have : IsSimpleGroup (TauCeti.BilinForm.isometryGroup b) :=
    Recognition.SymO.isSimpleGroup_isometryGroup b hb hbn hk hm
  have : IsSimpleGroup K := Φ.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with hbot | htop
  · exfalso
    obtain ⟨u, v, -, huv, -, -⟩ := exists_spT_chain hb hbn (by omega)
    have hu : u ≠ 0 := by
      intro h0
      rw [h0, LinearMap.map_zero₂] at huv
      exact zero_ne_one huv
    have hv : v ≠ 0 := by
      intro h0
      rw [h0, map_zero] at huv
      exact zero_ne_one huv
    have hcen : (⊤ : Subgroup K) ≤ Subgroup.centralizer (⊤ : Subgroup K) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hmem := Subgroup.mem_centralizer_iff.mp (hcen (Subgroup.mem_top (Φ.symm (spT hb v))))
      (Φ.symm (spT hb u)) (Subgroup.mem_top _)
    have h' := congrArg Φ hmem
    rw [map_mul, map_mul, Φ.apply_symm_apply, Φ.apply_symm_apply,
      spT_mul_comm_iff hb hbn hu, huv] at h'
    exact one_ne_zero h'
  · exact htop

end Model

end CFSG.Fischer.Classification.Orth2
