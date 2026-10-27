module

public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.LargeExtraspecial.S4Weak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup CFSG.CGT.Timmesfeld75

section Transport

variable {K₀ G₁ : Type*} [Group K₀] [Group G₁] (ψ : K₀ ≃* G₁) {T₀ : Subgroup K₀}

theorem map_conjSubgroup_of_mulEquiv (k : K₀) :
    (conjSubgroup k T₀).map ψ.toMonoidHom = conjSubgroup (ψ k) (T₀.map ψ.toMonoidHom) := by
  simp only [conjSubgroup, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjTwoTransitive_of_mulEquiv {K₀ G₁ : Type} [Group K₀] [Group G₁] (ψ : K₀ ≃* G₁)
    {T₀ : Subgroup K₀} (h : ConjTwoTransitive G₁ (T₀.map ψ.toMonoidHom)) :
    ConjTwoTransitive K₀ T₀ := by
  have hinj : Function.Injective (Subgroup.map ψ.toMonoidHom) :=
    Subgroup.map_injective ψ.injective
  intro a b c d hab hcd
  obtain ⟨g, hg1, hg2⟩ := h (ψ a) (ψ b) (ψ c) (ψ d)
    (by rwa [← map_conjSubgroup_of_mulEquiv, ← map_conjSubgroup_of_mulEquiv, Ne, hinj.eq_iff])
    (by rwa [← map_conjSubgroup_of_mulEquiv, ← map_conjSubgroup_of_mulEquiv, Ne, hinj.eq_iff])
  refine ⟨ψ.symm g, hinj ?_, hinj ?_⟩
  · rw [map_conjSubgroup_of_mulEquiv, map_conjSubgroup_of_mulEquiv, map_mul,
      MulEquiv.apply_symm_apply, hg1]
  · rw [map_conjSubgroup_of_mulEquiv, map_conjSubgroup_of_mulEquiv, map_mul,
      MulEquiv.apply_symm_apply, hg2]

theorem meet_of_mulEquiv
    (h : ∀ g : G₁, conjSubgroup g (T₀.map ψ.toMonoidHom) ⊓
      normalizer ((T₀.map ψ.toMonoidHom : Subgroup G₁) : Set G₁) ≠ ⊥) :
    ∀ k : K₀, conjSubgroup k T₀ ⊓ normalizer (T₀ : Set K₀) ≠ ⊥ := by
  intro k hk
  apply h (ψ k)
  rw [← map_conjSubgroup_of_mulEquiv, ← Subgroup.map_equiv_normalizer_eq,
    ← Subgroup.map_inf_eq _ _ ψ.toMonoidHom ψ.injective, hk, Subgroup.map_bot]

theorem card_conj_of_mulEquiv :
    Nat.card (Set.range fun k : K₀ => conjSubgroup k T₀) =
      Nat.card (Set.range fun g : G₁ => conjSubgroup g (T₀.map ψ.toMonoidHom)) := by
  have hinj : Function.Injective (Subgroup.map ψ.toMonoidHom) :=
    Subgroup.map_injective ψ.injective
  refine Nat.card_congr (Equiv.ofBijective (fun X => ⟨(X : Subgroup K₀).map ψ.toMonoidHom, ?_⟩)
    ⟨fun X Y h => Subtype.ext (hinj (congrArg Subtype.val h)), ?_⟩)
  · obtain ⟨k, hk⟩ := X.2
    exact ⟨ψ k, by rw [← hk, map_conjSubgroup_of_mulEquiv]⟩
  · rintro ⟨_, g, rfl⟩
    refine ⟨⟨conjSubgroup (ψ.symm g) T₀, ψ.symm g, rfl⟩, Subtype.ext ?_⟩
    simp only
    rw [map_conjSubgroup_of_mulEquiv, MulEquiv.apply_symm_apply]

end Transport

theorem card_sylow_le_card_conj {G₁ : Type*} [Group G₁] [Finite G₁] {T : Subgroup G₁}
    (S : Sylow 2 G₁) (hN : normalizer (T : Set G₁) = normalizer ((S : Subgroup G₁) : Set G₁)) :
    Nat.card (Sylow 2 G₁) ≤ Nat.card (Set.range fun g : G₁ => conjSubgroup g T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hex : ∀ P : Sylow 2 G₁, ∃ g : G₁, g • S = P := fun P => MulAction.exists_smul_eq G₁ S P
  let f : Sylow 2 G₁ → Set.range fun g : G₁ => conjSubgroup g T :=
    fun P => ⟨conjSubgroup (hex P).choose T, _, rfl⟩
  refine Nat.card_le_card_of_injective f fun P P' h => ?_
  have h1 : conjSubgroup (hex P).choose T = conjSubgroup (hex P').choose T :=
    congrArg Subtype.val h
  set a := (hex P).choose
  set b := (hex P').choose
  have e1 : ∀ x y : G₁, (T.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      T.map (MulAut.conj (y * x)).toMonoidHom := fun x y => by
    rw [Subgroup.map_map]
    congr 1
    ext
    simp [mul_assoc]
  have hmem : b⁻¹ * a ∈ normalizer (T : Set G₁) := by
    apply mem_normalizer_of_map_conj_eq
    rw [← e1 a b⁻¹]
    change (conjSubgroup a T).map _ = T
    rw [h1]
    change (T.map (MulAut.conj b).toMonoidHom).map (MulAut.conj b⁻¹).toMonoidHom = T
    rw [e1, inv_mul_cancel]
    ext x
    simp
  rw [hN] at hmem
  have hS : (b⁻¹ * a) • S = S := by
    apply Sylow.ext
    rw [Sylow.coe_subgroup_smul]
    exact map_conj_eq_of_mem_normalizer hmem
  rw [← (hex P).choose_spec, ← (hex P').choose_spec]
  change a • S = b • S
  calc a • S = b • ((b⁻¹ * a) • S) := by rw [smul_smul, mul_inv_cancel_left]
    _ = b • S := by rw [hS]

end CFSG.LargeExtraspecial.S4
