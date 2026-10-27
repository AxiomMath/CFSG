module

public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.CatalogueBAlternating

theorem generalizedFitting_centralizer_eq_bot (G : Type*) [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) :
    Subgroup.centralizer (GeneralizedFitting.subgroup G : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have hmem := GeneralizedFitting.centralizer_le G hg
  have hcenter : (⟨g, hmem⟩ : GeneralizedFitting.subgroup G) ∈
      Subgroup.center (GeneralizedFitting.subgroup G) := by
    apply Subgroup.mem_center_iff.mpr
    intro f
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg f.val f.property)
  rw [Helpers.center_eq_bot _ hnonab] at hcenter
  exact congrArg Subtype.val hcenter

theorem generalizedFitting_permutation_model {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (θ : GeneralizedFitting.subgroup G ≃* alternatingGroup (Fin n)) :
    ∃ ρ : G →* Equiv.Perm (Fin n), Function.Injective ρ ∧
      (∀ f : GeneralizedFitting.subgroup G, ρ f.val = (θ f).val) ∧
      (GeneralizedFitting.subgroup G).map ρ = alternatingGroup (Fin n) ∧
      alternatingGroup (Fin n) ≤ ρ.range ∧ (GeneralizedFitting.subgroup G).index ≤ 2 := by
  let F := GeneralizedFitting.subgroup G
  let : F.Normal := GeneralizedFitting.normal G
  let a : G →* MulAut F := MulAut.conjNormal
  have ha : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply le_bot_iff.mp
    intro g hg
    have hcentral : g ∈ Subgroup.centralizer (F : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro f hf
      have heq := congrArg (fun automorphism : MulAut F =>
        (automorphism (⟨f, hf⟩ : F)).val) hg
      change g * f * g⁻¹ = f at heq
      have hcomm := congrArg (fun x : G => x * g) heq
      have hgf : g * f = f * g := by
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcomm
      exact hgf.symm
    rw [generalizedFitting_centralizer_eq_bot G hnonab] at hcentral
    exact hcentral
  let c : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
        (by omega) (by omega))
  let ρ : G →* Equiv.Perm (Fin n) :=
    c.symm.toMonoidHom.comp ((MulAut.congr θ).toMonoidHom.comp a)
  have hρ : Function.Injective ρ := c.symm.injective.comp
    ((MulAut.congr θ).injective.comp ha)
  have hextends : ∀ f : F, ρ f.val = (θ f).val := by
    intro f
    apply c.injective
    change c (c.symm ((MulAut.congr θ) (a f.val))) = c (θ f).val
    rw [c.apply_symm_apply]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (θ ((a f.val) (θ.symm x))).val = ((c (θ f).val) x).val
    have hinner : a f.val = MulAut.conj f := MulAut.conjNormal_val
    rw [hinner, MulAut.conj_apply]
    change (θ (f * θ.symm x * f⁻¹)).val = (θ f).val * x.val * (θ f).val⁻¹
    simp only [map_mul, map_inv, θ.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hmap : F.map ρ = alternatingGroup (Fin n) := by
    apply le_antisymm
    · rintro g ⟨f, hf, rfl⟩
      rw [hextends (⟨f, hf⟩ : F)]
      exact (θ (⟨f, hf⟩ : F)).property
    · intro g hg
      let f := θ.symm (⟨g, hg⟩ : alternatingGroup (Fin n))
      refine ⟨f.val, f.property, ?_⟩
      rw [hextends f]
      exact congrArg Subtype.val (θ.apply_symm_apply _)
  have hindex : F.index ≤ 2 := by
    have hker : ρ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ρ).mpr hρ
    have hdvd := F.dvd_index_map (f := ρ) (by rw [hker]; exact bot_le)
    rw [hmap] at hdvd
    let : Nontrivial (Fin n) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩⟩
    rw [alternatingGroup.index_eq_two] at hdvd
    exact Nat.le_of_dvd (by decide) hdvd
  exact ⟨ρ, hρ, hextends, hmap, hmap ▸ Subgroup.map_le_range ρ F, hindex⟩

theorem generalizedFitting_between_alternating_symmetric {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (θ : GeneralizedFitting.subgroup G ≃* alternatingGroup (Fin n)) :
    ∃ K : Subgroup (Equiv.Perm (Fin n)), alternatingGroup (Fin n) ≤ K ∧
      ∃ e : G ≃* K, ∀ f : GeneralizedFitting.subgroup G, (e f.val).val = (θ f).val := by
  obtain ⟨ρ, hρ, hextends, _, hcontains, _⟩ :=
    generalizedFitting_permutation_model hnonab hn θ
  exact ⟨ρ.range, hcontains, MonoidHom.ofInjective hρ, hextends⟩

end CFSG.ComponentClassification.CatalogueBAlternating
