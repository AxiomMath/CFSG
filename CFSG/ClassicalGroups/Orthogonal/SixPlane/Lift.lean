module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.Basic
import CFSG.ClassicalGroups.Orthogonal.SixPlane.Align
import CFSG.ClassicalGroups.Orthogonal.SixPlane.Toral

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

private theorem lift_map_inv {a₀ : Fin 6} {σ : Equiv.Perm (Fin 6)} {A : Finset (Fin 6)}
    (h : (Finset.univ.erase a₀).map σ.toEmbedding = A) :
    A.map (σ⁻¹ : Equiv.Perm (Fin 6)).toEmbedding = Finset.univ.erase a₀ := by
  rw [← h, Finset.map_map]
  ext x
  simp

theorem exists_charts_of_lifts {H : Type u} [Group H] (a₀ : Fin 6)
    (φ₀ : ↥(supp 6 (Finset.univ.erase a₀)) →* H) (hφ₀ : Function.Injective φ₀)
    (b : Fin 6 → H)
    (hb : ∀ i (hi : i ∈ Finset.univ.erase a₀), φ₀ ⟨rot 6 i, rot_mem_supp hi⟩ = b i)
    (σ : Finset (Fin 6) → Equiv.Perm (Fin 6))
    (hσ : ∀ A : Finset (Fin 6), A.card = 5 → (Finset.univ.erase a₀).map (σ A).toEmbedding = A)
    (g : Finset (Fin 6) → H)
    (hg : ∀ A : Finset (Fin 6), A.card = 5 → ∀ i ∈ Finset.univ.erase a₀,
      g A * b i * (g A)⁻¹ = b (σ A i))
    (Y : Finset (Fin 6) → Subgroup H)
    (hY : ∀ S ⊆ Finset.univ.erase a₀, S.card = 4 →
      ((supp 6 S).subgroupOf (supp 6 (Finset.univ.erase a₀))).map φ₀ = Y S)
    (hYg : ∀ A : Finset (Fin 6), A.card = 5 → ∀ S ⊆ Finset.univ.erase a₀, S.card = 4 →
      (Y S).map (MulAut.conj (g A)).toMonoidHom = Y (S.map (σ A).toEmbedding)) :
    ∃ ψ : ∀ A : Finset (Fin 6), A.card = 5 → ↥(supp 6 A) →* H,
      (∀ (A : Finset (Fin 6)) (hA : A.card = 5), Function.Injective (ψ A hA)) ∧
      (∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
        (x : V 6 ≃ₗ[ZMod 2] V 6) (hxA : x ∈ supp 6 A), x ∈ supp 6 B →
          ∃ (x' : V 6 ≃ₗ[ZMod 2] V 6) (hx'B : x' ∈ supp 6 B), x' ∈ supp 6 A ∧
            ψ A hA ⟨x, hxA⟩ = ψ B hB ⟨x', hx'B⟩) ∧
      (∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
        (x : V 6 ≃ₗ[ZMod 2] V 6) (hxA : x ∈ supp 6 A) (hxB : x ∈ supp 6 B),
          x ∈ torus 6 Finset.univ → ψ A hA ⟨x, hxA⟩ = ψ B hB ⟨x, hxB⟩) ∧
      (∀ (A : Finset (Fin 6)) (hA : A.card = 5) (j : Fin 6) (hj : j ∈ A),
        ψ A hA ⟨rot 6 j, rot_mem_supp hj⟩ = b j) ∧
      (∀ (A : Finset (Fin 6)) (hA : A.card = 5),
        (ψ A hA).range = φ₀.range.map (MulAut.conj (g A)).toMonoidHom) ∧
      (∀ (A : Finset (Fin 6)) (hA : A.card = 5) (S : Finset (Fin 6)), S ⊆ A → S.card = 4 →
        ((supp 6 S).subgroupOf (supp 6 A)).map (ψ A hA) = Y S) := by
  classical
  have hinv : ∀ A : Finset (Fin 6), A.card = 5 →
      supp 6 (A.map (σ A)⁻¹.toEmbedding) = supp 6 (Finset.univ.erase a₀) := fun A hA =>
    congrArg (supp 6) (lift_map_inv (hσ A hA))
  let tr : ∀ A : Finset (Fin 6), A.card = 5 →
      ↥(supp 6 A) →* ↥(supp 6 (Finset.univ.erase a₀)) := fun A hA =>
    (((MulAut.conj (planePerm 6 (σ A)⁻¹)).toMonoidHom.comp (supp 6 A).subtype).codRestrict _
      fun x => (hinv A hA) ▸ planePerm_conj_mem_supp (σ A)⁻¹ x.2)
  have htr : ∀ A hA (x : ↥(supp 6 A)), ((tr A hA x : ↥(supp 6 (Finset.univ.erase a₀))) :
      V 6 ≃ₗ[ZMod 2] V 6) = planePerm 6 (σ A)⁻¹ * x * (planePerm 6 (σ A)⁻¹)⁻¹ := fun _ _ _ => rfl
  let ψ : ∀ A : Finset (Fin 6), A.card = 5 → ↥(supp 6 A) →* H := fun A hA =>
    (MulAut.conj (g A)).toMonoidHom.comp (φ₀.comp (tr A hA))
  have hψ : ∀ A hA x, ψ A hA x = g A * φ₀ (tr A hA x) * (g A)⁻¹ := fun _ _ _ => rfl
  have hrot : ∀ (A : Finset (Fin 6)) (hA : A.card = 5) (j : Fin 6) (hj : j ∈ A),
      ψ A hA ⟨rot 6 j, rot_mem_supp hj⟩ = b j := by
    intro A hA j hj
    have hj' : (σ A)⁻¹ j ∈ Finset.univ.erase a₀ := by
      rw [← lift_map_inv (hσ A hA)]
      exact Finset.mem_map_of_mem _ hj
    have htrj : tr A hA ⟨rot 6 j, rot_mem_supp hj⟩ = ⟨rot 6 ((σ A)⁻¹ j), rot_mem_supp hj'⟩ :=
      Subtype.ext ((htr A hA _).trans (planePerm_conj_rot _ _))
    rw [hψ A hA, htrj, hb _ hj', hg A hA _ hj']
    exact congrArg b ((σ A).apply_symm_apply j)
  have hS : ∀ (A : Finset (Fin 6)) (hA : A.card = 5) (S : Finset (Fin 6)), S ⊆ A →
      S.card = 4 → ((supp 6 S).subgroupOf (supp 6 A)).map (ψ A hA) = Y S := by
    intro A hA S hSA hS4
    have hS' : S.map (σ A)⁻¹.toEmbedding ⊆ Finset.univ.erase a₀ := by
      rw [← lift_map_inv (hσ A hA)]
      exact Finset.map_subset_map.mpr hSA
    have hS4' : (S.map (σ A)⁻¹.toEmbedding).card = 4 := by rw [Finset.card_map, hS4]
    have hmapS : (S.map (σ A)⁻¹.toEmbedding).map (σ A).toEmbedding = S := by
      rw [Finset.map_map]
      ext x
      simp
    have htrS : ((supp 6 S).subgroupOf (supp 6 A)).map (tr A hA) =
        (supp 6 (S.map (σ A)⁻¹.toEmbedding)).subgroupOf (supp 6 (Finset.univ.erase a₀)) := by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [htr A hA]
        exact planePerm_conj_mem_supp _ hx
      · intro hy
        have hx : planePerm 6 (σ A) * (y : V 6 ≃ₗ[ZMod 2] V 6) * (planePerm 6 (σ A))⁻¹ ∈
            supp 6 S := by
          convert planePerm_conj_mem_supp (σ A) hy using 2
          exact hmapS.symm
        refine ⟨⟨_, supp_mono hSA hx⟩, hx, Subtype.ext ?_⟩
        rw [htr A hA]
        change planePerm 6 (σ A)⁻¹ * (planePerm 6 (σ A) * (y : V 6 ≃ₗ[ZMod 2] V 6) *
          (planePerm 6 (σ A))⁻¹) * (planePerm 6 (σ A)⁻¹)⁻¹ = y
        rw [← planePerm_inv]
        group
    have hcomp : ψ A hA = (MulAut.conj (g A)).toMonoidHom.comp (φ₀.comp (tr A hA)) := rfl
    rw [hcomp, ← Subgroup.map_map, ← Subgroup.map_map, htrS, hY _ hS' hS4', hYg A hA _ hS' hS4',
      hmapS]
  refine ⟨ψ, ?_, ?_, ?_, hrot, ?_, hS⟩
  · intro A hA x y hxy
    have h1 := hφ₀ ((MulAut.conj (g A)).injective hxy)
    have h2 := congrArg Subtype.val h1
    rw [htr A hA, htr A hA] at h2
    exact Subtype.ext (by simpa using h2)
  · intro A B hA hB x hxA hxB
    by_cases hAB : A = B
    · subst hAB
      exact ⟨x, hxA, hxA, rfl⟩
    have hcard : (A ∩ B).card = 4 := by
      have hu := Finset.card_union_add_card_inter A B
      have hlt : A.card < (A ∪ B).card := by
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_union_left, fun h => hAB ?_⟩)
        refine (Finset.eq_of_subset_of_card_le (h ▸ Finset.subset_union_right) ?_).symm
        rw [hA, hB]
      have hle : (A ∪ B).card ≤ 6 := by
        simpa using Finset.card_le_univ (A ∪ B)
      omega
    have hxS : x ∈ supp 6 (A ∩ B) := by
      rw [← supp_inf]
      exact ⟨hxA, hxB⟩
    have hmem : ψ A hA ⟨x, hxA⟩ ∈ ((supp 6 (A ∩ B)).subgroupOf (supp 6 B)).map (ψ B hB) := by
      rw [hS B hB _ Finset.inter_subset_right hcard,
        ← hS A hA _ Finset.inter_subset_left hcard]
      exact ⟨⟨x, hxA⟩, hxS, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    exact ⟨y, y.2, supp_mono Finset.inter_subset_left hy, hyx.symm⟩
  · intro A B hA hB x hxA hxB hxT
    have hxS : x ∈ supp 6 (A ∩ B) := by
      rw [← supp_inf]
      exact ⟨hxA, hxB⟩
    have hxT' : x ∈ torus 6 (A ∩ B) := mem_torus_of_commute hxS fun i _ =>
      commute_of_mem_torus hxT (Subgroup.subset_closure ⟨i, Finset.mem_univ i, rfl⟩)
    have key : ∀ t ∈ torus 6 (A ∩ B), ∀ (htA : t ∈ supp 6 A) (htB : t ∈ supp 6 B),
        ψ A hA ⟨t, htA⟩ = ψ B hB ⟨t, htB⟩ := by
      intro t ht
      rw [torus] at ht
      induction ht using Subgroup.closure_induction with
      | mem t ht =>
        obtain ⟨j, hj, rfl⟩ := ht
        intro htA htB
        rw [Finset.mem_coe, Finset.mem_inter] at hj
        exact (hrot A hA j hj.1).trans (hrot B hB j hj.2).symm
      | one =>
        intro _ _
        exact ((ψ A hA).map_one).trans ((ψ B hB).map_one).symm
      | mul s t hs ht ihs iht =>
        intro _ _
        have hsA := supp_mono Finset.inter_subset_left (torus_le_supp _ hs)
        have hsB := supp_mono Finset.inter_subset_right (torus_le_supp _ hs)
        have htA := supp_mono Finset.inter_subset_left (torus_le_supp _ ht)
        have htB := supp_mono Finset.inter_subset_right (torus_le_supp _ ht)
        have e1 : (⟨s * t, (supp 6 A).mul_mem hsA htA⟩ : ↥(supp 6 A)) = ⟨s, hsA⟩ * ⟨t, htA⟩ :=
          rfl
        have e2 : (⟨s * t, (supp 6 B).mul_mem hsB htB⟩ : ↥(supp 6 B)) = ⟨s, hsB⟩ * ⟨t, htB⟩ :=
          rfl
        rw [e1, e2, map_mul, map_mul, ihs hsA hsB, iht htA htB]
      | inv t ht iht =>
        intro _ _
        have htA := supp_mono Finset.inter_subset_left (torus_le_supp _ ht)
        have htB := supp_mono Finset.inter_subset_right (torus_le_supp _ ht)
        have e1 : (⟨t⁻¹, (supp 6 A).inv_mem htA⟩ : ↥(supp 6 A)) = (⟨t, htA⟩)⁻¹ := rfl
        have e2 : (⟨t⁻¹, (supp 6 B).inv_mem htB⟩ : ↥(supp 6 B)) = (⟨t, htB⟩)⁻¹ := rfl
        rw [e1, e2, map_inv, map_inv, iht htA htB]
    exact key x hxT' hxA hxB
  · intro A hA
    have hcomp : ψ A hA = (MulAut.conj (g A)).toMonoidHom.comp (φ₀.comp (tr A hA)) := rfl
    have hsurj : Function.Surjective (tr A hA) := by
      intro y
      have hy := planePerm_conj_mem_supp (σ A) y.2
      rw [hσ A hA] at hy
      refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
      rw [htr A hA]
      change planePerm 6 (σ A)⁻¹ * (planePerm 6 (σ A) * (y : V 6 ≃ₗ[ZMod 2] V 6) *
        (planePerm 6 (σ A))⁻¹) * (planePerm 6 (σ A)⁻¹)⁻¹ = y
      rw [← planePerm_inv]
      group
    rw [hcomp, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj,
      ← MonoidHom.range_eq_map]

end CFSG.ClassicalGroups.Orthogonal.SixPlane

end
