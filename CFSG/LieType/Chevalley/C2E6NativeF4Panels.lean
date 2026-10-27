module

public import CFSG.LieType.Chevalley.C2E6NativeF4Partition
public import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder
public import CFSG.LieType.Chevalley.GraphFixedMinimalBorel

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
open scoped Pointwise

section Count

variable {A : Type*} [Group A] {G B U : Subgroup A} {D : Set A} {n : A}

theorem ncard_image_mk_of_bijOn (hDG : D ⊆ G) (hD : D⁻¹ = D)
    (hbij : Set.BijOn (fun p : A × A => p.1 * n * p.2) ((B : Set A) ×ˢ (U : Set A)) D) :
    ((fun x : G => (x : G ⧸ B.subgroupOf G)) '' (Subtype.val ⁻¹' D)).ncard = Nat.card U := by
  have hnu : ∀ u ∈ U, n * u ∈ D := fun u hu => by
    have h := hbij.mapsTo (Set.mk_mem_prod (one_mem B) hu)
    rwa [one_mul] at h
  have hmem : ∀ u : U, (u : A)⁻¹ * n⁻¹ ∈ G := fun u => by
    rw [← mul_inv_rev]
    exact inv_mem (hDG (hnu u u.2))
  set f : U → G ⧸ B.subgroupOf G := fun u => ((⟨_, hmem u⟩ : G) : G ⧸ B.subgroupOf G) with hf
  have hrange : (fun x : G => (x : G ⧸ B.subgroupOf G)) '' (Subtype.val ⁻¹' D) = Set.range f := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : A)⁻¹ ∈ D := by
        rw [← hD] at hx
        exact hx
      obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, hbu⟩ := hbij.surjOn hx'
      refine ⟨⟨u, hu⟩, ?_⟩
      rw [hf, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e : ((⟨_, hmem ⟨u, hu⟩⟩ : G)⁻¹ * x : G) = (b⁻¹ : A) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, inv_inv]
        dsimp only at hbu
        rw [← inv_inv (x : A), ← hbu]
        group
      rw [e]
      exact inv_mem hb
    · rintro ⟨u, rfl⟩
      refine ⟨⟨_, hmem u⟩, ?_, rfl⟩
      show (u : A)⁻¹ * n⁻¹ ∈ D
      rw [← mul_inv_rev, ← Set.mem_inv, hD]
      exact hnu u u.2
  have hinj : Function.Injective f := by
    intro u u' h
    rw [hf, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at h
    set b := n * (u : A) * (u' : A)⁻¹ * n⁻¹ with hb
    have hb' : n * (u : A) * ((u' : A)⁻¹ * n⁻¹) = b := by rw [hb]; group
    rw [hb'] at h
    have e := hbij.injOn (Set.mk_mem_prod h u'.2) (Set.mk_mem_prod (one_mem B) u.2)
      (by dsimp only; rw [hb]; group)
    exact Subtype.ext (congrArg Prod.snd e).symm
  rw [hrange, Set.ncard_range_of_injective hinj]

end Count

@[expose] def stdInvUnipotent
    (w : relWeylTwist TwistTag.E6) : Subgroup (ModGL Tag.E6 K) :=
  graphFixedInversionUnipotent TwistTag.E6 K barHom w

theorem bijOn_stdBruhatCell
    (w : relWeylTwist TwistTag.E6) :
    Set.BijOn (fun p : ModGL Tag.E6 K × ModGL Tag.E6 K => p.1 * stdRepM w * p.2)
      ((stdBorel : Set (ModGL Tag.E6 K)) ×ˢ (stdInvUnipotent w : Set (ModGL Tag.E6 K)))
      (stdBruhatCell w) := by
  have h := ((fixed_root_Bruhat_decomposition TwistTag.E6 K barEquiv).2.2.2.2.2.2.2.2.2.2.2.1 w
    w.2).1
  rw [barEquiv_toRingHom] at h
  exact h

theorem nativeSimple_inv
    (i : Fin 4) : (nativeSimple i)⁻¹ = nativeSimple i :=
  Subtype.ext (TwistTag.E6.orbitReflection_inv _)

theorem ncard_image_stdCell_nativeSimple
    (i : Fin 4) :
    ((fun x : stdGroup => (x : stdGroup ⧸ stdBorelG)) '' stdCell (nativeSimple i)).ncard =
      Nat.card (stdInvUnipotent (nativeSimple i)) := by
  refine ncard_image_mk_of_bijOn (stdBruhatCell_subset _) ?_ (bijOn_stdBruhatCell _)
  rw [inv_stdBruhatCell, nativeSimple_inv]

theorem card_stdInvUnipotent_nativeSimple
    (i : Fin 4) :
    Nat.card (stdInvUnipotent (nativeSimple i)) = if (i : ℕ) < 2 then 2 else 4 := by
  have h1 : (stdInvUnipotent (nativeSimple i) : Set (ModGL Tag.E6 K)) =
      Set.range fun c : orbitField TwistTag.E6 K barHom (foldedIndex i) =>
        (orbitX TwistTag.E6 K barHom (foldedIndex i) c : ModGL TwistTag.E6.tag K) := by
    have h := coe_rootSpan_simpleOrbitRoots_inf (t := TwistTag.E6) (K := K) (σ := barHom)
      (foldedIndex i)
    rw [← inversionSet_orbitReflection] at h
    exact h
  have hinj : Function.Injective fun c : orbitField TwistTag.E6 K barHom (foldedIndex i) =>
      (orbitX TwistTag.E6 K barHom (foldedIndex i) c : ModGL TwistTag.E6.tag K) :=
    Subtype.val_injective.comp (orbitX_injective barHom (foldedIndex i))
  have h2 : Nat.card (stdInvUnipotent (nativeSimple i)) =
      (stdInvUnipotent (nativeSimple i) : Set (ModGL Tag.E6 K)).ncard :=
    (Nat.card_coe_set_eq _).symm
  rw [h2, h1]
  refine (Set.ncard_range_of_injective hinj).trans ?_
  rw [card_orbitField, ← nativeOrbit_eq_orbit]
  fin_cases i <;> rfl

end CFSG.LieType.Chevalley.C2E6Std
