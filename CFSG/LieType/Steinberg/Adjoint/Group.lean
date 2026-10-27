module

public import CFSG.LieType.Steinberg.Adjoint.RankOne
public import CFSG.LieType.Steinberg.Adjoint.Torus
public import CFSG.LieType.Chevalley.Canonical
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

variable {τ : Tag} (F : RootOperatorFamily τ) {K : Type} [Field K]

open _root_.Classical in
@[expose] def xPar (γ : Fin τ.rank → ℤ) (c : K) : adjointGroup τ K :=
  if h : IsRoot τ γ then F.eltElement ⟨γ, h⟩ c else 1

variable {F}

theorem xPar_of_isRoot {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : K) :
    xPar F γ c = F.eltElement ⟨γ, h⟩ c := by
  classical
  exact dite_eq_left h

theorem xPar_of_not_isRoot {γ : Fin τ.rank → ℤ} (h : ¬IsRoot τ γ) (c : K) : xPar F γ c = 1 := by
  classical
  exact dite_eq_right h

theorem endHom_xPar (γ : Fin τ.rank → ℤ) (c : K) :
    endHom K (xPar F γ c) = RootOperatorFamily'.eltOr F K γ c := by
  by_cases h : IsRoot τ γ
  · rw [xPar_of_isRoot h, RootOperatorFamily'.eltOr_of_isRoot F K h]
    rfl
  · rw [xPar_of_not_isRoot h, RootOperatorFamily'.eltOr_of_not_isRoot F K h, map_one]

theorem xPar_simple (i : Fin τ.rank) (c : K) :
    xPar F (Pi.single i 1) c = F.eltElement (simpleRoot τ i) c :=
  xPar_of_isRoot (isRoot_single τ i) c

theorem xPar_neg_simple (i : Fin τ.rank) (c : K) :
    xPar F (-Pi.single i 1) c = F.eltElement (-simpleRoot τ i) c :=
  xPar_of_isRoot (isRoot_neg_single τ i) c

theorem xPar_mem {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : K) : xPar F γ c ∈ rootGroup F K γ := by
  rw [xPar_of_isRoot h, rootGroup_of_isRoot h]
  exact F.eltElement_mem_rootSubgroup _ c

theorem mem_rootGroup_iff {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (g : adjointGroup τ K) :
    g ∈ rootGroup F K γ ↔ ∃ c, xPar F γ c = g := by
  constructor
  · intro hg
    obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup h hg
    exact ⟨c, xPar_of_isRoot h c⟩
  · rintro ⟨c, rfl⟩
    exact xPar_mem h c

theorem xPar_add (γ : Fin τ.rank → ℤ) (c d : K) : xPar F γ (c + d) = xPar F γ c * xPar F γ d := by
  by_cases h : IsRoot τ γ
  · rw [xPar_of_isRoot h, xPar_of_isRoot h, xPar_of_isRoot h, F.eltElement_add]
  · rw [xPar_of_not_isRoot h, xPar_of_not_isRoot h, xPar_of_not_isRoot h, mul_one]

theorem xPar_zero (γ : Fin τ.rank → ℤ) : xPar F γ (0 : K) = 1 := by
  by_cases h : IsRoot τ γ
  · rw [xPar_of_isRoot h, F.eltElement_zero]
  · rw [xPar_of_not_isRoot h]

theorem xPar_neg (γ : Fin τ.rank → ℤ) (c : K) : (xPar F γ c)⁻¹ = xPar F γ (-c) := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, ← xPar_add, neg_add_cancel, xPar_zero]

theorem xPar_injective {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) :
    Function.Injective (xPar F γ : K → adjointGroup τ K) := by
  intro c d hcd
  obtain ⟨a, b, hab⟩ := RootOperatorFamily'.exists_D_one_apply_ne_zero F (R := K) ⟨γ, h⟩
  have hshift : labelWt τ a = labelWt τ b + γ := by
    have := F.mapsLabelWt_D (R := K) ⟨γ, h⟩ le_rfl a b hab
    rwa [one_nsmul] at this
  have h1 := congrArg (fun g => endHom K g (Finsupp.single b 1) a) hcd
  simp only [xPar_of_isRoot h, endHom_eltElement,
    RootOperatorFamily'.elt_apply_of_shift F ⟨γ, h⟩ _ hshift] at h1
  exact mul_right_cancel₀ hab h1

theorem rootGroup_ne_bot {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) : rootGroup F K γ ≠ ⊥ := by
  intro hbot
  have h1 := xPar_mem (F := F) h (1 : K)
  rw [hbot, Subgroup.mem_bot, ← xPar_zero (F := F) γ] at h1
  exact one_ne_zero (xPar_injective h h1)

theorem weylElement_xPar (i : Fin τ.rank) (t : Kˣ) :
    CFSG.LieType.Steinberg.weylElement (xPar F) i t =
      torusElement τ K i t * CFSG.LieType.Chevalley.weylElement τ K i := by
  rw [CFSG.LieType.Steinberg.weylElement, xPar_simple, xPar_neg_simple]
  have h := xyx_eq_weylElt F (i := i) (Units.ne_zero t)
  rw [Units.val_inv_eq_inv_val, h]
  refine Subtype.ext ?_
  change weylElt τ K i (Units.mk0 (t : K) _) = torusElt τ K i t * weylElt τ K i 1
  rw [torusElt_mul_weylElt_one, Units.mk0_val]

theorem weylElement_xPar_conj (i : Fin τ.rank) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (t : Kˣ) (u : K),
      CFSG.LieType.Steinberg.weylElement (xPar F) i t * xPar F β u *
          (CFSG.LieType.Steinberg.weylElement (xPar F) i t)⁻¹ =
        xPar F (CFSG.LieType.RootSystem.reflection τ.cartan i β)
          ((ε : K) * ((t ^ (-(∑ j, τ.cartan i j * β j)) : Kˣ) : K) * u) := by
  refine ⟨F.sign i ⟨β, hβ⟩, F.sign_eq i _, fun t u => ?_⟩
  have hrefl : CFSG.LieType.RootSystem.reflection τ.cartan i β = reflect τ i β := by
    rw [CFSG.LieType.RootSystem.reflection_apply]
    rfl
  have hs : simple τ i • (⟨β, hβ⟩ : Root τ) = ⟨reflect τ i β, IsRoot.reflect i hβ⟩ :=
    Subtype.ext (simple_smul i β)
  rw [weylElement_xPar, hrefl, xPar_of_isRoot hβ, xPar_of_isRoot (IsRoot.reflect i hβ),
    mul_inv_rev, show torusElement τ K i t * CFSG.LieType.Chevalley.weylElement τ K i *
        F.eltElement ⟨β, hβ⟩ u * ((CFSG.LieType.Chevalley.weylElement τ K i)⁻¹ *
          (torusElement τ K i t)⁻¹) =
      torusElement τ K i t * (CFSG.LieType.Chevalley.weylElement τ K i * F.eltElement ⟨β, hβ⟩ u *
        (CFSG.LieType.Chevalley.weylElement τ K i)⁻¹) * (torusElement τ K i t)⁻¹ by group,
    F.weylElement_mul_eltElement_mul_inv, hs, F.torusElement_mul_eltElement_mul_inv]
  congr 1
  rw [show (∑ j, τ.cartan i j * (⟨reflect τ i β, IsRoot.reflect i hβ⟩ : Root τ).1 j) =
    -∑ j, τ.cartan i j * β j from sum_cartan_mul_reflect τ i β]
  ring

theorem weylElement_conj_mem (i : Fin τ.rank) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {x : adjointGroup τ K} (hx : x ∈ rootGroup F K γ) :
    CFSG.LieType.Chevalley.weylElement τ K i * x * (CFSG.LieType.Chevalley.weylElement τ K i)⁻¹ ∈
      rootGroup F K (reflect τ i γ) := by
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
  rw [xPar_of_isRoot hγ, F.weylElement_mul_eltElement_mul_inv,
    show simple τ i • (⟨γ, hγ⟩ : Root τ) = ⟨reflect τ i γ, IsRoot.reflect i hγ⟩ from
      Subtype.ext (simple_smul i γ), ← xPar_of_isRoot (IsRoot.reflect i hγ)]
  exact xPar_mem (IsRoot.reflect i hγ) _

theorem torusElement_conj_mem (i : Fin τ.rank) (t : Kˣ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {x : adjointGroup τ K} (hx : x ∈ rootGroup F K γ) :
    torusElement τ K i t * x * (torusElement τ K i t)⁻¹ ∈ rootGroup F K γ := by
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
  rw [xPar_of_isRoot hγ, F.torusElement_mul_eltElement_mul_inv, ← xPar_of_isRoot hγ]
  exact xPar_mem hγ _

theorem weylElement_braid (hA : TauCeti.IsFiniteType τ.cartan) (i j : Fin τ.rank) :
    ((CoxeterSystem.braidWord (CFSG.LieType.RootSystem.coxeterMatrix hA) i j).map
        (CFSG.LieType.Chevalley.weylElement τ K)).prod =
      ((CoxeterSystem.braidWord (CFSG.LieType.RootSystem.coxeterMatrix hA) j i).map
        (CFSG.LieType.Chevalley.weylElement τ K)).prod := by
  refine Subtype.ext ?_
  rw [← Subgroup.coe_subtype, map_list_prod, map_list_prod, List.map_map, List.map_map]
  exact prod_braidWord_weylElt hA K i j

theorem prodInjective (φ : (Fin τ.rank → ℤ) →+ ℤ) (L : List (Fin τ.rank → ℤ)) (hnd : L.Nodup)
    (hL : ∀ γ ∈ L, IsRoot τ γ ∧ 0 < φ γ) (hsort : L.Pairwise fun γ δ => φ γ ≤ φ δ) :
    ProdInjectiveFor (rootGroup F K) L := by
  classical
  intro f g hf hg heq
  have hcf : ∀ γ ∈ L, ∃ c, xPar F γ c = f γ := fun γ hγ =>
    (mem_rootGroup_iff (hL γ hγ).1 _).1 (hf γ hγ)
  have hcg : ∀ γ ∈ L, ∃ c, xPar F γ c = g γ := fun γ hγ =>
    (mem_rootGroup_iff (hL γ hγ).1 _).1 (hg γ hγ)
  set c : (Fin τ.rank → ℤ) → K := fun γ => if h : γ ∈ L then (hcf γ h).choose else 0
  set c' : (Fin τ.rank → ℤ) → K := fun γ => if h : γ ∈ L then (hcg γ h).choose else 0
  have hfc : ∀ γ ∈ L, f γ = xPar F γ (c γ) := fun γ hγ => by
    simp only [c, dite_eq_left hγ]
    exact (hcf γ hγ).choose_spec.symm
  have hgc : ∀ γ ∈ L, g γ = xPar F γ (c' γ) := fun γ hγ => by
    simp only [c', dite_eq_left hγ]
    exact (hcg γ hγ).choose_spec.symm
  have hprod : (L.map fun γ => RootOperatorFamily'.eltOr F K γ (c γ)).prod =
      (L.map fun γ => RootOperatorFamily'.eltOr F K γ (c' γ)).prod := by
    have h1 := congrArg (endHom K) heq
    rw [map_list_prod, map_list_prod, List.map_map, List.map_map] at h1
    have e1 : L.map (endHom K ∘ f) = L.map fun γ => RootOperatorFamily'.eltOr F K γ (c γ) :=
      List.map_congr_left fun γ hγ => by simp only [Function.comp_apply, hfc γ hγ, endHom_xPar]
    have e2 : L.map (endHom K ∘ g) = L.map fun γ => RootOperatorFamily'.eltOr F K γ (c' γ) :=
      List.map_congr_left fun γ hγ => by simp only [Function.comp_apply, hgc γ hγ, endHom_xPar]
    rwa [e1, e2] at h1
  intro γ hγ
  rw [hfc γ hγ, hgc γ hγ,
    RootOperatorFamily'.prod_eltOr_injective F L hnd hL hsort c c' hprod γ hγ]

section Comm

variable {D : AdjData τ} (hD : D.Valid)
include hD

theorem commutator_xPar (hτ : NoG2 τ) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) (c d : K) :
    ⁅xPar F α c, xPar F β d⁆ =
      xPar F (α + β) ((RootOperatorFamily'.coeff11 F hD ⟨α, hα⟩ ⟨β, hβ⟩ : K) * c * d) *
        xPar F (α + 2 • β)
          ((RootOperatorFamily'.coeff12 F hD ⟨α, hα⟩ ⟨β, hβ⟩ : K) * c * d ^ 2) *
          xPar F (2 • α + β)
            ((RootOperatorFamily'.coeff21 F hD ⟨α, hα⟩ ⟨β, hβ⟩ : K) * c ^ 2 * d) := by
  refine endHom_injective ?_
  rw [commutatorElement_def, xPar_neg, xPar_neg]
  simp only [map_mul, endHom_xPar, RootOperatorFamily'.eltOr_of_isRoot F K hα,
    RootOperatorFamily'.eltOr_of_isRoot F K hβ]
  exact RootOperatorFamily'.comm_formula F hD hτ (α := ⟨α, hα⟩) (β := ⟨β, hβ⟩) hne hne' c d

theorem commute_xPar (hτ : NoG2 τ) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (hne : γ + δ ≠ 0) (hn : ¬IsRoot τ (γ + δ)) (a b : K) :
    Commute (xPar F γ a) (xPar F δ b) := by
  by_cases hγδ : γ = δ
  · subst hγδ
    rw [Commute, SemiconjBy, ← xPar_add, ← xPar_add, add_comm]
  · have hne' : γ ≠ -δ := fun h => hne (by rw [h, neg_add_cancel])
    have h12 : ¬IsRoot τ (γ + 2 • δ) := fun h =>
      hn (isRoot_add_of_isRoot_add_two_smul hδ hγ hγδ hne' h)
    have h21 : ¬IsRoot τ (2 • γ + δ) := fun h => hn (by
      rw [add_comm]
      exact isRoot_add_of_isRoot_add_two_smul hγ hδ (Ne.symm hγδ)
        (fun h' => hne' (by rw [h', neg_neg])) (by rwa [add_comm]))
    rw [← commutatorElement_eq_one_iff_commute, commutator_xPar hD hτ hγ hδ hγδ hne',
      xPar_of_not_isRoot hn, xPar_of_not_isRoot h12, xPar_of_not_isRoot h21, mul_one, mul_one]

end Comm

end CFSG.LieType.Steinberg.Adjoint
