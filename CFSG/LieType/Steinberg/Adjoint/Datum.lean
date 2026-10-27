module

public import CFSG.LieType.Steinberg.Adjoint.Group
public import CFSG.LieType.Steinberg.PartBHalfSpace
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
open scoped commutatorElement

variable {τ : Tag}

section Roots

open CFSG.LieType.RootSystem

theorem roots_eq_setOf_isRoot (hA : TauCeti.IsFiniteType τ.cartan) :
    CFSG.LieType.RootSystem.roots hA ∅ = {γ | IsRoot τ γ} := by
  ext γ
  constructor
  · rintro (⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩)
    · obtain ⟨ω, rfl⟩ := (coxeterMatrix hA).toCoxeterSystem.wordProd_surjective w
      induction ω with
      | nil => simpa using IsRoot.basis i
      | cons j ω ih =>
        rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple,
          reflection_apply]
        exact IsRoot.reflect j ih
    · exact absurd hi (Set.notMem_empty i)
  · intro h
    induction h with
    | basis j => exact Or.inl ⟨1, j, by simp⟩
    | @reflect i v _ ih =>
      rcases ih with ⟨w, j, hw⟩ | ⟨w, j, hj, -⟩
      · refine Or.inl ⟨(coxeterMatrix hA).toCoxeterSystem.simple i * w, j, ?_⟩
        rw [weylAction_mul_apply, ← hw, weylAction_simple, reflection_apply]
        rfl
      · exact absurd hj (Set.notMem_empty j)

theorem weylAction_simple_eq_reflect (hA : TauCeti.IsFiniteType τ.cartan) (i : Fin τ.rank)
    (γ : Fin τ.rank → ℤ) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple i) γ = reflect τ i γ := by
  rw [weylAction_simple, reflection_apply]
  rfl

end Roots

theorem eq_single_or_neg_of_support {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {i : Fin τ.rank}
    (h : ∀ k, k ≠ i → γ k = 0) : γ = Pi.single i 1 ∨ γ = -Pi.single i 1 := by
  have e : γ = γ i • Pi.single i 1 := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [h k hk, Pi.single_eq_of_ne hk]
  rcases hγ.eq_one_or_neg_one_of_eq_smul e with h1 | h1
  · left
    rw [e, h1, one_smul]
  · right
    rw [e, h1, neg_one_smul]

theorem eq_one_of_isRoot_nsmul {γ : Fin τ.rank → ℤ} {n : ℕ} (h : IsRoot τ (n • γ)) : n = 1 := by
  have e : (n • γ : Fin τ.rank → ℤ) = (n : ℤ) • γ := (Nat.cast_smul_eq_nsmul ℤ n γ).symm
  rcases h.eq_one_or_neg_one_of_eq_smul e with h1 | h1 <;> omega

variable (F : RootOperatorFamily τ) (K : Type) [Field K]

abbrev adjDatum : UniversalRootDatum ↥(adjointGroup τ K) where
  rank := τ.rank
  cartan := τ.cartan
  isFiniteType := isFiniteType_cartan τ
  divisible := ∅
  rootGroup := rootGroup F K

theorem adjDatum_roots : (adjDatum F K).roots = {γ | IsRoot τ γ} :=
  roots_eq_setOf_isRoot _

variable {F K}

theorem mem_adjDatum_roots {γ : Fin τ.rank → ℤ} : γ ∈ (adjDatum F K).roots ↔ IsRoot τ γ := by
  rw [adjDatum_roots]
  rfl

theorem xPar_single_mem_rankOne (i : Fin τ.rank) (c : K) :
    xPar F (Pi.single i 1) c ∈ CurtisTits.rankOne (rootGroup F K) i :=
  Subgroup.mem_sup_left (xPar_mem (isRoot_single τ i) c)

theorem xPar_neg_single_mem_rankOne (i : Fin τ.rank) (c : K) :
    xPar F (-Pi.single i 1) c ∈ CurtisTits.rankOne (rootGroup F K) i :=
  Subgroup.mem_sup_right (xPar_mem (isRoot_neg_single τ i) c)

theorem steinbergWeyl_mem_rankOne (i : Fin τ.rank) (t : Kˣ) :
    CFSG.LieType.Steinberg.weylElement (xPar F) i t ∈ CurtisTits.rankOne (rootGroup F K) i :=
  mul_mem (mul_mem (xPar_single_mem_rankOne i _) (xPar_neg_single_mem_rankOne i _))
    (xPar_single_mem_rankOne i _)

theorem torusElement_one_eq (i : Fin τ.rank) : torusElement τ K i 1 = 1 :=
  Subtype.ext (torusElt_one i)

variable (F) in
theorem weylElement_eq_xPar (i : Fin τ.rank) :
    CFSG.LieType.Chevalley.weylElement τ K i =
      CFSG.LieType.Steinberg.weylElement (xPar F) i 1 := by
  rw [weylElement_xPar, torusElement_one_eq, one_mul]

theorem weylElement_mem_rankOne (i : Fin τ.rank) :
    CFSG.LieType.Chevalley.weylElement τ K i ∈ CurtisTits.rankOne (rootGroup F K) i := by
  rw [weylElement_eq_xPar F i]
  exact steinbergWeyl_mem_rankOne i 1

theorem torus_le_rankOne (i : Fin τ.rank) : torus K i ≤ CurtisTits.rankOne (rootGroup F K) i := by
  rintro _ ⟨t, rfl⟩
  have h : torusHom K i t = CFSG.LieType.Steinberg.weylElement (xPar F) i t *
      (CFSG.LieType.Chevalley.weylElement τ K i)⁻¹ :=
    eq_mul_inv_of_mul_eq (weylElement_xPar i t).symm
  rw [h]
  exact mul_mem (steinbergWeyl_mem_rankOne i t) (inv_mem (weylElement_mem_rankOne i))

variable (F K) in
theorem iSup_rootGroup_eq_top : ⨆ γ ∈ {γ | IsRoot τ γ}, rootGroup F K γ = ⊤ := by
  set S : Set (ModGL τ K) := {g | ∃ (i : Fin τ.rank) (c : K),
    (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
      (g : Module.End K (RootModule τ K)) = yOp τ K i c}
  have hcl : Subgroup.closure (((↑) : adjointGroup τ K → ModGL τ K) ⁻¹' S) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · have e : g = xPar F (Pi.single i 1) c := endHom_injective (by
      rw [xPar_simple, endHom_eltElement, F.elt_simple]
      exact hg)
    rw [e]
    exact Subgroup.mem_iSup_of_mem (Pi.single i 1)
      (Subgroup.mem_iSup_of_mem (isRoot_single τ i) (xPar_mem (isRoot_single τ i) c))
  · have e : g = xPar F (-Pi.single i 1) c := endHom_injective (by
      rw [xPar_neg_simple, endHom_eltElement, F.elt_neg_simple]
      exact hg)
    rw [e]
    exact Subgroup.mem_iSup_of_mem (-Pi.single i 1)
      (Subgroup.mem_iSup_of_mem (isRoot_neg_single τ i) (xPar_mem (isRoot_neg_single τ i) c))

variable (F K) in
theorem adjDatum_isCTGroupDatum :
    CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (adjDatum F K).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (adjDatum F K).isFiniteType) (adjDatum F K).roots
      (adjDatum F K).rootGroup (CFSG.LieType.Chevalley.weylElement τ K) (torus K) where
  n_mem i := weylElement_mem_rankOne i
  conj_mem i γ hγ x hx := by
    change _ ∈ rootGroup F K _
    rw [weylAction_simple_eq_reflect (isFiniteType_cartan τ)]
    exact weylElement_conj_mem i (mem_adjDatum_roots.1 hγ) hx
  braid i j := weylElement_braid (isFiniteType_cartan τ) i j
  H_le i := torus_le_rankOne i
  sq_mem i := ⟨-1, Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact (weylElt_one_sq τ K i).symm)⟩
  H_conj_mem l γ hγ h hh x hx := by
    obtain ⟨t, rfl⟩ := hh
    exact torusElement_conj_mem l t (mem_adjDatum_roots.1 hγ) hx
  conj_H_mem j l h hh := by
    obtain ⟨t, rfl⟩ := hh
    have e : CFSG.LieType.Chevalley.weylElement τ K j * torusHom K l t *
        (CFSG.LieType.Chevalley.weylElement τ K j)⁻¹ =
          torusHom K l t * torusHom K j (t ^ (-τ.cartan l j)) :=
      Subtype.ext (weylElt_one_mul_torusElt_mul_inv τ K j l t)
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right ⟨t, rfl⟩) (Subgroup.mem_sup_left ⟨_, rfl⟩)
  le_rankOne i γ hγ hsupp := by
    rcases eq_single_or_neg_of_support (mem_adjDatum_roots.1 hγ) hsupp with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  iSup_eq_top := by
    rw [adjDatum_roots]
    exact iSup_rootGroup_eq_top F K

section Extras

variable {D : AdjData τ} (hD : D.Valid)
include hD

theorem commutator_mem_openCone (hτ : NoG2 τ) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hlin : LinIndepPair γ δ) {x y : adjointGroup τ K}
    (hx : x ∈ rootGroup F K γ) (hy : y ∈ rootGroup F K δ) :
    ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (adjDatum F K).roots γ δ, (adjDatum F K).rootGroup ε := by
  have hne : γ ≠ δ := fun h => by
    have := (hlin 1 (-1) (by rw [h, one_smul, neg_one_smul, add_neg_cancel])).1
    exact one_ne_zero this
  have hne' : γ ≠ -δ := fun h => by
    have := (hlin 1 1 (by rw [h, one_smul, one_smul, neg_add_cancel])).1
    exact one_ne_zero this
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
  obtain ⟨d, rfl⟩ := (mem_rootGroup_iff hδ y).1 hy
  have key : ∀ a b : ℕ, 0 < a → 0 < b → ∀ e : K, xPar F (a • γ + b • δ) e ∈
      ⨆ ε ∈ openCone (adjDatum F K).roots γ δ, (adjDatum F K).rootGroup ε := by
    intro a b ha hb e
    by_cases hr : IsRoot τ (a • γ + b • δ)
    · exact Subgroup.mem_iSup_of_mem (a • γ + b • δ) (Subgroup.mem_iSup_of_mem
        ⟨mem_adjDatum_roots.2 hr, a, b, ha, hb, rfl⟩ (xPar_mem hr e))
    · rw [xPar_of_not_isRoot hr]
      exact one_mem _
  rw [commutator_xPar hD hτ hγ hδ hne hne']
  refine mul_mem (mul_mem ?_ ?_) ?_
  · have := key 1 1 one_pos one_pos
      ((RootOperatorFamily'.coeff11 F hD ⟨γ, hγ⟩ ⟨δ, hδ⟩ : K) * c * d)
    rwa [one_smul, one_smul] at this
  · have := key 1 2 one_pos two_pos
      ((RootOperatorFamily'.coeff12 F hD ⟨γ, hγ⟩ ⟨δ, hδ⟩ : K) * c * d ^ 2)
    rwa [one_smul] at this
  · have := key 2 1 two_pos one_pos
      ((RootOperatorFamily'.coeff21 F hD ⟨γ, hγ⟩ ⟨δ, hδ⟩ : K) * c ^ 2 * d)
    rwa [one_smul] at this

theorem adjDatum_steinbergExtras (hτ : NoG2 τ) (hnb : ∀ i, ∃ k, τ.cartan i k = -1)
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : τ.cartan * B = 1) :
    SteinbergExtras (adjDatum F K) (CFSG.LieType.Chevalley.weylElement τ K) (torus K) where
  ne_bot γ hγ := rootGroup_ne_bot (mem_adjDatum_roots.1 hγ)
  two_smul_le γ _ h2 := absurd (eq_one_of_isRoot_nsmul (mem_adjDatum_roots.1 h2)) (by norm_num)
  commutator_mem γ hγ δ hδ hlin x hx y hy :=
    commutator_mem_openCone hD hτ (mem_adjDatum_roots.1 hγ) (mem_adjDatum_roots.1 hδ) hlin hx hy
  prodInjective_pos L hnd hmem hsort :=
    prodInjective htHom L hnd
      (fun γ hγ => ⟨mem_adjDatum_roots.1 ((hmem γ).1 hγ).1, ((hmem γ).1 hγ).2.1⟩) hsort
  prodInjective_neg L hnd hmem hsort :=
    prodInjective (-htHom) L hnd
      (fun γ hγ => ⟨mem_adjDatum_roots.1 ((hmem γ).1 hγ).1, by
        rw [AddMonoidHom.neg_apply, htHom_apply]
        exact neg_pos.2 ((hmem γ).1 hγ).2.1⟩)
      (hsort.imp fun h => by
        rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, htHom_apply, htHom_apply]
        exact neg_le_neg h)
  posPart_inf_negPart :=
    eq_bot_iff.2 ((inf_le_inf (iSup₂_le fun γ hγ => rootGroup_le_unip htHom hγ.2)
      (iSup₂_le fun γ hγ => rootGroup_le_unip (-htHom) (by
        rw [AddMonoidHom.neg_apply, htHom_apply]
        exact neg_pos.2 hγ.2))).trans (unip_inf_unip_neg htHom).le)
  rankOne_bruhat i g hg := rankOne_bruhat F i hg
  eq_one_of_mem_normalizer i u hu hn := by
    obtain ⟨k, hk⟩ := hnb i
    exact eq_one_of_mem_normalizer F hk hu hn
  torus_commute i j h hh h' hh' := torus_commute hh hh'
  torus_iSupIndep := torus_iSupIndep hB
  torus_inf_posPart :=
    eq_bot_iff.2 ((inf_le_inf_left _ (iSup₂_le fun γ hγ => rootGroup_le_unip htHom hγ.2)).trans
      (iSup_torus_inf_unip htHom).le)

end Extras

theorem adjDatum_isParametrization (Φ : CFSG.LieType.Steinberg.RootSystem (Fin τ.rank))
    (hΦ : Φ.roots = {γ | IsRoot τ γ}) :
    IsParametrization (Φ := Φ) (adjDatum F K).rootGroup (xPar F) := by
  intro γ hγ
  rw [hΦ] at hγ
  exact ⟨fun g => mem_rootGroup_iff hγ g, fun c d => xPar_add γ c d, xPar_injective hγ⟩

end CFSG.LieType.Steinberg.Adjoint
