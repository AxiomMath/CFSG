module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactEquivariance

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll mem_fixAll blockSpecialLinear
  centralizerPerfectCore_eq_map_of_le)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono mem_modelToG symm_mem_modelToG)
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] {F : Type} [Field F] {n : ℕ}

theorem siegelLevi_le_spBlock_univ : siegelLevi F n ≤ spBlock F Finset.univ := by
  intro x _ a b hab
  exact absurd ⟨by simp [mem_planeCoords], by simp [mem_planeCoords]⟩ hab

theorem siegelBlock_le_siegelLevi (B : Finset (Fin n)) : siegelBlock F B ≤ siegelLevi F n :=
  Subgroup.map_le_range _ _

theorem spFieldMap_leviEmbedSL (ι : K →+* F) (A : SL(n, K)) :
    spFieldMap n ι (leviEmbedSL K n A) = leviEmbedSL F n (Matrix.SpecialLinearGroup.map ι A) := by
  refine mat_injective ?_
  rw [mat_spFieldMap, mat_leviEmbedSL, mat_leviEmbedSL, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero ι), ← map_inv]
  congr 1

theorem spFieldMap_mem_siegelLevi (ι : K →+* F) {x : StatedSp n K} (hx : x ∈ siegelLevi K n) :
    spFieldMap n ι x ∈ siegelLevi F n := by
  obtain ⟨A, rfl⟩ := hx
  exact ⟨_, (spFieldMap_leviEmbedSL ι A).symm⟩

theorem diagSp_mul_leviEmbedSL_mul_inv (s : Fin n → Fˣ) (A : SL(n, F)) :
    diagSp F n s * leviEmbedSL F n A * (diagSp F n s)⁻¹ =
      leviEmbedSL F n (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F
        (TauCeti.diagGL s) A) := by
  rw [leviEmbedSL, MonoidHom.comp_apply, MonoidHom.comp_apply, diagSp, MonoidHom.comp_apply,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul,
    map_inv]

theorem diagSp_mem_normalizer_siegelLevi (s : Fin n → Fˣ) :
    diagSp F n s ∈ normalizer (siegelLevi F n : Set (StatedSp n F)) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨_, (diagSp_mul_leviEmbedSL_mul_inv s A).symm⟩
  · rintro ⟨A, hA⟩
    have hx : x = diagSp F n s⁻¹ * leviEmbedSL F n A * (diagSp F n s⁻¹)⁻¹ := by
      rw [hA, map_inv, inv_inv]
      group
    rw [hx]
    exact ⟨_, (diagSp_mul_leviEmbedSL_mul_inv s⁻¹ A).symm⟩

@[expose] noncomputable def fieldSiegel (σ : F ≃+* F) : MulAut (siegelLevi F n) where
  toFun x := ⟨spFieldMap n σ.toRingHom x, spFieldMap_mem_siegelLevi σ.toRingHom x.2⟩
  invFun x := ⟨spFieldMap n σ.symm.toRingHom x, spFieldMap_mem_siegelLevi σ.symm.toRingHom x.2⟩
  left_inv x := by
    apply Subtype.ext
    change spFieldMap n σ.symm.toRingHom (spFieldMap n σ.toRingHom (x : StatedSp n F)) = x
    refine mat_injective ?_
    rw [mat_spFieldMap, mat_spFieldMap]
    ext a b
    simp
  right_inv x := by
    apply Subtype.ext
    change spFieldMap n σ.toRingHom (spFieldMap n σ.symm.toRingHom (x : StatedSp n F)) = x
    refine mat_injective ?_
    rw [mat_spFieldMap, mat_spFieldMap]
    ext a b
    simp
  map_mul' x y := Subtype.ext (map_mul (spFieldMap n σ.toRingHom) (x : StatedSp n F) y)

theorem coe_fieldSiegel_apply (σ : F ≃+* F) (x : siegelLevi F n) :
    ((fieldSiegel σ x : siegelLevi F n) : StatedSp n F) = spFieldMap n σ.toRingHom x :=
  rfl

theorem siegelTorus_le_stringTorusSp (B : Finset (Fin n)) :
    siegelTorus K n ≤ stringTorusSp K B := by
  rintro _ ⟨s, rfl⟩
  exact ⟨fun _ => s, fun _ _ _ _ => rfl, rfl⟩

theorem liftParam_id (t : Fin n → Kˣ) : liftParam (RingHom.id K) t = t := by
  funext i
  exact Units.ext rfl

theorem perfectCore_siegelLevi_inf_centralizer_stringTorus [Finite F] (ι : K →+* F) {κ : Kˣ}
    (hκ : κ * κ ≠ 1) {B : Finset (Fin n)}
    (hperf : ⁅blockSpecialLinear (K := F) B, blockSpecialLinear (K := F) B⁆ =
      blockSpecialLinear B) :
    perfectCore (siegelLevi F n ⊓
        centralizer (diagSp F n '' (liftParam ι '' (stringTorusParam K B : Set (Fin n → Kˣ))))) =
      siegelBlock F B := by
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect
    (le_inf (siegelBlock_le_siegelLevi B) (siegelBlock_le_centralizer_of_const ?_))
    (commutator_siegelBlock_eq hperf))
  · rw [← perfectCore_spBlock_inf_centralizer_stringTorus ι hκ (Finset.subset_univ B) hperf]
    exact CFSG.Quasithin.perfectCore_mono (inf_le_inf_right _ siegelLevi_le_spBlock_univ)
  · rintro _ ⟨t, ht, rfl⟩ i hi j hj
    simp only [liftParam, ht i hi j hj]

theorem commute_of_mem_siegelBlock_of_disjoint {B B' : Finset (Fin n)} (hBB' : Disjoint B B')
    {x y : StatedSp n F} (hx : x ∈ siegelBlock F B) (hy : y ∈ siegelBlock F B') : Commute x y :=
  commute_of_mem_spBlock_of_disjoint hBB' (siegelBlock_le_spBlock B hx)
    (siegelBlock_le_spBlock B' hy)

end Model

section Glue

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  {n : ℕ} (e : L ≃* StatedSp n K) (ι : K →+* F)

@[expose] noncomputable def conjDiagSub {H : Subgroup (StatedSp n F)}
    (hH : ∀ s : Fin n → Fˣ, diagSp F n s ∈ normalizer (H : Set (StatedSp n F)))
    (t : Fin n → Kˣ) : MulAut H :=
  H.normalizerMonoidHom ⟨diagSp F n (liftParam ι t), hH _⟩

theorem coe_conjDiagSub_apply {H : Subgroup (StatedSp n F)}
    (hH : ∀ s : Fin n → Fˣ, diagSp F n s ∈ normalizer (H : Set (StatedSp n F)))
    (t : Fin n → Kˣ) (x : H) :
    ((conjDiagSub ι hH t x : H) : StatedSp n F) =
      diagSp F n (liftParam ι t) * x * (diagSp F n (liftParam ι t))⁻¹ :=
  rfl

@[expose] def SubTorusEquivariant {H : Subgroup (StatedSp n F)}
    (hH : ∀ s : Fin n → Fˣ, diagSp F n s ∈ normalizer (H : Set (StatedSp n F)))
    (P : Subgroup (Fin n → Kˣ)) (Φ : H →* G) : Prop :=
  ∀ t ∈ P, ∀ x : H, Φ (conjDiagSub ι hH t x) =
    ((e.symm (diagSp K n t) : L) : G) * Φ x * ((e.symm (diagSp K n t) : L) : G)⁻¹

theorem map_fixAll_conjDiagSub_eq {H : Subgroup (StatedSp n F)}
    (hH : ∀ s : Fin n → Fˣ, diagSp F n s ∈ normalizer (H : Set (StatedSp n F)))
    {P : Subgroup (Fin n → Kˣ)} (τ : modelToG e (diagTorusSp K P) → Fin n → Kˣ)
    (hτ : ∀ d, τ d ∈ P ∧ ((e.symm (diagSp K n (τ d)) : L) : G) = d) :
    (fixAll fun d => conjDiagSub ι hH (τ d)).map H.subtype =
      H ⊓ centralizer (diagSp F n '' (liftParam ι '' (P : Set (Fin n → Kˣ)))) := by
  have hsurj : ∀ t ∈ P, ∃ d, τ d = t := by
    intro t ht
    let d : modelToG e (diagTorusSp K P) :=
      ⟨((e.symm (diagSp K n t) : L) : G), symm_mem_modelToG e ⟨t, ht, rfl⟩⟩
    refine ⟨d, ?_⟩
    have h' : e.symm (diagSp K n (τ d)) = e.symm (diagSp K n t) := Subtype.ext (hτ d).2
    exact diagSp_injective (e.symm.injective h')
  ext x
  simp only [mem_map, mem_inf, coe_subtype, mem_centralizer_iff, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨d, rfl⟩ := hsurj t ht
    have h := congrArg Subtype.val (mem_fixAll.1 hy d)
    rw [coe_conjDiagSub_apply] at h
    calc diagSp F n (liftParam ι (τ d)) * (y : StatedSp n F) =
          diagSp F n (liftParam ι (τ d)) * (y : StatedSp n F) *
            (diagSp F n (liftParam ι (τ d)))⁻¹ * diagSp F n (liftParam ι (τ d)) := by group
      _ = (y : StatedSp n F) * diagSp F n (liftParam ι (τ d)) := by rw [h]
  · rintro ⟨hxH, hx⟩
    refine ⟨⟨x, hxH⟩, mem_fixAll.2 fun d => Subtype.ext ?_, rfl⟩
    rw [coe_conjDiagSub_apply]
    change diagSp F n (liftParam ι (τ d)) * x * (diagSp F n (liftParam ι (τ d)))⁻¹ = x
    rw [hx _ ⟨_, ⟨τ d, (hτ d).1, rfl⟩, rfl⟩, mul_inv_cancel_right]

variable [Finite G] [Finite F]

theorem torusCore_eq_map_of_conjDiagSub {H : Subgroup (StatedSp n F)}
    (hH : ∀ s : Fin n → Fˣ, diagSp F n s ∈ normalizer (H : Set (StatedSp n F)))
    {P : Subgroup (Fin n → Kˣ)} {X : Subgroup G} (hXP : X ≤ modelToG e (diagTorusSp K P))
    (Φ : H →* G) (hker : Φ.ker ≤ center H) (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : SubTorusEquivariant e ι hH P Φ) :
    torusCore e P = ((perfectCore (H ⊓ centralizer (diagSp F n ''
      (liftParam ι '' (P : Set (Fin n → Kˣ)))))).subgroupOf H).map Φ := by
  set T := modelToG e (diagTorusSp K P)
  let τ : T → Fin n → Kˣ := fun d => (exists_param_of_mem_modelToG_diagTorusSp e d.2).choose
  have hτ : ∀ d : T, τ d ∈ P ∧ ((e.symm (diagSp K n (τ d)) : L) : G) = d :=
    fun d => (exists_param_of_mem_modelToG_diagTorusSp e d.2).choose_spec
  have hα : ∀ (d : T) (x : H), Φ (conjDiagSub ι hH (τ d) x) = (d : G) * Φ x * (d : G)⁻¹ := by
    intro d x
    rw [hΦ _ (hτ d).1 x, (hτ d).2]
  rw [torusCore, centralizerPerfectCore_eq_map_of_le Φ hker hXP hrange
    (fun d => conjDiagSub ι hH (τ d)) hα]
  congr 1
  apply Subgroup.map_injective H.subtype_injective
  rw [CFSG.Quasithin.map_perfectCore, map_fixAll_conjDiagSub_eq e ι hH τ hτ,
    subgroupOf_map_subtype, inf_of_le_left ((CFSG.Quasithin.perfectCore_le _).trans inf_le_left)]

theorem torusCore_eq_map_of_conjDiagSub_prod {H : Subgroup (StatedSp n F)}
    (hH : ∀ s : Fin n → Fˣ, diagSp F n s ∈ normalizer (H : Set (StatedSp n F)))
    {P : Subgroup (Fin n → Kˣ)} {X : Subgroup G} (hXP : X ≤ modelToG e (diagTorusSp K P))
    (Ψ : H × H →* G) (hker : Ψ.ker ≤ center (H × H)) (hrange : Ψ.range = centralizerPerfectCore X)
    (hΨ : ∀ t ∈ P, ∀ x : H × H, Ψ (conjDiagSub ι hH t x.1, conjDiagSub ι hH t x.2) =
      ((e.symm (diagSp K n t) : L) : G) * Ψ x * ((e.symm (diagSp K n t) : L) : G)⁻¹) :
    torusCore e P = (((perfectCore (H ⊓ centralizer (diagSp F n ''
        (liftParam ι '' (P : Set (Fin n → Kˣ)))))).subgroupOf H).prod
      ((perfectCore (H ⊓ centralizer (diagSp F n ''
        (liftParam ι '' (P : Set (Fin n → Kˣ)))))).subgroupOf H)).map Ψ := by
  set T := modelToG e (diagTorusSp K P)
  let τ : T → Fin n → Kˣ := fun d => (exists_param_of_mem_modelToG_diagTorusSp e d.2).choose
  have hτ : ∀ d : T, τ d ∈ P ∧ ((e.symm (diagSp K n (τ d)) : L) : G) = d :=
    fun d => (exists_param_of_mem_modelToG_diagTorusSp e d.2).choose_spec
  set β : T → MulAut H := fun d => conjDiagSub ι hH (τ d) with hβ
  have hα : ∀ (d : T) (x : H × H),
      Ψ (((β d).prodCongr (β d)) x) = (d : G) * Ψ x * (d : G)⁻¹ := by
    intro d x
    rw [UnitaryPilot.prodCongr_apply_eq, hβ]
    rw [hΨ _ (hτ d).1 x, (hτ d).2]
  have hfix : perfectCore (fixAll β) = (perfectCore (H ⊓ centralizer (diagSp F n ''
      (liftParam ι '' (P : Set (Fin n → Kˣ)))))).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, hβ, map_fixAll_conjDiagSub_eq e ι hH τ hτ,
      subgroupOf_map_subtype, inf_of_le_left ((CFSG.Quasithin.perfectCore_le _).trans inf_le_left)]
  rw [torusCore, centralizerPerfectCore_eq_map_of_le Ψ hker hXP hrange
    (fun d => (β d).prodCongr (β d)) hα, UnitaryPilot.fixAll_prodCongr,
    UnitaryPilot.perfectCore_prod, hfix]

end Glue

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  {n : ℕ}

@[expose] def SiegelTorusEquivariant (e : L ≃* StatedSp n K) (ι : K →+* F)
    (P : Subgroup (Fin n → Kˣ)) (Φ : siegelLevi F n →* G) : Prop :=
  SubTorusEquivariant e ι diagSp_mem_normalizer_siegelLevi P Φ

structure SiegelFieldParam (e : L ≃* StatedSp n K) (t : G) (ι : K →+* F) (σ : F ≃+* F) where
  Φ : siegelLevi F n →* G
  range_eq : Φ.range = siegelCore e
  ker_le : Φ.ker ≤ center (siegelLevi F n)
  N1 : ∀ (x : StatedSp n K) (hx : x ∈ siegelLevi K n),
    Φ ⟨spFieldMap n ι x, spFieldMap_mem_siegelLevi ι hx⟩ = ((e.symm x : L) : G)
  N2 : SiegelTorusEquivariant e ι ⊤ Φ
  N3 : ∀ x : siegelLevi F n, t * Φ x * t⁻¹ = Φ (fieldSiegel σ x)

structure SiegelSwapParam (e : L ≃* StatedSp n K) (t : G) where
  Ψ : siegelLevi K n × siegelLevi K n →* G
  range_eq : Ψ.range = siegelCore e
  ker_le : Ψ.ker ≤ center (siegelLevi K n × siegelLevi K n)
  diag : ∀ x : siegelLevi K n, Ψ (x, x) = ((e.symm x : L) : G)
  N2 : ∀ (s : Fin n → Kˣ) (x : siegelLevi K n × siegelLevi K n),
    Ψ (conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi s x.1,
      conjDiagSub (RingHom.id K) diagSp_mem_normalizer_siegelLevi s x.2) =
      ((e.symm (diagSp K n s) : L) : G) * Ψ x * ((e.symm (diagSp K n s) : L) : G)⁻¹
  swap : ∀ x y : siegelLevi K n, t * Ψ (x, y) * t⁻¹ = Ψ (y, x)

end Param

section Commute

variable {G M : Type*} [Group G] [Group M]

theorem map_subgroupOf_le_centralizer_of_commute {S H₁ H₂ : Subgroup M}
    (h : ∀ x ∈ H₁, ∀ y ∈ H₂, Commute x y) (Φ : S →* G) :
    (H₁.subgroupOf S).map Φ ≤ centralizer (((H₂.subgroupOf S).map Φ : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hxy : y * x = x * y :=
    Subtype.ext (h _ (mem_subgroupOf.1 hx) _ (mem_subgroupOf.1 hy)).eq.symm
  rw [← map_mul, ← map_mul, hxy]

theorem map_prod_subgroupOf_le_centralizer_of_commute {S H₁ H₂ : Subgroup M}
    (h : ∀ x ∈ H₁, ∀ y ∈ H₂, Commute x y) (Ψ : S × S →* G) :
    ((H₁.subgroupOf S).prod (H₁.subgroupOf S)).map Ψ ≤
      centralizer ((((H₂.subgroupOf S).prod (H₂.subgroupOf S)).map Ψ : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hxy : y * x = x * y := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact (h _ (mem_subgroupOf.1 (mem_prod.1 hx).1) _
        (mem_subgroupOf.1 (mem_prod.1 hy).1)).eq.symm
    · exact (h _ (mem_subgroupOf.1 (mem_prod.1 hx).2) _
        (mem_subgroupOf.1 (mem_prod.1 hy).2)).eq.symm
  rw [← map_mul, ← map_mul, hxy]

end Commute

end CFSG.SeitzReduction.SymplecticPilot
