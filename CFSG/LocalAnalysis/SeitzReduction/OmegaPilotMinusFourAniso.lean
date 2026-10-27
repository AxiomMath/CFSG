module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourDiag
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoresAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoF6

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_le_centralizer
  commutator_centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll consecutiveBlock)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open scoped MatrixGroups

section Glue

variable {G : Type*} [Group G] {M : Type*} [Group M]

theorem map_centralizerPerfectCore_subgroupOf_eq_of_le [Finite G] [Finite M] {X T : Subgroup G}
    (hTX : centralizerPerfectCore T ≤ centralizerPerfectCore X)
    (π : centralizerPerfectCore X →* M) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center (centralizerPerfectCore X))
    (α : T → MulAut (centralizerPerfectCore X))
    (hα : ∀ (d : T) (x : centralizerPerfectCore X), ((α d x : centralizerPerfectCore X) : G) =
      (d : G) * x * (d : G)⁻¹)
    (β : T → MulAut M) (hαβ : ∀ d x, π (α d x) = β d (π x)) :
    ((centralizerPerfectCore T).subgroupOf (centralizerPerfectCore X)).map π =
      perfectCore (fixAll β) := by
  have hker' : (centralizerPerfectCore X).subtype.ker ≤ center (centralizerPerfectCore X) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 (centralizerPerfectCore X).subtype_injective]
    exact bot_le
  have h0 := LinearPilot.perfectCore_range_inf_centralizer (centralizerPerfectCore X).subtype
    hker' α hα
  rw [range_subtype] at h0
  have h1 : centralizerPerfectCore T =
      perfectCore (centralizerPerfectCore X ⊓ centralizer (T : Set G)) := by
    apply le_antisymm
    · exact le_perfectCore_of_perfect (le_inf hTX (centralizerPerfectCore_le_centralizer T))
        (commutator_centralizerPerfectCore T)
    · exact CFSG.Quasithin.perfectCore_mono inf_le_right
  have h2 : (centralizerPerfectCore T).subgroupOf (centralizerPerfectCore X) =
      perfectCore (fixAll α) := by
    rw [h1, h0, subgroupOf, comap_map_eq_self_of_injective
      (centralizerPerfectCore X).subtype_injective]
  rw [h2, map_perfectCore_fixAll_of_surjective π hπ hker α β hαβ]

end Glue

section FrameGlue

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)} {a b : Fin m → Fin d}
  (h : IsHypFrame Q a b) (e : L ≃* matrixProjectiveDerived Q) {F : Type} [Field F] [Finite F]

include h in
theorem map_frameCore_eq_of_conjDiag_quot_of_le {m' : ℕ}
    (δ : (Fin m → Kˣ) →* GL (Fin m' ⊕ Fin m') F)
    (hδ : ∀ t, δ t ∈ normalizer (StatedOmega (StatedQuadPlus m' F) : Set (GL (Fin m' ⊕ Fin m') F)))
    {P : Subgroup (Fin m → Kˣ)} {X : Subgroup G}
    (hN : ∀ g ∈ modelToG e (frameTorusOf Q a b P),
      g ∈ normalizer (centralizerPerfectCore X : Set G))
    (hTX : centralizerPerfectCore (modelToG e (frameTorusOf Q a b P)) ≤ centralizerPerfectCore X)
    (π : centralizerPerfectCore X →* StatedOmega (StatedQuadPlus m' F))
    (hπ : Function.Surjective π) (hker : π.ker ≤ center (centralizerPerfectCore X))
    (hequiv : ∀ t ∈ P, ∀ (hn : ((e.symm (h.frameHom t) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G)) (x : centralizerPerfectCore X),
      π ((centralizerPerfectCore X).normalizerMonoidHom ⟨_, hn⟩ x) =
        (StatedOmega (StatedQuadPlus m' F)).normalizerMonoidHom ⟨δ t, hδ t⟩ (π x)) :
    (((centralizerPerfectCore (modelToG e (frameTorusOf Q a b P))).subgroupOf
        (centralizerPerfectCore X)).map π).map (StatedOmega (StatedQuadPlus m' F)).subtype =
      perfectCore (StatedOmega (StatedQuadPlus m' F) ⊓
        centralizer (δ '' (P : Set (Fin m → Kˣ)))) := by
  set T := modelToG e (frameTorusOf Q a b P)
  let τ : T → Fin m → Kˣ := fun x => (exists_param_of_mem_modelToG_frameTorusOf h e x.2).choose
  have hτ : ∀ x : T, τ x ∈ P ∧ ((e.symm (h.frameHom (τ x)) : L) : G) = x :=
    fun x => (exists_param_of_mem_modelToG_frameTorusOf h e x.2).choose_spec
  have hN' : ∀ g : T, (g : G) ∈ normalizer (centralizerPerfectCore X : Set G) :=
    fun g => hN g g.2
  let α : T → MulAut (centralizerPerfectCore X) := fun g =>
    (centralizerPerfectCore X).normalizerMonoidHom ⟨g, hN' g⟩
  let β : T → MulAut (StatedOmega (StatedQuadPlus m' F)) := fun g =>
    (StatedOmega (StatedQuadPlus m' F)).normalizerMonoidHom ⟨δ (τ g), hδ (τ g)⟩
  have hαβ : ∀ g x, π (α g x) = β g (π x) := by
    intro g x
    have hn : ((e.symm (h.frameHom (τ g)) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G) := by
      rw [(hτ g).2]
      exact hN' g
    have hg : (⟨(g : G), hN' g⟩ : normalizer (centralizerPerfectCore X : Set G)) =
        ⟨((e.symm (h.frameHom (τ g)) : L) : G), hn⟩ := Subtype.ext (hτ g).2.symm
    change π ((centralizerPerfectCore X).normalizerMonoidHom ⟨g, hN' g⟩ x) = _
    rw [hg]
    exact hequiv (τ g) (hτ g).1 hn x
  rw [map_centralizerPerfectCore_subgroupOf_eq_of_le hTX π hπ hker α (fun _ _ => rfl) β hαβ,
    CFSG.Quasithin.map_perfectCore, map_fixAll_normalizerMonoidHom_eq_frame h e δ hδ τ hτ]

end FrameGlue

section Cover

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}

structure MinusAnisoFieldCover
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c))
    (ι : K →+* F) where
  π : anisoNeighbourCore e →* StatedOmega (StatedQuadPlus (r + 1) F)
  surjective : Function.Surjective π
  ker_le : π.ker ≤ center (anisoNeighbourCore e)
  equivariant : ∀ (t : Fin (r + 1) → Kˣ)
    (hN : ((e.symm ((isHypFrame_minus K hn b c).frameHom t) : L) : G) ∈
      normalizer (anisoNeighbourCore e : Set G)) (x : anisoNeighbourCore e),
    π ((anisoNeighbourCore e).normalizerMonoidHom ⟨_, hN⟩ x) =
      (StatedOmega (StatedQuadPlus (r + 1) F)).normalizerMonoidHom
        ⟨diagOmega F (r + 1) (liftParam ι t), diagOmega_mem_normalizer _⟩ (π x)

variable [Finite G] [Finite F] [CharP F 2]
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}

omit [CharP F 2] in
theorem MinusAnisoFieldCover.map_levelCore (A : MinusAnisoFieldCover e ι)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F)
    {J : Finset (Fin (r + 1))} (hJ : 2 ≤ J.card)
    (hUX : minusLevelCore e J ≤ anisoNeighbourCore e) :
    (((minusLevelCore e J).subgroupOf (anisoNeighbourCore e)).map A.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype = siegelBlockGL F J := by
  have hN : ∀ g ∈ modelToG e (frameTorusOf (coordinateQuadMinus (r + 2) K hn b c)
      (minusFrameLeft hn) (minusFrameRight hn) (levelParam J)),
      g ∈ normalizer (anisoNeighbourCore e : Set G) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact mem_normalizer_anisoNeighbourCore_of_mem e hirr (P := levelParam J) (Or.inl hx)
  have h := map_frameCore_eq_of_conjDiag_quot_of_le (isHypFrame_minus K hn b c) e
    ((diagOmega F (r + 1)).comp (liftParamHom ι)) (fun t => diagOmega_mem_normalizer _)
    (P := levelParam J) (X := modelToG e (anisoTorus hn b c)) hN hUX A.π A.surjective A.ker_le
    (fun t _ hN x => A.equivariant t hN x)
  have himg : ((diagOmega F (r + 1)).comp (liftParamHom ι)) ''
      ((levelParam J : Subgroup (Fin (r + 1) → Kˣ)) : Set (Fin (r + 1) → Kˣ)) =
      diagOmega F (r + 1) '' (liftParam ι ''
        ((levelParam J : Subgroup (Fin (r + 1) → Kˣ)) : Set (Fin (r + 1) → Kˣ))) := by
    rw [Set.image_image]
    rfl
  change (((minusLevelCore e J).subgroupOf (anisoNeighbourCore e)).map A.π).map _ = _ at h
  rw [h, himg, perfectCore_statedOmega_inf_centralizer_levelTorus_of_four_le hF ι hK hJ,
    siegelBlockGL_eq_map_omegaLeviSL hF hJ]

omit [Finite G] [Finite F] [CharP F 2] in
theorem MinusAnisoFieldCover.ker_comp_subtype_le (A : MinusAnisoFieldCover e ι) :
    ((StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp A.π).ker ≤
      center (anisoNeighbourCore e) := by
  intro x hx
  apply A.ker_le
  rw [MonoidHom.mem_ker] at hx ⊢
  exact Subtype.val_injective hx

omit [Finite G] [CharP F 2] in
theorem MinusAnisoFieldCover.exists_theta_of_images (A : MinusAnisoFieldCover e ι)
    (hF : 5 ≤ Nat.card F) {U V : Subgroup G} (hUE : U ≤ anisoNeighbourCore e)
    (hVE : V ≤ anisoNeighbourCore e) (hUp : ⁅U, U⁆ = U) (hVp : ⁅V, V⁆ = V) {a : ℕ}
    (ha : a + 3 ≤ r + 1)
    (hU : ((U.subgroupOf (anisoNeighbourCore e)).map A.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      siegelBlockGL F (consecutiveBlock (r + 1) a 2))
    (hV : ((V.subgroupOf (anisoNeighbourCore e)).map A.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      siegelBlockGL F (consecutiveBlock (r + 1) (a + 1) 2)) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = U ∧ (B23 F).map θ = V := by
  set E := anisoNeighbourCore e
  set M := U ⊔ V with hMdef
  have hME : M ≤ E := sup_le hUE hVE
  set π' : E →* GL (Fin (r + 1) ⊕ Fin (r + 1)) F :=
    (StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp A.π
  set ρ : M →* GL (Fin (r + 1) ⊕ Fin (r + 1)) F := π'.comp (Subgroup.inclusion hME)
  have hmap : ∀ B : Subgroup G, B ≤ M →
      (B.subgroupOf M).map ρ =
        ((B.subgroupOf E).map A.π).map (StatedOmega (StatedQuadPlus (r + 1) F)).subtype := by
    intro B hBM
    rw [← map_inclusion_subgroupOf hBM hME, Subgroup.map_map, Subgroup.map_map]
  have hP : (∅ : Finset (Fin (r + 1))) = ∅ := rfl
  refine exists_theta_of_central hF le_sup_left le_sup_right hUp hVp
    (modelTheta_injective a ha ∅) ρ ?_ ?_ ?_ ?_
  · rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self, hmap M le_rfl, hMdef,
      Subgroup.subgroupOf_sup hUE hVE, Subgroup.map_sup, Subgroup.map_sup, hU, hV,
      ← map_conj_flipGL_empty (siegelBlockGL F (consecutiveBlock (r + 1) a 2)),
      ← map_conj_flipGL_empty (siegelBlockGL F (consecutiveBlock (r + 1) (a + 1) 2)),
      ← map_B12_modelTheta a ha ∅, ← map_B23_modelTheta a ha ∅, ← Subgroup.map_sup,
      CFSG.ClassicalInvolution.WeakCT.B12_sup_B23, ← MonoidHom.range_eq_map]
  · intro x hx
    have hx' : Subgroup.inclusion hME x ∈ center E := A.ker_comp_subtype_le hx
    rw [mem_center_iff] at hx' ⊢
    intro y
    have h2 := congrArg Subtype.val (hx' (Subgroup.inclusion hME y))
    exact Subtype.ext h2
  · rw [hmap U le_sup_left, hU, map_B12_modelTheta, map_conj_flipGL_empty]
  · rw [hmap V le_sup_right, hV, map_B23_modelTheta, map_conj_flipGL_empty]

end Cover

section Edge

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem minusLevelCore_le_anisoNeighbourCore_of_param (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 4 ≤ n) (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) β γ)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {i j : Fin (n - 1)} (hij : i ≠ j) {F : Type} [Field F] [Finite F] {ι : K →+* F}
    {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (P : MinusRootFieldParam hn hirr e t ι σ i j) :
    minusLevelCore e ({i, j} : Finset (Fin (n - 1))) ≤ anisoNeighbourCore e := by
  have hn1 : 1 ≤ n := by omega
  have hA := minusLevelCore_le_centralizer_field hset hn hK hq hirr e ht hKt hij hσ1 hσσ hfix P
  have hX : anisoTorus (K := K) hn1 β γ ≤ stabPairsBar (coordinateQuadMinus n K hn1 β γ)
      (minusIndexEquiv n hn1 (.inl i)) (minusIndexEquiv n hn1 (.inr (.inl i)))
      (minusIndexEquiv n hn1 (.inl j)) (minusIndexEquiv n hn1 (.inr (.inl j))) :=
    anisoTorusOf_le_stabPairsBar (anisoCoord_ne hn1) (pairDisjoint_aniso hn1 i).symm
      (pairDisjoint_aniso hn1 j).symm
  exact F4Pilot.le_centralizerPerfectCore (commutator_centralizerPerfectCore _)
    (hA.trans (centralizer_le (UnitaryPilot.modelToG_mono e hX)))

theorem consecutiveBlock_three_one_two :
    consecutiveBlock (2 + 1) 1 2 = ({1, 2} : Finset (Fin (2 + 1))) := by
  decide

theorem exists_theta_minusNode_zero_one_four (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F} {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (hF : 5 ≤ Nat.card F)
    (P₀₁ : MinusRootFieldParam (n := 2 + 2) le_rfl hirr e t ι σ 0 1)
    (P₁₂ : MinusRootFieldParam (n := 2 + 2) le_rfl hirr e t ι σ 1 2)
    (A : MinusAnisoFieldCover (r := 2) e ι) (C₀ : MinusFieldCover (r := 2) e ι 0) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = minusNode C₀ 0 ∧
      (B23 F).map θ = minusNode C₀ 1 := by
  have hF4 : 4 ≤ Nat.card F := by omega
  have h01 := minusLevelCore_le_anisoNeighbourCore_of_param hset le_rfl hKc hq hirr e ht hKt
    (i := 0) (j := 1) (by decide) hσ1 hσσ hfix P₀₁
  have h12 := minusLevelCore_le_anisoNeighbourCore_of_param hset le_rfl hKc hq hirr e ht hKt
    (i := 1) (j := 2) (by decide) hσ1 hσσ hfix P₁₂
  have hU0 : minusNode C₀ 0 = minusLevelCore e (consecutiveBlock (2 + 1) 0 2) :=
    minusNode_of_le C₀ (j := 0) (by simp)
  have hU1 : minusNode C₀ 1 = minusLevelCore e (consecutiveBlock (2 + 1) 1 2) :=
    minusNode_of_le C₀ (j := 1) (by simp)
  have hb0 : consecutiveBlock (2 + 1) 0 2 = ({0, 1} : Finset (Fin (2 + 1))) := by decide
  rw [hU0, hU1]
  have h01' : minusLevelCore e (consecutiveBlock (2 + 1) 0 2) ≤ anisoNeighbourCore e := by
    rw [hb0]
    exact h01
  have h12' : minusLevelCore e (consecutiveBlock (2 + 1) 1 2) ≤ anisoNeighbourCore e := by
    rw [consecutiveBlock_three_one_two]
    exact h12
  have hcb : ∀ a, a + 2 ≤ 2 + 1 → 2 ≤ (consecutiveBlock (2 + 1) a 2).card := fun a ha =>
    (card_consecutiveBlock_two ha).ge
  refine A.exists_theta_of_images hF h01' h12' (commutator_centralizerPerfectCore _)
    (commutator_centralizerPerfectCore _) (a := 0) (by omega)
    (A.map_levelCore hirr hq hF4 (hcb 0 (by omega)) h01')
    (A.map_levelCore hirr hq hF4 (hcb 1 (by omega)) h12')

end Edge

section Inputs

@[expose] def OmegaMinusFourAnisoCoverInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (4 - 1), OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
          (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .field) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
        orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
        Nonempty (MinusAnisoFieldCover (r := 2) e ι)

@[expose] def OmegaMinusFourRootParamOneTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (4 - 1), OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
          (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .field) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
        orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
        Nonempty (MinusRootFieldParam (n := 2 + 2) le_rfl hirr e t ι σ ⟨1, by omega⟩
          ⟨2, by omega⟩)

theorem omegaMinusFourEdgeInput_of_aniso (haniso : OmegaMinusFourAnisoCoverInput)
    (hparam : OmegaMinusFourRootParamInput) (hparam' : OmegaMinusFourRootParamOneTwoInput) :
    OmegaMinusFourEdgeInput := by
  intro G _ _ L hset f K _ _ _ b c hirr hKc hf2 e t ht hKt hrow F _ _ _ ι σ hσ hfix C₀
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf2
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hF5 : 5 ≤ Nat.card F := by
    rw [hF]
    calc 5 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  obtain ⟨A⟩ := haniso G L hset f K b c hirr hKc hf2 e t ht hKt hrow F ι σ hσ hfix
  obtain ⟨P₀₁⟩ := hparam G L hset f K b c hirr hKc hf2 e t ht hKt hrow F ι σ hσ hfix
  obtain ⟨P₁₂⟩ := hparam' G L hset f K b c hirr hKc hf2 e t ht hKt hrow F ι σ hσ hfix
  exact exists_theta_minusNode_zero_one_four hset hKc hq hirr e ht hKt hσ1 hσσ hfix hF5 P₀₁ P₁₂
    A C₀


theorem omegaMinusFourInput_of_inputs_aniso (hswap : OmegaMinusFourSwapRowInput)
    (hcov : OmegaMinusFourCoverInput) (haniso : OmegaMinusFourAnisoCoverInput)
    (hparam : OmegaMinusFourRootParamInput) (hparam' : OmegaMinusFourRootParamOneTwoInput)
    (huniq : OmegaMinusFourUniqueInput) (hend : OmegaMinusFourEndInput) : OmegaMinusFourInput :=
  omegaMinusFourInput_of_inputs_final hswap hcov hparam
    (omegaMinusFourEdgeInput_of_aniso haniso hparam hparam') huniq hend

end Inputs

end CFSG.SeitzReduction.OmegaPilot
