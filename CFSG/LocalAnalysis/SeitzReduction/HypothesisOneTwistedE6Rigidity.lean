module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneHeightRigidity
public import CFSG.LieType.Chevalley.GraphFixedParabolicPointwiseRigidity
public import CFSG.LieType.Chevalley.EvenExceptionalActorCoverage

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem twistedE6_sigma_pow_order {f : ℕ} [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) : σ ^ TwistTag.E6.order = 1 := by
  have : Fintype K := Fintype.ofFinite K
  refine RingEquiv.ext fun x => ?_
  change σ (σ x) = x
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]


theorem borel_conj_mem_heightSeries {τ : Tag} (h' : ℤ) {y : ModGL τ K}
    (hy : y ∈ borelGroup τ K) {x : ModGL τ K} (hx : x ∈ heightSeries τ K h') :
    y * x * y⁻¹ ∈ heightSeries τ K h' :=
  (Subgroup.mem_normalizer_iff.1 ((sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)
    (heightSeries_le_normalizer K h') : borelGroup τ K ≤ _) hy) x).1 hx

theorem mem_graphFixedRootBorel_of_normalizes_fixedHeightSeries {t : TwistTag}
    {σ : K →+* K} (hσ : Function.Surjective σ) {h : ℤ} (h1 : 1 ≤ h)
    (hd : SimpleDiffTail t.tag h) {g : ModGL t.tag K} (hg : g ∈ graphFixedRootGroup t K σ)
    (hN : ∀ h' : ℤ, h ≤ h' → ∀ x ∈ heightSeries t.tag K h' ⊓ twistedFixedGroup t K σ,
      g * x * g⁻¹ ∈ heightSeries t.tag K h') :
    g ∈ graphFixedRootBorel t K σ := by
  classical
  have hg' : g ∈ ⋃ w : relWeylTwist t, graphFixedRootBruhatCell t K σ w := by
    rw [← graphFixedRootGroup_eq_iUnion hσ]
    exact hg
  obtain ⟨⟨w, hwρ⟩, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hw
  have hbB : b ∈ borelGroup t.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).1
  have hbΓ : b ∈ twistedFixedGroup t K σ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).2
  have hb'B : b' ∈ borelGroup t.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb').1).1
  have hb'Γ : b' ∈ twistedFixedGroup t K σ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb').1).2
  set n := canonicalRep (coxeterSystem t.tag) K w with hn
  have hnΓ : n ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hwρ)
  have hnN : ∀ h' : ℤ, h ≤ h' → ∀ x ∈ heightSeries t.tag K h' ⊓ twistedFixedGroup t K σ,
      n * x * n⁻¹ ∈ heightSeries t.tag K h' := by
    intro h' hh x hx
    obtain ⟨hxH, hxΓ⟩ := Subgroup.mem_inf.1 hx
    have e : n * x * n⁻¹ =
        b⁻¹ * ((b * n * b') * (b'⁻¹ * x * b'⁻¹⁻¹) * (b * n * b')⁻¹) * b⁻¹⁻¹ := by
      group
    rw [e]
    refine borel_conj_mem_heightSeries h' (inv_mem hbB) (hN h' hh _ (Subgroup.mem_inf.2
      ⟨borel_conj_mem_heightSeries h' (inv_mem hb'B) hxH, ?_⟩))
    exact mul_mem (mul_mem (inv_mem hb'Γ) hxΓ) (inv_mem (inv_mem hb'Γ))
  have hpos : ∀ γ, IsRoot t.tag γ → h ≤ height γ → 0 < height (w • γ) := by
    intro γ hγ hγh
    rcases CFSG.LieType.Chevalley.IsRoot.height_pos_or_neg (IsRoot.smul hγ w) with hp | hneg
    · exact hp
    · exfalso
      have hOpos : ∀ δ ∈ t.diagramOrbit γ, 0 < height δ := fun δ hδ => by
        rw [t.height_of_mem_diagramOrbit hδ]
        omega
      have hOmem : t.diagramOrbit γ ∈ t.diagramRootOrbits := ⟨γ, hγ, rfl⟩
      obtain ⟨z, hz, hcoord⟩ := exists_orbit_coordinate_element (K := K) σ hOmem hOpos
      obtain ⟨hzO, hzΓ⟩ := Subgroup.mem_inf.1 hz
      have hzH : z ∈ heightSeries t.tag K (height γ) := by
        refine rootSpan_mono (T := {α | IsRoot t.tag α ∧ 0 < height α ∧ height γ ≤ height α})
          (fun δ hδ => ?_) hzO
        exact ⟨t.isRoot_of_mem_diagramOrbit hγ hδ, hOpos δ hδ,
          (t.height_of_mem_diagramOrbit hδ).ge⟩
      have hx := hnN (height γ) hγh z (Subgroup.mem_inf.2 ⟨hzH, hzΓ⟩)
      have hm : n * z * n⁻¹ ∈ rootSpan t.tag K
          ((fun β => w • β) '' (t.diagramOrbit γ : Set (Fin t.tag.rank → ℤ))) := by
        rw [← (canonical_weyl_root_transport t.tag K).1 w _
          (fun β hβ => t.isRoot_of_mem_diagramOrbit hγ hβ)]
        exact ⟨z, hzO, rfl⟩
      have hneg' : n * z * n⁻¹ ∈ negUnipotent t.tag K := by
        refine rootSpan_mono ?_ hm
        rintro _ ⟨β, hβ, rfl⟩
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hβ
        refine ⟨IsRoot.smul (t.isRoot_of_mem_diagramOrbit hγ hβ) w, ?_⟩
        have hcomm : ∀ (k : ℕ) (v : Fin t.tag.rank → ℤ),
            w • permLattice (t.perm ^ k) v = permLattice (t.perm ^ k) (w • v) := by
          intro k
          induction k with
          | zero => intro v; rw [pow_zero]; rfl
          | succ k ih =>
            intro v
            rw [pow_succ', show permLattice (t.perm * t.perm ^ k) v =
                permLattice t.perm (permLattice (t.perm ^ k) v) from rfl,
              (mem_relWeylTwist_iff_smul t).1 hwρ, ih]
            rfl
        show height (w • permLattice (t.perm ^ k) γ) < 0
        rw [hcomm, height_permLattice]
        exact hneg
      have hB : n * z * n⁻¹ ∈ borelGroup t.tag K :=
        Subgroup.mem_sup_right (heightSeries_le_posUnipotent _ hx)
      have h0 := Subgroup.mem_inf.2 ⟨hB, hneg'⟩
      rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, mul_inv_eq_one, mul_eq_left] at h0
      obtain ⟨m, β, hβ⟩ := ((finite_setOf_isRoot t.tag).subset
        fun β (hβ : β ∈ {β | IsRoot t.tag β ∧ 0 < height β}) => hβ.1).fin_embedding
      have hz0 : z = (List.ofFn fun i => pinnedX t.tag K (β i) ((0 : Fin m → K) i)).prod := by
        simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]
        exact h0
      obtain ⟨i, hi⟩ : γ ∈ Set.range β := hβ ▸ ⟨hγ, by omega⟩
      exact ((hcoord β β.injective hβ).2 0 hz0 i).2 (by
        rw [hi]
        exact t.self_mem_diagramOrbit γ) rfl
  have htail : ∀ h' : ℤ, h ≤ h' →
      ∀ γ ∈ {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α ∧ h' ≤ height α},
        w • γ ∈ {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α ∧ h' ≤ height α} := by
    intro h' hh γ hγ
    set S := {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α ∧ h' ≤ height α} with hS
    have hle : rootSpan t.tag K ((fun β => w • β) '' S) ⊓ twistedFixedGroup t K σ ≤
        rootSpan t.tag K S ⊓ twistedFixedGroup t K σ := by
      intro y hy
      obtain ⟨hyS, hyΓ⟩ := Subgroup.mem_inf.1 hy
      rw [← (canonical_weyl_root_transport t.tag K).1 w S (fun β hβ => hβ.1)] at hyS
      obtain ⟨x, hx, rfl⟩ := hyS
      change n * x * n⁻¹ ∈ _
      change n * x * n⁻¹ ∈ twistedFixedGroup t K σ at hyΓ
      have hxΓ : x ∈ twistedFixedGroup t K σ := by
        have e : x = n⁻¹ * (n * x * n⁻¹) * n := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hnΓ) hyΓ) hnΓ
      exact Subgroup.mem_inf.2 ⟨hnN h' hh x (Subgroup.mem_inf.2 ⟨hx, hxΓ⟩), hyΓ⟩
    have hSpos : ∀ β ∈ (fun β => w • β) '' S, IsRoot t.tag β ∧ 0 < height β := by
      rintro _ ⟨β, hβ, rfl⟩
      exact ⟨IsRoot.smul hβ.1 w, hpos β hβ.1 (hh.trans hβ.2.2)⟩
    have hSρ : ∀ β ∈ (fun β => w • β) '' S, permLattice t.perm β ∈ (fun β => w • β) '' S := by
      rintro _ ⟨β, hβ, rfl⟩
      refine ⟨permLattice t.perm β, ⟨hβ.1.permLattice t.cartan_perm, ?_, ?_⟩,
        (mem_relWeylTwist_iff_smul t).1 hwρ β⟩
      · rw [height_permLattice]
        exact hβ.2.1
      · rw [height_permLattice]
        exact hβ.2.2
    exact subset_of_rootSpan_inf_le σ hSpos hSρ (fun β hβ => ⟨hβ.1, hβ.2.1⟩)
      heightSeriesSet_closed hle ⟨γ, hγ, rfl⟩
  have hht : ∀ γ, IsRoot t.tag γ → h ≤ height γ → height (w • γ) = height γ := by
    intro γ hγ hγh
    have hge := (htail (height γ) hγh γ ⟨hγ, by omega, le_rfl⟩).2.2
    by_contra hne
    have hgt : height γ + 1 ≤ height (w • γ) := by omega
    have hfin : {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α ∧
        height γ + 1 ≤ height α}.Finite :=
      (finite_setOf_isRoot t.tag).subset fun β hβ => hβ.1
    have hmaps : Set.MapsTo (fun β => w • β) {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧
        0 < height α ∧ height γ + 1 ≤ height α} {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧
        0 < height α ∧ height γ + 1 ≤ height α} := fun β hβ => htail _ (by omega) β hβ
    have hinj : Set.InjOn (fun β => w • β) {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧
        0 < height α ∧ height γ + 1 ≤ height α} := fun β _ γ' _ h => smul_left_cancel w h
    have hsurj := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj |>.surjOn
    obtain ⟨β, hβ, hβγ⟩ := hsurj ⟨IsRoot.smul hγ w, by omega, hgt⟩
    have hβγ' := smul_left_cancel w hβγ
    rw [hβγ'] at hβ
    exact absurd hβ.2.2 (by omega)
  have hw1 : w = 1 := by
    refine eq_one_of_forall_height_pos fun i => ?_
    obtain ⟨γ, δ, hγ, hδ, hγh, hδh, he⟩ := hd i
    rw [he, smul_sub, height_sub, hht γ hγ hγh, hht δ hδ hδh, ← height_sub, ← he,
      height_single]
    exact one_pos
  rw [hn, hw1, canonicalRep_one, mul_one]
  exact mul_mem hb hb'

theorem exists_eq_conj_of_mem_fixedActors_of_fix_fixedHeightSeries {t : TwistTag}
    (σ : K ≃+* K) (hσ : σ ^ t.order = 1) {h : ℤ} (h1 : 1 ≤ h) (hd : SimpleDiffTail t.tag h)
    {φ : MulAut (graphFixedRootGroup t K σ.toRingHom)}
    (hφ : φ ∈ fixedDiagonalFieldActors t K σ)
    (hfix : ∀ x : graphFixedRootGroup t K σ.toRingHom,
      (x : ModGL t.tag K) ∈ heightSeries t.tag K h → φ x = x) :
    ∃ u ∈ graphFixedPosUnipotent t K σ.toRingHom,
      ∃ hu : u ∈ graphFixedRootGroup t K σ.toRingHom, φ = MulAut.conj ⟨u, hu⟩ ∧
        ∀ x ∈ heightSeries t.tag K h ⊓ twistedFixedGroup t K σ.toRingHom, u * x = x * u := by
  classical
  set Th : Set (Fin t.tag.rank → ℤ) := {α | IsRoot t.tag α ∧ 0 < height α ∧ h ≤ height α}
    with hTh
  have hThρ : ∀ α ∈ Th, permLattice t.perm α ∈ Th := fun α hα =>
    ⟨hα.1.permLattice t.cartan_perm, by rw [height_permLattice]; exact hα.2.1,
      by rw [height_permLattice]; exact hα.2.2⟩
  have hQC : ∀ x ∈ heightSeries t.tag K h ⊓ twistedFixedGroup t K σ.toRingHom,
      x ∈ graphFixedRootGroup t K σ.toRingHom := fun x hx =>
    graphFixedPosUnipotent_le_graphFixedRootGroup t K _ (Subgroup.mem_inf.2
      ⟨heightSeries_le_posUnipotent h (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩)
  obtain ⟨g, hg, a, ha, δ, hδσ, hα⟩ := ((Chevalley_diagonal_field_actor_data.2 t K σ).1 φ).1 hφ
  have hδ : ∀ c, δ (σ.toRingHom c) = σ.toRingHom (δ c) := fun c =>
    congrArg (fun f : K ≃+* K => f c) hδσ
  have hfix' : ∀ x ∈ heightSeries t.tag K h ⊓ twistedFixedGroup t K σ.toRingHom,
      g * diagFieldAut t.tag a δ x * g⁻¹ = x := by
    intro x hx
    have h1 := congrArg Subtype.val (hfix ⟨x, hQC x hx⟩ (Subgroup.mem_inf.1 hx).1)
    rw [hα] at h1
    rw [diagFieldAut_apply]
    simpa only [mul_assoc] using h1
  have hgN : ∀ h' : ℤ, h ≤ h' → ∀ x ∈ heightSeries t.tag K h' ⊓ twistedFixedGroup t K σ.toRingHom,
      g * x * g⁻¹ ∈ heightSeries t.tag K h' := by
    intro h' hh x hx
    have hle : heightSeries t.tag K h' ≤ heightSeries t.tag K h :=
      iSup₂_le fun α hα => le_iSup₂_of_le α ⟨hα.1, hα.2.1, hh.trans hα.2.2⟩ le_rfl
    have hN := mem_normalizer_of_fixes
      (H := heightSeries t.tag K h' ⊓ twistedFixedGroup t K σ.toRingHom)
      (map_diagFieldAut_rootSpan_inf ha hδ fun γ hγ => hγ.1)
      (fun y hy => hfix' y (Subgroup.mem_inf.2 ⟨hle (Subgroup.mem_inf.1 hy).1,
        (Subgroup.mem_inf.1 hy).2⟩))
    exact (Subgroup.mem_inf.1 ((Subgroup.mem_normalizer_iff.1 hN x).1 hx)).1
  have hgB1 := mem_graphFixedRootBorel_of_normalizes_fixedHeightSeries σ.surjective h1 hd hg hgN
  have hgB' : g ∈ (borelGroup t.tag K : Set (ModGL t.tag K)) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hgB1).1).1
  rw [(triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.1] at hgB'
  obtain ⟨u, hu, s, hs, rfl⟩ := hgB'
  beta_reduce at hg hα hfix'
  obtain ⟨e, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hs
  set c := e * a with hc
  have hdc : rootDiagUnit t.tag e * rootDiagUnit t.tag a = rootDiagUnit t.tag c := by
    rw [hc, rootDiagUnit_mul]
  have hkey : ∀ x ∈ heightSeries t.tag K h ⊓ twistedFixedGroup t K σ.toRingHom,
      u * (rootDiagUnit t.tag c * Units.map (entrywiseHom δ.toRingHom) x *
        (rootDiagUnit t.tag c)⁻¹) * u⁻¹ = x := by
    intro x hx
    refine Eq.trans ?_ (hfix' x hx)
    rw [diagFieldAut_apply, ← hdc]
    group
  have hzQ : ∀ w ∈ relWeylTwist t, ∀ a', (∀ i ∈ t.orbit a',
      w • (Pi.single i 1 : Fin t.tag.rank → ℤ) ∈ Th) → ∀ y : orbitField t K σ.toRingHom a',
      canonicalRep (coxeterSystem t.tag) K w * (orbitX t K σ.toRingHom a' y : ModGL t.tag K) *
        (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
          heightSeries t.tag K h ⊓ twistedFixedGroup t K σ.toRingHom := by
    intro w hw a' hsub y
    obtain ⟨h1', h2'⟩ := Subgroup.mem_inf.1 (conj_orbitX_mem hw a' y)
    refine Subgroup.mem_inf.2 ⟨rootSpan_mono (T := Th) ?_ h1', h2'⟩
    rintro _ ⟨i, hi, rfl⟩
    exact hsub i hi
  have hconjO : ∀ w ∈ relWeylTwist t, ∀ a', (∀ i ∈ t.orbit a',
      w • (Pi.single i 1 : Fin t.tag.rank → ℤ) ∈ Th) → ∀ {y z : ModGL t.tag K},
      y ∈ rootSpan t.tag K
        ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a')) →
      z ∈ rootSpan t.tag K
        ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a')) →
      u * y * u⁻¹ = z → y = z := by
    intro w hw a' hsub y z hy hz hyz
    obtain ⟨i₀, hi₀⟩ := t.orbit_nonempty a'
    refine eq_of_conj_eq_of_mem_rootSpan (s := height (w • (Pi.single i₀ 1 :
      Fin t.tag.rank → ℤ))) (fun γ hγ => ?_) (hsub i₀ hi₀).2.1
      (fun γ hγ γ' hγ' p q hp hq => ?_) hu hy hz hyz
    · obtain ⟨i, hi, rfl⟩ := hγ
      exact ⟨(hsub i hi).1, height_eq_of_mem_orbitImage hw hi₀ (Finset.mem_image_of_mem _ hi)⟩
    · obtain ⟨i, hi, rfl⟩ := hγ
      obtain ⟨j, hj, rfl⟩ := hγ'
      exact not_isRoot_nsmul_add_nsmul_of_mem_orbitImage w a' (Finset.mem_image_of_mem _ hi)
        (Finset.mem_image_of_mem _ hj) hp hq
  have hchar : ∀ γ ∈ Th, rootChar c γ = 1 := by
    intro γ hγ
    obtain ⟨w, hw, a', hOγ⟩ := t.exists_diagramOrbit_eq hγ.1
    have hsub : ∀ i ∈ t.orbit a', w • (Pi.single i 1 : Fin t.tag.rank → ℤ) ∈ Th := fun i hi =>
      diagramOrbit_subset hThρ hγ (by rw [hOγ]; exact Finset.mem_image_of_mem _ hi)
    set n := canonicalRep (coxeterSystem t.tag) K w with hn
    set z := n * (orbitX t K σ.toRingHom a' 1 : ModGL t.tag K) * n⁻¹ with hz
    have hzQ' := hzQ w hw a' hsub 1
    have h1' : (⟨δ ((1 : orbitField t K σ.toRingHom a') : K),
        map_mem_orbitField hδ (1 : orbitField t K σ.toRingHom a').2⟩ :
          orbitField t K σ.toRingHom a') = 1 := Subtype.ext (by simp)
    have hzfix : Units.map (entrywiseHom δ.toRingHom) z = z := by
      rw [hz, hn, units_map_entrywiseHom_conj_orbitX hδ, h1']
    have hzO := (Subgroup.mem_inf.1 (conj_orbitX_mem (K := K) (σ := σ.toRingHom) hw a' 1)).1
    have hyO : rootDiagUnit t.tag c * z * (rootDiagUnit t.tag c)⁻¹ ∈ rootSpan t.tag K
        ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a')) := by
      have hmap := map_rootSpan_of_forall (f := (MulAut.conj (rootDiagUnit t.tag c)).toMonoidHom)
        (S := (fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a'))
        fun β hβ => by
          obtain ⟨i, hi, rfl⟩ := hβ
          exact map_conj_rootDiagUnit_rootSubgroup c (IsRoot.smul (isRoot_single t.tag i) w)
      rw [← hmap]
      exact ⟨z, hzO, rfl⟩
    have h1 : u * (rootDiagUnit t.tag c * z * (rootDiagUnit t.tag c)⁻¹) * u⁻¹ = z := by
      have := hkey z hzQ'
      rwa [hzfix] at this
    have hyz := hconjO w hw a' hsub hyO hzO h1
    obtain ⟨m, ord, hord⟩ := ((finite_setOf_isRoot t.tag).subset
      fun β (hβ : β ∈ {β | IsRoot t.tag β ∧ 0 < height β}) => hβ.1).fin_embedding
    have hordpos : ∀ i, IsRoot t.tag (ord i) ∧ 0 < height (ord i) := fun i => by
      have : ord i ∈ {β | IsRoot t.tag β ∧ 0 < height β} := hord ▸ Set.mem_range_self i
      exact this
    have hpos : ∀ i ∈ t.orbit a', 0 < height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) :=
      fun i hi => (hsub i hi).2.1
    obtain ⟨c₀, hc₀, hsupp⟩ := exists_coordinates_conj_orbitXProd (K := K) w a' hpos ord
      ord.injective hord
    have hz1 : (orbitX t K σ.toRingHom a' 1 : ModGL t.tag K) = orbitXProd t a' fun _ => 1 := by
      rw [coe_orbitX_eq_orbitXProd]
      refine orbitXProd_congr t fun j hj => ?_
      obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hj
      rw [orbitParam_pow t σ.toRingHom _ hk]
      simp
    have hzprod : z = (List.ofFn fun i => pinnedX t.tag K (ord i) (c₀ i)).prod := by
      rw [hz, hz1, ← hc₀]
    have hyprod : rootDiagUnit t.tag c * z * (rootDiagUnit t.tag c)⁻¹ =
        (List.ofFn fun i => pinnedX t.tag K (ord i) ((rootChar c (ord i) : K) * c₀ i)).prod := by
      rw [hzprod, rootDiagUnit_conj_list_prod c ord (fun i => (hordpos i).1) c₀]
    have hcc := (positive_root_product_injectivity t.tag K ord ord.injective hordpos).2
      (hyprod.symm.trans (hyz.trans hzprod))
    obtain ⟨i₀, hi₀⟩ : γ ∈ Set.range ord := hord ▸ ⟨hγ.1, hγ.2.1⟩
    have hne : c₀ i₀ ≠ 0 := (hsupp i₀).2 (by
      rw [hi₀, ← hOγ]
      exact t.self_mem_diagramOrbit γ)
    have h2 : (rootChar c (ord i₀) : K) * c₀ i₀ = c₀ i₀ := congrFun hcc i₀
    rw [hi₀] at h2
    have h3 : ((rootChar c γ : K) - 1) * c₀ i₀ = 0 := by linear_combination h2
    exact Units.ext (by
      rw [Units.val_one]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne))
  have hc1 : c = 1 := funext fun i => by
    obtain ⟨γ, γ', hγ, hγ', hγh, hγ'h, he⟩ := hd i
    have e : γ = Pi.single i 1 + γ' := by rw [he, sub_add_cancel]
    have h1 := hchar γ ⟨hγ, by omega, hγh⟩
    rw [e, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_add, rootChar_single,
      hchar γ' ⟨hγ', by omega, hγ'h⟩, mul_one] at h1
    exact h1
  have hdc1 : rootDiagUnit t.tag c = 1 := by rw [hc1, rootDiagUnit_one]
  obtain ⟨α₀, hα₀, hρα₀⟩ : ∃ α ∈ Th, permLattice t.perm α ≠ α := by
    obtain ⟨i, hi⟩ : ∃ i, t.perm i ≠ i := by cases t <;> decide
    obtain ⟨γ, γ', hγ, hγ', hγh, hγ'h, he⟩ := hd i
    by_contra hcon
    push Not at hcon
    have h1 := hcon γ ⟨hγ, by omega, hγh⟩
    have h2 := hcon γ' ⟨hγ', by omega, hγ'h⟩
    have h3 : permLattice t.perm (Pi.single i 1 : Fin t.tag.rank → ℤ) = Pi.single i 1 := by
      rw [he, show permLattice t.perm (γ - γ') = permLattice t.perm γ - permLattice t.perm γ'
        from rfl, h1, h2]
    rw [permLattice_single] at h3
    exact hi (t.single_one_injective h3)
  have hδ1 : δ = 1 := by
    obtain ⟨w, hw, a', hOα⟩ := t.exists_diagramOrbit_eq hα₀.1
    have hcard : (t.orbit a').card = t.order := by
      rcases t.card_orbit a' with h1 | h1
      · exfalso
        have hcard : (t.diagramOrbit α₀).card = 1 := by rw [hOα, t.card_image_smul_single, h1]
        have hmem1 := t.self_mem_diagramOrbit α₀
        have hmem2 : permLattice t.perm α₀ ∈ t.diagramOrbit α₀ :=
          t.mem_diagramOrbit.2 ⟨t.perm, Subgroup.mem_zpowers _, rfl⟩
        obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hcard
        rw [hx] at hmem1 hmem2
        exact hρα₀ ((Finset.mem_singleton.1 hmem2).trans (Finset.mem_singleton.1 hmem1).symm)
      · exact h1
    have hsub : ∀ i ∈ t.orbit a', w • (Pi.single i 1 : Fin t.tag.rank → ℤ) ∈ Th := fun i hi =>
      diagramOrbit_subset hThρ hα₀ (by rw [hOα]; exact Finset.mem_image_of_mem _ hi)
    have hfull : ∀ x : K, x ∈ orbitField t K σ.toRingHom a' := fun x => by
      rw [mem_orbitField, hcard]
      have h1 : σ.toRingHom ^ t.order = (σ ^ t.order).toRingHom := by
        induction t.order with
        | zero => rfl
        | succ k ih => rw [pow_succ, pow_succ, ih]; rfl
      rw [h1, hσ]
      rfl
    refine RingEquiv.ext fun x => ?_
    have h1 := hkey _ (hzQ w hw a' hsub ⟨x, hfull x⟩)
    rw [hdc1, one_mul, inv_one, mul_one, units_map_entrywiseHom_conj_orbitX hδ] at h1
    have h2 := hconjO w hw a' hsub
      (Subgroup.mem_inf.1 (conj_orbitX_mem (K := K) (σ := σ.toRingHom) hw a' _)).1
      (Subgroup.mem_inf.1 (conj_orbitX_mem (K := K) (σ := σ.toRingHom) hw a' _)).1 h1
    have h3 : (orbitX t K σ.toRingHom a' ⟨δ x, map_mem_orbitField hδ (hfull x)⟩ :
        ModGL t.tag K) = orbitX t K σ.toRingHom a' ⟨x, hfull x⟩ :=
      mul_left_cancel (mul_right_cancel h2)
    have h4 := orbitX_injective σ.toRingHom a' (Subtype.ext h3)
    exact congrArg Subtype.val h4
  subst hδ1
  have heb : rootDiagUnit t.tag e * rootDiagUnit t.tag a = 1 := by rw [hdc, hdc1]
  have hαu : ∀ x : graphFixedRootGroup t K σ.toRingHom, (φ x : ModGL t.tag K) = u * x * u⁻¹ := by
    intro x
    rw [hα, units_map_entrywiseHom_one_ringEquiv]
    calc u * rootDiagUnit t.tag e * rootDiagUnit t.tag a * x * (rootDiagUnit t.tag a)⁻¹ *
          (u * rootDiagUnit t.tag e)⁻¹ =
        u * (rootDiagUnit t.tag e * rootDiagUnit t.tag a) * x *
          (rootDiagUnit t.tag e * rootDiagUnit t.tag a)⁻¹ * u⁻¹ := by group
      _ = u * x * u⁻¹ := by rw [heb]; group
  have huΓ : u ∈ twistedFixedGroup t K σ.toRingHom := by
    refine (mem_twistedFixedGroup_iff_twistHom t K _).2 ⟨posUnipotent_le_adjointGroup hu, ?_⟩
    have hgF := ((mem_twistedFixedGroup_iff_twistHom t K _).1
      (graphFixedRootGroup_le t K _ hg)).2
    have hug : u = u * rootDiagUnit t.tag e * rootDiagUnit t.tag a := by
      rw [mul_assoc, heb, mul_one]
    rw [hug, map_mul, hgF, twistHom_rootDiagUnit ha]
  have huU : u ∈ graphFixedPosUnipotent t K σ.toRingHom := Subgroup.mem_inf.2 ⟨hu, huΓ⟩
  have huC0 : u ∈ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup t K _ huU
  refine ⟨u, huU, huC0, MulEquiv.ext fun x => Subtype.ext ?_, fun x hx => ?_⟩
  · rw [hαu]
    rfl
  · have h1 := congrArg Subtype.val (hfix ⟨x, hQC x hx⟩ (Subgroup.mem_inf.1 hx).1)
    rw [hαu] at h1
    calc u * x = u * x * u⁻¹ * u := by group
      _ = x * u := by rw [show u * x * u⁻¹ = x from h1]

theorem exists_eq_conj_of_fix_fixedHeightSeries_twistedE6 {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {h : ℤ}
    (h1 : 1 ≤ h) (h7 : h ≤ 7) (φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hfix : ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (x : ModGL TwistTag.E6.tag K) ∈ heightSeries TwistTag.E6.tag K h → φ x = x) :
    ∃ u ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom,
      ∃ hu : u ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom, φ = MulAut.conj ⟨u, hu⟩ ∧
        ∀ x ∈ heightSeries TwistTag.E6.tag K h ⊓ twistedFixedGroup TwistTag.E6 K σ.toRingHom,
          u * x = x * u := by
  have hA := EvenExceptionalActorCoverage.fixedDiagonalFieldActors_E6_eq_top hf hK σ hσ
  exact exists_eq_conj_of_mem_fixedActors_of_fix_fixedHeightSeries σ
    (twistedE6_sigma_pow_order hK hσ) h1 (simpleDiffTail_of_le (τ := .E6) h7)
    (hA ▸ Subgroup.mem_top φ) hfix

end CFSG.SeitzReduction
