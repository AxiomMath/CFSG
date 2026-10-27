module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY3Gen
public import CFSG.ClassicalInvolution.Q3.Q3AMLYShape
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuTab
public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSU3

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open scoped MatrixGroups commutatorElement

section Thin


variable {G : Type} [Group G] [Finite G]

theorem not_subset_center_of_isUniqueInvolution [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {M : Subgroup G} {a : G} (ha : IsUniqueInvolution M a) :
    ¬ ({a} : Set G) ⊆ Subgroup.center G := by
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
    · exact h'
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top x) y).symm
  exact fun hs => ha.ne_one (by
    have h1 : a ∈ Subgroup.center G := hs (Set.mem_singleton a)
    rwa [hZ, Subgroup.mem_bot] at h1)

theorem natCard_layerQuot_lt [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t) :
    Nat.card (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) <
      Nat.card G :=
  lt_of_le_of_lt (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective)
    (card_centralizingLayer_lt _
      (not_subset_center_of_isUniqueInvolution h.nonabelian h.std.hz))

theorem noTriangleAtEdge_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K J : Subgroup G}
    (hN : NoTriangleAtEdge Ω K J) (n : G) : NoTriangleAtEdge Ω (conjSub n K) (conjSub n J) := by
  intro K' hK' hJ'
  have h1 : conjSub n⁻¹ K' ∈ omegaNbr Ω K := by
    have h' := omegaNbr_conj hΩ hK' n⁻¹
    rwa [conjSub_inv_conjSub] at h'
  have h2 : conjSub n⁻¹ K' ∈ omegaNbr Ω J := by
    have h' := omegaNbr_conj hΩ hJ' n⁻¹
    rwa [conjSub_inv_conjSub] at h'
  exact hN _ h1 h2

theorem exists_uniform_of_layer {ι : Type} {Ω : Set (Subgroup G)} {M : Subgroup G} {a : G}
    (D₃ : LieSystemData3 ι
      (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a)) (layerFam Ω M a))
    (i₁ : ι) (hone : ∀ i, i = i₁) :
    ∃ D : LieSystemDataU 3 1 (Fin 1)
      (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a)) (layerFam Ω M a),
      D.kind 0 = D₃.kind i₁ :=
  ⟨{ kind := fun _ => D₃.kind i₁
     valid := fun _ => by
       rcases D₃.valid i₁ with ⟨t, n, ht, hadm, hc⟩ | hc | hc
       · exact Or.inl ⟨t, n, 1, ht, hadm, Or.inl rfl, hc⟩
       · exact Or.inr ⟨by norm_num, Or.inl hc⟩
       · exact Or.inr ⟨by norm_num, Or.inr hc⟩
     hom := fun _ => D₃.hom i₁
     ker_le_center := fun _ => D₃.ker_le_center i₁
     commute := fun i j hij => absurd (Subsingleton.elim i j) hij
     generate := by
       rw [← D₃.generate]
       refine le_antisymm (iSup_le fun _ => le_iSup (fun j => (D₃.hom j).range) i₁)
         (iSup_le fun j => ?_)
       rw [hone j]
       exact le_iSup (fun _ : Fin 1 => (D₃.hom i₁).range) 0
     fundamental := fun L hL => by
       obtain ⟨i, R', hR, e⟩ := D₃.fundamental L hL
       obtain rfl := hone i
       exact ⟨0, R', hR, e⟩
     meets := fun _ => D₃.meets i₁
     card_eq := fun _ => D₃.card_eq }, rfl⟩

theorem compIs_psl3 {c : Q3.CompData} (hc : c = Q3.CompData.model .PSL 3) :
    CompIs 3 1 c .PSL 3 :=
  ⟨1, Or.inl rfl, trivial, ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩, hc⟩

theorem compIs_psu3 {c : Q3.CompData} (hc : c = Q3.CompData.model .PSU 3) :
    CompIs 3 1 c .PSU 3 :=
  ⟨1, Or.inl rfl, trivial, Q3PP.statedLieAdmissible_psu3, hc⟩

theorem compIs_g2 {c : Q3.CompData} (hc : c = Q3.CompData.model .G2 0) : CompIs 3 1 c .G2 0 :=
  ⟨1, Or.inl rfl, trivial, ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩, hc⟩

theorem compIs_d4 {c : Q3.CompData} (hc : c = Q3.CompData.model .trialityD4 0) :
    CompIs 3 1 c .trialityD4 0 :=
  ⟨1, Or.inl rfl, trivial, ⟨Nat.prime_three, le_rfl, rfl⟩, hc⟩

theorem layer_nontrivial [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J) :
    Nontrivial (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) := by
  have hno := layerFam_noCommute h hint hN
  obtain ⟨L₀, hL₀⟩ := (layerFam_inClass3 h hint h.std.stand.mem h.std.hz).nonempty
  by_contra hcon
  rw [not_nontrivial_iff_subsingleton] at hcon
  exact hno L₀ hL₀ L₀ hL₀ (fun a _ b _ => Subsingleton.elim _ _)

theorem layer_transitive [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J) :
    ∀ K' ∈ layerFam Ω K z, ∀ L' ∈ layerFam Ω K z,
      ∃ g : ↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z),
        conjSub g K' = L' := by
  have hstd := h.std
  have hih : IH8T 3 1 (Nat.card G) := hstd.stand.ih
  have hGen := genSection_layerFam h hint hstd.stand.mem hstd.hz
  have hno := layerFam_noCommute h hint hN
  have hlt := natCard_layerQuot_lt h
  intro K' hK' L' hL'
  by_contra hcon
  push Not at hcon
  exact hno K' hK' L' hL' (hih.thm4 (by norm_num) (by norm_num) _ hlt _ hGen.modU hGen.oddCore
    hGen.aEmpty K' hK' L' hL' (fun ⟨g, hg⟩ => hcon g hg))

theorem layer_isSimple_of_T6 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J)
    (D : LieSystemDataU 3 1 (Fin 1)
      (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) (layerFam Ω K z))
    {t' : CFSG.Assembly.LowTwoRank.StatedLieTag} {k : ℕ}
    (htag : (t' = .PSL ∧ k = 3) ∨ (t' = .PSU ∧ k = 3) ∨ (t' = .G2 ∧ k = 0) ∨
      (t' = .trialityD4 ∧ k = 0))
    (hc : CompIs 3 1 (D.kind 0) t' k) :
    IsSimpleGroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) := by
  have hstd := h.std
  have hGen := genSection_layerFam h hint hstd.stand.mem hstd.hz
  have hconj : ConjInvariant (layerFam Ω K z) :=
    (layerFam_inClass3 h hint hstd.stand.mem hstd.hz).conjInvariant
  have := layer_nontrivial h hint hN
  obtain ⟨e, he, hft, hadm, hc'⟩ := hc
  exact Q3T6.isSimpleGroup_of_systemU (by norm_num) D 0 hconj htag hft hadm he hc'
    hGen.oddCore

theorem layer_isSimple_of_m11 {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
    (D : LieSystemDataU 3 1 (Fin 1)
      (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) (layerFam Ω K z))
    (hc : D.kind 0 = Q3.CompData.m11) :
    IsSimpleGroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) := by
  have hsurj : Function.Surjective (castHom hc (D.hom 0)) := by
    have h' := Q3T6.lieSystemDataU_surjective_hom D 0
    rw [← MonoidHom.range_eq_top] at h' ⊢
    rw [range_castHom]
    exact h'
  have hinj : Function.Injective (castHom hc (D.hom 0)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact (castHom_ker_le_center hc (D.hom 0) (D.ker_le_center 0)).trans
      (Q3.center_m11_eq_bot Q3.m11Facts).le
  have : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 := Q3.m11Facts.1
  exact (MulEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm.isSimpleGroup

theorem thinY_of_top [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z)
    (hTop : (⊤ : Subgroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z))) ∈
      layerFam Ω K z) : ThinY Ω K z := by
  classical
  have hstd := h.std
  have hK : K ∈ Ω := hstd.stand.mem
  have hz : IsUniqueInvolution K z := hstd.hz
  have hGen := genSection_layerFam h hint hK hz
  have hP : Q3CL.PartIHypG (layerFam Ω K z) := ⟨hGen.hyp, hGen.cls, hGen.aEmpty⟩
  obtain ⟨Sb⟩ : Nonempty (Sylow 2 (↥(nbrLayer Ω K z) ⧸
      classicalInvolutionOddCore ↥(nbrLayer Ω K z))) := inferInstance
  obtain ⟨η, hη, hinv⟩ := exists_invariant_mem_etaSet hGen.hyp Sb
  have hηG : η ∈ etaG (layerFam Ω K z) := ⟨Sb, hη, hinv⟩
  have hW' : (⨆ U ∈ η, U) ∈ CFSG.ClassicalInvolution.Asc77.WSet (layerFam Ω K z) :=
    ⟨η, hηG, rfl⟩
  have hcard := nbrLayer_exact_images h hint hK hz
  have hcard24 : ∀ A ∈ layerFam Ω K z, Nat.card A = 24 := by
    intro A hA
    obtain ⟨N, hN, rfl⟩ := exists_of_mem_layerFam hA
    exact hcard N hN
  have h24 : Nat.card (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) =
      24 := by
    have h' := hcard24 _ hTop
    rwa [Subgroup.card_top] at h'
  have hall : ∀ A ∈ layerFam Ω K z, A = ⊤ := fun A hA =>
    Subgroup.eq_top_of_card_eq A (by rw [hcard24 A hA, h24])
  refine ⟨_, hW', Q3T6.Mu.muIsoZ2_of_shape hP hW' ⟨⊤, hTop⟩ ?_⟩
  intro A hA
  refine Set.eq_empty_iff_forall_notMem.mpr fun J' hJ' => hJ'.2.1 ?_
  rw [hall J' hJ'.1, hall A hA]

theorem thinY_of_uniform [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J)
    (D : LieSystemDataU 3 1 (Fin 1)
      (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) (layerFam Ω K z))
    (hD : CompIs 3 1 (D.kind 0) .PSL 3 ∨ D.kind 0 = Q3.CompData.m11) : ThinY Ω K z := by
  classical
  have hstd := h.std
  have hK : K ∈ Ω := hstd.stand.mem
  have hz : IsUniqueInvolution K z := hstd.hz
  have hih : IH8T 3 1 (Nat.card G) := hstd.stand.ih
  have hGen := genSection_layerFam h hint hK hz
  obtain ⟨L₀, hL₀⟩ := (layerFam_inClass3 h hint hK hz).nonempty
  have hlt := natCard_layerQuot_lt h
  have hsimple : IsSimpleGroup
      (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) := by
    rcases hD with hc | hc
    · exact layer_isSimple_of_T6 h hint hN D (Or.inl ⟨rfl, rfl⟩) hc
    · exact layer_isSimple_of_m11 D hc
  have htrans := layer_transitive h hint hN
  obtain ⟨Sb⟩ : Nonempty (Sylow 2 (↥(nbrLayer Ω K z) ⧸
      classicalInvolutionOddCore ↥(nbrLayer Ω K z))) := inferInstance
  obtain ⟨η, hη, hinv⟩ := exists_invariant_mem_etaSet hGen.hyp Sb
  have hηG : η ∈ etaG (layerFam Ω K z) := ⟨Sb, hη, hinv⟩
  have hW' : (⨆ U ∈ η, U) ∈ CFSG.ClassicalInvolution.Asc77.WSet (layerFam Ω K z) :=
    ⟨η, hηG, rfl⟩
  have hrows := hih.muTable (by norm_num) (by norm_num)
    (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) hlt _ hGen.modU
    hGen.aEmpty ⟨L₀, hL₀⟩ htrans _ hW'
  refine ⟨_, hW', hrows.1.mpr ?_⟩
  have hpi : piSign 3 1 = false := by decide
  rw [hpi]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases hD with hc | hc
  · exact Or.inl ⟨Q3T8.omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hc⟩
  · exact Or.inr ⟨by norm_num, Q3T8.omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hc⟩

theorem false_of_thinY_of_uniform_s3 [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (h : BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z)
    (hN : NoTriangleAtEdge Ω K J) (hthin : ThinY Ω K z)
    (D : LieSystemDataU 3 1 (Fin 1)
      (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) (layerFam Ω K z))
    {t' : CFSG.Assembly.LowTwoRank.StatedLieTag} {k : ℕ}
    (htag : (t' = .PSU ∧ k = 3) ∨ (t' = .G2 ∧ k = 0) ∨ (t' = .trialityD4 ∧ k = 0))
    (hc : CompIs 3 1 (D.kind 0) t' k) : False := by
  classical
  have hstd := h.std
  have hK : K ∈ Ω := hstd.stand.mem
  have hz : IsUniqueInvolution K z := hstd.hz
  have hih : IH8T 3 1 (Nat.card G) := hstd.stand.ih
  have hGen := genSection_layerFam h hint hK hz
  obtain ⟨L₀, hL₀⟩ := (layerFam_inClass3 h hint hK hz).nonempty
  have hlt := natCard_layerQuot_lt h
  have hsimple : IsSimpleGroup
      (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) :=
    layer_isSimple_of_T6 h hint hN D (Or.inr htag) hc
  have htrans := layer_transitive h hint hN
  obtain ⟨W', hW', hZ2⟩ := hthin
  have hrows := hih.muTable (by norm_num) (by norm_num)
    (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) hlt _ hGen.modU
    hGen.aEmpty ⟨L₀, hL₀⟩ htrans W' hW'
  have hS3 : MuIsoS3 (layerFam Ω K z) W' := by
    refine hrows.2.1.mpr ?_
    have hpi : piSign 3 1 = false := by decide
    rw [hpi]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨Q3T8.omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hc⟩
    · exact Or.inr (Or.inl ⟨Q3T8.omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hc⟩)
    · exact Or.inr (Or.inr ⟨Q3T8.omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hc⟩)
  exact Q3T8.Asc77.false_of_muIsoZ2_of_muIsoS3 hZ2 hS3

theorem thinY_of_layerL3 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J)
    (hL3 : LayerL3 Ω K z) : ThinY Ω K z := by
  obtain ⟨ι, -, D₃, i₁, hone, hk⟩ := hL3
  obtain ⟨D, hD⟩ := exists_uniform_of_layer D₃ i₁ hone
  exact thinY_of_uniform h hint hN D (Or.inl (compIs_psl3 (hD.trans hk)))

theorem thinY_of_layerM11 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J)
    (hM11 : LayerM11 Ω K z) : ThinY Ω K z := by
  obtain ⟨ι, -, D₃, i₁, hone, hk⟩ := hM11
  obtain ⟨D, hD⟩ := exists_uniform_of_layer D₃ i₁ hone
  exact thinY_of_uniform h hint hN D (Or.inr (hD.trans hk))

theorem not_thinY_of_layerS3 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J)
    (hS3 : LayerS3 Ω K z) : ¬ ThinY Ω K z := by
  intro hthin
  obtain ⟨ι, -, D₃, i₁, hone, hk⟩ := hS3
  obtain ⟨D, hD⟩ := exists_uniform_of_layer D₃ i₁ hone
  rcases hk with hk | hk | hk
  · exact false_of_thinY_of_uniform_s3 h hint hN hthin D (Or.inl ⟨rfl, rfl⟩)
      (compIs_psu3 (hD.trans hk))
  · exact false_of_thinY_of_uniform_s3 h hint hN hthin D (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (compIs_g2 (hD.trans hk))
  · exact false_of_thinY_of_uniform_s3 h hint hN hthin D (Or.inr (Or.inr ⟨rfl, rfl⟩))
      (compIs_d4 (hD.trans hk))

theorem layerThinOrS3_proved : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (Ω : Set (Subgroup G)) (K J : Subgroup G) (S : Sylow 2 G) (R T W : Subgroup G) (z t : G),
    Q3T8.Asc77.BadStd8 Ω K J S R T W z t → IsIntrinsicU (.sl2 3 1) K z →
      NoTriangleAtEdge Ω K J → ThinY Ω K z ∨ LayerS3 Ω K z := by
  intro G _ _ _ Ω K J S R T W z t h hint hN
  rcases layer_shape h hint hN with hT | hL3 | hM11 | hS3
  · exact Or.inl (thinY_of_top h hint hT)
  · exact Or.inl (thinY_of_layerL3 h hint hN hL3)
  · exact Or.inl (thinY_of_layerM11 h hint hN hM11)
  · exact Or.inr hS3

theorem thinY_iff_not_layerS3 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J) :
    ThinY Ω K z ↔ ¬ LayerS3 Ω K z :=
  ⟨fun hthin hS3 => not_thinY_of_layerS3 h hint hN hS3 hthin, fun hn =>
    (layerThinOrS3_proved G Ω K J S R T W z t h hint hN).resolve_right hn⟩

theorem layer_shape_of_thinY [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J)
    (hthin : ThinY Ω K z) :
    (⊤ : Subgroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z))) ∈
        layerFam Ω K z ∨ LayerL3 Ω K z ∨ LayerM11 Ω K z := by
  rcases layer_shape h hint hN with hT | hL3 | hM11 | hS3
  · exact Or.inl hT
  · exact Or.inr (Or.inl hL3)
  · exact Or.inr (Or.inr hM11)
  · exact absurd hthin (not_thinY_of_layerS3 h hint hN hS3)

end Thin

end CFSG.ClassicalInvolution.Q3.Q3AM
