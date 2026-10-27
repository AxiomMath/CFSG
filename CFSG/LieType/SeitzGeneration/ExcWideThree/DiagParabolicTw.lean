module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagParabolic
public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagGlue

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWeight CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.CTP
open scoped Pointwise

abbrev TwTag (K : Type) [Field K] (σ : K ≃+* K) (hσ : σ ^ TwistTag.E6.order = 1) : Tag :=
  (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).tag

@[expose] def TwCompat (K : Type) [Field K] (σ : K →+* K) (b : Fin TwistTag.E6.tag.rank → Kˣ) :
    Prop :=
  ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)

theorem mem_normalizer_inf_of_mem_normalizer_twE6 {G : Type*} [Group G] {H K : Subgroup G} {t : G}
    (hH : t ∈ Subgroup.normalizer (H : Set G)) (hK : t ∈ Subgroup.normalizer (K : Set G)) :
    t ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH g, hK g]

section Tw

theorem rootChar_units_map {K : Type} [Field K] {τ : Tag} (σ : K →+* K)
    (b : Fin τ.rank → Kˣ) (μ : Fin τ.rank → ℤ) :
    rootChar (fun j => Units.map σ.toMonoidHom (b j)) μ =
      Units.map σ.toMonoidHom (rootChar b μ) := by
  unfold rootChar
  simp [map_prod, map_zpow]

theorem twCompat_weylTuple {K : Type} [Field K] {σ : K →+* K}
    {b : Fin TwistTag.E6.tag.rank → Kˣ} (hb : TwCompat K σ b)
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6) :
    TwCompat K σ (weylTuple w b) := by
  intro i
  have hc := (mem_relWeylTwist_iff_smul TwistTag.E6).1 (inv_mem hw) (Pi.single i 1)
  rw [permLattice_single] at hc
  unfold weylTuple
  rw [hc, rootChar_permLattice]
  have hfun : (fun j => b (TwistTag.E6.perm j)) = fun j => Units.map σ.toMonoidHom (b j) :=
    funext hb
  rw [hfun, rootChar_units_map]

theorem rootDiagUnit_mem_twistedE6DiagGL {K : Type} [Field K] (σ : K ≃+* K)
    {b : Fin TwistTag.E6.tag.rank → Kˣ} (hb : TwCompat K σ.toRingHom b) :
    rootDiagUnit TwistTag.E6.tag b ∈ twistedE6DiagGL K σ := by
  obtain ⟨u, hu⟩ := exists_compatDiag_eq hb
  rw [← hu]
  exact MonoidHom.mem_range.2 ⟨u, rfl⟩

theorem twistedE6DiagGL_le_twistedE6InndiagGL (K : Type) [Field K] (σ : K ≃+* K) :
    twistedE6DiagGL K σ ≤ twistedE6InndiagGL K σ :=
  le_sup_right

theorem mem_twistedE6InndiagGL_decomp (K : Type) [Field K] (σ : K ≃+* K)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ twistedE6InndiagGL K σ) :
    ∃ c ∈ twistedE6RootGroup K σ, ∃ t ∈ twistedE6DiagGL K σ, x = c * t := by
  have hN : twistedE6DiagGL K σ ≤ Subgroup.normalizer
      (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) :=
    (twistedE6DiagGL_le_twistedE6InndiagGL K σ).trans (twistedE6InndiagGL_le_normalizer K σ)
  have key : ∀ y ∈ Subgroup.closure ((twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) ∪
      (twistedE6DiagGL K σ : Set (ModGL TwistTag.E6.tag K))),
      ∃ c ∈ twistedE6RootGroup K σ, ∃ t ∈ twistedE6DiagGL K σ, y = c * t := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · exact ⟨z, hz, 1, one_mem _, (mul_one z).symm⟩
      · exact ⟨1, one_mem _, z, hz, (one_mul z).symm⟩
    | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc, t, ht, rfl⟩ := ha
      obtain ⟨c', hc', t', ht', rfl⟩ := hb
      refine ⟨c * (t * c' * t⁻¹), mul_mem hc ?_, t * t', mul_mem ht ht', ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hN ht) c').1 hc'
      · group
    | inv a _ ha =>
      obtain ⟨c, hc, t, ht, rfl⟩ := ha
      refine ⟨t⁻¹ * c⁻¹ * t, ?_, t⁻¹, inv_mem ht, ?_⟩
      · have h' := (Subgroup.mem_normalizer_iff.1 (hN (inv_mem ht)) c⁻¹).1 (inv_mem hc)
        rwa [inv_inv] at h'
      · group
  exact key x (mem_twistedE6InndiagGL_iff.1 hx)

theorem rootDiagUnit_mem_normalizer_graphFixedParabolicRadical {K : Type} [Field K]
    (σ : K ≃+* K) {b : Fin TwistTag.E6.tag.rank → Kˣ} (hb : TwCompat K σ.toRingHom b)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) :
    rootDiagUnit TwistTag.E6.tag b ∈ Subgroup.normalizer
      (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J : Set (ModGL TwistTag.E6.tag K)) := by
  have h1 : rootDiagUnit TwistTag.E6.tag b ∈ Subgroup.normalizer
      (parabolicRadical TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) :
        Set (ModGL TwistTag.E6.tag K)) := by
    refine mem_normalizer_of_map_eq ?_
    unfold parabolicRadical
    exact map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup b hα.1.1
  exact mem_normalizer_inf_of_mem_normalizer_twE6 h1
    (rootDiagUnit_mem_normalizer_twistedFixedGroup hb)

end Tw

theorem submodule_map_eq_of_le_of_inv_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {X : Submodule K V} {u : LinearMap.GeneralLinearGroup K V}
    (h : X.map (u : Module.End K V) ≤ X)
    (h' : X.map ((u⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) ≤ X) :
    X.map (u : Module.End K V) = X := by
  refine le_antisymm h ?_
  have e : (X.map ((u⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)).map
      (u : Module.End K V) = X := by
    rw [← submodule_map_units_mul, mul_inv_cancel, Units.val_one, Module.End.one_eq_id,
      Submodule.map_id]
  calc X = (X.map ((u⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)).map
        (u : Module.End K V) := e.symm
    _ ≤ X.map (u : Module.End K V) := Submodule.map_mono h'

section TwTorus

theorem mem_twistedE6DiagGL_iff (K : Type) [Field K] (σ : K ≃+* K)
    {t : ModGL TwistTag.E6.tag K} :
    t ∈ twistedE6DiagGL K σ ↔
      ∃ b : Fin TwistTag.E6.tag.rank → Kˣ, TwCompat K σ.toRingHom b ∧
        rootDiagUnit TwistTag.E6.tag b = t := by
  constructor
  · intro ht
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 ht
    refine ⟨compatDiag TwistTag.E6 σ.toRingHom u, compatDiag_perm u, ?_⟩
    rw [← hu]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact rootDiagUnit_mem_twistedE6DiagGL σ hb

theorem conj_inv_canonicalRep_twistedE6DiagGL (K : Type) [Field K] (σ : K ≃+* K)
    {w₀ : WeylGroup TwistTag.E6.tag} (hw : w₀ ∈ relWeylTwist TwistTag.E6)
    {t : ModGL TwistTag.E6.tag K} (ht : t ∈ twistedE6DiagGL K σ) :
    (canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀)⁻¹ * t *
        canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀ ∈ twistedE6DiagGL K σ := by
  obtain ⟨b, hb, rfl⟩ := (mem_twistedE6DiagGL_iff K σ).1 ht
  have hw' : w₀⁻¹ ∈ relWeylTwist TwistTag.E6 := inv_mem hw
  have hc : weylTuple w₀ (weylTuple w₀⁻¹ b) = b := by
    rw [weylTuple_weylTuple, mul_inv_cancel, weylTuple_one]
  have e : (canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀)⁻¹ *
      rootDiagUnit TwistTag.E6.tag b *
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀ =
      rootDiagUnit TwistTag.E6.tag (weylTuple w₀⁻¹ b) := by
    have h := canonicalRep_conj_rootDiagUnit w₀ (weylTuple w₀⁻¹ b)
    rw [hc] at h
    rw [← h]
    group
  rw [e]
  exact rootDiagUnit_mem_twistedE6DiagGL σ (twCompat_weylTuple hb hw')

theorem twistedE6DiagGL_le_normalizer_graphFixedParabolicRadical (K : Type) [Field K]
    (σ : K ≃+* K) (J : Set (Fin TwistTag.E6.foldedTag.rank)) :
    twistedE6DiagGL K σ ≤ Subgroup.normalizer
      (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J : Set (ModGL TwistTag.E6.tag K)) := by
  intro t ht
  obtain ⟨b, hb, rfl⟩ := (mem_twistedE6DiagGL_iff K σ).1 ht
  exact rootDiagUnit_mem_normalizer_graphFixedParabolicRadical σ hb J

theorem twistedE6DiagGL_le_normalizer_opposite (K : Type) [Field K] (σ : K ≃+* K)
    {w₀ : WeylGroup TwistTag.E6.tag} (hw : w₀ ∈ relWeylTwist TwistTag.E6)
    (J' : Set (Fin TwistTag.E6.foldedTag.rank)) :
    twistedE6DiagGL K σ ≤ Subgroup.normalizer
      (((graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J').map
        (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀)).toMonoidHom :
          Subgroup (ModGL TwistTag.E6.tag K)) : Set (ModGL TwistTag.E6.tag K)) := by
  intro t ht
  refine mem_normalizer_of_map_eq ?_
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀ with hn
  set s := n⁻¹ * t * n with hs
  have hsT : s ∈ twistedE6DiagGL K σ := conj_inv_canonicalRep_twistedE6DiagGL K σ hw ht
  have hsN : s ∈ Subgroup.normalizer
      (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J' : Set (ModGL TwistTag.E6.tag K)) :=
    twistedE6DiagGL_le_normalizer_graphFixedParabolicRadical K σ J' hsT
  have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj n).toMonoidHom.comp (MulAut.conj s).toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    show t * (n * x * n⁻¹) * t⁻¹ = n * (s * x * s⁻¹) * n⁻¹
    rw [hs]
    group
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_conj_eq_of_mem_normalizer hsN]

end TwTorus

section TwCore

theorem map_weightSpace_le_rootDiagUnit (K : Type) [Field K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) (b : Fin (TwTag K σ hσ).rank → Kˣ)
    (χ : (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space) :
    ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace χ).map
      (rootDiagUnit (TwTag K σ hσ) b : Module.End K (RootModule (TwTag K σ hσ) K)) ≤
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace χ := by
  refine Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 fun v hv => ?_)
  rw [SetLike.mem_coe, Submodule.mem_comap]
  rcases hv with ⟨α, hα, hχ, rfl⟩ | ⟨hχ0, j, rfl⟩
  · change rootDiag b (rootVec (TwTag K σ hσ) K α) ∈ _
    rw [rootDiag_rootVec b hα]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨α, hα, hχ, rfl⟩))
  · change rootDiag b (hVec (TwTag K σ hσ) K j) ∈ _
    rw [rootDiag_hVec b j]
    exact Submodule.subset_span (Or.inr ⟨hχ0, j, rfl⟩)

theorem map_weightSpace_eq_rootDiagUnit (K : Type) [Field K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) (b : Fin (TwTag K σ hσ).rank → Kˣ)
    (χ : (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space) :
    ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace χ).map
      (rootDiagUnit (TwTag K σ hσ) b : Module.End K (RootModule (TwTag K σ hσ) K)) =
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace χ := by
  refine submodule_map_eq_of_le_of_inv_le (map_weightSpace_le_rootDiagUnit K σ hσ b χ) ?_
  exact map_weightSpace_le_rootDiagUnit K σ hσ b⁻¹ χ

theorem filtration_map_le_rootDiagUnit (K : Type) [Field K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) (b : Fin (TwTag K σ hσ).rank → Kˣ)
    (l : (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space) (c : ℝ) :
    ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c).map
      (rootDiagUnit (TwTag K σ hσ) b : Module.End K (RootModule (TwTag K σ hσ) K)) ≤
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c := by
  refine Submodule.map_le_iff_le_comap.2 (weightFiltration_le_iff.2 fun χ hχ hc => ?_)
  rw [← Submodule.map_le_iff_le_comap]
  exact (map_weightSpace_le_rootDiagUnit K σ hσ b χ).trans (le_weightFiltration hχ hc)

theorem filtration_map_eq_rootDiagUnit (K : Type) [Field K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) (b : Fin (TwTag K σ hσ).rank → Kˣ)
    (l : (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space) (c : ℝ) :
    ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c).map
      (rootDiagUnit (TwTag K σ hσ) b : Module.End K (RootModule (TwTag K σ hσ) K)) =
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c := by
  refine submodule_map_eq_of_le_of_inv_le (filtration_map_le_rootDiagUnit K σ hσ b l c) ?_
  exact filtration_map_le_rootDiagUnit K σ hσ b⁻¹ l c

theorem mem_twistedE6InndiagGL_decompTw (K : Type) [Field K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) {x : ModGL (TwTag K σ hσ) K}
    (hx : x ∈ twistedE6InndiagGL K σ) :
    ∃ c : ModGL (TwTag K σ hσ) K, c ∈ twistedE6RootGroup K σ ∧
      ∃ t : ModGL (TwTag K σ hσ) K, t ∈ twistedE6DiagGL K σ ∧ x = c * t := by
  obtain ⟨c, hc, t, ht, h⟩ := mem_twistedE6InndiagGL_decomp K σ hx
  exact ⟨c, hc, t, ht, h⟩

theorem mem_twistedE6DiagGL_iffTw (K : Type) [Field K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) {t : ModGL (TwTag K σ hσ) K} :
    t ∈ twistedE6DiagGL K σ ↔
      ∃ b : Fin (TwTag K σ hσ).rank → Kˣ, TwCompat K σ.toRingHom b ∧
        rootDiagUnit (TwTag K σ hσ) b = t :=
  mem_twistedE6DiagGL_iff K σ

theorem map_weightSpace_eq_of_mem_twistedE6DiagGL (K : Type) [Field K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) {t : ModGL (TwTag K σ hσ) K}
    (ht : t ∈ twistedE6DiagGL K σ)
    (χ : (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space) :
    ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace χ).map
      (t : Module.End K (RootModule (TwTag K σ hσ) K)) =
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace χ := by
  obtain ⟨b, -, rfl⟩ := (mem_twistedE6DiagGL_iffTw K σ hσ).1 ht
  exact map_weightSpace_eq_rootDiagUnit K σ hσ b χ

theorem filtration_map_eq_of_mem_twistedE6DiagGL (K : Type) [Field K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) {t : ModGL (TwTag K σ hσ) K}
    (ht : t ∈ twistedE6DiagGL K σ)
    (l : (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space) (c : ℝ) :
    ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c).map
      (t : Module.End K (RootModule (TwTag K σ hσ) K)) =
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c := by
  obtain ⟨b, -, rfl⟩ := (mem_twistedE6DiagGL_iffTw K σ hσ).1 ht
  exact filtration_map_eq_rootDiagUnit K σ hσ b l c

theorem twistedE6DiagGL_le_normalizer_C0 (K : Type) [Field K] (σ : K ≃+* K) :
    twistedE6DiagGL K σ ≤
      Subgroup.normalizer (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) := by
  intro t ht
  obtain ⟨b, hb, rfl⟩ := (mem_twistedE6DiagGL_iff K σ).1 ht
  exact rootDiagUnit_mem_normalizer_graphFixedRootGroup (t := TwistTag.E6) (K := K)
    (σ := σ.toRingHom) hb

theorem mem_twistedParabolic_sup_torus_of_stab (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1)
    {l : (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space}
    (hl : l ∈ (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).dominant)
    {y : ModGL (TwTag K σ hσ) K} (hy : y ∈ twistedE6InndiagGL K σ)
    (hstab : ∀ c : ℝ,
      ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c).map
        (y : Module.End K (RootModule (TwTag K σ hσ) K)) =
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c) :
    y ∈ graphFixedParabolic TwistTag.E6 K σ.toRingHom
        ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).face l) ⊔
      twistedE6DiagGL K σ := by
  obtain ⟨c', hc', t', ht', rfl⟩ := mem_twistedE6InndiagGL_decompTw K σ hσ hy
  have hT : ∀ c : ℝ,
      ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c).map
        (t' : Module.End K (RootModule (TwTag K σ hσ) K)) =
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c :=
    fun c => filtration_map_eq_of_mem_twistedE6DiagGL K σ hσ ht' l c
  have hc'stab : ∀ c : ℝ,
      ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c).map
        (c' : Module.End K (RootModule (TwTag K σ hσ) K)) =
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l c := by
    intro c
    have h1 := hstab c
    erw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, hT c] at h1
    exact h1
  have hset :=
    (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).setOf_stab_eq_map_conj_parabolic
      hl (one_mem _)
      (F := (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l)
      (fun c => by rw [Units.val_one, Module.End.one_eq_id, Submodule.map_id])
  have hmem : c' ∈ ((((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).parabolic
      ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).face l)).map
        (MulAut.conj (1 : ModGL (TwTag K σ hσ) K)).toMonoidHom :
          Subgroup (ModGL (TwTag K σ hσ) K)) : Set (ModGL (TwTag K σ hσ) K)) := by
    erw [← hset]
    exact ⟨hc', hc'stab⟩
  obtain ⟨p, hp, hpc⟩ := Subgroup.mem_map.1 hmem
  have hpc' : p = c' := by simpa [MulAut.conj_apply] using hpc
  exact mul_mem (Subgroup.mem_sup_left (hpc' ▸ hp)) (Subgroup.mem_sup_right ht')

theorem graphFixedParabolic_eq_radical_sup_levi (K : Type) [Field K] (σ : K ≃+* K)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) :
    graphFixedParabolic TwistTag.E6 K σ.toRingHom J =
      graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J ⊔
        graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J := by
  obtain ⟨-, -, -, -, -, -, -, -, hQP, -, hLP, huniq, -, -, -, -, -, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σ J
  refine le_antisymm ?_ (sup_le hQP hLP)
  intro g hg
  obtain ⟨⟨q, l⟩, ⟨hq, hl, hgql⟩, -⟩ := huniq g hg
  rw [hgql]
  exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hl)

theorem not_three_dvd_index_graphFixed_sup (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    [Fact (ringChar K).Prime] [CharP K (ringChar K)] (hK3 : ringChar K ≠ 3)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) :
    ¬ 3 ∣ ((graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ).subgroupOf
      (graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ)).index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, -, -, -, -, -, hfin, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σ J
  have hQp : IsPGroup (ringChar K) (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J) :=
    hfin (ringChar K)
  have hPN : graphFixedParabolic TwistTag.E6 K σ.toRingHom J ≤ Subgroup.normalizer
      (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J : Set (ModGL TwistTag.E6.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm
  have hQPP : graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J ≤
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ :=
    hQP.trans le_sup_left
  have hLPP : graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ ≤
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ :=
    sup_le_sup_right hLP _
  have hQn : graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ ≤
      Subgroup.normalizer
        (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J : Set (ModGL TwistTag.E6.tag K)) :=
    sup_le hPN (twistedE6DiagGL_le_normalizer_graphFixedParabolicRadical K σ J)
  have hsup : (graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ) ⊔
      graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J =
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ := by
    rw [graphFixedParabolic_eq_radical_sup_levi K σ J]
    exact (sup_right_comm _ _ _).trans (congrArg (fun x => x ⊔ twistedE6DiagGL K σ) (sup_comm _ _))
  have hdvd := index_subgroupOf_dvd_card_of_sup hQPP hLPP hQn hsup
  have hQ3 : ¬ 3 ∣ Nat.card (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J) :=
    not_dvd_card_of_isPGroup hK3 hQp
  exact fun h => hQ3 (h.trans hdvd)

theorem le_iSup_centralizer_of_levi_sup_torus (k : Type) [Field k] [Finite k]
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p) (σ : k ≃+* k)
    (hσ : σ ^ TwistTag.E6.order = 1)
    [IsSimpleGroup (graphFixedRootGroup TwistTag.E6 k σ.toRingHom)]
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJ : J ≠ Set.univ)
    {A : Subgroup (ModGL (TwTag k σ hσ) k)} [IsElementaryAbelian p A]
    (hcard : p ^ 2 ≤ Nat.card A)
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J ⊔ twistedE6DiagGL k σ) :
    graphFixedRootGroup TwistTag.E6 k σ.toRingHom ≤
      ⨆ a ∈ A, ⨆ (_ : a ≠ 1), graphFixedRootGroup TwistTag.E6 k σ.toRingHom ⊓
        Subgroup.centralizer ({a} : Set (ModGL (TwTag k σ hσ) k)) := by
  have := finite_modGL (τ := TwTag k σ hσ) (K := k)
  have := finite_modGL (τ := TwistTag.E6.tag) (K := k)
  obtain ⟨w₀, δ, hmax, hδδ, hδ, hcomm⟩ := exists_longest_fixed_data TwistTag.E6
  have hw : w₀ ∈ relWeylTwist TwistTag.E6 :=
    mem_relWeylTwist_of_forall_length_le hmax
  obtain ⟨-, hR, hH⟩ := canonical_weyl_root_transport TwistTag.E6.tag k
  set C := graphFixedRootGroup TwistTag.E6 k σ.toRingHom
  have hnC : canonicalRep (coxeterSystem TwistTag.E6.tag) k w₀ ∈ C :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hmax)
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) k w₀
  have hpos : ∀ i, (rootSubgroup TwistTag.E6.tag k (Pi.single i 1)).map (MulAut.conj
      n).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (-Pi.single (δ i) 1) := fun i => by
    rw [hR w₀ _ (isRoot_single TwistTag.E6.tag i), hδ]
  have hneg : ∀ i, (rootSubgroup TwistTag.E6.tag k (-Pi.single i 1)).map (MulAut.conj
      n).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (Pi.single (δ i) 1) := fun i => by
    rw [hR w₀ _ (isRoot_neg_single TwistTag.E6.tag i), smul_neg, hδ, neg_neg]
  have hpos' : ∀ i, (rootSubgroup TwistTag.E6.tag k (Pi.single i 1)).map (MulAut.conj
      n⁻¹).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (-Pi.single (δ i) 1) := fun i => by
    rw [← map_conj_inv_map_conj (rootSubgroup TwistTag.E6.tag k (-Pi.single (δ i) 1)) n, hneg, hδδ]
  have hneg' : ∀ i, (rootSubgroup TwistTag.E6.tag k (-Pi.single i 1)).map (MulAut.conj
      n⁻¹).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (Pi.single (δ i) 1) := fun i => by
    rw [← map_conj_inv_map_conj (rootSubgroup TwistTag.E6.tag k (Pi.single (δ i) 1)) n, hpos, hδδ]
  set J' := (fun i => TwistTag.E6.orbitIndex (δ i)) '' TwistTag.E6.orbitUnion J
  have hJJ' : δ '' TwistTag.E6.orbitUnion J = TwistTag.E6.orbitUnion J' := image_orbitUnion_eq
      hcomm J
  have hJ'J : δ '' TwistTag.E6.orbitUnion J' = TwistTag.E6.orbitUnion J := by
    rw [← hJJ', image_image_of_involutive hδδ]
  have hLn : (graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J').map (MulAut.conj
      n).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J :=
    map_conj_graphFixedParabolicLevi_le hnC (by
      rw [← hJ'J]
      exact map_conj_parabolicLevi_le_of_rootSubgroup (hH w₀) hpos hneg _)
  have hLn' : (graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J).map (MulAut.conj
      n⁻¹).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J' :=
    map_conj_graphFixedParabolicLevi_le (inv_mem hnC) (by
      rw [← hJJ']
      exact map_conj_parabolicLevi_le_of_rootSubgroup (inv_mem (hH w₀)) hpos' hneg' _)
  set Q := graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J
  set Q' := (graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J').map (MulAut.conj
      n).toMonoidHom
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, -, -, -, -, -, hfin, hne⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 k σ J
  obtain ⟨-, -, -, -, -, -, -, -, hQP', hQnorm', hLP', -, -, -, -, -, hfin', -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 k σ J'
  have hQp : IsPGroup r Q := hfin r
  have hQ'p : IsPGroup r Q' := (hfin' r).map _
  have hQ1 : Q ≠ ⊥ := hne hJ
  have hQC : Q ≤ C := hQP.trans (graphFixedParabolic_le TwistTag.E6 k σ.toRingHom J)
  have hQ'C : Q' ≤ C := by
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem hnC ((hQP'.trans (graphFixedParabolic_le TwistTag.E6 k σ.toRingHom J'))
      hq))
      (inv_mem hnC)
  have hPQ : graphFixedParabolic TwistTag.E6 k σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag k)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm
  have hPQ' : graphFixedParabolic TwistTag.E6 k σ.toRingHom J' ≤
      Subgroup.normalizer (graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J' : Set (ModGL
      TwistTag.E6.tag k)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP').1 hQnorm'
  have hLQ : graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag k)) := hLP.trans hPQ
  have hLQ' : graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J ≤
      Subgroup.normalizer (Q' : Set (ModGL TwistTag.E6.tag k)) := fun m hm => by
    have h := mem_normalizer_map_conj_inv (n := n⁻¹) (m := m)
      (H := graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J')
      (hPQ' (hLP' (hLn' (Subgroup.mem_map_of_mem _ hm))))
    rwa [inv_inv] at h
  have hgen : C ≤ Q ⊔ Q' ⊔ graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J := by
    refine sup_le ((graphFixedPosUnipotent_le_sup σ J).trans
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)) ?_
    rw [← map_conj_graphFixedPosUnipotent hmax]
    refine (Subgroup.map_mono (graphFixedPosUnipotent_le_sup σ J')).trans ?_
    rw [Subgroup.map_sup]
    exact sup_le (le_sup_right.trans le_sup_left) (hLn.trans le_sup_right)
  have hXC : Q ⊔ Q' ≤ C := sup_le hQC hQ'C
  have hCX : C ≤ Q ⊔ Q' := by
    have hN : C ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup (ModGL TwistTag.E6.tag k)) : Set (ModGL
      TwistTag.E6.tag k)) :=
      hgen.trans (sup_le Subgroup.le_normalizer fun m hm =>
        mem_normalizer_sup_of_mem (hLQ hm) (hLQ' hm))
    have : ((Q ⊔ Q').subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q ⊔ Q').subgroupOf C) with h | h
    · exfalso
      apply hQ1
      have hdis := Subgroup.subgroupOf_eq_bot.1 h
      exact eq_bot_iff.2 fun q hq => (Subgroup.disjoint_def.1 hdis)
        (Subgroup.mem_sup_left hq) (hQC hq) ▸ Subgroup.mem_bot.2 rfl
    · exact Subgroup.subgroupOf_eq_top.1 h
  have hAQ : A ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag k)) :=
    hAL.trans (sup_le hLQ (twistedE6DiagGL_le_normalizer_graphFixedParabolicRadical k σ J))
  have hAQ' : A ≤ Subgroup.normalizer (Q' : Set (ModGL TwistTag.E6.tag k)) :=
    hAL.trans (sup_le hLQ' (twistedE6DiagGL_le_normalizer_opposite k σ hw J'))
  have h1 := le_iSup_inf_centralizer_of_coprime hcard (not_dvd_card_of_isPGroup hrp hQp)
    hAQ hQC
  have h2 := le_iSup_inf_centralizer_of_coprime hcard (not_dvd_card_of_isPGroup hrp hQ'p)
    hAQ' hQ'C
  exact hCX.trans (sup_le h1 h2)

theorem twE6InndiagCentralizerGeneration_aux (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) (f : ℕ) (hp : (ringChar K).Prime) (hf : 1 ≤ f)
    (hK3 : ringChar K ≠ 3) (hσq : ∀ c, σ c = c ^ (ringChar K ^ f))
    (hKq : Nat.card K = (ringChar K ^ f) ^ 2)
    (A : Subgroup (ModGL (TwTag K σ hσ) K)) (hAle : A ≤ twistedE6InndiagGL K σ)
    (hAEA : CFSG.IsElementaryAbelian 3 A) (hAcard : 3 ^ 2 ≤ Nat.card A)
    (R : Subgroup (ModGL (TwTag K σ hσ) K)) (hRC : R ≤ twistedE6RootGroup K σ)
    (hRp : IsPGroup (ringChar K) R) (hR1 : R ≠ ⊥)
    (hRn : A ≤ Subgroup.normalizer (R : Set (ModGL (TwTag K σ hσ) K))) :
    (⨆ a ∈ A, ⨆ (_ : a ≠ 1),
        (twistedE6RootGroup K σ : Subgroup (ModGL (TwTag K σ hσ) K)) ⊓
          Subgroup.centralizer ({a} : Set (ModGL (TwTag K σ hσ) K))) =
      (twistedE6RootGroup K σ : Subgroup (ModGL (TwTag K σ hσ) K)) := by
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_modGL (τ := TwTag K σ hσ) (K := K)
  haveI := hAEA
  have hcardTw : Nat.card K = (ringChar K ^ f) ^ TwistTag.E6.order := hKq
  have hperf := finite_fixed_root_group_perfect TwistTag.E6 hp hf K hcardTw σ.toRingHom hσq
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := CFSG.LieType.SeitzGeneration.nonempty_derivedCentralQuotient_equiv _ _
    hperf.2.2.1 hZ
  haveI hSimple : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    (CFSG.LieType.Simplicity.fam_2e6_simplicity
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) (ringChar K) f
      ⟨⟨hp, hf, rfl⟩, K, inferInstance, inferInstance, hcardTw, σ.toRingHom, hσq,
        ⟨ψ.symm⟩⟩).2
  obtain ⟨M, -, ⟨g₁, hg₁, l₁, hl₁, hgl₁⟩, -, F, hF, -, ⟨g₀, hg₀, l₀, hl₀, hl₀1, hgl₀⟩,
      hdom, hsemi⟩ :=
    RootWeightDatum.root_p_subgroup_optimal_parabolic_containment
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K)
      (ringChar K) R hRC hRp hR1
  obtain ⟨hJ, -, -, -, -⟩ := hdom g₀ hg₀ l₀ hl₀ hl₀1 hgl₀
  set J₀ : Set (Fin TwistTag.E6.foldedTag.rank) :=
    (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).face l₀ with hJ₀
  have hC0Inn : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤ twistedE6InndiagGL K σ :=
    le_sup_left
  have hg₀I : g₀ ∈ twistedE6InndiagGL K σ := hC0Inn hg₀
  have hPh_le : graphFixedParabolic TwistTag.E6 K σ.toRingHom J₀ ⊔ twistedE6DiagGL K σ ≤
      twistedE6InndiagGL K σ :=
    sup_le ((graphFixedParabolic_le TwistTag.E6 K σ.toRingHom J₀).trans hC0Inn)
      (twistedE6DiagGL_le_twistedE6InndiagGL K σ)
  have hstabN : ∀ x : ModGL (TwTag K σ hσ) K, x ∈ twistedE6InndiagGL K σ →
      x ∈ Subgroup.normalizer (R : Set (ModGL (TwTag K σ hσ) K)) →
      ∀ c : ℝ, (F c).map (x : Module.End K (RootModule (TwTag K σ hσ) K)) = F c := by
    intro x hx hxN c
    obtain ⟨c₀, hc₀, t₀, ht₀, rfl⟩ := mem_twistedE6InndiagGL_decompTw K σ hσ hx
    set s : RootModule (TwTag K σ hσ) K ≃ₗ[K] RootModule (TwTag K σ hσ) K :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv K (RootModule (TwTag K σ hσ) K) t₀
      with hs_def
    have hs_apply : ∀ v, s v = (t₀ : Module.End K (RootModule (TwTag K σ hσ) K)) v :=
      fun v => rfl
    have hs_symm : ∀ v, s.symm v =
        ((t₀⁻¹ : ModGL (TwTag K σ hσ) K) : Module.End K (RootModule (TwTag K σ hσ) K)) v := by
      intro v
      rw [LinearEquiv.symm_apply_eq, hs_apply, ← Module.End.mul_apply, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Module.End.one_eq_id, LinearMap.id_apply]
    have hs_eq : ∀ g : ModGL (TwTag K σ hσ) K, semilinearConjUnit s g = t₀ * g * t₀⁻¹ := by
      intro g
      apply Units.ext
      apply LinearMap.ext
      intro v
      rw [coe_semilinearConjUnit, semilinearConj_apply, hs_symm, hs_apply, Units.val_mul,
        Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
    have hsC : ∀ g : ModGL (TwTag K σ hσ) K,
        semilinearConjUnit s g ∈
            (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).group ↔
          g ∈ (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).group := by
      intro g
      rw [hs_eq]
      exact (Subgroup.mem_normalizer_iff.1 (twistedE6DiagGL_le_normalizer_C0 K σ ht₀) g).symm
    have hsW : ∀ χ ∈ (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weights,
        ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace χ).map
          s.toLinearMap =
          (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace
            ((LinearIsometryEquiv.refl ℝ
              (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space) χ) := by
      intro χ _
      exact map_weightSpace_eq_of_mem_twistedE6DiagGL K σ hσ ht₀ χ
    have hQ' : ∀ x' : ModGL (TwTag K σ hσ) K, x' ∈ R ↔
        ∃ q ∈ R, c₀ * semilinearConjUnit s q * c₀⁻¹ = x' := by
      intro x'
      simp only [hs_eq]
      constructor
      · intro hx'
        refine ⟨(c₀ * t₀)⁻¹ * x' * (c₀ * t₀), ?_, ?_⟩
        · have h' := (Subgroup.mem_normalizer_iff.1 (inv_mem hxN) x').1 hx'
          rwa [inv_inv] at h'
        · group
      · rintro ⟨q, hq, rfl⟩
        have h' := (Subgroup.mem_normalizer_iff.1 hxN q).1 hq
        have e : c₀ * (t₀ * q * t₀⁻¹) * c₀⁻¹ = c₀ * t₀ * q * (c₀ * t₀)⁻¹ := by group
        rw [e]
        exact h'
    have hcov := hsemi (RingHom.id K) (RingHom.id K) s hsC (LinearIsometryEquiv.refl ℝ _)
      (by simp) hsW c₀ hc₀ R hQ'
    have h1 := hcov.2.2 g₁ hg₁ l₁ hl₁ hgl₁ c
    have h2 := hF g₁ hg₁ l₁ hl₁ hgl₁ c
    have e : (F c).map s.toLinearMap =
        (F c).map (t₀ : Module.End K (RootModule (TwTag K σ hσ) K)) := rfl
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, ← e]
    exact h1.symm.trans h2
  have hstabG : ∀ x ∈ A, g₀⁻¹ * x * g₀ ∈
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J₀ ⊔ twistedE6DiagGL K σ := by
    intro x hx
    have hxI := hAle hx
    have hxN := hRn hx
    have hgI : g₀⁻¹ * x * g₀ ∈ twistedE6InndiagGL K σ :=
      mul_mem (mul_mem (inv_mem hg₀I) hxI) hg₀I
    have key : ∀ c : ℝ,
        ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l₀ c).map
          ((g₀⁻¹ * x * g₀ : ModGL (TwTag K σ hσ) K) :
            Module.End K (RootModule (TwTag K σ hσ) K)) =
        (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l₀ c := by
      intro c
      have h1 := hF g₀ hg₀ l₀ hl₀1 hgl₀ c
      have h2 := hstabN x hxI hxN c
      rw [submodule_map_units_mul, submodule_map_units_mul, h1, h2, ← h1,
        ← submodule_map_units_mul, inv_mul_cancel, Units.val_one, Module.End.one_eq_id,
        Submodule.map_id]
    exact mem_twistedParabolic_sup_torus_of_stab K σ hσ hl₀ hgI key
  have hA0 : A.map (MulAut.conj g₀⁻¹).toMonoidHom ≤
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J₀ ⊔ twistedE6DiagGL K σ := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hstabG x hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact h
  haveI hA0e : IsElementaryAbelian 3 (A.map (MulAut.conj g₀⁻¹).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hA0p : IsPGroup 3 (A.map (MulAut.conj g₀⁻¹).toMonoidHom) :=
    IsElementaryAbelian.isPGroup 3 _
  have hindex := not_three_dvd_index_graphFixed_sup K σ hK3 J₀
  obtain ⟨y, hyPh, hyA⟩ := exists_conj_le_of_not_dvd_index hA0 hA0p hindex
  set A₁ := (A.map (MulAut.conj g₀⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom with hA₁
  haveI hA₁e : IsElementaryAbelian 3 A₁ := IsElementaryAbelian.map _
  have hA₁card : 3 ^ 2 ≤ Nat.card A₁ := by
    rw [hA₁, Subgroup.card_map_of_injective (MulAut.conj y).injective,
      Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective]
    exact hAcard
  have hG := le_iSup_centralizer_of_levi_sup_torus K hK3 σ hσ hJ hA₁card hyA
  have hyC : y * g₀⁻¹ ∈ Subgroup.normalizer
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom : Set (ModGL TwistTag.E6.tag K)) :=
    twistedE6InndiagGL_le_normalizer K σ (mul_mem (hPh_le hyPh) (inv_mem hg₀I))
  have hconjeq : A.map (MulAut.conj (y * g₀⁻¹)).toMonoidHom = A₁ := by
    have hfun : (MulAut.conj (y * g₀⁻¹)).toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp (MulAut.conj g₀⁻¹).toMonoidHom := by
      refine MonoidHom.ext fun z => ?_
      show y * g₀⁻¹ * z * (y * g₀⁻¹)⁻¹ = y * (g₀⁻¹ * z * g₀⁻¹⁻¹) * y⁻¹
      group
    rw [hA₁, Subgroup.map_map, hfun]
  have hC_sup : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤
      ⨆ a ∈ A, ⨆ (_ : a ≠ 1), graphFixedRootGroup TwistTag.E6 K σ.toRingHom ⊓
        Subgroup.centralizer ({a} : Set (ModGL (TwTag K σ hσ) K)) :=
    le_iSup_inf_centralizer_of_map_conj_normalizer (G := ModGL (TwTag K σ hσ) K) hyC (by
      rw [hconjeq]
      exact hG)
  exact le_antisymm (iSup₂_le fun a _ => iSup_le fun _ => inf_le_left) hC_sup

theorem twE6InndiagCentralizerGeneration_holds : TwE6InndiagCentralizerGeneration := by
  intro K _ _ σ q hK3 hσq hKq A hAle hAEA hAcard R hRC hRp hR1 hRn
  have hq2 : 2 ≤ q := by
    by_contra h
    have hq : q ≤ 1 := by omega
    have h1 : Nat.card K ≤ 1 := by
      rw [hKq]
      nlinarith [Nat.zero_le q]
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    omega
  obtain ⟨hp, f, hf, rfl⟩ := ExcHighThree.exists_pow_ringChar_of_card_sq K q hKq hq2
  have hσ : σ ^ TwistTag.E6.order = 1 := by
    have hsq : σ ^ 2 = 1 := by
      refine RingEquiv.ext fun c => ?_
      have hσσ : σ (σ c) = c := by
        haveI := Fintype.ofFinite K
        rw [hσq (σ c), hσq c, ← pow_mul, ← sq, ← hKq, Nat.card_eq_fintype_card]
        exact FiniteField.pow_card c
      simpa only [pow_two, RingAut.mul_apply, RingAut.one_apply] using hσσ
    exact hsq
  exact twE6InndiagCentralizerGeneration_aux K σ hσ f hp hf hK3 hσq hKq A hAle hAEA hAcard R
    hRC hRp hR1 hRn

theorem twE6InndiagParabolic'_holds : TwE6InndiagParabolic' :=
  twE6InndiagParabolic'_of_generic twE6InndiagCentralizerGeneration_holds

theorem twE6InndiagParabolic_holds : TwE6InndiagParabolic := twE6InndiagParabolic'_holds

end TwCore

end CFSG.LieType.SeitzGeneration.ExcWideThree
