module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Conj
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4DiagLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OddIdx
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Defs

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang
  CFSG.GH74.GLS.Stage2.OddAut CFSG.RankThree.PartOne.KGD CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem conj_injective_of_center_eq_bot {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center Y := Subgroup.mem_center_iff.2 fun y => by
    have e := congrArg (fun φ : MulAut Y => φ y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at e
    calc y * g = (g * y * g⁻¹) * g := by rw [e]
      _ = g * y := by group
  rw [hZ] at hc
  exact Subgroup.mem_bot.1 hc


section Core

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K₃ : Type} [Field K₃] [Finite K₃]

theorem shintani_core (hT : ThreeD4FixedNF) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (σ : K₃ ≃+* K₃) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K₃ L] [IsAlgClosure K₃ L] [CharP L ℓ]
    {x : ModGL TwistTag.D4.tag L} (hx : x ∈ adjointGroup TwistTag.D4.tag L)
    (hxF : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x)
    (hx3 : (x * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1) :
    ∃ u ∈ adjointGroup TwistTag.D4.tag L,
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) u = u ∧
      ∃ t ∈ graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L), t ^ 3 = 1 ∧
        u * (x * (diagramMap TwistTag.D4 L)⁻¹) * u⁻¹ = t * (diagramMap TwistTag.D4 L)⁻¹ := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₃
  have hℓ : ℓ.Prime := Fact.out
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hF₁P : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (diagramMap TwistTag.D4 L) =
      diagramMap TwistTag.D4 L := units_map_entrywiseHom_diagramMap _
  have hF₂ : ∀ g, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g = diagramMap TwistTag.D4 L *
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * (diagramMap TwistTag.D4 L)⁻¹ :=
    fun g => twistHom_apply _ g
  have hP3 : diagramMap TwistTag.D4 L * diagramMap TwistTag.D4 L *
      diagramMap TwistTag.D4 L = 1 := by
    rw [← pow_three']
    exact diagramMap_pow_order TwistTag.D4 L
  have hx3' : (x * (diagramMap TwistTag.D4 L)⁻¹) * (x * (diagramMap TwistTag.D4 L)⁻¹) *
      (x * (diagramMap TwistTag.D4 L)⁻¹) = 1 := by
    rw [← pow_three']
    exact hx3
  obtain ⟨g, hg, hgF⟩ := lang_conjugator_D4 (K := K₃) hf L
    (diagramMap TwistTag.D4 L * x⁻¹ * (diagramMap TwistTag.D4 L)⁻¹) (d4P_conj_mem (inv_mem hx))
  have hF₁g : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g =
      (diagramMap TwistTag.D4 L)⁻¹ * g * diagramMap TwistTag.D4 L * x⁻¹ := by
    rw [hF₂] at hgF
    calc Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g = (diagramMap TwistTag.D4 L)⁻¹ *
        (diagramMap TwistTag.D4 L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g *
          (diagramMap TwistTag.D4 L)⁻¹) * diagramMap TwistTag.D4 L := by group
      _ = (diagramMap TwistTag.D4 L)⁻¹ * (g * (diagramMap TwistTag.D4 L * x⁻¹ *
          (diagramMap TwistTag.D4 L)⁻¹)) * diagramMap TwistTag.D4 L := by rw [hgF]
      _ = (diagramMap TwistTag.D4 L)⁻¹ * g * diagramMap TwistTag.D4 L * x⁻¹ := by group
  set y := g * x * (diagramMap TwistTag.D4 L)⁻¹ * g⁻¹ * diagramMap TwistTag.D4 L with hydef
  have hyG : y ∈ adjointGroup TwistTag.D4.tag L := by
    have e : y = g * x * ((diagramMap TwistTag.D4 L)⁻¹ * g⁻¹ * diagramMap TwistTag.D4 L) := by
      rw [hydef]
      group
    rw [e]
    exact mul_mem (mul_mem hg hx) (d4P_inv_conj_mem (inv_mem hg))
  have hyF : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) y = y := by
    rw [hF₂, hydef, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hF₁g, hxF, hF₁P]
    group
  have hymem : y ∈ (triEmb K₃ σ L).range := by
    rw [triEmb_range (σ := σ) (L := L) hℓ hf hK₃ hσ _ hFr]
    exact Subgroup.mem_inf.2 ⟨hyG, hyF⟩
  obtain ⟨y₀, hy₀⟩ := hymem
  have hδ : ∀ w : graphFixedRootGroup TwistTag.D4 K₃ σ.toRingHom,
      triEmb K₃ σ L (fieldActor (t := TwistTag.D4) σ σ w) =
        (diagramMap TwistTag.D4 L)⁻¹ * triEmb K₃ σ L w * diagramMap TwistTag.D4 L := by
    intro w
    rw [triEmb_apply, triEmb_apply, coe_fieldActor_eq_conj, map_mul, map_mul, map_inv,
      baseChangeGL_diagramMap]
  have hN : normSeq (fieldActor (t := TwistTag.D4) σ σ) y₀ 3 = 1 := by
    apply triEmb_injective (L := L)
    have e : normSeq (fieldActor (t := TwistTag.D4) σ σ) y₀ 3 =
        y₀ * fieldActor (t := TwistTag.D4) σ σ y₀ *
          fieldActor (t := TwistTag.D4) σ σ (fieldActor (t := TwistTag.D4) σ σ y₀) := by
      simp only [normSeq, pow_two, MulAut.mul_apply, MulAut.one_apply, pow_zero, pow_one, one_mul]
    rw [e, map_mul, map_mul, hδ, hδ, hδ, hy₀, map_one]
    calc y * ((diagramMap TwistTag.D4 L)⁻¹ * y * diagramMap TwistTag.D4 L) *
        ((diagramMap TwistTag.D4 L)⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * y *
          diagramMap TwistTag.D4 L) * diagramMap TwistTag.D4 L) =
        g * ((x * (diagramMap TwistTag.D4 L)⁻¹) * (x * (diagramMap TwistTag.D4 L)⁻¹) *
          (x * (diagramMap TwistTag.D4 L)⁻¹)) * g⁻¹ *
            (diagramMap TwistTag.D4 L * diagramMap TwistTag.D4 L *
              diagramMap TwistTag.D4 L) := by
          rw [hydef]
          group
      _ = 1 := by rw [hx3', hP3]; group
  obtain ⟨k, s₀, hs₀δ, hs₀3, hks⟩ := hT ℓ f hℓ hℓ5 hf K₃ hK₃ σ hσ y₀ hN
  have hks' : k * y₀ * (fieldActor (t := TwistTag.D4) σ σ k)⁻¹ = s₀ := by
    rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.conj_twist_eq] at hks
    exact conj_injective_of_center_eq_bot (center_graphFixedRootGroup_eq_bot σ.surjective)
      (mul_right_cancel hks)
  set k' := triEmb K₃ σ L k
  set t₀ := triEmb K₃ σ L s₀
  have ht₀eq : k' * y * ((diagramMap TwistTag.D4 L)⁻¹ * k' * diagramMap TwistTag.D4 L)⁻¹ = t₀ := by
    have h := congrArg (triEmb K₃ σ L) hks'
    rw [map_mul, map_mul, map_inv, hδ, hy₀] at h
    exact h
  have ht₀P : t₀ * diagramMap TwistTag.D4 L = diagramMap TwistTag.D4 L * t₀ := by
    have h := congrArg (triEmb K₃ σ L) hs₀δ
    rw [hδ] at h
    calc t₀ * diagramMap TwistTag.D4 L =
        diagramMap TwistTag.D4 L * ((diagramMap TwistTag.D4 L)⁻¹ * t₀ *
          diagramMap TwistTag.D4 L) := by group
      _ = diagramMap TwistTag.D4 L * t₀ := by rw [h]
  have ht₀C : t₀ ∈ graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L) :=
    Subgroup.mem_inf.2 ⟨triEmb_mem_adjointGroup s₀,
      Subgroup.mem_centralizer_singleton_iff.2 ht₀P⟩
  have ht₀3 : t₀ ^ 3 = 1 := by rw [← map_pow, hs₀3, map_one]
  obtain ⟨h, hhC, hhF⟩ := D4_diagram_centralizer_Lang ℓ (by omega) L hf t₀ ht₀C
  obtain ⟨hhG, hhc⟩ := Subgroup.mem_inf.1 hhC
  have hhP : h * diagramMap TwistTag.D4 L = diagramMap TwistTag.D4 L * h :=
    Subgroup.mem_centralizer_singleton_iff.1 hhc
  have hF₁h : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) h = h * t₀ :=
    inv_mul_eq_iff_eq_mul.1 hhF
  have hF₁k : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) k' =
      (diagramMap TwistTag.D4 L)⁻¹ * k' * diagramMap TwistTag.D4 L := by
    have hcomm : (algebraMap K₃ L).comp σ.toRingHom =
        (iterateFrobenius L ℓ f).comp (algebraMap K₃ L) := by
      ext c
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [hFr, hσ, map_pow]
    have h1 := triEmb_fixed (iterateFrobenius L ℓ f) hcomm k
    rw [hF₂] at h1
    calc Units.map (entrywiseHom (iterateFrobenius L ℓ f)) k' = (diagramMap TwistTag.D4 L)⁻¹ *
        (diagramMap TwistTag.D4 L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) k' *
          (diagramMap TwistTag.D4 L)⁻¹) * diagramMap TwistTag.D4 L := by group
      _ = (diagramMap TwistTag.D4 L)⁻¹ * k' * diagramMap TwistTag.D4 L := by rw [h1]
  have hPh : diagramMap TwistTag.D4 L * h⁻¹ * (diagramMap TwistTag.D4 L)⁻¹ = h⁻¹ := by
    calc diagramMap TwistTag.D4 L * h⁻¹ * (diagramMap TwistTag.D4 L)⁻¹ =
        h⁻¹ * (h * diagramMap TwistTag.D4 L) * h⁻¹ * (diagramMap TwistTag.D4 L)⁻¹ := by group
      _ = h⁻¹ * (diagramMap TwistTag.D4 L * h) * h⁻¹ * (diagramMap TwistTag.D4 L)⁻¹ := by
          rw [hhP]
      _ = h⁻¹ := by group
  refine ⟨h * k' * g, mul_mem (mul_mem hhG (triEmb_mem_adjointGroup k)) hg, ?_,
    h * t₀ * h⁻¹, mul_mem (mul_mem hhC ht₀C) (inv_mem hhC), ?_, ?_⟩
  · rw [map_mul, map_mul, hF₁h, hF₁k, hF₁g, ← ht₀eq, hydef]
    group
  · rw [conj_pow, ht₀3]
    group
  · rw [← ht₀eq, hydef]
    calc h * k' * g * (x * (diagramMap TwistTag.D4 L)⁻¹) * (h * k' * g)⁻¹ =
        h * k' * g * x * (diagramMap TwistTag.D4 L)⁻¹ * g⁻¹ * k'⁻¹ *
          (diagramMap TwistTag.D4 L * h⁻¹ * (diagramMap TwistTag.D4 L)⁻¹) := by rw [hPh]; group
      _ = _ := by group

theorem shintani_core_d4 (hT : ThreeD4FixedNF) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (σ : K₃ ≃+* K₃) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K₃ L] [IsAlgClosure K₃ L] [CharP L ℓ]
    {x : ModGL Tag.D4 L} (hx : x ∈ adjointGroup Tag.D4 L)
    (hxF : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x)
    (hx3 : (x * (d4P L)⁻¹) ^ 3 = 1) :
    ∃ u ∈ adjointGroup Tag.D4 L, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) u = u ∧
      ∃ t ∈ graphCentralizer Tag.D4 L (d4P L), t ^ 3 = 1 ∧
        u * (x * (d4P L)⁻¹) * u⁻¹ = t * (d4P L)⁻¹ := by
  obtain ⟨u, hu, huF, t, ht, ht3, hut⟩ := shintani_core hT hℓ5 hf hK₃ σ hσ L hx hxF hx3
  exact ⟨u, hu, huF, t, ht, ht3, hut⟩

end Core

theorem graphShintaniNF_of (hT : ThreeD4FixedNF) : GraphShintaniNF := by
  intro K _ _ h5 x hx hx3
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓp⟩
  have hf : 1 ≤ (n : ℕ) := n.pos
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨K₃, _, _, _, _, hK₃, σ, hσ⟩ := D4Dual.graphType_exists_ext hf K hK
  have : Algebra.IsAlgebraic K (AlgebraicClosure K₃) :=
    Algebra.IsAlgebraic.trans K K₃ (AlgebraicClosure K₃)
  set L := AlgebraicClosure K₃
  set ι := algebraMap K L
  have hFrK : ∀ c : L, iterateFrobenius L (ringChar K) n c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def (ringChar K) n c
  have hFrι : (iterateFrobenius L (ringChar K) n).comp ι = ι := by
    ext c
    rw [RingHom.comp_apply, hFrK, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hPι : baseChangeGL ι (d4P K) = d4P L := D4Dual.graphType_baseChangeGL_d4P ι
  have hxL : baseChangeGL ι x ∈ adjointGroup Tag.D4 L :=
    baseChangeGL_mem_adjointGroup_of_mem_inndiag ι hx
  have hxF : Units.map (entrywiseHom (iterateFrobenius L (ringChar K) n)) (baseChangeGL ι x) =
      baseChangeGL ι x := by
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hFrι]
  have hx3L : (baseChangeGL ι x * (d4P L)⁻¹) ^ 3 = 1 := by
    rw [← hPι, ← map_inv, ← map_mul, ← map_pow, hx3, map_one]
  obtain ⟨u, hu, huF, t, ht, ht3, hut⟩ :=
    shintani_core_d4 hT (by omega) hf hK₃ σ hσ L hxL hxF hx3L
  obtain ⟨b, u', ⟨j, hj, rfl⟩, hub⟩ :=
    exists_rootDiagUnit_mul_of_frobenius_fixed Tag.D4 _ hFrK hu huF
  have hv : rootDiagUnit Tag.D4 b * j ∈ inndiagGroup Tag.D4 K := ⟨b, j, hj, rfl⟩
  have huv : u = baseChangeGL ι (rootDiagUnit Tag.D4 b * j) := by rw [hub, map_mul]
  set tK := (rootDiagUnit Tag.D4 b * j) * (x * (d4P K)⁻¹) * (rootDiagUnit Tag.D4 b * j)⁻¹ *
    d4P K with htKdef
  have htK : baseChangeGL ι tK = t := by
    have e : baseChangeGL ι tK = u * (baseChangeGL ι x * (d4P L)⁻¹) * u⁻¹ * d4P L := by
      rw [htKdef, huv]
      simp only [map_mul, map_inv, hPι]
    rw [e, hut]
    group
  have htK3 : tK ^ 3 = 1 := baseChangeGL_injective ι (by rw [map_pow, htK, ht3, map_one])
  have htKΓ : tK ∈ inndiagGroup Tag.D4 K := by
    have e : tK = ((rootDiagUnit Tag.D4 b * j) * x) *
        ((d4P K)⁻¹ * (rootDiagUnit Tag.D4 b * j)⁻¹ * d4P K) := by
      rw [htKdef]
      group
    rw [e]
    exact mul_mem (mul_mem hv hx) (inv_conj_d4P_mem_inndiag (inv_mem hv))
  have htKG := mem_adjointGroup_of_mem_inndiag_of_pow_three htKΓ htK3
  have htKP : d4P K * tK * (d4P K)⁻¹ = tK := by
    apply baseChangeGL_injective ι
    rw [map_mul, map_mul, map_inv, hPι, htK]
    have htc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht).2
    calc d4P L * t * (d4P L)⁻¹ = (t * d4P L) * (d4P L)⁻¹ := by rw [htc]
      _ = t := by group
  refine ⟨rootDiagUnit Tag.D4 b * j, hv, ⟨tK, htKG⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [coe_d4Graph, pow_one]
    exact htKP
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact htK3
  · show _ = tK * (d4P K)⁻¹
    rw [htKdef]
    group

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd
