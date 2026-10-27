module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4MaxBase
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.EntryLemma

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section SimplyLaced


structure SimplyLacedData (τ : Tag) : Prop where
  norm_two : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → rootNorm τ γ = 2
  connected : ∀ i j : Fin τ.rank, Relation.ReflTransGen
    (fun a b : Fin τ.rank => τ.cartan a b = -1 ∧ τ.cartan b a = -1) i j
  notG2 : τ ≠ .G2
  simple : ∀ (K : Type) [Field K] [Finite K], IsSimpleGroup ↥(adjointGroup τ K)

theorem d4SimplyLaced : SimplyLacedData Tag.D4 :=
  ⟨fun _ hγ => rootNorm_D4_two hγ, cartanD4_connected, by decide,
    fun K _ _ => isSimpleGroup_adjointGroup_D4 K⟩

variable {τ : Tag} {K : Type} [Field K]

theorem exists_weyl_move_sl (hSL : SimplyLacedData τ)
    {R : Subgroup ↥(adjointGroup τ K)}
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ R)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hn : rootNorm τ β = rootNorm τ γ) :
    ∃ r ∈ R, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ endHom K r (rootVec τ K β) = (ε : K) • rootVec τ K γ ∧
      ∀ z : RootModule τ K, (endHom K r z) (rootLabel hγ) = (ε : K) * z (rootLabel hβ) := by
  obtain ⟨j, hj, mj⟩ := exists_simple_move hw hβ
  obtain ⟨j', hj', mj'⟩ := exists_simple_move hw hγ
  have hm : WeylMove R (Pi.single j 1) (Pi.single j' 1) :=
    weylMove_of_connected hw hSL.connected j j'
  exact ((mj.trans hm (isRoot_single τ j)).trans mj'.symm (isRoot_single τ j')) hβ hγ

theorem rootVec_mem_span_orbit_sl (hSL : SimplyLacedData τ) {k : Subfield K}
    {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ K β ∈ Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} := by
  classical
  set S := Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} with hSp
  have hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ R :=
    weylElement_one_mem_of_rat k R hrat
  have hRinv : ∀ r ∈ R, ∀ v ∈ S, endHom K r v ∈ S := by
    intro r hr v hv
    refine Submodule.span_induction (p := fun v _ => endHom K r v ∈ S) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨r', hr', rfl⟩
      exact Submodule.subset_span ⟨r * r', R.mul_mem hr hr', by rw [map_mul]; rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact S.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact S.smul_mem a hx
  have transfer : ∀ {γ δ : Fin τ.rank → ℤ}, IsRoot τ γ → IsRoot τ δ →
      rootNorm τ γ = rootNorm τ δ → rootVec τ K γ ∈ S → rootVec τ K δ ∈ S := by
    intro γ δ hγ hδ hn hγS
    obtain ⟨r, hr, ε, hε, hv, -⟩ := exists_weyl_move_sl hSL hw hγ hδ hn
    have hεε : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
      rcases hε with rfl | rfl <;> simp
    have e : rootVec τ K δ = ((ε : ℤ) : K) • endHom K r (rootVec τ K γ) := by
      rw [hv, smul_smul, hεε, one_smul]
    rw [e]
    exact S.smul_mem _ (hRinv r hr _ hγS)
  have hθS : rootVec τ K θ ∈ S := Submodule.subset_span ⟨1, R.one_mem, by simp⟩
  have hsame : ∀ γ, IsRoot τ γ → rootNorm τ γ = rootNorm τ θ → rootVec τ K γ ∈ S :=
    fun γ hγ hn => transfer hθ.1 hγ hn.symm hθS
  exact hsame β hβ (by rw [hSL.norm_two β hβ, hSL.norm_two θ hθ.1])

theorem hVec_mem_span_orbit_sl (hSL : SimplyLacedData τ) {k : Subfield K}
    {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (i : Fin τ.rank) :
    hVec τ K i ∈ Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} := by
  classical
  set S := Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} with hS
  have hRinv : ∀ r ∈ R, ∀ v ∈ S, endHom K r v ∈ S := by
    intro r hr v hv
    refine Submodule.span_induction (p := fun v _ => endHom K r v ∈ S) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨r', hr', rfl⟩
      exact Submodule.subset_span ⟨r * r', R.mul_mem hr hr', by rw [map_mul]; rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact S.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact S.smul_mem a hx
  have h1 : rootVec τ K (-Pi.single i 1) ∈ S :=
    rootVec_mem_span_orbit_sl hSL hrat hθ (isRoot_neg_single τ i)
  have h2 : rootVec τ K (Pi.single i 1) ∈ S :=
    rootVec_mem_span_orbit_sl hSL hrat hθ (isRoot_single τ i)
  have hxr : xPar (rootOperatorFamily τ) (Pi.single i 1) (1 : K) ∈ R :=
    hrat _ (isRoot_single τ i) 1 k.one_mem
  have h4 := hRinv _ hxr _ h1
  have e : endHom K (xPar (rootOperatorFamily τ) (Pi.single i 1) (1 : K)) = xOp τ K i 1 := by
    rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
  rw [e, CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single] at h4
  have h5 := S.sub_mem (S.sub_mem h4 h1) h2
  convert h5 using 1
  module

theorem span_orbit_eq_top_sl (hSL : SimplyLacedData τ) {k : Subfield K}
    {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) :
    Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} = ⊤ := by
  rw [eq_top_iff, ← (Finsupp.basisSingleOne (R := K) (ι := Label τ)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, rfl⟩
  rw [Finsupp.coe_basisSingleOne]
  rcases b with i | ⟨β, hβ⟩
  · exact hVec_mem_span_orbit_sl hSL hrat hθ i
  · have := rootVec_mem_span_orbit_sl hSL hrat hθ hβ
    rwa [rootVec_of_isRoot' hβ] at this

theorem endHom_xPar_simple_poly_sl (hSL : SimplyLacedData τ) (i : Fin τ.rank) :
    (∃ X₁ X₂ : Module.End K (RootModule τ K), ∀ c : K,
        endHom K (xPar (rootOperatorFamily τ) (Pi.single i 1) c) = 1 + c • X₁ + c ^ 2 • X₂) ∧
      (∃ X₁ X₂ : Module.End K (RootModule τ K), ∀ c : K,
        endHom K (xPar (rootOperatorFamily τ) (-Pi.single i 1) c) = 1 + c • X₁ + c ^ 2 • X₂) := by
  have hG2 : τ ≠ .G2 := hSL.notG2
  have hb : entryDegreeBound τ = 2 := by simp [entryDegreeBound, hG2]
  constructor
  · refine ⟨xCoeff τ K i 1, xCoeff τ K i 2, fun c => ?_⟩
    have e : endHom K (xPar (rootOperatorFamily τ) (Pi.single i 1) c) = xOp τ K i c := by
      rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
    rw [e, xOp_eq_sum_xCoeff_entryDegreeBound, hb]
    simp [Finset.sum_range_succ, xCoeff_zero, add_assoc]
  · refine ⟨yCoeff τ K i 1, yCoeff τ K i 2, fun c => ?_⟩
    have e : endHom K (xPar (rootOperatorFamily τ) (-Pi.single i 1) c) = yOp τ K i c := by
      rw [xPar_neg_simple, endHom_eltElement, (rootOperatorFamily τ).elt_neg_simple]
    rw [e, yOp_eq_sum_yCoeff_entryDegreeBound, hb]
    simp [Finset.sum_range_succ, yCoeff_zero, add_assoc]

theorem vanishSub_invariant_sl (hSL : SimplyLacedData τ) {k : Subfield K}
    (h3 : 3 ≤ Nat.card k) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    (a : Label τ) (x : ↥(adjointGroup τ K)) {z : RootModule τ K} (hz : z ∈ vanishSub R a) :
    endHom K x z ∈ vanishSub R a := by
  classical
  set Z := vanishSub R a with hZ
  let Stab : Subgroup ↥(adjointGroup τ K) :=
    { carrier := {g | (∀ z ∈ Z, endHom K g z ∈ Z) ∧ (∀ z ∈ Z, endHom K g⁻¹ z ∈ Z)}
      one_mem' := ⟨fun z hz => by simpa using hz, fun z hz => by simpa using hz⟩
      mul_mem' := fun {g₁ g₂} h1 h2 => ⟨fun z hz => by
          rw [map_mul, Module.End.mul_apply]
          exact h1.1 _ (h2.1 z hz), fun z hz => by
          rw [mul_inv_rev, map_mul, Module.End.mul_apply]
          exact h2.2 _ (h1.2 z hz)⟩
      inv_mem' := fun {g} h => ⟨h.2, fun z hz => by simpa using h.1 z hz⟩ }
  have hinvgen : ∀ (i : Fin τ.rank) (c : K), xPar (rootOperatorFamily τ) (Pi.single i 1) c ∈ Stab ∧
      xPar (rootOperatorFamily τ) (-Pi.single i 1) c ∈ Stab := by
    intro i c
    obtain ⟨⟨X₁, X₂, hX⟩, ⟨Y₁, Y₂, hY⟩⟩ := endHom_xPar_simple_poly_sl (K := K) hSL i
    have key : ∀ (γ : Fin τ.rank → ℤ) (hγ : IsRoot τ γ) (X₁ X₂ : Module.End K (RootModule τ K)),
        (∀ c : K, endHom K (xPar (rootOperatorFamily τ) γ c) = 1 + c • X₁ + c ^ 2 • X₂) →
        ∀ c : K, ∀ z ∈ Z, endHom K (xPar (rootOperatorFamily τ) γ c) z ∈ Z := by
      intro γ hγ X₁ X₂ hX c z hz
      have h0 : ∀ c ∈ k, ∀ z ∈ Z, z + c • X₁ z + c ^ 2 • X₂ z ∈ Z := by
        intro c₀ hc₀ z hz
        have := hz
        have hr := hz
        have := (mem_vanishSub.1 hz)
        have hxR : xPar (rootOperatorFamily τ) γ c₀ ∈ R := hrat γ hγ c₀ hc₀
        have hRinv : endHom K (xPar (rootOperatorFamily τ) γ c₀) z ∈ Z := by
          refine mem_vanishSub.2 fun r hr => ?_
          rw [← Module.End.mul_apply, ← map_mul]
          exact mem_vanishSub.1 hz (r * xPar (rootOperatorFamily τ) γ c₀) (R.mul_mem hr hxR)
        rw [hX c₀] at hRinv
        simpa [add_assoc] using hRinv
      have := poly_invariant Z X₁ X₂ h3 h0 c hz
      rw [hX c]
      simpa [add_assoc] using this
    have hneg : ∀ (γ : Fin τ.rank → ℤ) (c : K), (xPar (rootOperatorFamily τ) γ c)⁻¹ =
        xPar (rootOperatorFamily τ) γ (-c) := fun γ c => xPar_neg γ c
    refine ⟨⟨key _ (isRoot_single τ i) X₁ X₂ hX c, ?_⟩, ⟨key _ (isRoot_neg_single τ i) Y₁ Y₂ hY c, ?_⟩⟩
    · rw [hneg]
      exact key _ (isRoot_single τ i) X₁ X₂ hX (-c)
    · rw [hneg]
      exact key _ (isRoot_neg_single τ i) Y₁ Y₂ hY (-c)
  have htop : Stab = ⊤ := by
    set S : Set (ModGL τ K) := {g | ∃ (i : Fin τ.rank) (c : K),
      (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
        (g : Module.End K (RootModule τ K)) = yOp τ K i c} with hS
    have hcl : Subgroup.closure (((↑) : ↥(adjointGroup τ K) → ModGL τ K) ⁻¹' S) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have e : g = xPar (rootOperatorFamily τ) (Pi.single i 1) c := endHom_injective (by
        rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
        exact hg)
      rw [e]
      exact (hinvgen i c).1
    · have e : g = xPar (rootOperatorFamily τ) (-Pi.single i 1) c := endHom_injective (by
        rw [xPar_neg_simple, endHom_eltElement, (rootOperatorFamily τ).elt_neg_simple]
        exact hg)
      rw [e]
      exact (hinvgen i c).2
  have hxS : x ∈ Stab := by rw [htop]; trivial
  exact hxS.1 z hz

theorem vanishSub_rootCoord_sl (hSL : SimplyLacedData τ) {k : Subfield K}
    {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) {z : RootModule τ K}
    (hz : z ∈ vanishSub R (negLabel hθ.1)) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hn : rootNorm τ β = rootNorm τ θ) : z (rootLabel hβ) = 0 := by
  have hw := weylElement_one_mem_of_rat k R hrat
  obtain ⟨r, hr, ε, hε, -, hcoord⟩ := exists_weyl_move_sl hSL hw hβ (isRoot_neg_iff.2 hθ.1)
    (hn.trans (rootNorm_neg θ).symm)
  have h0 := mem_vanishSub.1 hz r hr
  rw [hcoord z] at h0
  rcases hε with rfl | rfl <;> simpa using h0

theorem eq_one_of_sub_mem_vanishSub_sl (hSL : SimplyLacedData τ) [Finite K]
    {k : Subfield K} (h3 : 3 ≤ Nat.card k) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (x : ↥(adjointGroup τ K))
    (hx : ∀ v : RootModule τ K, endHom K x v - v ∈ vanishSub R (negLabel hθ.1)) : x = 1 := by
  classical
  set Z := vanishSub R (negLabel hθ.1) with hZ
  have hinv : ∀ y : ↥(adjointGroup τ K), ∀ z ∈ Z, endHom K y z ∈ Z := fun y z hz =>
    vanishSub_invariant_sl hSL h3 hrat _ y hz
  let N : Subgroup ↥(adjointGroup τ K) :=
    { carrier := {y | ∀ v : RootModule τ K, endHom K y v - v ∈ Z}
      one_mem' := fun v => by simp
      mul_mem' := fun {y₁ y₂} h1 h2 v => by
        have e : endHom K (y₁ * y₂) v - v =
            endHom K y₁ (endHom K y₂ v - v) + (endHom K y₁ v - v) := by
          rw [map_mul, Module.End.mul_apply, map_sub]
          abel
        rw [e]
        exact Z.add_mem (hinv y₁ _ (h2 v)) (h1 v)
      inv_mem' := fun {y} h v => by
        have e : endHom K y⁻¹ v - v = -(endHom K y (endHom K y⁻¹ v) - endHom K y⁻¹ v) := by
          have : endHom K y (endHom K y⁻¹ v) = v := by
            rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
          rw [this]
          abel
        rw [e]
        exact Z.neg_mem (h _) }
  have hNn : N.Normal := ⟨fun y hy h v => by
    have e : endHom K (h * y * h⁻¹) v - v = endHom K h (endHom K y (endHom K h⁻¹ v) - endHom K h⁻¹ v) := by
      have : endHom K h (endHom K h⁻¹ v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, map_sub, this]
    rw [e]
    exact hinv h _ (hy _)⟩
  haveI := hSL.simple K
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · have hxN : x ∈ N := hx
    rw [h] at hxN
    exact (Subgroup.mem_bot.1 hxN)
  · exfalso
    have hmem : xPar (rootOperatorFamily τ) θ (1 : K) ∈ N := by rw [h]; trivial
    have h1 := hmem (rootVec τ K (-θ))
    have h2 := vanishSub_rootCoord_sl hSL hrat hθ h1 hθ.1 rfl
    apply xPar_apply_neg_root_coord hθ.1 (K := K)
    have hv : (rootVec τ K (-θ)) (rootLabel hθ.1) = 0 := by
      rw [rootVec_of_isRoot' (isRoot_neg_iff.2 hθ.1)]
      have hne : (rootLabel hθ.1 : Label τ) ≠ negLabel hθ.1 := by
        intro hh
        have hh' : θ = -θ := by simpa using hh
        have := hθ.height_pos
        have h3' := congrArg height hh'
        simp only [height, Pi.neg_apply, Finset.sum_neg_distrib] at h3'
        simp only [height] at this
        omega
      simp [Finsupp.single_apply, hne]
    simpa [hv] using h2

theorem mem_subfieldGroup_of_entries_sl (hSL : SimplyLacedData τ) [Finite K]
    (σ : K ≃+* K) (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ))
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K))
    (hall : ∀ r ∈ subfieldGroup τ σ, ∀ r' ∈ subfieldGroup τ σ,
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield σ) :
    g ∈ subfieldGroup τ σ := by
  classical
  set k := fixSubfield σ with hk
  set R := subfieldGroup τ σ with hR
  have h3 : 3 ≤ Nat.card k := three_le_card_fixSubfield σ hD
  have hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R :=
    fun γ _ c hc => xPar_mem_subfieldGroup τ σ γ hc
  set g₂ : ↥(adjointGroup τ K) := entrywiseAdjointAut τ σ g with hg₂
  have hRfix : ∀ r ∈ R, entrywiseAdjointAut τ σ r = r := fun r hr => mem_fixedSubgroup.1 hr
  have hent : ∀ r ∈ R, ∀ r' ∈ R, entry (r * g₂ * r') (negLabel hθ.1) (rootLabel hθ.1) =
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) := by
    intro r hr r' hr'
    have e : r * g₂ * r' = entrywiseAdjointAut τ σ (r * g * r') := by
      rw [map_mul, map_mul, hRfix r hr, hRfix r' hr']
    rw [e, entry_entrywiseAdjointAut]
    exact (mem_fixSubfield σ).1 (hall r hr r' hr')
  set Z := vanishSub R (negLabel hθ.1) with hZ
  have hDmem : ∀ r' ∈ R, (endHom K g₂ - endHom K g) (endHom K r' (rootVec τ K θ)) ∈ Z := by
    intro r' hr'
    refine mem_vanishSub.2 fun r hr => ?_
    have hv : rootVec τ K θ = Finsupp.single (rootLabel hθ.1) 1 := rootVec_of_isRoot' hθ.1
    have h1 := hent r hr r' hr'
    unfold entry at h1
    rw [hv]
    simp only [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, ← Module.End.mul_apply, ← map_mul] at h1 ⊢
    rw [sub_eq_zero]
    simpa [mul_assoc, Module.End.mul_apply] using h1
  have hspan := span_orbit_eq_top_sl hSL hrat hθ
  have hle : Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} ≤
      Z.comap (endHom K g₂ - endHom K g) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨r', hr', rfl⟩
    exact hDmem r' hr'
  rw [hspan] at hle
  have hDV : ∀ v, (endHom K g₂ - endHom K g) v ∈ Z := fun v => hle (Submodule.mem_top (x := v))
  have hx : ∀ v : RootModule τ K, endHom K (g₂ * g⁻¹) v - v ∈ Z := by
    intro v
    have h1 := hDV (endHom K g⁻¹ v)
    have e1 : endHom K g (endHom K g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.sub_apply, e1] at h1
    rw [map_mul, Module.End.mul_apply]
    exact h1
  have h1 := eq_one_of_sub_mem_vanishSub_sl hSL h3 hrat hθ (g₂ * g⁻¹) hx
  have h2 : g₂ = g := mul_inv_eq_one.1 h1
  rw [hR, subfieldGroup, mem_fixedSubgroup]
  exact h2

theorem exists_bad_entry_sl (hSL : SimplyLacedData τ) [Finite K] (σ : K ≃+* K)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ)) {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K)) (hg : g ∉ subfieldGroup τ σ) :
    ∃ r ∈ subfieldGroup τ σ, ∃ r' ∈ subfieldGroup τ σ,
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield σ := by
  by_contra h
  push Not at h
  exact hg (mem_subfieldGroup_of_entries_sl hSL σ hD hθ g h)

end SimplyLaced

end CFSG.LieType.SeitzGeneration.ExcWideThree
