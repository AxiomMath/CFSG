module

public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Curtis

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.Quasithin.SmithCurtis
open Module
open Representation
open scoped MonoidAlgebra TensorProduct

section Generic

variable {F : Type*} [Field F] [Finite F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] (ρ : Representation F G V) [IsIrreducible ρ]

theorem endField_charP (p : ℕ) [CharP F p] : CharP (End F[G] ρ.asModule) p := by
  refine (CharP.charP_iff_prime_eq_zero (CharP.char_is_prime F p)).2 ?_
  ext m
  change (p : Module.End F[G] ρ.asModule) m = 0
  rw [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p, zero_smul]

section Descent

variable {p : ℕ} [Fact p.Prime] [Finite G]
  {B : Type*} {M : CoxeterMatrix B} {Weyl : Type*} [Group Weyl] {cs : CoxeterSystem M Weyl}

omit [Fact p.Prime] in
theorem heckeT_extendScalars_tmul (D : CurtisDatum G cs p) {K : Type*} [Field K]
    {W : Type*} [AddCommGroup W] [Module K W] (σ : Representation K G W) (k : Type*) [Field k]
    [Algebra K k] (s : B) (a : k) (w : W) :
    D.heckeT (Theory.Representation.extendScalars k σ) s (a ⊗ₜ w) = a ⊗ₜ D.heckeT σ s w := by
  classical
  have := Fintype.ofFinite (D.X s)
  rw [D.heckeT_apply (Theory.Representation.extendScalars k σ) s (a ⊗ₜ w),
    D.heckeT_apply σ s w]
  simp only [Theory.Representation.extendScalars_apply, LinearMap.baseChange_tmul,
    TensorProduct.tmul_sum]

private theorem exists_scalar_of_baseChange_smul
    {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    {k : Type*} [Field k] [Algebra K k] {C : Submodule K M} {v : M}
    (hline : ∀ x ∈ C, ∃ c : K, c • v = x)
    (h10 : (1 : k) ⊗ₜ[K] v ≠ 0)
    (T : M →ₗ[K] M) (hT : T v ∈ C) (b : k)
    (hb : T.baseChange k ((1 : k) ⊗ₜ[K] v) = b • ((1 : k) ⊗ₜ[K] v)) :
    ∃ c : K, T v = c • v ∧ b = algebraMap K k c := by
  obtain ⟨c, hc⟩ := hline (T v) hT
  refine ⟨c, hc.symm, ?_⟩
  have hbase : T.baseChange k ((1 : k) ⊗ₜ[K] v) =
      algebraMap K k c • ((1 : k) ⊗ₜ[K] v) := by
    rw [LinearMap.baseChange_tmul, ← hc, TensorProduct.tmul_smul]
    simp
  exact smul_left_injective k h10 (hb.symm.trans hbase)

theorem exists_isCurtisType_endField (D : CurtisDatum G cs p)
    (k : Type*) [Field k] [CharP k p] [Algebra (End F[G] ρ.asModule) k]
    {y : k ⊗[End F[G] ρ.asModule] ρ.asModule} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType (Theory.Representation.extendScalars k (endFieldRep ρ)) y χ μ) :
    ∃ (yR : ρ.asModule) (χR : G → End F[G] ρ.asModule) (μR : B → End F[G] ρ.asModule),
      D.IsCurtisType (endFieldRep ρ) yR χR μR ∧
        (∀ h ∈ D.H, χ h = algebraMap (End F[G] ρ.asModule) k (χR h)) ∧
        ∀ s, μ s = algebraMap (End F[G] ρ.asModule) k (μR s) := by
  classical
  let K := End F[G] ρ.asModule
  let σ := endFieldRep ρ
  let W := Theory.Representation.extendScalars k σ
  have : Finite V := Module.finite_iff_finite.mp ‹FiniteDimensional F V›
  have : FiniteDimensional K ρ.asModule := finiteDimensional_endField ρ
  have : IsIrreducible W := extendScalars_isIrreducible ρ k
  have hsimple : IsSimpleRep W := isSimpleRep_of_isIrreducible W
  have hdimW : finrank k (D.fixU W) = 1 := by
    rw [D.fixU_eq_span hsimple ht, finrank_span_singleton ht.2.1]
  have hdimK : finrank K (D.fixU σ) = 1 := by
    change finrank K (fixSubGen σ D.U) = 1
    rw [← finrank_fixSubGen_extendScalars ρ k D.U]
    exact hdimW
  have : Module.Free K ↥(D.fixU σ) := Module.Free.of_divisionRing K _
  obtain ⟨⟨v, hvmem⟩, hv0sub, hspan⟩ := finrank_eq_one_iff'.mp hdimK
  have hv0 : v ≠ 0 := fun hv => hv0sub (Subtype.ext hv)
  have hline : ∀ x ∈ D.fixU σ, ∃ c : K, c • v = x := by
    intro x hx
    obtain ⟨c, hc⟩ := hspan ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have h10 : (1 : k) ⊗ₜ[K] v ≠ 0 := by
    intro hz
    exact hv0 ((Module.FaithfullyFlat.one_tmul_eq_zero_iff K ρ.asModule (A := k) v).mp hz)
  have h1 : ((1 : k) ⊗ₜ[K] v) ∈ D.fixU W := by
    intro u hu
    show W u ((1 : k) ⊗ₜ[K] v) = (1 : k) ⊗ₜ[K] v
    rw [show W u = (σ u).baseChange k from rfl, LinearMap.baseChange_tmul, hvmem u hu]
  obtain ⟨a, ha⟩ := D.fixU_eq_smul hsimple ht h1
  have htW : D.IsCurtisType W ((1 : k) ⊗ₜ[K] v) χ μ := by
    refine ⟨h1, h10, ?_, ?_⟩
    · intro h hh
      rw [ha, map_smul, ht.2.2.1 h hh, smul_comm]
    · intro s
      rw [ha, map_smul, ht.2.2.2 s, smul_comm]
  have hχ' : ∀ h : G, h ∈ D.H → ∃ c : K, σ h v = c • v ∧ χ h = algebraMap K k c := by
    intro h hh
    exact exists_scalar_of_baseChange_smul hline h10 (σ h)
      (D.act_H_mem_fixU σ hh hvmem) (χ h) (htW.2.2.1 h hh)
  have hμ' : ∀ s : B, ∃ c : K, D.heckeT σ s v = c • v ∧ μ s = algebraMap K k c := by
    intro s
    have heq : (D.heckeT σ s).baseChange k ((1 : k) ⊗ₜ[K] v) =
        μ s • ((1 : k) ⊗ₜ[K] v) := by
      rw [LinearMap.baseChange_tmul, ← heckeT_extendScalars_tmul D σ k s (1 : k) v]
      exact htW.2.2.2 s
    exact exists_scalar_of_baseChange_smul hline h10 (D.heckeT σ s)
      (D.heckeT_mem_fixU σ s hvmem) (μ s) heq
  let χR : G → K := fun h => if hh : h ∈ D.H then (hχ' h hh).choose else 0
  have hχR : ∀ h (hh : h ∈ D.H), σ h v = χR h • v ∧ χ h = algebraMap K k (χR h) := by
    intro h hh
    rw [show χR h = (hχ' h hh).choose from dif_pos hh]
    exact (hχ' h hh).choose_spec
  let μR : B → K := fun s => (hμ' s).choose
  have hμR : ∀ s, D.heckeT σ s v = μR s • v ∧ μ s = algebraMap K k (μR s) :=
    fun s => (hμ' s).choose_spec
  exact ⟨v, χR, μR, ⟨hvmem, hv0, fun h hh => (hχR h hh).1, fun s => (hμR s).1⟩,
    fun h hh => (hχR h hh).2, fun s => (hμR s).2⟩

end Descent

section Converse

variable {p : ℕ} [Fact p.Prime] [Finite G]
  {B : Type*} {M : CoxeterMatrix B} {Weyl : Type*} [Group Weyl] {cs : CoxeterSystem M Weyl}

private noncomputable def restrictRep (C : Subfield (End F[G] ρ.asModule)) :
    Representation C G ρ.asModule where
  toFun g := (endFieldRep ρ g).restrictScalars C
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [Finite G] in
private theorem restrictRep_apply (C : Subfield (End F[G] ρ.asModule)) (g : G)
    (m : ρ.asModule) : restrictRep ρ C g m = endFieldRep ρ g m := rfl

omit [Finite G] in
private theorem isSimpleRep_restrictRep (C : Subfield (End F[G] ρ.asModule))
    (hF : ∀ f : F, f • (1 : End F[G] ρ.asModule) ∈ C) : IsSimpleRep (restrictRep ρ C) := by
  refine ⟨Subrepresentation.irreducible_module_nontrivial (F := F) (G := G) (V := V) (ρ := ρ),
    fun S hS => ?_⟩
  let S' : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := S.carrier
          add_mem' := S.add_mem'
          zero_mem' := S.zero_mem
          smul_mem' := fun f m hm => S.smul_mem (⟨f • 1, hF f⟩ : C) hm }
      apply_mem_toSubmodule := fun g m hm => hS g m hm }
  rcases (inferInstance : IsIrreducible ρ).eq_bot_or_eq_top S' with h | h
  · refine Or.inl (eq_bot_iff.mpr fun m hm => (Submodule.mem_bot C).mpr ?_)
    have hm' : (m : V) ∈ S'.toSubmodule := hm
    rw [congrArg Subrepresentation.toSubmodule h] at hm'
    exact (Submodule.mem_bot (R := F) (M := V) (x := (m : V))).mp hm'
  · refine Or.inr (eq_top_iff.mpr fun m _ => ?_)
    have hm' : (m : V) ∈ S'.toSubmodule := by
      rw [congrArg Subrepresentation.toSubmodule h]
      exact Submodule.mem_top (R := F) (M := V) (x := (m : V))
    exact hm'

theorem isCurtisType_subfield_eq_top_of_smul_one_mem [CharP F p] (D : CurtisDatum G cs p)
    {yR : ρ.asModule} {χR : G → End F[G] ρ.asModule} {μR : B → End F[G] ρ.asModule}
    (htR : D.IsCurtisType (endFieldRep ρ) yR χR μR) (C : Subfield (End F[G] ρ.asModule))
    (hF : ∀ f : F, f • (1 : End F[G] ρ.asModule) ∈ C) (hC : ∀ h ∈ D.H, χR h ∈ C) :
    C = ⊤ := by
  classical
  have hcharR : CharP (End F[G] ρ.asModule) p := endField_charP ρ p
  have hμ : ∀ s, μR s ∈ C := by
    intro s
    rcases htR.mu_eq s with h | h
    · rw [h]; exact C.zero_mem
    · rw [h]
      have := Fintype.ofFinite (D.X s)
      unfold CurtisDatum.d'Scalar
      exact C.sum_mem fun x hx => hC _ (D.psi_mem s x x.2 fun hx1 =>
        Finset.ne_of_mem_erase hx (OneMemClass.coe_eq_one.mp hx1))
  let χC : G → C := fun h => if hh : h ∈ D.H then ⟨χR h, hC h hh⟩ else 0
  let μC : B → C := fun s => ⟨μR s, hμ s⟩
  have htC : D.IsCurtisType (restrictRep ρ C) yR χC μC := by
    refine ⟨htR.1, htR.2.1, fun h hh => ?_, fun s => ?_⟩
    · rw [restrictRep_apply, htR.2.2.1 h hh]
      simp only [χC, dif_pos hh, Subfield.smul_def]
    · have hT : D.heckeT (restrictRep ρ C) s yR = D.heckeT (endFieldRep ρ) s yR := by
        have := Fintype.ofFinite (D.X s)
        rw [D.heckeT_apply (restrictRep ρ C) s, D.heckeT_apply (endFieldRep ρ) s]
        rfl
      rw [hT, htR.2.2.2 s]
      simp only [μC, Subfield.smul_def]
  have hcharC : CharP C p := Subfield.charP C p
  have hspan := D.fixU_eq_span (ρ := restrictRep ρ C) (isSimpleRep_restrictRep ρ C hF) htC
  refine Subfield.ext fun r => ⟨fun _ => Subfield.mem_top r, fun _ => ?_⟩
  have hyU : r • yR ∈ D.fixU (restrictRep ρ C) := by
    intro u hu
    rw [restrictRep_apply, map_smul, htR.1 u hu]
  rw [hspan, Submodule.mem_span_singleton] at hyU
  obtain ⟨c, hc⟩ := hyU
  have hc' : (c : End F[G] ρ.asModule) • yR = r • yR := by
    rwa [Subfield.smul_def] at hc
  have hcr : (c : End F[G] ρ.asModule) = r :=
    smul_left_injective (End F[G] ρ.asModule) htR.2.1 hc'
  rw [← hcr]
  exact c.2

end Converse

end Generic

section Binary

variable {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
  {B : Type*} {M : CoxeterMatrix B} {Weyl : Type*} [Group Weyl] {cs : CoxeterSystem M Weyl}

theorem isCurtisType_subfield_eq_top (D : CurtisDatum G cs 2)
    {yR : ρ.asModule} {χR : G → End (ZMod 2)[G] ρ.asModule} {μR : B → End (ZMod 2)[G] ρ.asModule}
    (htR : D.IsCurtisType (endFieldRep ρ) yR χR μR) (C : Subfield (End (ZMod 2)[G] ρ.asModule))
    (hC : ∀ h ∈ D.H, χR h ∈ C) : C = ⊤ := by
  refine isCurtisType_subfield_eq_top_of_smul_one_mem ρ D htR C ?_ hC
  intro f
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) f with rfl | rfl
  · rw [zero_smul]
    exact C.zero_mem
  · rw [one_smul]
    exact C.one_mem

theorem isCurtisType_chi_mem_subfield_iff (D : CurtisDatum G cs 2)
    (k : Type*) [Field k] [CharP k 2] [Algebra (End (ZMod 2)[G] ρ.asModule) k]
    {y : k ⊗[End (ZMod 2)[G] ρ.asModule] ρ.asModule} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType (Theory.Representation.extendScalars k (endFieldRep ρ)) y χ μ)
    (C : Subfield k) :
    (∀ h ∈ D.H, χ h ∈ C) ↔ ∀ r : End (ZMod 2)[G] ρ.asModule,
      algebraMap (End (ZMod 2)[G] ρ.asModule) k r ∈ C := by
  constructor
  · intro hχC r
    obtain ⟨yR, χR, μR, htR, hχ, -⟩ := exists_isCurtisType_endField ρ D k ht
    let C' : Subfield (End (ZMod 2)[G] ρ.asModule) := C.comap (algebraMap _ k)
    have hC' : ∀ h ∈ D.H, χR h ∈ C' := by
      intro h hh
      rw [Subfield.mem_comap, ← hχ h hh]
      exact hχC h hh
    have htop : C' = ⊤ := isCurtisType_subfield_eq_top ρ D htR C' hC'
    have hmem : r ∈ C' := htop ▸ Subfield.mem_top r
    rwa [Subfield.mem_comap] at hmem
  · intro hC h hh
    obtain ⟨c, hc⟩ := isCurtisType_chi_mem_endField ρ D k ht h hh
    rw [hc]
    exact hC c

theorem isCurtisType_fieldRange_eq_closure (D : CurtisDatum G cs 2)
    (k : Type*) [Field k] [CharP k 2] [Algebra (End (ZMod 2)[G] ρ.asModule) k]
    {y : k ⊗[End (ZMod 2)[G] ρ.asModule] ρ.asModule} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType (Theory.Representation.extendScalars k (endFieldRep ρ)) y χ μ) :
    (algebraMap (End (ZMod 2)[G] ρ.asModule) k).fieldRange =
      Subfield.closure (χ '' (D.H : Set G)) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨r, rfl⟩
    exact (isCurtisType_chi_mem_subfield_iff ρ D k ht
      (Subfield.closure (χ '' (D.H : Set G)))).mp
        (fun h hh => Subfield.subset_closure ⟨h, hh, rfl⟩) r
  · rw [Subfield.closure_le]
    rintro x ⟨h, hh, rfl⟩
    obtain ⟨c, hc⟩ := isCurtisType_chi_mem_endField ρ D k ht h hh
    rw [hc]
    exact RingHom.mem_fieldRange.mpr ⟨c, rfl⟩

theorem card_endField_eq_two_of_isCurtisType (D : CurtisDatum G cs 2) (hH : ∀ h ∈ D.H, h = 1)
    {yR : ρ.asModule} {χR : G → End (ZMod 2)[G] ρ.asModule} {μR : B → End (ZMod 2)[G] ρ.asModule}
    (htR : D.IsCurtisType (endFieldRep ρ) yR χR μR) :
    Nat.card (End (ZMod 2)[G] ρ.asModule) = 2 := by
  have : CharP (End (ZMod 2)[G] ρ.asModule) 2 := endField_charP ρ 2
  let φ : ZMod 2 →+* End (ZMod 2)[G] ρ.asModule := ZMod.castHom (dvd_refl 2) _
  have hC : ∀ h ∈ D.H, χR h ∈ φ.fieldRange := by
    intro h hh
    rw [hH h hh, htR.chi_one]
    exact φ.fieldRange.one_mem
  have htop : φ.fieldRange = ⊤ := isCurtisType_subfield_eq_top ρ D htR φ.fieldRange hC
  have hsurj : Function.Surjective φ := by
    intro r
    exact RingHom.mem_fieldRange.mp (htop ▸ Subfield.mem_top r)
  have hle : Nat.card (End (ZMod 2)[G] ρ.asModule) ≤ Nat.card (ZMod 2) :=
    Nat.card_le_card_of_surjective φ hsurj
  have hz : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hgt : 1 < Nat.card (End (ZMod 2)[G] ρ.asModule) := Finite.one_lt_card
  omega

end Binary

end CFSG.HardMathSupport.GuralnickMalle
