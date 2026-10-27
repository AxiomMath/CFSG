module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4ThreeOdd
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.ActorTools
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenActorTools
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenCyclotomicThree

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.F4Weyl CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical SteinbergBN
  CFSG.RankThree.Chevalley.EvenF4Actors CFSG.RankThree.Chevalley.EvenF4QPlus
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open scoped Pointwise commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

section Actor

variable (K : Type) [Field K] [Finite K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (F : Ω →+* Ω)

theorem f4ThreeActor_even {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1) {g : ModGL Tag.F4 Ω}
    (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g =
      canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 4))
    {x : ModGL Tag.F4 Ω} (hx : x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹)
    (hxp : orderOf x = p) (hne : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty)
    {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹) :
    F4FourActorAt K Ω p g x x₁ := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  obtain ⟨K₃, hK₃⟩ := exists_intermediateField_finrank K Ω 3
  have : FiniteDimensional K K₃ := Module.finite_of_finrank_eq_succ hK₃
  have : Finite K₃ := Module.finite_of_finite K
  obtain ⟨n, hn⟩ : ∃ n, n = canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 4) := ⟨_, rfl⟩
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, T₀ = torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹ := ⟨_, rfl⟩
  have hεw : ((1 : ℤ) = 1 ∧ f4Coxeter ^ 4 = f4Coxeter ^ 4 ∧
      p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      ((1 : ℤ) = -1 ∧ f4Coxeter ^ 4 = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1) :=
    Or.inl ⟨rfl, rfl, hpd⟩
  obtain ⟨-, -, hcls⟩ := (F4_three_six_torus_data K Ω F hF hεw hp hp3).2 g hg hgn
  rw [← hn] at hgn
  have hx' : x ∈ T₀ := hT₀ ▸ hx
  obtain ⟨u, κ, δ, hδ, hu, huw⟩ := ((hcls x hx hxp).1).resolve_left hne.ne_empty
  obtain ⟨h, hh⟩ : ∃ h, h = canonicalRep (coxeterSystem Tag.F4) Ω u := ⟨_, rfl⟩
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ₁, Γ₁ = (conjEntrywiseImage K g⁻¹).map (MulAut.conj h).toMonoidHom :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = Γ₁ ⊓ centralizer {h * x * h⁻¹} := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = ⁅D, D⁆ := ⟨_, rfl⟩
  obtain ⟨-, a, ha, hRQ, hRQK, hRq, -, -, -, hcent, hZT, hZodd, hSL2, x₀, hx₀, hCx, hR₀', hq₀,
      -, -, -, R₀, hR₀le, k, hk, hRk⟩ :=
    even_F4_cyclotomic_three_nonregular_derived_centralizer K hK Ω F hF hp hp3 K₃ hK₃ n g hn hg
      hgn _ T₀ rfl hT₀ x hx' hxp κ u δ hδ hu (by simpa using huw) h (h * x * h⁻¹) hh rfl Γ₁ D R
      hΓ₁ hD hR
  have hx₀₁ : x₀ = x₁ :=
    Subtype.ext (baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω) (hx₀.trans hx₁.symm))
  subst hx₀₁
  have hinjK := baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω)
  have hι'inj : Function.Injective ((baseChangeGL (algebraMap K Ω)).comp
      (adjointGroup Tag.F4 K).subtype) := hinjK.comp Subtype.val_injective
  subst hR
  obtain ⟨-, hdz, hcentr, hodd⟩ := centralizer_layer_of_transport _ hι'inj
    (MulAut.conj (g * h⁻¹)) _ D hCx hcent hZodd
  have hcardR : Nat.card (⁅D, D⁆ : Subgroup (ModGL Tag.F4 Ω)) = Nat.card SL(3, K) := by
    rw [hRQ, hRQK, Subgroup.card_map_of_injective (MulAut.conj _).injective,
      Subgroup.card_map_of_injective hinjK]
    exact Nat.card_congr (f4A2Equiv K κ).toEquiv
  have hpR : ¬ Nat.Coprime p (Nat.card (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K))) := by
    have hcard : Nat.card (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
        centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) =
        Nat.card (⁅D, D⁆ : Subgroup (ModGL Tag.F4 Ω)) := by
      rw [← Subgroup.card_map_of_injective hι'inj, hR₀',
        Subgroup.card_map_of_injective (MulAut.conj (g * h⁻¹)).injective]
    rw [hcard, hcardR]
    exact fun hc' => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc' dvd_rfl
      (p_dvd_card_SL3 hp hp3 hpd))
  have hRg : (R₀.map ((baseChangeGL (algebraMap K K₃)).comp (adjointGroup Tag.F4 K).subtype)).map
      (MulAut.conj k).toMonoidHom =
      ((Matrix.SpecialLinearGroup.map (algebraMap K K₃)).range.map
        (CFSG.RankThree.Classical.conjSL 1)).map (rootSL2 Tag.F4 K₃ (Pi.single κ.i 1)) := by
    have hid : ∀ H : Subgroup (SL2 K₃), H.map (CFSG.RankThree.Classical.conjSL 1) = H :=
      fun H => by
        ext A
        constructor
        · rintro ⟨A', hA', rfl⟩
          rwa [CFSG.RankThree.Classical.conjSL_one]
        · intro hA
          exact ⟨A, hA, CFSG.RankThree.Classical.conjSL_one A⟩
    rw [hRk, MonoidHom.range_comp, hid]
  refine ⟨hq₀, hpR, fun η hηx hηR => exists_inner_of_fixes_layer x₀ hcentr hodd R₀ hR₀le
    (fun X hX => le_of_forall_sq_eq_one_mem_of_descended R₀ K₃ (algebraMap K K₃) 1 hRg hX)
    (fun η' hη' => (even_F4_descended_root_SL2_pointwise_automorphisms_inner hf K hK K₃
      (algebraMap K K₃) R₀ hk (isRoot_single _ κ.i) 1 hRg).1 η' hη') η hηx hηR,
    fun y hy => ?_⟩
  obtain ⟨d, hdDR, hdy⟩ := hdz y hy
  have hdZ : d ∈ (Subgroup.center D).map D.subtype := hcent ▸ hdDR
  have hkey : g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g =
      h⁻¹ * d * h⁻¹⁻¹ := by
    have hdy' : baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) = (g * h⁻¹) * d * (g * h⁻¹)⁻¹ :=
      hdy
    rw [hdy']
    group
  have hdT : d ∈ torusGroup Tag.F4 Ω := by
    obtain ⟨z, hz, rfl⟩ := hZT hdZ
    have hle : torusGroup Tag.F4 K₃ ≤
        (torusGroup Tag.F4 Ω).comap (baseChangeGL (algebraMap K₃ Ω)) := by
      rw [torusGroup, Subgroup.closure_le]
      rintro _ ⟨⟨i, t⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
      exact torusElt_mem_torusGroup i _
    exact hle hz
  have ha' : baseChangeGL (algebraMap K₃ Ω) a ∈ subsystemGroup Tag.F4 Ω {κ.i, κ.j} :=
    baseChangeGL_mem_subsystemGroup (algebraMap K₃ Ω) ha
  have hχ : d ∈ torusGroup Tag.F4 Ω ∧ torusRootChar d (Pi.single κ.i 1) = 1 ∧
      torusRootChar d (Pi.single κ.j 1) = 1 := by
    refine (mem_centralizer_conj_A2_iff κ
      (U := {X : SL(3, Ω) | ∃ Y : SL(3, K), X = Matrix.SpecialLinearGroup.map (algebraMap K Ω) Y})
      (fun C hC => exists_scalar_of_commute_map_SL3 (algebraMap K Ω) C hC) ha'
      (Subgroup.mem_sup_left hdT)).1 ?_
    rintro X ⟨Y, rfl⟩
    set y' : subsystemGroup Tag.F4 K {κ.i, κ.j} := (f4A2Equiv K κ).symm Y with hy'
    have hmem : baseChangeGL (algebraMap K Ω) (y' : ModGL Tag.F4 K) ∈
        subsystemGroup Tag.F4 Ω {κ.i, κ.j} := baseChangeGL_mem_subsystemGroup _ y'.2
    have hsymm : (f4A2Equiv Ω κ).symm (Matrix.SpecialLinearGroup.map (algebraMap K Ω) Y) =
        ⟨baseChangeGL (algebraMap K Ω) (y' : ModGL Tag.F4 K), hmem⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [f4A2Equiv_baseChange_algebraMap κ y', hy', MulEquiv.apply_symm_apply]
      rfl
    rw [hsymm]
    have hRmem : baseChangeGL (algebraMap K₃ Ω) a * baseChangeGL (algebraMap K Ω)
        (y' : ModGL Tag.F4 K) * (baseChangeGL (algebraMap K₃ Ω) a)⁻¹ ∈ (⁅D, D⁆ : Subgroup _) := by
      rw [hRQ, hRQK]
      exact ⟨_, ⟨y', y'.2, rfl⟩, rfl⟩
    exact (mem_centralizer_iff.1 hdDR.2 _ hRmem).symm
  obtain ⟨-, h1', h2'⟩ := hχ
  obtain ⟨hzH, hker⟩ := torusRootChar_conj_eq_one_of_forall u κ hu hdT h1' h2'
  subst hh
  exact ⟨by rw [hkey]; exact hzH, fun α hα => by rw [hkey]; exact hker α hα⟩

end Actor

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
