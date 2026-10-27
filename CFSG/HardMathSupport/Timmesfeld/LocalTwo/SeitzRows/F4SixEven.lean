module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4ThreeOdd
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.ActorTools
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Six

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.F4Weyl CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical SteinbergBN
  CFSG.RankThree.Chevalley.EvenF4Actors CFSG.RankThree.Chevalley.EvenF4QPlus
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open scoped Pointwise commutatorElement MatrixGroups Matrix

set_option linter.unusedSectionVars false

theorem exists_map_unitary_of_mem_unitarySet {L Ω : Type} [Field L] [Finite L] [Field Ω]
    [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f) (ι : L →+* Ω)
    (hL : Nat.card L = (ℓ ^ f) ^ 2) (σ : L ≃+* L) (hσ : ∀ b, σ b = b ^ ℓ ^ f)
    {X : SL(3, Ω)}
    (hX : Matrix.SpecialLinearGroup.toGL X ∈ CFSG.RankThree.Classical2.unitarySet (ℓ ^ f) 3) :
    ∃ A : SL(3, L), ((A : Matrix (Fin 3) (Fin 3) L).map σ)ᵀ * A = 1 ∧
      Matrix.SpecialLinearGroup.map ι A = X := by
  classical
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨K', hK'card, hK'mem⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_exists_subfield (Ω := Ω) (ℓ := ℓ) hf
  have hK'fin : Finite K' := Nat.finite_of_card_ne_zero (by
    rw [hK'card]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero))
  have hpow : ∀ b : L, b ^ (ℓ ^ f) ^ 2 = b := fun b => by
    rw [← hL, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card b
  have hsub : Set.range ι ⊆ (K' : Set Ω) := by
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, hK'mem, ← map_pow, hpow]
  have hcardr : (Set.range ι).ncard = Nat.card K' := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective ι.injective, hL, hK'card]
  have heq : Set.range ι = (K' : Set Ω) :=
    Set.eq_of_subset_of_ncard_le hsub (by
      rw [hcardr, ← Nat.card_coe_set_eq]
      exact le_of_eq rfl) (Set.toFinite _)
  have hrange : ∀ c : Ω, c ∈ Set.range ι ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [heq, SetLike.mem_coe, hK'mem]
  obtain ⟨h1, h2, h3⟩ := hX
  have hX1 : ∀ i j, (X : Matrix (Fin 3) (Fin 3) Ω) i j ^ (ℓ ^ f) ^ 2 =
      (X : Matrix (Fin 3) (Fin 3) Ω) i j := h1
  have hX2 : (X : Matrix (Fin 3) (Fin 3) Ω).det = 1 := h2
  have hX3 : ((X : Matrix (Fin 3) (Fin 3) Ω).map (· ^ (ℓ ^ f)))ᵀ *
      (X : Matrix (Fin 3) (Fin 3) Ω) = 1 := h3
  have hentry : ∀ i j, ∃ b : L, ι b = (X : Matrix (Fin 3) (Fin 3) Ω) i j := fun i j =>
    (hrange _).mpr (hX1 i j)
  choose B₁ hB₁ using hentry
  obtain ⟨B₀, hB₀map⟩ : ∃ B₀ : Matrix (Fin 3) (Fin 3) L,
      B₀.map ι = (X : Matrix (Fin 3) (Fin 3) Ω) :=
    ⟨Matrix.of B₁, by
      ext i j
      exact hB₁ i j⟩
  have hdet : B₀.det = 1 := by
    apply ι.injective
    rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hB₀map, hX2]
  have hσι : ∀ b : L, ι (σ b) = ι b ^ ℓ ^ f := fun b => by rw [hσ, map_pow]
  refine ⟨⟨B₀, hdet⟩, ?_, Subtype.ext hB₀map⟩
  apply Matrix.map_injective ι.injective
  have hmap : ((B₀.map σ).map ι) = (B₀.map ι).map (· ^ (ℓ ^ f)) := by
    ext i j
    simp only [Matrix.map_apply]
    exact hσι _
  simp only [Matrix.map_mul, Matrix.transpose_map, hmap, hB₀map,
    Matrix.map_one ι (map_zero ι) (map_one ι)]
  exact hX3

theorem exists_sextic_tower (K : Type) [Field K] [Finite K] [CharP K 2] (Ω : Type) [Field Ω]
    [Algebra K Ω] [IsAlgClosed Ω] :
    ∃ K₆ : IntermediateField K Ω, Module.finrank K K₆ = 6 ∧ Module.Finite K K₆ ∧ Finite K₆ ∧
      ∃ K₂ K₃ : IntermediateField K K₆, Module.finrank K K₂ = 2 ∧ Module.finrank K K₃ = 3 ∧
        Module.Finite K K₂ ∧ Finite K₂ ∧ CharP K₂ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₆, hK₆⟩ := exists_intermediateField_finrank K Ω 6
  have : FiniteDimensional K K₆ := Module.finite_of_finrank_eq_succ hK₆
  have : Finite K₆ := Module.finite_of_finite K
  obtain ⟨L₂, hL₂⟩ := exists_intermediateField_finrank K Ω 2
  obtain ⟨L₃, hL₃⟩ := exists_intermediateField_finrank K Ω 3
  obtain ⟨e₂⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := K) (K := L₂) (L := K₆)
    (by rw [hL₂, hK₆]; norm_num)
  obtain ⟨e₃⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := K) (K := L₃) (L := K₆)
    (by rw [hL₃, hK₆]; norm_num)
  have h2 : Module.finrank K e₂.fieldRange = 2 := by
    rw [← e₂.equivFieldRange.toLinearEquiv.finrank_eq]
    exact hL₂
  have h3 : Module.finrank K e₃.fieldRange = 3 := by
    rw [← e₃.equivFieldRange.toLinearEquiv.finrank_eq]
    exact hL₃
  have : FiniteDimensional K e₂.fieldRange := Module.finite_of_finrank_eq_succ h2
  have : Finite e₂.fieldRange := Module.finite_of_finite K
  exact ⟨K₆, hK₆, inferInstance, inferInstance, e₂.fieldRange, e₃.fieldRange, h2, h3,
    inferInstance, inferInstance, charP_of_injective_algebraMap
      (algebraMap K e₂.fieldRange).injective 2⟩

theorem exists_pow_ringEquiv (L : Type) [Field L] [Finite L] [CharP L 2] (f : ℕ) :
    ∃ σ : L ≃+* L, ∀ b, σ b = b ^ 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨CFSG.LieType.BorelTits.unitaryInvolution L 2 f, fun b =>
    CFSG.LieType.BorelTits.unitaryInvolution_apply ..⟩

section Actor

theorem f4A2Equiv_baseChange_hom {L M : Type} [Field L] [Field M] [CharP L 2] [CharP M 2]
    (ι : L →+* M) (κ : F4A2Kind) (y : subsystemGroup Tag.F4 L {κ.i, κ.j}) :
    ((f4A2Equiv M κ ⟨_, baseChangeGL_mem_subsystemGroup ι y.2⟩ : SL(3, M)) :
        Matrix (Fin 3) (Fin 3) M) =
      ((f4A2Equiv L κ y : SL(3, L)) : Matrix (Fin 3) (Fin 3) L).map ι := by
  rw [coe_f4A2Equiv_eq_blockMat, coe_f4A2Equiv_eq_blockMat]
  exact blockMat_baseChangeGL ι (isRoot_f4A2Root κ) _

theorem card_f4A2UnitaryGroup_eq {L : Type} [Field L] [Finite L] [CharP L 2] {f : ℕ}
    (hL : Nat.card L = (2 ^ f) ^ 2) (σ : L ≃+* L) (hσ : ∀ b, σ b = b ^ 2 ^ f) (κ : F4A2Kind)
    {U : Subgroup (ModGL Tag.F4 L)}
    (hU : ∀ w, w ∈ U ↔ ∃ hw : w ∈ subsystemGroup Tag.F4 L {κ.i, κ.j},
      ((f4A2Equiv L κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) L).map σ)ᵀ *
        (f4A2Equiv L κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) L) = 1) :
    Nat.card U = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) :=
  (CFSG.StandardType.F4Nonsplit.card_f4A2UnitaryGroup σ κ hU).trans
    (CFSG.StandardType.F4Nonsplit.card_unitarySL3 hL σ hσ)

theorem torusRootChar_eq_one_of_centralizes_unitary {K : Type} [Field K] [Finite K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (κ : F4A2Kind) (K₆ : IntermediateField K Ω)
    (K₂ K₃ : IntermediateField K K₆) [Finite K₂] (hcardF : Nat.card K₂ = (2 ^ f) ^ 2)
    (σ₂ : K₂ ≃+* K₂) (hσ₂f : ∀ b, σ₂ b = b ^ 2 ^ f) (U : Subgroup (ModGL Tag.F4 K₂))
    (hAU : ∀ A : SL(3, K₂), ((A : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ * A = 1 ↔
      ∃ g : subsystemGroup Tag.F4 K₂ {κ.i, κ.j}, (g : ModGL Tag.F4 K₂) ∈ U ∧
        f4A2Equiv K₂ κ g = A)
    (a : ModGL Tag.F4 K₃) (ha : a ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j})
    (R : Subgroup (ModGL Tag.F4 Ω))
    (hR : ∀ gU : subsystemGroup Tag.F4 K₂ {κ.i, κ.j}, (gU : ModGL Tag.F4 K₂) ∈ U →
      baseChangeGL (algebraMap K₆ Ω) (baseChangeGL (algebraMap K₃ K₆) a *
        baseChangeGL (algebraMap K₂ K₆) (gU : ModGL Tag.F4 K₂) *
        (baseChangeGL (algebraMap K₃ K₆) a)⁻¹) ∈ R)
    {d : ModGL Tag.F4 Ω} (hdT : d ∈ torusGroup Tag.F4 Ω)
    (hdR : d ∈ centralizer (R : Set (ModGL Tag.F4 Ω))) :
    torusRootChar d (Pi.single κ.i 1) = 1 ∧ torusRootChar d (Pi.single κ.j 1) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  set ι₂ : K₂ →+* Ω := (algebraMap K₆ Ω).comp (algebraMap K₂ K₆) with hι₂
  have ha' : baseChangeGL (algebraMap K₆ Ω) (baseChangeGL (algebraMap K₃ K₆) a) ∈
      subsystemGroup Tag.F4 Ω {κ.i, κ.j} :=
    baseChangeGL_mem_subsystemGroup _ (baseChangeGL_mem_subsystemGroup _ ha)
  refine ((mem_centralizer_conj_A2_iff κ
    (U := {X : SL(3, Ω) | Matrix.SpecialLinearGroup.toGL X ∈
      CFSG.RankThree.Classical2.unitarySet (Nat.card K) 3})
    (fun C hC => exists_scalar_of_commute_unitary (K := K) C hC) ha'
    (Subgroup.mem_sup_left hdT)).1 ?_).2
  intro X hX
  obtain ⟨A, hAσ, hAX⟩ := exists_map_unitary_of_mem_unitarySet (ℓ := 2) hf ι₂ hcardF σ₂ hσ₂f
    (hK ▸ hX)
  obtain ⟨gU, hgUU, hgUA⟩ := (hAU A).1 hAσ
  have hsymm : (f4A2Equiv Ω κ).symm X = ⟨baseChangeGL ι₂ (gU : ModGL Tag.F4 K₂),
      baseChangeGL_mem_subsystemGroup ι₂ gU.2⟩ := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [f4A2Equiv_baseChange_hom ι₂ κ gU, hgUA, ← hAX]
    rfl
  have hform : baseChangeGL (algebraMap K₆ Ω) (baseChangeGL (algebraMap K₃ K₆) a) *
      (((f4A2Equiv Ω κ).symm X : subsystemGroup Tag.F4 Ω {κ.i, κ.j}) : ModGL Tag.F4 Ω) *
      (baseChangeGL (algebraMap K₆ Ω) (baseChangeGL (algebraMap K₃ K₆) a))⁻¹ =
      baseChangeGL (algebraMap K₆ Ω) (baseChangeGL (algebraMap K₃ K₆) a *
        baseChangeGL (algebraMap K₂ K₆) (gU : ModGL Tag.F4 K₂) *
        (baseChangeGL (algebraMap K₃ K₆) a)⁻¹) := by
    rw [hsymm, map_mul, map_mul, map_inv]
    simp only [hι₂]
    rw [← baseChangeGL_baseChangeGL (algebraMap K₂ K₆) (algebraMap K₆ Ω)]
  rw [hform]
  exact (mem_centralizer_iff.1 hdR _ (hR gU hgUU)).symm

variable (K : Type) [Field K] [Finite K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (F : Ω →+* Ω)

theorem f4SixActor_even {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1) {g : ModGL Tag.F4 Ω}
    (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g =
      canonicalRep (coxeterSystem Tag.F4) Ω f4PhiSix)
    {x : ModGL Tag.F4 Ω} (hx : x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹)
    (hxp : orderOf x = p) (hne : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty)
    {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹) :
    F4FourActorAt K Ω p g x x₁ := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨n, hn⟩ : ∃ n, n = canonicalRep (coxeterSystem Tag.F4) Ω f4PhiSix := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, Γ = conjEntrywiseImage K g⁻¹ := ⟨_, rfl⟩
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, T₀ = torusGroup Tag.F4 Ω ⊓ Γ := ⟨_, rfl⟩
  have hεw : ((-1 : ℤ) = 1 ∧ f4PhiSix = f4Coxeter ^ 4 ∧
      p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      ((-1 : ℤ) = -1 ∧ f4PhiSix = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1) :=
    Or.inr ⟨rfl, rfl, hpd⟩
  obtain ⟨-, -, hcls⟩ := (F4_three_six_torus_data K Ω F hF hεw hp hp3).2 g hg hgn
  rw [← hn] at hgn
  subst hΓ
  have hx' : x ∈ T₀ := hT₀ ▸ hx
  obtain ⟨u, κ, δ, hδ, hu, huw⟩ := ((hcls x hx hxp).1).resolve_left hne.ne_empty
  obtain ⟨K₆, hK₆, hK₆f, hK₆fin, K₂, K₃, h2, h3, hK₂f, hK₂fin, hK₂c⟩ := exists_sextic_tower K Ω
  obtain ⟨σ₂, hσ₂f⟩ := exists_pow_ringEquiv K₂ f
  have hσ₂ : ∀ b, σ₂ b = b ^ Nat.card K := fun b => by rw [hσ₂f, hK]
  obtain ⟨U, hU⟩ := CFSG.StandardType.F4Nonsplit.exists_f4A2UnitaryGroup σ₂ κ
  obtain ⟨h, hh⟩ : ∃ h, h = canonicalRep (coxeterSystem Tag.F4) Ω u := ⟨_, rfl⟩
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ₁, Γ₁ = (conjEntrywiseImage K g⁻¹).map (MulAut.conj h).toMonoidHom :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = Γ₁ ⊓ centralizer {h * x * h⁻¹} := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = ⁅D, D⁆ := ⟨_, rfl⟩
  obtain ⟨-, -, hAU, a, ha, -, -, ⟨eU, heU⟩, hRq, -, -, -, hcentD, hZT, hZodd, x₀, hx₀, hCx,
      R₀, hR₀le, k, hk, P, hRk⟩ :=
    even_F4_cyclotomic_six_nonregular_derived_centralizer hf K hK Ω F hF hp hp3 hpd K₆ hK₆ K₂ K₃
      h2 h3 σ₂ hσ₂ n g hn hg hgn _ T₀ rfl hT₀ x hx' hxp u κ δ hδ hu
      (fun z hz => by rw [huw z hz, neg_smul, one_smul]) h (h * x * h⁻¹) hh rfl Γ₁ D R hΓ₁ hD hR
      U hU
  have hx₀₁ : x₀ = x₁ :=
    Subtype.ext (baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω) (hx₀.trans hx₁.symm))
  subst hx₀₁
  have hι'inj : Function.Injective ((baseChangeGL (algebraMap K Ω)).comp
      (adjointGroup Tag.F4 K).subtype) :=
    (baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω)).comp Subtype.val_injective
  subst hR
  obtain ⟨hR₀', hdz, hcentr, hodd⟩ := centralizer_layer_of_transport _ hι'inj
    (MulAut.conj (g * h⁻¹)) _ D hCx hcentD hZodd
  have eR : (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) ≃*
        (⁅D, D⁆ : Subgroup (ModGL Tag.F4 Ω)) :=
    (Subgroup.equivMapOfInjective _ _ hι'inj).trans ((MulEquiv.subgroupCongr hR₀').trans
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj (g * h⁻¹)).injective).symm)
  have hq₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eR.symm hRq
  have hcardF : Nat.card K₂ = (2 ^ f) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), h2, hK]
  have hpRR : p ∣ Nat.card (⁅D, D⁆ : Subgroup (ModGL Tag.F4 Ω)) := by
    rw [← Nat.card_congr eU.toEquiv, card_f4A2UnitaryGroup_eq hcardF σ₂ hσ₂f κ hU, ← hK]
    exact dvd_card_SU3_of_dvd hpd
  have hpR : ¬ Nat.Coprime p (Nat.card (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K))) := by
    rw [Nat.card_congr eR.toEquiv]
    exact fun hc' => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc' dvd_rfl hpRR)
  refine ⟨hq₀, hpR, fun η hηx hηR => exists_inner_of_fixes_layer x₀ hcentr hodd R₀ hR₀le
    (fun X hX => le_of_forall_sq_eq_one_mem_of_descended R₀ K₆ (algebraMap K K₆)
      (Matrix.GeneralLinearGroup.map (algebraMap K₂ K₆) P) hRk hX)
    (fun η' hη' => (even_F4_descended_root_SL2_pointwise_automorphisms_inner hf K hK K₆
      (algebraMap K K₆) R₀ hk (isRoot_single _ κ.i)
      (Matrix.GeneralLinearGroup.map (algebraMap K₂ K₆) P) hRk).1 η' hη') η hηx hηR,
    fun y hy => ?_⟩
  obtain ⟨d, hdDR, hdy⟩ := hdz y hy
  have hdZ : d ∈ (Subgroup.center D).map D.subtype := hcentD ▸ hdDR
  have hkey : g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g =
      h⁻¹ * d * h⁻¹⁻¹ := by
    have hdy' : baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) = (g * h⁻¹) * d * (g * h⁻¹)⁻¹ :=
      hdy
    rw [hdy']
    group
  have hdT : d ∈ torusGroup Tag.F4 Ω := by
    obtain ⟨z, hz, rfl⟩ := hZT hdZ
    have hle : torusGroup Tag.F4 K₆ ≤
        (torusGroup Tag.F4 Ω).comap (baseChangeGL (algebraMap K₆ Ω)) := by
      rw [torusGroup, Subgroup.closure_le]
      rintro _ ⟨⟨i, t⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
      exact torusElt_mem_torusGroup i _
    exact hle hz
  obtain ⟨h1', h2'⟩ := torusRootChar_eq_one_of_centralizes_unitary hf hK κ K₆ K₂ K₃ hcardF σ₂
    hσ₂f U hAU a ha _ (fun gU hgU => by
      rw [← (heU.1 ⟨gU, hgU⟩)]
      exact (eU ⟨gU, hgU⟩).2) hdT hdDR.2
  obtain ⟨hzH, hker⟩ := torusRootChar_conj_eq_one_of_forall u κ hu hdT h1' h2'
  subst hh
  exact ⟨by rw [hkey]; exact hzH, fun α hα => by rw [hkey]; exact hker α hα⟩

end Actor

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
