module

public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.LieType.Chevalley.PinnedBridge
public import CFSG.LieType.Chevalley.RootOps.All
public import CFSG.LieType.Chevalley.D4TripleA2Lemmas
public import CFSG.LieType.Chevalley.TwistMap
public import CFSG.LieType.Chevalley.OppositeBorel

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_nsmul (a : Fin τ.rank → Kˣ) (k : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar a (k • v) = rootChar a v ^ k := by
  induction k with
  | zero => rw [zero_smul, rootChar_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, rootChar_add, ih, pow_succ]

theorem rootDiag_mul_pinnedCoeff
    (a : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (k : ℕ) :
    rootDiag a * pinnedCoeff τ K α k =
      ((rootChar a α ^ k : Kˣ) : K) • (pinnedCoeff τ K α k * rootDiag a) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pinnedCoeff_zero, pow_zero, Units.val_one, one_smul, mul_one, one_mul]
  · have hC : MapsLabelWt (pinnedCoeff τ K α k) (· + k • α) := by
      rw [(rootOperatorFamily τ).pinnedCoeff_eq_smul_D K hα k]
      exact ((rootOperatorFamily τ).mapsLabelWt_D (R := K) ⟨α, hα⟩ hk).smul _
    rw [rootDiag_mul_of_mapsLabelWt a hC, rootChar_nsmul]

theorem rootDiag_mul_pinnedX
    (a : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (c : K) :
    rootDiag a * (pinnedX τ K α c : Module.End K (RootModule τ K)) =
      (pinnedX τ K α ((rootChar a α : K) * c) : Module.End K (RootModule τ K)) * rootDiag a := by
  rw [pinnedX_eq_sum, pinnedX_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, rootDiag_mul_pinnedCoeff a hα k, smul_smul, smul_mul_assoc, mul_pow,
    Units.val_pow_eq_pow_val, mul_comm]

theorem rootDiagUnit_conj_pinnedX
    (a : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (c : K) :
    rootDiagUnit τ a * pinnedX τ K α c * (rootDiagUnit τ a)⁻¹ =
      pinnedX τ K α ((rootChar a α : K) * c) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  change rootDiag a * (pinnedX τ K α c : Module.End K (RootModule τ K)) * rootDiag a⁻¹ = _
  rw [rootDiag_mul_pinnedX a hα, mul_assoc, rootDiag_mul_rootDiag, mul_inv_cancel, rootDiag_one,
    mul_one]

theorem baseChange_entrywise (σ : K →+* K) (A : Module.End K (RootModule τ K)) :
    BaseChange σ A (entrywise σ A) := fun b => (entrywise_single σ A b).symm

theorem entrywise_pinnedX
    (σ : K →+* K) (α : Fin τ.rank → ℤ) (c : K) :
    entrywise σ (pinnedX τ K α c : Module.End K (RootModule τ K)) =
      pinnedX τ K α (σ c) :=
  (baseChange_entrywise σ _).unique (baseChange_pinnedX σ α c)

theorem map_rootChar (σ : K →+* K) (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    Units.map σ.toMonoidHom (rootChar a v) =
      rootChar (fun i => Units.map σ.toMonoidHom (a i)) v := by
  simp only [rootChar, map_prod, map_zpow]

theorem entrywise_rootDiag (σ : K →+* K) (a : Fin τ.rank → Kˣ) :
    entrywise σ (rootDiag a) = rootDiag fun i => Units.map σ.toMonoidHom (a i) := by
  refine end_ext_single fun b => ?_
  rw [entrywise_single, rootDiag_single, rootDiag_single, ← map_rootChar]
  ext l
  simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, map_mul,
    Finsupp.single_apply]
  split_ifs <;> simp

theorem map_rootSubgroup_of_eq
    {f : ModGL τ K →* ModGL τ K} {α : Fin τ.rank → ℤ} {g : K → K}
    (hg : Function.Surjective g) (hf : ∀ c, f (pinnedX τ K α c) = pinnedX τ K α (g c)) :
    (rootSubgroup τ K α).map f = rootSubgroup τ K α := by
  rw [rootSubgroup, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨g c, (hf c).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨d, rfl⟩ := hg c
    exact ⟨_, ⟨d, rfl⟩, hf d⟩

theorem map_rootSpan_of_forall
    {f : ModGL τ K →* ModGL τ K} {S : Set (Fin τ.rank → ℤ)}
    (h : ∀ α ∈ S, (rootSubgroup τ K α).map f = rootSubgroup τ K α) :
    (rootSpan τ K S).map f = rootSpan τ K S := by
  simp only [rootSpan, Subgroup.map_iSup]
  exact iSup_congr fun α => iSup_congr fun hα => h α hα

theorem map_conj_rootDiagUnit_rootSubgroup
    (a : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    (rootSubgroup τ K α).map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom =
      rootSubgroup τ K α :=
  map_rootSubgroup_of_eq (g := fun c => (rootChar a α : K) * c)
    (fun c => ⟨((rootChar a α)⁻¹ : Kˣ) * c, by
      simp only [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]⟩)
    fun c => by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact rootDiagUnit_conj_pinnedX a hα c

theorem map_entrywise_rootSubgroup
    (σ : K ≃+* K) (α : Fin τ.rank → ℤ) :
    (rootSubgroup τ K α).map (Units.map (entrywiseHom σ.toRingHom)) = rootSubgroup τ K α :=
  map_rootSubgroup_of_eq (g := σ) σ.surjective fun c => Units.ext (by
    rw [Units.coe_map]
    exact entrywise_pinnedX σ.toRingHom α c)

theorem conj_rootDiagUnit_mem_adjointGroup
    (a : Fin τ.rank → Kˣ) {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K) :
    rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ ∈ adjointGroup τ K :=
  ((Subgroup.mem_normalizer_iff.1 (root_diagonal_conjugation τ K a).2.2) g).1 hg

theorem rootDiagUnit_mul (a b : Fin τ.rank → Kˣ) :
    rootDiagUnit τ (a * b) = rootDiagUnit τ a * rootDiagUnit τ b :=
  Units.ext (rootDiag_mul_rootDiag a b).symm

theorem rootDiagUnit_one : rootDiagUnit τ (1 : Fin τ.rank → Kˣ) = 1 :=
  Units.ext rootDiag_one

theorem rootDiagUnit_inv (a : Fin τ.rank → Kˣ) : (rootDiagUnit τ a)⁻¹ = rootDiagUnit τ a⁻¹ :=
  Units.ext rfl

variable (τ K) in
@[expose] def rootDiagAut
    (a : Fin τ.rank → Kˣ) : MulAut (adjointGroup τ K) where
  toFun g := ⟨rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹,
    conj_rootDiagUnit_mem_adjointGroup a g.2⟩
  invFun g := ⟨rootDiagUnit τ a⁻¹ * g * (rootDiagUnit τ a⁻¹)⁻¹,
    conj_rootDiagUnit_mem_adjointGroup a⁻¹ g.2⟩
  left_inv g := Subtype.ext (by
    simp only [← rootDiagUnit_inv, inv_inv]
    group)
  right_inv g := Subtype.ext (by
    simp only [← rootDiagUnit_inv, inv_inv]
    group)
  map_mul' g h := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

theorem coe_rootDiagAut
    (a : Fin τ.rank → Kˣ) (g : adjointGroup τ K) :
    ((rootDiagAut τ K a g : adjointGroup τ K) : ModGL τ K) =
      rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ :=
  rfl

variable (τ K) in
@[expose] def rootDiagAutHom
    : (Fin τ.rank → Kˣ) →* MulAut (adjointGroup τ K) where
  toFun := rootDiagAut τ K
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    rw [coe_rootDiagAut, rootDiagUnit_one, one_mul, inv_one, mul_one]
    rfl)
  map_mul' a b := MulEquiv.ext fun g => Subtype.ext (by
    rw [coe_rootDiagAut, rootDiagUnit_mul, MulAut.mul_apply, coe_rootDiagAut, coe_rootDiagAut]
    group)

theorem rootDiagAutHom_injective
    : Function.Injective (rootDiagAutHom τ K) := by
  intro a b hab
  funext i
  have h := congrArg (fun φ : MulAut (adjointGroup τ K) =>
    ((φ ⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩ : adjointGroup τ K) : ModGL τ K)) hab
  simp only [rootDiagAutHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_rootDiagAut] at h
  rw [(root_diagonal_conjugation τ K a).1 i 1, (root_diagonal_conjugation τ K b).1 i 1,
    mul_one, mul_one] at h
  have h2 := congrArg Units.val h
  rw [coe_xUnit, coe_xUnit] at h2
  exact Units.ext (xOp_injective (τ := τ) (R := K) i h2)

theorem chevalley_root_character_and_field_conjugation
    (τ : Tag) (K : Type) [Field K] :
    (∀ (a : Fin τ.rank → Kˣ) (α : Fin τ.rank → ℤ), IsRoot τ α → ∀ c : K,
      rootDiagUnit τ a * pinnedX τ K α c * (rootDiagUnit τ a)⁻¹ =
        pinnedX τ K α ((rootChar a α : K) * c)) ∧
    (∀ (σ : K ≃+* K) (α : Fin τ.rank → ℤ) (c : K),
      entrywise σ.toRingHom (pinnedX τ K α c : Module.End K (RootModule τ K)) =
        pinnedX τ K α (σ c)) ∧
    (∀ (σ : K ≃+* K) (a : Fin τ.rank → Kˣ), entrywise σ.toRingHom (rootDiag a) =
      rootDiag fun i => Units.map σ.toRingHom.toMonoidHom (a i)) ∧
    (∀ a : Fin τ.rank → Kˣ,
      (adjointGroup τ K).map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom = adjointGroup τ K ∧
      (posUnipotent τ K).map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom = posUnipotent τ K ∧
      (negUnipotent τ K).map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom = negUnipotent τ K) ∧
    (∀ σ : K ≃+* K,
      (adjointGroup τ K).map (Units.map (entrywiseHom σ.toRingHom)) = adjointGroup τ K ∧
      (posUnipotent τ K).map (Units.map (entrywiseHom σ.toRingHom)) = posUnipotent τ K ∧
      (negUnipotent τ K).map (Units.map (entrywiseHom σ.toRingHom)) = negUnipotent τ K) ∧
    ∃ φ : (Fin τ.rank → Kˣ) →* MulAut (adjointGroup τ K), Function.Injective φ ∧
      ∀ a g, ((φ a g : adjointGroup τ K) : ModGL τ K) =
        rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ := by
  refine ⟨fun a α hα c => rootDiagUnit_conj_pinnedX a hα c,
    fun σ α c => entrywise_pinnedX σ.toRingHom α c,
    fun σ a => entrywise_rootDiag σ.toRingHom a, fun a => ⟨?_, ?_, ?_⟩, fun σ => ⟨?_, ?_, ?_⟩,
    ⟨rootDiagAutHom τ K, rootDiagAutHom_injective, fun a g => rfl⟩⟩
  · exact map_conj_eq_of_mem_normalizer (root_diagonal_conjugation τ K a).2.2
  · exact map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a hα.1
  · exact map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a hα.1
  · rw [adjointGroup, MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨h, ⟨i, c, hh | hh⟩, rfl⟩
      · refine ⟨i, σ c, Or.inl ?_⟩
        rw [Units.coe_map]
        change entrywise σ.toRingHom (h : Module.End K (RootModule τ K)) = _
        rw [hh]
        exact entrywise_xOp σ.toRingHom i c
      · refine ⟨i, σ c, Or.inr ?_⟩
        rw [Units.coe_map]
        change entrywise σ.toRingHom (h : Module.End K (RootModule τ K)) = _
        rw [hh]
        exact entrywise_yOp σ.toRingHom i c
    · rintro ⟨i, c, hg | hg⟩
      · refine ⟨xUnit τ K i (σ.symm c), ⟨i, σ.symm c, Or.inl (coe_xUnit i _)⟩, Units.ext ?_⟩
        rw [Units.coe_map, hg]
        change entrywise σ.toRingHom (xUnit τ K i (σ.symm c) : Module.End K (RootModule τ K)) = _
        rw [coe_xUnit, entrywise_xOp]
        simp
      · refine ⟨yUnit τ K i (σ.symm c), ⟨i, σ.symm c, Or.inr (coe_yUnit i _)⟩, Units.ext ?_⟩
        rw [Units.coe_map, hg]
        change entrywise σ.toRingHom (yUnit τ K i (σ.symm c) : Module.End K (RootModule τ K)) = _
        rw [coe_yUnit, entrywise_yOp]
        simp
  · exact map_rootSpan_of_forall fun α _ => map_entrywise_rootSubgroup σ α
  · exact map_rootSpan_of_forall fun α _ => map_entrywise_rootSubgroup σ α

end CFSG.LieType.Chevalley
