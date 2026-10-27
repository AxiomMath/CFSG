module

public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRationalBase
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents
public import CFSG.LieType.Chevalley.E6SignedGraphQuasisimple
public import CFSG.LieType.Chevalley.GraphFixedOddPerfect
public import CFSG.LieType.Chevalley.LangActualInvolutionReduction
public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Elementary

variable {K : Type} [Field K]

theorem orbitFieldUnit_one (σ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank) :
    orbitFieldUnit TwistTag.E6 σ.toRingHom (1 : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) = 1 :=
  map_one _

theorem orbitFieldUnit_neg_one (σ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank) :
    orbitFieldUnit TwistTag.E6 σ.toRingHom (-1 : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) =
      -1 :=
  Units.ext (by
    rw [coe_orbitFieldUnit]
    simp only [Units.val_neg, Units.val_one, NegMemClass.coe_neg, OneMemClass.coe_one])

theorem exists_unit_pow_sub_one_eq_neg_one [Finite K] {q : ℕ} (hq : Odd q)
    (hK : Nat.card K = q ^ 2) : ∃ μ : Kˣ, μ ^ (q - 1) = -1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, rfl⟩ := hq
  have hm : 1 ≤ m := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at h1
      norm_num at h1
    · exact h0
  have hunits : Fintype.card Kˣ = 4 * m * (m + 1) := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    ring_nf
    omega
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hoζ : orderOf ζ = 4 * m * (m + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_eq_fintype_card, hunits]
  refine ⟨ζ ^ (m + 1), ?_⟩
  have hx : (ζ ^ (m + 1)) ^ (2 * m + 1 - 1) = ζ ^ (2 * m * (m + 1)) := by
    rw [← pow_mul]
    congr 1
    rw [Nat.add_sub_cancel]
    ring
  rw [hx]
  set x := ζ ^ (2 * m * (m + 1)) with hxdef
  have hx2 : (x : K) * x = 1 := by
    rw [← Units.val_mul, ← pow_add, show 2 * m * (m + 1) + 2 * m * (m + 1) = 4 * m * (m + 1) by
      ring, ← hoζ, pow_orderOf_eq_one, Units.val_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hoζ] at h'
    have hle := Nat.le_of_dvd (by positivity) h'
    nlinarith
  rcases mul_self_eq_one_iff.1 hx2 with h | h
  · exact absurd (Units.ext h) hx1
  · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])

@[expose] def twE6Tuple (μ : Kˣ) : Fin TwistTag.E6.tag.rank → Kˣ :=
  ![1, μ, 1, 1, 1, 1]

@[expose] def twE6Untwist (μ : Kˣ) : ModGL TwistTag.E6.tag K :=
  rootDiagUnit TwistTag.E6.tag (twE6Tuple μ)

theorem twE6Tuple_perm (μ : Kˣ) :
    (fun i => twE6Tuple μ (TwistTag.E6.perm.symm i)) = twE6Tuple μ := by
  funext i
  change Fin 6 at i
  fin_cases i <;> rfl

theorem entrywise_twE6Untwist (σ : K ≃+* K) {μ : Kˣ} (hμ : σ (μ : K) = -μ) :
    Units.map (entrywiseHom σ.toRingHom) (twE6Untwist μ) =
      twE6Untwist μ * rootDiagUnit TwistTag.E6.tag (signTuple K) := by
  rw [twE6Untwist, units_map_entrywiseHom_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext i
  rw [Pi.mul_apply]
  change Fin 6 at i
  fin_cases i <;> refine Units.ext ?_ <;> simp [twE6Tuple, signTuple, hμ]

end Elementary

section TwoCerts

variable {K : Type} [Field K]

theorem twistA_conj_twE6Untwist (μ : Kˣ) :
    twistA K * twE6Untwist μ * (twistA K)⁻¹ = twE6Untwist μ := by
  rw [twE6Untwist, twistA_conj_rootDiagUnit, twE6Tuple_perm]

end TwoCerts

variable {K : Type} [Field K] [Finite K]

@[expose] def twE6SignU (σ : K ≃+* K) :
    (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ :=
  fun a => if a = ⟨3, by decide⟩ then -1 else 1

@[expose] def twE6SignAut (σ : K ≃+* K) :
    MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
  compatDiagAutHom TwistTag.E6 K σ.toRingHom (twE6SignU σ) * fieldActor σ σ

theorem coe_twE6SignAut {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
    (twE6SignAut σ g : ModGL TwistTag.E6.tag K) = twistA K * g * (twistA K)⁻¹ := by
  obtain ⟨-, -, -, -, hcd, hΔ, -, -, -, hσP, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hb : compatDiag TwistTag.E6 σ.toRingHom (twE6SignU σ) = signTuple K := by
    rw [hcd]
    have h0 : twE6SignU σ ⟨0, by decide⟩ = 1 := ite_eq_right (by decide)
    have h1 : twE6SignU σ ⟨1, by decide⟩ = 1 := ite_eq_right (by decide)
    have h2 : twE6SignU σ ⟨2, by decide⟩ = 1 := ite_eq_right (by decide)
    have h3 : twE6SignU σ ⟨3, by decide⟩ = -1 := ite_eq_left rfl
    simp only [h0, h1, h2, h3, orbitFieldUnit_one, orbitFieldUnit_neg_one, map_one]
    rfl
  rw [twE6SignAut, MulAut.mul_apply, hΔ, hσP, hb, twistA]
  group

omit [Finite K] in
theorem twistHom_eq_iff_of_commute (σ : K ≃+* K) {y : ModGL TwistTag.E6.tag K}
    (hy : twistA K * y = y * twistA K) :
    twistHom TwistTag.E6 K σ.toRingHom y = y ↔
      Units.map (entrywiseHom σ.toRingHom) y = (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ *
        y * rootDiagUnit TwistTag.E6.tag (signTuple K) := by
  set d := rootDiagUnit TwistTag.E6.tag (signTuple K) with hd
  set P := diagramMap TwistTag.E6 K with hP
  have hPP : P * P = 1 := diagramMap_E6_mul_self
  have hPi : P⁻¹ = P := inv_eq_of_mul_eq_one_right hPP
  have hA : twistA K = d * P := rfl
  have hPA : P = d⁻¹ * twistA K := by rw [hA, inv_mul_cancel_left]
  rw [twistHom_apply]
  constructor
  · intro h
    calc Units.map (entrywiseHom σ.toRingHom) y =
        P⁻¹ * (P * Units.map (entrywiseHom σ.toRingHom) y * P⁻¹) * P := by group
      _ = P * y * P := by rw [h, hPi]
      _ = d⁻¹ * (twistA K * y) * P := by
          nth_rewrite 1 [hPA]
          group
      _ = d⁻¹ * y * d * (P * P) := by rw [hy, hA]; group
      _ = d⁻¹ * y * d := by rw [hPP, mul_one]
  · intro h
    rw [h]
    calc P * (d⁻¹ * y * d) * P⁻¹ = (twistA K)⁻¹ * y * twistA K := by
          rw [hA, mul_inv_rev, hPi]
          group
      _ = y := by rw [mul_assoc, ← hy, inv_mul_cancel_left]

omit
  [Finite K] in
theorem baseChangeGL_twistA (σ : K ≃+* K) :
    baseChangeGL (fixSubfield σ).subtype (twistA (fixSubfield σ)) = twistA K := by
  rw [twistA, CFSG.LieType.AlgebraicGroups.baseChangeGL_rootDiagUnit_mul_diagramMap, twistA]
  congr 2
  funext i
  change Fin 6 at i
  fin_cases i <;> ext <;> simp [signTuple]

@[expose] def twE6C4Image (σ : K ≃+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  (rootGenerated (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype)

omit
  [Finite K] in
theorem twE6C4Image_le (σ : K ≃+* K) :
    twE6C4Image σ ≤ fixedFieldImage TwistTag.E6.tag σ ⊓ fixedGroup K := by
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨hsC, hsA⟩ := mem_fixedGroup.1 (rootGenerated_le_fixedGroup hs)
  refine ⟨⟨s, hsC, rfl⟩, mem_fixedGroup.2 ⟨map_baseChangeGL_adjointGroup_le _ ⟨s, hsC, rfl⟩, ?_⟩⟩
  rw [← baseChangeGL_twistA σ, ← map_mul, hsA, map_mul]

theorem twE6C4Image_conj_mem (hK : ringChar K ≠ 2) (σ : K ≃+* K)
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ fixedGroup K ⊓ entrywiseFixedGroup TwistTag.E6.tag σ)
    {s : ModGL TwistTag.E6.tag K} (hs : s ∈ twE6C4Image σ) : g * s * g⁻¹ ∈ twE6C4Image σ := by
  have hk2 := ringChar_fixSubfield_ne_two hK σ
  obtain ⟨-, hinj, -, hle, -, hnorm, -⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup TwistTag.E6.tag K σ
  set ι := (fixSubfield σ).subtype with hι
  set Mbig := (fixedGroup (fixSubfield σ)).map (baseChangeGL ι) with hMbig
  obtain ⟨hgA, hgσ⟩ := Subgroup.mem_inf.1 hg
  have hgM : Mbig.map (MulAut.conj g).toMonoidHom ≤ Mbig := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨hcC, hcA⟩ := mem_fixedGroup.1 hc
    have hcJ : baseChangeGL ι c ∈ fixedFieldImage TwistTag.E6.tag σ := ⟨c, hcC, rfl⟩
    have h := hnorm.conj_mem ⟨_, hle hcJ⟩ hcJ ⟨g, hgσ⟩
    obtain ⟨c', hc'C, hc'⟩ := h
    have hcomm : baseChangeGL ι c * twistA K = twistA K * baseChangeGL ι c := by
      rw [← baseChangeGL_twistA σ, ← map_mul, hcA, map_mul]
    obtain ⟨-, hgA'⟩ := mem_fixedGroup.1 hgA
    have hc'A : c' * twistA (fixSubfield σ) = twistA (fixSubfield σ) * c' := by
      apply hinj
      rw [map_mul, map_mul, baseChangeGL_twistA σ]
      rw [hc']
      change g * baseChangeGL ι c * g⁻¹ * twistA K = twistA K * (g * baseChangeGL ι c * g⁻¹)
      have hgi : g⁻¹ * twistA K = twistA K * g⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgA', mul_inv_cancel_right]
      calc g * baseChangeGL ι c * g⁻¹ * twistA K = g * baseChangeGL ι c * (g⁻¹ * twistA K) := by
            group
        _ = g * (baseChangeGL ι c * twistA K) * g⁻¹ := by rw [hgi]; group
        _ = (g * twistA K) * baseChangeGL ι c * g⁻¹ := by rw [hcomm]; group
        _ = twistA K * (g * baseChangeGL ι c * g⁻¹) := by rw [hgA']; group
    refine ⟨c', mem_fixedGroup.2 ⟨hc'C, hc'A⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hc'
  have hMeq : twE6C4Image σ = ⁅Mbig, Mbig⁆ := by
    rw [twE6C4Image, ← commutator_fixedGroup hk2, Subgroup.map_commutator]
  rw [hMeq] at hs ⊢
  have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hs
  rw [Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono hgM hgM h

@[expose] def twE6C4Sub (σ : K ≃+* K) (μ : Kˣ) : Subgroup (ModGL TwistTag.E6.tag K) :=
  (twE6C4Image σ).map (MulAut.conj (twE6Untwist μ)⁻¹).toMonoidHom

omit
  [Finite K] in
theorem twE6C4Sub_commute (σ : K ≃+* K) (μ : Kˣ) {j : ModGL TwistTag.E6.tag K}
    (hj : j ∈ twE6C4Sub σ μ) : twistA K * j = j * twistA K := by
  obtain ⟨s, hs, rfl⟩ := hj
  obtain ⟨-, hsA⟩ := mem_fixedGroup.1 ((twE6C4Image_le σ hs).2)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have ht := twistA_conj_twE6Untwist (K := K) μ
  have htA : twistA K * twE6Untwist μ = twE6Untwist μ * twistA K := by
    calc twistA K * twE6Untwist μ = twistA K * twE6Untwist μ * (twistA K)⁻¹ * twistA K := by
          group
      _ = twE6Untwist μ * twistA K := by rw [ht]
  have htA' : twistA K * (twE6Untwist μ)⁻¹ = (twE6Untwist μ)⁻¹ * twistA K := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, htA, inv_mul_cancel_left]
  calc twistA K * ((twE6Untwist μ)⁻¹ * s * twE6Untwist μ) =
      (twE6Untwist μ)⁻¹ * (twistA K * s) * twE6Untwist μ := by
        rw [← mul_assoc, ← mul_assoc, htA']; group
    _ = (twE6Untwist μ)⁻¹ * s * (twistA K * twE6Untwist μ) := by rw [← hsA]; group
    _ = _ := by rw [htA]; group

omit
  [Finite K] in
theorem twE6C4Sub_le_adjointGroup (σ : K ≃+* K) (μ : Kˣ) :
    twE6C4Sub σ μ ≤ adjointGroup TwistTag.E6.tag K := by
  rintro _ ⟨s, hs, rfl⟩
  have hsC := (mem_fixedGroup.1 ((twE6C4Image_le σ hs).2)).1
  have h := (rootDiagAut TwistTag.E6.tag K (twE6Tuple μ)⁻¹ ⟨s, hsC⟩).2
  rw [coe_rootDiagAut, ← rootDiagUnit_inv, inv_inv] at h
  exact h

omit [Finite K] in
theorem twE6C4Sub_le_twistedFixedGroup (σ : K ≃+* K) {μ : Kˣ} (hμ : σ (μ : K) = -μ) :
    twE6C4Sub σ μ ≤ twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
  intro j hj
  refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨twE6C4Sub_le_adjointGroup σ μ hj,
    (twistHom_eq_iff_of_commute σ (twE6C4Sub_commute σ μ hj)).2 ?_⟩
  obtain ⟨s, hs, rfl⟩ := hj
  have hsσ := (Subgroup.mem_inf.1 (twE6C4Image_le σ hs)).1
  have hsσ' : Units.map (entrywiseHom σ.toRingHom) s = s :=
    (mem_entrywiseFixedGroup.1 (fixedFieldImage_le hsσ)).2
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv,
    entrywise_twE6Untwist σ hμ, hsσ']
  group

@[expose] def twE6C4SubEquiv (σ : K ≃+* K) (μ : Kˣ) :
    rootGenerated (fixSubfield σ) ≃* twE6C4Sub σ μ :=
  ((rootGenerated (fixSubfield σ)).equivMapOfInjective _ (baseChangeGL_injective _)).trans
    ((twE6C4Image σ).equivMapOfInjective _ (MulAut.conj (twE6Untwist μ)⁻¹).injective)

omit [Finite K] in
theorem commutator_twE6C4Sub (hK : ringChar K ≠ 2) (σ : K ≃+* K) (μ : Kˣ) :
    ⁅twE6C4Sub σ μ, twE6C4Sub σ μ⁆ = twE6C4Sub σ μ := by
  have hk2 := ringChar_fixSubfield_ne_two hK σ
  rw [twE6C4Sub, twE6C4Image, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
    commutator_rootGenerated hk2]

omit [Finite K] in
theorem twE6C4Sub_le_graphFixedRootGroup (hK : ringChar K ≠ 2) (σ : K ≃+* K) {μ : Kˣ}
    (hμ : σ (μ : K) = -μ) : twE6C4Sub σ μ ≤ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  obtain ⟨-, -, hΓ⟩ := odd_diagram_fixed_root_group_perfect TwistTag.E6 K hK σ
  rw [← commutator_twE6C4Sub hK σ μ, ← hΓ]
  exact Subgroup.commutator_mono (twE6C4Sub_le_twistedFixedGroup σ hμ)
    (twE6C4Sub_le_twistedFixedGroup σ hμ)

omit [Finite K] in
theorem isQuasisimple_twE6C4Sub (hK : ringChar K ≠ 2) (σ : K ≃+* K) (μ : Kˣ) :
    IsQuasisimple (twE6C4Sub σ μ) := by
  have hk2 := ringChar_fixSubfield_ne_two hK σ
  obtain ⟨-, -, hq, -⟩ := E6_signed_graph_fixed_root_group_quasisimple (fixSubfield σ) hk2
  exact LocalCores.isQuasisimple_of_mulEquiv (twE6C4SubEquiv σ μ) hq

omit [Finite K] in
theorem untwist_mem (σ : K ≃+* K) {μ : Kˣ} (hμ : σ (μ : K) = -μ) {g : ModGL TwistTag.E6.tag K}
    (hgC : g ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hgA : twistA K * g = g * twistA K) :
    twE6Untwist μ * g * (twE6Untwist μ)⁻¹ ∈
      fixedGroup K ⊓ entrywiseFixedGroup TwistTag.E6.tag σ := by
  have hgΓ := graphFixedRootGroup_le _ _ _ hgC
  have hgσ := (twistHom_eq_iff_of_commute σ hgA).1 hgΓ.2
  have hC : twE6Untwist μ * g * (twE6Untwist μ)⁻¹ ∈ adjointGroup TwistTag.E6.tag K := by
    have h := (rootDiagAut TwistTag.E6.tag K (twE6Tuple μ) ⟨g, hgΓ.1⟩).2
    rwa [coe_rootDiagAut] at h
  have htA : twistA K * twE6Untwist μ = twE6Untwist μ * twistA K := by
    calc twistA K * twE6Untwist μ = twistA K * twE6Untwist μ * (twistA K)⁻¹ * twistA K := by
          group
      _ = twE6Untwist μ * twistA K := by rw [twistA_conj_twE6Untwist]
  have htA' : twistA K * (twE6Untwist μ)⁻¹ = (twE6Untwist μ)⁻¹ * twistA K := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, htA, inv_mul_cancel_left]
  refine ⟨mem_fixedGroup.2 ⟨hC, ?_⟩, mem_entrywiseFixedGroup.2 ⟨hC, ?_⟩⟩
  · calc twE6Untwist μ * g * (twE6Untwist μ)⁻¹ * twistA K =
        twE6Untwist μ * g * (twistA K * (twE6Untwist μ)⁻¹) := by rw [htA']; group
      _ = twE6Untwist μ * (twistA K * g) * (twE6Untwist μ)⁻¹ := by rw [hgA]; group
      _ = twistA K * (twE6Untwist μ * g * (twE6Untwist μ)⁻¹) := by rw [← mul_assoc, ← htA]; group
  · rw [map_mul, map_mul, map_inv, entrywise_twE6Untwist σ hμ, hgσ]
    have hdt : rootDiagUnit TwistTag.E6.tag (signTuple K) * twE6Untwist μ =
        twE6Untwist μ * rootDiagUnit TwistTag.E6.tag (signTuple K) := by
      rw [twE6Untwist, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    group

theorem twE6C4Sub_conj_mem (hK : ringChar K ≠ 2) (σ : K ≃+* K) {μ : Kˣ} (hμ : σ (μ : K) = -μ)
    {g : ModGL TwistTag.E6.tag K} (hgC : g ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hgA : twistA K * g = g * twistA K) {j : ModGL TwistTag.E6.tag K}
    (hj : j ∈ twE6C4Sub σ μ) : g * j * g⁻¹ ∈ twE6C4Sub σ μ := by
  obtain ⟨s, hs, rfl⟩ := hj
  have h := twE6C4Image_conj_mem hK σ (untwist_mem σ hμ hgC hgA) hs
  refine ⟨_, h, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  group

end CFSG.ComponentClassification.Burgoyne.E2
