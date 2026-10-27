module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCSpSplit
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem solvable_or_quasisimple_map {G H : Type*} [Group G] [Group H] {L : Subgroup G}
    (hL : Group.IsSolvable L ∨ IsQuasisimple L) (f : G →* H) :
    Group.IsSolvable (L.map f) ∨ IsQuasisimple (L.map f) := by
  have hfr : (f.comp L.subtype).range = L.map f := by rw [MonoidHom.range_comp, range_subtype]
  rcases hL with hs | hq
  · left
    rw [← hfr]
    exact Group.isSolvable_of_surjective (f.comp L.subtype).rangeRestrict_surjective
  · rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq (f.comp L.subtype)
      with h | h
    · left
      rw [← hfr, h]
      infer_instance
    · right
      rwa [← hfr]

omit [Finite K] in
theorem toBlocks₁₁_mul_of_toBlocks₁₂ {M N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hM : M.toBlocks₁₂ = 0) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, hM, fromBlocks_multiply,
    toBlocks_fromBlocks₁₁]
  rw [Matrix.zero_mul, add_zero]

omit [Finite K] in
@[expose] def leviDet (h2 : (2 : K) ≠ 0) : spCent r K (stdSkewGsp r K) →* K where
  toFun g := (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₁₁.det
  map_one' := by
    change ((1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₁₁).det = 1
    rw [← fromBlocks_one, toBlocks_fromBlocks₁₁, det_one]
  map_mul' g h := by
    change ((((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * (((h : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).toBlocks₁₁.det = _
    have hg := congrArg Matrix.toBlocks₁₂
      (fromBlocks_of_commute_stdSkew h2 (mem_spCent.1 g.2).symm)
    rw [toBlocks_fromBlocks₁₂] at hg
    rw [toBlocks₁₁_mul_of_toBlocks₁₂ hg, det_mul]

theorem psp_skewSplit_false (hK : ringChar K ≠ 2) (hr : 2 ≤ r) {l : K} (hl0 : l ≠ 0)
    {A : StatedSp r K}
    (hA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      l • stdSkew r K)
    {R₁ R₂ : Subgroup (StatedProj (StatedSp r K))} {p m : ℕ} [Fact p.Prime]
    (hC : PropCData (projH _ A) R₁ R₂ p m) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hZ := scalars_subgroupOf_le_center (H := StatedSp r K)
  have hcent : centralizer ({A} : Set (StatedSp r K)) = spCent r K (stdSkewGsp r K) := by
    ext g
    rw [mem_centralizer_singleton_iff, mem_spCent, coe_stdSkewGsp]
    constructor
    · intro h
      have := congrArg (fun u : StatedSp r K =>
        ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h
      simp only [Subgroup.coe_mul, Units.val_mul, hA, Matrix.mul_smul, Matrix.smul_mul] at this
      exact (smul_right_injective _ hl0 this).symm
    · intro h
      apply statedSp_ext
      simp only [Subgroup.coe_mul, Units.val_mul, hA, Matrix.mul_smul, Matrix.smul_mul, h]
  have hcomm : ⁅centralizer ({A} : Set (StatedSp r K)),
      centralizer ({A} : Set (StatedSp r K))⁆ ≤ (leviSL r K).range := by
    rw [hcent, commutator_le]
    intro g hg h hh
    have hk := Abelianization.commutator_subset_ker (leviDet h2).toHomUnits
      (commutator_mem_commutator (mem_top (⟨g, hg⟩ : spCent r K (stdSkewGsp r K)))
        (mem_top (⟨h, hh⟩ : spCent r K (stdSkewGsp r K))))
    rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one] at hk
    obtain ⟨x, hx, -⟩ := eq_leviSL_of_blockDiag
      (fromBlocks_of_commute_stdSkew h2 (mem_spCent.1
        (⁅(⟨g, hg⟩ : spCent r K (stdSkewGsp r K)),
          (⟨h, hh⟩ : spCent r K (stdSkewGsp r K))⁆).2).symm) hk
    exact ⟨x, hx.symm⟩
  have hNH : (leviSL r K).range.map (QuotientGroup.mk' _) ≤
      centralizer ({QuotientGroup.mk' _ A} : Set (StatedProj (StatedSp r K))) := by
    rintro _ ⟨g, ⟨y, rfl⟩, rfl⟩
    have hy : leviSL r K y ∈ centralizer ({A} : Set (StatedSp r K)) := by
      rw [hcent]
      exact leviSL_mem_spCent y
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hy]
  have hN : Group.IsSolvable ((leviSL r K).range.map (QuotientGroup.mk'
        ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)))) ∨
      IsQuasisimple ((leviSL r K).range.map (QuotientGroup.mk'
        ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)))) := by
    refine solvable_or_quasisimple_map ?_ _
    by_cases h3 : r = 2 ∧ Nat.card K = 3
    · left
      obtain ⟨rfl, hK3⟩ := h3
      have hs := isSolvable_SL_two_of_card_three hK3 (F := K)
      exact Group.isSolvable_of_surjective (f := (MonoidHom.ofInjective (leviSL_injective (r := 2)
        (K := K))).toMonoidHom) (MonoidHom.ofInjective _).surjective
    · right
      refine isQuasisimple_leviSL_range hr ?_
      by_contra hcon
      push Not at hcon
      have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
      have h2' : 2 ≤ Nat.card K := Finite.one_lt_card
      obtain ⟨j, hj⟩ := hodd
      exact h3 ⟨by omega, by omega⟩
  exact propCData_false_of_layer hC hNH
    (fun L hL hp => (le_map_commutator_of_perfect_mk hZ A hL hp).trans (map_mono hcomm)) hN

section Abstract

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem unitary_layer_abstract {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) [CharP K ℓ] (hr : 2 ≤ r)
    (hdim : Module.finrank K V = 2 * r) {B : LinearMap.BilinForm K V} (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) {A : LinearMap.GeneralLinearGroup K V}
    (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1) {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1)
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = (-d) * B v w) :
    Group.IsSolvable (UnitaryHigher.similitudeCentralizer B A) ∨
      ∃ L : Subgroup (UnitaryHigher.similitudeCentralizer B A), L.Normal ∧ IsQuasisimple L ∧
        ⁅(⊤ : Subgroup (UnitaryHigher.similitudeCentralizer B A)), ⊤⁆ ≤ L := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hd0 : d ≠ 0 := fun h => hd 0 (by rw [h]; ring)
  have hodd : Odd (Nat.card K) := by rw [hKc]; exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨-, -, hnonsplit⟩ := UnitaryHigher.odd_symplectic_scalar_square_centralizer_structure hℓ
    hℓ2 hf hKc (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  obtain ⟨-, hF, hcard, hfinrank, bar, hbar, -, hbarbar, -, hneg⟩ := hnonsplit hd
  obtain ⟨hh, -, hsymm, hsep, hiff⟩ := hneg (by rw [neg_div, div_self hd0])
  let : Field (UnitaryHigher.scalarSquareField (A : Module.End K V)) := hF.toField
  have hEodd : Odd (Nat.card (UnitaryHigher.scalarSquareField (A : Module.End K V))) := by
    rw [hcard]
    exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
  have := CatalogueBSymplecticB.finite_of_odd_card hEodd
  have : Module.Finite (UnitaryHigher.scalarSquareField (A : Module.End K V)) V :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule_finite _
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
  let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[UnitaryHigher.scalarSquareField (A : Module.End K V)]
    UnitaryHigher.scalarSquareField (A : Module.End K V) := hh
  have hnd : h'.Nondegenerate :=
    ⟨hsep, fun y hy => hsep y fun x => by
      rw [← hsymm.eq x y]
      exact (congrArg bar (hy x)).trans (map_zero bar)⟩
  have hsigma : sigma ^ 2 = 1 := RingEquiv.ext hbarbar
  have hne : sigma ≠ 1 := by
    intro heq
    let x : UnitaryHigher.scalarSquareField (A : Module.End K V) :=
      ⟨A, Algebra.self_mem_adjoin_singleton K _⟩
    have hx := hbar x 0 1 (by simp only [zero_smul, zero_add, one_smul, x])
    have hfix : bar x = x := DFunLike.congr_fun heq x
    rw [hfix] at hx
    simp only [zero_smul, zero_sub, one_smul, x] at hx
    have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
    have hA2 : (2 : K) • (A : Module.End K V) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hx]
      exact add_neg_cancel _
    apply hAns 0
    rw [zero_smul]
    calc (A : Module.End K V) = (2 : K)⁻¹ • ((2 : K) • (A : Module.End K V)) := by
          rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = 0 := by rw [hA2, smul_zero]
  have hfixcard : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield
      (UnitaryHigher.scalarSquareField (A : Module.End K V)) sigma) = ℓ ^ f := by
    have h1 := CatalogueBLinearTwoDescent.fixedSubfield_finrank _ sigma hsigma hne
    let _ : Fintype (UnitaryHigher.scalarSquareField (A : Module.End K V)) := Fintype.ofFinite _
    let _ : Fintype (CatalogueBLinearTwoDescent.fixedSubfield
      (UnitaryHigher.scalarSquareField (A : Module.End K V)) sigma) := Fintype.ofFinite _
    have h2 := Module.card_eq_pow_finrank (K := CatalogueBLinearTwoDescent.fixedSubfield
      (UnitaryHigher.scalarSquareField (A : Module.End K V)) sigma)
      (V := UnitaryHigher.scalarSquareField (A : Module.End K V))
    rw [h1, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard] at h2
    exact (Nat.pow_left_injective two_ne_zero h2).symm
  have hq3 : 3 ≤ ℓ ^ f := by
    have := hℓ.two_le
    have : 3 ≤ ℓ := by omega
    exact this.trans (Nat.le_self_pow (by omega) ℓ)
  obtain ⟨Φ⟩ : Nonempty (UnitaryHigher.similitudeCentralizer B A ≃*
      CatalogueBUnitaryIsometry.isometryGroup h') :=
    ⟨(CatalogueBSymplecticB.centralizerSimilitudeEquiv B A).symm.trans
      (CatalogueBSymplecticB.evaluationIsometryEquiv B A
        (CatalogueBUnitaryIsometry.isometryGroup h') (fun φ => ∀ v w, hh (φ v) (φ w) = hh v w)
        (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff)⟩
  by_cases hrq : 3 ≤ r ∨ 5 ≤ ℓ ^ f
  · right
    have hquasi : IsQuasisimple (CatalogueBUnitaryIsometry.specialIsometry h') :=
      (CatalogueBUnitaryIsometry.isometry_all_dimensions_nonsmall h' hsymm hnd hsigma hne
        (by rw [hfinrank]; omega) (by rw [hfixcard]; omega) (by rw [hfinrank]; omega)
        (by
          rw [hfinrank, hfixcard]
          intro h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          simp only at h1 h2
          omega)).1
    refine ⟨(CatalogueBUnitaryIsometry.specialIsometry h').comap Φ.toMonoidHom,
      Subgroup.Normal.comap (MonoidHom.normal_ker _) _, isQuasisimple_comap_equiv Φ hquasi, ?_⟩
    rw [CatalogueBUnitaryIsometry.specialIsometry, MonoidHom.comap_ker]
    exact Abelianization.commutator_subset_ker _
  · left
    push Not at hrq
    have hr2 : r = 2 := by omega
    have hq : ℓ ^ f = 3 := by
      have hqodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
      obtain ⟨j, hj⟩ := hqodd
      omega
    have hs := (CatalogueBUnitaryIsometry.isometry_all_dimensions_small h' hsymm hnd hsigma hne
      (Or.inr ⟨by rw [hfinrank, hr2], by rw [hfixcard, hq]⟩)).1
    exact Group.isSolvable_of_isSolvable_injective (f := Φ.toMonoidHom) Φ.injective

end Abstract

theorem psp_skewNs_false {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    {A : StatedSp r K}
    (hA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      skewNs r K d)
    {R₁ R₂ : Subgroup (StatedProj (StatedSp r K))} {p m : ℕ} [Fact p.Prime]
    (hC : PropCData (projH _ A) R₁ R₂ p m) : False := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hd0 : d ≠ 0 := fun h => hd 0 (by rw [h]; ring)
  have hZ := scalars_subgroupOf_le_center (H := StatedSp r K)
  set Ag : gsp r K := ⟨A, statedSp_le_gsp A.2⟩ with hAg
  have hAgm : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      skewNs r K d := hA
  have hAns : ∀ c : Kˣ, (Ag : GL (Fin r ⊕ Fin r) K) ≠
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro c hc
    apply skewNsGsp_ne_scalar (r := r) (by omega) hd0 c
    rw [← hc]
    exact Units.ext (by rw [coe_skewNsGsp, hAgm])
  have hAA : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1 := by
    rw [hAgm, skewNs_mul_self]
  have hJ : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      formJ r K * ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (-d) • formJ r K := by
    rw [hAgm, skewNs_similitude]
  have hAμ : ∀ v w, pairedSympForm K r (((linA Ag : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA Ag : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = (-d) * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude hJ]
  have hcent : centralizer ({A} : Set (StatedSp r K)) = spCent r K Ag := by
    ext g
    rw [mem_centralizer_singleton_iff, mem_spCent]
    constructor
    · intro h
      have := congrArg (fun u : StatedSp r K =>
        ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h
      simp only [Subgroup.coe_mul, Units.val_mul] at this
      exact this.symm
    · intro h
      apply statedSp_ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      exact h.symm
  rcases unitary_layer_abstract hℓ hℓ2 hf hKc hr finrank_standard pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate
      (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) hd (linA_mul_self hAA) hAμ with
    hs | ⟨L, hLn, hLq, hLc⟩
  ·
    have hs' : Group.IsSolvable (spCent r K Ag) := Group.isSolvable_of_isSolvable_injective
      (f := (spCentEquiv Ag).toMonoidHom) (spCentEquiv Ag).injective
    have hN : Group.IsSolvable ((spCent r K Ag).map (QuotientGroup.mk'
        ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)))) ∨
        IsQuasisimple ((spCent r K Ag).map (QuotientGroup.mk'
          ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)))) :=
      solvable_or_quasisimple_map (Or.inl hs') _
    have hNH : (spCent r K Ag).map (QuotientGroup.mk' _) ≤
        centralizer ({QuotientGroup.mk' _ A} : Set (StatedProj (StatedSp r K))) := by
      rintro _ ⟨g, hg, rfl⟩
      rw [← hcent] at hg
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hg]
    refine propCData_false_of_layer hC hNH (fun L' hL' hp => ?_) hN
    refine (le_map_commutator_of_perfect_mk hZ A hL' hp).trans (map_mono ?_)
    rw [hcent]
    exact commutator_le_self _
  ·
    set L' := (L.comap (spCentEquiv Ag).toMonoidHom).map (spCent r K Ag).subtype with hL'
    have hL'C : L' ≤ spCent r K Ag := map_subtype_le _
    have hL'q : IsQuasisimple L' := isQuasisimple_map_subtype_comap (spCentEquiv Ag) hLq
    have hcomm : ⁅centralizer ({A} : Set (StatedSp r K)),
        centralizer ({A} : Set (StatedSp r K))⁆ ≤ L' := by
      rw [hcent, commutator_le]
      intro g hg h hh
      refine ⟨⁅(⟨g, hg⟩ : spCent r K Ag), (⟨h, hh⟩ : spCent r K Ag)⁆, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement]
      exact hLc (commutator_mem_commutator (mem_top _) (mem_top _))
    have hNH : L'.map (QuotientGroup.mk' _) ≤
        centralizer ({QuotientGroup.mk' _ A} : Set (StatedProj (StatedSp r K))) := by
      rintro _ ⟨g, hg, rfl⟩
      have hg' := hL'C hg
      rw [← hcent] at hg'
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        mem_centralizer_singleton_iff.1 hg']
    exact propCData_false_of_layer hC hNH
      (fun L₀ hL₀ hp => (le_map_commutator_of_perfect_mk hZ A hL₀ hp).trans (map_mono hcomm))
      (solvable_or_quasisimple_map (Or.inr hL'q) _)

end CFSG.ComponentClassification.Burgoyne.C
