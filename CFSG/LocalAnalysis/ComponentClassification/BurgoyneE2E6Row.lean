module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Odd
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Three
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralD5

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar
  root_diagonal_conjugation)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.HighestRoot (rankOneGroup rankOneGroup_adjDatum centralizerCondition_rankOneGroup
  noG2_E6' symmetrizer_le_one neg_one_eq_HSL_neg_one isolatedCheck_E6)
open scoped MatrixGroups

@[expose] def e6Gamma1 : List ((Fin (Tag.rank .E6) → ℤ) × ℤ) :=
  [(Pi.single (e6Node 1) 1, 3), (Pi.single (e6Node 2) 1, 4), (Pi.single (e6Node 3) 1, 1),
    (Pi.single (e6Node 4) 1, 1), (Pi.single (e6Node 5) 1, 5)]

theorem e6Gamma1_reg : ∀ α ∈ rootFinset .E6,
    (∑ j, regCoweight e6Gamma1 j * α j) ≠ 0 ∧ (∑ j, regCoweight e6Gamma1 j * α j).natAbs < 12 := by
  decide +kernel

theorem e6Gamma1_nodes : ∀ y ∈ e6Gamma1, ∃ k : Fin 5, y.1 = Pi.single (e6D5Node k) 1 := by
  decide


abbrev e6QD5 (K : Type) [Field K] : Subgroup (adjointGroup .E6 K) :=
  ⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5Node k)

theorem isQuasisimple_e6QD5 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) : IsQuasisimple (e6QD5 K) :=
  (exists_psi_D5_E6 hp hp2 hK).choose_spec.2.2.1

theorem map_e6QD5 {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    (e6QD5 K).map (adjointGroup .E6 K).subtype =
      rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsD5)) := by
  rw [map_subtype_iSup_rankOne, subsystemGroup_eq_rootSpan, rootCharKernel_e6BitsD5 hK2]
  rfl

theorem e6QD5_le_fixedSubgroup {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) :
    e6QD5 K ≤ fixedSubgroup (rootDiagAut .E6 K (bitsTuple e6BitsD5)) := by
  intro g hg
  rw [mem_fixedSubgroup_rootDiagAut]
  obtain ⟨hSX, -⟩ := odd_toral_involution_centralizer_p_component_root_reduction .E6 K hK2 _
    (bitsTuple_mem _)
  refine hSX ?_
  rw [← map_e6QD5 hK2]
  exact ⟨g, hg, rfl⟩

theorem fixedSubgroup_le_normalizer_e6QD5 {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) :
    fixedSubgroup (rootDiagAut .E6 K (bitsTuple e6BitsD5)) ≤
      normalizer ((e6QD5 K : Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) := by
  obtain ⟨hSX, hSn, -⟩ := odd_toral_involution_centralizer_p_component_root_reduction .E6 K hK2 _
    (bitsTuple_mem _)
  have hmem : ∀ x : adjointGroup .E6 K, x ∈ e6QD5 K ↔
      (x : ModGL .E6 K) ∈ rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsD5)) := by
    intro x
    rw [← map_e6QD5 hK2]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [Subtype.ext hyx] at hy
  intro g hg
  have hgX := mem_fixedSubgroup_rootDiagAut.1 hg
  rw [mem_normalizer_iff]
  intro x
  rw [hmem, hmem]
  have hconj : ∀ y : ModGL .E6 K, y ∈ rootSpan .E6 K (rootCharKernel (bitsTuple (K := K)
      e6BitsD5)) → y ∈ toralCentralizer .E6 K (bitsTuple e6BitsD5) →
      ∀ h : ModGL .E6 K, h ∈ toralCentralizer .E6 K (bitsTuple e6BitsD5) →
        h * y * h⁻¹ ∈ rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsD5)) := by
    intro y hy hyX h hh
    exact hSn.conj_mem ⟨y, hyX⟩ hy ⟨h, hh⟩
  constructor
  · intro hx
    have hxX : (x : ModGL .E6 K) ∈ toralCentralizer .E6 K (bitsTuple e6BitsD5) := hSX hx
    have := hconj _ hx hxX _ hgX
    simpa using this
  · intro hx
    have hx' : ((g * x * g⁻¹ : adjointGroup .E6 K) : ModGL .E6 K) ∈
        toralCentralizer .E6 K (bitsTuple e6BitsD5) := hSX hx
    have := hconj _ hx hx' _ (inv_mem hgX)
    simpa [mul_assoc] using this

theorem rankOne_le_e6QD5 (K : Type) [Field K] (k : Fin 5) :
    rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5Node k) ≤ e6QD5 K :=
  le_iSup (fun k => rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5Node k)) k

abbrev torusEltE6 (K : Type) [Field K] (i : Fin (Tag.rank .E6)) (t : Kˣ) : adjointGroup .E6 K :=
  ⟨torusElt .E6 K i t, torusElt_mem_adjointGroup i t⟩

abbrev e6RootZero (K : Type) [Field K] : Subgroup (adjointGroup .E6 K) :=
  rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6Node 0)

@[expose] def rhoZero (K : Type) [Field K] : SL2 K →* adjointGroup .E6 K :=
  (simpleRootSL2 .E6 K (e6Node 0)).codRestrict _ fun A => simpleRootSL2_mem_adjointGroup _ A

theorem coe_rhoZero (K : Type) [Field K] (A : SL2 K) :
    ((rhoZero K A : adjointGroup .E6 K) : ModGL .E6 K) = simpleRootSL2 .E6 K (e6Node 0) A :=
  rfl

theorem range_rhoZero (K : Type) [Field K] : (rhoZero K).range = e6RootZero K := by
  ext x
  change _ ↔ x ∈ rankOneGroup (adjDatum (rootOperatorFamily .E6) K) (Pi.single (e6Node 0) 1)
  rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf,
    ← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, Subtype.ext hA⟩

theorem rhoZero_injective {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    Function.Injective (rhoZero K) := fun _ _ h =>
  simpleRootSL2_injective hK2 (e6Node 0) (congrArg Subtype.val h)

theorem rhoZero_neg_one (K : Type) [Field K] : rhoZero K (-1) = torusEltE6 K (e6Node 0) (-1) := by
  apply Subtype.ext
  rw [coe_rhoZero, neg_one_eq_HSL_neg_one, simpleRootSL2_HSL]

@[expose] def e6RootZeroEquiv {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    e6RootZero K ≃* SL2 K :=
  ((MonoidHom.ofInjective (rhoZero_injective hK2)).trans
    (MulEquiv.subgroupCongr (range_rhoZero K))).symm

theorem e6RootZeroEquiv_symm_apply {K : Type} [Field K] (hK2 : ringChar K ≠ 2) (A : SL2 K) :
    (((e6RootZeroEquiv hK2).symm A : e6RootZero K) : adjointGroup .E6 K) = rhoZero K A :=
  rfl

theorem torusEltE6_zero_mem_e6RootZero (K : Type) [Field K] :
    torusEltE6 K (e6Node 0) (-1) ∈ e6RootZero K := by
  rw [← range_rhoZero, ← rhoZero_neg_one]
  exact ⟨-1, rfl⟩

theorem center_e6RootZero {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    (center (e6RootZero K)).map (e6RootZero K).subtype =
      zpowers (torusEltE6 K (e6Node 0) (-1)) := by
  have he : (((e6RootZeroEquiv hK2) ⟨_, torusEltE6_zero_mem_e6RootZero K⟩ : SL2 K) :
      Matrix (Fin 2) (Fin 2) K) = -1 := by
    have : (e6RootZeroEquiv hK2) ⟨_, torusEltE6_zero_mem_e6RootZero K⟩ = -1 := by
      rw [← MulEquiv.eq_symm_apply]
      apply Subtype.ext
      rw [e6RootZeroEquiv_symm_apply, rhoZero_neg_one]
    rw [this]
    simp
  rw [Proj.center_eq_zpowers_of_sl (e6RootZeroEquiv hK2) he, MonoidHom.map_zpowers]
  rfl

theorem orderOf_torusEltE6_zero {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    orderOf (torusEltE6 K (e6Node 0) (-1)) = 2 := by
  rw [← rhoZero_neg_one, orderOf_injective _ (rhoZero_injective hK2)]
  have h1 : (-1 : SL2 K) ≠ 1 := by
    intro h
    have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at this
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 this
  exact orderOf_eq_prime (by rw [neg_one_sq]) h1

theorem e6RootZero_le_centralizer {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    e6RootZero K ≤ centralizer ({torusEltE6 K (e6Node 0) (-1)} : Set (adjointGroup .E6 K)) := by
  intro s hs
  rw [mem_centralizer_singleton_iff]
  have hz : torusEltE6 K (e6Node 0) (-1) ∈ (center (e6RootZero K)).map (e6RootZero K).subtype := by
    rw [center_e6RootZero hK2]
    exact mem_zpowers _
  obtain ⟨z, hz, hzeq⟩ := hz
  have := (mem_center_iff.1 hz) ⟨s, hs⟩
  rw [← hzeq]
  exact congrArg Subtype.val this

theorem isQuasisimple_e6RootZero {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    (h5 : 5 ≤ Nat.card K) : IsQuasisimple (e6RootZero K) := by
  obtain ⟨hle, -, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .E6 K hK2
    (isRoot_single _ (e6Node 0))
  have hq := (hfin.2 h5).1
  have e : e6RootZero K = (rootSubgroup .E6 K (Pi.single (e6Node 0) 1) ⊔
      rootSubgroup .E6 K (-Pi.single (e6Node 0) 1)).subgroupOf (adjointGroup .E6 K) :=
    rankOneGroup_adjDatum _ (isRoot_single _ _)
  rw [e]
  exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq

theorem torusEltE6_mem_rankOne {K : Type} [Field K] (i : Fin (Tag.rank .E6)) (t : Kˣ) :
    torusEltE6 K i t ∈ rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup i := by
  change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily .E6) K) (Pi.single i 1)
  rw [rankOneGroup_adjDatum _ (isRoot_single _ i), mem_subgroupOf]
  change torusElt .E6 K i t ∈ rootSubgroup .E6 K (Pi.single i 1) ⊔
    rootSubgroup .E6 K (-Pi.single i 1)
  rw [← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
  exact ⟨HSL t, simpleRootSL2_HSL i t⟩

theorem centralizer_le_normalizer_e6RootZero {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) :
    centralizer ({torusEltE6 K (e6Node 0) (-1)} : Set (adjointGroup .E6 K)) ≤
      normalizer ((e6RootZero K : Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) :=
  (centralizerCondition_rankOneGroup noG2_E6' hK2 (symmetrizer_le_one .E6 rfl _)
    isolatedCheck_E6 _ (torusEltE6_mem_rankOne _ _) (orderOf_torusEltE6_zero hK2)).1

abbrev xZero (K : Type) [Field K] (c : K) : adjointGroup .E6 K :=
  ⟨xUnit .E6 K (e6Node 0) c, xUnit_mem_adjointGroup _ c⟩

theorem xZero_mem_e6RootZero (K : Type) [Field K] (c : K) : xZero K c ∈ e6RootZero K := by
  rw [← range_rhoZero]
  exact ⟨uSL c, Subtype.ext (simpleRootSL2_uSL _ c)⟩

theorem rootDiagAut_mem_e6RootZero {K : Type} [Field K] (b : Fin (Tag.rank .E6) → Kˣ)
    {s : adjointGroup .E6 K} (hs : s ∈ e6RootZero K) : rootDiagAut .E6 K b s ∈ e6RootZero K := by
  rw [← range_rhoZero] at hs ⊢
  obtain ⟨A, rfl⟩ := hs
  have hR : (rhoZero K).range.map (adjointGroup .E6 K).subtype =
      Subgroup.closure (Set.range (xUnit .E6 K (e6Node 0)) ∪
        Set.range (yUnit .E6 K (e6Node 0))) := by
    rw [← range_simpleRootSL2]
    ext y
    constructor
    · rintro ⟨_, ⟨B, rfl⟩, rfl⟩
      exact ⟨B, rfl⟩
    · rintro ⟨B, rfl⟩
      exact ⟨rhoZero K B, ⟨B, rfl⟩, rfl⟩
  have hconj : Subgroup.closure (Set.range (xUnit .E6 K (e6Node 0)) ∪
      Set.range (yUnit .E6 K (e6Node 0))) ≤ (Subgroup.closure
        (Set.range (xUnit .E6 K (e6Node 0)) ∪ Set.range (yUnit .E6 K (e6Node 0)))).comap
          (MulAut.conj (rootDiagUnit .E6 b)).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation .E6 K b).1]
      exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation .E6 K b).2.1]
      exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  have hA : (rhoZero K A : ModGL .E6 K) ∈ Subgroup.closure (Set.range (xUnit .E6 K (e6Node 0)) ∪
      Set.range (yUnit .E6 K (e6Node 0))) := by
    rw [← hR]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  have h1 := hconj hA
  rw [← hR] at h1
  obtain ⟨y, hy, hyeq⟩ := h1
  rwa [show rootDiagAut .E6 K b (rhoZero K A) = y from
    Subtype.ext ((coe_rootDiagAut b (rhoZero K A)).trans hyeq.symm)]

theorem rootDiagAut_mem_e6RootZero_iff {K : Type} [Field K] (b : Fin (Tag.rank .E6) → Kˣ)
    (s : adjointGroup .E6 K) : rootDiagAut .E6 K b s ∈ e6RootZero K ↔ s ∈ e6RootZero K := by
  refine ⟨fun h => ?_, rootDiagAut_mem_e6RootZero b⟩
  have h' := rootDiagAut_mem_e6RootZero b⁻¹ h
  have e : rootDiagAut .E6 K b⁻¹ (rootDiagAut .E6 K b s) = s := by
    have h1 : rootDiagAut .E6 K b⁻¹ * rootDiagAut .E6 K b = 1 := by
      change rootDiagAutHom .E6 K b⁻¹ * rootDiagAutHom .E6 K b = 1
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [← MulAut.mul_apply, h1, MulAut.one_apply]
  rwa [e] at h'

theorem rootDiagAut_xZero_ne {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    rootDiagAut .E6 K (bitsTuple e6BitsD5) (xZero K 1) ≠ xZero K 1 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_rootDiagAut, (root_diagonal_conjugation .E6 K (bitsTuple e6BitsD5)).1] at h'
  have hb : (bitsTuple (K := K) e6BitsD5 (e6Node 0) : K) = -1 := by
    simp [bitsTuple, show e6BitsD5 (e6Node 0) = true from by decide]
  rw [hb, neg_one_mul] at h'
  have h2 : rhoZero K (uSL (-1)) = rhoZero K (uSL 1) :=
    Subtype.ext ((simpleRootSL2_uSL _ _).trans (h'.trans (simpleRootSL2_uSL _ _).symm))
  have h3 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 1)
    (rhoZero_injective hK2 h2)
  simp [uSL] at h3
  exact Ring.neg_one_ne_one_of_char_ne_two hK2 h3

theorem exists_eq_rootDiagAut_of_odd_fix_e6QD5 {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) {β : MulAut (adjointGroup .E6 K)} (hβ : Odd (orderOf β))
    (hfix : ∀ x ∈ e6QD5 K, β x = x) :
    ∃ e : Fin (Tag.rank .E6) → Kˣ, β = rootDiagAut .E6 K e ∧
      ∀ k : Fin 5, rootChar e (Pi.single (e6D5Node k) 1) = 1 := by
  have hQ : ∀ (k : Fin 5) (u : adjointGroup .E6 K), (u : ModGL .E6 K) ∈
      rootSubgroup .E6 K (Pi.single (e6D5Node k) 1) ⊔
        rootSubgroup .E6 K (-Pi.single (e6D5Node k) 1) → β u = u := by
    intro k u hu
    refine hfix u (rankOne_le_e6QD5 K k ?_)
    change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily .E6) K) (Pi.single (e6D5Node k) 1)
    rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf]
    exact hu
  obtain ⟨e, he⟩ := exists_eq_rootDiagAut_of_odd_fix (Or.inl rfl) hK2 hβ (e6D5Node 0)
    (fun x hx => hfix x (rankOne_le_e6QD5 K 0 hx)) e6Gamma1
    (fun y hy => by obtain ⟨k, hk⟩ := e6Gamma1_nodes y hy; rw [hk]; exact isRoot_single _ _)
    (fun y hy u hu => by
      obtain ⟨k, hk⟩ := e6Gamma1_nodes y hy
      rw [hk] at hu
      exact hQ k u hu)
    12 (fun α hα => e6Gamma1_reg α (mem_rootFinset.2 hα))
  refine ⟨e, he, fun k => rootChar_eq_one_of_fix_pinnedX (isRoot_single _ _) ?_⟩
  rw [← he]
  refine hQ k _ (le_sup_left (a := rootSubgroup .E6 K (Pi.single (e6D5Node k) 1)) ?_)
  exact Subgroup.subset_closure ⟨1, rfl⟩

theorem burgTorusFor_E6_t1 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K) :
    BurgTorusFor (rootDiagAut .E6 K (bitsTuple e6BitsD5)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (one_le_and_three_le_of_card hp hp2 hK).1 hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨p', n', hp', hp'2, hn', ⟨eGF⟩⟩ := PSL.exists_sl_galoisField (K := K) hK2
  refine ⟨e6QD5 K, isQuasisimple_e6QD5 hp hp2 hK, e6QD5_le_fixedSubgroup hK2,
    fixedSubgroup_le_normalizer_e6QD5 hK2, torusEltE6 K (e6Node 0) (-1), e6RootZero K,
    orderOf_torusEltE6_zero hK2, isQuasisimple_e6RootZero hK2 h5, e6RootZero_le_centralizer hK2,
    centralizer_le_normalizer_e6RootZero hK2,
    ⟨p', n', hp', hp'2, hn', ⟨(e6RootZeroEquiv hK2).trans eGF⟩⟩, center_e6RootZero hK2,
    rootDiagAut_mem_e6RootZero_iff _,
    ⟨xZero K 1, xZero_mem_e6RootZero K 1, rootDiagAut_xZero_ne hK2⟩, fun β hβ _ hfix => ?_⟩
  obtain ⟨e, rfl, he⟩ := exists_eq_rootDiagAut_of_odd_fix_e6QD5 hK2 hβ hfix
  refine ⟨rootDiagAut_mem_e6RootZero_iff e, fun hS => ?_⟩
  have h0 : rootChar e (Pi.single (e6Node 0) 1) = 1 := by
    refine rootChar_eq_one_of_fix_pinnedX (isRoot_single _ _) ?_
    have hx : (⟨pinnedX .E6 K (Pi.single (e6Node 0) 1) 1,
        pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup .E6 K) = xZero K 1 :=
      Subtype.ext (pinnedX_single _ _ _ _)
    rw [hx]
    exact hS _ (xZero_mem_e6RootZero K 1)
  refine rootDiagAut_eq_one_of_rootChar fun j => ?_
  by_cases hj : j = e6Node 0
  · rw [hj]
    exact h0
  · obtain ⟨k, rfl⟩ : ∃ k, e6D5Node k = j := by
      by_contra hne
      push Not at hne
      exact hj (eq_zero_of_forall_e6D5Node_ne j hne)
    exact he k

theorem burgCoreFor_E6_t1_three {K : Type} [Field K] [Finite K] (h3 : Nat.card K = 3) :
    BurgCoreFor (rootDiagAut .E6 K (bitsTuple e6BitsD5)) := by
  have hK2 : ringChar K ≠ 2 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact h3)
    rw [ringChar.eq K 3]
    decide
  refine ⟨pPrimeCore_fixedSubgroup_rootDiagAut
    (pPrimeCore_toralCentralizer_eq_bot_three h3 hK2 (bitsTuple_mem _)), fun β hβ _ hfix => ?_⟩
  obtain ⟨e, rfl, -⟩ := exists_eq_rootDiagAut_of_odd_fix_e6QD5 hK2 hβ fun x hx =>
    hfix x (e6QD5_le_fixedSubgroup hK2 hx)
  have hsq : rootDiagAut .E6 K e ^ 2 = 1 := by
    have he2 : e ^ 2 = 1 := funext fun j => units_sq_eq_one_of_card_three h3 (e j)
    change rootDiagAutHom .E6 K e ^ 2 = 1
    rw [← map_pow, he2, map_one]
  have hd : orderOf (rootDiagAut .E6 K e) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1 : orderOf (rootDiagAut .E6 K e) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact h
    · rw [h] at hβ
      exact absurd hβ (by decide)
  exact orderOf_eq_one_iff.1 h1

end CFSG.ComponentClassification.Burgoyne.E2
