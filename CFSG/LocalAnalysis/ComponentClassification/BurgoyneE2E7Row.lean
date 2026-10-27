module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Torus
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Levi
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LieType.HighestRoot.CentChevalleyThree
public import CFSG.LieType.HighestRoot.CentChevalleyData
public import CFSG.RankThree.PartOne.KE.OrdinaryEPointwise

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit root_diagonal_conjugation)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.HighestRoot (rankOneGroup rankOneGroup_adjDatum isolatedCheck
  centralizerCondition_rankOneGroup noG2_E7' symmetrizer_le_one neg_one_eq_HSL_neg_one)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.Chevalley (conjGL baseChangeGL_simpleRootSL2)
open scoped MatrixGroups

@[expose] def witE7Six : List ℕ :=
  [143165832, 143169672, 143165577, 143165592, 143169672, 0, 0, 143165832, 143165577, 143169672,
    143165592, 143165577, 143165577, 143165592, 143165592, 143169672, 0, 0, 0, 0, 143165577,
    143165577, 143165592, 143165577, 143165592, 143165577, 143165577, 143165592, 0, 0, 0, 0,
    143165577, 143165577, 143165577, 143165577, 143165592, 143165577, 0, 143165577, 0, 0, 0, 0,
    143165577, 143165577, 143165577, 0, 143165577, 0, 143165577, 0, 0, 0, 0, 0, 143165577, 0,
    143165577, 0, 0, 143165577, 0, 0, 0, 0, 0, 143165577, 0, 0, 143165832, 0, 0, 0, 0, 0, 0,
    143165832, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 143165577, 0, 0, 0, 0, 0, 143165577,
    143165577, 0, 0, 143165577, 0, 0, 143165832, 0, 0, 143165832, 0, 143165592, 0, 143165592,
    143165592, 143165592, 143165592, 143165592, 143165592, 143165592, 143165832, 143165832,
    143165577, 143165577, 143165577, 143165577]

theorem isolatedCheck_E7_six : isolatedCheck .E7 (e7Node 6) witE7Six = true := by
  decide +kernel

theorem conjGL_one' {M : Type*} [Field M] (A : SL2 M) : conjGL (1 : GL (Fin 2) M) A = A :=
  Subtype.ext (by simp [conjGL])


abbrev e7RootSix (K : Type) [Field K] : Subgroup (adjointGroup .E7 K) :=
  rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7Node 6)

@[expose] def rhoSix (K : Type) [Field K] : SL2 K →* adjointGroup .E7 K :=
  (simpleRootSL2 .E7 K (e7Node 6)).codRestrict _ fun A => simpleRootSL2_mem_adjointGroup _ A

theorem coe_rhoSix (K : Type) [Field K] (A : SL2 K) :
    ((rhoSix K A : adjointGroup .E7 K) : ModGL .E7 K) = simpleRootSL2 .E7 K (e7Node 6) A :=
  rfl

theorem range_rhoSix (K : Type) [Field K] : (rhoSix K).range = e7RootSix K := by
  ext x
  change _ ↔ x ∈ rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single (e7Node 6) 1)
  rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf,
    ← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, Subtype.ext hA⟩

theorem rhoSix_injective {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    Function.Injective (rhoSix K) := fun _ _ h =>
  simpleRootSL2_injective hK2 (e7Node 6) (congrArg Subtype.val h)

theorem rhoSix_neg_one (K : Type) [Field K] : rhoSix K (-1) = torusEltC K (e7Node 6) (-1) := by
  apply Subtype.ext
  rw [coe_rhoSix, neg_one_eq_HSL_neg_one, simpleRootSL2_HSL]

@[expose] def e7RootSixEquiv {K : Type} [Field K] (hK2 : ringChar K ≠ 2) : e7RootSix K ≃* SL2 K :=
  ((MonoidHom.ofInjective (rhoSix_injective hK2)).trans
    (MulEquiv.subgroupCongr (range_rhoSix K))).symm

theorem e7RootSixEquiv_symm_apply {K : Type} [Field K] (hK2 : ringChar K ≠ 2) (A : SL2 K) :
    (((e7RootSixEquiv hK2).symm A : e7RootSix K) : adjointGroup .E7 K) = rhoSix K A :=
  rfl

theorem torusEltC_six_mem_e7RootSix (K : Type) [Field K] :
    torusEltC K (e7Node 6) (-1) ∈ e7RootSix K := by
  rw [← range_rhoSix, ← rhoSix_neg_one]
  exact ⟨-1, rfl⟩

theorem center_e7RootSix {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    (center (e7RootSix K)).map (e7RootSix K).subtype = zpowers (torusEltC K (e7Node 6) (-1)) := by
  have he : (((e7RootSixEquiv hK2) ⟨_, torusEltC_six_mem_e7RootSix K⟩ : SL2 K) :
      Matrix (Fin 2) (Fin 2) K) = -1 := by
    have : (e7RootSixEquiv hK2) ⟨_, torusEltC_six_mem_e7RootSix K⟩ = -1 := by
      rw [← MulEquiv.eq_symm_apply]
      apply Subtype.ext
      rw [e7RootSixEquiv_symm_apply, rhoSix_neg_one]
    rw [this]
    simp
  rw [Proj.center_eq_zpowers_of_sl (e7RootSixEquiv hK2) he, MonoidHom.map_zpowers]
  rfl

theorem orderOf_torusEltC_six {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    orderOf (torusEltC K (e7Node 6) (-1)) = 2 := by
  rw [← rhoSix_neg_one, orderOf_injective _ (rhoSix_injective hK2)]
  have h1 : (-1 : SL2 K) ≠ 1 := by
    intro h
    have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at this
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 this
  exact orderOf_eq_prime (by rw [neg_one_sq]) h1

theorem e7RootSix_le_centralizer {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    e7RootSix K ≤ centralizer ({torusEltC K (e7Node 6) (-1)} : Set (adjointGroup .E7 K)) := by
  intro s hs
  rw [mem_centralizer_singleton_iff]
  have hz : torusEltC K (e7Node 6) (-1) ∈ (center (e7RootSix K)).map (e7RootSix K).subtype := by
    rw [center_e7RootSix hK2]
    exact mem_zpowers _
  obtain ⟨z, hz, hzeq⟩ := hz
  have := (mem_center_iff.1 hz) ⟨s, hs⟩
  rw [← hzeq]
  exact congrArg Subtype.val this

theorem isQuasisimple_e7RootSix {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    (h5 : 5 ≤ Nat.card K) : IsQuasisimple (e7RootSix K) := by
  obtain ⟨hle, -, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .E7 K hK2
    (isRoot_single _ (e7Node 6))
  have hq := (hfin.2 h5).1
  have e : e7RootSix K = (rootSubgroup .E7 K (Pi.single (e7Node 6) 1) ⊔
      rootSubgroup .E7 K (-Pi.single (e7Node 6) 1)).subgroupOf (adjointGroup .E7 K) :=
    rankOneGroup_adjDatum _ (isRoot_single _ _)
  rw [e]
  exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq

theorem centralizer_le_normalizer_e7RootSix {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) :
    centralizer ({torusEltC K (e7Node 6) (-1)} : Set (adjointGroup .E7 K)) ≤
      normalizer ((e7RootSix K : Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) :=
  (centralizerCondition_rankOneGroup noG2_E7' hK2 (symmetrizer_le_one .E7 rfl _)
    isolatedCheck_E7_six _ (torusEltC_mem_rankOne _ _) (orderOf_torusEltC_six hK2)).1

abbrev xSix (K : Type) [Field K] (c : K) : adjointGroup .E7 K :=
  ⟨xUnit .E7 K (e7Node 6) c, xUnit_mem_adjointGroup _ c⟩

theorem xSix_mem_e7RootSix (K : Type) [Field K] (c : K) : xSix K c ∈ e7RootSix K := by
  rw [← range_rhoSix]
  exact ⟨uSL c, Subtype.ext (simpleRootSL2_uSL _ c)⟩

theorem rootDiagAut_mem_e7RootSix {K : Type} [Field K] (b : Fin (Tag.rank .E7) → Kˣ)
    {s : adjointGroup .E7 K} (hs : s ∈ e7RootSix K) : rootDiagAut .E7 K b s ∈ e7RootSix K := by
  rw [← range_rhoSix] at hs ⊢
  obtain ⟨A, rfl⟩ := hs
  have hR : (rhoSix K).range.map (adjointGroup .E7 K).subtype =
      Subgroup.closure (Set.range (xUnit .E7 K (e7Node 6)) ∪
        Set.range (yUnit .E7 K (e7Node 6))) := by
    rw [← range_simpleRootSL2]
    ext y
    constructor
    · rintro ⟨_, ⟨B, rfl⟩, rfl⟩
      exact ⟨B, rfl⟩
    · rintro ⟨B, rfl⟩
      exact ⟨rhoSix K B, ⟨B, rfl⟩, rfl⟩
  have hconj : Subgroup.closure (Set.range (xUnit .E7 K (e7Node 6)) ∪
      Set.range (yUnit .E7 K (e7Node 6))) ≤ (Subgroup.closure
        (Set.range (xUnit .E7 K (e7Node 6)) ∪ Set.range (yUnit .E7 K (e7Node 6)))).comap
          (MulAut.conj (rootDiagUnit .E7 b)).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation .E7 K b).1]
      exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation .E7 K b).2.1]
      exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  have hA : (rhoSix K A : ModGL .E7 K) ∈ Subgroup.closure (Set.range (xUnit .E7 K (e7Node 6)) ∪
      Set.range (yUnit .E7 K (e7Node 6))) := by
    rw [← hR]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  have h1 := hconj hA
  rw [← hR] at h1
  obtain ⟨y, hy, hyeq⟩ := h1
  rwa [show rootDiagAut .E7 K b (rhoSix K A) = y from
    Subtype.ext ((coe_rootDiagAut b (rhoSix K A)).trans hyeq.symm)]

theorem rootDiagAut_mem_e7RootSix_iff {K : Type} [Field K] (b : Fin (Tag.rank .E7) → Kˣ)
    (s : adjointGroup .E7 K) : rootDiagAut .E7 K b s ∈ e7RootSix K ↔ s ∈ e7RootSix K := by
  refine ⟨fun h => ?_, rootDiagAut_mem_e7RootSix b⟩
  have h' := rootDiagAut_mem_e7RootSix b⁻¹ h
  have e : rootDiagAut .E7 K b⁻¹ (rootDiagAut .E7 K b s) = s := by
    have h1 : rootDiagAut .E7 K b⁻¹ * rootDiagAut .E7 K b = 1 := by
      change rootDiagAutHom .E7 K b⁻¹ * rootDiagAutHom .E7 K b = 1
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [← MulAut.mul_apply, h1, MulAut.one_apply]
  rwa [e] at h'

theorem rootDiagAut_xSix_ne {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    rootDiagAut .E7 K (bitsTuple e7BitsSix) (xSix K 1) ≠ xSix K 1 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_rootDiagAut, (root_diagonal_conjugation .E7 K (bitsTuple e7BitsSix)).1] at h'
  have hb : (bitsTuple (K := K) e7BitsSix (e7Node 6) : K) = -1 := by
    simp [bitsTuple, show e7BitsSix (e7Node 6) = true from by decide]
  rw [hb, neg_one_mul] at h'
  have h2 : rhoSix K (uSL (-1)) = rhoSix K (uSL 1) :=
    Subtype.ext ((simpleRootSL2_uSL _ _).trans (h'.trans (simpleRootSL2_uSL _ _).symm))
  have h3 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 1)
    (rhoSix_injective hK2 h2)
  simp [uSL] at h3
  exact Ring.neg_one_ne_one_of_char_ne_two hK2 h3

theorem e7LeviE6_sup_e7RootSix (K : Type) [Field K] : e7LeviE6 K ⊔ e7RootSix K = ⊤ := by
  have hgen : ∀ (i : Fin (Tag.rank .E7)) (x : adjointGroup .E7 K),
      x ∈ rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup i →
        x ∈ e7LeviE6 K ⊔ e7RootSix K := by
    intro i x hx
    by_cases h6 : i = e7Node 6
    · subst h6
      exact le_sup_right (α := Subgroup (adjointGroup .E7 K)) hx
    · obtain ⟨k, rfl⟩ : ∃ k, e7LeviE6Node k = i := by
        by_contra hne
        push Not at hne
        exact h6 (eq_six_of_forall_e7LeviE6Node_ne i hne)
      exact le_sup_left (α := Subgroup (adjointGroup .E7 K)) (le_iSup (fun k =>
        rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7LeviE6Node k)) k hx)
  have hrk : ∀ (i : Fin (Tag.rank .E7)) (g : ModGL .E7 K) (hg : g ∈ adjointGroup .E7 K),
      g ∈ Subgroup.closure (Set.range (xUnit .E7 K i) ∪ Set.range (yUnit .E7 K i)) →
        (⟨g, hg⟩ : adjointGroup .E7 K) ∈
          rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup i := by
    intro i g hg hgc
    change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single i 1)
    rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf,
      ← closure_xUnit_yUnit_eq_rootSubgroup_sup]
    exact hgc
  have hle : adjointGroup .E7 K ≤ (e7LeviE6 K ⊔ e7RootSix K).map (adjointGroup .E7 K).subtype := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro g ⟨i, c, h | h⟩
    · have hg : g = xUnit .E7 K i c := Units.ext (h.trans (coe_xUnit i c).symm)
      subst hg
      exact ⟨_, hgen i _ (hrk i _ (xUnit_mem_adjointGroup i c)
        (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))), rfl⟩
    · have hg : g = yUnit .E7 K i c := Units.ext (h.trans (coe_yUnit i c).symm)
      subst hg
      exact ⟨_, hgen i _ (hrk i _ (yUnit_mem_adjointGroup i c)
        (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩))), rfl⟩
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨y, hy, hyx⟩ := hle hx
  rwa [show (⟨x, hx⟩ : adjointGroup .E7 K) = y from Subtype.ext hyx.symm]

theorem mem_inner_of_odd_fix_e7LeviE6 {K : Type} [Field K] [Finite K]
    {β : MulAut (adjointGroup .E7 K)} (hβ : Odd (orderOf β)) (hfix : ∀ x ∈ e7LeviE6 K, β x = x) :
    β ∈ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range := by
  have hU : ∀ B : SL2 K, 1 * simpleRootSL2 .E7 K (e7Node 0) (conjGL 1
      (Matrix.SpecialLinearGroup.map (algebraMap K K) B)) * 1⁻¹ ∈
        (adjointGroup .E7 K).map (baseChangeGL (algebraMap K K)) := by
    intro B
    refine ⟨simpleRootSL2 .E7 K (e7Node 0) B, simpleRootSL2_mem_adjointGroup _ B, ?_⟩
    rw [baseChangeGL_simpleRootSL2, conjGL_one', one_mul, inv_one, mul_one]
  have hZ : ∀ η ∈ zpowers β, ∀ (u : adjointGroup .E7 K) (B : SL2 K),
      baseChangeGL (algebraMap K K) (u : ModGL .E7 K) = 1 * simpleRootSL2 .E7 K (e7Node 0)
        (conjGL 1 (Matrix.SpecialLinearGroup.map (algebraMap K K) B)) * 1⁻¹ → η u = u := by
    intro η hη u B hu
    rw [conjGL_one', one_mul, inv_one, mul_one, ← baseChangeGL_simpleRootSL2] at hu
    have hu' : (u : ModGL .E7 K) = simpleRootSL2 .E7 K (e7Node 0) B :=
      baseChangeGL_injective (algebraMap K K) hu
    have huQ : u ∈ e7LeviE6 K := by
      refine le_iSup (fun k => rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup
        (e7LeviE6Node k)) 0 ?_
      change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single (e7Node 0) 1)
      rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf, hu',
        ← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
      exact ⟨B, rfl⟩
    have hβu : β ∈ MulAction.stabilizer (MulAut (adjointGroup .E7 K)) u := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hfix u huQ
    have h := (zpowers_le.2 hβu) hη
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h
  obtain ⟨-, -, hE7, -⟩ :=
    RankThree.PartOne.KE.ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free .E7
      (Or.inr (Or.inl rfl)) K K (e7Node 0) 1 1 hU (zpowers β) hZ
  have hcard := hE7 rfl
  rw [MonoidHom.map_zpowers, Nat.card_zpowers] at hcard
  have hodd : Odd (orderOf (QuotientGroup.mk' (inner (adjointGroup .E7 K)) β)) :=
    Odd.of_dvd_nat hβ (orderOf_map_dvd _ β)
  have h1 : orderOf (QuotientGroup.mk' (inner (adjointGroup .E7 K)) β) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hcard with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem burgTorusFor_E7_t7 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K) :
    BurgTorusFor (rootDiagAut .E7 K (bitsTuple e7BitsSix)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (one_le_and_three_le_of_card hp hp2 hK).1 hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hZ : center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot_field .E7 K
  obtain ⟨p', n', hp', hp'2, hn', ⟨eGF⟩⟩ := PSL.exists_sl_galoisField (K := K) hK2
  set z := torusEltC K (e7Node 6) (-1) with hz
  refine ⟨e7LeviE6 K, isQuasisimple_e7LeviE6 hp hp2 hK, e7LeviE6_le_fixedSubgroup hK2,
    fixedSubgroup_le_normalizer_e7LeviE6 hK2, z, e7RootSix K, orderOf_torusEltC_six hK2,
    isQuasisimple_e7RootSix hK2 h5, e7RootSix_le_centralizer hK2,
    centralizer_le_normalizer_e7RootSix hK2,
    ⟨p', n', hp', hp'2, hn', ⟨(e7RootSixEquiv hK2).trans eGF⟩⟩, center_e7RootSix hK2,
    rootDiagAut_mem_e7RootSix_iff _, ⟨xSix K 1, xSix_mem_e7RootSix K 1, rootDiagAut_xSix_ne hK2⟩,
    fun β hβ _ hfix => ?_⟩
  obtain ⟨g, rfl⟩ := mem_inner_of_odd_fix_e7LeviE6 hβ hfix
  have hgQ : ∀ x ∈ e7LeviE6 K, g * x = x * g := by
    intro x hx
    have h := hfix x hx
    rw [MulAut.conj_apply] at h
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]
  have hgz : g ∈ centralizer ({z} : Set (adjointGroup .E7 K)) :=
    mem_centralizer_singleton_iff.2 (hgQ z (torusEltC_six_mem_e7LeviE6 K))
  have hgN := centralizer_le_normalizer_e7RootSix hK2 hgz
  refine ⟨fun s => ?_, fun hSfix => ?_⟩
  · rw [MulAut.conj_apply]
    exact (mem_normalizer_iff.1 hgN s).symm
  · have hgS : ∀ x ∈ e7RootSix K, g * x = x * g := by
      intro x hx
      have h := hSfix x hx
      rw [MulAut.conj_apply] at h
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h]
    have hgC : g ∈ center (adjointGroup .E7 K) := by
      rw [mem_center_iff]
      intro x
      have hx : x ∈ e7LeviE6 K ⊔ e7RootSix K := by rw [e7LeviE6_sup_e7RootSix]; exact mem_top x
      have hcen : e7LeviE6 K ⊔ e7RootSix K ≤ centralizer ({g} : Set (adjointGroup .E7 K)) :=
        sup_le (fun x hx => mem_centralizer_singleton_iff.2 (hgQ x hx).symm)
          (fun x hx => mem_centralizer_singleton_iff.2 (hgS x hx).symm)
      exact mem_centralizer_singleton_iff.1 (hcen hx)
    rw [hZ, mem_bot] at hgC
    rw [hgC, map_one]

end CFSG.ComponentClassification.Burgoyne.E2
