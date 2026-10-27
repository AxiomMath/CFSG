module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Glue
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Row
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1ToralData

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.Adjoint
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit root_diagonal_conjugation)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.HighestRoot (rankOneGroup rankOneGroup_adjDatum)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.Chevalley (conjGL baseChangeGL_simpleRootSL2)
open scoped MatrixGroups

theorem burgCoreFor_of_inner {T : Type} [Group T] [Finite T] (hZ : center T = ⊥)
    {α : MulAut T} (h1 : pPrimeCore 2 (fixedSubgroup α) = ⊥)
    (h2 : ∀ β : MulAut T, Odd (orderOf β) → α * β = β * α →
      (∀ x ∈ fixedSubgroup α, β x = x) → β ∈ (MulAut.conj : T →* MulAut T).range) :
    BurgCoreFor α := by
  have hinj := conj_injective hZ
  refine ⟨h1, fun β hβ hαβ hfix => ?_⟩
  obtain ⟨g, rfl⟩ := h2 β hβ hαβ hfix
  have hgα : α g = g := by
    apply hinj
    rw [← mul_conj_mul_inv, hαβ, mul_inv_cancel_right]
  let g' : fixedSubgroup α := ⟨g, hgα⟩
  have hg'Z : g' ∈ center (fixedSubgroup α) := by
    rw [mem_center_iff]
    intro x
    have h3 := hfix x x.2
    simp only [MulAut.conj_apply] at h3
    refine Subtype.ext ?_
    change (x : T) * g = g * x
    calc (x : T) * g = g * x * g⁻¹ * g := by rw [h3]
      _ = g * x := by group
  have hnorm : (zpowers g').Normal := ⟨fun y hy k => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
    rw [mem_center_iff.1 (zpow_mem hg'Z n) k, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers g') n⟩
  have hodd : Nat.Coprime 2 (Nat.card (zpowers g')) := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, show ((g' : T)) = g from rfl,
      ← orderOf_injective _ hinj g]
    exact Nat.coprime_two_left.2 hβ
  have hbot := (pPrimeCore_eq_bot_iff.1 h1) _ hnorm hodd
  have hg1 : g' = 1 := by
    have h3 : g' ∈ zpowers g' := mem_zpowers g'
    rw [hbot, mem_bot] at h3
    exact h3
  have hg : g = 1 := congrArg Subtype.val hg1
  rw [hg, map_one]

@[expose] def e7BitsOne : Fin (Tag.rank .E7) → Bool :=
  listMask [true, false, false, false, false, false, false]

@[expose] def e7BitsTwo : Fin (Tag.rank .E7) → Bool :=
  listMask [false, true, false, false, false, false, false]

@[expose] def e7BurgData1 : Fin (Tag.rank .E7) → List ((Fin (Tag.rank .E7) → ℤ) × ℤ) :=
  ![[(![2, 2, 3, 4, 3, 2, 1], 1), (![0, 1, 0, 0, 0, 0, 0], -2), (![0, 0, 1, 0, 0, 0, 0], -3),
      (![0, 0, 0, 1, 0, 0, 0], -4), (![0, 0, 0, 0, 1, 0, 0], -3),
      (![0, 0, 0, 0, 0, 1, 0], -2), (![0, 0, 0, 0, 0, 0, 1], -1)],
    [(![0, 1, 0, 0, 0, 0, 0], 2)],
    [(![0, 0, 1, 0, 0, 0, 0], 2)],
    [(![0, 0, 0, 1, 0, 0, 0], 2)],
    [(![0, 0, 0, 0, 1, 0, 0], 2)],
    [(![0, 0, 0, 0, 0, 1, 0], 2)],
    [(![0, 0, 0, 0, 0, 0, 1], 2)]]

theorem e7BurgData1_check :
    (∀ j, ∀ x ∈ e7BurgData1 j ++ e7BurgData1 j, x.1 ∈ rootFinset .E7 ∧
      maskChar (listMask (τ := .E7) [true, false, false, false, false, false, false])
        (Multiplicative.ofAdd x.1) = 1) ∧
    (∀ j, ((e7BurgData1 j).map fun x => x.2 • x.1).sum = (2 : ℤ) • Pi.single j 1) ∧
    (∀ i j, 2 * Tag.E7.cartan i j =
      ((e7BurgData1 i).map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum) := by
  decide +kernel

@[expose] def e7BurgData2 : Fin (Tag.rank .E7) → List ((Fin (Tag.rank .E7) → ℤ) × ℤ) :=
  ![[(![1, 0, 0, 0, 0, 0, 0], 2)],
    [(![2, 2, 3, 4, 3, 2, 1], 1), (![1, 0, 0, 0, 0, 0, 0], -2), (![0, 0, 1, 0, 0, 0, 0], -3),
      (![0, 0, 0, 1, 0, 0, 0], -4), (![0, 0, 0, 0, 1, 0, 0], -3),
      (![0, 0, 0, 0, 0, 1, 0], -2), (![0, 0, 0, 0, 0, 0, 1], -1)],
    [(![0, 0, 1, 0, 0, 0, 0], 2)],
    [(![0, 0, 0, 1, 0, 0, 0], 2)],
    [(![0, 0, 0, 0, 1, 0, 0], 2)],
    [(![0, 0, 0, 0, 0, 1, 0], 2)],
    [(![0, 0, 0, 0, 0, 0, 1], 2)]]

theorem e7BurgData2_check :
    (∀ j, ∀ x ∈ e7BurgData2 j ++ e7BurgData2 j, x.1 ∈ rootFinset .E7 ∧
      maskChar (listMask (τ := .E7) [false, true, false, false, false, false, false])
        (Multiplicative.ofAdd x.1) = 1) ∧
    (∀ j, ((e7BurgData2 j).map fun x => x.2 • x.1).sum = (2 : ℤ) • Pi.single j 1) ∧
    (∀ i j, 2 * Tag.E7.cartan i j =
      ((e7BurgData2 i).map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum) := by
  decide +kernel


theorem mem_inner_of_odd_fix_rankOne {K : Type} [Field K] [Finite K] (k : Fin (Tag.rank .E7))
    {β : MulAut (adjointGroup .E7 K)} (hβ : Odd (orderOf β))
    (hfix : ∀ x ∈ rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup k, β x = x) :
    β ∈ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range := by
  have hU : ∀ B : SL2 K, 1 * simpleRootSL2 .E7 K k (conjGL 1
      (Matrix.SpecialLinearGroup.map (algebraMap K K) B)) * 1⁻¹ ∈
        (adjointGroup .E7 K).map (baseChangeGL (algebraMap K K)) := by
    intro B
    refine ⟨simpleRootSL2 .E7 K k B, simpleRootSL2_mem_adjointGroup _ B, ?_⟩
    rw [baseChangeGL_simpleRootSL2, conjGL_one', one_mul, inv_one, mul_one]
  have hZ : ∀ η ∈ zpowers β, ∀ (u : adjointGroup .E7 K) (B : SL2 K),
      baseChangeGL (algebraMap K K) (u : ModGL .E7 K) = 1 * simpleRootSL2 .E7 K k
        (conjGL 1 (Matrix.SpecialLinearGroup.map (algebraMap K K) B)) * 1⁻¹ → η u = u := by
    intro η hη u B hu
    rw [conjGL_one', one_mul, inv_one, mul_one, ← baseChangeGL_simpleRootSL2] at hu
    have hu' : (u : ModGL .E7 K) = simpleRootSL2 .E7 K k B :=
      baseChangeGL_injective (algebraMap K K) hu
    have huL : u ∈ rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup k := by
      change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single k 1)
      rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf, hu',
        ← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
      exact ⟨B, rfl⟩
    have hβu : β ∈ MulAction.stabilizer (MulAut (adjointGroup .E7 K)) u := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hfix u huL
    have h := (zpowers_le.2 hβu) hη
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h
  obtain ⟨-, -, hE7, -⟩ :=
    RankThree.PartOne.KE.ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free .E7
      (Or.inr (Or.inl rfl)) K K k 1 1 hU (zpowers β) hZ
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

theorem rankOne_le_fixedSubgroup_rootDiagAut {K : Type} [Field K] {a : Fin (Tag.rank .E7) → Kˣ}
    {k : Fin (Tag.rank .E7)} (hk : a k = 1) :
    rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup k ≤
      fixedSubgroup (rootDiagAut .E7 K a) := by
  intro x hx
  change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single k 1) at hx
  rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf,
    ← closure_xUnit_yUnit_eq_rootSubgroup_sup] at hx
  have hle : Subgroup.closure (Set.range (xUnit .E7 K k) ∪ Set.range (yUnit .E7 K k)) ≤
      Subgroup.centralizer ({rootDiagUnit .E7 a} : Set (ModGL .E7 K)) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      have h := (root_diagonal_conjugation .E7 K a).1 k c
      rw [hk, Units.val_one, one_mul] at h
      calc xUnit .E7 K k c * rootDiagUnit .E7 a =
          rootDiagUnit .E7 a * xUnit .E7 K k c * (rootDiagUnit .E7 a)⁻¹ * rootDiagUnit .E7 a := by
            rw [h]
        _ = rootDiagUnit .E7 a * xUnit .E7 K k c := by group
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      have h := (root_diagonal_conjugation .E7 K a).2.1 k c
      rw [hk, inv_one, Units.val_one, one_mul] at h
      calc yUnit .E7 K k c * rootDiagUnit .E7 a =
          rootDiagUnit .E7 a * yUnit .E7 K k c * (rootDiagUnit .E7 a)⁻¹ * rootDiagUnit .E7 a := by
            rw [h]
        _ = rootDiagUnit .E7 a * yUnit .E7 K k c := by group
  have hx' := mem_centralizer_singleton_iff.1 (hle hx)
  change rootDiagAut .E7 K a x = x
  apply Subtype.ext
  rw [coe_rootDiagAut, ← hx']
  group

theorem pPrimeCore_fixedSubgroup_rootDiagAut {τ : Tag} {K : Type} [Field K]
    {a : Fin τ.rank → Kˣ} (h : pPrimeCore 2 (toralCentralizer τ K a) = ⊥) :
    pPrimeCore 2 (fixedSubgroup (rootDiagAut τ K a)) = ⊥ := by
  have hmap : (fixedSubgroup (rootDiagAut τ K a)).map (adjointGroup τ K).subtype =
      toralCentralizer τ K a := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_fixedSubgroup_rootDiagAut.1 hx
    · intro hy
      have hyC : y ∈ adjointGroup τ K := (mem_inf.1 hy).1
      exact ⟨⟨y, hyC⟩, mem_fixedSubgroup_rootDiagAut.2 hy, rfl⟩
  let e : fixedSubgroup (rootDiagAut τ K a) ≃* toralCentralizer τ K a :=
    ((fixedSubgroup (rootDiagAut τ K a)).equivMapOfInjective _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have h1 := pPrimeCore_map_iso 2 e
  rw [h] at h1
  exact (map_eq_bot_iff_of_injective _ e.injective).1 h1

theorem burgCoreFor_rootDiagAut_E7 {K : Type} [Field K] [Finite K] {a : Fin (Tag.rank .E7) → Kˣ}
    (hcore : pPrimeCore 2 (toralCentralizer .E7 K a) = ⊥) {k : Fin (Tag.rank .E7)}
    (hk : a k = 1) : BurgCoreFor (rootDiagAut .E7 K a) :=
  burgCoreFor_of_inner (center_adjointGroup_eq_bot_field .E7 K)
    (pPrimeCore_fixedSubgroup_rootDiagAut hcore) fun _ hβ _ hfix =>
      mem_inner_of_odd_fix_rankOne k hβ fun x hx =>
        hfix x (rankOne_le_fixedSubgroup_rootDiagAut hk hx)

theorem burgCoreFor_E7_t1 {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) :
    BurgCoreFor (rootDiagAut .E7 K (bitsTuple e7BitsOne)) := by
  obtain ⟨hd, h1, h2⟩ := e7BurgData1_check
  exact burgCoreFor_rootDiagAut_E7
    (pPrimeCore_toralCentralizer_bits_eq_bot hK2 _ e7BurgData1 e7BurgData1 hd h1 h2)
    (k := e7Node 1) (by simp [bitsTuple, show e7BitsOne (e7Node 1) = false from by decide])

theorem burgCoreFor_E7_t4 {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) :
    BurgCoreFor (rootDiagAut .E7 K (bitsTuple e7BitsTwo)) := by
  obtain ⟨hd, h1, h2⟩ := e7BurgData2_check
  exact burgCoreFor_rootDiagAut_E7
    (pPrimeCore_toralCentralizer_bits_eq_bot hK2 _ e7BurgData2 e7BurgData2 hd h1 h2)
    (k := e7Node 0) (by simp [bitsTuple, show e7BitsTwo (e7Node 0) = false from by decide])

end CFSG.ComponentClassification.Burgoyne.E2
