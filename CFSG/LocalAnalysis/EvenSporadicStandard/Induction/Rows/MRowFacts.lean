module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MBShared
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RowGen2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RowGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.Monster.Existence CFSG.Monster.Existence.Compat
  CFSG.Open CFSG.EvenSporadicStandard.Induction

abbrev MIsK : GroupClass := IsKPinned .M (fun n => 2 * monsterBabyOrder ≤ n)

theorem isKPinned_of_mulEquiv {s : TauCeti.SporadicName} {P : ℕ → Prop} {X Y : Type} [Group X]
    [Group Y] (e : X ≃* Y) (h : IsKPinned s P X) : IsKPinned s P Y := by
  obtain ⟨u, K, hP, ⟨f⟩⟩ := h
  exact ⟨u, K, hP, ⟨e.symm.trans f⟩⟩

section KData

variable (mf : MonsterFacts (Carrier .M))

include mf in
theorem finite_carrier_m : Finite (Carrier .M) :=
  Nat.finite_of_card_ne_zero (by rw [mf.card]; unfold monsterOrder; norm_num)

include mf in
theorem mIsK_cent {X : Type} [Group X] (hX : MIsK X) :
    ∃ u : Carrier .M, orderOf u = 2 ∧ IsTwoACentralizer u ∧
      Nat.card ↥(centralizer ({u} : Set (Carrier .M))) = 2 * monsterBabyOrder ∧
        Nonempty (X ≃* ↥(centralizer ({u} : Set (Carrier .M)))) := by
  obtain ⟨u, K, ⟨-, hu2, -, hKu, hcard⟩, ⟨e⟩⟩ := hX
  have := finite_carrier_m mf
  have hKC : K ≤ centralizer ({u} : Set (Carrier .M)) := fun k hk =>
    mem_centralizer_singleton_iff.2 (hKu k hk)
  have hge : 2 * monsterBabyOrder ≤ Nat.card ↥(centralizer ({u} : Set (Carrier .M))) :=
    hcard.trans (Subgroup.card_le_of_le hKC)
  obtain ⟨hA, hC, -⟩ := mf.twoA u hu2 hge
  have hKeq : K = centralizer ({u} : Set (Carrier .M)) :=
    Subgroup.eq_of_le_of_card_ge hKC (by rw [hC]; exact hcard)
  exact ⟨u, hu2, hA, hC, ⟨e.trans (MulEquiv.subgroupCongr hKeq)⟩⟩

include mf in
theorem mIsK_data {X : Type} [Group X] (hX : MIsK X) :
    CFSG.IsQuasisimple X ∧ Nat.card (center X) = 2 ∧ Nat.card X = 2 * monsterBabyOrder ∧
      IsSporadic (X ⧸ center X) .B := by
  obtain ⟨u, hu2, hA, hC, ⟨e⟩⟩ := mIsK_cent mf hX
  obtain ⟨hp, hz, ⟨f⟩⟩ := hA
  have hq : CFSG.IsQuasisimple ↥(centralizer ({u} : Set (Carrier .M))) :=
    @isQuasisimple_of_perfect_simple_quotient ↥(centralizer ({u} : Set (Carrier .M)))
      NativeSporadic.B _ _ hp f mf.baby_simple
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, ?_, ?_, ?_⟩
  · rw [card_center_of_mulEquiv' e, ← Subgroup.card_map_of_injective
      (centralizer ({u} : Set (Carrier .M))).subtype_injective, hz, Nat.card_zpowers, hu2]
  · rw [Nat.card_congr e.toEquiv]
    exact hC
  · exact ⟨(quotientCenterEquiv' e).trans f⟩

theorem mIsK_card_cq (mf : MonsterFacts (Carrier .M)) {X : Type} [Group X] (hX : MIsK X) :
    Nat.card (X ⧸ center X) = monsterBabyOrder := by
  obtain ⟨-, hz, hc, -⟩ := mIsK_data mf hX
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
  rw [hz, hc] at h1
  omega

theorem mIsK_oddCore (mf : MonsterFacts (Carrier .M)) {X : Type} [Group X] (hX : MIsK X) :
    CFSG.oddCore X = ⊥ := by
  obtain ⟨hq, hz, hc, -⟩ := mIsK_data mf hX
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hc]; unfold monsterBabyOrder; norm_num)
  have : IsSimpleGroup (X ⧸ center X) := hq.2.1
  refine oddCore_eq_bot_of_card_center_two ?_ hz
  rw [mIsK_card_cq mf hX]
  unfold monsterBabyOrder
  decide

theorem mIsK_iso (mf : MonsterFacts (Carrier .M)) (mi : MonsterInvolutions (Carrier .M))
    {X Y : Type} [Group X] [Group Y] (hX : MIsK X) (hY : MIsK Y) : Nonempty (X ≃* Y) := by
  obtain ⟨u, hu2, -, hCu, ⟨eX⟩⟩ := mIsK_cent mf hX
  obtain ⟨v, hv2, -, hCv, ⟨eY⟩⟩ := mIsK_cent mf hY
  obtain ⟨φ⟩ := centEquivOfIsConj (mi.conj u v hu2 hv2 hCu.ge hCv.ge)
  exact ⟨eX.trans (φ.trans eY.symm)⟩

end KData

@[expose] def BInvCentNonsolvable : Prop :=
  ∀ (X : Type) [Group X], IsSporadic X .B → ∀ b : X, b ≠ 1 → b * b = 1 →
    ¬ Group.IsSolvable ↥(centralizer ({b} : Set X))

structure MHyp31Inputs : Prop where
  noCover : MonsterNoCover
  bRank : BCoverRank
  bInvCent : BInvCentNonsolvable
  evenB : EvenCoverOutHered [.M] .B

section Fields

theorem oddMultTrivial_m (h : MonsterNoCover) : OddMultTrivial .M :=
  fun L _ _ hq _ hsp => h L hq hsp

theorem mLink (mf : MonsterFacts (Carrier .M)) (hmult : OddMultTrivial .M) {G : Type} [Group G]
    [Finite G] {L K₁ T : Subgroup G} {s : G} (hcov : OddCover .M L)
    (hdata : Sol78Link5bData K₁ L T s) (hq : CFSG.IsQuasisimple ↥K₁)
    (hK : MIsK (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    ∃ l : G, l ∈ L ∧ orderOf l = 2 ∧ (∀ k ∈ K₁, k * l = l * k) ∧
      2 * monsterBabyOrder ≤ Nat.card ↥K₁ ∧ MonsterFacts ↥L ∧
        Nat.card ↥(centralizer ((K₁.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤ 2 := by
  have hLM : IsSporadic ↥L .M := hcov.isSporadic_of_mult hmult
  obtain ⟨e⟩ := hLM
  have hinL : AllInner ↥L := AllInner.of_mulEquiv e.symm mf.allInner
  have hMf : MonsterFacts ↥L := MonsterFacts.of_mulEquiv e mf hinL
  have hZL : center ↥L = ⊥ := hcov.center_eq_bot hmult
  have hKL : K₁ ≤ L := hdata.le_left
  have hne : K₁ ≠ L := by
    rintro rfl
    have h1 : Nat.card (↥K₁ ⧸ center ↥K₁) = monsterOrder :=
      card_isSporadic_m mf hcov.2.2
    have : Group.IsPerfect ↥K₁ := hq.1
    obtain ⟨e₃⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥K₁))
      (QuotientGroup.mk'_surjective _) (by
        rw [QuotientGroup.ker_mk']
        exact oddCore_le_center hq)
    rw [Nat.card_congr e₃.toEquiv, mIsK_card_cq mf hK] at h1
    unfold monsterBabyOrder monsterOrder at h1
    norm_num at h1
  obtain ⟨l, hlL, hl2, hlK⟩ := exists_involution_of_link hdata hq hne hinL hZL
  have hcard : 2 * monsterBabyOrder ≤ Nat.card ↥K₁ := by
    have hle : Nat.card (↥K₁ ⧸ CFSG.oddCore ↥K₁) ≤ Nat.card ↥K₁ :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    rw [(mIsK_data mf hK).2.2.1] at hle
    exact hle
  obtain ⟨hKeq, hKeq', hA, -, -⟩ := m_pair_data hMf hlL hl2 hKL hlK hcard
  refine ⟨l, hlL, hl2, hlK, hcard, hMf, ?_⟩
  let u' : ↥L := ⟨l, hlL⟩
  have hu'2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hl2
  have hZ : Nat.card ↥(center ↥(K₁.subgroupOf L)) = 2 := by
    rw [hKeq', ← Subgroup.card_map_of_injective (centralizer ({u'} : Set ↥L)).subtype_injective,
      hA.2.1, Nat.card_zpowers, hu'2]
  have hzH : u' ∈ K₁.subgroupOf L := mem_subgroupOf.2 (by
    rw [hKeq]
    exact ⟨hlL, mem_centralizer_singleton_iff.2 rfl⟩)
  exact card_centralizer_le_of_center (subgroupOf_eq_centralizer hlL hKeq) hzH hZ.le

theorem stdRow_m (mf : MonsterFacts (Carrier .M)) (hmult : OddMultTrivial .M) (G : Type) [Group G]
    [Finite G] (L K₁ T : Subgroup G) (s : G) (hL : ∃ s' ∈ [TauCeti.SporadicName.M], OddCover s' L)
    (_ : T ≠ ⊥) (hdata : Sol78Link5bData K₁ L T s) (hq : CFSG.IsQuasisimple ↥K₁)
    (hK : MIsK (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2 := by
  obtain ⟨s', hs', hcov⟩ := hL
  rw [List.mem_singleton] at hs'
  subst hs'
  obtain ⟨l, hlL, hl2, hlK, hcard, hMf, -⟩ := mLink mf hmult hcov hdata hq hK
  obtain ⟨h1, h2⟩ := solomonLocalQ_of_monsterFacts hcov hMf hlL hl2 hdata.le_left hlK hcard
  exact ⟨h1.standard_in_L, h2.trans (by norm_num)⟩

theorem autC_m (mf : MonsterFacts (Carrier .M)) (hmult : OddMultTrivial .M) (G : Type) [Group G]
    [Finite G] (L K₁ N₀ T : Subgroup G) (s : G)
    (hL : ∃ s' ∈ [TauCeti.SporadicName.M], OddCover s' L) (_ : T ≠ ⊥)
    (hdata : Sol78Link5bData K₁ L T s) (hq : CFSG.IsQuasisimple ↥K₁)
    (hK : MIsK (↥K₁ ⧸ CFSG.oddCore ↥K₁)) (hcan : CanLoc K₁ N₀) :
    Group.IsSolvable ↥(autCentralizer L N₀) ∧ twoAdic (autCentralizer L N₀) ≤ 1 ∧
      ElemBound 2 ↥(autCentralizer L N₀) ∧
        (True → ∀ α ∈ autCentralizer L N₀, ∃ g : ↥L, α = MulAut.conj g) := by
  obtain ⟨s', hs', hcov⟩ := hL
  rw [List.mem_singleton] at hs'
  subst hs'
  obtain ⟨l, hlL, hl2, hlK, hcard, hMf, hcent⟩ := mLink mf hmult hcov hdata hq hK
  have hN₀ : N₀ = K₁ :=
    canLoc_eq_of_even hcan (even_card_center_of_quot hq (mIsK_data mf hK).2.1)
  subst hN₀
  have hinn : ∀ α : MulAut ↥L, ∃ c : ↥L, ∀ x, α x = c * x * c⁻¹ := fun α => by
    obtain ⟨g, hg⟩ := hMf.allInner α
    exact ⟨g, fun x => by rw [hg]; rfl⟩
  have hcardA : Nat.card ↥(autCentralizer L N₀) ≤ 2 :=
    (Subgroup.card_le_of_le (autCentralizer_le_map_centralizer (K := N₀) hinn)).trans
      ((Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)).trans hcent)
  exact ⟨isSolvable_autCentralizer_of_card_le (hcardA.trans (by norm_num)),
    twoAdic_le_one_of_card_le_two _ hcardA, elemBound_of_card_le hcardA,
    fun _ α _ => hMf.allInner α⟩

theorem fixNonsolvable_m (mf : MonsterFacts (Carrier .M)) (hB : BInvCentNonsolvable)
    (K₂ : Type) [Group K₂] [Finite K₂] (hperf : Group.IsPerfect K₂)
    (hcq : IsSporadic (K₂ ⧸ center K₂) .B) (α : MulAut K₂) (h1 : α ≠ 1) (h2 : α * α = 1) :
    ¬ Group.IsSolvable ↥(fixSubgroup α) := by
  obtain ⟨ε⟩ := hcq
  have hinB : AllInner (K₂ ⧸ center K₂) := AllInner.of_mulEquiv ε.symm mf.baby_allInner
  obtain ⟨c, hc⟩ := exists_inner_of_perfect_of_quotient_inner (fun β => by
    obtain ⟨g, hg⟩ := hinB β
    exact ⟨g, fun y => by rw [hg]; rfl⟩) α
  have hfix : fixSubgroup α = centralizer ({c} : Set K₂) := by
    ext x
    rw [mem_centralizer_singleton_iff]
    show α x = x ↔ x * c = c * x
    rw [hc x]
    constructor
    · intro h
      calc x * c = (c * x * c⁻¹) * c := by rw [h]
        _ = c * x := by group
    · intro h
      calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [h]
        _ = x := by group
  have hαc : α = MulAut.conj c := MulEquiv.ext fun x => by rw [hc x]; rfl
  let π : K₂ →* K₂ ⧸ center K₂ := QuotientGroup.mk' (center K₂)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ center K₂ := le_of_eq (QuotientGroup.ker_mk' _)
  have hc1 : π c ≠ 1 := by
    intro h
    have hcc : c ∈ center K₂ := (QuotientGroup.eq_one_iff c).1 h
    apply h1
    rw [hαc]
    ext x
    show c * x * c⁻¹ = x
    rw [← mem_center_iff.1 hcc x]
    group
  have hc2 : π c * π c = 1 := by
    have hcc : c * c ∈ center K₂ := by
      rw [mem_center_iff]
      intro g
      have := congrArg (fun β : MulAut K₂ => β g) h2
      simp only [MulAut.mul_apply, hαc, MulAut.conj_apply, MulAut.one_apply] at this
      calc g * (c * c) = (c * (c * g * c⁻¹) * c⁻¹) * (c * c) := by rw [this]
        _ = (c * c) * g := by group
    have : π (c * c) = 1 := (QuotientGroup.eq_one_iff _).2 hcc
    rw [← map_mul, this]
  intro hsol
  rw [hfix] at hsol
  exact hB (K₂ ⧸ center K₂) ⟨ε⟩ (π c) hc1 hc2 (isSolvable_centralizer_of_cover π hπ hker c hsol)

theorem sec_m (mf : MonsterFacts (Carrier .M)) (G : Type) [Group G] [Finite G]
    (K₁ N₀ : Subgroup G) (hq : CFSG.IsQuasisimple ↥K₁) (hK : MIsK (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) :
    ¬ (Group.IsSolvable ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ∧
      (True → TwoSubgroupsAbelian
        ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))))) := by
  rintro ⟨hs, -⟩
  have hN₀ : N₀ = K₁ :=
    canLoc_eq_of_even hcan (even_card_center_of_quot hq (mIsK_data mf hK).2.1)
  subst hN₀
  rw [Subgroup.subgroupOf_self, Subgroup.map_top,
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hs
  exact not_isSolvable_cq_of_isQuasisimple hq
    (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := ↥N₀ ⧸ center ↥N₀)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := ↥N₀ ⧸ center ↥N₀)).symm.injective)

theorem fourA_m (mf : MonsterFacts (Carrier .M)) (hmult : OddMultTrivial .M)
    (hB : BInvCentNonsolvable) : FourAFacts MIsK [.M] :=
  fourAFacts_of_lamProfile True 1 2 (by norm_num)
    (fun G _ _ L K₁ N₀ T s hL hT hdata hq hK hcan =>
      autC_m mf hmult G L K₁ N₀ T s hL hT hdata hq hK hcan)
    (fun K₂ _ _ hperf ⟨X, _, hX, ⟨e⟩⟩ α h1 h2 => by
      obtain ⟨f⟩ := (mIsK_data mf hX).2.2.2
      exact not_lamProfile_of_not_fix True (2 * 2) (fun β hβ1 hβ2 hL =>
        fixNonsolvable_m mf hB K₂ hperf ⟨e.trans f⟩ β hβ1 hβ2 hL.1) α h1 h2)
    (fun G _ _ K₁ N₀ hq hK hcan => sec_m mf G K₁ N₀ hq hK hcan)

theorem reachRow_m (F : TwoAFacts) (mf : MonsterFacts (Carrier .M))
    (mi : MonsterInvolutions (Carrier .M)) (inp : MHyp31Inputs) :
    ReachRow MIsK [.M] [] [.B] (fun X _ => IsSporadic X .B ∨ IsSporadic X .M) where
  iso := fun X Y _ _ e h => by
    rcases h with h | h
    · obtain ⟨f⟩ := h
      exact Or.inl ⟨e.symm.trans f⟩
    · obtain ⟨f⟩ := h
      exact Or.inr ⟨e.symm.trans f⟩
  fi23 := fun s hs => by
    rw [List.append_nil, List.mem_singleton] at hs
    subst hs
    exact fi23Excl_m F mf
  fi23_lo := fun s hs => by
    rw [List.mem_singleton] at hs
    subst hs
    exact fi23Excl_b F
  K_reach := fun X _ hX => Or.inl (mIsK_data mf hX).2.2.2
  K_quot := fun X _ hX =>
    isKPinned_of_mulEquiv (quotientOddCoreEquiv (mIsK_oddCore mf hX)).symm hX
  K_not_sporadic := fun X _ hX s hs h => by
    rw [List.append_nil, List.mem_singleton] at hs
    subst hs
    have h1 := card_isSporadic_m mf h
    rw [mIsK_card_cq mf hX] at h1
    unfold monsterBabyOrder monsterOrder at h1
    norm_num at h1
  K_odd_lo := fun X _ hX hodd s _ _ => by
    rw [(mIsK_data mf hX).2.1] at hodd
    exact absurd hodd (by decide)
  lo := Or.inl fun s hs X Y _ _ hX hY => by
    rw [List.mem_singleton] at hs
    subst hs
    obtain ⟨f⟩ := hX
    obtain ⟨g⟩ := (mIsK_data mf hY).2.2.2
    exact ⟨f.trans g.symm⟩
  K_iso := fun X Y _ _ hX hY _ _ => mIsK_iso mf mi hX hY
  K_cq := fun X Y _ _ hX hY => by
    obtain ⟨f⟩ := (mIsK_data mf hX).2.2.2
    obtain ⟨g⟩ := (mIsK_data mf hY).2.2.2
    exact ⟨f.trans g.symm⟩
  not_exc := fun X _ h => by
    rcases h with h | h
    · exact sporadicNotExc_b F X h
    · exact sporadicNotExc_m mf X h
  sp_not_exc := fun s hs => by
    rw [List.append_nil, List.mem_singleton] at hs
    subst hs
    exact sporadicNotExc_m mf
  rank := fun X _ _ hq hR hodd => by
    rcases hR with hB | hM
    · exact inp.bRank X hq hB
    · exfalso
      have hZ : center X = ⊥ := inp.noCover X hq hM
      exact hodd (by rw [hZ, Subgroup.card_bot]; exact odd_one) ⟨.M, by simp, hM⟩
  up_reach := fun s hs => absurd hs List.not_mem_nil
  closure := fun Y _ _ hY N' hN hidx hkp P hsol hq hR hnS hlow _ _ => by
    have hPB : IsSporadic (↥P ⧸ center ↥P) .B := by
      rcases hR with h | h
      · exact h
      · exact absurd ⟨.M, by simp, h⟩ hnS
    have heven : ¬ Odd (Nat.card ↥(center ↥P)) := fun hodd => hlow hodd ⟨.B, by simp, hPB⟩
    obtain ⟨s'', hs'', hN'⟩ := inp.evenB Y hY N' hN hidx hkp P hsol hq hPB heven
    rw [List.mem_singleton] at hs''
    subst hs''
    exact Or.inr hN'
  notR := fun Y _ _ N hN hidx hkp ⟨L, hL, s, hs, hcov⟩ hR => by
    rw [List.mem_singleton] at hs
    subst hs
    have hLM : IsSporadic ↥L .M := hcov.isSporadic_of_mult (oddMultTrivial_m inp.noCover)
    have hcardL : Nat.card ↥L = monsterOrder := card_isSporadic_m mf hLM
    obtain ⟨T, hT, hTp, hLT⟩ := hL
    have hle : Nat.card ↥L ≤ Nat.card Y := Subgroup.card_le_card_group L
    rcases hR with hR | hR
    ·
      obtain ⟨e⟩ := hR
      have hNtop : N = ⊤ := eq_top_of_allInner hN (AllInner.of_mulEquiv e.symm mf.baby_allInner)
      have hcardY : Nat.card Y = monsterBabyOrder := by
        have : Nat.card ↥N = Nat.card Y := by rw [hNtop]; exact Subgroup.card_top
        rw [← this]
        exact card_isSporadic_b F ⟨e⟩
      rw [hcardL, hcardY] at hle
      unfold monsterOrder monsterBabyOrder at hle
      norm_num at hle
    ·
      obtain ⟨e⟩ := hR
      have hNtop : N = ⊤ := eq_top_of_allInner hN (AllInner.of_mulEquiv e.symm mf.allInner)
      have hcardY : Nat.card Y = monsterOrder := by
        have : Nat.card ↥N = Nat.card Y := by rw [hNtop]; exact Subgroup.card_top
        rw [← this]
        exact card_isSporadic_m mf ⟨e⟩
      have hLtop : L = ⊤ := Subgroup.eq_top_of_card_eq L (by rw [hcardL, hcardY])
      have hcen : center Y = ⊥ := center_eq_bot_of_fStarSimple hN
      apply hT
      rw [eq_bot_iff]
      intro t ht
      have hz : t ∈ center Y := Subgroup.mem_center_iff.2 fun g =>
        (mem_centralizer_iff.1 (hLT.1 (hLtop ▸ mem_top g)) t ht).symm
      rw [hcen] at hz
      exact hz
  pair_into := fun Y _ _ _ N' hN hidx hkp P hsol hq hR hnS hlow _ ⟨s, hs, hN'M⟩ => by
    rw [List.mem_singleton] at hs
    subst hs
    have hPB : IsSporadic (↥P ⧸ center ↥P) .B := by
      rcases hR with h | h
      · exact h
      · exact absurd ⟨.M, by simp, h⟩ hnS
    have heven : ¬ Odd (Nat.card ↥(center ↥P)) := fun hodd => hlow hodd ⟨.B, by simp, hPB⟩
    obtain ⟨e⟩ := hN'M
    have hNtop : N' = ⊤ := eq_top_of_allInner hN (AllInner.of_mulEquiv e.symm mf.allInner)
    let eY : Y ≃* Carrier .M :=
      ((MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv).symm.trans e
    obtain ⟨-, t, ht2, hc⟩ := hsol
    have hPC : P ≤ centralizer ({t} : Set Y) := hc.1
    have hfinM := finite_carrier_m mf
    have ht2' : orderOf (eY t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
    have hP'C : P.map eY.toMonoidHom ≤ centralizer ({eY t} : Set (Carrier .M)) := by
      rw [← map_centralizer_equiv eY t]
      exact Subgroup.map_mono hPC
    have hcardP' : Nat.card ↥(P.map eY.toMonoidHom) = Nat.card ↥P :=
      Subgroup.card_map_of_injective eY.injective
    have hcardP : Nat.card ↥P = monsterBabyOrder * Nat.card (center ↥P) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥P)
      rwa [card_isSporadic_b F hPB] at h1
    have hZpos : 0 < Nat.card (center ↥P) := Nat.card_pos
    have hZev : Even (Nat.card (center ↥P)) := Nat.not_odd_iff_even.1 heven
    have hZ2 : 2 ≤ Nat.card (center ↥P) := by
      obtain ⟨r, hr⟩ := hZev
      omega
    have hBpos : 0 < monsterBabyOrder := by unfold monsterBabyOrder; norm_num
    have hge : 2 * monsterBabyOrder ≤
        Nat.card ↥(centralizer ({eY t} : Set (Carrier .M))) := by
      have := Subgroup.card_le_of_le hP'C
      rw [hcardP', hcardP] at this
      nlinarith
    obtain ⟨-, hC, -⟩ := mf.twoA (eY t) ht2' hge
    have hle : Nat.card ↥P ≤ 2 * monsterBabyOrder := by
      have := Subgroup.card_le_of_le hP'C
      rw [hC, hcardP'] at this
      exact this
    have hZ2' : Nat.card (center ↥P) = 2 := by
      rw [hcardP] at hle
      nlinarith
    have hPeq : P.map eY.toMonoidHom = centralizer ({eY t} : Set (Carrier .M)) :=
      Subgroup.eq_of_le_of_card_ge hP'C (by rw [hC, hcardP', hcardP, hZ2']; omega)
    have : Finite ↥P := inferInstance
    have : IsSimpleGroup (↥P ⧸ center ↥P) := hq.2.1
    have hO : CFSG.oddCore ↥P = ⊥ := by
      refine oddCore_eq_bot_of_card_center_two ?_ hZ2'
      rw [card_isSporadic_b F hPB]
      unfold monsterBabyOrder
      decide
    refine ⟨eY t, P.map eY.toMonoidHom, ⟨mem_top _, ht2', le_top, fun k hk =>
      mem_centralizer_singleton_iff.1 (hP'C hk), ?_⟩, ⟨?_⟩⟩
    · rw [hcardP', hcardP, hZ2']
      omega
    · exact (quotientOddCoreEquiv hO).trans (P.equivMapOfInjective eY.toMonoidHom eY.injective)

theorem hyp31RowFacts_m (F : TwoAFacts) (mf : MonsterFacts (Carrier .M))
    (mi : MonsterInvolutions (Carrier .M)) (inp : MHyp31Inputs) :
    Hyp31RowFacts MIsK [.M] [] [.B] where
  reach := ⟨_, reachRow_m F mf mi inp⟩
  evenOut := fun s hs => by
    rw [List.mem_singleton] at hs
    subst hs
    exact evenCoverExcl_M inp.noCover
  up := ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  thm24 := fun s hs => by
    rw [List.mem_singleton] at hs
    exact Or.inl hs
  std_row := fun G _ _ L K₁ T s hL hT hdata hq hK =>
    stdRow_m mf (oddMultTrivial_m inp.noCover) G L K₁ T s hL hT hdata hq hK
  four_a := fourA_m mf (oddMultTrivial_m inp.noCover) inp.bInvCent

end Fields

end CFSG.EvenSporadicStandard.Induction.Hyp
