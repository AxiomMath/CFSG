module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwisted
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyChain
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsKG2Dichotomy

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped MatrixGroups commutatorElement

section Centres

theorem center_modelUniv_G2 (n p e : ℕ) (hp : p.Prime) :
    Subgroup.center (modelUniv .G2 n p e hp).K = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot

theorem center_twistedGroup_eq_bot_of_card {K : Type} [Field K] [Finite K] (σ : K →+* K) {p e : ℕ}
    (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = (p ^ e) ^ 3) (hσq : ∀ c, σ c = c ^ (p ^ e)) :
    Subgroup.center (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ) = ⊥ := by
  have hq : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  let σ' : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hσsurj⟩
  have hσ' : σ'.toRingHom = σ := rfl
  obtain ⟨-, -, hder, -⟩ := CFSG.LieType.Chevalley.finite_fixed_root_group_perfect
    (p := p) (f := e) .D4 hp he K hK σ hσq
  have hcen := CFSG.LieType.Chevalley.exceptional_fixed_center_trivial .D4 K σ'
  rw [hσ'] at hcen
  let E := CFSG.LieType.Steinberg.TwistedD4.twistedGroupEquivDerived σ hq hK hσq
  let E' := E.trans (MulEquiv.subgroupCongr hder)
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hc : E' z ∈ Subgroup.center ↥(CFSG.LieType.Chevalley.graphFixedRootGroup .D4 K σ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := E'.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz h]
  rw [hcen, Subgroup.mem_bot] at hc
  exact E'.injective (hc.trans (map_one E').symm)

theorem center_modelUniv_triality (n p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    Subgroup.center (modelUniv .trialityD4 n p e hp).K = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  exact center_twistedGroup_eq_bot_of_card (iterateFrobenius (GaloisField p (3 * e)) p e) hp he hK
    (fun c => iterateFrobenius_def p e c)

theorem center_modelUniv_eq_bot_of_exc {t : StatedLieTag} (n p e : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (ht : t = .G2 ∨ t = .trialityD4) : Subgroup.center (modelUniv t n p e hp).K = ⊥ := by
  rcases ht with rfl | rfl
  exacts [center_modelUniv_G2 n p e hp, center_modelUniv_triality n p e hp he]

end Centres

section Unique

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem isUniqueInvolution_of_exact (hodd : Odd (Nat.card (GaloisField p f)))
    {L : Subgroup G} (hL : classicalInvolutionOddCore L = ⊥) {z : G}
    (hz : IsClassicalMember p f L z) : IsUniqueInvolution L z where
  mem := hz.mem
  ne_one := by
    intro h
    have := hz.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  sq := by
    have := pow_orderOf_eq_one z
    rwa [hz.orderOf_eq_two, pow_two] at this
  unique := by
    intro y hy hyy
    obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hL
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      have h2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1
      have h3 : orderOf (⟨y, hy⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h2
      have h4 : orderOf (⟨z, hz.mem⟩ : ↥L) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact hz.orderOf_eq_two
      have := ((CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp h3).trans
        ((CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp h4).symm
      exact congrArg Subtype.val this

end Unique

section Twin

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem modelTwinClass_of_family_x {ι : Type} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {j : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag j)
      (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D)
    (hperf : FundPerfect (D.tag j) (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D)
    (T : ι → Subgroup G) (hTx : ∀ k, T k ∈ centralizingMembers Ω {x})
    (hTj : ∀ k, locImg Ω x (T k) ≤ (D.hom j).range) (hinj : Function.Injective T)
    (hcomm : ∀ k l, k ≠ l → Commutes (T k) (T l))
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, ∀ k l,
      (N = T k ∨ Commutes N (T k)) ↔ (N = T l ∨ Commutes N (T l))) :
    ∃ F : ι → Subgroup (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).K,
      (∀ k, F k ∈ compFund D j) ∧ Function.Injective F ∧
      (∀ k l, k ≠ l → Commutes (F k) (F l)) ∧
      ∀ k l, ∀ S ∈ compFund D j, (S = F k ∨ Commutes S (F k)) ↔ (S = F l ∨ Commutes S (F l)) := by
  choose R hR using fun k => exists_corr_left hΩ hex D (⟨hTx k, hTj k⟩ : T k ∈ compMembers Ω x D j)
  refine ⟨R, fun k => (hR k).2.1, ?_, ?_, ?_⟩
  · intro k l hkl
    exact hinj (corr_unique_right hΩ hP1 (hR k) (hkl ▸ hR l))
  · intro k l hkl
    exact (corr_commutes hΩ hP1 hperf (hR k) (hR l)).mp (hcomm k l hkl)
  · intro k l S hS
    obtain ⟨N, hN⟩ := exists_corr_right hΩ D hsc hS
    have key : ∀ m, (S = R m ∨ Commutes S (R m)) ↔ (N = T m ∨ Commutes N (T m)) := by
      intro m
      constructor
      · rintro (h | h)
        · left
          exact corr_unique_right hΩ hP1 (h ▸ hN) (hR m)
        · right
          exact (corr_commutes hΩ hP1 hperf hN (hR m)).mpr h
      · rintro (h | h)
        · left
          exact corr_unique_left hperf (h ▸ hN) (hR m)
        · right
          exact (corr_commutes hΩ hP1 hperf hN (hR m)).mp h
    rw [key k, key l]
    exact htwin N hN.1 k l

end Twin

section Tags

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem orderOf_mul_of_commute_involutions {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hc : a * b = b * a) (hne : a ≠ b) : orderOf (a * b) = 2 := by
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, pow_two] at this
  have hbb : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb, pow_two] at this
  refine orderOf_eq_prime (by
    rw [pow_two]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hc]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, one_mul]) ?_
  intro h
  apply hne
  have h1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have h2 : a = b⁻¹ := mul_eq_one_iff_eq_inv.mp h
  rw [h2, h1]

omit [Finite G] in
theorem locMk_mul_central {x z w : G} (hzY : z ∈ locLayer Ω x) (hwY : w ∈ locLayer Ω x)
    (hx : z * w = x) (a : locQuot Ω x) :
    locMk Ω x ⟨z, hzY⟩ * locMk Ω x ⟨w, hwY⟩ * a =
      a * (locMk Ω x ⟨z, hzY⟩ * locMk Ω x ⟨w, hwY⟩) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  rw [← map_mul]
  show QuotientGroup.mk' _ (_ * y) = QuotientGroup.mk' _ (y * _)
  congr 1
  apply Subtype.ext
  have := Subgroup.mem_centralizer_singleton_iff.mp
    (centralizingLayer_le_centralizer Ω {x} y.2)
  show z * w * (y : G) = (y : G) * (z * w)
  rw [hx]
  exact this.symm

theorem model_false_of_central {t : StatedLieTag} {n e : ℕ} (he : 1 ≤ e) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (ht : t = .G2 ∨ t = .trialityD4) {X : Type} [Group X]
    (φ : (modelUniv t n p e Fact.out).K →* X) (hker : φ.ker ≤ Subgroup.center _) {a : X}
    (ha : a ∈ φ.range) (hc : ∀ y : X, a * y = y * a) (h1 : a ≠ 1) : False := by
  obtain ⟨r, rfl⟩ := ha
  have hqs := CFSG.ClassicalInvolution.ModelFacts.isQuasisimple_modelUniv t n p e Fact.out hfund
    hadm
  have : Group.IsPerfect (modelUniv t n p e Fact.out).K := ⟨hqs.1⟩
  have hr : r ∈ Subgroup.center (modelUniv t n p e Fact.out).K := by
    refine mem_center_of_comm_mem_center fun s => hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hc (φ s))
  rw [center_modelUniv_eq_bot_of_exc n p e Fact.out he ht, Subgroup.mem_bot] at hr
  exact h1 (by rw [hr, map_one])

theorem tag_of_twins (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {i : Fin D.card} {K M : Subgroup G}
    (hK : K ∈ compMembers Ω x D i) (hM : M ∈ compMembers Ω x D i) (hKM : Commutes K M)
    (hne : K ≠ M) {z w : G} (hz : IsClassicalMember p f K z) (hw : IsClassicalMember p f M w)
    (hxzw : z * w = x) (hzw : z ≠ w)
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, (N = K ∨ Commutes N K) ↔ (N = M ∨ Commutes N M)) :
    D.exp i = f ∧ (D.tag i = .PSL ∨ D.tag i = .PSU ∨ D.tag i = .PSp ∨ D.tag i = .POmegaOdd ∨
      D.tag i = .POmegaPlus ∨ D.tag i = .POmegaMinus) := by
  have hq4 : 4 ≤ p ^ f := by omega
  have hexp := D.exp_eq i
  by_cases hex2 : D.tag i = .G2 ∨ D.tag i = .trialityD4
  · exfalso
    have hzY : z ∈ locLayer Ω x := le_centralizingLayer hK.1 hz.mem
    have hwY : w ∈ locLayer Ω x := le_centralizingLayer hM.1 hw.mem
    have ha₁ : locMk Ω x ⟨z, hzY⟩ ∈ (D.hom i).range :=
      hK.2 ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
    have ha₃ : locMk Ω x ⟨w, hwY⟩ ∈ (D.hom i).range :=
      hM.2 ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr hw.mem, rfl⟩
    have hcomm : z * w = w * z := hKM z hz.mem w hw.mem
    have hx2 : orderOf x = 2 := by
      rw [← hxzw]
      exact orderOf_mul_of_commute_involutions hz.orderOf_eq_two hw.orderOf_eq_two hcomm hzw
    have hxY : x ∈ locLayer Ω x := hxzw ▸ (locLayer Ω x).mul_mem hzY hwY
    have hmul : locMk Ω x ⟨z, hzY⟩ * locMk Ω x ⟨w, hwY⟩ = locElt Ω x x hxY := by
      have := locElt_mul hzY hwY
      simp only [locElt] at this ⊢
      rw [this]
      congr 1
      exact Subtype.ext hxzw
    have hne1 : locMk Ω x ⟨z, hzY⟩ * locMk Ω x ⟨w, hwY⟩ ≠ 1 := by
      rw [hmul]
      intro h1
      have := orderOf_locElt hxY hx2
      rw [h1, orderOf_one] at this
      omega
    have hexp' : 1 ≤ D.exp i := by
      have := (D.admissible i).2.1
      omega
    exact model_false_of_central hexp' (D.isFundTag i) (D.admissible i) hex2 (D.hom i)
      (D.ker_le_center i) (mul_mem ha₁ ha₃) (locMk_mul_central hzY hwY hxzw) hne1
  have hDe : D.exp i = f := by
    rcases hexp with h | ⟨h, -⟩
    · exact h
    · exact absurd (Or.inr h) hex2
  have hG2 : D.tag i ≠ .G2 := fun h => hex2 (Or.inl h)
  have hD4 : D.tag i ≠ .trialityD4 := fun h => hex2 (Or.inr h)
  by_cases hfe : D.tag i = .F4 ∨ D.tag i = .E6 ∨ D.tag i = .E7 ∨ D.tag i = .E8 ∨
      D.tag i = .twistedE6
  · exfalso
    have hsc := fundamentalSingleClass_of_ne D i hG2 hD4
    have hperf := fundPerfect_modelUniv hp2 (D.isFundTag i) (D.admissible i)
      (by rw [hDe]; exact hq4)
    obtain ⟨F, hFmem, hFinj, hFcomm, hFtwin⟩ := modelTwinClass_of_family_x hΩ hex hP1 D hsc hperf
      (ι := Fin 2) ![K, M]
      (by intro k; fin_cases k; exacts [hK.1, hM.1])
      (by intro k; fin_cases k; exacts [hK.2, hM.2])
      (by
        intro k l hkl
        fin_cases k <;> fin_cases l
        · rfl
        · exact absurd hkl hne
        · exact absurd hkl.symm hne
        · rfl)
      (by
        intro k l hkl
        fin_cases k <;> fin_cases l
        · exact absurd rfl hkl
        · exact hKM
        · exact hKM.symm
        · exact absurd rfl hkl)
      (by
        intro N hN k l
        fin_cases k <;> fin_cases l
        · exact Iff.rfl
        · exact htwin N hN
        · exact (htwin N hN).symm
        · exact Iff.rfl)
    have hadm : StatedLieAdmissible (D.tag i) (D.rank i) p f := by
      have := D.admissible i
      rwa [hDe] at this
    exact Exotic.mfTwinExc hp2 hq (D.tag i) (D.rank i) 2 hfe hadm le_rfl
      (Exotic.modelTwinClass_congr rfl rfl hDe ⟨F, hFmem, hFinj, hFcomm, hFtwin⟩)
  refine ⟨hDe, ?_⟩
  have h1 := D.isFundTag i
  revert h1 hex2 hfe
  generalize D.tag i = t
  intro h1 hex2 hfe
  cases t <;> simp_all [IsFundTag]

end Tags

section Chain

variable {p : ℕ} [Fact p.Prime]

theorem chainSign_of_lifts {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hcls : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n p e) {X : Type} [Group X]
    (φ : (modelUniv t n p e Fact.out).K →* X) (hker : φ.ker ≤ Subgroup.center _)
    {R₁ R₂ R₃ : Subgroup (modelUniv t n p e Fact.out).K}
    (h₁ : R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (h₂ : R₂ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (h₃ : R₃ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) {a₁ a₂ a₃ : X}
    (ha₁ : IsUniqueInvolution (R₁.map φ) a₁) (ha₂ : IsUniqueInvolution (R₂.map φ) a₂)
    (ha₃ : IsUniqueInvolution (R₃.map φ) a₃) (hcen : ∀ y : X, a₁ * a₃ * y = y * (a₁ * a₃))
    (hnorm : conjSub a₂ (R₁.map φ) = R₁.map φ) (hR₁₃ : Commutes (R₁.map φ) (R₃.map φ))
    (hne₁₂ : R₁.map φ ≠ R₂.map φ) (hne₃₂ : R₃.map φ ≠ R₂.map φ)
    (hnc₁₂ : ¬ Commutes (R₁.map φ) (R₂.map φ)) (hnc₃₂ : ¬ Commutes (R₃.map φ) (R₂.map φ)) :
    ((∃ W, LinearBlockStandardPair (GaloisField p e) W (R₁.map φ) (R₂.map φ)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p e) W (R₂.map φ) (R₃.map φ)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₁.map φ) (R₂.map φ)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₂.map φ) (R₃.map φ)) := by
  have hG2 : t ≠ .G2 := by rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hfund : IsFundTag t := by rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [hcard]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by omega
  have hSL2 : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField p e)) := fun R hR =>
    CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund
      hadm hG2 hD4 hR
  have hlong : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      R ∈ CFSG.ClassicalInvolution.ModelFacts.longestFundamental
        (modelUniv t n p e Fact.out).D := fun R hR =>
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR
  obtain ⟨c₁, hc₁, ho₁, hu₁, ha₁', -, hperf₁⟩ :=
    ConnectedA2.exists_lift_central_involution hodd h4 φ hker (hSL2 R₁ h₁).some ha₁
  obtain ⟨c₂, hc₂, ho₂, -, ha₂', -, -⟩ :=
    ConnectedA2.exists_lift_central_involution hodd h4 φ hker (hSL2 R₂ h₂).some ha₂
  obtain ⟨c₃, hc₃, ho₃, -, ha₃', -, hperf₃⟩ :=
    ConnectedA2.exists_lift_central_involution hodd h4 φ hker (hSL2 R₃ h₃).some ha₃
  have hqs := CFSG.ClassicalInvolution.ModelFacts.isQuasisimple_modelUniv t n p e Fact.out hfund
    hadm
  have : Group.IsPerfect (modelUniv t n p e Fact.out).K := ⟨hqs.1⟩
  have hperf₁' : ⁅R₁, R₁⁆ = R₁ :=
    le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) hperf₁
  have hR₁₃' : Commutes R₁ R₃ := commutes_of_map_commutes hker hperf₁' hR₁₃
  have h₁₃ : c₁ * c₃ = c₃ * c₁ := hR₁₃' c₁ hc₁ c₃ hc₃
  have hz13 : c₁ * c₃ ∈ Subgroup.center (modelUniv t n p e Fact.out).K := by
    refine mem_center_of_comm_mem_center fun s => hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have : φ (c₁ * c₃) = a₁ * a₃ := by rw [map_mul, ← ha₁', ← ha₃']
    rw [this]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcen (φ s))
  have h₂₁ : c₂ * c₁ = c₁ * c₂ :=
    ConnectedA2.commute_of_conjSub_map hker hperf₁ hc₁ ho₁ hu₁ (by rw [← ha₂']; exact hnorm)
  have h₃₂ : c₃ * c₂ = c₂ * c₃ := by
    have hz := Subgroup.mem_center_iff.mp hz13 c₂
    have : c₁ * (c₂ * c₃) = c₁ * (c₃ * c₂) := by
      calc c₁ * (c₂ * c₃) = (c₁ * c₂) * c₃ := by rw [mul_assoc]
        _ = (c₂ * c₁) * c₃ := by rw [h₂₁]
        _ = c₂ * (c₁ * c₃) := by rw [mul_assoc]
        _ = (c₁ * c₃) * c₂ := hz
        _ = c₁ * (c₃ * c₂) := by rw [mul_assoc]
    exact (mul_left_cancel this).symm
  exact CFSG.ClassicalInvolution.ModelFacts.StandardPairChainSign.map_of_commute
    (CFSG.ClassicalInvolution.ModelFacts.standardPairChainSign_of_classical hcls hadm) hfund hadm
    hp2 hq φ hker (hlong R₁ h₁) (hlong R₂ h₂) (hlong R₃ h₃) hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₂₁.symm h₃₂
    h₁₃ hR₁₃ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂

end Chain

section Images

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem chainSign_images (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hIH : LocalLieSystems p f Ω) {x : G}
    (hxc : ¬ ({x} : Set G) ⊆ Subgroup.center G) (hP1 : LocalOddCentral Ω {x})
    {K β M : Subgroup G} {z v w : G} (hz : IsClassicalMember p f K z)
    (hv : IsClassicalMember p f β v) (hw : IsClassicalMember p f M w)
    (hKx : K ∈ centralizingMembers Ω {x}) (hβx : β ∈ centralizingMembers Ω {x})
    (hMx : M ∈ centralizingMembers Ω {x}) (hxzw : z * w = x) (hzw : z ≠ w)
    (hKM : Commutes K M) (hKM' : K ≠ M) (hKβ : K ≠ β) (hβM : β ≠ M) (hnKβ : ¬ Commutes K β)
    (hnβM : ¬ Commutes β M) (hvK : conjSub v K = K)
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, (N = K ∨ Commutes N K) ↔ (N = M ∨ Commutes N M)) :
    ((∃ W, LinearBlockStandardPair (GaloisField p f) W (locImg Ω x K) (locImg Ω x β)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (locImg Ω x β) (locImg Ω x M)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (locImg Ω x K)
          (locImg Ω x β)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (locImg Ω x β)
          (locImg Ω x M)) := by
  obtain ⟨D⟩ := NonClassical.exists_lieSystemData hIH hxc
  obtain ⟨i, hKi, hβi, hrest⟩ := exists_pair hΩ hex hP1 D hKx hβx hnKβ
  have hMi : M ∈ compMembers Ω x D i := hrest M hMx (fun h => hnβM h.symm)
  obtain ⟨hDe, hcls⟩ := tag_of_twins hp2 hq hΩ hex hP1 D hKi hMi hKM hKM' hz hw hxzw hzw htwin
  obtain ⟨R₁, hR₁⟩ := exists_corr_left hΩ hex D hKi
  obtain ⟨R₂, hR₂⟩ := exists_corr_left hΩ hex D hβi
  obtain ⟨R₃, hR₃⟩ := exists_corr_left hΩ hex D hMi
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f hf]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hzY : z ∈ locLayer Ω x := le_centralizingLayer hKx hz.mem
  have hvY : v ∈ locLayer Ω x := le_centralizingLayer hβx hv.mem
  have hwY : w ∈ locLayer Ω x := le_centralizingLayer hMx hw.mem
  have hu₁ := ConnectedA2.isUniqueInvolution_locImg hex hKx
    (isUniqueInvolution_of_exact hodd (hex K hKx.1) hz)
  have hu₂ := ConnectedA2.isUniqueInvolution_locImg hex hβx
    (isUniqueInvolution_of_exact hodd (hex β hβx.1) hv)
  have hu₃ := ConnectedA2.isUniqueInvolution_locImg hex hMx
    (isUniqueInvolution_of_exact hodd (hex M hMx.1) hw)
  rw [hR₁.2.2] at hu₁
  rw [hR₂.2.2] at hu₂
  rw [hR₃.2.2] at hu₃
  have hnorm : conjSub (locMk Ω x ⟨v, hvY⟩) (R₁.map (D.hom i)) = R₁.map (D.hom i) := by
    have h := locImg_conjSub_layer (Ω := Ω) (x := x) K ⟨v, hvY⟩
    rw [show ((⟨v, hvY⟩ : ↥(locLayer Ω x)) : G) = v from rfl, hvK] at h
    rw [← hR₁.2.2]
    exact h.symm
  have key := chainSign_of_lifts hp2 (by rw [hDe]; exact hq) hcls (D.admissible i) (D.hom i)
    (D.ker_le_center i) hR₁.2.1 hR₂.2.1 hR₃.2.1 hu₁ hu₂ hu₃
    (locMk_mul_central hzY hwY hxzw) hnorm
    (by
      rw [← hR₁.2.2, ← hR₃.2.2]
      exact commutes_locImg_of_commutes hKM)
    (by
      rw [← hR₁.2.2, ← hR₂.2.2]
      intro h
      exact hKβ (locImg_injOn hΩ hP1 hKx hβx h))
    (by
      rw [← hR₃.2.2, ← hR₂.2.2]
      intro h
      exact hβM (locImg_injOn hΩ hP1 hβx hMx h.symm))
    (by
      rw [← hR₁.2.2, ← hR₂.2.2]
      exact fun h => hnKβ ((commutes_iff_locImg hΩ hP1 hKx hβx).mpr h))
    (by
      rw [← hR₃.2.2, ← hR₂.2.2]
      exact fun h => hnβM ((commutes_iff_locImg hΩ hP1 hβx hMx).mpr h.symm))
  rw [← hR₁.2.2, ← hR₂.2.2, ← hR₃.2.2] at key
  rw [hDe] at key
  exact key

end Images

section Pairs

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem unitaryBlockStandardPair_le_sup {K : Type} [Field K] [Finite K] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {X : Type} [Group X] {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair K p f W U V) : W ≤ U ⊔ V := by
  obtain ⟨θ, c, hrange, -, hcases⟩ := h
  have hB : (CFSG.ClassicalInvolution.Phan.B12 K p f).map (MulAut.conj c⁻¹).toMonoidHom ⊔
      (CFSG.ClassicalInvolution.Phan.B23 K p f).map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, CFSG.ClassicalInvolution.Phan.B12_sup_B23 hK hq]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)
  have hW : W = ((CFSG.ClassicalInvolution.Phan.B12 K p f).map
        (MulAut.conj c⁻¹).toMonoidHom).map θ ⊔
      ((CFSG.ClassicalInvolution.Phan.B23 K p f).map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
    rw [← hrange, MonoidHom.range_eq_map, ← hB, Subgroup.map_sup]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hW, h1, h2]
  · rw [hW, h1, h2, sup_comm]

theorem linearBlockStandardPair_locImg {x : G} (hP1 : LocalOddCentral Ω {x}) {A B : Subgroup G}
    (hA : A ≤ locLayer Ω x) (hB : B ≤ locLayer Ω x)
    (h : ∃ W, LinearBlockStandardPair (GaloisField p f) W A B) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W (locImg Ω x A) (locImg Ω x B) := by
  obtain ⟨W, hW⟩ := h
  have hWY : W ≤ locLayer Ω x := (linearBlockStandardPair_le_sup hW).trans (sup_le hA hB)
  have h1 := linearBlockStandardPair_subgroupOf hWY hW
  have h2 := CFSG.ClassicalInvolution.Balance.linearBlockStandardPair_map_of_ker_le_center h1
    (locMk Ω x) (by rw [QuotientGroup.ker_mk']; exact hP1)
  exact ⟨_, h2⟩

theorem unitaryBlockStandardPair_locImg {x : G} (hq : 5 ≤ p ^ f) (hP1 : LocalOddCentral Ω {x})
    {A B : Subgroup G} (hA : A ≤ locLayer Ω x) (hB : B ≤ locLayer Ω x)
    (h : ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W A B) :
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (locImg Ω x A) (locImg Ω x B) := by
  obtain ⟨W, hW⟩ := h
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hWY : W ≤ locLayer Ω x :=
    (unitaryBlockStandardPair_le_sup hK (by omega) hW).trans (sup_le hA hB)
  have h1 := unitaryBlockStandardPair_subgroupOf hWY hW
  have h2 := CFSG.ClassicalInvolution.Balance.unitaryBlockStandardPair_map_of_ker_le_center hK hq h1
    (locMk Ω x) (by rw [QuotientGroup.ker_mk']; exact hP1)
  exact ⟨_, h2⟩

variable [Finite G]

theorem linear_of_chainSign_images (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {K β M : Subgroup G} (hKx : K ∈ centralizingMembers Ω {x})
    (hβx : β ∈ centralizingMembers Ω {x}) (hMx : M ∈ centralizingMembers Ω {x})
    (hs : ((∃ W, LinearBlockStandardPair (GaloisField p f) W (locImg Ω x K) (locImg Ω x β)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (locImg Ω x β) (locImg Ω x M)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (locImg Ω x K)
          (locImg Ω x β)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (locImg Ω x β)
          (locImg Ω x M)))
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W β M := by
  have h1 := linearBlockStandardPair_locImg hP1 (le_centralizingLayer hKx)
    (le_centralizingLayer hβx) hlin
  obtain ⟨W, hW⟩ := ModelFacts.linear_of_chain_sign hp2 hq hs h1
  exact linearBlockStandardPair_of_locImg (by omega) (NonClassical.oddCoverSL3 hq) hΩ hP1 hβx hMx
    hW

theorem unitary_of_chainSign_images (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {K β M : Subgroup G} (hKx : K ∈ centralizingMembers Ω {x})
    (hβx : β ∈ centralizingMembers Ω {x}) (hMx : M ∈ centralizingMembers Ω {x})
    (hs : ((∃ W, LinearBlockStandardPair (GaloisField p f) W (locImg Ω x K) (locImg Ω x β)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (locImg Ω x β) (locImg Ω x M)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (locImg Ω x K)
          (locImg Ω x β)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (locImg Ω x β)
          (locImg Ω x M)))
    (huni : ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K β) :
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W β M := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have h1 := unitaryBlockStandardPair_locImg hq hP1 (le_centralizingLayer hKx)
    (le_centralizingLayer hβx) huni
  obtain ⟨W, hW⟩ := ModelFacts.unitary_of_chain_sign hp2 hq hs h1
  obtain ⟨zβ, hzβ⟩ := hΩ.classical β hβx.1
  obtain ⟨zM, hzM⟩ := hΩ.classical M hMx.1
  exact unitaryBlockStandardPair_of_locImg_perfect hq hK (oddCoverSU3 hp2 hK hq) hP1
    (le_centralizingLayer hβx) (le_centralizingLayer hMx)
    (commutator_eq_of_isClassicalMember hzβ).ge (commutator_eq_of_isClassicalMember hzM).ge hW

end Pairs

end CFSG.ClassicalInvolution.RouteD
