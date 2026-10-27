module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporCardRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeM2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Out
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.LocalAnalysis.GLTheoremA.S8.I2014HN
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIII
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66At
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.L3AutGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeB2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.GLTheoremA.K14Spor (CardRow cardRow_of_model)
open CFSG.LocalAnalysis.GLTheoremA.BMType
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] noncomputable def inducedAut {Y : Type} [Group Y] (α : MulAut Y) :
    MulAut (Y ⧸ Subgroup.center Y) :=
  QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) α (Subgroup.map_center_eq α)

theorem component_to_simple_explicit {Y : Type} [Group Y] [Finite Y] {α : MulAut Y}
    {J : Subgroup Y}
    (hJ : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) J) :
    ∃ J' : Subgroup (Y ⧸ Subgroup.center Y),
      GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (inducedAut α)) J' ∧
        ∃ ψ : PQuot 3 J →* PQuot 3 J', Function.Surjective ψ ∧
          ψ.ker ≤ Subgroup.center (PQuot 3 J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center Y := (QuotientGroup.ker_mk' _).le
  have hαβ : ∀ y, π (α y) = inducedAut α (π y) := fun y => rfl
  have hJ' : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (inducedAut α))
      (J.map π) :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup π hker α (inducedAut α)
      hαβ hπ Nat.prime_three hJ
  refine ⟨J.map π, hJ', ?_⟩
  let φ0 : ↥J →* PQuot 3 (J.map π) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(J.map π))).comp (π.subgroupMap J)
  have hφ0 : Function.Surjective φ0 :=
    (QuotientGroup.mk'_surjective _).comp (MonoidHom.subgroupMap_surjective π J)
  have hker0 : GLAPPrimeCore 3 ↥J ≤ φ0.ker := by
    intro x hx
    have := CFSG.map_pPrimeCore_le (π.subgroupMap J) (MonoidHom.subgroupMap_surjective π J)
      ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 this
  let ψ : PQuot 3 J →* PQuot 3 (J.map π) := QuotientGroup.lift (GLAPPrimeCore 3 ↥J) φ0 hker0
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ0 y
    exact ⟨QuotientGroup.mk x, rfl⟩
  refine ⟨ψ, hψ, ?_⟩
  have hKq : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ
  have hKq' : CFSG.Open.IsQuasisimple (PQuot 3 (J.map π)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ'
  have hKqn : CFSG.IsQuasisimple (PQuot 3 J) :=
    ⟨⟨hKq.1⟩, hKq.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hKq⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKqn (inferInstance : ψ.ker.Normal) with h | h
  · exfalso
    have hsub : Subsingleton (PQuot 3 (J.map π)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := hψ a
      obtain ⟨y, rfl⟩ := hψ b
      have hx : x ∈ ψ.ker := h ▸ Subgroup.mem_top x
      have hy : y ∈ ψ.ker := h ▸ Subgroup.mem_top y
      rw [MonoidHom.mem_ker] at hx hy
      rw [hx, hy]
    have := hKq'.2.toNontrivial
    obtain ⟨a, b, hab⟩ :=
      exists_pair_ne (PQuot 3 (J.map π) ⧸ Subgroup.center (PQuot 3 (J.map π)))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (congrArg _ (Subsingleton.elim a b))
  · exact h

theorem eq_one_of_inducedAut_eq_one {Y : Type} [Group Y] (hY : commutator Y = ⊤) {α : MulAut Y}
    (h : inducedAut α = 1) : α = 1 := by
  have hinj := CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hY
  apply hinj
  rw [map_one]
  exact h

theorem isType1430_cases {T : Type} [Group T] (h : catalogIs T S8.L84.isType1430) :
    catalogIs T (isAltN 9) ∨ catalogIs T (S8.sporIs .J3) ∨ catalogIs T S9.isSp6two ∨
      catalogIs T (onLie fun | .A 1 q => q.card = 729 | _ => False) ∨
      catalogIs T S9.isSp4eight := by
  obtain ⟨i, hi, he⟩ := h
  rcases hi with hi | hi | hi
  · exact Or.inl ⟨i, hi, he⟩
  · exact Or.inr (Or.inl ⟨i, hi, he⟩)
  · cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | B r q =>
        rcases r with _ | _ | _ | _ | r
        · exact hi.elim
        · exact hi.elim
        · have hq : q.card = 8 := hi
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨TauCeti.CFSGIndex.lie ⟨_, hv⟩, hq, he⟩)))
        · have hq : q.card = 2 := hi
          exact Or.inr (Or.inr (Or.inl ⟨TauCeti.CFSGIndex.lie ⟨_, hv⟩, hq, he⟩))
        · exact hi.elim
      | A r q =>
        rcases r with _ | _ | r
        · exact hi.elim
        · have hq : q.card = 729 := hi
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨TauCeti.CFSGIndex.lie ⟨_, hv⟩, hq, he⟩)))
        · exact hi.elim
      | _ => exact hi.elim
    | _ => exact hi.elim

theorem not_pow_six_dvd_aux {o m : ℕ} (a : ℕ) (ha : a ≤ 6) (hm : ¬ 3 ∣ m)
    (ho : ¬ 3 ^ (6 - a) ∣ o) : ¬ 3 ^ 6 ∣ o * (3 ^ a * m) := by
  intro h
  have h6 : (3 : ℕ) ^ 6 = 3 ^ a * 3 ^ (6 - a) := by rw [← pow_add]; congr 1; omega
  rw [h6, show o * (3 ^ a * m) = 3 ^ a * (o * m) by ring] at h
  have h1 := (Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num : 0 < 3) a)).1 h
  have hcop : Nat.Coprime (3 ^ (6 - a)) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm)
  exact ho (hcop.dvd_of_dvd_mul_right h1)


theorem typeHyp2_alt9
    : TypeHyp2 (isAltN 9) 181440 where
  card T _ _ h := by
    obtain ⟨i, hi, ⟨e⟩⟩ := h
    cases i with
    | alternating n hn =>
      simp only [isAltN] at hi
      subst hi
      rw [CFSG.LocalAnalysis.GLTheoremA.CatDistinct.card_alternating_of_iso hn e]
      decide
    | _ => exact hi.elim
  aut T _ _ h := by
    obtain ⟨i, hi, ⟨e⟩⟩ := h
    cases i with
    | alternating n hn =>
      simp only [isAltN] at hi
      subst hi
      have ho := CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.card_outer_of_equiv e
      have h9 : ¬ 9 ∣ Nat.card (Outer T) := by
        rw [ho]
        exact CFSG.AGLEmbedding.not_nine_dvd_card_outer_alt hn
      rw [show (181440 : ℕ) = 3 ^ 4 * 2240 by norm_num]
      exact not_pow_six_dvd_aux 4 (by norm_num) (by norm_num) (by simpa using h9)
    | _ => exact hi.elim
  big := by norm_num
  eleven := by norm_num
  thirtyone := by norm_num
  nine := by norm_num

theorem typeHyp2_sp6two
    : TypeHyp2 S9.isSp6two 1451520 where
  card _ _ _ h := K14Spor.card_sp6two h
  aut T _ _ h := by
    have h3 := CFSG.LocalAnalysis.GLTheoremA.CatB.not_three_dvd_outer_sp6two h
    rw [show (1451520 : ℕ) = 3 ^ 4 * 17920 by norm_num]
    refine not_pow_six_dvd_aux 4 (by norm_num) (by norm_num) fun h9 => h3 ?_
    exact (dvd_pow_self 3 (by norm_num)).trans h9
  big := by norm_num
  eleven := by norm_num
  thirtyone := by norm_num
  nine := by norm_num

theorem typeHyp2_sp4eight
    : TypeHyp2 S9.isSp4eight 1056706560 where
  card T _ _ h := by
    obtain ⟨i, hi, ⟨f⟩⟩ := h
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | B r q =>
        rcases r with _ | _ | _ | r
        · exact False.elim hi
        · exact False.elim hi
        · have hq : q.card = 8 := hi
          rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hv⟩ T ⟨f⟩]
          show orderBC 2 q.card = 1056706560
          rw [hq]
          decide
        · exact False.elim hi
      | _ => exact False.elim hi
    | _ => exact False.elim hi
  aut T _ _ h := by
    have h6 := CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Out.card_outer_sp4eight_le h
    have hpos : 0 < Nat.card (Outer T) := by
      haveI : Finite (MulAut T) := CFSG.HardMathSupport.Dickson.Sec6.BM2.finite_mulAut T
      haveI : Finite (Outer T) :=
        Finite.of_surjective _ (QuotientGroup.mk'_surjective _ : Function.Surjective
          (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)))
      exact Nat.card_pos
    rw [show (1056706560 : ℕ) = 3 ^ 4 * 13045760 by norm_num]
    refine not_pow_six_dvd_aux 4 (by norm_num) (by norm_num) fun h9 => ?_
    have := Nat.le_of_dvd hpos h9
    norm_num at this
    omega
  big := by norm_num
  eleven := by norm_num
  thirtyone := by norm_num
  nine := by norm_num

theorem typeHyp2_j3
    : TypeHyp2 (S8.sporIs .J3) 50232960 where
  card T _ _ h := by
    obtain ⟨i, hi, ⟨e⟩⟩ := h
    simp only [S8.sporIs] at hi
    subst hi
    rw [Nat.card_congr e.toEquiv,
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds]
    decide
  aut T _ _ h := by
    obtain ⟨i, hi, ⟨e⟩⟩ := h
    simp only [S8.sporIs] at hi
    subst hi
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .J3
    have ho : Nat.card (Outer T) = Nat.card (Outer NativeSporadic.J3) :=
      CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.card_outer_of_equiv (e.trans b.symm)
    have h2 : Nat.card (Outer T) ≤ 2 := ho ▸ CFSG.RankThree.PartTwo.Sec4.card_outer_J3
    have hpos : 0 < Nat.card (Outer T) := by
      haveI : Finite (MulAut T) := CFSG.HardMathSupport.Dickson.Sec6.BM2.finite_mulAut T
      haveI : Finite (Outer T) :=
        Finite.of_surjective _ (QuotientGroup.mk'_surjective _ : Function.Surjective
          (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)))
      exact Nat.card_pos
    rw [show (50232960 : ℕ) = 3 ^ 5 * 206720 by norm_num]
    refine not_pow_six_dvd_aux 5 (by norm_num) (by norm_num) fun h3 => ?_
    have := Nat.le_of_dvd hpos h3
    norm_num at this
    omega
  big := by norm_num
  eleven := by norm_num
  thirtyone := by norm_num
  nine := by norm_num

theorem card_l2_729
    {T : Type} [Group T] [Finite T]
    (h : catalogIs T (onLie fun | .A 1 q => q.card = 729 | _ => False)) :
    Nat.card T = 193709880 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · exact False.elim hi
      · have hq : q.card = 729 := hi
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hv⟩ T ⟨f⟩]
        show orderA 1 q.card = 193709880
        rw [hq]
        decide
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

theorem card_isType1430
    {T : Type} [Group T] [Finite T] (h : catalogIs T S8.L84.isType1430) :
    Nat.card T = 181440 ∨ Nat.card T = 50232960 ∨ Nat.card T = 1451520 ∨
      Nat.card T = 193709880 ∨ Nat.card T = 1056706560 := by
  rcases isType1430_cases h with h | h | h | h | h
  · exact Or.inl (typeHyp2_alt9.card T h)
  · exact Or.inr (Or.inl (typeHyp2_j3.card T h))
  · exact Or.inr (Or.inr (Or.inl (typeHyp2_sp6two.card T h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (card_l2_729 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (typeHyp2_sp4eight.card T h))))

theorem cardRow_of_not_dvd
    {n : ℕ} {s : TauCeti.SporadicName}
    (h : ¬ n ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s) : CardRow n s := by
  intro S _ _ ⟨e⟩ β _ _ J _ hc
  apply h
  rw [← (Nat.card_congr e.toEquiv).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s), ← hc]
  have h2 : Nat.card (PSimple 3 J) ∣ Nat.card (PQuot 3 J) := Subgroup.card_quotient_dvd_card _
  have h3 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  exact h2.trans (h3.trans (Subgroup.card_subgroup_dvd_card J))

theorem typeRow2_B
    {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp2 P n) :
    TypeRow P .B := by
  obtain ⟨hfin, hs, ⟨b⟩, hnc⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_B
  exact @typeRow_of_model P .B (Carrier .B) _ hfin hs
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds b hnc
    fun k hk J hJ hT => false_of_type2_B hP (s := k) hk hJ hT

theorem typeRow2_M
    {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp2 P n) :
    TypeRow P .M := by
  obtain ⟨-, hs, hfin⟩ := CFSG.Monster.Generated.generated_rational_group_finite_simple
  obtain ⟨b⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  have hnc : ∃ a c : CFSG.Monster.Generated.Gmat, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by
      rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, CFSG.Open.monsterOrder]
      norm_num)
  exact @typeRow_of_model P .M CFSG.Monster.Generated.Gmat _ hfin hs
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds b hnc
    fun k hk J hJ hT => false_of_type2_gmat hP (s := k) hk hJ hT

theorem cardRow_1430
    {s : TauCeti.SporadicName} (hHN : s ≠ .HN) (hCo1 : s ≠ .Co1)
    (hB : s ≠ .B) (hM : s ≠ .M) {n : ℕ}
    (hn : n = 181440 ∨ n = 50232960 ∨ n = 1451520 ∨ n = 193709880 ∨ n = 1056706560) :
    CardRow n s := by
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases s <;>
    first
    | exact absurd rfl hHN
    | exact absurd rfl hCo1
    | exact absurd rfl hB
    | exact absurd rfl hM
    | exact cardRow_of_not_dvd (by decide +kernel)
    | exact K14Spor.cardRow_j3' hOut hbr (by decide) (by decide)
    | exact K14Spor.cardRow_mcl' hOut hbr _
    | exact K14Spor.cardRow_suz' hOut hbr (by decide) (by decide)
    | exact K14Spor.cardRow_co3' hOut hbr (by decide)
    | exact K14Spor.cardRow_co2' hOut hbr (by decide)
    | exact K14Spor.cardRow_on' hOut hbr (by decide)
    | exact K14Spor.cardRow_fi22' hOut hbr (by decide)
    | exact K14Spor.cardRow_fi23' hOut hbr (by decide)
    | exact K14Spor.cardRow_fi24' hbr hOut (by decide) (by decide)
    | exact K14Spor.cardRow_ly' hOut hbr (by decide)
    | exact K14Spor.cardRow_th' hOut hbr (by decide)

theorem typeRow_1430
    {s : TauCeti.SporadicName} (hHN : s ≠ .HN) (hCo1 : s ≠ .Co1) :
    TypeRow S8.L84.isType1430 s := by
  intro S _ _ e β hβ hβ1 J hJ hT
  by_cases hB : s = .B
  · subst hB
    rcases isType1430_cases hT with h | h | h | h | h
    · exact typeRow2_B typeHyp2_alt9 S e β hβ hβ1 J hJ h
    · exact typeRow2_B typeHyp2_j3 S e β hβ hβ1 J hJ h
    · exact typeRow2_B typeHyp2_sp6two S e β hβ hβ1 J hJ h
    · exact cardRow_of_not_dvd (n := 193709880) (by decide) S e β hβ hβ1 J hJ (card_l2_729 h)
    · exact typeRow2_B typeHyp2_sp4eight S e β hβ hβ1 J hJ h
  by_cases hM : s = .M
  · subst hM
    rcases isType1430_cases hT with h | h | h | h | h
    · exact typeRow2_M typeHyp2_alt9 S e β hβ hβ1 J hJ h
    · exact typeRow2_M typeHyp2_j3 S e β hβ hβ1 J hJ h
    · exact typeRow2_M typeHyp2_sp6two S e β hβ hβ1 J hJ h
    · exact cardRow_of_not_dvd (n := 193709880) (by decide) S e β hβ hβ1 J hJ (card_l2_729 h)
    · exact typeRow2_M typeHyp2_sp4eight S e β hβ hβ1 J hJ h
  exact cardRow_1430 hHN hCo1 hB hM (card_isType1430 hT) S e β hβ hβ1 J hJ rfl

set_option maxRecDepth 10000 in
theorem not_rkY_co1
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hcore : GLAPPrimeCore 3 Y = ⊥)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group)
    (hRk : CFSG.HardMathSupport.Dickson.Sec6.I1431.RkY Y) : False := by
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  have hdvd := CFSG.LocalAnalysis.GLTheoremA.i66_card_center_dvd
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
    inferInstance .Co1 e
  have hZ3 : IsPGroup 3 (Subgroup.center Y) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot
      Nat.prime_three hcore
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hZ3
  have h2 : Nat.card (Subgroup.center Y) ∣ 2 := by
    have : CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder .Co1 = 2 := by decide
    rwa [this] at hdvd
  have h1 : Nat.card (Subgroup.center Y) = 1 := by
    rw [ha] at h2 ⊢
    rcases a with _ | a
    · rfl
    · exfalso
      have : 3 ∣ 2 := (dvd_pow_self 3 (Nat.succ_ne_zero a)).trans h2
      omega
  have hZ : Subgroup.center Y = ⊥ := (Subgroup.eq_bot_iff_card _).2 h1
  have eY : Y ≃* Y ⧸ Subgroup.center Y :=
    (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  haveI : Finite NativeSporadic.Co1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  let φ : NativeSporadic.Co1 ≃* Y := b.trans (e.symm.trans eY.symm)
  obtain ⟨U, E, hU2, hU1, hEN, hEe, hEc⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.CoRows.exists_local_of_equiv
    (CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank Nat.prime_three (k := 4)
      (by norm_num) CFSG.RankThree.PartTwo.Census.four_le_localRank_three_Co1) φ
  have hEZ : E ⊓ Subgroup.center Y = ⊥ := by simp [hZ]
  have := (hRk U hU1 hU2 E hEN hEe).2 hEZ
  rw [hEc] at this
  norm_num at this

theorem i1431SporS_holds
    : I1431SporS := by
  intro Y _ _ hY hcore hRk s hcat ξ hξ3 hξ1 J hJ hJT
  by_contra hHN
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  by_cases hCo1 : s = .Co1
  · subst hCo1
    exact not_rkY_co1 hY hcore e hRk
  obtain ⟨J', hJ', ψ, hψs, hψk⟩ := component_to_simple_explicit hJ
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ
  have hq' : CFSG.Open.IsQuasisimple (PQuot 3 J') :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ'
  haveI : Nontrivial (PQuot 3 J') := by
    have := hq'.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 J' ⧸ Subgroup.center (PQuot 3 J'))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.psimple_equiv_of_central_surj hq ψ hψs hψk
  have hT' : catalogIs (PSimple 3 J') S8.L84.isType1430 := catalogIs_of_mulEquiv eP.symm hJT.1
  have hβ3 : inducedAut ξ ^ 3 = 1 := by
    rw [show inducedAut ξ = CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot Y ξ from rfl,
      ← map_pow, hξ3, map_one]
  have hβ1 : inducedAut ξ ≠ 1 := fun h => hξ1 (eq_one_of_inducedAut_eq_one hY.1 h)
  exact typeRow_1430 hHN hCo1 (Y ⧸ Subgroup.center Y) ⟨e⟩ (inducedAut ξ) hβ3 hβ1 J' hJ' hT'

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
