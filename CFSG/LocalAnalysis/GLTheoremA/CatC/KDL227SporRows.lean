module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23ThreeC
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThShape
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporNoComp
public import CFSG.LocalAnalysis.GLTheoremA.S3.I112L227
public import CFSG.LocalAnalysis.GLTheoremA.S8.I2014Core
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.KDL227Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def KDL227SporRow (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (fixSubgroup β) J → ¬ catalogIs (PSimple 3 J) (onLie (isL2 27))

@[expose] def NoL227At (Q : Type) [Group Q] : Prop :=
  ∀ k : Q, k ≠ 1 → k ^ 3 = 1 → ∀ J : Subgroup Q,
    GLAPComponent 3 (Subgroup.centralizer ({k} : Set Q)) J →
      ¬ catalogIs (PSimple 3 J) (onLie (isL2 27))

theorem NoL227At.of_equiv {Q Q' : Type} [Group Q] [Group Q'] [Finite Q'] (e : Q ≃* Q')
    (h : NoL227At Q) : NoL227At Q' := by
  intro k hk1 hk3 J hJ hL
  have hJ' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three e.symm hJ
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv] at hJ'
  refine h (e.symm k) (fun h1 => hk1 (by simpa using congrArg e h1))
    (by rw [← map_pow, hk3, map_one]) _ hJ' ?_
  exact (KDSpor.catalogIs_congr (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3
    (J.equivMapOfInjective e.symm.toMonoidHom e.symm.injective))).1 hL

theorem kdl227Row_of_model {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : NoL227At Q) : KDL227SporRow s := by
  intro S _ _ ⟨e⟩ β hβ hβ1 J hJ hL
  let φ : S ≃* Q := e.trans b.symm
  haveI : IsSimpleGroup S := (MulEquiv.isSimpleGroup_congr φ).2 inferInstance
  have hncS : ∃ a c : S, a * c ≠ c * a := by
    obtain ⟨a, c, hac⟩ := hnc
    refine ⟨φ.symm a, φ.symm c, fun h' => hac ?_⟩
    have := congrArg φ h'
    simpa using this
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h' | h'
    · exact h'
    · obtain ⟨a, c, hac⟩ := hncS
      exact absurd ((Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top c)) a) hac
  have hout := hOut S inferInstance hncS s ⟨e⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, rfl, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three (by norm_num)
      hcen hout β hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hβ1 (map_one MulAut.conj)
  rw [KDSpor.fixSubgroup_conj_eq] at hJ
  exact NoL227At.of_equiv φ.symm h x hx1 hxp J hJ hL

theorem noL227At_of_centShape {Q : Type} [Group Q] [Finite Q]
    {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape 3 Good Q)
    (hnot : ∀ (T : Type) [Group T], Good T → ¬ catalogIs T (onLie (isL2 27))) : NoL227At Q := by
  intro k hk1 hk3 J hJ hL
  rcases h k hk1 hk3 with hc | ⟨J0, -, huniq, hg⟩
  · exact KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three hc hJ
  · obtain rfl := huniq J hJ
    exact hnot _ hg hL

theorem prime_pow_27 {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (h : p ^ f = 27) :
    p = 3 ∧ f = 3 := by
  have hp3 : p = 3 := by
    have hd : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 3 by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h]
      exact dvd_pow_self p hf.ne')
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    (show 3 ^ f = 3 ^ 3 by norm_num [h])⟩

theorem isL2_elim {n : ℕ} {ℓ : TauCeti.LieTypeIndex} (h : isL2 n ℓ) :
    ∃ q : TauCeti.PrimePower, ℓ = .A 1 q ∧ q.card = n := by
  cases ℓ
  case A r q =>
    rcases r with _ | _ | r
    · exact False.elim h
    · exact ⟨q, rfl, h⟩
    · exact False.elim h
  all_goals exact False.elim h

theorem isL227_of_catalogIs' {X : Type} [Group X] (h : catalogIs X (onLie (isL2 27))) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven X := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic name => exact False.elim hi
  | lie d =>
    obtain ⟨ℓ, hv⟩ := d
    have hℓ : isL2 27 ℓ := hi
    obtain ⟨q, rfl, hq⟩ := isL2_elim hℓ
    obtain ⟨p, f, hpp, hff⟩ := q
    have hpf : p ^ f = 27 := (TauCeti.PrimePower.card_def _).symm.trans hq
    obtain ⟨rfl, rfl⟩ := prime_pow_27 hpp hff hpf
    haveI : Fact (Nat.Prime 3) := ⟨hpp⟩
    refine ⟨GaloisField 3 3, inferInstance, inferInstance, ?_, ⟨(e.trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨3, 3, hpp, hff⟩ hv)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 3 3))⟩⟩
    rw [GaloisField.card 3 3 (by norm_num)]
    norm_num

theorem not_card_alt_9828 {T : Type} [Group T] {n : ℕ} (hn : 5 ≤ n)
    (f : T ≃* ↥(alternatingGroup (Fin n))) (hc : Nat.card T = 9828) : False := by
  have h := (Nat.card_congr f.toEquiv).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
  rw [hc] at h
  rcases lt_or_ge n 8 with h8 | h8
  · interval_cases n <;> norm_num [Nat.factorial] at h
  · have := Nat.factorial_le h8
    norm_num [Nat.factorial] at this
    omega

theorem not_catalogIs_L227_of_leafType {T : Type} [Group T]
    (h : CFSG.HardMathSupport.Dickson.I271.LeafType 3 T) : ¬ catalogIs T (onLie (isL2 27)) := by
  intro hL
  rcases h with ⟨-, hn, -⟩ | ⟨n, hn5, -, -, ⟨f⟩⟩
  · exact hn (isL227_of_catalogIs' hL)
  · exact not_card_alt_9828 hn5 f (card_of_catalogIs_L227 hL)

theorem not_catalogIs_L227_of_A6 {T : Type} [Group T]
    (h : CFSG.HardMathSupport.Dickson.I271.IsA6At 3 T) : ¬ catalogIs T (onLie (isL2 27)) := by
  intro hL
  obtain ⟨-, ⟨f⟩⟩ := h
  exact not_card_alt_9828 (by norm_num) f (card_of_catalogIs_L227 hL)

theorem noL227At_of_centShapeSplit {Q : Type} [Group Q] [Finite Q]
    (h : CFSG.HardMathSupport.Dickson.I271.CentShapeSplit 3 Q) : NoL227At Q := by
  intro k hk1 hk3 J hJ hL
  rcases h k hk1 hk3 with hc | ⟨J0, -, huniq, hg⟩
  · exact KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three hc hJ
  · obtain rfl := huniq J hJ
    rcases hg with hg | ⟨hg, -⟩
    · exact not_catalogIs_L227_of_leafType hg hL
    · exact not_catalogIs_L227_of_A6 hg hL

section RowFi22

theorem kdl227Row_Fi22 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDL227SporRow .Fi22 := by
  haveI := CFSG.HardMathSupport.Dickson.I271.TabFi22Small.finite_J_tab
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) :=
    Finite.of_equiv _ CFSG.Sporadic.Fi22.fi22EquivJ.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) :=
    CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) = 64561751654400 :=
    CFSG.Sporadic.Fi22.card_Fi22
  exact kdl227Row_of_model hOut (hbr .Fi22).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (noL227At_of_centShape CFSG.HardMathSupport.Dickson.I271.leafShape_Fi22
      fun _ _ h => not_catalogIs_L227_of_leafType h)

end RowFi22

section RowTh

theorem kdl227Row_Th (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDL227SporRow .Th := by
  haveI : Finite ↥CFSG.Sporadic.Th.J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
    Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th CFSG.Sporadic.Th.th_kernel_facts
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Th) = 90745943887872000 :=
    CFSG.RankThree.OddKernel.card_Th_eq
  exact kdl227Row_of_model hOut (hbr .Th).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (noL227At_of_centShape CFSG.HardMathSupport.Dickson.I271.leafShape_Th
      fun _ _ h => not_catalogIs_L227_of_leafType h)

end RowTh

section RowSuz

theorem kdl227Row_Suz (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDL227SporRow .Suz := by
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Suz) :=
    Finite.of_equiv _ CFSG.Sporadic.SuzOddCore.suzEquivM.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Suz) :=
    CFSG.Sporadic.Suz.isSimpleGroup_Suz
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Suz) = 448345497600 :=
    CFSG.Sporadic.Suz.card_Suz
  exact kdl227Row_of_model hOut (hbr .Suz).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (noL227At_of_centShapeSplit CFSG.HardMathSupport.Dickson.I271.centShapeSplit_Suz)

end RowSuz

section RowFi23

theorem kdl227Row_Fi23 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDL227SporRow .Fi23 := by
  haveI := CFSG.HardMathSupport.Dickson.I271.TabFi23.finite_J23
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) :=
    Finite.of_equiv _ CFSG.Sporadic.Fi23.fi23EquivJ.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) :=
    CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) = 4089470473293004800 :=
    CFSG.Sporadic.Fi23.card_Fi23
  exact kdl227Row_of_model hOut (hbr .Fi23).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (noL227At_of_centShape (CFSG.HardMathSupport.Dickson.I271.TabFi23.leafShape_Fi23_of
      CFSG.HardMathSupport.Dickson.I271.TabFi23.pConstrained_t3_two)
      fun _ _ h => not_catalogIs_L227_of_leafType h)

end RowFi23

theorem card_pSimple_dvd {S : Type} [Group S] [Finite S] (p : ℕ) (J : Subgroup S) :
    Nat.card (PSimple p J) ∣ Nat.card J :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

theorem three_mul_card_pSimple_dvd {S : Type} [Group S] [Finite S] {k : S} (hk : orderOf k = 3)
    {J : Subgroup S} (hJ : J ≤ Subgroup.centralizer ({k} : Set S)) :
    3 * Nat.card (PSimple 3 J) ∣ Nat.card S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkc : ∀ g ∈ J, g * k = k * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 (hJ hg)
  by_cases hkJ : k ∈ J
  · set k' : ↥J := ⟨k, hkJ⟩
    set kb : PQuot 3 J := (QuotientGroup.mk k' : PQuot 3 J) with hkb
    have hZ : kb ∈ Subgroup.center (PQuot 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      rw [hkb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hkc g g.2)
    have hk'3 : orderOf k' = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact hk
    have hkb1 : kb ≠ 1 := by
      intro h
      have hmem : k' ∈ GLAPPrimeCore 3 ↥J := (QuotientGroup.eq_one_iff k').1 h
      have h3 := Subgroup.orderOf_dvd_natCard _ hmem
      rw [hk'3] at h3
      have hcop := GL83.PiGen.coprime_card_glaPPrimeCore Nat.prime_three ↥J
      exact absurd (Nat.Coprime.coprime_dvd_right h3 hcop) (by norm_num)
    have hkb3 : orderOf kb = 3 := by
      refine orderOf_eq_prime ?_ hkb1
      rw [hkb, ← QuotientGroup.mk_pow, ← hk'3, pow_orderOf_eq_one, QuotientGroup.mk_one]
    have h3Z := Subgroup.orderOf_dvd_natCard _ hZ
    rw [hkb3] at h3Z
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot 3 J))
    have h2 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
    have h3 : Nat.card J ∣ Nat.card S := Subgroup.card_subgroup_dvd_card J
    refine Dvd.dvd.trans ?_ (h2.trans h3)
    rw [h1, mul_comm]
    exact Nat.mul_dvd_mul_left _ h3Z
  · have hN : Subgroup.zpowers k ≤ Subgroup.normalizer (J : Set S) := by
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have : k * g * k⁻¹ = g := by rw [← hkc g hg]; group
        rw [this]; exact hg
      · intro hg
        have hg' : k⁻¹ * (k * g * k⁻¹) * k ∈ J := by
          have hx := hkc _ hg
          have : k⁻¹ * (k * g * k⁻¹) * k = k * g * k⁻¹ := by
            calc k⁻¹ * (k * g * k⁻¹) * k = k⁻¹ * ((k * g * k⁻¹) * k) := by group
              _ = k⁻¹ * (k * (k * g * k⁻¹)) := by rw [hx]
              _ = k * g * k⁻¹ := by group
          rw [this]; exact hg
        have : k⁻¹ * (k * g * k⁻¹) * k = g := by group
        rwa [this] at hg'
    have hb : Subgroup.zpowers k ⊓ J = ⊥ := by
      have hd : Nat.card ↥(Subgroup.zpowers k ⊓ J) ∣ 3 := by
        rw [← hk, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact Subgroup.card_eq_one.1 h
      · exfalso
        have heq : Subgroup.zpowers k ⊓ J = Subgroup.zpowers k :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hk, h])
        exact hkJ ((heq ▸ inf_le_right : Subgroup.zpowers k ≤ J) (Subgroup.mem_zpowers k))
    have hc := CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.card_sup_of_inf_bot hN hb
    rw [Nat.card_zpowers, hk] at hc
    calc 3 * Nat.card (PSimple 3 J) ∣ 3 * Nat.card J := Nat.mul_dvd_mul_left 3 (card_pSimple_dvd 3 J)
      _ = Nat.card ↥(Subgroup.zpowers k ⊔ J) := hc.symm
      _ ∣ Nat.card S := Subgroup.card_subgroup_dvd_card _

theorem kdl227Row_of_not_dvd {s : TauCeti.SporadicName}
    (h : ¬ 9828 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group) : KDL227SporRow s := by
  intro S _ _ ⟨e⟩ β hβ hβ1 J hJ hL
  apply h
  rw [← Nat.card_congr e.toEquiv, ← card_of_catalogIs_L227 hL]
  exact (card_pSimple_dvd 3 J).trans (Subgroup.card_subgroup_dvd_card J)

theorem noL227At_of_card {Q : Type} [Group Q] [Finite Q] (h : ¬ 3 * 9828 ∣ Nat.card Q) :
    NoL227At Q := by
  intro k hk1 hk3 J hJ hL
  have hko : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  apply h
  rw [← card_of_catalogIs_L227 hL]
  exact three_mul_card_pSimple_dvd hko hJ.1

theorem kdl227Row_Ru
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDL227SporRow .Ru := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Ru) = 145926144000 :=
    CFSG.Sporadic.Ru.card_Ru
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ru) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ru) :=
    CFSG.Sporadic.Ru.isSimpleGroup_Ru
  exact kdl227Row_of_model hOut (hbr .Ru).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (noL227At_of_card (by rw [hc]; norm_num))

end CFSG.LocalAnalysis.GLTheoremA.KDL227Rows
