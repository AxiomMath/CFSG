module

public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicData
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.PGroupNormalE4
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointRankFour
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CoverSplit
public import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicRank
public import CFSG.Models.Transport
public import CFSG.HardMathSupport.Timmesfeld.LieRank.G2
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.Walter.Ree.Model.JTHyp

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open Subgroup

theorem nine_le_card_inf_centralizer {K : Type} [Group K] [Finite K] {E : Subgroup K}
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 4) {k : K}
    (hkn : k ∈ normalizer (E : Set K)) (hk3 : ∀ e ∈ E, k ^ 3 * e = e * k ^ 3) :
    9 ≤ Nat.card ↥(E ⊓ centralizer ({k} : Set K)) := by
  classical
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
  let α : E →* E := MonoidHom.mk' (fun e => ⟨k * e * k⁻¹, (mem_normalizer_iff.1 hkn e).1 e.2⟩)
    (by
      intro a b
      apply Subtype.ext
      simp [mul_assoc])
  have hα : ∀ e, α (α (α e)) = e := by
    intro e
    apply Subtype.ext
    change k * (k * (k * (e : K) * k⁻¹) * k⁻¹) * k⁻¹ = e
    have h1 : k * (k * (k * (e : K) * k⁻¹) * k⁻¹) * k⁻¹ =
        (k * (k * k)) * e * (k * (k * k))⁻¹ := by
      simp [mul_assoc]
    have h2 : k * (k * k) * (e : K) = e * (k * (k * k)) := by
      have := hk3 e e.2
      rwa [pow_three] at this
    rw [h1, h2]
    exact mul_inv_cancel_right _ _
  have h3 : ∀ y : E, y ^ 3 = 1 := fun y => Subtype.ext (by simpa using hE.2 y y.2)
  have h9 := CFSG.LocalAnalysis.RankFourTheoremC.nine_le_card_eqLocus (E := E) hEc h3 α hα
  refine h9.trans ?_
  calc Nat.card (MonoidHom.eqLocus α (MonoidHom.id E))
      = Nat.card ((MonoidHom.eqLocus α (MonoidHom.id E)).map E.subtype) :=
        (card_map_of_injective E.subtype_injective).symm
    _ ≤ Nat.card ↥(E ⊓ centralizer ({k} : Set K)) := by
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨f, hf, rfl⟩
      refine ⟨f.2, mem_centralizer_singleton_iff.2 ?_⟩
      have hf' : α f = f := hf
      have := congrArg Subtype.val hf'
      change k * (f : K) * k⁻¹ = f at this
      calc (f : K) * k = (k * (f : K) * k⁻¹) * k := by rw [this]
        _ = k * (f : K) := by group

theorem exists_cent_of_center_three {K : Type} [Group K] [Finite K]
    (hrk : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) (hZ : Nat.card (center K) = 3)
    {k : K} (hkZ : k ∉ center K) (hk3 : k ^ 3 ∈ center K) :
    ∃ x : K, x ^ 3 = 1 ∧ x * k = k * x ∧ x ∉ zpowers k ⊔ center K := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hZ3 : ∀ z ∈ center K, z ^ 3 = 1 := by
    intro z hz
    have h1 : (⟨z, hz⟩ : center K) ^ Nat.card (center K) = 1 := pow_card_eq_one'
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hk9 : k ^ 9 = 1 := by
    calc k ^ 9 = (k ^ 3) ^ 3 := by rw [← pow_mul]
      _ = 1 := hZ3 _ hk3
  have hpg : IsPGroup 3 (zpowers k) := by
    have hord : orderOf k ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hk9)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp3).1 hord
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  obtain ⟨P, hkP⟩ := hpg.exists_le_sylow
  have hP4 : 4 ≤ Open.pRank 3 (P : Subgroup K) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact hrk
  obtain ⟨E, hEP, hPn, hE, hEc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.gl83NormalElementaryRankFour_holds K
      (P : Subgroup K) P.isPGroup' hP4
  have hkP' : k ∈ (P : Subgroup K) := hkP (mem_zpowers k)
  have hkn : k ∈ normalizer (E : Set K) := hPn hkP'
  have hk3c : ∀ e ∈ E, k ^ 3 * e = e * k ^ 3 := fun e _ => ((mem_center_iff.1 hk3) e).symm
  have h9 := nine_le_card_inf_centralizer hE hEc hkn hk3c
  set C : Subgroup K := E ⊓ centralizer ({k} : Set K) with hC
  by_contra hno
  push Not at hno
  have hCM : ∀ c ∈ C, c ∈ zpowers k ⊔ center K := fun c hc =>
    hno c (hE.2 c hc.1) (mem_centralizer_singleton_iff.1 hc.2)
  have hkcomm : ∀ e ∈ center K, e * k = k * e := fun e he => (mem_center_iff.1 he k).symm
  by_cases hk1 : k ^ 3 = 1
  ·
    have hMcard : Nat.card ↥(center K ⊔ zpowers k) = 9 := by
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp3 (center K) hk1 hkZ hkcomm, hZ]
    by_cases hkE : k ∈ E
    · have hEM : E ≤ center K ⊔ zpowers k := by
        intro e he
        rw [sup_comm]
        exact hno e (hE.2 e he) (congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨k, hkE⟩))
      have := Subgroup.card_le_of_le hEM
      rw [hMcard, hEc] at this
      omega
    · have hkC : k ∉ C := fun h => hkE h.1
      have hCcomm : ∀ e ∈ C, e * k = k * e := fun e he => mem_centralizer_singleton_iff.1 he.2
      have hYcard : Nat.card ↥(C ⊔ zpowers k) = Nat.card C * 3 :=
        CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp3 C hk1 hkC hCcomm
      haveI hCe : CFSG.IsElementaryAbelian 3 C :=
        CFSG.IsElementaryAbelian.of_le
          ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE) inf_le_left
      haveI hke : CFSG.IsElementaryAbelian 3 (zpowers k) :=
        CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hk1
      have hle : zpowers k ≤ centralizer (C : Set K) := by
        rw [zpowers_le]
        exact mem_centralizer_iff.2 fun c hc => hCcomm c hc
      have hY := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
        (CFSG.IsElementaryAbelian.sup_of_le_centralizer hle)
      have hYM : C ⊔ zpowers k ≤ center K ⊔ zpowers k := by
        intro y hy
        have hyk : k ∈ C ⊔ zpowers k := mem_sup_right (mem_zpowers k)
        rw [sup_comm]
        exact hno y (hY.2 y hy) (congrArg Subtype.val (hY.1.is_comm.comm ⟨y, hy⟩ ⟨k, hyk⟩))
      have := Subgroup.card_le_of_le hYM
      rw [hMcard, hYcard] at this
      omega
  ·
    have hzo : orderOf (k ^ 3) = 3 := orderOf_eq_prime (hZ3 _ hk3) hk1
    have hzp : zpowers (k ^ 3) ≤ center K := zpowers_le.2 hk3
    have hzc : Nat.card (zpowers (k ^ 3)) = Nat.card (center K) := by
      rw [Nat.card_zpowers, hzo, hZ]
    have heq : zpowers (k ^ 3) = center K :=
      Subgroup.eq_of_le_of_card_ge hzp (by rw [hzc])
    have hZk : center K ≤ zpowers k := by
      rw [← heq, zpowers_le]
      exact pow_mem (mem_zpowers k) 3
    have hCk : C ≤ zpowers k := fun c hc => by
      have := hCM c hc
      rwa [sup_eq_left.2 hZk] at this
    haveI : IsCyclic ↥C := Subgroup.isCyclic_of_le hCk
    have hexp : Monoid.exponent ↥C = Nat.card C := IsCyclic.exponent_eq_card
    have hdvd : Monoid.exponent ↥C ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hE.2 x x.2.1)
    rw [hexp] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega


section Table

open CFSG.Assembly.LowTwoRank CFSG.Models TauCeti
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem not_dvd_pow_sub_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) : ¬ p ∣ p ^ f - 1 := by
  intro h
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at this
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)

theorem not_dvd_pow_add_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) : ¬ p ∣ p ^ f + 1 := by
  intro h
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have := Nat.dvd_sub h h1
  rw [Nat.add_sub_cancel_left] at this
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)

theorem table_step (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    {n f : ℕ} (hm : LieModel (K ⧸ Subgroup.center K) t n p f) (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    p = 3 ∧ ((t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1)) := by
  have hdvd := center_dvd_table hGA (isQuasisimple_of_open' hq) (MulEquiv.refl _) hm
  have hf : 1 ≤ f := hm.1.2.1
  rcases case_of_dvd_table hp hp2 (hpZ.trans hdvd) with ⟨-, hd⟩ | ⟨-, hd⟩ |
    ⟨⟨-, hp3, hd⟩ | ⟨-, hp3, hd⟩⟩ | ⟨hp3, hcases⟩
  · exact absurd (hd.trans (Nat.gcd_dvd_right _ _)) (not_dvd_pow_sub_one hp hf)
  · exact absurd (hd.trans (Nat.gcd_dvd_right _ _)) (not_dvd_pow_add_one hp hf)
  · subst hp3; exact absurd hd (not_dvd_pow_sub_one hp hf)
  · subst hp3; exact absurd hd (not_dvd_pow_add_one hp hf)
  · refine ⟨hp3, ?_⟩
    rcases hcases with ⟨ht, hn, -, hf2⟩ | ⟨ht, hn, -, hf2⟩ | ⟨ht, hn, -, hf2⟩ | ⟨ht, hn, -, hf2⟩
    · exact Or.inl ⟨ht, hn, hf2⟩
    · exact Or.inr (Or.inl ⟨ht, hn, hf2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨ht, hn, hf2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ht, hn, hf2⟩))

theorem center_shape (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (d : ValidLieTypeIndex) (hchar : d.1.characteristic = p)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    p = 3 ∧
      (StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 4 3 1 ∨
        StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaOdd 3 3 1 ∨
        (LieModel (K ⧸ Subgroup.center K) .G2 0 3 1 ∧
          ∃ (q : PrimePower) (d' : ValidLieTypeIndex), q.card = 3 ∧ d'.1 = LieTypeIndex.G2 q ∧
            Nonempty ((K ⧸ Subgroup.center K) ≃* (CFSGIndex.lie d').Group))) := by
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have dead : ∀ {t : StatedLieTag} {n f : ℕ}, LieModel (K ⧸ Subgroup.center K) t n p f →
      t ≠ .PSL → t ≠ .POmegaOdd → t ≠ .G2 → t ≠ .PSU → False := by
    intro t n f hm h1 h2 h3 h4
    rcases (table_step hGA hq hp hp2 hm hpZ).2 with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
    · exact h1 ht
    · exact h2 ht
    · exact h3 ht
    · exact h4 ht
  cases d with
  | A r q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    have hm := (lieModel_typeA r q hv).of_mulEquiv e.symm
    obtain ⟨hp3, h⟩ := table_step hGA hq hp hp2 hm hpZ
    rcases h with ⟨-, hn, hf⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
    · exfalso
      have hr : r = 1 := by omega
      subst hr
      have hcard : q.card = 9 := by rw [PrimePower.card_def, hp3, hf]; norm_num
      exact ((LieTypeIndex.valid_iff _).1 hv).2 ((LieTypeIndex.isDuplicateRepresentative_iff _).2
        (Or.inl ⟨rfl, Or.inr (Or.inr hcard)⟩))
    all_goals exact absurd ht (by decide)
  | twistedA r q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    obtain ⟨hp3, h⟩ := table_step hGA hq hp hp2 (lieModel_of_classical hc) hpZ
    rcases h with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, hn, hf⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · refine ⟨hp3, Or.inl ?_⟩
      have hr : r = 3 := by omega
      subst hr
      rw [hp3, hf] at hc
      exact hc
  | B r q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    have hr2 : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact (dead (lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e))
        (by decide) (by decide) (by decide) (by decide)).elim
    · have hc := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr3 e
      obtain ⟨hp3, h⟩ := table_step hGA hq hp hp2 (lieModel_of_classical hc) hpZ
      rcases h with ⟨ht, -⟩ | ⟨-, hn, hf⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
      · exact absurd ht (by decide)
      · refine ⟨hp3, Or.inr (Or.inl ?_)⟩
        subst hn
        rw [hp3, hf] at hc
        exact hc
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
  | C r q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    exact (dead (lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e))
      (by decide) (by decide) (by decide) (by decide)).elim
  | D r q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    exact (dead (lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e))
      (by decide) (by decide) (by decide) (by decide)).elim
  | twistedD r q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    exact (dead (lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e))
      (by decide) (by decide) (by decide) (by decide)).elim
  | E6 q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    exact (dead ((lieModel_lie (t := .E6) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩
      ⟨rfl, rfl⟩).of_mulEquiv e.symm) (by decide) (by decide) (by decide) (by decide)).elim
  | E7 q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    exact (dead ((lieModel_lie (t := .E7) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩
      ⟨rfl, rfl⟩).of_mulEquiv e.symm) (by decide) (by decide) (by decide) (by decide)).elim
  | E8 q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    exact (dead ((lieModel_lie (t := .E8) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩
      ⟨rfl, rfl⟩).of_mulEquiv e.symm) (by decide) (by decide) (by decide) (by decide)).elim
  | F4 q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    exact (dead ((lieModel_lie (t := .F4) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩
      ⟨rfl, rfl⟩).of_mulEquiv e.symm) (by decide) (by decide) (by decide) (by decide)).elim
  | G2 q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [PrimePower.card_def] using hrange
    have hm := (lieModel_lie (t := .G2) ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩ ⟨.G2 q, hv⟩
      ⟨rfl, rfl⟩).of_mulEquiv e.symm
    obtain ⟨hp3, h⟩ := table_step hGA hq hp hp2 hm hpZ
    rcases h with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, -, hf⟩ | ⟨ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · refine ⟨hp3, Or.inr (Or.inr ?_)⟩
      rw [hp3, hf] at hm
      refine ⟨hm, q, ⟨.G2 q, hv⟩, ?_, rfl, ⟨e⟩⟩
      rw [PrimePower.card_def, hp3, hf]
      norm_num
    · exact absurd ht (by decide)
  | twistedE6 q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    exact (dead ((lieModel_lie (t := .twistedE6) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩).of_mulEquiv e.symm)
      (by decide) (by decide) (by decide) (by decide)).elim
  | trialityD4 q =>
    have hqp : q.p = p := by simpa using hchar
    subst hqp
    exact (dead ((lieModel_lie (t := .trialityD4) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩).of_mulEquiv e.symm)
      (by decide) (by decide) (by decide) (by decide)).elim
  | suzuki m => exact (hp2 (by simpa using hchar.symm)).elim
  | reeG2 m =>
    have hp3 : p = 3 := by simpa using hchar.symm
    subst hp3
    have hm1 : 1 ≤ m := hrange
    exact (dead ((lieModel_lie (t := .twistedG2) (p := 3) (f := 2 * m + 1)
      ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩
      ⟨rfl, rfl⟩).of_mulEquiv e.symm) (by decide) (by decide) (by decide) (by decide)).elim
  | reeF4 m => exact (hp2 (by simpa using hchar.symm)).elim
  | tits => exact (hp2 (by simpa using hchar.symm)).elim

end Table

section Rank

open CFSG.HardMathSupport.Timmesfeld.LieRank CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem exponent_le_of_dvd {j N e : ℕ} (hdvd : 3 ^ j ∣ N) (hnd : ¬ 3 ^ (e + 1) ∣ N) :
    j ≤ e := by
  by_contra h
  exact hnd ((pow_dvd_pow 3 (by omega : e + 1 ≤ j)).trans hdvd)

theorem u43_center (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hc : StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 4 3 1)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥) :
    (Nat.card (Subgroup.center K) = 3 ∧ 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) ∨
      (Nat.card (Subgroup.center K) = 9 ∧ (∀ z ∈ Subgroup.center K, z ^ 3 = 1) ∧
        Nonempty (K ⧸ Subgroup.center K ≃* CFSG.LieType.Multipliers.U43.X₀)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd := center_dvd_table hGA (isQuasisimple_of_open' hq) (MulEquiv.refl _)
    (lieModel_of_classical hc)
  have h36 : (genericOrders .PSU 4 3 1).1 * (genericOrders .PSU 4 3 1).2 *
      ((exceptionalOrders .PSU 4 3 1).1 * (exceptionalOrders .PSU 4 3 1).2) = 36 := by
    norm_num [genericOrders, exceptionalOrders]
  rw [h36] at hdvd
  obtain ⟨j, hj⟩ := hZp.exists_card_eq
  have hj0 : j ≠ 0 := fun h => hZ (Subgroup.card_eq_one.1 (by rw [hj, h, pow_zero]))
  have hj2 : j ≤ 2 := exponent_le_of_dvd (N := 36) (e := 2) (hj ▸ hdvd) (by norm_num)
  have hB : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU 4 3 1 := Or.inl ⟨by decide, hc⟩
  obtain ⟨e₀⟩ := nonempty_mulEquiv_X₀_of_lieModel hB
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj0
  interval_cases j
  · left
    refine ⟨by rw [hj]; norm_num, ?_⟩
    have h3 : 3 ∣ Nat.card (Subgroup.center K) := by rw [hj]; norm_num
    have h1 := pRank_quotient_le_of_cover_U43 e₀ h3
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) := by
      obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (by norm_num) hc
      rcases hr with ⟨h, -⟩ | ⟨-, ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | h
      · exact absurd h (by decide)
      · exact absurd h (by norm_num)
      · exact h
      · exact absurd h (by decide)
      · exact h
    omega
  · right
    have hZ9 : Nat.card (Subgroup.center K) = 9 := by rw [hj]; norm_num
    refine ⟨hZ9, fun z hz => ?_, ⟨e₀⟩⟩
    have h12 : (⟨z, hz⟩ : Subgroup.center K) ^ 12 = 1 := by
      have := center_pow_lcm hGA hq (MulEquiv.refl _) (lieModel_of_classical hc) ⟨z, hz⟩
      have hl : Nat.lcm (genericOrders .PSU 4 3 1).1 12 = 12 := by
        norm_num [genericOrders]
      rwa [hl] at this
    have h9 : (⟨z, hz⟩ : Subgroup.center K) ^ 9 = 1 := by
      rw [← hZ9]
      exact pow_card_eq_one'
    have h3 := pow_gcd_eq_one.2 ⟨h12, h9⟩
    rw [show Nat.gcd 12 9 = 3 by norm_num] at h3
    exact congrArg Subtype.val h3

theorem o73_center (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K)
    (hc : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaOdd 3 3 1)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥) :
    Nat.card (Subgroup.center K) = 3 ∧ 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd := center_dvd_table hGA (isQuasisimple_of_open' hq) (MulEquiv.refl _)
    (lieModel_of_classical hc)
  have h6 : (genericOrders .POmegaOdd 3 3 1).1 * (genericOrders .POmegaOdd 3 3 1).2 *
      ((exceptionalOrders .POmegaOdd 3 3 1).1 * (exceptionalOrders .POmegaOdd 3 3 1).2) = 6 := by
    norm_num [genericOrders, exceptionalOrders]
  rw [h6] at hdvd
  obtain ⟨j, hj⟩ := hZp.exists_card_eq
  have hj0 : j ≠ 0 := fun h => hZ (Subgroup.card_eq_one.1 (by rw [hj, h, pow_zero]))
  have hj1 : j ≤ 1 := exponent_le_of_dvd (N := 6) (e := 1) (hj ▸ hdvd) (by norm_num)
  have hj1' : j = 1 := by omega
  subst hj1'
  have hZ3 : Nat.card (Subgroup.center K) = 3 := by rw [hj]; norm_num
  refine ⟨hZ3, ?_⟩
  have hB : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaOdd 3 3 1 :=
    Or.inl ⟨by decide, hc⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_openOmega_of_lieModel hB
  have h3 : 3 ∣ Nat.card (Subgroup.center K) := by rw [hZ3]
  have h1 := O7.pRank_quotient_le_of_cover_O7 hq e h3 (by rw [hZ3]; norm_num)
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) := by
    obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (by norm_num) hc
    rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  omega

end Rank

section G2Rank

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U CFSG.Assembly.LowTwoRank CFSG.Models TauCeti
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.Blueprint.Multiplier CFSG.HardMathSupport.Timmesfeld.LieRank


theorem g23_center (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hm : LieModel (K ⧸ Subgroup.center K) .G2 0 3 1)
    (hsh : ∃ (q : PrimePower) (d : ValidLieTypeIndex), q.card = 3 ∧ d.1 = LieTypeIndex.G2 q ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (CFSGIndex.lie d).Group))
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥) :
    Nat.card (Subgroup.center K) = 3 ∧ 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd := center_dvd_table hGA (isQuasisimple_of_open' hq) (MulEquiv.refl _) hm
  have h3' : (genericOrders .G2 0 3 1).1 * (genericOrders .G2 0 3 1).2 *
      ((exceptionalOrders .G2 0 3 1).1 * (exceptionalOrders .G2 0 3 1).2) = 3 := by
    norm_num [genericOrders, exceptionalOrders]
  rw [h3'] at hdvd
  obtain ⟨j, hj⟩ := hZp.exists_card_eq
  have hj0 : j ≠ 0 := fun h => hZ (Subgroup.card_eq_one.1 (by rw [hj, h, pow_zero]))
  have hj1 : j ≤ 1 := exponent_le_of_dvd (N := 3) (e := 1) (hj ▸ hdvd) (by norm_num)
  have hj1' : j = 1 := by omega
  subst hj1'
  have hZ3 : Nat.card (Subgroup.center K) = 3 := by rw [hj]; norm_num
  refine ⟨hZ3, ?_⟩
  obtain ⟨q, d, hq3, hd, ⟨e⟩⟩ := hsh
  have hqcard : q.p ^ q.exponent = 3 := by rwa [PrimePower.card_def] at hq3
  obtain ⟨hp3, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).1 hqcard
  obtain ⟨d1, hv⟩ := d
  have hd1 : d1 = LieTypeIndex.G2 q := hd
  subst hd1
  have hCh := CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_three q hv hp3 hf1
  have hCh' := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hCh
  have hB : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .G2 0 3 1 :=
    Or.inr (Or.inl ⟨rfl, by decide, hCh'⟩)
  obtain ⟨eA⟩ := nonempty_mulEquiv_adjointGroup_G2_of_lieModel hB
  obtain ⟨e', -⟩ : ∃ e' : K ⧸ Subgroup.center K ≃* RG, True :=
    ⟨eA.trans (Subgroup.equivMapOfInjective _ (glHom (RingEquiv.refl (ZMod 3)))
      (glHom_injective _)), trivial⟩
  have h3 : 3 ∣ Nat.card (Subgroup.center K) := by rw [hZ3]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center K)) 3 h3
  have hzL : orderOf (z : K) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  let φ : K →* RG :=
    (e' : K ⧸ Subgroup.center K →* RG).comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := by
    ext x
    simp [φ]
  exact four_le_pRank_of_cover_RG φ hφ hker.le (z := (z : K)) (by rw [hker]; exact z.2) hzL

end G2Rank

@[expose] def KDU43NineFold : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Nonempty (K ⧸ Subgroup.center K ≃* CFSG.LieType.Multipliers.U43.X₀) →
      Nat.card (Subgroup.center K) = 9 → (∀ z ∈ Subgroup.center K, z ^ 3 = 1) →
        ∀ k : K, k ∉ Subgroup.center K → k ^ 3 ∈ Subgroup.center K →
          ∃ x : K, x ^ 3 = 1 ∧ x * k = k * x ∧ x ∉ Subgroup.zpowers k ⊔ Subgroup.center K

section Assembly

open CFSG.Assembly.LowTwoRank CFSG.Models TauCeti


theorem kdCenterCase_of_nineFold (hGA : GriessAllModelsStatement) (hNine : KDU43NineFold) :
    KDCenterCase := by
  intro p hp hp2 K _ _ hq hL hZp hZ k hkZ hkp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨idx, ⟨e⟩, hchar⟩ := hL
  have hpZ : p ∣ Nat.card (Subgroup.center K) := by
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.1 (by simpa using hn)) hZ
    · rw [hn]
      exact dvd_pow_self p (Nat.succ_ne_zero n)
  obtain ⟨rfl, hcases⟩ := center_shape hGA hq hp hp2 idx hchar e hpZ
  rcases hcases with hU | hO | ⟨hG, hsh⟩
  · rcases u43_center hGA hq hU hZp hZ with ⟨hZ3, hrk⟩ | ⟨hZ9, hZe, hX⟩
    · exact exists_cent_of_center_three hrk hZ3 hkZ hkp
    · exact hNine K hq hX hZ9 hZe k hkZ hkp
  · obtain ⟨hZ3, hrk⟩ := o73_center hGA hq hO hZp hZ
    exact exists_cent_of_center_three hrk hZ3 hkZ hkp
  · obtain ⟨hZ3, hrk⟩ := g23_center hGA hq hG hsh hZp hZ
    exact exists_cent_of_center_three hrk hZ3 hkZ hkp

end Assembly

end CFSG.HardMathSupport.Dickson.I271
