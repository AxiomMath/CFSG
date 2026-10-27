module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711d
public import CFSG.Walter.W67.W1Basic
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentRes
public import CFSG.RankThree.Native.HSMcLFiveCentralizers
public import CFSG.RankThree.Native.HSMcLSmall
public import CFSG.HardMathSupport.Dickson.BMRows.Types
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo2
public import CFSG.Monster.B.Pinned.Primes.FiveRelations
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenEmb
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenQ
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenZCent
public import CFSG.RankThree.PartOne.KS.HeSevenCentralizers
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenShape
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM7
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzQuasi
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Shape
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.Sporadic.Co2Smith.GlC0JankoA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeFinal
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeMoore
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeALeech
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24LeafShape
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi24
public import CFSG.RankThree.Asc83Table.J3
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicRankData
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveHN
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveShape
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7
public import Certificates.Data.TabCo1ThreeE

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711d

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

section FullRank

theorem false_of_nonabelian_sylow {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {C A R : Subgroup Q} (hAC : A ≤ C) (hA : IsElemAbelian p A) (hA4 : p ^ 4 ≤ Nat.card A)
    (hC5 : ¬ p ^ 5 ∣ Nat.card C) (hRC : R ≤ C) (hR : IsPGroup p R)
    (hRnc : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hA
  have hk4 : 4 ≤ k := by
    rw [hk] at hA4
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hA4
  have hdvd : p ^ k ∣ Nat.card C := hk ▸ Subgroup.card_dvd_of_le hAC
  have hk5 : k = 4 := by
    by_contra h
    exact hC5 ((Nat.pow_dvd_pow p (by omega)).trans hdvd)
  subst hk5
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hf4 : 4 ≤ (Nat.card C).factorization p := (hp.pow_dvd_iff_le_factorization hC0).1 hdvd
  have hf5 : ¬ 5 ≤ (Nat.card C).factorization p := fun h =>
    hC5 ((hp.pow_dvd_iff_le_factorization hC0).2 h)
  have hfac : Nat.card A = p ^ (Nat.card C).factorization p := by
    rw [hk]
    congr 1
    omega
  obtain ⟨g, -, hg⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Co2Spor.exists_conj_le_of_full hAC hfac hRC hR
  obtain ⟨a, ha, b, hb, hab⟩ := hRnc
  apply hab
  have h1 := isElemAbelian_commute hA (hg a ha) (hg b hb)
  have h2 : g⁻¹ * (a * b) * g = g⁻¹ * (b * a) * g := by
    calc g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
      _ = (g⁻¹ * b * g) * (g⁻¹ * a * g) := h1
      _ = g⁻¹ * (b * a) * g := by group
  have h3 := congrArg (fun x => g * x * g⁻¹) h2
  simpa [mul_assoc] using h3

@[expose] def FullRankBound (p : ℕ) (Q : Type) [Group Q] : Prop :=
  ∀ x : Q, x ≠ 1 → x ^ p = 1 →
    (∃ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) I) →
      ¬ p ^ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set Q)) ∧
        ∃ R : Subgroup Q, R ≤ Subgroup.centralizer ({x} : Set Q) ∧ IsPGroup p R ∧
          ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a

theorem FullRankBound.of_equiv {p : ℕ} (hp : p.Prime) {Q Q' : Type} [Group Q] [Finite Q] [Group Q']
    [Finite Q'] (e : Q ≃* Q') (h : FullRankBound p Q) : FullRankBound p Q' := by
  intro x' hx1 hxp hI
  set x := e.symm x' with hx
  have hmap : (Subgroup.centralizer ({x} : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ({x'} : Set Q') := by
    rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton e x, hx, e.apply_symm_apply]
  have hmap' : (Subgroup.centralizer ({x'} : Set Q')).map e.symm.toMonoidHom =
      Subgroup.centralizer ({x} : Set Q) := by
    rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton e.symm x']
  have h1 : x ≠ 1 := fun h1 => hx1 (by rw [← e.apply_symm_apply x', ← hx, h1, map_one])
  have h2 : x ^ p = 1 := by rw [hx, ← map_pow, hxp, map_one]
  obtain ⟨I, hI⟩ := hI
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp e.symm hI
  rw [hmap'] at hI'
  obtain ⟨h5, R, hR, hRp, a, ha, b, hb, hab⟩ := h x h1 h2 ⟨_, hI'⟩
  refine ⟨?_, R.map e.toMonoidHom, ?_, hRp.map _, e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, ?_⟩
  · rw [← hmap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact h5
  · rw [← hmap]
    exact Subgroup.map_mono hR
  · rw [← map_mul, ← map_mul]
    exact fun h => hab (e.injective h)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem exists_mem_B0 (hp : p.Prime) {L B E : Subgroup X} (hB : IsElemAbelian p B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) (hEB : E ≤ B)
    (hE2 : 2 ≤ CFSG.Open.pRank p E) (hC1 : CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1)
    (hle : ∀ e ∈ E, GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥)
    (hB4 : 4 ≤ CFSG.Open.pRank p B) {Q : Type} [Group Q] [Finite Q]
    (σ : (↥L ⧸ Subgroup.center ↥L) ≃* Q) (hQ : FullRankBound p Q) :
    ∃ z ∈ B ⊓ Subgroup.centralizer (L : Set X), z ≠ 1 := by
  by_contra hno
  push Not at hno
  obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
  set b : ↥B := ⟨e, hEB he⟩ with hb
  set t := barHom hin b with ht
  have hmap := CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton σ t
  have hx1 : σ t ≠ 1 := fun h =>
    heC ((barHom_eq_one_iff hin b).1 (σ.injective (h.trans (map_one σ).symm)))
  have hxp : σ t ^ p = 1 := by
    rw [← map_pow, (isElemAbelian_range_barHom hB hin).2 _ ⟨b, rfl⟩, map_one]
  obtain ⟨I, hI⟩ := exists_glaPComponent_barHom hp hin b (hle e he)
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ hI
  rw [hmap] at hI'
  obtain ⟨h5, R, hRC, hRp, hRnc⟩ := hQ (σ t) hx1 hxp ⟨_, hI'⟩
  set A : Subgroup Q := (barHom hin).range.map σ.toMonoidHom with hA
  have hAel : IsElemAbelian p A :=
    CFSG.SectionRank.isElemAbelian_map (isElemAbelian_range_barHom hB hin) _
  have hAC : A ≤ Subgroup.centralizer ({σ t} : Set Q) := by
    rw [← hmap]
    exact Subgroup.map_mono (range_barHom_le_centralizer hB hin b)
  have hB0 : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) = 1 := by
    rw [Subgroup.card_eq_one]
    exact eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (hno z hz)
  have hcard : Nat.card A = Nat.card B := by
    have h1 := card_range_barHom_mul hin
    rw [hB0, mul_one] at h1
    rw [hA, Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective, h1]
  have hA4 : p ^ 4 ≤ Nat.card A := by
    rw [hcard, Inputs27.card_eq_pow_pRank hp hB]
    exact Nat.pow_le_pow_right hp.pos hB4
  exact false_of_nonabelian_sylow hp hAC hAel hA4 h5 hRC hRp hRnc

theorem inf_centralizer_sup_eq {L : Subgroup X} {e z : X}
    (hz : z ∈ Subgroup.centralizer (L : Set X)) :
    L ⊓ Subgroup.centralizer ((Subgroup.zpowers e ⊔ Subgroup.zpowers z : Subgroup X) : Set X) =
      L ⊓ Subgroup.centralizer ((Subgroup.zpowers e : Subgroup X) : Set X) := by
  apply le_antisymm
  · exact inf_le_inf_left L (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
  · intro y hy
    obtain ⟨hyL, hy⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨hyL, ?_⟩
    have h1 : Subgroup.zpowers e ≤ Subgroup.centralizer ({y} : Set X) := by
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_iff.1 hy w hw
      exact this
    have h2 : Subgroup.zpowers z ≤ Subgroup.centralizer ({y} : Set X) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_iff.1 hz y hyL
      exact this.symm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := Subgroup.mem_centralizer_singleton_iff.1 (sup_le h1 h2 hw)
    exact this

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)


theorem exists_jD_one (hp : p.Prime) (hp2 : p ≠ 2) (h183 : Input18_3_4)
    (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p 2)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) {name : TauCeti.SporadicName} (hpS : p ∣ sporOrd name)
    (h12 : ¬ sporOrd name ∣ Nat.factorial 12)
    {L B J0 E : Subgroup X} (hLK : CFSG.IsKGroup ↥L) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hname : IsSporType name (↥L ⧸ Subgroup.center ↥L))
    (hJ0 : CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      L ⊓ Subgroup.normalizer (U : Set X))) (hJt : Inputs2711c.J0Type p ↥J0) (hEB : E ≤ B)
    (hEC : B ⊓ Subgroup.centralizer (L : Set X) ≤ E)
    (hEl : GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥)
    {e z : X} (he : e ∈ E) (heC : e ∉ Subgroup.centralizer (L : Set X))
    (hz : z ∈ B ⊓ Subgroup.centralizer (L : Set X)) (hz1 : z ≠ 1) :
    ∃ J : Subgroup X,
      GLAPComponent p (L ⊓ Subgroup.centralizer ((Subgroup.zpowers e : Subgroup X) : Set X)) J ∧
      ((Inputs2711c.AltOrChevTwo (PSimple p J) ∧ ¬ sporOrd name ∣ Nat.card (PSimple p J)) ∨
        (Nat.card (PSimple p J) ∣ 720 ∨ Nat.card (PSimple p J) ∣ 20160 ∨
          Nat.card (PSimple p J) ∣ 25920 ∨ Nat.card (PSimple p J) ∣ 60)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEel : IsElemAbelian p E := isElemAbelian_mono hB hEB
  have hzE : z ∈ E := hEC hz
  set D : Subgroup X := Subgroup.zpowers e ⊔ Subgroup.zpowers z with hD
  have hDE : D ≤ E := sup_le (Subgroup.zpowers_le.2 he) (Subgroup.zpowers_le.2 hzE)
  have hDel : IsElemAbelian p D := isElemAbelian_mono hEel hDE
  have he1 : e ≠ 1 := fun h => heC (h ▸ Subgroup.one_mem _)
  have hord : ∀ {w : X}, w ∈ E → w ≠ 1 → Nat.card (Subgroup.zpowers w) = p := fun hw hw1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hEel.2 _ hw) hw1
  have hinf : Subgroup.zpowers e ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro w ⟨hwe, hwz⟩
    rw [Subgroup.mem_bot]
    by_contra hw1
    have hwE : w ∈ E := Subgroup.zpowers_le.2 he hwe
    have h1 : Subgroup.zpowers w = Subgroup.zpowers e :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hwe)
        (by rw [hord he he1, hord hwE hw1])
    have h3 : Subgroup.zpowers e ≤ Subgroup.zpowers z := h1 ▸ Subgroup.zpowers_le.2 hwz
    exact heC (Subgroup.zpowers_le.2 hz.2 (h3 (Subgroup.mem_zpowers e)))
  have hcomm : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := fun a ha b hb =>
    isElemAbelian_commute hEel (Subgroup.zpowers_le.2 he ha) (Subgroup.zpowers_le.2 hzE hb)
  have hDc : Nat.card D = p ^ 2 := by
    have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute _ _ hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, hord he he1, hord hzE hz1] at h
    rw [hD, h, sq]
  have hD2r : 2 ≤ CFSG.Open.pRank p D := (pRank_eq_two hp hDel hDc).ge
  have hDC : ¬ D ≤ Subgroup.centralizer (L : Set X) := fun h =>
    heC (h (Subgroup.mem_sup_left (Subgroup.mem_zpowers e)))
  obtain ⟨J, hJ, hJalt⟩ := exists_jD hp hp2 h183 hD2 hSpM hOrd hpS h12 hLK hLq hB hBN hname hJ0 hJt
    hEB hEl hDE hD2r hDC
  rw [inf_centralizer_sup_eq hz.2] at hJ
  exact ⟨J, hJ, hJalt⟩

end FullRank

section ConjHelpers

theorem centralizer_conj_eq' {P : Type} [Group P] (g x : P) :
    Subgroup.centralizer ({g * x * g⁻¹} : Set P) =
      (Subgroup.centralizer ({x} : Set P)).map (MulAut.conj g).toMonoidHom :=
  (CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton (MulAut.conj g) x).symm

theorem conj_comm_iff {P : Type} [Group P] (g a b : P) :
    (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) ↔ a * b = b * a := by
  constructor
  · intro h
    have h1 := congrArg (fun x => g⁻¹ * x * g) h
    have e1 : g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g = a * b := by group
    have e2 : g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g = b * a := by group
    rw [e1, e2] at h1
    exact h1
  · intro h
    calc (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [h]
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group

theorem exists_nonabelian_of_equiv {G H : Type} [Group G] [Group H] {E : Subgroup G}
    {P A : Subgroup H} (φ : ↥E ≃* ↥P) (hAP : A ≤ P) {p n : ℕ} [Fact p.Prime]
    (hAc : Nat.card A = p ^ n) (hnc : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a) :
    ∃ R : Subgroup G, R ≤ E ∧ IsPGroup p R ∧ ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  refine ⟨((A.subgroupOf P).map φ.symm.toMonoidHom).map E.subtype, ?_, ?_, _,
    ⟨φ.symm ⟨a, hAP ha⟩, ⟨⟨a, hAP ha⟩, ha, rfl⟩, rfl⟩, _,
    ⟨φ.symm ⟨b, hAP hb⟩, ⟨⟨b, hAP hb⟩, hb, rfl⟩, rfl⟩, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · refine IsPGroup.of_card (n := n) ?_
    rw [Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.card_map_of_injective (f := φ.symm.toMonoidHom) φ.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAc]
  · intro h
    apply hab
    have h3 : φ.symm (⟨a, hAP ha⟩ * ⟨b, hAP hb⟩) = φ.symm (⟨b, hAP hb⟩ * ⟨a, hAP ha⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h
    have h4 := φ.symm.injective h3
    exact congrArg Subtype.val h4

theorem nonabelian_conj {P : Type} [Group P] {p : ℕ} {C R : Subgroup P} (g : P) (hRC : R ≤ C)
    (hR : IsPGroup p R) (hnc : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) :
    ∃ R' : Subgroup P, R' ≤ C.map (MulAut.conj g).toMonoidHom ∧ IsPGroup p R' ∧
      ∃ a ∈ R', ∃ b ∈ R', a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  refine ⟨R.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hRC, hR.map _, _, ⟨a, ha, rfl⟩, _,
    ⟨b, hb, rfl⟩, ?_⟩
  intro h
  apply hab
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  exact (conj_comm_iff g a b).1 h

theorem map_symm_map {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (X : Subgroup Q) :
    (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩

end ConjHelpers

section PairB5

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (sFiveA orderOf_sFiveA)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Dickson.BMRows (PCompCensus)
open CFSG.RankThree.Native (hs100P hs100FiveA23 hs100FiveC23 hs100Equiv card_hs100P)
open CFSG.Monster.B.Pinned (zFive)

theorem exists_nonabelian_five_hs100P :
    hs100FiveA23 ≤ hs100P ∧ Nat.card hs100FiveA23 = 125 ∧
      ∃ a ∈ hs100FiveA23, ∃ b ∈ hs100FiveA23, a * b ≠ b * a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨hAC, -, hAP, hAc, -, hcent, -⟩, -⟩ :=
    CFSG.RankThree.Native.R3E_HS_full_five_centralizer_structures
  refine ⟨hAP, hAc, ?_⟩
  by_contra hno
  push Not at hno
  have hle : hs100FiveA23 ≤
      Subgroup.centralizer (hs100FiveA23 : Set (Equiv.Perm (Fin 100))) ⊓ hs100FiveC23 :=
    le_inf (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => hno b hb a ha) hAC
  have := Subgroup.card_le_of_le hle
  rw [hAc, hcent] at this
  norm_num at this

theorem fullRankBound_B_five
    (hconj : ∀ y : NativeSporadic.B, orderOf y = 5 → ∃ c : ℕ, ¬ 5 ∣ c ∧
      ∃ g : NativeSporadic.B, g * zFive ^ c * g⁻¹ = y ∨ g * sFiveA ^ c * g⁻¹ = y)
    (hNC : TabBFiveBNoComp) (hA : TabBFiveACard) (hHS : TabBFiveAHS) :
    FullRankBound 5 NativeSporadic.B := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro y hy1 hy5 hI
  have hord : orderOf y = 5 := orderOf_eq_prime hy5 hy1
  obtain ⟨c, hc, g, hg | hg⟩ := hconj y hord
  · exfalso
    obtain ⟨I, hI⟩ := hI
    have hC : Subgroup.centralizer ({y} : Set NativeSporadic.B) =
        (Subgroup.centralizer ({zFive} : Set NativeSporadic.B)).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, centralizer_conj_eq',
        CFSG.HardMathSupport.Dickson.I271.TabMFive.centralizer_pow_eq_of_five
          CFSG.Monster.B.Pinned.orderOf_zFive hc]
    rw [hC] at hI
    have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv (by norm_num)
      (MulAut.conj g).symm hI
    rw [map_symm_map] at hI'
    exact hNC _ hI'
  · obtain ⟨E, hEC, ⟨eE⟩⟩ := hHS
    have hC : Subgroup.centralizer ({y} : Set NativeSporadic.B) =
        (Subgroup.centralizer ({sFiveA} : Set NativeSporadic.B)).map
          (MulAut.conj g).toMonoidHom := by
      rw [← hg, centralizer_conj_eq',
        CFSG.HardMathSupport.Dickson.I271.TabMFive.centralizer_pow_eq_of_five orderOf_sFiveA hc]
    have hcard : Nat.card (Subgroup.centralizer ({y} : Set NativeSporadic.B)) =
        Nat.card (Subgroup.centralizer ({sFiveA} : Set NativeSporadic.B)) := by
      rw [hC, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective]
    have hEcard : Nat.card E = 44352000 :=
      (Nat.card_congr (eE.trans hs100Equiv).toEquiv).trans card_hs100P
    refine ⟨fun h5 => ?_, ?_⟩
    · rw [hcard] at h5
      have hE : 44352000 ∣ Nat.card (Subgroup.centralizer ({sFiveA} : Set NativeSporadic.B)) :=
        hEcard ▸ Subgroup.card_dvd_of_le hEC
      have hl := Nat.lcm_dvd h5 hE
      have hl' : Nat.lcm (5 ^ 5) 44352000 = 1108800000 := by decide
      rw [hl'] at hl
      have := Nat.le_of_dvd Nat.card_pos hl
      have hA' : Nat.card (Subgroup.centralizer ({sFiveA} : Set NativeSporadic.B)) < 665280000 := hA
      omega
    · obtain ⟨hAP, hAc, hnc⟩ := exists_nonabelian_five_hs100P
      obtain ⟨R₀, hR₀E, hR₀p, hR₀nc⟩ :=
        exists_nonabelian_of_equiv (p := 5) (n := 3) (eE.trans hs100Equiv) hAP
          (by rw [hAc]; norm_num) hnc
      rw [hC]
      exact nonabelian_conj g (hR₀E.trans hEC) hR₀p hR₀nc

@[expose] def PBZero (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .B).Group)

@[expose] def PBOne (T : Type) [Group T] : Prop :=
  PBZero T ∨ Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .HS).Group)

@[expose] def PBLevel : ℕ → ∀ (T : Type) [Group T], Prop
  | 0 => PBZero
  | _ => PBOne

theorem isoInv_PBZero : Inputs2711c.IsoInv PBZero := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem isoInv_PBOne : Inputs2711c.IsoInv PBOne := by
  intro T T' _ _ e h
  rcases h with h | ⟨⟨f⟩⟩
  · exact Or.inl (isoInv_PBZero T T' e h)
  · exact Or.inr ⟨e.symm.trans f⟩

theorem isoInv_PBLevel : ∀ n, Inputs2711c.IsoInv (PBLevel n)
  | 0 => isoInv_PBZero
  | _ + 1 => isoInv_PBOne

theorem downStep_PBZero (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hcen : PCompCensus 5 (NativeSporadic.Carrier .B) (· = .sporadic .HS)) :
    DownStep 5 PBZero PBOne := by
  intro S _ _ hs hnab hP α hα I hI
  obtain ⟨bB⟩ := hBr .B
  haveI : Finite (NativeSporadic.Carrier .B) := Finite.of_equiv _ (hP.some.trans bB.symm).toEquiv
  exact Inputs2711c.pSimple_of_sporCensus Nat.prime_five (by norm_num) hOut bB
    (Good := fun T _ => CFSG.Yardstones.Md0ec50421ce4.catalogIs T (· = .sporadic .HS))
    (fun _ _ _ _ e h => CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv _ _ e h) hcen
    isoInv_PBOne (Or.inl ⟨MulEquiv.refl _⟩)
    (fun _ _ ⟨i, hi, hf⟩ => by subst hi; exact Or.inr hf) hnab hP α hα I hI

theorem dvd_card_of_PBOne (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T]
    (h : PBOne T) : 44352000 ∣ Nat.card T := by
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · rw [Nat.card_congr f.toEquiv, hOrd .B]
    simp only [sporOrd, CFSG.Open.orderBabyMonster]
    norm_num
  · rw [Nat.card_congr f.toEquiv, hOrd .HS]
    rfl

theorem disj_PBOne (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {T : Type} [Group T]
    [Finite T] (hP : PBOne T) (hA : Inputs2711c.AltOrChevTwo T) (hnd : ¬ sporOrd .B ∣ Nat.card T) :
    False := by
  rcases hP with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact hnd (by rw [Nat.card_congr f.toEquiv, hOrd .B])
  · have hT : Nat.card T = 44352000 := by rw [Nat.card_congr f.toEquiv, hOrd .HS]; rfl
    rcases hA with h | h
    · exact Inputs2711c.not_alt_of_card hT (m₀ := 12) (by norm_num) (by decide) (by decide) h
    · exact CFSG.HardMathSupport.Dickson.BMRows.not_isChevSimple_of_card_hs hb hT 2 h


theorem sporPairCase_B_five (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hb : LieOrderBridge) (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 5 2)
    (hcen : CFSG.Open.IsKGroup (NativeSporadic.Carrier .B) →
      PCompCensus 5 (NativeSporadic.Carrier .B) (· = .sporadic .HS))
    (hFR : CFSG.Open.IsKGroup (NativeSporadic.Carrier .B) →
      FullRankBound 5 (NativeSporadic.Carrier .B)) :
    Inputs2711c.SporPairCase .B 5 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN _ hB4 _ _ _ hC1 hname hin J0 hJ0 hJt _ E hEB hEC _ hEl hE2 _
    hle
  exfalso
  have hK := Inputs2711c.isKGroup_carrier hLK hname hBr
  have hname' := hname
  obtain ⟨eS⟩ := hname'
  obtain ⟨bB⟩ := hBr .B
  haveI : Finite (NativeSporadic.Carrier .B) := Finite.of_equiv _ (eS.trans bB.symm).toEquiv
  have σ : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .B := eS.trans bB.symm
  obtain ⟨z, hz, hz1⟩ := exists_mem_B0 hp hB hin hEB hE2 hC1 hle hB4 σ (hFR hK)
  obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
  have hpS : 5 ∣ sporOrd .B := by simp only [sporOrd, CFSG.Open.orderBabyMonster]; norm_num
  have h12 : ¬ sporOrd .B ∣ Nat.factorial 12 := fun h =>
    absurd (Nat.le_of_dvd (Nat.factorial_pos 12) h)
      (by simp only [sporOrd, CFSG.Open.orderBabyMonster]; norm_num [Nat.factorial])
  obtain ⟨J, hJL, hJ⟩ := exists_jD_one hp hp2 h183 hD2 hSpM hOrd hpS h12 hLK hLq hB hBN hname hJ0 hJt
    hEB hEC hEl he heC hz hz1
  obtain ⟨hLL, ⟨ePL⟩⟩ := selfComp hp hOrd hpS hLq hname
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  have hEel : IsElemAbelian 5 E := isElemAbelian_mono hB hEB
  have hAel : IsElemAbelian 5 (Subgroup.zpowers e) := isElemAbelian_mono hEel (Subgroup.zpowers_le.2 he)
  have hAc : Nat.card (Subgroup.zpowers e) ≤ 5 ^ 1 := by
    rw [Nat.card_zpowers, pow_one]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hEel.2 e he))
  have hT : PBLevel 1 (PSimple 5 J) :=
    typeClosure_graded hp hp2 (k := 1) (P := PBLevel)
      (fun n hn T _ h => by
        interval_cases n
        exact Or.inl h)
      (fun n hn => by
        interval_cases n
        exact downStep_PBZero hOut hBr (hcen hK))
      isoInv_PBLevel h183 hLK' hLL ⟨ePL⟩ hAel
      ((Subgroup.zpowers_le.2 (hEB he)).trans hBN) le_rfl hAc hJL
  rcases hJ with ⟨hA, hnS⟩ | hsmall
  · exact disj_PBOne hOrd hb hT hA hnS
  · have h1 := dvd_card_of_PBOne hOrd hT
    rcases hsmall with h | h | h | h
    · exact absurd (h1.trans h) (by decide)
    · exact absurd (h1.trans h) (by decide)
    · exact absurd (h1.trans h) (by decide)
    · exact absurd (h1.trans h) (by decide)

end PairB5

section PairM7FullRank

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.Monster.Generated (Gmat)
open CFSG.AGLEmbedding.Norton.MON5_7 (dG zG tG)
open CFSG.HardMathSupport.Dickson.I271.TabMSeven
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (orderOf_dG orderOf_zG orderOf_tG
  isTwoBCentralizer_tG centralizer_pow_eq_of_prime)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus (monsterSevenClasses)
open CFSG.Sporadic.HeldB (heP)
open CFSG.RankThree.PartOne (heSevenA0 heSevenC0)


theorem exists_nonabelian_seven_heP
    :
    heSevenA0 ≤ heP ∧ Nat.card heSevenA0 = 343 ∧
      ∃ a ∈ heSevenA0, ∃ b ∈ heSevenA0, a * b ≠ b * a := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨hAC, -, hAP, hAc, -, hcent, -⟩, -, -⟩ :=
    CFSG.RankThree.PartOne.R3E_He_full_seven_centralizer_structures
  refine ⟨hAP, hAc, ?_⟩
  by_contra hno
  push Not at hno
  have hle : heSevenA0 ≤
      Subgroup.centralizer (heSevenA0 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC0 :=
    le_inf (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => hno b hb a ha) hAC
  have := Subgroup.card_le_of_le hle
  rw [hAc, hcent] at this
  norm_num at this

theorem fullRankBound_Gmat
    : FullRankBound 7 Gmat := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hcls, h2A, h2B, hG5⟩ := gmat_seven_bounds
  obtain ⟨hHk, ⟨e⟩⟩ := tabMSeven_he_le_cent_dG
  have hE8 : HePE8 := hePE8
  obtain ⟨hcard, htA, huB, h2Bd⟩ :=
    tabMSeven_sevenA_facts hE8 hcls h2A h2B hG5 orderOf_dG hHk e
  have hzd : ∀ (g : Gmat) (m : ℕ), g * zG * g⁻¹ ≠ dG ^ m := by
    intro g m h
    by_cases hm : dG ^ m = 1
    · rw [hm] at h
      apply CFSG.AGLEmbedding.Norton.MON5_7.zG_ne_one
      have h' := congrArg (fun x => g⁻¹ * x * g) h
      simpa [mul_assoc] using h'
    · have h1 : Nat.card ↥(Subgroup.centralizer ({zG} : Set Gmat)) = 7 * 4030387200 := by
        rw [← card_centralizer_conj g zG, h, centralizer_pow_eq_of_prime orderOf_dG hm, hcard]
      have h6 := seven_pow_dvd_card_cent_zG
      rw [h1] at h6
      norm_num at h6
  have hQ : ∃ S : Subgroup Gmat, S ≤ Subgroup.centralizer ({zG} : Set Gmat) ∧
      Nonempty (↥S ≃* QuaternionGroup 4) := by
    obtain ⟨z, f, hz, hf, hzf, hzt, hft, S, hSz, ⟨eS⟩⟩ := tabMSeven_sevenB_data
    rcases monsterSevenClasses z hz with h | h
    · exfalso
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      have huo : orderOf (c * tG * c⁻¹) = 2 := by rw [orderOf_conj_eq, orderOf_tG]
      have hud : c * tG * c⁻¹ * dG = dG * (c * tG * c⁻¹) := by
        rw [← hc]
        exact Commute.conj hzt.symm c
      have huc : Nat.card ↥(Subgroup.centralizer ({c * tG * c⁻¹} : Set Gmat)) =
          CFSG.Monster.Existence.twoBCentralizerOrder := by
        rw [card_centralizer_conj]
        exact isTwoBCentralizer_tG.2.2.2.2.1
      have hf' : c * f * c⁻¹ ∈ Subgroup.centralizer ({c * tG * c⁻¹} : Set Gmat) ⊓
          Subgroup.centralizer ({dG} : Set Gmat) := by
        refine ⟨Subgroup.mem_centralizer_singleton_iff.2 (Commute.conj hft c),
          Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        rw [← hc]
        exact Commute.conj hzf.symm c
      have h5 := Subgroup.orderOf_dvd_natCard _ hf'
      rw [h2Bd _ huo hud huc, orderOf_conj_eq, hf] at h5
      norm_num at h5
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      refine ⟨S.map (MulAut.conj c).toMonoidHom, ?_,
        ⟨(S.equivMapOfInjective _ (MulAut.conj c).injective).symm.trans eS⟩⟩
      rintro _ ⟨s, hs, rfl⟩
      have hsz := Subgroup.mem_centralizer_singleton_iff.1 (hSz hs)
      rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        ← hc]
      exact Commute.conj hsz c
  have hzG : ∀ J : Subgroup Gmat, ¬ GLAPComponent 7 (Subgroup.centralizer ({zG} : Set Gmat)) J :=
    CFSG.HardMathSupport.Dickson.BMRows.census_M_seven_noComp orderOf_zG hzd htA huB hQ
  intro y hy1 hy7 hI
  have hk : orderOf y = 7 := orderOf_eq_prime hy7 hy1
  rcases monsterSevenClasses y hk with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hy : y = c⁻¹ * dG * c⁻¹⁻¹ := by rw [← hc]; group
    have hC : Subgroup.centralizer ({y} : Set Gmat) =
        (Subgroup.centralizer ({dG} : Set Gmat)).map (MulAut.conj c⁻¹).toMonoidHom := by
      rw [hy]
      exact centralizer_conj_eq' _ _
    refine ⟨?_, ?_⟩
    · rw [hC, Subgroup.card_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom)
        (MulAut.conj c⁻¹).injective, hcard]
      decide
    · obtain ⟨hA0P, hA0c, hnc⟩ := exists_nonabelian_seven_heP
      obtain ⟨R₀, hR₀H, hR₀p, hR₀nc⟩ :=
        exists_nonabelian_of_equiv (p := 7) (n := 3) e hA0P (by rw [hA0c]; norm_num) hnc
      rw [hC]
      exact nonabelian_conj c⁻¹ (hR₀H.trans hHk) hR₀p hR₀nc
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hy : y = c⁻¹ * zG * c⁻¹⁻¹ := by rw [← hc]; group
    have hC : Subgroup.centralizer ({y} : Set Gmat) =
        (Subgroup.centralizer ({zG} : Set Gmat)).map (MulAut.conj c⁻¹).toMonoidHom := by
      rw [hy]
      exact centralizer_conj_eq' _ _
    obtain ⟨I, hI⟩ := hI
    rw [hC] at hI
    have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv (by norm_num)
      (MulAut.conj c⁻¹).symm hI
    rw [map_symm_map] at hI'
    exact hzG _ hI'

theorem fullRankBound_M_seven
    : FullRankBound 7 (NativeSporadic.Carrier .M) := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : CFSG.Monster.Existence.MGriess ≃* NativeSporadic.Carrier .M := e₀
  have φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  let eG : Gmat ≃* NativeSporadic.Carrier .M := φ.symm.trans e
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv Gmat eG.toEquiv
  exact FullRankBound.of_equiv (by norm_num) eG fullRankBound_Gmat

end PairM7FullRank

section PairM7

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Dickson.BMRows (PCompCensus)

@[expose] def PMSZero (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .M).Group)

@[expose] def PMSOne (T : Type) [Group T] : Prop :=
  PMSZero T ∨ Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .He).Group)

@[expose] def PMSLevel : ℕ → ∀ (T : Type) [Group T], Prop
  | 0 => PMSZero
  | _ => PMSOne

theorem isoInv_PMSZero : Inputs2711c.IsoInv PMSZero := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem isoInv_PMSOne : Inputs2711c.IsoInv PMSOne := by
  intro T T' _ _ e h
  rcases h with h | ⟨⟨f⟩⟩
  · exact Or.inl (isoInv_PMSZero T T' e h)
  · exact Or.inr ⟨e.symm.trans f⟩

theorem isoInv_PMSLevel : ∀ n, Inputs2711c.IsoInv (PMSLevel n)
  | 0 => isoInv_PMSZero
  | _ + 1 => isoInv_PMSOne

theorem downStep_PMSZero (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hcen : PCompCensus 7 (NativeSporadic.Carrier .M) (· = .sporadic .He)) :
    DownStep 7 PMSZero PMSOne := by
  intro S _ _ hs hnab hP α hα I hI
  obtain ⟨bM⟩ := hBr .M
  haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv _ (hP.some.trans bM.symm).toEquiv
  exact Inputs2711c.pSimple_of_sporCensus (by norm_num) (by norm_num) hOut bM
    (Good := fun T _ => CFSG.Yardstones.Md0ec50421ce4.catalogIs T (· = .sporadic .He))
    (fun _ _ _ _ e h => CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv _ _ e h) hcen
    isoInv_PMSOne (Or.inl ⟨MulEquiv.refl _⟩)
    (fun _ _ ⟨i, hi, hf⟩ => by subst hi; exact Or.inr hf) hnab hP α hα I hI

theorem dvd_card_of_PMSOne (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T]
    (h : PMSOne T) : 4030387200 ∣ Nat.card T := by
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · rw [Nat.card_congr f.toEquiv, hOrd .M]
    simp only [sporOrd, CFSG.Open.orderMonster]
    norm_num
  · rw [Nat.card_congr f.toEquiv, hOrd .He]
    rfl

theorem disj_PMSOne (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {T : Type} [Group T]
    [Finite T] (hP : PMSOne T) (hA : Inputs2711c.AltOrChevTwo T) (hnd : ¬ sporOrd .M ∣ Nat.card T) :
    False := by
  rcases hP with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact hnd (by rw [Nat.card_congr f.toEquiv, hOrd .M])
  · have hT : Nat.card T = 4030387200 := by rw [Nat.card_congr f.toEquiv, hOrd .He]; rfl
    exact not_altOrChevTwo_of_card hb hT 10 3935925 14 (by norm_num) (by decide) (by norm_num)
      (by decide) (by norm_num) (by decide) (by decide) hA


theorem sporPairCase_M_seven (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hb : LieOrderBridge) (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 7 2)
    (hcen : PCompCensus 7 (NativeSporadic.Carrier .M) (· = .sporadic .He))
    (hFR : FullRankBound 7 (NativeSporadic.Carrier .M)) :
    Inputs2711c.SporPairCase .M 7 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN _ hB4 _ _ _ hC1 hname hin J0 hJ0 hJt _ E hEB hEC _ hEl hE2 _
    hle
  exfalso
  have hname' := hname
  obtain ⟨eS⟩ := hname'
  obtain ⟨bM⟩ := hBr .M
  haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv _ (eS.trans bM.symm).toEquiv
  have σ : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M := eS.trans bM.symm
  obtain ⟨z, hz, hz1⟩ := exists_mem_B0 hp hB hin hEB hE2 hC1 hle hB4 σ hFR
  obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
  have hpS : 7 ∣ sporOrd .M := by simp only [sporOrd, CFSG.Open.orderMonster]; norm_num
  have h12 : ¬ sporOrd .M ∣ Nat.factorial 12 := fun h =>
    absurd (Nat.le_of_dvd (Nat.factorial_pos 12) h)
      (by simp only [sporOrd, CFSG.Open.orderMonster]; norm_num [Nat.factorial])
  obtain ⟨J, hJL, hJ⟩ := exists_jD_one hp hp2 h183 hD2 hSpM hOrd hpS h12 hLK hLq hB hBN hname hJ0 hJt
    hEB hEC hEl he heC hz hz1
  obtain ⟨hLL, ⟨ePL⟩⟩ := selfComp hp hOrd hpS hLq hname
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  have hEel : IsElemAbelian 7 E := isElemAbelian_mono hB hEB
  have hAel : IsElemAbelian 7 (Subgroup.zpowers e) := isElemAbelian_mono hEel (Subgroup.zpowers_le.2 he)
  have hAc : Nat.card (Subgroup.zpowers e) ≤ 7 ^ 1 := by
    rw [Nat.card_zpowers, pow_one]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hEel.2 e he))
  have hT : PMSLevel 1 (PSimple 7 J) :=
    typeClosure_graded hp hp2 (k := 1) (P := PMSLevel)
      (fun n hn T _ h => by
        interval_cases n
        exact Or.inl h)
      (fun n hn => by
        interval_cases n
        exact downStep_PMSZero hOut hBr hcen)
      isoInv_PMSLevel h183 hLK' hLL ⟨ePL⟩ hAel
      ((Subgroup.zpowers_le.2 (hEB he)).trans hBN) le_rfl hAc hJL
  rcases hJ with ⟨hA, hnS⟩ | hsmall
  · exact disj_PMSOne hOrd hb hT hA hnS
  · have h1 := dvd_card_of_PMSOne hOrd hT
    rcases hsmall with h | h | h | h
    · exact absurd (h1.trans h) (by decide)
    · exact absurd (h1.trans h) (by decide)
    · exact absurd (h1.trans h) (by decide)
    · exact absurd (h1.trans h) (by decide)

end PairM7

section Split

@[expose] def SporPairCaseWith (name : TauCeti.SporadicName) (p : ℕ)
    (H : ∀ (X : Type) [Group X], Subgroup X → Subgroup X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], p.Prime → p ≠ 2 → ∀ (L B : Subgroup X), H X L B →
    CFSG.IsKGroup ↥L → CFSG.Open.IsQuasisimple ↥L → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set X) →
    (∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B) →
    4 ≤ CFSG.Open.pRank p B →
    (¬ ∃ n : ℕ, IsAltType n (↥L ⧸ Subgroup.center ↥L)) →
    (¬ ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥L ⧸ Subgroup.center ↥L)) →
    (∃ A : Subgroup (MulAut ↥L), IsElemAbelian p A ∧ 3 ≤ CFSG.Open.pRank p A) →
    CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1 →
    IsSporType name (↥L ⧸ Subgroup.center ↥L) →
    (∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) →
    ∀ J0 : Subgroup X,
      CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)) →
      Inputs2711c.J0Type p ↥J0 → ¬ (p = 3 ∧ IsAltType 5 J0) →
    ∀ E : Subgroup X, E ≤ B → B ⊓ Subgroup.centralizer (L : Set X) ≤ E →
      Nat.card B ≤ p ^ 2 * Nat.card E →
      GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ →
      2 ≤ CFSG.Open.pRank p E →
      GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ →
      (∀ e ∈ E, GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥) →
      L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)

theorem sporPairCase_of_with {name : TauCeti.SporadicName} {p : ℕ}
    {H : ∀ (X : Type) [Group X], Subgroup X → Subgroup X → Prop}
    (h₁ : SporPairCaseWith name p H) (h₂ : SporPairCaseWith name p fun X _ L B => ¬ H X L B) :
    Inputs2711c.SporPairCase name p := by
  intro X _ _ hp hp2 L B
  by_cases hH : H X L B
  · exact h₁ X hp hp2 L B hH
  · exact h₂ X hp hp2 L B hH

end Split

section QuasiCent

open CFSG.HardMathSupport.Dickson.I271

variable {Q : Type} [Group Q] [Finite Q]

theorem comps_of_quasisimple_centralizer {p : ℕ} (hp : p.Prime) {k : Q} {T : Type} [Group T]
    (e : ↥(Subgroup.centralizer ({k} : Set Q)) ≃* T) (hq : CFSG.Open.IsQuasisimple T)
    (hZ : IsPGroup p ↥(Subgroup.center T)) (hpT : p ∣ Nat.card T) :
    (∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
      Nonempty (PSimple p I ≃* (T ⧸ Subgroup.center T))) ∧
    (∀ I I' : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
      GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I' → I = I') := by
  set C := Subgroup.centralizer ({k} : Set Q) with hC
  have hq' : CFSG.Open.IsQuasisimple ↥C :=
    CFSG.HardMathSupport.Timmesfeld.Proving.isQuasisimple_of_mulEquiv' e.symm hq
  have ec : ↥(Subgroup.center ↥C) ≃* ↥(Subgroup.center T) :=
    ((Subgroup.center ↥C).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_center_eq e))
  have hZ' : IsPGroup p ↥(Subgroup.center ↥C) := hZ.of_equiv ec.symm
  have hp' : p ∣ Nat.card ↥C := by
    rw [Nat.card_congr e.toEquiv]
    exact hpT
  have eq : (↥C ⧸ Subgroup.center ↥C) ≃* (T ⧸ Subgroup.center T) :=
    QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center T) e (Subgroup.map_center_eq e)
  have hLn : ∀ g ∈ C, ∀ l ∈ C, g * l * g⁻¹ ∈ C := fun g hg l hl =>
    C.mul_mem (C.mul_mem hg hl) (C.inv_mem hg)
  have hcent : IsPGroup p ↥(C ⊓ Subgroup.centralizer (C : Set Q)) :=
    isPGroup_inf_centralizer_self C hZ'
  have hcore : GLAPPrimeCore p ↥C = ⊥ :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple hp le_rfl hLn hq' hp' hcent
  have huniq : ∀ I, GLAPComponent p C I → I = C := fun I hI =>
    eq_of_glaPComponent_of_normal_quasisimple hp le_rfl hLn hq' hcore hcent hI
  refine ⟨fun I hI => ?_, fun I I' hI hI' => (huniq I hI).trans (huniq I' hI').symm⟩
  rw [huniq I hI]
  exact ⟨(pSimpleEquivCenterQuot C hcore).trans eq⟩

end QuasiCent

section PairSuz

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT (yPerm yPerm_mem yPerm_pow Cy_eq Tg card_Tg
  Tg_elemAbelian)
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def PX₀ (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* X₀)

theorem isoInv_PX₀ : Inputs2711c.IsoInv PX₀ := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem downClosed_PX₀
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) : Inputs2711c.DownClosed 3 PX₀ := by
  intro T _ _ hs hnab hP α hα I hI
  obtain ⟨e⟩ := hP
  have hC : IsChevSimple 3 T := isChevSimple_of_mulEquiv e.symm isChevSimple_three_X₀
  obtain ⟨f⟩ := Inputs2711c.pSimple_equiv_of_terminal Nat.prime_three hKD hnab hC
    (Inputs2711c.mem_inner_of_X₀ hnab e) α hα I hI
  exact ⟨f.trans e⟩

theorem suz_five_le_pRank :
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥suzM) := by
  refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top (E := Tg) Tg_elemAbelian ?_
  rw [card_Tg]
  norm_num

theorem suz_card_centralizer_y :
    Nat.card (Subgroup.centralizer ({(⟨yPerm, yPerm_mem⟩ : ↥suzM)} : Set ↥suzM)) = 3240 := by
  obtain ⟨hC, hCcard⟩ := Cy_eq
  have h1 : Nat.card ↥(Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) = 3240 :=
    hC ▸ hCcard
  rw [← Subgroup.card_map_of_injective suzM.subtype_injective, map_centralizer_subtype']
  exact h1

theorem suz_constrained_XB :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3
      (Subgroup.centralizer ({(⟨fuseXB, fuseXB_mem⟩ : ↥suzM)} : Set ↥suzM)) := by
  refine pConstrainedShape_of_map_injective suzM.subtype suzM.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨hcard, -, hle, hnorm, hcent⟩ := TabSuzB.caseB_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hcent

theorem suzM_census_five
    {x : ↥suzM} (hx1 : x ≠ 1)
    (hx3 : x ^ 3 = 1)
    (h5 : 3 ^ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set ↥suzM))) :
    (∀ I : Subgroup ↥suzM, GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥suzM)) I →
      PX₀ (PSimple 3 I)) ∧
    (∀ I I' : Subgroup ↥suzM, GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥suzM)) I →
      GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥suzM)) I' → I = I') := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : orderOf (x : Equiv.Perm (Fin 1782)) = 3 := by
    have h1 : (x : Equiv.Perm (Fin 1782)) ^ 3 = 1 := by
      have := congrArg Subtype.val hx3
      simpa using this
    have h2 : (x : Equiv.Perm (Fin 1782)) ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨k, hk, c, hc, e, he, hcon⟩ := suz_exists_conj_classes x.2 hs3
  have key : ∀ (c' : ↥suzM), (c' : Equiv.Perm (Fin 1782)) = c → c' ^ 3 = 1 →
      Subgroup.centralizer ({x} : Set ↥suzM) =
        (Subgroup.centralizer ({c'} : Set ↥suzM)).map (MulAut.conj (⟨k, hk⟩ : ↥suzM)).toMonoidHom := by
    intro c' hc' hc'3
    have hx : x = (⟨k, hk⟩ : ↥suzM) * c' ^ e * (⟨k, hk⟩ : ↥suzM)⁻¹ := by
      apply Subtype.ext
      rw [← hcon, ← hc']
      simp
    rw [hx]
    exact centralizer_conj_pow hc'3 he _
  rcases hc with rfl | rfl | rfl
  · set k0 : ↥suzM := ⟨fuseXA, fuseXA_mem⟩ with hk0
    have hk' := key k0 rfl (Subtype.ext (by simpa using fuseXA_pow))
    obtain ⟨hq, hcen, ⟨eT⟩⟩ := aSub_quasisimple
    have hmap : (Subgroup.centralizer ({k0} : Set ↥suzM)).map suzM.subtype = aSub := by
      rw [map_centralizer_subtype' suzM k0]
      exact aSub_eq.symm
    let e1 : ↥(Subgroup.centralizer ({k0} : Set ↥suzM)) ≃* ↥aSub :=
      ((Subgroup.centralizer ({k0} : Set ↥suzM)).equivMapOfInjective suzM.subtype
        suzM.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
    let e2 : ↥(Subgroup.centralizer ({x} : Set ↥suzM)) ≃*
        ↥(Subgroup.centralizer ({k0} : Set ↥suzM)) :=
      (MulEquiv.subgroupCongr hk').trans
        ((Subgroup.centralizer ({k0} : Set ↥suzM)).equivMapOfInjective
          (MulAut.conj (⟨k, hk⟩ : ↥suzM)).toMonoidHom (MulAut.conj (⟨k, hk⟩ : ↥suzM)).injective).symm
    have hz3 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ^ 3 = 1 := Subtype.ext (by simpa using fuseXA_pow)
    have hz1 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ≠ 1 := fun h => fuseXA_ne_one (congrArg Subtype.val h)
    have hord : orderOf (⟨fuseXA, aX_mem⟩ : ↥aSub) = 3 := orderOf_eq_prime hz3 hz1
    have hZ3 : IsPGroup 3 ↥(Subgroup.center ↥aSub) := by
      have h3 : IsPGroup 3 ↥(Subgroup.zpowers (⟨fuseXA, aX_mem⟩ : ↥aSub)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
      exact h3.of_equiv (MulEquiv.subgroupCongr hcen.symm)
    have h3 : 3 ∣ Nat.card ↥aSub := by
      rw [card_aSub]
      norm_num
    obtain ⟨h1, h2⟩ := comps_of_quasisimple_centralizer Nat.prime_three (e2.trans e1) hq hZ3 h3
    exact ⟨fun I hI => let ⟨f⟩ := h1 I hI; ⟨f.trans eT⟩, h2⟩
  · have hcon' := pConstrainedShape_map (MulAut.conj (⟨k, hk⟩ : ↥suzM)) suz_constrained_XB
    rw [← key ⟨fuseXB, fuseXB_mem⟩ rfl (Subtype.ext (by simpa using fuseXB_pow))] at hcon'
    exact ⟨fun I hI => (no_glaPComponent_of_pConstrainedShape Nat.prime_three hcon' hI).elim,
      fun I _ hI _ => (no_glaPComponent_of_pConstrainedShape Nat.prime_three hcon' hI).elim⟩
  · exfalso
    rw [key ⟨yPerm, yPerm_mem⟩ rfl (Subtype.ext (by simpa using yPerm_pow)),
      Subgroup.card_map_of_injective (f := (MulAut.conj (⟨k, hk⟩ : ↥suzM)).toMonoidHom)
        (MulAut.conj (⟨k, hk⟩ : ↥suzM)).injective, suz_card_centralizer_y] at h5
    norm_num at h5


theorem suzM_census_full
    {x : ↥suzM} (hx1 : x ≠ 1)
    (hx3 : x ^ 3 = 1)
    (hdvd : 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup ↥suzM) ∣
      Nat.card (Subgroup.centralizer ({x} : Set ↥suzM))) :
    (∀ I : Subgroup ↥suzM, GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥suzM)) I →
      PX₀ (PSimple 3 I)) ∧
    (∀ I I' : Subgroup ↥suzM, GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥suzM)) I →
      GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥suzM)) I' → I = I') :=
  suzM_census_five hx1 hx3 ((Nat.pow_dvd_pow 3 suz_five_le_pRank).trans hdvd)


theorem sporPairCase_Suz_three_of_not_dvd (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) (hb : LieOrderBridge)
    (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2) :
    SporPairCaseWith .Suz 3 fun X _ L _ => ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := by
  intro X _ _ hp hp2 L B hZL hLK hLq hB hBN hmax _ _ _ _ hC1 hname hin J0 hJ0 hJt _ E hEB _ _ hEl hE2 _
    _
  exfalso
  have hname' := hname
  obtain ⟨eS⟩ := hname'
  obtain ⟨bS⟩ := hBr .Suz
  let σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥suzM :=
    (eS.trans bS.symm).trans (suzEquivM : NativeSporadic.Suz ≃* ↥suzM)
  obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
  obtain ⟨hcG, hcU⟩ := census_barHom hp hB hmax hin hZL σ (Good := PX₀) isoInv_PX₀
    (fun x hx1 hx3 hdvd => suzM_census_full hx1 hx3 hdvd) ⟨e, hEB he⟩ heC
  have hEel : IsElemAbelian 3 E := isElemAbelian_mono hB hEB
  obtain ⟨D, hDE, heD, hDc⟩ := exists_card_sq hp hEel hE2 he
  have hDel : IsElemAbelian 3 D := isElemAbelian_mono hEel hDE
  have hD2r : 2 ≤ CFSG.Open.pRank 3 D := (pRank_eq_two hp hDel hDc).ge
  have hDC : ¬ D ≤ Subgroup.centralizer (L : Set X) := fun h => heC (h heD)
  have hpS : 3 ∣ sporOrd .Suz := by simp only [sporOrd]; norm_num
  have h12 : ¬ sporOrd .Suz ∣ Nat.factorial 12 := fun h =>
    absurd (Nat.le_of_dvd (Nat.factorial_pos 12) h)
      (by simp only [sporOrd]; norm_num [Nat.factorial])
  obtain ⟨J, hJL, hJ⟩ := exists_jD hp hp2 h183 hD2 hSpM hOrd hpS h12 hLK hLq hB hBN hname hJ0 hJt
    hEB hEl hDE hD2r hDC
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  obtain ⟨fJ⟩ : PX₀ (PSimple 3 J) :=
    typeClosure_of_unique hp hp2 (downClosed_PX₀ hKD) isoInv_PX₀ h183 hLK' hDel
      (hDE.trans (hEB.trans hBN)) heD hcG hcU hJL
  have hcard : Nat.card (PSimple 3 J) = 3265920 :=
    (Nat.card_congr fJ.toEquiv).trans CFSG.LieType.Multipliers.U43.card_X₀
  rcases hJ with ⟨hA, -⟩ | hsmall
  · exact Inputs2711c.not_altOrChevTwo_U43 hb hcard hA
  · rw [hcard] at hsmall
    rcases hsmall with h | h | h | h <;> exact absurd h (by decide)

end PairSuz

section PairFi24

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def PFZero (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group)

@[expose] def PFOne (T : Type) [Group T] : Prop :=
  PFZero T ∨ FiGood T

@[expose] def PFLevel : ℕ → ∀ (T : Type) [Group T], Prop
  | 0 => PFZero
  | _ => PFOne

theorem isoInv_PFZero : Inputs2711c.IsoInv PFZero := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem isoInv_PFOne : Inputs2711c.IsoInv PFOne := by
  intro T T' _ _ e h
  rcases h with h | h
  · exact Or.inl (isoInv_PFZero T T' e h)
  · exact Or.inr (fiGood_iso T T' e h)

theorem isoInv_PFLevel : ∀ n, Inputs2711c.IsoInv (PFLevel n)
  | 0 => isoInv_PFZero
  | _ + 1 => isoInv_PFOne

theorem downStep_PFZero (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hFi : CentShapeRk 3 FiGood (fun _ _ => True) (NativeSporadic.Carrier .Fi24Prime)) :
    DownStep 3 PFZero PFOne := by
  intro S _ _ hs hnab hF α hα I hI
  obtain ⟨bF⟩ := hBr .Fi24Prime
  haveI : Finite (NativeSporadic.Carrier .Fi24Prime) :=
    Finite.of_equiv _ (hF.some.trans bF.symm).toEquiv
  exact Inputs2711c.pSimple_of_sporShape Nat.prime_three (by norm_num) hOut bF fiGood_iso
    (fun _ _ _ _ _ h => h) hFi isoInv_PFOne (Or.inl ⟨MulEquiv.refl _⟩)
    (fun _ _ h => Or.inr h) hnab hF α hα I hI

theorem dvd_card_of_PFOne (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T]
    (h : PFOne T) : 4245696 ∣ Nat.card T := by
  rcases h with ⟨⟨f⟩⟩ | h | h
  · rw [Nat.card_congr f.toEquiv, hOrd .Fi24Prime]
    simp only [sporOrd, CFSG.Open.orderFi24Prime]
    norm_num
  · rw [h]; norm_num
  · rw [h]

theorem disj_PFOne (hb : LieOrderBridge) {T : Type} [Group T] [Finite T] (hOrd : SporadicOrdersTable)
    (hP : PFOne T) (hA : Inputs2711c.AltOrChevTwo T) (hnd : ¬ sporOrd .Fi24Prime ∣ Nat.card T) :
    False := by
  rcases hP with ⟨⟨f⟩⟩ | h | h
  · exact hnd (by rw [Nat.card_congr f.toEquiv, hOrd .Fi24Prime])
  · exact not_altOrChevTwo_of_card hb h 12 1209028275 16 (by norm_num) (by decide) (by norm_num)
      (by decide) (by norm_num) (by decide) (by decide) hA
  · exact not_altOrChevTwo_of_card hb h 6 66339 11 (by norm_num) (by decide) (by norm_num)
      (by decide) (by norm_num) (by decide) (by decide) hA


theorem sporPairCase_Fi24_three_of_ne_bot (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hb : LieOrderBridge) (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2)
    (hFi : CentShapeRk 3 FiGood (fun _ _ => True) (NativeSporadic.Carrier .Fi24Prime)) :
    SporPairCaseWith .Fi24Prime 3 fun X _ L B => ¬ B ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by
  intro X _ _ hp hp2 L B hB0 hLK hLq hB hBN _ _ _ _ _ hC1 hname _ J0 hJ0 hJt _ E hEB hEC _ hEl hE2 _ _
  exfalso
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB0
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
  have hpS : 3 ∣ sporOrd .Fi24Prime := by simp only [sporOrd, CFSG.Open.orderFi24Prime]; norm_num
  have h12 : ¬ sporOrd .Fi24Prime ∣ Nat.factorial 12 := fun h =>
    absurd (Nat.le_of_dvd (Nat.factorial_pos 12) h)
      (by simp only [sporOrd, CFSG.Open.orderFi24Prime]; norm_num [Nat.factorial])
  obtain ⟨J, hJL, hJ⟩ := exists_jD_one hp hp2 h183 hD2 hSpM hOrd hpS h12 hLK hLq hB hBN hname hJ0 hJt
    hEB hEC hEl he heC hz hz1'
  obtain ⟨hLL, ⟨ePL⟩⟩ := selfComp hp hOrd hpS hLq hname
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  have hEel : IsElemAbelian 3 E := isElemAbelian_mono hB hEB
  have hAel : IsElemAbelian 3 (Subgroup.zpowers e) :=
    isElemAbelian_mono hEel (Subgroup.zpowers_le.2 he)
  have hAc : Nat.card (Subgroup.zpowers e) ≤ 3 ^ 1 := by
    rw [Nat.card_zpowers, pow_one]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hEel.2 e he))
  have hT : PFLevel 1 (PSimple 3 J) :=
    typeClosure_graded hp hp2 (k := 1) (P := PFLevel)
      (fun n hn T _ h => by
        interval_cases n
        exact Or.inl h)
      (fun n hn => by
        interval_cases n
        exact downStep_PFZero hOut hBr hFi)
      isoInv_PFLevel h183 hLK' hLL ⟨ePL⟩ hAel
      ((Subgroup.zpowers_le.2 (hEB he)).trans hBN) le_rfl hAc hJL
  rcases hJ with ⟨hA, hnS⟩ | hsmall
  · exact disj_PFOne hb hOrd hT hA hnS
  · have h1 := dvd_card_of_PFOne hOrd hT
    rcases hsmall with h | h | h | h <;> exact absurd (h1.trans h) (by decide)

end PairFi24

section TerminalCount

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem false_of_terminal_comp (hp : p.Prime) (hp2 : p ≠ 2) (h183 : Input18_3_4)
    {P : ∀ (T : Type) [Group T], Prop} (hD : Inputs2711c.DownClosed p P)
    (hinv : Inputs2711c.IsoInv P) {L B E : Subgroup X} (hLK : CFSG.Open.IsKGroup ↥L)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    (hZL : ¬ p ∣ Nat.card (Subgroup.center ↥L)) (hEB : E ≤ B)
    (hEC : B ⊓ Subgroup.centralizer (L : Set X) ≤ E) (hEi : Nat.card B ≤ p ^ 2 * Nat.card E)
    (hlE : GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥) {e : X} (he : e ∈ E)
    {L₁ : Subgroup X}
    (hU : ∀ C : Subgroup X, GLAPComponent p (L ⊓ Subgroup.centralizer ({e} : Set X)) C → C = L₁)
    (hPt : ∀ C : Subgroup X, GLAPComponent p (L ⊓ Subgroup.centralizer ({e} : Set X)) C →
      P (PSimple p C))
    (hcardP : ∀ (T : Type) [Group T] [Finite T], P T → Nat.card L₁ ≤ Nat.card T)
    (hL₁L : L₁ ≤ L)
    (hZ₁ : ∀ y ∈ (L₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)),
      (∀ w ∈ (L₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)), y * w = w * y) → y = 1)
    {T : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (hTL : T ≤ (L₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
    (hT : IsElemAbelian p T) {r : ℕ} (hTc : Nat.card T = p ^ r) (hr : 3 ≤ r) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEel : IsElemAbelian p E := isElemAbelian_mono hB hEB
  have hEN : E ≤ Subgroup.normalizer (L : Set X) := hEB.trans hBN
  obtain ⟨J, hJ⟩ := Inputs2711.exists_glaPComponent_of_ne_bot hlE
  have hPJ : P (PSimple p J) :=
    typeClosure_of_unique hp hp2 hD hinv h183 hLK hEel hEN he hPt
      (fun C C' hC hC' => (hU C hC).trans (hU C' hC').symm) hJ
  have hJlay := glaPComponent_le_glaPLayer_centralizer_sub hp h183 hLK hEel hEN
    (Subgroup.zpowers_le.2 he) hJ
  have hcz : Subgroup.centralizer ((Subgroup.zpowers e : Subgroup X) : Set X) =
      Subgroup.centralizer ({e} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcz] at hJlay
  have hJL₁ : J ≤ L₁ := hJlay.trans (sSup_le fun C hC => (hU C hC).le)
  have hcJ : Nat.card L₁ ≤ Nat.card J :=
    (hcardP _ hPJ).trans (Nat.le_of_dvd Nat.card_pos (Inputs2711c.card_pSimple_dvd p J))
  have hJeq : J = L₁ := Subgroup.eq_of_le_of_card_ge hJL₁ hcJ
  have hL₁E : L₁ ≤ Subgroup.centralizer (E : Set X) := hJeq ▸ (hJ.1.trans inf_le_right)
  have hinE : ∀ b ∈ E, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X) :=
    fun b hb => hin b (hEB hb)
  set Ebar : Subgroup (↥L ⧸ Subgroup.center ↥L) := (barHom hinE).range with hEbar
  set L₁bar : Subgroup (↥L ⧸ Subgroup.center ↥L) :=
    (L₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) with hL₁bar
  have hk : ∀ f : ↥E, ∀ l ∈ L₁, Commute ((kOf hinE f : ↥L) : X) l := by
    intro f l hl
    have hc : Commute l (((kOf hinE f : ↥L) : X)⁻¹ * (f : X)) :=
      Subgroup.mem_centralizer_iff.1 (kOf_spec hinE f) l (hL₁L hl)
    have hf : Commute (f : X) l := Subgroup.mem_centralizer_iff.1 (hL₁E hl) f f.2
    have hkf : ((kOf hinE f : ↥L) : X) =
        (f : X) * (((kOf hinE f : ↥L) : X)⁻¹ * (f : X))⁻¹ := by group
    rw [hkf]
    exact hf.mul_left hc.inv_right.symm
  have hEcomm : ∀ a ∈ Ebar, ∀ w ∈ L₁bar, a * w = w * a := by
    rintro _ ⟨f, rfl⟩ _ ⟨l, hl, rfl⟩
    rw [barHom_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hk f l (Subgroup.mem_subgroupOf.1 hl)).eq
  have hdisj : ∀ y ∈ Ebar, y ∈ T → y = 1 := fun y hyE hyT =>
    hZ₁ y (hTL hyT) fun w hw => hEcomm y hyE w hw
  have hcommT : ∀ a ∈ Ebar, ∀ t ∈ T, a * t = t * a := fun a ha t ht => hEcomm a ha t (hTL ht)
  have hEbel : IsElemAbelian p Ebar := isElemAbelian_range_barHom hEel hinE
  obtain ⟨hAel, hAc⟩ := Inputs2711c.card_prodHom_range hEbel hT hcommT hdisj
  set a := CFSG.Open.pRank p Ebar with ha
  have hEa : Nat.card Ebar = p ^ a := Inputs27.card_eq_pow_pRank hp hEbel
  have hEcard : Nat.card Ebar * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) = Nat.card E := by
    have h := card_range_barHom_mul hinE
    have hEq : E ⊓ Subgroup.centralizer (L : Set X) = B ⊓ Subgroup.centralizer (L : Set X) :=
      le_antisymm (inf_le_inf_right _ hEB) (le_inf hEC inf_le_right)
    rw [hEq] at h
    exact h
  have h1 : a + r ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hAel (by rw [hAc, hEa, hTc, pow_add])
  have h2 := CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_centerQuotient_le_of_not_dvd hp hZL
  have h3 := pow_pRank_mul_le hp hB hmax hZL
  have hb0 : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) := Nat.card_pos
  have hchain : p ^ (a + r) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) ≤
      p ^ (a + 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) := by
    calc p ^ (a + r) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X))
        ≤ p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (h1.trans h2))
      _ ≤ Nat.card B := h3
      _ ≤ p ^ 2 * Nat.card E := hEi
      _ = p ^ (a + 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) := by
          rw [← hEcard, hEa, pow_add]
          ring
  have h4 := Nat.le_of_mul_le_mul_right hchain hb0
  have h5 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h4
  omega

end TerminalCount

section PairCo2

open CFSG.HardMathSupport.Dickson.I271 CFSG.Sporadic.Co2Cert
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QP45)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)

@[expose] def PU42 (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* ↥QP45.originalSubgroup)

theorem isoInv_PU42 : Inputs2711c.IsoInv PU42 := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem downClosed_PU42
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) : Inputs2711c.DownClosed 3 PU42 := by
  intro T _ _ hs hnab hP α hα I hI
  obtain ⟨e⟩ := hP
  have hC : IsChevSimple 3 T := isChevSimple_three_of_equiv_QP45 e
  have hcard : Nat.card (MulAut T) = 2 * Nat.card T := by
    rw [CFSG.Sporadic.Co2Smith.card_mulAut_of_equiv e, Nat.card_congr e.toEquiv, card_QP45_eq]
  have hin : ∀ β : MulAut T, β ^ 3 = 1 →
      β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner T := fun β hβ =>
    Inputs2711c.mem_inner_of_card
      (CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab)
      Nat.prime_three hcard (by decide) β hβ
  obtain ⟨f⟩ := Inputs2711c.pSimple_equiv_of_terminal Nat.prime_three hKD hnab hC hin α hα I hI
  exact ⟨f.trans e⟩


theorem co2_constrained_XA (hXA : co2XA ∈ co2P) :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3
      (Subgroup.centralizer ({(⟨co2XA, hXA⟩ : ↥co2P)} : Set ↥co2P)) := by
  refine pConstrainedShape_of_map_injective co2P.subtype co2P.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := co2CaseA_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_forall_conj hnorm)
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent


theorem co2_comp_XB (hXB : co2XB ∈ co2P) :
    (∀ I : Subgroup ↥co2P,
      GLAPComponent 3 (Subgroup.centralizer ({(⟨co2XB, hXB⟩ : ↥co2P)} : Set ↥co2P)) I →
        I = Lsub.comap co2P.subtype) ∧
      Nonempty (↥(Lsub.comap co2P.subtype) ≃* ↥QP45.originalSubgroup) := by
  obtain ⟨-, -, -, hcard, hLC, hLn, hcent, hrels⟩ := co2CaseB_spec
  obtain ⟨eL⟩ := nonempty_mulEquiv_QP45_of_rels uvGen hrels hcard
  have hLP : Lsub ≤ co2P := fun l hl => (hLC hl).2
  set x : ↥co2P := ⟨co2XB, hXB⟩ with hx
  set C' : Subgroup ↥co2P := Subgroup.centralizer ({x} : Set ↥co2P) with hC'
  set L' : Subgroup ↥co2P := Lsub.comap co2P.subtype with hL'
  have e' : ↥L' ≃* ↥QP45.originalSubgroup := (Subgroup.subgroupOfEquivOfLe hLP).trans eL
  haveI hs : IsSimpleGroup ↥L' := isSimpleGroup_of_equiv_QP45 e'
  have hnab : ∃ a b : ↥L', a * b ≠ b * a := nonabelian_of_equiv_QP45 e'
  have hp3 : 3 ∣ Nat.card ↥L' := three_dvd_card_of_equiv_QP45 e'
  have hmapC : C'.map co2P.subtype = Subgroup.centralizer ({(x : Equiv.Perm (Fin 2300))} :
      Set (Equiv.Perm (Fin 2300))) ⊓ co2P := map_centralizer_subtype' co2P x
  have hLC' : L' ≤ C' := by
    intro l hl
    have hl1 : (l : Equiv.Perm (Fin 2300)) ∈
        Subgroup.centralizer ({co2XB} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P := hLC hl
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hl1).1
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hc)
  have hgC : ∀ g ∈ C', (g : Equiv.Perm (Fin 2300)) ∈
      Subgroup.centralizer ({co2XB} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P := fun g hg => by
    have : (g : Equiv.Perm (Fin 2300)) ∈ C'.map co2P.subtype := ⟨g, hg, rfl⟩
    rw [hmapC] at this
    exact this
  have hLn' : ∀ g ∈ C', ∀ l ∈ L', g * l * g⁻¹ ∈ L' := by
    intro g hg l hl
    have h := hLn _ (hgC g hg) _ (show (l : Equiv.Perm (Fin 2300)) ∈ Lsub from hl)
    show ((g * l * g⁻¹ : ↥co2P) : Equiv.Perm (Fin 2300)) ∈ Lsub
    simpa using h
  have hLq : CFSG.Open.IsQuasisimple ↥L' := isQuasisimple_of_simple_nonab hnab
  have hcentP : IsPGroup 3 ↥(C' ⊓ Subgroup.centralizer (L' : Set ↥co2P)) := by
    intro c
    refine ⟨1, ?_⟩
    have hcC := hgC c.1 (Subgroup.mem_inf.1 c.2).1
    have hcomm : ∀ l ∈ Lsub, l * ((c : ↥co2P) : Equiv.Perm (Fin 2300)) =
        ((c : ↥co2P) : Equiv.Perm (Fin 2300)) * l := by
      intro l hl
      have hlL : (⟨l, hLP hl⟩ : ↥co2P) ∈ L' := hl
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 c.2).2 _ hlL)
    have h0 := hcent _ hcC hcomm
    have h1 : (c : ↥co2P) ^ 3 = 1 := Subtype.ext (by simpa using h0)
    rw [pow_one]
    exact Subtype.ext h1
  have hcore : GLAPPrimeCore 3 ↥C' = ⊥ :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three hLC' hLn' hLq hp3 hcentP
  exact ⟨fun I hI =>
    eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three hLC' hLn' hLq hcore hcentP hI, ⟨e'⟩⟩

theorem co2_comps {x : ↥co2P} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hI : ∃ I : Subgroup ↥co2P, GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥co2P)) I) :
    ∃ g : ↥co2P, ∀ I : Subgroup ↥co2P,
      GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥co2P)) I →
        I = (Lsub.comap co2P.subtype).map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : orderOf (x : Equiv.Perm (Fin 2300)) = 3 := by
    have h1 : (x : Equiv.Perm (Fin 2300)) ^ 3 = 1 := by
      have := congrArg Subtype.val hx3
      simpa using this
    have h2 : (x : Equiv.Perm (Fin 2300)) ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨k, hk, c, hc, e, he, hcon⟩ := co2_exists_conj_classes x.2 hs3
  obtain ⟨hXA3, -, hXAm, -⟩ := co2CaseA_spec
  obtain ⟨hXB3, -, hXBm, -⟩ := co2CaseB_spec
  have key : ∀ (c' : ↥co2P), (c' : Equiv.Perm (Fin 2300)) = c → c' ^ 3 = 1 →
      Subgroup.centralizer ({x} : Set ↥co2P) =
        (Subgroup.centralizer ({c'} : Set ↥co2P)).map
          (MulAut.conj (⟨k, hk⟩ : ↥co2P)).toMonoidHom := by
    intro c' hc' hc'3
    have hx : x = (⟨k, hk⟩ : ↥co2P) * c' ^ e * (⟨k, hk⟩ : ↥co2P)⁻¹ := by
      apply Subtype.ext
      rw [← hcon, ← hc']
      simp
    rw [hx]
    exact centralizer_conj_pow hc'3 he _
  rcases hc with rfl | rfl
  · exfalso
    obtain ⟨I, hI⟩ := hI
    have hcon' := pConstrainedShape_map (MulAut.conj (⟨k, hk⟩ : ↥co2P)) (co2_constrained_XA hXAm)
    rw [← key ⟨co2XA, hXAm⟩ rfl (Subtype.ext (by simpa using hXA3))] at hcon'
    exact no_glaPComponent_of_pConstrainedShape Nat.prime_three hcon' hI
  · refine ⟨⟨k, hk⟩, fun I hI => ?_⟩
    rw [key ⟨co2XB, hXBm⟩ rfl (Subtype.ext (by simpa using hXB3))] at hI
    have hI' := glaPComponent_map_equiv Nat.prime_three (MulAut.conj (⟨k, hk⟩ : ↥co2P)).symm hI
    rw [map_symm_map] at hI'
    have hI'' := (co2_comp_XB hXBm).1 _ hI'
    rw [← hI'']
    exact (map_symm_map (MulAut.conj (⟨k, hk⟩ : ↥co2P)).symm I).symm

theorem co2_conj_data (hXB : co2XB ∈ co2P) (g : ↥co2P) :
    PU42 (PSimple 3 ((Lsub.comap co2P.subtype).map (MulAut.conj g).toMonoidHom)) ∧
      Nat.card ↥((Lsub.comap co2P.subtype).map (MulAut.conj g).toMonoidHom) = 25920 ∧
      (∀ z ∈ (Lsub.comap co2P.subtype).map (MulAut.conj g).toMonoidHom,
        (∀ w ∈ (Lsub.comap co2P.subtype).map (MulAut.conj g).toMonoidHom, z * w = w * z) →
          z = 1) ∧
      ∃ T : Subgroup ↥co2P, T ≤ (Lsub.comap co2P.subtype).map (MulAut.conj g).toMonoidHom ∧
        IsElemAbelian 3 T ∧ Nat.card T = 3 ^ 3 := by
  obtain ⟨-, ⟨e'⟩⟩ := co2_comp_XB hXB
  set L' : Subgroup ↥co2P := Lsub.comap co2P.subtype with hL'
  set K : Subgroup ↥co2P := L'.map (MulAut.conj g).toMonoidHom with hK
  have eK : ↥K ≃* ↥QP45.originalSubgroup := ((MulAut.conj g).subgroupMap L').symm.trans e'
  haveI hs : IsSimpleGroup ↥K := isSimpleGroup_of_equiv_QP45 eK
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := nonabelian_of_equiv_QP45 eK
  have hp3 : 3 ∣ Nat.card ↥K := three_dvd_card_of_equiv_QP45 eK
  have hcore : GLAPPrimeCore 3 ↥K = ⊥ := Inputs2711c.glaPPrimeCore_eq_bot_of_simple Nat.prime_three hp3
  have hZK : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_nonab hnab
  refine ⟨⟨(pSimpleEquivSelf K hcore hZK).trans eK⟩, ?_, ?_, ?_⟩
  · rw [Nat.card_congr eK.toEquiv, card_QP45_eq]
  · intro z hz hcomm
    have hzc : (⟨z, hz⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hcomm w w.2).symm
    rw [hZK, Subgroup.mem_bot] at hzc
    exact congrArg Subtype.val hzc
  · obtain ⟨E₀, hE₀, hE₀c⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.U42.psp43_exists_E27
    let ψ : CFSG.GH74.Exceptional.PSp43 →* ↥co2P :=
      K.subtype.comp (CFSG.ComponentClassification.CatFactsSmall.PSp43.psp43EquivP.trans
        eK.symm).toMonoidHom
    have hψ : Function.Injective ψ := fun a b h =>
      (CFSG.ComponentClassification.CatFactsSmall.PSp43.psp43EquivP.trans eK.symm).injective
        (K.subtype_injective h)
    refine ⟨E₀.map ψ, ?_, CFSG.SectionRank.isElemAbelian_map hE₀ ψ, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact (CFSG.ComponentClassification.CatFactsSmall.PSp43.psp43EquivP.trans eK.symm y).2
    · rw [Subgroup.card_map_of_injective hψ, hE₀c]


theorem sporPairCase_Co2_three (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) :
    Inputs2711c.SporPairCase .Co2 3 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN hmax _ _ _ _ hC1 hname hin _ _ _ _ E hEB hEC hEi _ hE2
    hlE hle
  exfalso
  have hname' := hname
  obtain ⟨eS⟩ := hname'
  have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
    have h := CFSG.HardMathSupport.Dickson.I271.card_center_dvd_multiplier hSpM hLq .Co2 eS
    have h1 : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.sporadicMultiplierOrder .Co2 = 1 := by
      decide
    rw [h1] at h
    exact Nat.dvd_one.1 h
  have hZ : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
  have hZL : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := by
    rw [hZ1]
    decide
  obtain ⟨bC⟩ := hBr .Co2
  let σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥co2P :=
    (eS.trans bC.symm).trans (co2PermEquiv : CFSG.Blueprint.NativeSporadic.Co2 ≃* co2P)
  obtain ⟨-, -, hXBm, -⟩ := co2CaseB_spec
  have hcen : ∀ x : ↥co2P, x ≠ 1 → x ^ 3 = 1 →
      3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup ↥co2P) ∣ Nat.card (Subgroup.centralizer ({x} : Set ↥co2P)) →
      (∀ I : Subgroup ↥co2P, GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥co2P)) I →
        PU42 (PSimple 3 I)) ∧
      (∀ I I' : Subgroup ↥co2P, GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥co2P)) I →
        GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥co2P)) I' → I = I') := by
    intro x hx1 hx3 _
    by_cases hex : ∃ I : Subgroup ↥co2P, GLAPComponent 3 (Subgroup.centralizer ({x} : Set ↥co2P)) I
    · obtain ⟨g, hg⟩ := co2_comps hx1 hx3 hex
      refine ⟨fun I hI => ?_, fun I I' hI hI' => (hg I hI).trans (hg I' hI').symm⟩
      rw [hg I hI]
      exact (co2_conj_data hXBm g).1
    · exact ⟨fun I hI => (hex ⟨I, hI⟩).elim, fun I _ hI _ => (hex ⟨I, hI⟩).elim⟩
  obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
  set b : ↥B := ⟨e, hEB he⟩ with hb
  obtain ⟨hcG, hcU⟩ := census_barHom hp hB hmax hin hZL σ (Good := PU42) isoInv_PU42 hcen b heC
  obtain ⟨L₁, hL₁⟩ := Inputs2711.exists_glaPComponent_of_ne_bot (hle e he)
  have hU : ∀ C : Subgroup X, GLAPComponent 3 (L ⊓ Subgroup.centralizer ({e} : Set X)) C → C = L₁ :=
    fun C hC => hcU C L₁ hC hL₁
  have hL₁L : L₁ ≤ L := hL₁.1.trans inf_le_left
  obtain ⟨h1, -⟩ := transfer_barHom hp hin b hL₁
  obtain ⟨h2, -⟩ := Inputs1415.comp_transport hp σ h1
  have hx1 : σ (barHom hin b) ≠ 1 := fun h =>
    heC ((barHom_eq_one_iff hin b).1 (σ.injective (h.trans (map_one σ).symm)))
  have hx3 : σ (barHom hin b) ^ 3 = 1 := by
    rw [← map_pow, (isElemAbelian_range_barHom hB hin).2 _ ⟨b, rfl⟩, map_one]
  obtain ⟨g, hg⟩ := co2_comps hx1 hx3 ⟨_, h2⟩
  have hK := hg _ h2
  obtain ⟨-, hKc, hKZ, T', hT'K, hT'el, hT'c⟩ := co2_conj_data hXBm g
  set L₁bar : Subgroup (↥L ⧸ Subgroup.center ↥L) :=
    (L₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) with hL₁bar
  have hmk : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥L)) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hZ])
  have hcL₁ : Nat.card L₁ = 25920 := by
    have h : Nat.card ↥(((L₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map
        σ.toMonoidHom) = Nat.card ↥((Lsub.comap co2P.subtype).map (MulAut.conj g).toMonoidHom) := by
      rw [hK]
    rw [Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective,
      Subgroup.card_map_of_injective hmk, hKc] at h
    rw [← h]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁L).toEquiv).symm
  have hcardP : ∀ (T : Type) [Group T] [Finite T], PU42 T → Nat.card L₁ ≤ Nat.card T := by
    intro T _ _ ⟨f⟩
    rw [hcL₁, Nat.card_congr f.toEquiv, card_QP45_eq]
  have hZ₁ : ∀ y ∈ L₁bar, (∀ w ∈ L₁bar, y * w = w * y) → y = 1 := by
    intro y hy hcomm
    have hσy : σ y ∈ (Lsub.comap co2P.subtype).map (MulAut.conj g).toMonoidHom := by
      rw [← hK]
      exact ⟨y, hy, rfl⟩
    apply σ.injective
    rw [map_one]
    refine hKZ (σ y) hσy fun w hw => ?_
    rw [← hK] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    change σ y * σ w' = σ w' * σ y
    rw [← map_mul, ← map_mul, hcomm w' hw']
  have hTL : T'.map σ.symm.toMonoidHom ≤ L₁bar := by
    have h3 := Subgroup.map_mono (f := σ.symm.toMonoidHom) hT'K
    rw [← hK, map_symm_map] at h3
    exact h3
  have hTel : IsElemAbelian 3 (T'.map σ.symm.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hT'el _
  have hTc : Nat.card (T'.map σ.symm.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (f := σ.symm.toMonoidHom) σ.symm.injective, hT'c]
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  exact false_of_terminal_comp hp hp2 h183 (downClosed_PU42 hKD) isoInv_PU42 hLK' hB hBN hmax hin
    hZL hEB hEC hEi hlE he hU hcG hcardP hL₁L hZ₁ hTL hTel hTc le_rfl

end PairCo2

section CensusAt

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem census_barHom_at (hp : p.Prime) {L B : Subgroup X}
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) {Q : Type} [Group Q]
    [Finite Q] (σ : (↥L ⧸ Subgroup.center ↥L) ≃* Q) {Good : ∀ (T : Type) [Group T], Prop}
    (hGood : Inputs2711c.IsoInv Good) (e : ↥B)
    (hcen : (∀ I : Subgroup Q,
        GLAPComponent p (Subgroup.centralizer ({σ (barHom hin e)} : Set Q)) I → Good (PSimple p I)) ∧
      (∀ I I' : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({σ (barHom hin e)} : Set Q)) I →
        GLAPComponent p (Subgroup.centralizer ({σ (barHom hin e)} : Set Q)) I' → I = I')) :
    (∀ J : Subgroup X, GLAPComponent p (L ⊓ Subgroup.centralizer ({(e : X)} : Set X)) J →
      Good (PSimple p J)) ∧
    (∀ J J' : Subgroup X, GLAPComponent p (L ⊓ Subgroup.centralizer ({(e : X)} : Set X)) J →
      GLAPComponent p (L ⊓ Subgroup.centralizer ({(e : X)} : Set X)) J' → J = J') := by
  obtain ⟨hG, hU⟩ := hcen
  refine ⟨fun J hJ => ?_, fun J J' hJ hJ' => ?_⟩
  · obtain ⟨h1, ⟨e1⟩⟩ := transfer_barHom hp hin e hJ
    obtain ⟨h2, ⟨e2⟩⟩ := Inputs1415.comp_transport hp σ h1
    exact hGood _ _ (e1.trans e2).symm (hG _ h2)
  · obtain ⟨h1, -⟩ := transfer_barHom hp hin e hJ
    obtain ⟨h1', -⟩ := transfer_barHom hp hin e hJ'
    obtain ⟨h2, -⟩ := Inputs1415.comp_transport hp σ h1
    obtain ⟨h2', -⟩ := Inputs1415.comp_transport hp σ h1'
    have h3 := hU _ _ h2 h2'
    have h4 := Subgroup.map_injective (f := σ.toMonoidHom) σ.injective h3
    exact eq_of_transfer_barHom hp hin e hJ hJ' h4

end CensusAt

section NormalQuasi

open CFSG.HardMathSupport.Dickson.I271

theorem comps_of_normal_quasisimple {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (P : Subgroup G)
    [Finite P] (x : ↥P) (J : Subgroup G)
    (hJC : J ≤ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P)
    (hJn : ∀ g ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P, ∀ l ∈ J, g * l * g⁻¹ ∈ J)
    (hq : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card ↥J)
    (hZ : IsPGroup p ↥(Subgroup.center ↥J))
    (hcent : ∀ c ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P, (∀ l ∈ J, l * c = c * l) →
      c ^ p = 1) :
    (∀ I : Subgroup ↥P, GLAPComponent p (Subgroup.centralizer ({x} : Set ↥P)) I →
      I = J.comap P.subtype) ∧
    Nonempty (PSimple p (J.comap P.subtype) ≃* (↥J ⧸ Subgroup.center ↥J)) := by
  have hJP : J ≤ P := fun l hl => (hJC hl).2
  set C' : Subgroup ↥P := Subgroup.centralizer ({x} : Set ↥P) with hC'
  set J' : Subgroup ↥P := J.comap P.subtype with hJ'
  have eJ : ↥J' ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJP
  have hq' : CFSG.Open.IsQuasisimple ↥J' :=
    CFSG.HardMathSupport.Timmesfeld.Proving.isQuasisimple_of_mulEquiv' eJ.symm hq
  have hp' : p ∣ Nat.card ↥J' := by rw [Nat.card_congr eJ.toEquiv]; exact hpJ
  have hmapC : C'.map P.subtype = Subgroup.centralizer ({(x : G)} : Set G) ⊓ P :=
    map_centralizer_subtype' P x
  have hgC : ∀ g ∈ C', (g : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := fun g hg => by
    have : (g : G) ∈ C'.map P.subtype := ⟨g, hg, rfl⟩
    rw [hmapC] at this
    exact this
  have hJC' : J' ≤ C' := by
    intro l hl
    have hl1 : (l : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := hJC hl
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hl1).1
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hc)
  have hJn' : ∀ g ∈ C', ∀ l ∈ J', g * l * g⁻¹ ∈ J' := by
    intro g hg l hl
    have h := hJn _ (hgC g hg) _ (show (l : G) ∈ J from hl)
    show ((g * l * g⁻¹ : ↥P) : G) ∈ J
    simpa using h
  have hcentP : IsPGroup p ↥(C' ⊓ Subgroup.centralizer (J' : Set ↥P)) := by
    intro c
    refine ⟨1, ?_⟩
    have hcC := hgC c.1 (Subgroup.mem_inf.1 c.2).1
    have hcomm : ∀ l ∈ J, l * ((c : ↥P) : G) = ((c : ↥P) : G) * l := by
      intro l hl
      have hlL : (⟨l, hJP hl⟩ : ↥P) ∈ J' := hl
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 c.2).2 _ hlL)
    have h0 := hcent _ hcC hcomm
    have h1 : (c : ↥P) ^ p = 1 := Subtype.ext (by simpa using h0)
    rw [pow_one]
    exact Subtype.ext h1
  have hcore : GLAPPrimeCore p ↥C' = ⊥ :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple hp hJC' hJn' hq' hp' hcentP
  have hZ' : IsPGroup p ↥(Subgroup.center ↥J') := by
    have ec : ↥(Subgroup.center ↥J') ≃* ↥(Subgroup.center ↥J) :=
      ((Subgroup.center ↥J').equivMapOfInjective eJ.toMonoidHom eJ.injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_center_eq eJ))
    exact hZ.of_equiv ec.symm
  have hLn : ∀ g ∈ J', ∀ l ∈ J', g * l * g⁻¹ ∈ J' := fun g hg l hl =>
    J'.mul_mem (J'.mul_mem hg hl) (J'.inv_mem hg)
  have hcore' : GLAPPrimeCore p ↥J' = ⊥ :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple hp le_rfl hLn hq' hp'
      (isPGroup_inf_centralizer_self J' hZ')
  have eq : (↥J' ⧸ Subgroup.center ↥J') ≃* (↥J ⧸ Subgroup.center ↥J) :=
    QuotientGroup.congr (Subgroup.center ↥J') (Subgroup.center ↥J) eJ (Subgroup.map_center_eq eJ)
  exact ⟨fun I hI =>
    eq_of_glaPComponent_of_normal_quasisimple hp hJC' hJn' hq' hcore hcentP hI,
    ⟨(pSimpleEquivCenterQuot J' hcore').trans eq⟩⟩

end NormalQuasi


section FreePair

theorem eq_zero_of_fpf_pair {G V : Type} [Group G] [AddCommGroup V] (act : G → V → V)
    (hmul : ∀ g h v, act (g * h) v = act g (act h v)) (hone : ∀ v, act 1 v = v)
    (hadd : ∀ g u w, act g (u + w) = act g u + act g w) (h2 : ∀ v : V, v + v = 0) {a b : G}
    (hab : a * b = b * a) (ha3 : a * a * a = 1) (hb3 : b * b * b = 1)
    (hfa : ∀ v, act a v = v → v = 0) (hfb : ∀ v, act b v = v → v = 0)
    (hfab : ∀ v, act (a * b) v = v → v = 0) (hfabb : ∀ v, act (a * b * b) v = v → v = 0)
    (v : V) : v = 0 := by
  have hsum : ∀ g : G, g * g * g = 1 → (∀ v, act g v = v → v = 0) →
      ∀ u, u + act g u + act g (act g u) = 0 := by
    intro g hg3 hg u
    apply hg
    rw [hadd, hadd]
    have h3 : act g (act g (act g u)) = u := by
      rw [← hmul g g (act g u), ← hmul (g * g) g u, hg3, hone]
    rw [h3]
    abel
  have hc : Commute a b := hab
  have hba : b * b * a = a * (b * b) := by
    rw [mul_assoc, ← hab, ← mul_assoc, ← hab, mul_assoc]
  have hab3 : a * b * (a * b) * (a * b) = 1 := by
    rw [← pow_three', hc.mul_pow, pow_three', pow_three', ha3, hb3, one_mul]
  have habb3 : a * b * b * (a * b * b) * (a * b * b) = 1 := by
    rw [← pow_three', mul_assoc a b b, (hc.mul_right hc).mul_pow, pow_three' a, ha3, one_mul,
      pow_three', show b * b * (b * b) * (b * b) = (b * b * b) * (b * b * b) by group, hb3, one_mul]
  have e1 := hsum a ha3 hfa v
  have e2 := hsum a ha3 hfa (act b v)
  have e3 := hsum a ha3 hfa (act b (act b v))
  have e4 := hsum b hb3 hfb v
  have e5 := hsum (a * b) hab3 hfab v
  have e6 := hsum (a * b * b) habb3 hfabb v
  have r5 : act (a * b) (act (a * b) v) = act a (act a (act b (act b v))) := by
    rw [← hmul (a * b) (a * b) v, ← hmul b b v, ← hmul a (b * b) v, ← hmul a (a * (b * b)) v]
    congr 1
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = a * (a * (b * b)) := by group
  have r6 : act (a * b * b) (act (a * b * b) v) = act a (act a (act b v)) := by
    rw [← hmul (a * b * b) (a * b * b) v, ← hmul a b v, ← hmul a (a * b) v]
    congr 1
    calc a * b * b * (a * b * b) = a * (b * b * a) * (b * b) := by group
      _ = a * (a * (b * b)) * (b * b) := by rw [hba]
      _ = a * (a * (b * b * b * b)) := by group
      _ = a * (a * b) := by rw [hb3, one_mul]
  have r5' : act (a * b) v = act a (act b v) := hmul a b v
  have r6' : act (a * b * b) v = act a (act b (act b v)) := by
    rw [hmul (a * b) b v, hmul a b (act b v)]
  rw [r5, r5'] at e5
  rw [r6, r6'] at e6
  have hS1 : (v + act a v + act a (act a v)) + (act b v + act a (act b v) + act a (act a (act b v))) +
      (act b (act b v) + act a (act b (act b v)) + act a (act a (act b (act b v)))) = 0 := by
    rw [e1, e2, e3, zero_add, zero_add]
  have hS2 : (v + act a v + act a (act a v)) + (v + act b v + act b (act b v)) +
      (v + act a (act b v) + act a (act a (act b (act b v)))) +
      (v + act a (act b (act b v)) + act a (act a (act b v))) = 0 := by
    rw [e1, e4, e5, e6, zero_add, zero_add, zero_add]
  have hS : v + v + v + v + (v + act a v + act a (act a v) + act b v + act a (act b v) +
      act a (act a (act b v)) + act b (act b v) + act a (act b (act b v)) +
      act a (act a (act b (act b v)))) = v + act a v + act a (act a v) + act b v + act a (act b v) +
      act a (act a (act b v)) + act b (act b v) + act a (act b (act b v)) +
      act a (act a (act b (act b v))) := by
    have h3 : v + v + v + v = 0 := by rw [h2 v, zero_add, h2 v]
    rw [h3, zero_add]
  have hT : v + v + v + v + (v + act a v + act a (act a v) + act b v + act a (act b v) +
      act a (act a (act b v)) + act b (act b v) + act a (act b (act b v)) +
      act a (act a (act b (act b v)))) = v := by
    have : v + v + v + v + (v + act a v + act a (act a v) + act b v + act a (act b v) +
        act a (act a (act b v)) + act b (act b v) + act a (act b (act b v)) +
        act a (act a (act b (act b v)))) = v + ((v + act a v + act a (act a v)) +
          (v + act b v + act b (act b v)) + (v + act a (act b v) + act a (act a (act b (act b v)))) +
          (v + act a (act b (act b v)) + act a (act a (act b v)))) := by abel
    rw [this, hS2, add_zero]
  have hU : v + act a v + act a (act a v) + act b v + act a (act b v) + act a (act a (act b v)) +
      act b (act b v) + act a (act b (act b v)) + act a (act a (act b (act b v))) = 0 := by
    have : v + act a v + act a (act a v) + act b v + act a (act b v) + act a (act a (act b v)) +
        act b (act b v) + act a (act b (act b v)) + act a (act a (act b (act b v))) =
        (v + act a v + act a (act a v)) + (act b v + act a (act b v) + act a (act a (act b v))) +
          (act b (act b v) + act a (act b (act b v)) + act a (act a (act b (act b v)))) := by abel
    rw [this, hS1]
  rw [hS, hU] at hT
  exact hT.symm

theorem fpf_conj_of {G V : Type} [Group G] [AddCommGroup V] (act : G → V → V)
    (hmul : ∀ g h v, act (g * h) v = act g (act h v)) (hone : ∀ v, act 1 v = v)
    (hzero : ∀ g, act g 0 = 0) {g x : G} (hx : ∀ v, act x v = v → v = 0) :
    ∀ v, act (g * x * g⁻¹) v = v → v = 0 := by
  intro v hv
  have h1 : act x (act g⁻¹ v) = act g⁻¹ v := by
    have h2 : act g⁻¹ (act (g * x * g⁻¹) v) = act g⁻¹ v := by rw [hv]
    rw [← hmul] at h2
    rw [← hmul, ← h2]
    congr 1
    group
  have h3 : v = act g (act g⁻¹ v) := by
    rw [← hmul, mul_inv_cancel, hone]
  rw [h3, hx _ h1, hzero]

end FreePair

section Co1Dich

@[expose] def Co1Dich (Q : Type) [Group Q] (act : Q → (Fin 24 → ZMod 2) → (Fin 24 → ZMod 2)) :
    Prop :=
  ∀ t : Q, orderOf t = 3 → 3 ^ 6 ∣ Nat.card (Subgroup.centralizer ({t} : Set Q)) →
    (∃ I : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({t} : Set Q)) I) →
    (∃ g x : Q, t = g * x * g⁻¹ ∧ ∀ v, act x v = v → v = 0) ∨
      ((∀ I : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({t} : Set Q)) I →
          PX₀ (PSimple 3 I)) ∧
        (∀ I I' : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({t} : Set Q)) I →
          GLAPComponent 3 (Subgroup.centralizer ({t} : Set Q)) I' → I = I'))

theorem Co1Dich.of_equiv {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q'] (e : Q ≃* Q')
    {act : Q → (Fin 24 → ZMod 2) → (Fin 24 → ZMod 2)}
    {act' : Q' → (Fin 24 → ZMod 2) → (Fin 24 → ZMod 2)}
    (hact : ∀ g v, act' (e g) v = act g v) (h : Co1Dich Q act) : Co1Dich Q' act' := by
  intro t' hto' h6' hI'
  set t := e.symm t' with htdef
  have het : e t = t' := e.apply_symm_apply t'
  have hto : orderOf t = 3 := by
    have h1 : orderOf (e t) = orderOf t := MulEquiv.orderOf_eq e t
    rw [het] at h1
    rw [← h1, hto']
  have hmap : (Subgroup.centralizer ({t} : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ({t'} : Set Q') := by
    rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton e t, het]
  have hmap' : (Subgroup.centralizer ({t'} : Set Q')).map e.symm.toMonoidHom =
      Subgroup.centralizer ({t} : Set Q) := by
    rw [← hmap, map_symm_map]
  have h6 : 3 ^ 6 ∣ Nat.card (Subgroup.centralizer ({t} : Set Q)) := by
    rw [← hmap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at h6'
    exact h6'
  have hI : ∃ I : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({t} : Set Q)) I := by
    obtain ⟨I', hI'⟩ := hI'
    have h1 := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three e.symm hI'
    rw [hmap'] at h1
    exact ⟨_, h1⟩
  rcases h t hto h6 hI with hf | ⟨hG, hU⟩
  · left
    obtain ⟨g, x, hgx, hx⟩ := hf
    refine ⟨e g, e x, ?_, fun v hv => hx v (by rw [← hact]; exact hv)⟩
    rw [← het, hgx, map_mul, map_mul, map_inv]
  · right
    refine ⟨fun I' hI' => ?_, fun I' I'' hI' hI'' => ?_⟩
    · have h1 := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three e.symm hI'
      rw [hmap'] at h1
      obtain ⟨f⟩ := hG _ h1
      have e1 : PSimple 3 I' ≃* PSimple 3 (I'.map e.symm.toMonoidHom) :=
        CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3 (e.symm.subgroupMap I')
      exact ⟨e1.trans f⟩
    · have h1 := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three e.symm hI'
      have h2 := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three e.symm hI''
      rw [hmap'] at h1 h2
      exact Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective (hU _ _ h1 h2)

end Co1Dich

section PairCo1

open CFSG.Sporadic.Co1Schreier (GA GL24 MRep finite_GA)
open CFSG.Sporadic.Co1Block (co1MatEquiv)
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)

@[expose] def gaAct (g : ↥GA) (v : Fin 24 → ZMod 2) : Fin 24 → ZMod 2 :=
  Matrix.mulVec ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) v

theorem gaAct_mul (g h : ↥GA) (v : Fin 24 → ZMod 2) : gaAct (g * h) v = gaAct g (gaAct h v) := by
  unfold gaAct
  rw [Matrix.mulVec_mulVec, Subgroup.coe_mul, Units.val_mul]

theorem gaAct_one (v : Fin 24 → ZMod 2) : gaAct 1 v = v := by
  unfold gaAct
  rw [Subgroup.coe_one, Units.val_one]
  exact Matrix.one_mulVec v

theorem gaAct_zero (g : ↥GA) : gaAct g 0 = 0 := by
  unfold gaAct
  exact Matrix.mulVec_zero _

theorem co1_six_le_pRank :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥GA) := by
  haveI : Finite ↥GA := finite_GA
  have hTc : Nat.card CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.eSplit.T = 3 ^ 6 := by
    rw [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.SplitData.T, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.eSplit.φ_injective,
      Subgroup.card_top, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.card_vec,
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.aGA_length]
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.eSplit.T_elemAbelian hTc


theorem co1Dich_GA : Co1Dich ↥GA gaAct := by
  haveI : Finite ↥GA := finite_GA
  intro t hto h6 hI
  obtain ⟨g, x', hy, hcases⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.tabCo1_census_three t hto
  have hC : Subgroup.centralizer ({t} : Set ↥GA) =
      (Subgroup.centralizer ({x'} : Set ↥GA)).map (MulAut.conj g).toMonoidHom := by
    rw [hy]
    exact centralizer_conj_eq' g x'
  have hC' : (Subgroup.centralizer ({t} : Set ↥GA)).map (MulAut.conj g).symm.toMonoidHom =
      Subgroup.centralizer ({x'} : Set ↥GA) := by
    rw [hC, map_symm_map]
  have hcard : Nat.card (Subgroup.centralizer ({t} : Set ↥GA)) =
      Nat.card (Subgroup.centralizer ({x'} : Set ↥GA)) := by
    rw [hC, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  rcases hcases with h | h | h | h
  ·
    exfalso
    obtain ⟨I, hI⟩ := hI
    have hc := CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_map (MulAut.conj g)
      (CFSG.HardMathSupport.Dickson.I271.TabCo1.tabCo1_threeC x' h)
    rw [← hC] at hc
    exact CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape Nat.prime_three hc hI
  ·
    right
    obtain ⟨J, hJC, hJn, hq, hp3, hZ3, hcent, ⟨eJ⟩⟩ :=
      CFSG.HardMathSupport.Dickson.I271.TabCo1.threeB_data h
    obtain ⟨hU, ⟨eP⟩⟩ := comps_of_normal_quasisimple Nat.prime_three GA x' J hJC hJn hq hp3 hZ3 hcent
    have hcomp : ∀ I : Subgroup ↥GA, GLAPComponent 3 (Subgroup.centralizer ({t} : Set ↥GA)) I →
        I.map (MulAut.conj g).symm.toMonoidHom = J.comap GA.subtype := by
      intro I hI
      have h1 := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three
        (MulAut.conj g).symm hI
      rw [hC'] at h1
      exact hU _ h1
    refine ⟨fun I hI => ?_, fun I I' hI hI' => ?_⟩
    · have e1 : PSimple 3 I ≃* PSimple 3 (I.map (MulAut.conj g).symm.toMonoidHom) :=
        CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3 ((MulAut.conj g).symm.subgroupMap I)
      rw [hcomp I hI] at e1
      exact ⟨(e1.trans eP).trans eJ⟩
    · exact Subgroup.map_injective (f := (MulAut.conj g).symm.toMonoidHom)
        (MulAut.conj g).symm.injective ((hcomp I hI).trans (hcomp I' hI').symm)
  ·
    exfalso
    obtain ⟨-, -, hxy, hM, hy1⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.moore_data h
    have hpres := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 9)
      (by norm_num) CFSG.HardMathSupport.Dickson.I271.TabCo1.mooreM hM).2.2.2.2.2 (by norm_num)
      ⟨1, ⟨le_rfl, by norm_num⟩, hy1⟩
    obtain ⟨-, ⟨e⟩⟩ := hpres
    have hAC : Subgroup.closure
        (CFSG.HardMathSupport.Dickson.I271.TabCo1.mooreM '' Set.Icc 1 (9 - 2)) ≤
        Subgroup.centralizer ({(x' : GL24)} : Set GL24) ⊓ GA := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨j, ⟨hj1, hj7⟩, rfl⟩
      exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (hxy j hj1 (by omega)).symm,
        CFSG.HardMathSupport.Dickson.I271.TabCo1.mooreM_mem j⟩
    obtain ⟨-, -, hcardA⟩ := CFSG.HardMathSupport.Dickson.I271.alt9_subgroup_data e
    have hle := CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeDRoot.card_cent_threeD_root_le x' h
    have heq := CFSG.HardMathSupport.Dickson.I271.TabCo1.card_centralizer_GA_eq_inf GA x'
    have hdvd : 181440 ∣ Nat.card (Subgroup.centralizer ({x'} : Set ↥GA)) := by
      rw [heq, ← hcardA]
      exact Subgroup.card_dvd_of_le hAC
    have hpos : 0 < Nat.card (Subgroup.centralizer ({x'} : Set ↥GA)) := Nat.card_pos
    obtain ⟨k, hk⟩ := hdvd
    rw [hcard, hk] at h6
    rw [hk] at hle hpos
    have hk3 : k ≤ 3 := by omega
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0] at hpos
        omega
      · exact h0
    interval_cases k <;> norm_num at h6
  ·
    left
    have hfix : ∀ v, gaAct x' v = v → v = 0 := by
      intro v hv
      have hn := CFSG.Sporadic.Co1.Module.Odd.ncard_fixedSet
        [CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech.threeARows ()]
      obtain ⟨w, hw⟩ :=
        Set.ncard_eq_one.1 (hn.trans CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech.fix_counts.2.2.2)
      have hset : ∀ u : Fin 24 → ZMod 2, gaAct x' u = u →
          u ∈ {w : Fin 24 → ZMod 2 | ∀ M ∈ [CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech.threeARows ()],
            Matrix.mulVec (CFSG.Sporadic.SmallF2.rowsMatrix 24 M) w = w} := by
        intro u hu M hM
        rw [List.mem_singleton.1 hM]
        exact (congrArg (fun A => Matrix.mulVec A u) h).trans hu
      have h0 := hset 0 (gaAct_zero x')
      have hv' := hset v hv
      rw [hw, Set.mem_singleton_iff] at h0 hv'
      exact hv'.trans h0.symm
    exact ⟨g, x', hy, hfix⟩

@[expose] noncomputable def co1GAEquiv : ↥GA ≃* CFSG.Blueprint.NativeSporadic.Carrier .Co1 :=
  co1MatEquiv.symm

@[expose] noncomputable def co1VAct (y : CFSG.Blueprint.NativeSporadic.Carrier .Co1)
    (v : Fin 24 → ZMod 2) : Fin 24 → ZMod 2 :=
  gaAct (co1GAEquiv.symm y) v

theorem co1VAct_mul (y z : CFSG.Blueprint.NativeSporadic.Carrier .Co1) (v : Fin 24 → ZMod 2) :
    co1VAct (y * z) v = co1VAct y (co1VAct z v) := by
  unfold co1VAct
  rw [map_mul, gaAct_mul]

theorem co1VAct_one (v : Fin 24 → ZMod 2) : co1VAct 1 v = v := by
  unfold co1VAct
  rw [map_one, gaAct_one]

theorem co1VAct_add (y : CFSG.Blueprint.NativeSporadic.Carrier .Co1) (u w : Fin 24 → ZMod 2) :
    co1VAct y (u + w) = co1VAct y u + co1VAct y w := by
  unfold co1VAct gaAct
  exact Matrix.mulVec_add _ u w

theorem co1VAct_zero (y : CFSG.Blueprint.NativeSporadic.Carrier .Co1) : co1VAct y 0 = 0 := by
  unfold co1VAct gaAct
  exact Matrix.mulVec_zero _

theorem co1VAct_fpf_conj {g x : CFSG.Blueprint.NativeSporadic.Carrier .Co1}
    (hx : ∀ v, co1VAct x v = v → v = 0) : ∀ v, co1VAct (g * x * g⁻¹) v = v → v = 0 :=
  fpf_conj_of co1VAct co1VAct_mul co1VAct_one co1VAct_zero hx

theorem co1Dich_carrier [Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co1)] :
    Co1Dich (CFSG.Blueprint.NativeSporadic.Carrier .Co1) co1VAct := by
  haveI : Finite ↥GA := finite_GA
  exact @Co1Dich.of_equiv ↥GA (CFSG.Blueprint.NativeSporadic.Carrier .Co1) (Subgroup.toGroup GA)
    finite_GA _ _ co1GAEquiv gaAct co1VAct
    (fun g v => by unfold co1VAct; rw [MulEquiv.symm_apply_apply]) co1Dich_GA

theorem co1_six_le_pRank_carrier [Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co1)] :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Co1)) := by
  haveI : Finite ↥GA := finite_GA
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥GA) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Co1)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) co1GAEquiv
  exact h2 ▸ co1_six_le_pRank


theorem sporPairCase_Co1_three (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) (hb : LieOrderBridge)
    (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2) :
    Inputs2711c.SporPairCase .Co1 3 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN hmax _ _ _ _ hC1 hname hin J0 hJ0 hJt _ E hEB hEC hEi hEl hE2
    _ hle
  exfalso
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co1) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .Co1 (by decide)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZL : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := not_dvd_card_center hSpM hLq hname (by decide)
  have hname' := hname
  obtain ⟨eS⟩ := hname'
  obtain ⟨bC⟩ := hBr .Co1
  let σ : (↥L ⧸ Subgroup.center ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .Co1 := eS.trans bC.symm
  have hrk : 6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) σ]
    exact co1_six_le_pRank_carrier
  have hdich : ∀ f : X, ∀ hf : f ∈ E, f ∉ Subgroup.centralizer (L : Set X) →
      (∀ v, co1VAct (σ (barHom hin ⟨f, hEB hf⟩)) v = v → v = 0) ∨
      ((∀ I : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Co1),
          GLAPComponent 3 (Subgroup.centralizer ({σ (barHom hin ⟨f, hEB hf⟩)} : Set (CFSG.Blueprint.NativeSporadic.Carrier .Co1))) I →
            PX₀ (PSimple 3 I)) ∧
        (∀ I I' : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Co1),
          GLAPComponent 3 (Subgroup.centralizer ({σ (barHom hin ⟨f, hEB hf⟩)} : Set (CFSG.Blueprint.NativeSporadic.Carrier .Co1))) I →
          GLAPComponent 3 (Subgroup.centralizer ({σ (barHom hin ⟨f, hEB hf⟩)} : Set (CFSG.Blueprint.NativeSporadic.Carrier .Co1))) I' →
            I = I')) := by
    intro f hf hfC
    set t := barHom hin ⟨f, hEB hf⟩ with ht
    have ht1 : σ t ≠ 1 := fun h =>
      hfC ((barHom_eq_one_iff hin ⟨f, hEB hf⟩).1 (σ.injective (h.trans (map_one σ).symm)))
    have ht3 : σ t ^ 3 = 1 := by
      rw [← map_pow, (isElemAbelian_range_barHom hB hin).2 _ ⟨⟨f, hEB hf⟩, rfl⟩, map_one]
    have hmapt := CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton σ t
    have h6 : 3 ^ 6 ∣ Nat.card (Subgroup.centralizer ({σ t} : Set (CFSG.Blueprint.NativeSporadic.Carrier .Co1))) := by
      rw [← hmapt, Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective]
      exact (Nat.pow_dvd_pow 3 hrk).trans
        (pow_pRank_dvd_card_centralizer hp hB hmax hin hZL ⟨f, hEB hf⟩)
    have hI : ∃ I : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Co1), GLAPComponent 3 (Subgroup.centralizer ({σ t} : Set (CFSG.Blueprint.NativeSporadic.Carrier .Co1))) I := by
      obtain ⟨I, hI⟩ := exists_glaPComponent_barHom hp hin ⟨f, hEB hf⟩ (hle f hf)
      refine ⟨I.map σ.toMonoidHom, ?_⟩
      rw [← hmapt]
      exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ hI
    rcases co1Dich_carrier _ (orderOf_eq_prime ht3 ht1) h6 hI with ⟨g, x, hgx, hx⟩ | h
    · left
      rw [hgx]
      exact co1VAct_fpf_conj hx
    · exact Or.inr h
  by_cases hA : ∃ f : X, ∃ hf : f ∈ E, f ∉ Subgroup.centralizer (L : Set X) ∧
      ((∀ I : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Co1),
          GLAPComponent 3 (Subgroup.centralizer ({σ (barHom hin ⟨f, hEB hf⟩)} : Set (CFSG.Blueprint.NativeSporadic.Carrier .Co1))) I →
            PX₀ (PSimple 3 I)) ∧
        (∀ I I' : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Co1),
          GLAPComponent 3 (Subgroup.centralizer ({σ (barHom hin ⟨f, hEB hf⟩)} : Set (CFSG.Blueprint.NativeSporadic.Carrier .Co1))) I →
          GLAPComponent 3 (Subgroup.centralizer ({σ (barHom hin ⟨f, hEB hf⟩)} : Set (CFSG.Blueprint.NativeSporadic.Carrier .Co1))) I' →
            I = I'))
  ·
    obtain ⟨e, he, heC, hcen⟩ := hA
    obtain ⟨hcG, hcU⟩ := census_barHom_at hp hin σ isoInv_PX₀ ⟨e, hEB he⟩ hcen
    have hEel : IsElemAbelian 3 E := isElemAbelian_mono hB hEB
    obtain ⟨D, hDE, heD, hDc⟩ := exists_card_sq hp hEel hE2 he
    have hDel : IsElemAbelian 3 D := isElemAbelian_mono hEel hDE
    have hD2r : 2 ≤ CFSG.Open.pRank 3 D := (pRank_eq_two hp hDel hDc).ge
    have hDC : ¬ D ≤ Subgroup.centralizer (L : Set X) := fun h => heC (h heD)
    have hpS : 3 ∣ sporOrd .Co1 := by simp only [sporOrd, CFSG.Open.orderCo1]; norm_num
    have h12 : ¬ sporOrd .Co1 ∣ Nat.factorial 12 := fun h =>
      absurd (Nat.le_of_dvd (Nat.factorial_pos 12) h)
        (by simp only [sporOrd, CFSG.Open.orderCo1]; norm_num [Nat.factorial])
    obtain ⟨J, hJL, hJ⟩ := exists_jD hp hp2 h183 hD2 hSpM hOrd hpS h12 hLK hLq hB hBN hname hJ0 hJt
      hEB hEl hDE hD2r hDC
    have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
    obtain ⟨fJ⟩ : PX₀ (PSimple 3 J) :=
      typeClosure_of_unique hp hp2 (downClosed_PX₀ hKD) isoInv_PX₀ h183 hLK' hDel
        (hDE.trans (hEB.trans hBN)) heD hcG hcU hJL
    have hcardJ : Nat.card (PSimple 3 J) = 3265920 :=
      (Nat.card_congr fJ.toEquiv).trans CFSG.LieType.Multipliers.U43.card_X₀
    rcases hJ with ⟨hA', -⟩ | hsmall
    · exact Inputs2711c.not_altOrChevTwo_U43 hb hcardJ hA'
    · rw [hcardJ] at hsmall
      rcases hsmall with h | h | h | h <;> exact absurd h (by decide)
  ·
    have hfpf : ∀ f : X, ∀ hf : f ∈ E, f ∉ Subgroup.centralizer (L : Set X) →
        ∀ v, co1VAct (σ (barHom hin ⟨f, hEB hf⟩)) v = v → v = 0 := fun f hf hfC =>
      (hdich f hf hfC).resolve_right fun h => hA ⟨f, hf, hfC, h⟩
    have hinE : ∀ b ∈ E, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X) :=
      fun b hb => hin b (hEB hb)
    have hbar : ∀ f : ↥E, barHom hinE f = barHom hin ⟨f, hEB f.2⟩ := fun f =>
      mk_eq_of_inner (kOf_spec hinE f) (kOf_spec hin ⟨f, hEB f.2⟩)
    have hEel : IsElemAbelian 3 E := isElemAbelian_mono hB hEB
    set R := (barHom hinE).range with hR
    have hRel : IsElemAbelian 3 R := isElemAbelian_range_barHom hEel hinE
    have hRc : 9 < Nat.card R := by
      have h1 := card_range_barHom_mul hinE
      have hEq : E ⊓ Subgroup.centralizer (L : Set X) = B ⊓ Subgroup.centralizer (L : Set X) :=
        le_antisymm (inf_le_inf_right _ hEB) (le_inf hEC inf_le_right)
      rw [hEq] at h1
      have h2 := pow_pRank_mul_le hp hB hmax hZL
      have h3 := CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_centerQuotient_le_of_not_dvd hp hZL
      have h4 : 3 ^ 6 ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
        Nat.pow_le_pow_right (by norm_num) (hrk.trans h3)
      have hb0 : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) := Nat.card_pos
      have h5 : 3 ^ 6 * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) ≤
          3 ^ 2 * (Nat.card R * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X))) := by
        rw [h1]
        exact (Nat.mul_le_mul_right _ h4).trans (h2.trans hEi)
      have h6 : 3 ^ 6 ≤ 3 ^ 2 * Nat.card R := by
        rw [← mul_assoc] at h5
        exact Nat.le_of_mul_le_mul_right h5 hb0
      omega
    obtain ⟨r, hrR, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
      by_contra h
      push Not at h
      have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).2 h
      rw [this, Subgroup.card_bot] at hRc
      omega
    obtain ⟨s, hsR, hsr⟩ : ∃ s ∈ R, s ∉ Subgroup.zpowers r := by
      by_contra h
      push Not at h
      have h1 := Subgroup.card_le_of_le (show R ≤ Subgroup.zpowers r from h)
      rw [Nat.card_zpowers] at h1
      have h2 : orderOf r ≤ 3 :=
        Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hRel.2 r hrR))
      omega
    obtain ⟨a, rfl⟩ := hrR
    obtain ⟨b, rfl⟩ := hsR
    have hne : ∀ u : ↥E, barHom hinE u ≠ 1 → (u : X) ∉ Subgroup.centralizer (L : Set X) :=
      fun u hu hC => hu ((barHom_eq_one_iff hinE u).2 hC)
    have hfree : ∀ u : ↥E, barHom hinE u ≠ 1 → ∀ v, co1VAct (σ (barHom hinE u)) v = v → v = 0 := by
      intro u hu
      rw [hbar u]
      exact hfpf u u.2 (hne u hu)
    have hs1 : barHom hinE b ≠ 1 := fun h => hsr (h ▸ Subgroup.one_mem _)
    have hab1 : barHom hinE (a * b) ≠ 1 := by
      rw [map_mul]
      intro h
      apply hsr
      rw [eq_inv_of_mul_eq_one_right h]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    have hb3 : barHom hinE b * barHom hinE b * barHom hinE b = 1 := by
      rw [← pow_three']
      exact hRel.2 _ ⟨b, rfl⟩
    have ha3 : barHom hinE a * barHom hinE a * barHom hinE a = 1 := by
      rw [← pow_three']
      exact hRel.2 _ ⟨a, rfl⟩
    have habb1 : barHom hinE (a * b * b) ≠ 1 := by
      rw [map_mul, map_mul]
      intro h
      apply hsr
      have h2 : barHom hinE b * barHom hinE b = (barHom hinE a)⁻¹ := by
        rw [mul_assoc] at h
        exact eq_inv_of_mul_eq_one_right h
      have h3 : barHom hinE b =
          (barHom hinE b * barHom hinE b) * (barHom hinE b * barHom hinE b) := by
        calc barHom hinE b = (barHom hinE b * barHom hinE b * barHom hinE b) * barHom hinE b := by
              rw [hb3, one_mul]
          _ = _ := by group
      rw [h3, h2]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
    have hcommR : barHom hinE a * barHom hinE b = barHom hinE b * barHom hinE a :=
      congrArg Subtype.val (hRel.1.1.1 ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨b, rfl⟩⟩)
    have hcomm : σ (barHom hinE a) * σ (barHom hinE b) = σ (barHom hinE b) * σ (barHom hinE a) := by
      rw [← map_mul σ, ← map_mul σ, hcommR]
    have hσa3 : σ (barHom hinE a) * σ (barHom hinE a) * σ (barHom hinE a) = 1 := by
      rw [← map_mul σ, ← map_mul σ, ha3, map_one]
    have hσb3 : σ (barHom hinE b) * σ (barHom hinE b) * σ (barHom hinE b) = 1 := by
      rw [← map_mul σ, ← map_mul σ, hb3, map_one]
    have hfab : ∀ v, co1VAct (σ (barHom hinE a) * σ (barHom hinE b)) v = v → v = 0 := by
      have h := hfree (a * b) hab1
      rwa [map_mul, map_mul] at h
    have hfabb : ∀ v, co1VAct (σ (barHom hinE a) * σ (barHom hinE b) * σ (barHom hinE b)) v = v →
        v = 0 := by
      have h := hfree (a * b * b) habb1
      rwa [map_mul, map_mul, map_mul, map_mul] at h
    have h0 := eq_zero_of_fpf_pair co1VAct co1VAct_mul co1VAct_one co1VAct_add
      (fun v => funext fun i => CharTwo.add_self_eq_zero (v i))
      hcomm hσa3 hσb3 (hfree a hr1) (hfree b hs1) hfab hfabb (Pi.single 0 1)
    have h1 := congrFun h0 0
    simp at h1

end PairCo1

section Fi24Tools

open CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

theorem comps_of_simple_pindex {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) {t : Q}
    (L : Subgroup Q) (hLC : L ≤ Subgroup.centralizer ({t} : Set Q))
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    {k : ℕ} (hk : Nat.card ↥(Subgroup.centralizer ({t} : Set Q)) = Nat.card ↥L * p ^ k)
    (hfac : (p ^ k).factorial < Nat.card ↥(Subgroup.centralizer ({t} : Set Q))) :
    GLAPComponent p (Subgroup.centralizer ({t} : Set Q)) L ∧
      ∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({t} : Set Q)) I → I = L := by
  set C : Subgroup Q := Subgroup.centralizer ({t} : Set Q) with hCdef
  let E : Subgroup ↥C := L.subgroupOf C
  have eL : ↥E ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  have hEmap : E.map C.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLC
  haveI hsE' : IsSimpleGroup ↥E := eL.isSimpleGroup_congr.2 hs
  have hcardE : Nat.card ↥E = Nat.card ↥L := Nat.card_congr eL.toEquiv
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  have hidx : E.index = p ^ k := by
    have h1 : E.index * Nat.card ↥E = Nat.card ↥C := Subgroup.index_mul_card E
    rw [hcardE, hk] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])
  haveI hEn : E.Normal := normal_of_isSimple_of_index E hidx (pow_ne_zero k hp.ne_zero) hfac
  have hq : IsPGroup p (↥C ⧸ E) := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact IsPGroup.of_card (n := k) hidx
  haveI := hs
  have hZL : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_nonab hnab
  have hZ : Subgroup.center ↥(E.map C.subtype) = ⊥ := by
    rw [hEmap]
    exact hZL
  have hcent := isPGroup_inf_centralizer_of_normal_index E hZ hq
  rw [hEmap] at hcent
  have hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    have hl' : (⟨l, hLC hl⟩ : ↥C) ∈ E := hl
    have h2 := hEn.conj_mem _ hl' ⟨g, hg⟩
    exact h2
  have hLq : CFSG.Open.IsQuasisimple ↥L := isQuasisimple_of_simple_nonab hnab
  have hcore : GLAPPrimeCore p ↥C = ⊥ :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple hp hLC hLn hLq hpL hcent
  exact ⟨glaPComponent_of_normal_quasisimple hLC hLn hLq hcore,
    fun I hI => eq_of_glaPComponent_of_normal_quasisimple hp hLC hLn hLq hcore hcent hI⟩

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem exists_mem_B0_of_card_center (hp : p.Prime) {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hZ : Nat.card (Subgroup.center ↥L) = p) :
    ∃ z ∈ B ⊓ Subgroup.centralizer (L : Set X), z ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hcyc : IsCyclic (Subgroup.center ↥L) := isCyclic_of_prime_card hZ
  obtain ⟨z₀, hz₀⟩ := hcyc.exists_generator
  set z : X := ((z₀ : ↥L) : X) with hzdef
  have hord₀ : orderOf z₀ = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hz₀, hZ]
  have hord : orderOf z = p := by
    rw [hzdef, orderOf_submonoid, orderOf_submonoid, hord₀]
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact hp.one_lt.ne' hord.symm
  have hzp : z ^ p = 1 := hord ▸ pow_orderOf_eq_one z
  have hzL : z ∈ L := (z₀ : ↥L).2
  have hzC : z ∈ Subgroup.centralizer (L : Set X) := mem_centralizer_of_mem_center z₀.2
  have hconj : ∀ b ∈ B, ∃ n : ℤ, b * z * b⁻¹ = z ^ n := by
    intro b hb
    have hwL : b * z * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hBN hb) z).1 hzL
    have hwZ : (⟨b * z * b⁻¹, hwL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have hl' : b⁻¹ * (l : X) * b ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hBN hb)) l).1 l.2
        simpa using this
      have hc : (b⁻¹ * (l : X) * b) * z = z * (b⁻¹ * (l : X) * b) :=
        Subgroup.mem_centralizer_iff.1 hzC _ hl'
      show (l : X) * (b * z * b⁻¹) = (b * z * b⁻¹) * l
      calc (l : X) * (b * z * b⁻¹) = b * ((b⁻¹ * l * b) * z) * b⁻¹ := by group
        _ = b * (z * (b⁻¹ * l * b)) * b⁻¹ := by rw [hc]
        _ = (b * z * b⁻¹) * l := by group
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hz₀ ⟨_, hwZ⟩)
    refine ⟨n, ?_⟩
    have := congrArg (fun w : ↥(Subgroup.center ↥L) => ((w : ↥L) : X)) hn
    simp only [SubgroupClass.coe_zpow] at this
    exact this.symm
  have hcomm : ∀ b ∈ B, b * z = z * b := by
    intro b hb
    obtain ⟨n, hn⟩ := hconj b hb
    have hiter : ∀ j : ℕ, b ^ j * z * (b ^ j)⁻¹ = z ^ (n ^ j) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc b ^ (j + 1) * z * (b ^ (j + 1))⁻¹ = b * (b ^ j * z * (b ^ j)⁻¹) * b⁻¹ := by group
          _ = b * z ^ (n ^ j) * b⁻¹ := by rw [ih]
          _ = (b * z * b⁻¹) ^ (n ^ j) := by
              rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
          _ = (z ^ n) ^ (n ^ j) := by rw [hn]
          _ = z ^ (n ^ (j + 1)) := by rw [← zpow_mul, pow_succ, mul_comm]
    have hbp : b ^ p = 1 := hB.2 b hb
    have h1 : z ^ (n ^ p) = z := by
      have := hiter p
      rw [hbp] at this
      simpa using this.symm
    have h2 : z ^ (n ^ p - 1) = 1 := by
      rw [zpow_sub, h1, zpow_one, mul_inv_cancel]
    have h3 : (p : ℤ) ∣ n ^ p - 1 := by
      have := orderOf_dvd_iff_zpow_eq_one.2 h2
      rwa [hord] at this
    have h4 : (p : ℤ) ∣ n - 1 := by
      have hf : ((n ^ p - 1 : ℤ) : ZMod p) = ((n - 1 : ℤ) : ZMod p) := by
        push_cast
        rw [ZMod.pow_card]
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h3
      rw [hf] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 this
    have h5 : z ^ n = z := by
      have h6 : z ^ (n - 1) = 1 := by
        rw [← hord] at h4
        exact orderOf_dvd_iff_zpow_eq_one.1 h4
      calc z ^ n = z ^ (n - 1) * z := by rw [← zpow_add_one, sub_add_cancel]
        _ = z := by rw [h6, one_mul]
    have h7 : b * z * b⁻¹ = z := hn.trans h5
    calc b * z = b * z * b⁻¹ * b := by group
      _ = z * b := by rw [h7]
  refine ⟨z, ⟨?_, hzC⟩, hz1⟩
  by_contra hzB
  have hZel : IsElemAbelian p (Subgroup.zpowers z) :=
    CFSG.Open.IsElemAbelian.closure_of_commute (s := {z}) (by simp) (by simp [hzp]) |>.mono
      (by rw [Subgroup.zpowers_eq_closure])
  have hdisj : ∀ x ∈ B, x ∈ Subgroup.zpowers z → x = 1 := by
    intro x hxB hxz
    by_contra hx1
    apply hzB
    have hxo : orderOf x = p := orderOf_eq_prime (hB.2 x hxB) hx1
    have h1 : Subgroup.zpowers x = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxz)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hord])
    have h2 : z ∈ Subgroup.zpowers x := h1 ▸ Subgroup.mem_zpowers z
    exact Subgroup.zpowers_le.2 hxB h2
  have hBz : ∀ a ∈ B, ∀ c ∈ Subgroup.zpowers z, a * c = c * a := by
    intro a ha c hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact ((Commute.zpow_right (hcomm a ha) j))
  obtain ⟨hPel, hPc⟩ := Inputs2711c.card_prodHom_range hB hZel hBz hdisj
  have hPle : (Inputs2711c.prodHom hBz).range ≤ B ⊔ L := by
    rintro _ ⟨w, rfl⟩
    rw [Inputs2711c.prodHom_apply]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left w.1.2) (Subgroup.mem_sup_right ?_)
    exact Subgroup.zpowers_le.2 hzL w.2.2
  have h1 := hmax _ hPle hPel
  rw [hPc, Nat.card_zpowers, hord] at h1
  have hBpos : 0 < Nat.card B := Nat.card_pos
  nlinarith [hp.one_lt]

variable {G : Type} [Group G] [Finite G]

theorem exists_comp_of_unique (hp : p.Prime) (h183 : Input18_3_4)
    {L E : Subgroup G} (hLK : CFSG.Open.IsKGroup ↥L) (hE : IsElemAbelian p E)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) {e : G} (he : e ∈ E)
    (huniq : ∀ C C' : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer ({e} : Set G)) C →
      GLAPComponent p (L ⊓ Subgroup.centralizer ({e} : Set G)) C' → C = C')
    {J : Subgroup G} (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set G)) J) :
    ∃ C : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer ({e} : Set G)) C ∧ J ≤ C ∧
      E ≤ Subgroup.normalizer (C : Set G) ∧
      GLAPComponent p (C ⊓ Subgroup.centralizer (E : Set G)) J := by
  have hEpg : IsPGroup p E := isPGroup_of_isElemAbelian hE
  set H : Subgroup G := L ⊔ E with hH
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hEN
  have hHK : CFSG.Open.IsKGroup ↥H := chevTools_isKGroup_sup hp hLK hEN hEpg
  set X₁ : Subgroup G := H ⊓ Subgroup.centralizer ({e} : Set G) with hX₁
  have hX₁K : CFSG.Open.IsKGroup ↥X₁ := CFSG.Open.IsKGroup.of_le hHK inf_le_left
  have heE : ({e} : Set G) ⊆ E := Set.singleton_subset_iff.2 he
  have hEX₁ : E ≤ X₁ := le_inf le_sup_right
    (Inputs2711c.le_centralizer_of_elem hE (Subgroup.zpowers_le.2 he) |>.trans
      (Subgroup.centralizer_le (by
        rw [Set.singleton_subset_iff]
        exact Subgroup.mem_zpowers e)))
  have hCE : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.centralizer_le heE
  have heq : X₁ ⊓ Subgroup.centralizer (E : Set G) = H ⊓ Subgroup.centralizer (E : Set G) := by
    rw [hX₁, inf_assoc, inf_eq_right.2 hCE]
  have hSX : L ⊓ Subgroup.centralizer (E : Set G) ≤ H ⊓ Subgroup.centralizer (E : Set G) :=
    inf_le_inf_right _ le_sup_left
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer (E : Set G))
      (H ⊓ Subgroup.centralizer (E : Set G)) :=
    IsSubnormal.step hSX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hSX).2
        (chev_inf_centralizer_le_normalizer hHN E)) (IsSubnormal.refl _)
  have hJ' : GLAPComponent p (X₁ ⊓ Subgroup.centralizer (E : Set G)) J := by
    rw [heq]
    exact glaPComponent_of_isSubnormal' hp hsub hJ
  obtain ⟨𝒞, hcomp, hsup, hinv', -⟩ := h183 G X₁ hX₁K p hp E hEX₁ hE J hJ'
  have hcompL : ∀ C ∈ 𝒞, GLAPComponent p (L ⊓ Subgroup.centralizer ({e} : Set G)) C := by
    intro C hC
    have hCL : C ≤ L := chevTools_perfect_le_of_sup hp hEN hEpg ((hcomp C hC).1.trans inf_le_left)
      (glaPComponent_perfect (hcomp C hC))
    exact glaPComponent_of_le hp (hcomp C hC) (le_inf hCL ((hcomp C hC).1.trans inf_le_right))
      (inf_le_inf_right _ le_sup_left)
  have hJle : J ≤ ⨆ C ∈ 𝒞, C := by
    rw [hsup]
    exact (gLBConj_one J).symm.le.trans (le_iSup₂
      (f := fun g (_ : g ∈ GLAPLayer p X₁) => GLBConj g J) (1 : G) (Subgroup.one_mem _))
  obtain ⟨C, hC⟩ : ∃ C, C ∈ 𝒞 := by
    by_contra h
    push Not at h
    have h0 : (⨆ C ∈ 𝒞, C) = ⊥ := by simp [h]
    rw [h0, le_bot_iff] at hJle
    exact glaPComponent_ne_bot' hJ hJle
  have hall : ∀ C' ∈ 𝒞, C' = C := fun C' hC' => huniq C' C (hcompL C' hC') (hcompL C hC)
  have hJC : J ≤ C := hJle.trans (iSup₂_le fun C' hC' => (hall C' hC').le)
  have hEC : E ≤ Subgroup.normalizer (C : Set G) := by
    intro d hd
    rw [mem_normalizer_iff_gLBConj_eq]
    exact hall _ (hinv' C hC d hd)
  have hCL : C ≤ L := (hcompL C hC).1.trans inf_le_left
  exact ⟨C, hcompL C hC, hJC, hEC,
    glaPComponent_of_le hp hJ (le_inf hJC (hJ.1.trans inf_le_right)) (inf_le_inf_right _ hCL)⟩

theorem glaPLayer_inf_centralizer_eq_bot {Q : Type} [Group Q] [Finite Q]
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) {K : Subgroup Q} (hs : IsSimpleGroup ↥K)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) (hC : IsChevSimple 3 ↥K) {κ : Q} (hκK : κ ∈ K)
    (hκ1 : κ ≠ 1) (hκ3 : κ ^ 3 = 1) :
    GLAPLayer 3 (K ⊓ Subgroup.centralizer ({κ} : Set Q)) = ⊥ := by
  by_contra hne
  obtain ⟨J', hJ'⟩ := Inputs2711.exists_glaPComponent_of_ne_bot hne
  haveI := hs
  set α : MulAut ↥K := MulAut.conj (⟨κ, hκK⟩ : ↥K) with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨κ, hκK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hκ3)
    rw [this, map_one]
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_nonab hnab
  have hα1 : α ≠ 1 := by
    intro h
    apply hκ1
    have hmem : (⟨κ, hκK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut ↥K => φ g) h
      simp only [hα, MulAut.conj_apply, MulAut.one_apply] at this
      calc g * ⟨κ, hκK⟩ = (⟨κ, hκK⟩ * g * (⟨κ, hκK⟩ : ↥K)⁻¹) * ⟨κ, hκK⟩ := by rw [this]
        _ = ⟨κ, hκK⟩ * g := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K := ⟨⟨κ, hκK⟩, rfl⟩
  have hlay := hKD ↥K hs hnab hC α hα3 hα1 hin
  have h1 := glaPComponent_subgroupOf (p := 3) Nat.prime_three
    (inf_le_left : K ⊓ Subgroup.centralizer ({κ} : Set Q) ≤ K) hJ'
  rw [subgroupOf_inf_centralizer_eq hκK] at h1
  have h2 : J'.subgroupOf K ≤ GLAPLayer 3
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) := le_sSup h1
  rw [hlay, le_bot_iff, Subgroup.subgroupOf_eq_bot] at h2
  have hJK : J' ≤ K := hJ'.1.trans inf_le_left
  exact glaPComponent_ne_bot' hJ' (disjoint_self.1 (h2.mono_right hJK))

end Fi24Tools

section Fi24Model

@[expose] def FiAt (Q : Type) [Group Q] (t : Q) : Prop :=
  ∃ K : Subgroup Q, K ≤ Subgroup.centralizer ({t} : Set Q) ∧
    (∀ I : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({t} : Set Q)) I → I = K) ∧
    IsSimpleGroup ↥K ∧ (∃ a b : ↥K, a * b ≠ b * a) ∧ IsChevSimple 3 ↥K ∧
    Nat.card (Subgroup.centralizer ({t} : Set Q)) = 9 * Nat.card K

@[expose] def FiDich (Q : Type) [Group Q] : Prop :=
  ∀ t : Q, orderOf t = 3 →
    (∃ I : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({t} : Set Q)) I) → FiAt Q t

theorem FiAt.of_equiv {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q'] (e : Q ≃* Q')
    {t : Q} (h : FiAt Q t) : FiAt Q' (e t) := by
  obtain ⟨K, hKC, hU, hs, hnab, hchev, hcard⟩ := h
  have hmap : (Subgroup.centralizer ({t} : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ({e t} : Set Q') :=
    CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton e t
  have hmap' : (Subgroup.centralizer ({e t} : Set Q')).map e.symm.toMonoidHom =
      Subgroup.centralizer ({t} : Set Q) := by
    rw [← hmap, map_symm_map]
  let eK : ↥K ≃* ↥(K.map e.toMonoidHom) := e.subgroupMap K
  refine ⟨K.map e.toMonoidHom, ?_, ?_, eK.isSimpleGroup_congr.1 hs, ?_,
    CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv eK hchev, ?_⟩
  · rw [← hmap]
    exact Subgroup.map_mono hKC
  · intro I hI
    have h1 := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three e.symm hI
    rw [hmap'] at h1
    rw [← hU _ h1]
    exact (map_symm_map e.symm I).symm
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eK a, eK b, fun h => hab (eK.injective (by rw [map_mul, map_mul]; exact h))⟩
  · rw [← hmap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]

theorem FiDich.of_equiv {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q'] (e : Q ≃* Q')
    (h : FiDich Q) : FiDich Q' := by
  intro t' hto' hI'
  set t := e.symm t' with htdef
  have het : e t = t' := e.apply_symm_apply t'
  have hto : orderOf t = 3 := by
    have h1 : orderOf (e t) = orderOf t := MulEquiv.orderOf_eq e t
    rw [het] at h1
    rw [← h1, hto']
  have hmap' : (Subgroup.centralizer ({t'} : Set Q')).map e.symm.toMonoidHom =
      Subgroup.centralizer ({t} : Set Q) := by
    rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton e.symm t']
  have hI : ∃ I : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({t} : Set Q)) I := by
    obtain ⟨I', hI'⟩ := hI'
    have h1 := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three e.symm hI'
    rw [hmap'] at h1
    exact ⟨_, h1⟩
  have h2 := FiAt.of_equiv e (h t hto hI)
  rwa [het] at h2

open CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabFi24
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (J lvl)


theorem fiAt_s0 : FiAt ↥J s0 := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  obtain ⟨hcard, hsimple, hnab, hleaf⟩ := fiN_facts
  have hKC : fiN ≤ Subgroup.centralizer ({s0} : Set ↥J) := fiN_le_lvl_two.trans lvl_two_le_cent0
  have hk : Nat.card ↥(Subgroup.centralizer ({s0} : Set ↥J)) = Nat.card ↥fiN * 3 ^ 2 := by
    show Nat.card ↥cent0 = _
    rw [card_cent0, hcard]
    norm_num
  obtain ⟨-, hU⟩ := comps_of_simple_pindex Nat.prime_three fiN hKC hsimple hnab
    (by rw [hcard]; norm_num) hk (by show (3 ^ 2).factorial < Nat.card ↥cent0; rw [card_cent0]; decide)
  have hchev : IsChevSimple 3 ↥fiN := by
    rcases hleaf with ⟨hC, -, -⟩ | ⟨n, hn5, -, -, hf⟩
    · exact hC
    · exact absurd ⟨n, hn5, hf⟩ (Inputs2711c.not_alt_of_card hcard (m₀ := 16) (by norm_num)
        (by decide) (by decide))
  refine ⟨fiN, hKC, hU, hsimple, hnab, hchev, ?_⟩
  rw [hk, hcard]
  norm_num


theorem fiAt_xJ : FiAt ↥J xJ := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hF := frame_facts
  obtain ⟨hleaf, hsimp, hnab, hcard⟩ := leaf_closure_of_six_some epsJ hF.eps_rel hF.eps_ne
  have hLS : Subgroup.closure (Set.range epsJ) ≤ stab4 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨h0, h1, hA, hB⟩ := hF.eps_fix i
    exact mem_stab4.2 ⟨mem_lvl_two_of_fix h0 h1, hA, hB⟩
  have hS : Nat.card stab4 = 4245696 :=
    le_antisymm card_stab4_le (hcard ▸ Subgroup.card_le_of_le hLS)
  have hKC : Subgroup.closure (Set.range epsJ) ≤ Subgroup.centralizer ({xJ} : Set ↥J) :=
    hLS.trans stab4_le_centX
  have hk : Nat.card ↥(Subgroup.centralizer ({xJ} : Set ↥J)) =
      Nat.card ↥(Subgroup.closure (Set.range epsJ)) * 3 ^ 2 := by
    show Nat.card ↥centX = _
    rw [card_centX, hS, hcard]
    norm_num
  obtain ⟨-, hU⟩ := comps_of_simple_pindex Nat.prime_three (Subgroup.closure (Set.range epsJ)) hKC
    hsimp hnab (by rw [hcard]; norm_num) hk
    (by show (3 ^ 2).factorial < Nat.card ↥centX; rw [card_centX, hS]; decide)
  have hchev : IsChevSimple 3 ↥(Subgroup.closure (Set.range epsJ)) := by
    rcases hleaf with ⟨hC, -, -⟩ | ⟨n, hn5, -, -, hf⟩
    · exact hC
    · exact absurd ⟨n, hn5, hf⟩ (Inputs2711c.not_alt_of_card hcard (m₀ := 11) (by norm_num)
        (by decide) (by decide))
  refine ⟨Subgroup.closure (Set.range epsJ), hKC, hU, hsimp, hnab, hchev, ?_⟩
  rw [hk, hcard]
  norm_num


theorem fiDich_J : FiDich ↥J := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  intro t hto hI
  obtain ⟨i, hconj⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Sylow.fi24ThreeClasses_holds t hto
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have ht : (MulAut.conj c⁻¹) (fi24Rep3 i) = t := by
    rw [← hc, MulAut.conj_apply]
    group
  have hconstr : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3
      (Subgroup.centralizer ({fi24Rep3 i} : Set ↥J)) → False := fun h => by
    obtain ⟨I, hI⟩ := hI
    have hmap := CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton (MulAut.conj c⁻¹)
      (fi24Rep3 i)
    rw [ht] at hmap
    have hc' := CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_map (MulAut.conj c⁻¹) h
    rw [hmap] at hc'
    exact CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape Nat.prime_three hc' hI
  fin_cases i
  · obtain ⟨d, hd⟩ := isConj_iff.1 isConj_rep0_s0
    have h := FiAt.of_equiv (MulAut.conj (c⁻¹ * d⁻¹)) fiAt_s0
    have he : (MulAut.conj (c⁻¹ * d⁻¹)) s0 = t := by
      rw [← ht, MulAut.conj_apply, MulAut.conj_apply, ← hd]
      show c⁻¹ * d⁻¹ * (d * wordElt [18] * d⁻¹) * (c⁻¹ * d⁻¹)⁻¹ = c⁻¹ * wordElt [18] * c⁻¹⁻¹
      group
    rwa [he] at h
  · exfalso
    obtain ⟨-, h1, -, -, -, -⟩ := fi24Three_facts
    exact hconstr (pConstrainedShape_of_twinFacts h1 bound_base3
      Certificates.certificate17566)
  · exfalso
    obtain ⟨-, -, h2, h3, -, -⟩ := fi24Three_facts
    exact hconstr (pConstrainedShape_of_twinFacts h2 (bound_14069 h3)
      Certificates.certificate17565)
  · exfalso
    obtain ⟨-, -, -, -, h4, -⟩ := fi24Three_facts
    exact hconstr (pConstrainedShape_of_twinFacts h4 bound_base3
      Certificates.certificate17567)
  · obtain ⟨d, hd⟩ := isConj_iff.1 isConj_rep4_xJ
    have h := FiAt.of_equiv (MulAut.conj (c⁻¹ * d⁻¹)) fiAt_xJ
    have he : (MulAut.conj (c⁻¹ * d⁻¹)) xJ = t := by
      rw [← ht, MulAut.conj_apply, MulAut.conj_apply, ← hd]
      show c⁻¹ * d⁻¹ * (d * wordElt [2] * d⁻¹) * (c⁻¹ * d⁻¹)⁻¹ = c⁻¹ * wordElt [2] * c⁻¹⁻¹
      group
    rwa [he] at h

theorem fiDich_carrier [Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime)] :
    FiDich (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have e : CFSG.Blueprint.NativeSporadic.Fi24prime ≃* ↥J := CFSG.Sporadic.Fi24.fi24EquivJ
  exact FiDich.of_equiv (Q := ↥J) (Q' := CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) e.symm
    fiDich_J

end Fi24Model

section PairFi24Bot

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

theorem fi24_seven_le_pRank
    [Finite (NativeSporadic.Carrier .Fi24Prime)] :
    7 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Fi24Prime)) := by
  obtain ⟨D, -, hn, -⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicRank.sylowCover_Fi24
  have hD : IsElemAbelian 3 D.span :=
    CFSG.Open.IsElemAbelian.closure_of_commute (s := Set.range D.a)
      (by
        rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
        exact D.comm i j)
      (by
        rintro _ ⟨i, rfl⟩
        exact D.pow i)
  have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hD (D.card_span Nat.prime_three)
  rw [hn] at h
  exact h


theorem sporPairCase_Fi24_three_of_bot (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) :
    SporPairCaseWith .Fi24Prime 3 fun X _ L B => B ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by
  intro X _ _ hp hp2 L B hB0 hLK hLq hB hBN hmax _ _ _ _ _ hname hin _ _ _ _ E hEB _ hEi _ _ hLE hle
  exfalso
  haveI : Finite (NativeSporadic.Carrier .Fi24Prime) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .Fi24Prime (by decide)
  obtain ⟨eS⟩ := hname
  obtain ⟨bF⟩ := hBr .Fi24Prime
  have hZdvd : Nat.card (Subgroup.center ↥L) ∣ 3 :=
    card_center_dvd_multiplier hSpM hLq .Fi24Prime eS
  have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hZdvd with h | h
    · exact h
    · exfalso
      obtain ⟨z, hz, hz1⟩ := exists_mem_B0_of_card_center hp hB hBN hmax h
      rw [hB0, Subgroup.mem_bot] at hz
      exact hz1 hz
  have hZ : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
  have hZL : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := by
    rw [hZ1]
    norm_num
  let ι : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let σ : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .Fi24Prime := eS.trans bF.symm
  let π : ↥L ≃* NativeSporadic.Carrier .Fi24Prime := ι.symm.trans σ
  have hFD : FiDich ↥L := FiDich.of_equiv π.symm fiDich_carrier
  have hinE : ∀ b ∈ E, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X) :=
    fun b hb => hin b (hEB hb)
  let φ : ↥E →* ↥L := ι.toMonoidHom.comp (barHom hinE)
  have hφ : ∀ u : ↥E, φ u = kOf hinE u := fun u => rfl
  have hφc : ∀ u : ↥E, ((φ u : ↥L) : X)⁻¹ * (u : X) ∈ Subgroup.centralizer (L : Set X) :=
    fun u => by
      rw [hφ u]
      exact kOf_spec hinE u
  have hCu : ∀ u : ↥E, (L ⊓ Subgroup.centralizer ({(u : X)} : Set X)).subgroupOf L =
      Subgroup.centralizer ({φ u} : Set ↥L) := fun u => by
    rw [Inputs2711b.inf_centralizer_eq_of_inner (hφc u), subgroupOf_inf_centralizer_eq (φ u).2,
      Inputs1415.fixSubgroup_conj]
  set R : Subgroup ↥L := φ.range with hR
  have hCE : (L ⊓ Subgroup.centralizer (E : Set X)).subgroupOf L =
      Subgroup.centralizer (R : Set ↥L) := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      have h1 : y ∈ (L ⊓ Subgroup.centralizer ({(u : X)} : Set X)).subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2) u u.2).symm
      rw [hCu u, Subgroup.mem_centralizer_singleton_iff] at h1
      exact h1.symm
    · intro hy
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 : y ∈ Subgroup.centralizer ({φ ⟨u, hu⟩} : Set ↥L) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.1 hy) _ ⟨⟨u, hu⟩, rfl⟩).symm
      rw [← hCu ⟨u, hu⟩, Subgroup.mem_subgroupOf] at h1
      exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h1).2).symm
  have hEel : IsElemAbelian 3 E := isElemAbelian_mono hB hEB
  have hRel : IsElemAbelian 3 R := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun t ht => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      change (x : ↥L) * y = y * x
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (isElemAbelian_commute hEel a.2 b.2)
    · obtain ⟨a, rfl⟩ := ht
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hEel.2 a a.2)
      rw [this, map_one]
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : barHom hinE u = 1 := ι.injective (hu.trans (map_one ι).symm)
    have h3 : (u : X) ∈ B ⊓ Subgroup.centralizer (L : Set X) :=
      ⟨hEB u.2, (barHom_eq_one_iff hinE u).1 h1⟩
    rw [hB0, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hRc : Nat.card R = Nat.card E := by
    rw [hR, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj, Subgroup.card_top]
  have hrkL : 7 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Fi24Prime)) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) π
    rw [h2]
    exact fi24_seven_le_pRank
  have hBc : 3 ^ 7 ≤ Nat.card B := by
    have h1 := pow_pRank_mul_le hp hB hmax hZL
    rw [hB0, Subgroup.card_bot, mul_one] at h1
    exact (Nat.pow_le_pow_right (by norm_num) hrkL).trans h1
  have hRc' : 243 ≤ Nat.card R := by
    rw [hRc]
    have h1 := hBc.trans hEi
    norm_num at h1
    omega
  have hcompu : ∀ u : ↥E, ∃ I : Subgroup ↥L,
      GLAPComponent 3 (Subgroup.centralizer ({φ u} : Set ↥L)) I := by
    intro u
    obtain ⟨J, hJ⟩ := Inputs2711.exists_glaPComponent_of_ne_bot (hle u u.2)
    have h1 := glaPComponent_subgroupOf (p := 3) Nat.prime_three
      (inf_le_left : L ⊓ Subgroup.centralizer ({(u : X)} : Set X) ≤ L) hJ
    rw [hCu u] at h1
    exact ⟨_, h1⟩
  obtain ⟨J, hJ⟩ := Inputs2711.exists_glaPComponent_of_ne_bot hLE
  have hJ1 := glaPComponent_subgroupOf (p := 3) Nat.prime_three
    (inf_le_left : L ⊓ Subgroup.centralizer (E : Set X) ≤ L) hJ
  rw [hCE] at hJ1
  obtain ⟨r₀, hr₀R, hr₀1⟩ : ∃ r ∈ R, r ≠ 1 := by
    by_contra h
    push Not at h
    have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).2 h
    rw [this, Subgroup.card_bot] at hRc'
    norm_num at hRc'
  obtain ⟨u₀, rfl⟩ := hr₀R
  have hr₀3 : orderOf (φ u₀) = 3 := orderOf_eq_prime (hRel.2 _ ⟨u₀, rfl⟩) hr₀1
  obtain ⟨K, hKC, hU, hs, hnab, hchev, hcard⟩ := hFD (φ u₀) hr₀3 (hcompu u₀)
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  have hTK : CFSG.Open.IsKGroup ↥(⊤ : Subgroup ↥L) := hLK'.subgroup ⊤
  have hRN : R ≤ Subgroup.normalizer ((⊤ : Subgroup ↥L) : Set ↥L) := by
    intro r _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  have hJtop : GLAPComponent 3 ((⊤ : Subgroup ↥L) ⊓ Subgroup.centralizer (R : Set ↥L))
      (J.subgroupOf L) := by
    rw [top_inf_eq]
    exact hJ1
  obtain ⟨C, hC, -, hRC, hJCE⟩ := exists_comp_of_unique (p := 3) Nat.prime_three h183 hTK hRel hRN
    (⟨u₀, rfl⟩ : φ u₀ ∈ R) (fun C C' hC hC' => by
      rw [top_inf_eq] at hC hC'
      rw [hU C hC, hU C' hC']) hJtop
  rw [top_inf_eq] at hC
  rw [hU C hC] at hRC hJCE
  have hRC0 : R ≤ Subgroup.centralizer ({φ u₀} : Set ↥L) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hRel hr ⟨u₀, rfl⟩
  have hidx : K.relIndex (Subgroup.centralizer ({φ u₀} : Set ↥L)) = 9 := by
    have h1 := Subgroup.relIndex_mul_card K (Subgroup.centralizer ({φ u₀} : Set ↥L))
    rw [inf_eq_left.2 hKC, hcard] at h1
    have hpos : 0 < Nat.card K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hidxR : K.relIndex R ≤ 9 :=
    hidx ▸ Subgroup.relIndex_le_of_le_right hRC0 (by rw [hidx]; norm_num)
  have h2 := Subgroup.relIndex_mul_card K R
  have hKR : 1 < Nat.card ↥(K ⊓ R) := by
    by_contra h
    push Not at h
    have h3 : K.relIndex R * Nat.card ↥(K ⊓ R) ≤ 9 * 1 := Nat.mul_le_mul hidxR h
    omega
  obtain ⟨⟨κ, hκ⟩, hκ1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).1 ((Subgroup.one_lt_card_iff_ne_bot _).1 hKR)
  have hκ1' : κ ≠ 1 := fun h => hκ1 (Subtype.ext h)
  have hκ3 : κ ^ 3 = 1 := hRel.2 κ hκ.2
  have hlay := glaPLayer_inf_centralizer_eq_bot hKD hs hnab hchev hκ.1 hκ1' hκ3
  have hnone : ∀ C' : Subgroup ↥L,
      ¬ GLAPComponent 3 (K ⊓ Subgroup.centralizer ({κ} : Set ↥L)) C' := by
    intro C' hC'
    have h1 : C' ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer ({κ} : Set ↥L)) := le_sSup hC'
    rw [hlay, le_bot_iff] at h1
    exact glaPComponent_ne_bot' hC' h1
  obtain ⟨C', hC', -⟩ := exists_comp_of_unique (p := 3) Nat.prime_three h183 (hLK'.subgroup K) hRel
    hRC hκ.2 (fun C₁ _ hC₁ _ => (hnone C₁ hC₁).elim) hJCE
  exact hnone C' hC'

end PairFi24Bot

section PairFi24Full

open CFSG.Blueprint
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)


theorem sporPairCase_Fi24_three (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) (hb : LieOrderBridge)
    (hD32 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2) :
    Inputs2711c.SporPairCase .Fi24Prime 3 :=
  sporPairCase_of_with (sporPairCase_Fi24_three_of_bot h183 hSpM hBr hKD)
    (sporPairCase_Fi24_three_of_ne_bot h183 hSpM hOrd hOut hBr hb hD32 centShapeRk_fi24_fiGood)

end PairFi24Full

section RankCover

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem pow_pRank_le_mul_card_range (hp : p.Prime) {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hin : ∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X))
    (hZ : ¬ p ^ 2 ∣ Nat.card (Subgroup.center ↥L)) :
    p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ p * Nat.card (barHom hin).range := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A₀, -, hA₀, hA₀c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup ↥L)
  set A : Subgroup X := A₀.map L.subtype with hAdef
  have hA : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hA₀ L.subtype
  have hAc : Nat.card A = p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
    rw [hAdef, Subgroup.card_map_of_injective L.subtype_injective, hA₀c]
  have hAL : A ≤ L := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  set B₀ := B ⊓ Subgroup.centralizer (L : Set X) with hB₀
  have hB₀el : IsElemAbelian p B₀ := CFSG.Open.IsElemAbelian.mono hB inf_le_left
  have hAC : ∀ a ∈ A, ∀ c ∈ B₀, a * c = c * a := fun a ha c hc =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 a (hAL ha))
  set f := Inputs2711c.prodHom hAC with hf
  have hfel : IsElemAbelian p f.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      apply Subtype.ext
      change (x : X) * y = y * x
      rw [← hu, ← hv, hf, Inputs2711c.prodHom_apply, Inputs2711c.prodHom_apply]
      have h1 := Inputs27.elem_mul_comm hA u.1.2 v.1.2
      have h2 := Inputs27.elem_mul_comm hB₀el u.2.2 v.2.2
      have h3 := hAC _ u.1.2 _ v.2.2
      have h4 := hAC _ v.1.2 _ u.2.2
      calc (u.1 : X) * u.2 * (v.1 * v.2) = (u.1 * v.1) * (u.2 * v.2) := by
            rw [mul_assoc, ← mul_assoc (u.2 : X), ← h4, mul_assoc, mul_assoc]
        _ = (v.1 * u.1) * (v.2 * u.2) := by rw [h1, h2]
        _ = (v.1 : X) * v.2 * (u.1 * u.2) := by
            rw [mul_assoc, ← mul_assoc (u.1 : X), h3, mul_assoc, mul_assoc]
    · obtain ⟨u, rfl⟩ := hz
      rw [hf, Inputs2711c.prodHom_apply]
      have hc : Commute (u.1 : X) u.2 := hAC _ u.1.2 _ u.2.2
      rw [hc.mul_pow, hA.2 _ u.1.2, hB₀el.2 _ u.2.2, one_mul]
  have hfle : f.range ≤ B ⊔ L := by
    rintro _ ⟨x, rfl⟩
    rw [hf, Inputs2711c.prodHom_apply]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hAL x.1.2))
      (Subgroup.mem_sup_left (Subgroup.mem_inf.1 x.2.2).1)
  have hI : Nat.card ↥(A ⊓ B₀) ≤ p := by
    have hIL : A ⊓ B₀ ≤ L := inf_le_left.trans hAL
    have hIZ : (A ⊓ B₀).subgroupOf L ≤ Subgroup.center ↥L := by
      intro y hy
      exact mem_center_of_mem_centralizer (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hy).2).2
    have hdvd : Nat.card ↥(A ⊓ B₀) ∣ Nat.card (Subgroup.center ↥L) := by
      have h1 := Subgroup.card_dvd_of_le hIZ
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIL).toEquiv] at h1
    have hpg : IsPGroup p ↥(A ⊓ B₀) := isPGroup_of_isElemAbelian (isElemAbelian_mono hA inf_le_left)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).1 hpg
    rw [hk] at hdvd ⊢
    have hk2 : k < 2 := by
      by_contra h
      push Not at h
      exact hZ ((Nat.pow_dvd_pow p h).trans hdvd)
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  have hker : Nat.card f.ker ≤ p := by
    refine le_trans (Nat.card_le_card_of_injective (fun x : ↥f.ker =>
      (⟨((x : ↥A × ↥B₀).1 : X), ⟨(x : ↥A × ↥B₀).1.2, ?_⟩⟩ : ↥(A ⊓ B₀))) ?_) hI
    · have h1 : ((x : ↥A × ↥B₀).1 : X) * ((x : ↥A × ↥B₀).2 : X) = 1 :=
        (Inputs2711c.prodHom_apply hAC (x : ↥A × ↥B₀)).symm.trans (MonoidHom.mem_ker.1 x.2)
      rw [eq_inv_of_mul_eq_one_left h1]
      exact B₀.inv_mem (x : ↥A × ↥B₀).2.2
    · intro x y hxy
      have h1 : ((x : ↥A × ↥B₀).1 : X) = ((y : ↥A × ↥B₀).1 : X) :=
        congrArg (fun z : ↥(A ⊓ B₀) => (z : X)) hxy
      have hx1 : ((x : ↥A × ↥B₀).1 : X) * ((x : ↥A × ↥B₀).2 : X) = 1 :=
        (Inputs2711c.prodHom_apply hAC (x : ↥A × ↥B₀)).symm.trans (MonoidHom.mem_ker.1 x.2)
      have hy1 : ((y : ↥A × ↥B₀).1 : X) * ((y : ↥A × ↥B₀).2 : X) = 1 :=
        (Inputs2711c.prodHom_apply hAC (y : ↥A × ↥B₀)).symm.trans (MonoidHom.mem_ker.1 y.2)
      have h2 : ((x : ↥A × ↥B₀).2 : X) = ((y : ↥A × ↥B₀).2 : X) := by
        rw [eq_inv_of_mul_eq_one_right hx1, eq_inv_of_mul_eq_one_right hy1, h1]
      exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [Nat.card_prod, hAc] at h1
  have h2 := hmax _ hfle hfel
  have h3 := card_range_barHom_mul hin
  have hB₀pos : 0 < Nat.card ↥B₀ := Nat.card_pos
  have h4 : p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) * Nat.card ↥B₀ ≤
      p * Nat.card (barHom hin).range * Nat.card ↥B₀ := by
    rw [← h1, mul_assoc, h3]
    calc Nat.card f.ker * Nat.card f.range ≤ p * Nat.card B :=
          Nat.mul_le_mul hker h2
      _ = p * Nat.card B := rfl
  exact Nat.le_of_mul_le_mul_right h4 hB₀pos

end RankCover

section PairSuzCover

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)


theorem sporPairCase_Suz_three_of_dvd (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) (hb : LieOrderBridge)
    (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2) :
    SporPairCaseWith .Suz 3 fun X _ L _ => 3 ∣ Nat.card (Subgroup.center ↥L) := by
  intro X _ _ hp hp2 L B hZ3 hLK hLq hB hBN hmax _ _ _ _ hC1 hname hin J0 hJ0 hJt _ E hEB _ _ hEl hE2 _
    _
  exfalso
  have hname' := hname
  obtain ⟨eS⟩ := hname'
  obtain ⟨bS⟩ := hBr .Suz
  let σ₀ : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .Suz := eS.trans bS.symm
  let σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥suzM :=
    (eS.trans bS.symm).trans (suzEquivM : NativeSporadic.Suz ≃* ↥suzM)
  have hZ6 : Nat.card (Subgroup.center ↥L) ∣ 6 := card_center_dvd_multiplier hSpM hLq .Suz eS
  obtain ⟨D₀, hn, hA, hF⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicRank.exists_spec_Suz
  have hrk : 6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
    have := CFSG.HardMathSupport.Timmesfeld.SporadicRank.lower_of_cover hLq σ₀ hZ6 hZ3 D₀ hA hF
    omega
  have hZ9 : ¬ 3 ^ 2 ∣ Nat.card (Subgroup.center ↥L) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans hZ6)
    norm_num at this
  have hR := pow_pRank_le_mul_card_range hp hB hmax hin hZ9
  have hRel : IsElemAbelian 3 (barHom hin).range := isElemAbelian_range_barHom hB hin
  have hR5 : 3 ^ 5 ∣ Nat.card (barHom hin).range := by
    have h3 : Nat.card (barHom hin).range = 3 ^ CFSG.Open.pRank 3 (barHom hin).range :=
      Inputs27.card_eq_pow_pRank hp hRel
    have h4 : 3 ^ 6 ≤ 3 * 3 ^ CFSG.Open.pRank 3 (barHom hin).range :=
      (Nat.pow_le_pow_right (by norm_num) hrk).trans (h3 ▸ hR)
    have h5 : 5 ≤ CFSG.Open.pRank 3 (barHom hin).range := by
      rw [← pow_succ'] at h4
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h4
      omega
    rw [h3]
    exact Nat.pow_dvd_pow 3 h5
  obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
  set t := barHom hin ⟨e, hEB he⟩ with ht
  have ht1 : σ t ≠ 1 := fun h =>
    heC ((barHom_eq_one_iff hin ⟨e, hEB he⟩).1 (σ.injective (h.trans (map_one σ).symm)))
  have ht3 : σ t ^ 3 = 1 := by
    rw [← map_pow, hRel.2 _ ⟨⟨e, hEB he⟩, rfl⟩, map_one]
  have hmapt := CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton σ t
  have h5 : 3 ^ 5 ∣ Nat.card (Subgroup.centralizer ({σ t} : Set ↥suzM)) := by
    rw [← hmapt, Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective]
    exact hR5.trans (Subgroup.card_dvd_of_le (range_barHom_le_centralizer hB hin ⟨e, hEB he⟩))
  obtain ⟨hcG, hcU⟩ := census_barHom_at hp hin σ isoInv_PX₀ ⟨e, hEB he⟩
    (suzM_census_five ht1 ht3 h5)
  have hEel : IsElemAbelian 3 E := isElemAbelian_mono hB hEB
  obtain ⟨D, hDE, heD, hDc⟩ := exists_card_sq hp hEel hE2 he
  have hDel : IsElemAbelian 3 D := isElemAbelian_mono hEel hDE
  have hD2r : 2 ≤ CFSG.Open.pRank 3 D := (pRank_eq_two hp hDel hDc).ge
  have hDC : ¬ D ≤ Subgroup.centralizer (L : Set X) := fun h => heC (h heD)
  have hpS : 3 ∣ sporOrd .Suz := by simp only [sporOrd]; norm_num
  have h12 : ¬ sporOrd .Suz ∣ Nat.factorial 12 := fun h =>
    absurd (Nat.le_of_dvd (Nat.factorial_pos 12) h)
      (by simp only [sporOrd]; norm_num [Nat.factorial])
  obtain ⟨J, hJL, hJ⟩ := exists_jD hp hp2 h183 hD2 hSpM hOrd hpS h12 hLK hLq hB hBN hname hJ0 hJt
    hEB hEl hDE hD2r hDC
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  obtain ⟨fJ⟩ : PX₀ (PSimple 3 J) :=
    typeClosure_of_unique hp hp2 (downClosed_PX₀ hKD) isoInv_PX₀ h183 hLK' hDel
      (hDE.trans (hEB.trans hBN)) heD hcG hcU hJL
  have hcard : Nat.card (PSimple 3 J) = 3265920 :=
    (Nat.card_congr fJ.toEquiv).trans CFSG.LieType.Multipliers.U43.card_X₀
  rcases hJ with ⟨hA', -⟩ | hsmall
  · exact Inputs2711c.not_altOrChevTwo_U43 hb hcard hA'
  · rw [hcard] at hsmall
    rcases hsmall with h | h | h | h <;> exact absurd h (by decide)

theorem sporPairCase_Suz_three (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) (hb : LieOrderBridge)
    (hD32 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2) :
    Inputs2711c.SporPairCase .Suz 3 :=
  sporPairCase_of_with (sporPairCase_Suz_three_of_dvd h183 hSpM hOrd hBr hKD hb hD32)
    (sporPairCase_Suz_three_of_not_dvd h183 hSpM hOrd hBr hKD hb hD32)

end PairSuzCover

section PairJ3Bot

open CFSG.Blueprint
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)

theorem sporPairCase_J3_three_of_bot
    (hBr : SporadicBridges) :
    SporPairCaseWith .J3 3 fun X _ L B => B ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by
  intro X _ _ hp _ L B hB0 _ _ hB _ _ hrk4 _ _ _ _ hname hin _ _ _ _ _ _ _ _ _ _ _ _
  exfalso
  have hle : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicThreeRankLe .J3 3 :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicThreeRankLe_of_carrier .J3 3 (hBr .J3) (by
      intro _
      show CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.J3) ≤ 3
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.RankThree.Asc83Table.J3.native_J3.1])
  have h3 := hle _ hname
  have hRel : IsElemAbelian 3 (barHom hin).range := isElemAbelian_range_barHom hB hin
  have h1 := card_range_barHom_mul hin
  rw [hB0, Subgroup.card_bot, mul_one, Inputs27.card_eq_pow_pRank hp hB] at h1
  have h4 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hRel h1
  omega

end PairJ3Bot

section Residual

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Dickson.BMRows (PCompCensus)

structure SporPairsResidual2 : Prop where
  J3_three_B0 :
    SporPairCaseWith .J3 3 fun X _ L B => ¬ B ⊓ Subgroup.centralizer (L : Set X) = ⊥
  ONan_three : Inputs2711c.SporPairCase .ONan 3
  HN_three : Inputs2711c.SporPairCase .HN 3
  Co1_five : Inputs2711c.SporPairCase .Co1 5


theorem sporPairsResidual_of_rest2
    (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) (hb : LieOrderBridge)
    (hD32 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2)
    (hD52 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 5 2)
    (hD72 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 7 2)
    (hcM3 : CFSG.Open.IsKGroup (NativeSporadic.Carrier .M) →
      PCompCensus 3 (NativeSporadic.Carrier .M)
        (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th))
    (hcB5 : CFSG.Open.IsKGroup (NativeSporadic.Carrier .B) →
      PCompCensus 5 (NativeSporadic.Carrier .B) (· = .sporadic .HS))
    (hNC5 : CFSG.Open.IsKGroup (NativeSporadic.Carrier .B) → TabBFiveBNoComp)
    (hA5 : TabBFiveACard) (h : SporPairsResidual2) : Inputs2711c.SporPairsResidual where
  J3_three := sporPairCase_of_with (sporPairCase_J3_three_of_bot hBr) h.J3_three_B0
  Suz_three := sporPairCase_Suz_three h183 hSpM hOrd hBr hKD hb hD32
  ONan_three := h.ONan_three
  Co3_three := sporPairCase_Co3_three hSpM hBr
  Co2_three := sporPairCase_Co2_three h183 hSpM hBr hKD
  Co1_three := sporPairCase_Co1_three h183 hSpM hOrd hBr hKD hb hD32
  Fi24Prime_three := sporPairCase_Fi24_three h183 hSpM hOrd hOut hBr hKD hb hD32
  HN_three := h.HN_three
  M_three := sporPairCase_M_three h183 hSpM hOrd hOut hBr hKD hb hD32 hcM3 centShapeRk_fi24_fiGood
  Co1_five := h.Co1_five
  B_five := sporPairCase_B_five h183 hSpM hOrd hOut hBr hb hD52 hcB5
    (fun hK => fullRankBound_B_five tabBFive_hconj (hNC5 hK) hA5 tabBFiveAHS_of_cert)
  M_seven := sporPairCase_M_seven h183 hSpM hOrd hOut hBr hb hD72
    CFSG.HardMathSupport.Dickson.BMRows.census_M_seven fullRankBound_M_seven

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711d
