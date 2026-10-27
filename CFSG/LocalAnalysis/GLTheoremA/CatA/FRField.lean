module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMarked
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
open scoped commutatorElement

theorem exists_noncomm_of_perfect {S : Type} [Group S] {D T : Subgroup S} (hTD : T ≤ D)
    (hperf : ⁅T, T⁆ = T) (hne : T ≠ ⊥) : ∃ x y : ↥D, x * y ≠ y * x := by
  by_contra hc
  push Not at hc
  apply hne
  rw [← hperf, Subgroup.commutator_eq_bot_iff_le_centralizer.2]
  intro a ha b hb
  exact (Subtype.ext_iff.1 (hc ⟨a, hTD ha⟩ ⟨b, hTD hb⟩)).symm

theorem false_of_perfect_solvable {S : Type} [Group S] {D T : Subgroup S} (hTD : T ≤ D)
    (hperf : ⁅T, T⁆ = T) (hne : T ≠ ⊥) (hsol : Group.IsSolvable ↥D) : False := by
  haveI : Group.IsSolvable ↥T :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hTD)
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hne
  have hc : commutator ↥T = ⊤ := by
    apply Subgroup.map_injective T.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hperf]
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥T).ne hc

@[expose] def DatumCore (D : Type) [Group D] : Prop :=
  ∃ E : Subgroup D, IsSimpleGroup ↥E ∧ (∃ x y : ↥E, x * y ≠ y * x) ∧
    (∀ T : Subgroup D, ⁅T, T⁆ = T → T ≤ E) ∧
    (Nat.card D = Nat.card ↥E ∨ Nat.card D = 2 * Nat.card ↥E) ∧
    (IsChevSimple 2 ↥E ∨ Nat.card ↥E = 168)

theorem datumCore_of_simple {D : Type} [Group D] (hs : IsSimpleGroup D)
    (hna : ∃ x y : D, x * y ≠ y * x) (hch : IsChevSimple 2 D ∨ Nat.card D = 168) : DatumCore D := by
  refine ⟨⊤, (MulEquiv.isSimpleGroup_congr Subgroup.topEquiv).mpr hs, ?_, fun T _ => le_top,
    Or.inl (Subgroup.card_top).symm, ?_⟩
  · obtain ⟨x, y, h⟩ := hna
    exact ⟨⟨x, trivial⟩, ⟨y, trivial⟩, fun h' => h (congrArg Subtype.val h')⟩
  · rcases hch with h | h
    · exact Or.inl (chev_isChevSimple_of_mulEquiv Subgroup.topEquiv h)
    · exact Or.inr (by rw [Subgroup.card_top]; exact h)

theorem coreSub_of_subfield {S : Type} [Group S] [Finite S] {β : MulAut S} {D : Subgroup S}
    (hD : SubfieldGrp β D) (hC : DatumCore ↥D) : CoreSub (FP.fixSub β) := by
  obtain ⟨hDC, hcomm, hodd⟩ := hD
  obtain ⟨E, hE, hna, hperf, hidx, hch⟩ := hC
  have eE : ↥E ≃* ↥(E.map D.subtype) := E.equivMapOfInjective D.subtype D.subtype_injective
  have hcard : Nat.card ↥(E.map D.subtype) = Nat.card ↥E :=
    Subgroup.card_map_of_injective D.subtype_injective
  refine ⟨E.map D.subtype, (Subgroup.map_subtype_le E).trans hDC, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MulEquiv.isSimpleGroup_congr eE).mp hE
  · obtain ⟨x, y, h⟩ := hna
    exact ⟨eE x, eE y, fun h' => h (eE.injective (by rw [map_mul, map_mul]; exact h'))⟩
  · intro T hTC hTp
    have hTD : T ≤ D := hTp ▸ (Subgroup.commutator_mono hTC hTC).trans hcomm
    have hTT : (T.subgroupOf D).map D.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTD
    have hT'p : ⁅T.subgroupOf D, T.subgroupOf D⁆ = T.subgroupOf D := by
      apply Subgroup.map_injective D.subtype_injective
      rw [Subgroup.map_commutator, hTT, hTp]
    calc T = (T.subgroupOf D).map D.subtype := hTT.symm
      _ ≤ E.map D.subtype := Subgroup.map_mono (hperf _ hT'p)
  · have hCD : Nat.card ↥(FP.fixSub β) = D.relIndex (FP.fixSub β) * Nat.card ↥D := by
      have := Subgroup.relIndex_mul_card (H := D) (K := FP.fixSub β)
      rw [inf_eq_left.2 hDC] at this
      exact this.symm
    have h1 : twoPart (Nat.card ↥(FP.fixSub β)) = twoPart (Nat.card ↥D) := by
      rw [hCD]
      exact FP.twoPart_mul_odd hodd Nat.card_pos.ne'
    have h2 : twoPart (Nat.card ↥D) ≤ 2 * twoPart (Nat.card ↥E) := by
      rcases hidx with h | h
      · rw [h]
        have : 1 ≤ twoPart (Nat.card ↥E) := Nat.one_le_two_pow
        omega
      · rw [h]
        unfold twoPart
        rw [Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, pow_add,
          Nat.Prime.factorization_self Nat.prime_two]
        simp
    rw [h1, hcard]
    exact h2
  · rcases hch with h | h
    · exact Or.inl (chev_isChevSimple_of_mulEquiv eE.symm h)
    · exact Or.inr (by rw [hcard]; exact h)

@[expose] def SmallDatum : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel) (D : Type) [Group D], p.Prime → LargeEvenInLambda2 lab → p ∣ lab.n →
    ¬ LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ →
    CFSG.Assembly.LargeEvenRawDatum ⟨lab.tag, lab.rank, lab.n / p⟩
      (fun R' _ _ _ => Nonempty (D ≃* R')) → Group.IsSolvable D ∨ DatumCore D

@[expose] def TwF4Core (p : ℕ) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (L : Subgroup G) (b : G) (hF : FieldOn p b L),
    (∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ lab.tag = .twF4 ∧ lab.n = p ∧
      MarkedModel lab (PSimple p L)) →
    (∃ T : Subgroup (PSimple p L), T ≤ FP.fixSub (indAut p L b hF.1) ∧ ⁅T, T⁆ = T ∧ T ≠ ⊥) →
    CoreSub (FP.fixSub (indAut p L b hF.1))

@[expose] def TD4Core : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (X L : Subgroup G) (b : G)
    (hb : b ∈ Subgroup.normalizer (L : Set G)), GLAPComponent 3 X L → IsChevSimple 2 (PSimple 3 L) →
    b ^ 3 = 1 → IsTD4 3 L → NonInner 3 b L →
    (∃ T : Subgroup (PSimple 3 L), T ≤ FP.fixSub (indAut 3 L b hb) ∧ ⁅T, T⁆ = T ∧ T ≠ ⊥) →
    CoreSub (FP.fixSub (indAut 3 L b hb))

section Rows


variable {G : Type} [Group G] [Finite G]

theorem coreSub_of_fieldOn {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hSmall : SmallDatum)
    (hTwF4 : TwF4Core p) {L : Subgroup G} {b : G} (hF : FieldOn p b L)
    (hT : ∃ T : Subgroup (PSimple p L), T ≤ FP.fixSub (indAut p L b hF.1) ∧ ⁅T, T⁆ = T ∧ T ≠ ⊥) :
    CoreSub (FP.fixSub (indAut p L b hF.1)) := by
  obtain ⟨lab, hlab, h3, hM, hpn, D, hD, hdat⟩ := fieldOn_subfield hp hp2 hF
  obtain ⟨T, hTC, hTp, hTne⟩ := hT
  have hTD : T ≤ D := hTp ▸ (Subgroup.commutator_mono hTC hTC).trans hD.2.1
  have hna := exists_noncomm_of_perfect hTD hTp hTne
  rcases hdat with hdat | hexc
  · by_cases hΛ : LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩
    · have hG : lab.tag ≠ .G2der := by
        intro h
        obtain ⟨t, r, n⟩ := lab
        dsimp only at h hpn hlab
        subst h
        have : n = 1 := hlab.2.2
        rw [this] at hpn
        exact hp.one_lt.ne' (Nat.dvd_one.1 hpn)
      have hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Nonempty (↥D ≃* R) →
          ∃ a b : R, a * b ≠ b * a := fun R _ I F ⟨e⟩ => by
        obtain ⟨x, y, h⟩ := hna
        exact ⟨e x, e y, fun h' => h (e.injective (by rw [map_mul, map_mul]; exact h'))⟩
      obtain ⟨R', _, I', F', ⟨e'⟩, hMR⟩ :=
        Canonical.largeEvenRawDatum_exists (Canonical.largeEvenRawDatum_markedModel hΛ hQ hdat)
      obtain ⟨hs, hch⟩ := simple_chev_of_markedModel (lab := ⟨lab.tag, lab.rank, lab.n / p⟩) hG
        (MarkedModel.of_mulEquiv e'.symm hMR)
      exact coreSub_of_subfield hD (datumCore_of_simple hs hna hch)
    · rcases hSmall p lab ↥D hp hlab hpn hΛ hdat with hsol | hC
      · exact (false_of_perfect_solvable hTD hTp hTne hsol).elim
      · exact coreSub_of_subfield hD hC
  · rcases hexc with ⟨htag, hn, hsol⟩ | ⟨htag, hn⟩
    · exact (false_of_perfect_solvable hTD hTp hTne hsol).elim
    · exact hTwF4 L b hF ⟨lab, hlab, htag, hn, hM⟩ ⟨T, hTC, hTp, hTne⟩

theorem coreSub_of_r2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hSmall : SmallDatum)
    (hTwF4 : TwF4Core p) (hTD4 : TD4Core) {X L : Subgroup G} {b : G} (hX : GLAPComponent p X L)
    (hchev : IsChevSimple 2 (PSimple p L)) (hbp : b ^ p = 1) (hR : R2Prop p b L)
    (hI : Ipart p L b ≠ ⊥) :
    ∃ hb : b ∈ Subgroup.normalizer (L : Set G), CoreSub (FP.fixSub (indAut p L b hb)) := by
  rcases hR with hF | ⟨rfl, hT, hNI⟩
  · exact ⟨hF.1, coreSub_of_fieldOn hp hp2 hSmall hTwF4 hF (exists_perfect_of_ipart hp hF.1 hbp hI)⟩
  · exact ⟨hNI.1, hTD4 X L b hNI.1 hX hchev hbp hT hNI (exists_perfect_of_ipart hp hNI.1 hbp hI)⟩

theorem i91CentIAt_of_residuals {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hSmall : SmallDatum)
    (hTwF4 : TwF4Core p) (hTD4 : TD4Core) : I91CentIAt G p := by
  intro X L b hX hchev hbp hR hI
  obtain ⟨hb, hcore⟩ := coreSub_of_r2 hp hp2 hSmall hTwF4 hTD4 hX hchev hbp hR hI
  exact (ipart_of_core hp hp2 hb hbp hcore hI).2.2

theorem i91CompAt_of_residuals {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hSmall : SmallDatum)
    (hTwF4 : TwF4Core p) (hTD4 : TD4Core)
    (hR168 : ∀ (R : Type) [Group R], IsSimpleGroup R → Nat.card R = 168 → IsChevSimple 2 R) :
    I91CompAt G p := by
  intro X L b hX hchev hbp hR hI
  obtain ⟨hb, hcore⟩ := coreSub_of_r2 hp hp2 hSmall hTwF4 hTD4 hX hchev hbp hR hI
  obtain ⟨h1, h2, -⟩ := ipart_of_core hp hp2 hb hbp hcore hI
  exact ⟨h1, h2.elim id fun h => hR168 _ (chev_pSimple_simple_nonabelian hp h1).1 h⟩

end Rows

end FR

end CFSG.LocalAnalysis.GLTheoremA
