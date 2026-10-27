module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Parts
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporRank
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def SporadicRankThreePair (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (s = .Co1 ∧ p = 5) ∨ (s = .HN ∧ p = 5) ∨ (s = .Ly ∧ p = 5) ∨ (s = .B ∧ p = 5) ∨
    (s = .M ∧ p = 5) ∨ (s = .M ∧ p = 7)

@[expose] def RankThreeWitness (p : ℕ) {S : Type*} [Group S] (x : S) : Prop :=
  (∃ P : Sylow p S, (P : Subgroup S) ≤ centralizer ({x} : Set S)) ∨
  (∃ Q Z : Subgroup S, (∀ y ∈ Q, y ^ p = 1) ∧ Z ≤ Q ∧ (∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z) ∧
      Nat.card Z = p ∧ (∀ y ∈ Q, ∀ w ∈ Q, y * w * y⁻¹ * w⁻¹ ∈ Z) ∧ p ^ 5 ≤ Nat.card Q ∧
      x ∈ Q ∧ x ∉ Z) ∨
  (∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ x ∈ E)

theorem rankThreeWitness_of_conj_mem {S T : Type*} [Group S] [Group T] {p : ℕ} (f : S ≃* T)
    {A : Subgroup T} (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ 3) {x : S} (c : T)
    (hx : c * f x * c⁻¹ ∈ A) : RankThreeWitness p x := by
  refine Or.inr (Or.inr ⟨(A.map (MulAut.conj c⁻¹).toMonoidHom).map f.symm.toMonoidHom,
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hA _) _, ?_, ?_⟩)
  · rw [Subgroup.card_map_of_injective (f := f.symm.toMonoidHom) f.symm.injective,
      Subgroup.card_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom)
        (MulAut.conj c⁻¹).injective, hcard]
  · refine ⟨c⁻¹ * (c * f x * c⁻¹) * c, ⟨_, hx, ?_⟩, ?_⟩
    · simp [MulAut.conj_apply]
    · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.symm_apply_apply]
      group

theorem three_le_pRank_centralizer_of_witness {S : Type*} [Group S] [Finite S] {p : ℕ}
    [Fact p.Prime] {x : S} (hx : RankThreeWitness p x)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) := by
  rcases hx with ⟨P, hP⟩ | ⟨Q, Z, hexp, hZQ, hZc, hZ, hcomm, hcard, hxQ, hxZ⟩ |
    ⟨E, hE, hcard, hxE⟩
  · exact three_le_pRank_centralizer_of_sylow P hP h3
  · exact three_le_pRank_centralizer_of_extraspecial hexp hZQ hZc hZ hcomm hcard hxQ hxZ
  · haveI := hE.1
    have hEC : E ≤ centralizer ({x} : Set S) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (setLike_mul_comm hy hxE)
    exact CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt hEC hE hcard

@[expose] def SporadicRankTable : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → 5 ≤ p → ∀ (S : Type) [Group S] [Finite S],
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) → SporadicRankThreePair s p

@[expose] def SporadicClassWitnessAt (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ x : S, orderOf x = p → RankThreeWitness p x

@[expose] def SporadicClassWitness : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), SporadicRankThreePair s p → SporadicClassWitnessAt s p

theorem sporadicClassWitness_of_pairs (h1 : SporadicClassWitnessAt .Co1 5)
    (h2 : SporadicClassWitnessAt .HN 5) (h3 : SporadicClassWitnessAt .Ly 5)
    (h4 : SporadicClassWitnessAt .B 5) (h5 : SporadicClassWitnessAt .M 5)
    (h6 : SporadicClassWitnessAt .M 7) : SporadicClassWitness := by
  intro s p hpair
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  exacts [h1, h2, h3, h4, h5, h6]

@[expose] def SporadicCentralizerRank : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → 5 ≤ p → ∀ (S : Type) [Group S] [Finite S],
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) → ∀ x : S, orderOf x = p →
      3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S))

theorem sporadicCentralizerRank_of_data (hT : SporadicRankTable) (hC : SporadicClassWitness) :
    SporadicCentralizerRank := by
  intro s p hp hp5 S _ _ he h3 x hx
  haveI : Fact p.Prime := ⟨hp⟩
  exact three_le_pRank_centralizer_of_witness (hC s p (hT s p hp hp5 S he h3) S he x hx) h3

@[expose] def SporadicOutOdd : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group)

theorem mem_of_pow_eq_one_of_not_dvd_card_outer {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (L : Subgroup X) [L.Normal] (hcen : centralizer (L : Set X) = ⊥)
    (hout : ¬ p ∣ Nat.card (Outer ↥L)) {e : X} (he : e ^ p = 1) : e ∈ L := by
  have hαp : (MulAut.conjNormal (H := L) e) ^ p = 1 := by
    rw [← map_pow, he, map_one]
  have hcop : Nat.Coprime p (Nat.card (Outer ↥L)) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hout
  have h1 : (QuotientGroup.mk (MulAut.conjNormal (H := L) e) : Outer ↥L) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hαp, QuotientGroup.mk_one]
  have h4 : orderOf (QuotientGroup.mk (MulAut.conjNormal (H := L) e) : Outer ↥L) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard _)
  have hinn : MulAut.conjNormal (H := L) e ∈ inner ↥L :=
    (QuotientGroup.eq_one_iff (N := inner ↥L) _).1 (orderOf_eq_one_iff.1 h4)
  obtain ⟨t, ht⟩ := hinn
  have key : ∀ h ∈ L, (t : X) * h * (t : X)⁻¹ = e * h * e⁻¹ := by
    intro h hh
    have h1 := congrArg Subtype.val (DFunLike.congr_fun ht ⟨h, hh⟩)
    simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using h1
  have hcen' : (t : X)⁻¹ * e ∈ centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    calc h * ((t : X)⁻¹ * e) = (t : X)⁻¹ * ((t : X) * h * (t : X)⁻¹) * e := by group
      _ = (t : X)⁻¹ * (e * h * e⁻¹) * e := by rw [key h hh]
      _ = (t : X)⁻¹ * e * h := by group
  rw [hcen, Subgroup.mem_bot] at hcen'
  have het : e = (t : X) := (inv_mul_eq_one.1 hcen').symm
  rw [het]
  exact t.2

theorem pRank_top_le_pRank_top_of_forall_le {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (L : Subgroup X) (hL : ∀ E : Subgroup X, IsElemAbelian p E → E ≤ L) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup X)
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact CFSG.SectionRank.le_pRank hp1 (hL E hE) hE hcard

theorem kd29Spor_of_rank (hOut : SporadicOutOdd) (hR : SporadicCentralizerRank) : KD29Spor := by
  intro p hp hp5 X _ _ L _ hs hn hc hcat hl hcen h3 hex d hd hd1 hdp
  obtain ⟨s, ⟨e⟩⟩ := hcat
  obtain ⟨x, hxL, hxo, hx2⟩ := hex
  exfalso
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hout : ¬ p ∣ Nat.card (Outer ↥L) := by
    have h1 := hOut s p hp (by omega)
    rwa [← Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv] at h1
  have hEL : ∀ E : Subgroup X, IsElemAbelian p E → E ≤ L := fun E hE y hy =>
    mem_of_pow_eq_one_of_not_dvd_card_outer hp L hcen hout (hE.2 y hy)
  have hL3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) :=
    h3.trans (pRank_top_le_pRank_top_of_forall_le L hEL)
  have hxo' : orderOf (⟨x, hxL⟩ : ↥L) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hxo
  have h4 := hR s p hp hp5 ↥L ⟨e⟩ hL3 ⟨x, hxL⟩ hxo'
  have h5 : CFSG.Open.pRank p (centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L)) ≤
      CFSG.Open.pRank p (centralizer ({x} : Set X)) := by
    refine (CFSG.SectionRank.pRank_le_map hp1 L.subtype L.subtype_injective _).trans
      (CFSG.SectionRank.pRank_mono hp1 ?_)
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy'
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy')
  omega

theorem kd29Spor_of_data (hOut : SporadicOutOdd) (hT : SporadicRankTable)
    (hC : SporadicClassWitness) : KD29Spor :=
  kd29Spor_of_rank hOut (sporadicCentralizerRank_of_data hT hC)

end CFSG.LocalAnalysis.RankFourTheoremC
