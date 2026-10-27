module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterA1
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterC
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterTwistedA

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.GorensteinWalter
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

@[expose] def DefCharOuterRankTwoFam (k : DefCharFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → 5 < p → idx.1.characteristic = p →
        ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 →
          ∃ x ∈ D ⊓ innerAut S, x ≠ 1

theorem lt_pow_two_of_prime {p : ℕ} (hp : p.Prime) : p < p ^ 2 := by
  simpa using Nat.pow_lt_pow_right hp.one_lt (show 1 < 2 by norm_num)

theorem ne_two_of_five_lt {p : ℕ} (hp5 : 5 < p) : p ≠ 2 := by omega

theorem exists_inner_transport_lt {S C : Type} [Group S] [Group C] (e : S ≃* C) {p : ℕ}
    (D : Subgroup (MulAut S)) (hD : ∀ a ∈ D, a ^ p = 1) (hlt : p < Nat.card D)
    (H : ∀ D' : Subgroup (MulAut C), (∀ a ∈ D', a ^ p = 1) → p < Nat.card D' →
      ∃ x ∈ D' ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner C, x ≠ 1) :
    ∃ x ∈ D ⊓ innerAut S, x ≠ 1 := by
  set φ := MulAut.congr e with hφ
  have hcardD : Nat.card (D.map φ.toMonoidHom) = Nat.card D :=
    Subgroup.card_map_of_injective φ.injective
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := H (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ p = 1
      rw [← map_pow, hD a ha, map_one])
    (by rw [hcardD]; exact hlt)
  obtain ⟨x, hxD, rfl⟩ := hx'D
  obtain ⟨g, hg⟩ := hx'I
  refine ⟨x, ⟨hxD, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
  apply φ.injective
  change _ = φ.toMonoidHom x
  rw [← hg]
  ext s
  simp [hφ, MulAut.congr_apply]

open CFSG.LocalAnalysis.ComponentInitial LinearFlag in
theorem outerRank_A_of_two_le {S : Type} [Group S] [Finite S] (idx : TauCeti.ValidLieTypeIndex)
    (hidx : ∃ r q, idx.1 = .A r q ∧ 2 ≤ r)
    (hS : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hch : idx.1.characteristic = p) (D : Subgroup (MulAut S))
    (hD : IsElemAbelian p D) (hlt : p < Nat.card D) :
    ∃ x ∈ D ⊓ innerAut S, x ≠ 1 := by
  obtain ⟨r, q, hr, hr2⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  let e : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e0.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hndvd : ¬ q.p ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by
    intro h
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self _ q.exponent_pos.ne'
    rw [hKq] at h
    have h2 : q.p ∣ q.p ^ q.exponent - (q.p ^ q.exponent - 1) := Nat.dvd_sub h1 h
    have hpos : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ hp.pos
    rw [Nat.sub_sub_self hpos] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt fun D' hexp hc =>
    exists_inner_of_elemAbelian_projectiveSL (K := GaloisField q.p q.exponent) (n := r + 1)
      (by omega) hp hp2 hndvd D' hexp hc

theorem outerRank_A_one {S : Type} [Group S] [Finite S] (idx : TauCeti.ValidLieTypeIndex)
    (hidx : ∃ q, idx.1 = .A 1 q)
    (hS : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hch : idx.1.characteristic = p) (D : Subgroup (MulAut S))
    (hD : IsElemAbelian p D) (hlt : p < Nat.card D) :
    ∃ x ∈ D ⊓ innerAut S, x ≠ 1 := by
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  have hlin : CFSG.AGLEmbedding.IsLinTwoIndex q.p q.exponent ⟨.A 1 q, hv⟩ := ⟨q, rfl, rfl, rfl⟩
  obtain ⟨e0⟩ := hS
  obtain ⟨e1⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hlin
  let e : S ≃* CFSG.GorensteinWalter.PSL2 (GaloisField q.p q.exponent) := e0.trans e1
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hodd : IsOddPrimePower (Nat.card (GaloisField q.p q.exponent)) :=
    ⟨q.p, q.exponent, q.prime_p, q.prime_p.odd_of_ne_two hp2, q.exponent_pos, hKq⟩
  have h4 : 4 ≤ q.p ^ q.exponent := by
    have := hv
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff] at this
    simpa [TauCeti.PrimePower.card_def] using this.1.2 rfl
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt fun D' hexp hc =>
    exists_inner_of_elemAbelian_psl2 (K := GaloisField q.p q.exponent) hodd (by rw [hKq]; omega)
      hp hp2 D' hexp hc

theorem defCharOuterRankTwoFamA : DefCharOuterRankTwoFam .A := by
  intro S _ _ hS hnab idx hk hidx p hp hp5 hch D hD hcard
  obtain ⟨r, q, hrq⟩ := hk
  have hv := idx.2
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff, hrq] at hv
  have hr1 : 1 ≤ r := hv.1.1
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  by_cases hr : r = 1
  · exact outerRank_A_one idx ⟨q, hrq.trans (by rw [hr])⟩ hidx hp (ne_two_of_five_lt hp5) hch D hD
      hlt
  · exact outerRank_A_of_two_le idx ⟨r, q, hrq, by omega⟩ hidx hp (ne_two_of_five_lt hp5) hch D hD
      hlt

theorem outerRank_C {S : Type} [Group S] [Finite S] (idx : TauCeti.ValidLieTypeIndex)
    (hidx : ∃ r q, idx.1 = .C r q)
    (hS : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) {p : ℕ} (hp : p.Prime)
    (hch : idx.1.characteristic = p) (D : Subgroup (MulAut S))
    (hD : IsElemAbelian p D) (hlt : p < Nat.card D) :
    ∃ x ∈ D ⊓ innerAut S, x ≠ 1 := by
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hpq : p = q.p := by simpa using hch.symm
  have hfin := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField (⟨.C r q, hv⟩ :
    TauCeti.ValidLieTypeIndex)
  let K := ↥(TauCeti.ValidLieTypeIndex.fixedField (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex))
  let e : S ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp r K) :=
    e0.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
  have hKq : Nat.card K = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  have hndvd : ¬ p ∣ Nat.card K - 1 := by
    intro h
    have h1 : p ∣ q.p ^ q.exponent := by
      rw [← hpq]; exact dvd_pow_self _ q.exponent_pos.ne'
    rw [hKq] at h
    have h2 : p ∣ q.p ^ q.exponent - (q.p ^ q.exponent - 1) := Nat.dvd_sub h1 h
    have hpos : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ q.prime_p.pos
    rw [Nat.sub_sub_self hpos] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt fun D' hexp hc =>
    exists_inner_of_elemAbelian_projectiveSp (K := K) (r := r) hrange.1 hp hndvd D' hexp hc

theorem defCharOuterRankTwoFamC : DefCharOuterRankTwoFam .C := by
  intro S _ _ hS hnab idx hk hidx p hp hp5 hch D hD hcard
  exact outerRank_C idx hk hidx hp hch D hD (by rw [hcard]; exact lt_pow_two_of_prime hp)

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag in
theorem defCharOuterRankTwoFamTwistedA : DefCharOuterRankTwoFam .twistedA := by
  intro S _ _ hS' hnab idx hidx hS p hp hp5 hch D hD hcard
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := K))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hpq' : p = q.p := hpq
  subst hpq'
  have hndvd : ¬ q.p ∣ q.p ^ q.exponent + 1 := by
    intro hd
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self _ q.exponent_pos.ne'
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hd))
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt fun D' hexp hc =>
    exists_inner_of_elemAbelian_primeFormP h (n := r + 1) (by omega) hq' hp hndvd D' hexp hc

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
