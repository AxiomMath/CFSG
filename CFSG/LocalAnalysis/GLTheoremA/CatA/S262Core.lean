module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieAmb
import CFSG.GroupTheory.PLayer.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms

theorem good_map_congr {K T : Type*} [Group K] [Group T] [Finite K] [Finite T] {p : ℕ}
    (hp : p.Prime) (e : K ≃* T) (A : Subgroup (MulAut K))
    (hgood : ∀ a ∈ A, a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥) :
    ∀ a ∈ A.map (MulAut.congr e).toMonoidHom, a ≠ 1 →
      GLAPLayer p (fixSubgroup a) = ⊥ := by
  rintro a ⟨b, hb, rfl⟩ ha1
  change GLAPLayer p (fixSubgroup ((MulAut.congr e) b)) = ⊥
  rw [CFSG.glaPLayer_fixSubgroup_congr hp e b,
    hgood b hb (fun hb1 => ha1 (by rw [hb1, map_one]))]
  exact Subgroup.map_bot _

theorem i262_of_lie_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hExc : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264ExcNoGood p) (hG : I262GF2)
    {K : Type} [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex)
    (hchar : d.1.characteristic = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpK : p ∣ Nat.card K) (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A)
    (hAcard : p ^ 2 ≤ Nat.card A)
    (hgood : ∀ a ∈ A, a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥) :
    (p = 3 ∧ (catalogIs K S265.tyA ∨ catalogIs K S265.tyUn ∨ catalogIs K S265.tyC ∨
        catalogIs K S265.tyD)) ∨
      (p = 5 ∧ catalogIs K S265.tyE) ∨ catalogIs K (S265.tyF p) := by
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv K e.toEquiv
  let A' : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group) :=
    A.map (MulAut.congr e).toMonoidHom
  have hA' : IsElemAbelian p A' := hA.map _
  have hcard' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hgood' : ∀ a ∈ A', a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥ :=
    good_map_congr hp e A hgood
  have hpchar : p ≠ d.1.characteristic := by rw [hchar]; exact hp2
  have hpdvd : p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
    rw [← Nat.card_congr e.toEquiv]
    exact hpK
  by_cases h2 : p = 3 ∧ ov2Idx d.1
  · have h9 : 9 ≤ Nat.card A' := by
      rw [hcard']
      simpa [h2.1] using hAcard
    have hA3 : IsElemAbelian 3 A' := by simpa [h2.1] using hA'
    have hgood3 : ∀ a ∈ A', a ≠ 1 → GLAPLayer 3 (fixSubgroup a) = ⊥ := by
      simpa [h2.1] using hgood'
    rcases hG d hchar h2.2 A' hA3 h9 hgood3 with h | h | h
    · exact Or.inl ⟨h2.1, Or.inl ⟨.lie d, h, ⟨e⟩⟩⟩
    · exact Or.inl ⟨h2.1, Or.inr (Or.inl ⟨.lie d, h, ⟨e⟩⟩)⟩
    · exact Or.inl ⟨h2.1, Or.inr (Or.inr (Or.inl ⟨.lie d, h, ⟨e⟩⟩))⟩
  · have hAcard' : p ^ 2 ≤ Nat.card A' := by rw [hcard']; exact hAcard
    rcases hExc p hp hp2 d hpchar hpdvd A' hA' hAcard' hgood' with
      hx1 | hx2 | hx3 | hx4
    · exact absurd hx1 h2
    · obtain ⟨hp3, ⟨q, hq, hq8⟩, -⟩ := hx2
      have hty : S265.tyD (.lie d) := by
        simp only [S265.tyD, onLie]
        rcases hq with hq | hq <;> rw [hq] <;> exact hq8
      exact Or.inl ⟨hp3, Or.inr (Or.inr (Or.inr ⟨.lie d, hty, ⟨e⟩⟩))⟩
    · obtain ⟨hp5, he⟩ := hx3
      have hty : S265.tyE (.lie d) := by
        simp only [S265.tyE, onLie]
        rcases he with he | he <;> rw [he] <;> simp
      exact Or.inr (Or.inl ⟨hp5, ⟨.lie d, hty, ⟨e⟩⟩⟩)
    · obtain ⟨hlp, -⟩ := hx4
      simp only [lpEpsIdx] at hlp
      rcases hlp with ⟨q, hq | hq⟩
      · obtain ⟨hd, hdvd⟩ := hq
        have hty : S265.tyF p (.lie d) := by
          simp only [S265.tyF, onLie]
          rw [hd]
          have hq2 : q.p = 2 := by
            rw [hd] at hchar
            simpa [TauCeti.LieTypeIndex.characteristic_A] using hchar
          exact ⟨Nat.succ_pred_eq_of_pos hp.pos, hq2, hdvd⟩
        exact Or.inr (Or.inr ⟨.lie d, hty, ⟨e⟩⟩)
      · obtain ⟨hd, hdvd⟩ := hq
        have hty : S265.tyF p (.lie d) := by
          simp only [S265.tyF, onLie]
          rw [hd]
          have hq2 : q.p = 2 := by
            rw [hd] at hchar
            simpa [TauCeti.LieTypeIndex.characteristic_twistedA] using hchar
          exact ⟨Nat.succ_pred_eq_of_pos hp.pos, hq2, hdvd⟩
        exact Or.inr (Or.inr ⟨.lie d, hty, ⟨e⟩⟩)

theorem i262_of_alternating {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hA8 : I262Alt8)
    {K : Type} [Group K] [Finite K] (n : ℕ) (hn : 5 ≤ n)
    (h568 : n = 5 ∨ n = 6 ∨ n = 8)
    (e : K ≃* (TauCeti.CFSGIndex.alternating n hn).Group)
    (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A) (hAcard : p ^ 2 ≤ Nat.card A)
    (hgood : ∀ a ∈ A, a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥) :
    (p = 3 ∧ (catalogIs K S265.tyA ∨ catalogIs K S265.tyUn ∨ catalogIs K S265.tyC ∨
        catalogIs K S265.tyD)) ∨
      (p = 5 ∧ catalogIs K S265.tyE) ∨ catalogIs K (S265.tyF p) := by
  let A' : Subgroup (MulAut (TauCeti.CFSGIndex.alternating n hn).Group) :=
    A.map (MulAut.congr e).toMonoidHom
  have hA' : IsElemAbelian p A' := hA.map _
  have hcard' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hgood' : ∀ a ∈ A', a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥ :=
    good_map_congr hp e A hgood
  have hpsq : p ^ 2 ≤ Nat.card A' := by rw [hcard']; exact hAcard
  have hnotle : ¬ (Nat.card A' ≤ p) := by
    intro hle
    nlinarith [hp.two_le, hpsq, hle]
  have hamb : ¬ (p = 3 ∧ (n = 6 ∨ n = 8)) → Nat.card A' ≤ p := by
    intro hexcl
    exact (kd264Amb_holds p hp hp2).1 n hn h568 hexcl A' hA'
  rcases h568 with rfl | rfl | rfl
  · exact absurd (hamb (by rintro ⟨-, h | h⟩ <;> omega)) hnotle
  · by_cases hp3 : p = 3
    · have hty : S265.tyA (.alternating 6 hn) := by
        simp [S265.tyA, S265.tyAlt6]
      refine Or.inl ⟨hp3, Or.inl ⟨.alternating 6 hn, hty, ⟨e⟩⟩⟩
    · exact absurd (hamb (by rintro ⟨hp3', -⟩; exact hp3 hp3')) hnotle
  · by_cases hp3 : p = 3
    · have h9 : 9 ≤ Nat.card A' := by
        rw [hcard']
        simpa [hp3] using hAcard
      have hA3 : IsElemAbelian 3 A' := by simpa [hp3] using hA'
      have hgood3 : ∀ a ∈ A', a ≠ 1 → GLAPLayer 3 (fixSubgroup a) = ⊥ := by
        simpa [hp3] using hgood'
      rcases hA8 A' hA3 h9 with ⟨a, ha, ha1, hane⟩
      exact absurd (hgood3 a ha ha1) hane
    · exact absurd (hamb (by rintro ⟨hp3', -⟩; exact hp3 hp3')) hnotle

theorem i262_of_psl27 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hExc : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264ExcNoGood p)
    {K : Type} [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hd : d.1 = .A 1 q) (hq7 : q.card = 7)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hpK : p ∣ Nat.card K)
    (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A) (hAcard : p ^ 2 ≤ Nat.card A)
    (hgood : ∀ a ∈ A, a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥) :
    (p = 3 ∧ (catalogIs K S265.tyA ∨ catalogIs K S265.tyUn ∨ catalogIs K S265.tyC ∨
        catalogIs K S265.tyD)) ∨
      (p = 5 ∧ catalogIs K S265.tyE) ∨ catalogIs K (S265.tyF p) := by
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv K e.toEquiv
  let A' : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group) :=
    A.map (MulAut.congr e).toMonoidHom
  have hA' : IsElemAbelian p A' := hA.map _
  have hcard' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hgood' : ∀ a ∈ A', a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥ :=
    good_map_congr hp e A hgood
  have hpsq : p ^ 2 ≤ Nat.card A' := by rw [hcard']; exact hAcard
  have hqp7 : q.p = 7 := by
    have hdvd : q.p ∣ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    rw [hq7] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p (by norm_num)).1 hdvd
  have hfs7 : fieldSize d.1 = 7 := by
    rw [hd]
    simpa [fieldSize] using hq7
  have hchar7 : d.1.characteristic = 7 := by
    rw [hd]
    simpa [TauCeti.LieTypeIndex.characteristic_A] using hqp7
  by_cases hp7 : p = 7
  · have hle : Nat.card A' ≤ 7 := by
      have hle' := (kd264Amb_holds p hp hp2).2 hp7 d ⟨q, hd, hq7⟩ A' hA'
      simpa [hp7] using hle'
    rw [hp7] at hpsq
    omega
  · have hpchar : p ≠ d.1.characteristic := by rw [hchar7]; exact hp7
    have hpdvd : p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
      rw [← Nat.card_congr e.toEquiv]
      exact hpK
    have hAcard' : p ^ 2 ≤ Nat.card A' := hpsq
    rcases hExc p hp hp2 d hpchar hpdvd A' hA' hAcard' hgood' with
      hx1 | hx2 | hx3 | hx4
    · exfalso
      obtain ⟨-, hov2⟩ := hx1
      change fieldSize d.1 = 2 at hov2
      rw [hfs7] at hov2
      omega
    · exfalso
      obtain ⟨-, ⟨q', hq', hq'8⟩, -⟩ := hx2
      rcases hq' with hq' | hq'
      · have hqq : q' = q := by
          have hEq : TauCeti.LieTypeIndex.A 1 q' = TauCeti.LieTypeIndex.A 1 q :=
            hq'.symm.trans hd
          injection hEq with _ h
        rw [hqq] at hq'8
        omega
      · cases hq'.symm.trans hd
    · exfalso
      obtain ⟨-, he⟩ := hx3
      rcases he with he | he
      · cases he.symm.trans hd
      · cases he.symm.trans hd
    · exfalso
      obtain ⟨hlp, -⟩ := hx4
      simp only [lpEpsIdx] at hlp
      rcases hlp with ⟨q', hq' | hq'⟩
      · obtain ⟨hd', -⟩ := hq'
        have hp1 : p - 1 = 1 := by
          have hEq : TauCeti.LieTypeIndex.A (p - 1) q' = TauCeti.LieTypeIndex.A 1 q :=
            hd'.symm.trans hd
          injection hEq with h _
        omega
      · obtain ⟨hd', -⟩ := hq'
        cases hd'.symm.trans hd

theorem i262_of_psu33 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hExc : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264ExcNoGood p)
    {K : Type} [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hd : d.1 = .twistedA 2 q) (hq3 : q.card = 3)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hpK : p ∣ Nat.card K)
    (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A) (hAcard : p ^ 2 ≤ Nat.card A)
    (hgood : ∀ a ∈ A, a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥) :
    (p = 3 ∧ (catalogIs K S265.tyA ∨ catalogIs K S265.tyUn ∨ catalogIs K S265.tyC ∨
        catalogIs K S265.tyD)) ∨
      (p = 5 ∧ catalogIs K S265.tyE) ∨ catalogIs K (S265.tyF p) := by
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv K e.toEquiv
  let A' : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group) :=
    A.map (MulAut.congr e).toMonoidHom
  have hA' : IsElemAbelian p A' := hA.map _
  have hcard' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hgood' : ∀ a ∈ A', a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥ :=
    good_map_congr hp e A hgood
  have hpsq : p ^ 2 ≤ Nat.card A' := by rw [hcard']; exact hAcard
  have hqp3 : q.p = 3 := by
    have hdvd : q.p ∣ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    rw [hq3] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p (by norm_num)).1 hdvd
  have hfs3 : fieldSize d.1 = 3 := by
    rw [hd]
    simpa [fieldSize] using hq3
  have hchar3 : d.1.characteristic = 3 := by
    rw [hd]
    simpa [TauCeti.LieTypeIndex.characteristic_twistedA] using hqp3
  by_cases hp3 : p = 3
  · have hty : S265.tyC (.lie d) := by
      simp only [S265.tyC, onLie]
      rw [hd]
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      simpa using hq3
    exact Or.inl ⟨hp3, Or.inr (Or.inr (Or.inl ⟨.lie d, hty, ⟨e⟩⟩))⟩
  · exfalso
    have hpchar : p ≠ d.1.characteristic := by rw [hchar3]; exact hp3
    have hpdvd : p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
      rw [← Nat.card_congr e.toEquiv]
      exact hpK
    rcases hExc p hp hp2 d hpchar hpdvd A' hA' hpsq hgood' with
      hx1 | hx2 | hx3 | hx4
    · obtain ⟨hp3', -⟩ := hx1
      exact hp3 hp3'
    · obtain ⟨hp3', -, -⟩ := hx2
      exact hp3 hp3'
    · obtain ⟨-, he⟩ := hx3
      rcases he with he | he
      · cases he.symm.trans hd
      · cases he.symm.trans hd
    · obtain ⟨hlp, -⟩ := hx4
      simp only [lpEpsIdx] at hlp
      rcases hlp with ⟨q', hq' | hq'⟩
      · obtain ⟨hd', -⟩ := hq'
        cases hd'.symm.trans hd
      · obtain ⟨hd', -⟩ := hq'
        have hp1 : p - 1 = 2 := by
          have hEq : TauCeti.LieTypeIndex.twistedA (p - 1) q' =
              TauCeti.LieTypeIndex.twistedA 2 q := hd'.symm.trans hd
          injection hEq with h _
        omega

theorem i262_of_parts (hExc : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264ExcNoGood p)
    (hG : I262GF2) (hA8 : I262Alt8) : I262 := by
  intro p hp hp2 K _ _ hK hpK A hA hAcard hgood
  rcases hK with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      have hchar : d.1.characteristic = 2 := by simpa [onLie] using hi
      exact i262_of_lie_two hp hp2 hExc hG d hchar e hpK A hA hAcard hgood
    | alternating n hn => exact False.elim (by simpa [onLie] using hi)
    | sporadic s => exact False.elim (by simpa [onLie] using hi)
    | cyclic q hq => exact False.elim (by simpa [onLie] using hi)
  · rcases CFSG.StandardType.ChevTwo.ambiguousChev_two_cases hi with
      ⟨h5, rfl⟩ | ⟨h6, rfl⟩ | ⟨h8, rfl⟩ | ⟨q, hv, hq7, rfl⟩ | ⟨q, hv, hq3, rfl⟩
    · exact i262_of_alternating hp hp2 hA8 5 h5 (Or.inl rfl) e A hA hAcard hgood
    · exact i262_of_alternating hp hp2 hA8 6 h6 (Or.inr (Or.inl rfl)) e A hA hAcard hgood
    · exact i262_of_alternating hp hp2 hA8 8 h8 (Or.inr (Or.inr rfl)) e A hA hAcard hgood
    · exact i262_of_psl27 hp hp2 hExc ⟨.A 1 q, hv⟩ q rfl hq7 e hpK A hA hAcard hgood
    · exact i262_of_psu33 hp hp2 hExc ⟨.twistedA 2 q, hv⟩ q rfl hq3 e hpK A hA hAcard hgood

end CFSG.LocalAnalysis.GLTheoremA.S262

end
