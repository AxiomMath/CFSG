module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcRee
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267RankAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019AmbAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def S267FactBadExcLie : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ (S B : Subgroup Ω), S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        catalogIs (PSimple p S) (onLie fun d => d.characteristic = q ∧ S2019.S2019ExcCoreIdx d) →
        ¬ catalogIs (PSimple p S) (onLie S267ClassicalIdx) →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B → p ^ 4 ≤ Nat.card B →
        Nat.card ↥(B ⊓ centModSubgroup p S) = p → ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B

theorem exists_elemAbelian_aut_cube {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime) {S B : Subgroup Ω}
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) :
    ∃ A : Subgroup (MulAut (PSimple p S)), IsElemAbelian p A ∧ p ^ 3 ≤ Nat.card A := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := card_le_card_inf_centMod_mul_pow hp hS hperf hB
  rw [hBC] at h
  have h' : p ^ 4 ≤ p ^ (1 + CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p S)))) := by
    rw [pow_add, pow_one]; exact hB4.trans h
  have hr : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p S))) := by
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h'
    omega
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hr
  exact ⟨E, hE, hcard.ge⟩

section Red


theorem s267FactBadExc_of_lie (h : S267FactBadExcLie) : S267FactBadExc := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ hK S B hSn hperf hSp hChev hncl hBel hSB hrank hB4 hBC hp3B hHq
  obtain ⟨A, hA, hcard⟩ := exists_elemAbelian_aut_cube hp hSn hperf hBel hB4 hBC
  rcases hChev with hLie | hAmb
  · obtain ⟨i, hi, e⟩ := hLie
    cases i with
    | cyclic r hr => simp [onLie] at hi
    | alternating n hn => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie d =>
      obtain ⟨d, hv⟩ := d
      have hchar : d.characteristic = q := hi
      have hcl : ∀ (_ : S267ClassicalIdx d), False := fun hc => hncl ⟨.lie ⟨d, hv⟩, hc, e⟩
      have hcore : ∀ (_ : S2019.S2019ExcCoreIdx d), S267ConcA p S B ∨ S267ConcBCDE p q S B := fun hc =>
        h p q hp hp2 hq hq2 hqp Ω hK S B hSn hperf hSp ⟨.lie ⟨d, hv⟩, ⟨hchar, hc⟩, e⟩ hncl hBel hSB hrank hB4 hBC
          hp3B hHq
      cases d with
      | A n Q => exact (hcl trivial).elim
      | twistedA n Q => exact (hcl trivial).elim
      | B n Q => exact (hcl trivial).elim
      | C n Q => exact (hcl trivial).elim
      | D n Q => exact (hcl trivial).elim
      | twistedD n Q => exact (hcl trivial).elim
      | E6 Q => exact hcore trivial
      | E7 Q => exact hcore trivial
      | E8 Q => exact hcore trivial
      | F4 Q => exact hcore trivial
      | G2 Q => exact hcore trivial
      | twistedE6 Q => exact hcore trivial
      | trialityD4 Q => exact hcore trivial
      | suzuki m => exact absurd hchar.symm (by simpa using hq2)
      | reeF4 m => exact absurd hchar.symm (by simpa using hq2)
      | tits => exact absurd hchar.symm (by simpa using hq2)
      | reeG2 m =>
        exfalso
        have hq3 : q = 3 := by simpa using hchar.symm
        have hp3 : p ≠ 3 := fun hp3 => hqp (hq3.trans hp3.symm)
        have hm : 1 ≤ m := by
          have hr := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
          simpa using (TauCeti.LieTypeIndex.inStandardRange_iff _).mp hr
        obtain ⟨e₀⟩ := e
        exact S2019.false_of_reeG2_aut GL83.I713.i_7_13_1_holds hp hp2 hp3 hm e₀
          ⟨TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩, ⟨e₀⟩⟩ hA hcard
  · exfalso
    have hlt := S2019.s2019FactAmbAut_holds p q hp hp2 hq hq2 hqp _ hAmb A hA
    have : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)
    omega

end Red

end CFSG.LocalAnalysis.GLTheoremA.S267

end
