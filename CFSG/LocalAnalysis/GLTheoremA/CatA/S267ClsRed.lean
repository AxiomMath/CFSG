module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcCoreDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019A1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

@[expose] def BadClsAt (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ (S B : Subgroup Ω), S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        d.1.characteristic = q → Nonempty (PSimple p S ≃* (TauCeti.CFSGIndex.lie d).Group) →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
        p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
        ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B

section Red


theorem false_of_A1 {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqp : q ≠ p) {T : Type} [Group T] [Finite T] {Q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.A 1 Q).Valid} (hQp : Q.p = q)
    (e : T ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 Q, hv⟩).Group)
    {A : Subgroup (MulAut T)} (hA : IsElemAbelian p A) (hcard : p ^ 3 ≤ Nat.card A) : False := by
  have hL := S2019.lieModel_A1 Q hv e
  obtain ⟨⟨-, -, -, -, hn3⟩, F, hFf, hFfin, hcardF, ⟨e2⟩⟩ :=
    hL.statedClassicalModel (by decide)
  rw [hQp] at hcardF hn3
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hge : q ≤ q ^ Q.exponent := Nat.le_self_pow (by
    rintro h0
    rw [h0, pow_zero] at hcardF
    exact absurd hcardF (by
      haveI := hFfin
      exact (Finite.one_lt_card).ne')) q
  have hF : CFSG.GH74.GLS.IVK.L2Field F := by
    refine ⟨?_, ?_⟩
    · rw [hcardF]; exact (hq.odd_of_ne_two hq2).pow
    · have hne : q ^ Q.exponent ≠ 3 := fun h => hn3 (by rw [h])
      rw [hcardF]; omega
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hcardF]
    intro hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd)).symm
  have h2 := S2019.card_le_sq_aut_L2 hF e2 hp hp2 hpF hA
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem s267FactBadCls_of_at (hcore : S267FactBadExcCore)
    (h : ∀ d : TauCeti.ValidLieTypeIndex, S267ClassicalIdx d.1 → (∀ Q, d.1 ≠ .A 1 Q) →
      BadClsAt d) :
    S267FactBadCls := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ hK S B hSn hperf hSp hChev _hcl hBel hSB hrank hB4 hBC hp3B hHq
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
      have hcls : S267ClassicalIdx d → (∀ Q, d ≠ .A 1 Q) →
          S267ConcA p S B ∨ S267ConcBCDE p q S B := fun hc hA1 =>
        h ⟨d, hv⟩ hc hA1 p q hp hp2 hq hq2 hqp Ω hK S B hSn hperf hSp hchar e hBel hSB hrank hB4
          hBC hp3B hHq
      have hexc : S2019.S2019ExcCoreIdx d → S267ConcA p S B ∨ S267ConcBCDE p q S B := fun hc =>
        hcore p q hp hp2 hq hq2 hqp Ω hK S B hSn hperf hSp ⟨.lie ⟨d, hv⟩, ⟨hchar, hc⟩, e⟩ hBel hSB
          hrank hB4 hBC hp3B hHq
      cases d with
      | A n Q =>
        by_cases hn : n = 1
        · subst hn
          exfalso
          obtain ⟨e₀⟩ := e
          have hQp : Q.p = q := by rwa [TauCeti.LieTypeIndex.characteristic_A] at hchar
          exact false_of_A1 hp hp2 hq hq2 hqp hQp e₀ hA hcard
        · exact hcls trivial fun Q' h' => hn (TauCeti.LieTypeIndex.A.inj h').1
      | twistedA n Q => exact hcls trivial fun Q' h' => by cases h'
      | B n Q => exact hcls trivial fun Q' h' => by cases h'
      | C n Q => exact hcls trivial fun Q' h' => by cases h'
      | D n Q => exact hcls trivial fun Q' h' => by cases h'
      | twistedD n Q => exact hcls trivial fun Q' h' => by cases h'
      | E6 Q => exact hexc trivial
      | E7 Q => exact hexc trivial
      | E8 Q => exact hexc trivial
      | F4 Q => exact hexc trivial
      | G2 Q => exact hexc trivial
      | twistedE6 Q => exact hexc trivial
      | trialityD4 Q => exact hexc trivial
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

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
