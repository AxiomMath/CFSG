module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PExcNormCore
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.I171
open CFSG.HardMathSupport.Solomon.Coordinator (PerfectInLayer)
open CFSG.ComponentClassification.OuterAutomorphisms (inner_le_innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.S267.Gen (CompNormal)


private theorem shapeModelNormAt_adjointGroup {τ : CFSG.Blueprint.Chevalley.Tag}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hG2 : τ = .G2 → 3 ≤ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hE6 : τ = .E6 → p = 3 → ¬ 3 ∣ Nat.card K - 1)
    (hPL : ∀ x : ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K), x ≠ 1 → x ^ p = 1 →
      PerfectInLayer (MulAut.conj x)) :
    ShapeModelNormAt ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K) p := by
  intro x y hx1 hxp _hyp hxy J hJ
  haveI : Fintype K := Fintype.ofFinite K
  have hCN : CompNormal (MulAut.conj x) := by
    by_cases hEp : τ = .E6 ∧ p = 3
    · obtain ⟨rfl, hp3⟩ := hEp
      exact compNormal_E6_charTwo_three (hE6 rfl hp3) x hx1 (by simpa [hp3] using hxp)
    · refine S267.Gen.compNormal_adjointGroup hτ (fun h => by have := hG2 h; omega) hp hp2
        ?_ ?_ (MulAut.conj x) ?_ ?_ ?_
      ·
        obtain ⟨n, -, hn⟩ := FiniteField.card K 2
        have hKn : Nat.card K = 2 ^ (n : ℕ) := by
          rw [Nat.card_eq_fintype_card]; exact hn
        rw [hKn]
        intro hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      · intro h h3
        exact hEp ⟨h, h3⟩
      · exact inner_le_innAutDerived _ ⟨x, rfl⟩
      · rw [← map_pow, hxp, map_one]
      · intro h
        exact hx1 (CFSG.mulAutConj_injective_of_center_eq_bot
          CFSG.LieType.Chevalley.center_adjointGroup_eq_bot h)
  exact mem_normalizer_glaPComponent_of_compNormal hxy (hPL x hx1 hxp) hCN hJ

theorem excUNorm_of (hL : CatLayer) (hI : ShapeModelNormIso) :
    SimpleNormModel (CharTwoOf KD264Lie.isExcUntwistedIdx) := by
  intro S _ _ p hp hp2 hcat hshape
  obtain ⟨i, hi, ⟨eCat⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])
  | lie dd =>
    obtain ⟨idx, hv⟩ := dd
    obtain ⟨hPexc, hPchar⟩ := hi
    cases idx with
    | G2 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_G2]; exact hPchar
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
      letI := hKf
      letI := hKfin
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have h4 : 4 ≤ Nat.card K := by
        rw [hKcard, TauCeti.PrimePower.card_def, hq2]
        have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        have hq3 : 3 ≤ 2 ^ q.exponent := by
          have h := hr
          simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
          rw [TauCeti.PrimePower.card_def, hq2] at h
          exact h
        have h2 : 2 ≤ q.exponent := by
          by_contra h
          have h1 : q.exponent ≤ 1 := by omega
          have hle : 2 ^ q.exponent ≤ 2 := by
            simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h1
          omega
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
      have hchar : (TauCeti.LieTypeIndex.G2 q).characteristic = 2 := by
        rw [TauCeti.LieTypeIndex.characteristic_G2]; exact hq2
      have hcatA : catalogIs ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)
          (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.G2 q, hv⟩, hchar, ⟨eAd.symm⟩⟩
      have hPL : ∀ x : ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K), x ≠ 1 → x ^ p = 1 →
          PerfectInLayer (MulAut.conj x) :=
        fun x hx1 hxp =>
          hL ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) p hp hp2 hcatA x hx1 hxp
      have hnorm := shapeModelNormAt_adjointGroup (τ := .G2) (K := K) (Or.inl rfl)
        (fun _ => by omega) hp hp2 (fun h => absurd h (by decide)) hPL
      exact hI _ _ (eAd.symm.trans eCat.symm) p hnorm
    | F4 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_F4]; exact hPchar
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
      letI := hKf
      letI := hKfin
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have hchar : (TauCeti.LieTypeIndex.F4 q).characteristic = 2 := by
        rw [TauCeti.LieTypeIndex.characteristic_F4]; exact hq2
      have hcatA : catalogIs ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 K)
          (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.F4 q, hv⟩, hchar, ⟨eAd.symm⟩⟩
      have hPL : ∀ x : ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 K), x ≠ 1 → x ^ p = 1 →
          PerfectInLayer (MulAut.conj x) :=
        fun x hx1 hxp =>
          hL ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 K) p hp hp2 hcatA x hx1 hxp
      have hnorm := shapeModelNormAt_adjointGroup (τ := .F4) (K := K) (Or.inr (Or.inl rfl))
        (fun h => absurd h (by decide)) hp hp2 (fun h => absurd h (by decide)) hPL
      exact hI _ _ (eAd.symm.trans eCat.symm) p hnorm
    | E6 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_E6]; exact hPchar
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
      letI := hKf
      letI := hKfin
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have hE6 : (.E6 : CFSG.Blueprint.Chevalley.Tag) = .E6 → p = 3 →
          ¬ 3 ∣ Nat.card K - 1 := by
        intro _ hp3 h3
        apply hshape
        refine ⟨.lie ⟨.E6 q, hv⟩, ⟨hp3, hq2, ?_⟩, ⟨eCat⟩⟩
        rw [hKcard] at h3
        exact h3
      have hchar : (TauCeti.LieTypeIndex.E6 q).characteristic = 2 := by
        rw [TauCeti.LieTypeIndex.characteristic_E6]; exact hq2
      have hcatA : catalogIs ↥(CFSG.Blueprint.Chevalley.adjointGroup .E6 K)
          (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.E6 q, hv⟩, hchar, ⟨eAd.symm⟩⟩
      have hPL : ∀ x : ↥(CFSG.Blueprint.Chevalley.adjointGroup .E6 K), x ≠ 1 → x ^ p = 1 →
          PerfectInLayer (MulAut.conj x) :=
        fun x hx1 hxp =>
          hL ↥(CFSG.Blueprint.Chevalley.adjointGroup .E6 K) p hp hp2 hcatA x hx1 hxp
      have hnorm := shapeModelNormAt_adjointGroup (τ := .E6) (K := K)
        (Or.inr (Or.inr (Or.inl rfl))) (fun h => absurd h (by decide)) hp hp2 hE6 hPL
      exact hI _ _ (eAd.symm.trans eCat.symm) p hnorm
    | E7 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_E7]; exact hPchar
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
      letI := hKf
      letI := hKfin
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have hchar : (TauCeti.LieTypeIndex.E7 q).characteristic = 2 := by
        rw [TauCeti.LieTypeIndex.characteristic_E7]; exact hq2
      have hcatA : catalogIs ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 K)
          (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.E7 q, hv⟩, hchar, ⟨eAd.symm⟩⟩
      have hPL : ∀ x : ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 K), x ≠ 1 → x ^ p = 1 →
          PerfectInLayer (MulAut.conj x) :=
        fun x hx1 hxp =>
          hL ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 K) p hp hp2 hcatA x hx1 hxp
      have hnorm := shapeModelNormAt_adjointGroup (τ := .E7) (K := K)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (fun h => absurd h (by decide)) hp hp2
        (fun h => absurd h (by decide)) hPL
      exact hI _ _ (eAd.symm.trans eCat.symm) p hnorm
    | E8 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_E8]; exact hPchar
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
      letI := hKf
      letI := hKfin
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have hchar : (TauCeti.LieTypeIndex.E8 q).characteristic = 2 := by
        rw [TauCeti.LieTypeIndex.characteristic_E8]; exact hq2
      have hcatA : catalogIs ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 K)
          (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.E8 q, hv⟩, hchar, ⟨eAd.symm⟩⟩
      have hPL : ∀ x : ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 K), x ≠ 1 → x ^ p = 1 →
          PerfectInLayer (MulAut.conj x) :=
        fun x hx1 hxp =>
          hL ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 K) p hp hp2 hcatA x hx1 hxp
      have hnorm := shapeModelNormAt_adjointGroup (τ := .E8) (K := K)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (fun h => absurd h (by decide)) hp hp2
        (fun h => absurd h (by decide)) hPL
      exact hI _ _ (eAd.symm.trans eCat.symm) p hnorm
    | _ => exact hPexc.elim

end CFSG.LocalAnalysis.GLTheoremA.F151

end
