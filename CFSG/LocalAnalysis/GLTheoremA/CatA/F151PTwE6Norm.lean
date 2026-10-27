module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PExcNormCore
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.I171 CFSG.LocalAnalysis.GLTheoremA.S267.Gen
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration


private theorem compNormal_twE6_cat {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hcat : catalogIs S (onLie (CharTwoOf isTwE6Idx)))
    (hnotshape : ¬ catalogIs S (onLie (I171LieShape p)))
    {x : S} (hx1 : x ≠ 1) (hxp : x ^ p = 1) :
    CompNormal (MulAut.conj x) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨hstw, hchar⟩ := hi
    obtain ⟨di, hv⟩ := d
    cases di with
    | twistedE6 q =>
      obtain ⟨K, hKf, σ, hKcard, hσ, ⟨eK⟩⟩ := exists_catEquiv_twistedE6 q hv
      letI : Field K := hKf
      haveI : Finite K := Nat.finite_of_card_ne_zero (by
        rw [hKcard]
        exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
      let e' : S ≃* ↥(twistedE6RootGroup K σ) := e.trans eK
      have hq2 : q.p = 2 := by simpa using hchar
      have hcongr : MulAut.congr e' (MulAut.conj x) = MulAut.conj (e' x) := by
        ext y
        simp [MulAut.congr_apply, MulAut.conj_apply]
      by_cases hp3 : p = 3
      · subst p
        have hx'3 : (e' x) ^ 3 = 1 := by rw [← map_pow e' x 3, hxp, map_one]
        have hq3 : ¬ 3 ∣ q.p ^ q.exponent + 1 := by
          intro hdiv
          refine hnotshape ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩,
            ?_, ⟨e⟩⟩
          show I171LieShape 3 (TauCeti.LieTypeIndex.twistedE6 q)
          exact ⟨rfl, hq2, by rw [TauCeti.PrimePower.card_def]; exact hdiv⟩
        have hcomp : CompNormal (MulAut.conj (e' x)) :=
          compNormal_twE6_charTwo_three (q := q) (K := K) hq2 σ hKcard hσ hq3 (e' x)
            (fun h => hx1 ((MulEquiv.map_eq_one_iff e').mp h)) hx'3
        exact compNormal_of_congr e' (MulAut.conj x) (hcongr.symm ▸ hcomp)
      · have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
          exceptional_fixed_center_trivial TwistTag.E6 K σ
        have hβ1 : MulAut.conj (e' x) ≠ 1 := by
          intro h
          have hc : e' x ∈ Subgroup.center ↥(twistedE6RootGroup K σ) := by
            rw [Subgroup.mem_center_iff]
            intro y
            have hy : (e' x) * y * (e' x)⁻¹ = y := by
              simpa [MulAut.conj_apply] using
                congrArg (fun f : MulAut ↥(twistedE6RootGroup K σ) => f y) h
            have hg : (e' x) * y = y * (e' x) := by
              calc (e' x) * y = ((e' x) * y * (e' x)⁻¹) * (e' x) := by group
                _ = y * (e' x) := by rw [hy]
            exact hg.symm
          rw [hZ, Subgroup.mem_bot] at hc
          exact hx1 ((MulEquiv.map_eq_one_iff e').mp hc)
        have hx'p : (e' x) ^ p = 1 := by rw [← map_pow e' x p, hxp, map_one]
        have hβp : (MulAut.conj (e' x)) ^ p = 1 := by
          rw [← map_pow (MulAut.conj :
            ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)) (e' x) p,
            hx'p, map_one]
        have hinner : MulAut.conj (e' x) ∈
            CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
              ↥(twistedE6RootGroup K σ) :=
          CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _
            ⟨e' x, rfl⟩
        have hpℓ : p ≠ q.p := by rw [hq2]; exact hp2
        have hcomp : CompNormal (MulAut.conj (e' x)) :=
          compNormal_twistedE6 q.prime_p q.exponent_pos hKcard σ hσ hp hp2 hp3 hpℓ
            (MulAut.conj (e' x)) hinner hβp hβ1
        exact compNormal_of_congr e' (MulAut.conj x) (hcongr.symm ▸ hcomp)
    | A n q => exact absurd hstw (by simp [isTwE6Idx])
    | twistedA n q => exact absurd hstw (by simp [isTwE6Idx])
    | B n q => exact absurd hstw (by simp [isTwE6Idx])
    | C n q => exact absurd hstw (by simp [isTwE6Idx])
    | D n q => exact absurd hstw (by simp [isTwE6Idx])
    | twistedD n q => exact absurd hstw (by simp [isTwE6Idx])
    | E6 q => exact absurd hstw (by simp [isTwE6Idx])
    | E7 q => exact absurd hstw (by simp [isTwE6Idx])
    | E8 q => exact absurd hstw (by simp [isTwE6Idx])
    | F4 q => exact absurd hstw (by simp [isTwE6Idx])
    | G2 q => exact absurd hstw (by simp [isTwE6Idx])
    | trialityD4 q => exact absurd hstw (by simp [isTwE6Idx])
    | suzuki m => exact absurd hstw (by simp [isTwE6Idx])
    | reeG2 m => exact absurd hstw (by simp [isTwE6Idx])
    | reeF4 m => exact absurd hstw (by simp [isTwE6Idx])
    | tits => exact absurd hstw (by simp [isTwE6Idx])
  | cyclic p' hp' => exact absurd hi (by simp [onLie])
  | alternating n hn => exact absurd hi (by simp [onLie])
  | sporadic name => exact absurd hi (by simp [onLie])

theorem twE6Norm_of (hL : CatLayer) (hI : ShapeModelNormIso) :
    SimpleNormModel (CharTwoOf isTwE6Idx) := by
  intro S _ _ p hp hp2 hcat hnotshape
  have hcat2 : catalogIs S (onLie fun d : TauCeti.LieTypeIndex => d.characteristic = 2) := by
    obtain ⟨i, hi, he⟩ := hcat
    cases i with
    | lie d => exact ⟨.lie d, hi.2, he⟩
    | cyclic p' hp' => exact absurd hi (by simp [onLie])
    | alternating n hn => exact absurd hi (by simp [onLie])
    | sporadic name => exact absurd hi (by simp [onLie])
  intro x y hx1 hxp hyp hcomm J hJ
  exact mem_normalizer_glaPComponent_of_compNormal hcomm
    (hL S p hp hp2 hcat2 x hx1 hxp)
    (compNormal_twE6_cat hp hp2 hcat hnotshape hx1 hxp) hJ

end CFSG.LocalAnalysis.GLTheoremA.F151

end
