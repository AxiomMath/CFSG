module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9TwE6CovCube
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GF2
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoBound

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Chevalley.C2E6Std CFSG.EvenSmallLie.TwoE6
  CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.Blueprint.Chevalley

section Equiv

set_option linter.unusedSectionVars false


private theorem twE6Cov_isTE6n_one {i : TauCeti.CFSGIndex} (h : S9.isTE6two i) :
    S10.isTE6n 1 i := by
  cases i with
  | lie d' =>
    obtain ⟨d, hv⟩ := d'
    cases d with
    | twistedE6 q =>
      have hq2 : q.card = 2 := by simpa [S9.isTE6two, onLie] using h
      have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
      have hp : q.p = 2 := by
        have h1 : q.p ∣ 2 := by
          rw [← hpe]
          exact dvd_pow_self _ q.exponent_pos.ne'
        exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
      have he : q.exponent = 1 := by
        rw [hp] at hpe
        exact Nat.pow_right_injective (le_refl 2) (show 2 ^ q.exponent = 2 ^ 1 by rw [hpe])
      simpa [S10.isTE6n, onLie] using And.intro hp he
    | _ => simp [S9.isTE6two, onLie] at h
  | cyclic _ _ => simp [S9.isTE6two, onLie] at h
  | alternating _ _ => simp [S9.isTE6two, onLie] at h
  | sporadic _ => simp [S9.isTE6two, onLie] at h

theorem twE6Cov_equiv_stdGroup {X : Type} [Group X] (h : catalogIs X S9.isTE6two) :
    Nonempty (X ≃* ↥stdGroup) := by
  obtain ⟨i, hi, he⟩ := h
  exact (lieModel_twistedE6_two_iff X).1
    (CFSG.LocalAnalysis.GLTheoremA.T263.lieModel_twE6_of_catalogIs ⟨i, twE6Cov_isTE6n_one hi, he⟩)

end Equiv

section Lift

set_option linter.unusedSectionVars false


theorem twE6Cov_central_cube {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (hZ3 : IsPGroup 3 (Subgroup.center Q))
    (hQcat : catalogIs (Q ⧸ Subgroup.center Q) S9.isTE6two) {x : Q}
    (hx : x ^ 3 ∈ Subgroup.center Q) : x ^ 3 = 1 := by
  classical
  obtain ⟨e⟩ := twE6Cov_equiv_stdGroup hQcat
  let p : Q →* ↥stdGroup := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : p.ker = Subgroup.center Q := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective]
    exact QuotientGroup.ker_mk' _
  haveI : Group.IsPerfect Q := ⟨hQ.1⟩
  obtain ⟨D, _, _, η, φ, hηs, -, -, hηsq, hφs, hfib⟩ :=
    derived_fibre_facts (π := p) hp hker.le
  have hφk : ∀ c ∈ η.ker, φ c = 1 := by
    intro c hc
    have hc1 : η c = 1 := hc
    have hpc : p (φ c) = 1 := by rw [hfib, hc1, map_one]
    have hmem : φ c ∈ Subgroup.center Q := by rw [← hker]; exact hpc
    obtain ⟨k, hk⟩ := hZ3 ⟨φ c, hmem⟩
    have hk' : (φ c) ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hc2 : (φ c) ^ 2 = 1 := by rw [← map_pow, hηsq c hc, map_one]
    have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left k (by norm_num)
    have h := (pow_gcd_eq_one (a := φ c)).2 ⟨hk', hc2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
  obtain ⟨d, rfl⟩ := hφs x
  have h1 : p (φ d ^ 3) = 1 := (MonoidHom.mem_ker).1 (hker ▸ hx)
  have h2 : isogenyStd (η d) ^ 3 = 1 := by
    rw [← hfib d, ← map_pow]
    exact h1
  have h3 : (e6IsogenyFixed (frobQ 2 1) (η d)) ^ 3 = 1 := by
    apply baseChangeGL_injective fieldEquiv.toRingHom
    have h4 : ((isogenyStd (η d) : ↥stdGroup) : ModGL Tag.E6 C2E6Overlap.K) ^ 3 = 1 := by
      simpa using congrArg Subtype.val h2
    rw [map_pow, map_one]
    exact h4
  have hK : Nat.card (GaloisField 2 (2 * 1)) = 4 := by
    rw [GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  have h5 : η d ^ 3 = 1 := twE6Cov_cube_eq_one_of_frob hK (frobQ 2 1)
    (fun c => by rw [frobQ_apply]; norm_num) (η d) h3
  rw [← map_pow]
  exact hφk _ (by rw [MonoidHom.mem_ker, map_pow, h5])

end Lift

end CFSG.LocalAnalysis.GLTheoremA.I141F
