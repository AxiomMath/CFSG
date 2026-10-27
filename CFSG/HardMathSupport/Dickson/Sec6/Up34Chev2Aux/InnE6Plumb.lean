module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

namespace Up34Chev2

section Diag

set_option linter.unusedSectionVars false


theorem noL34Layer_e6InndiagConj_two (hI : Char2Hrat Tag.E6 .inner) (hS : Char2Hrat Tag.E6 .suN)
    (hD : Char2Hrat Tag.E6 .twoD) (hE : Char2Hrat Tag.E6 .exc) {F : Type} [Field F] [Finite F]
    {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (g : ↥(e6InndiagGL F))
    (hg3 : (g : ModGL Tag.E6 F) ^ 3 = 1) (hg1 : (g : ModGL Tag.E6 F) ≠ 1) :
    NoL34Layer (e6InndiagConj F g) := by
  set L := AlgebraicClosure F with hL
  set ι : F →+* L := algebraMap F L with hι
  have hroot : ∀ c : Fˣ, ∃ u : Lˣ, u ^ 3 = Units.map ι.toMonoidHom c := by
    intro c
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι c) (n := 3) (by norm_num)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hz
      exact c.ne_zero (ι.injective (hz.symm.trans (map_zero ι).symm))
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  have hgL : baseChangeGL ι (g : ModGL Tag.E6 F) ∈ adjointGroup Tag.E6 L :=
    map_e6InndiagGL_le ι hroot (Subgroup.mem_map_of_mem _ g.2)
  exact noL34Layer_exc_inner_untw_two (Or.inr (Or.inl rfl)) hI hS hD hE hf hF
    (e6InndiagConj F g) (g : ModGL Tag.E6 F) hgL (fun c => e6InndiagConj_apply g c) hg3 hg1

theorem noL34Layer_conj_adjointE6_two (hI : Char2Hrat Tag.E6 .inner)
    (hS : Char2Hrat Tag.E6 .suN) (hD : Char2Hrat Tag.E6 .twoD) (hE : Char2Hrat Tag.E6 .exc)
    {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (y : ↥(adjointGroup Tag.E6 F)) (hy3 : (MulAut.conj y : MulAut ↥(adjointGroup Tag.E6 F)) ^ 3 = 1)
    (hy1 : (MulAut.conj y : MulAut ↥(adjointGroup Tag.E6 F)) ≠ 1) :
    NoL34Layer (MulAut.conj y : MulAut ↥(adjointGroup Tag.E6 F)) := by
  have hZ : Subgroup.center ↥(adjointGroup Tag.E6 F) = ⊥ := center_adjointGroup_eq_bot
  have hy3' : y ^ 3 = 1 := by
    have h1 : (MulAut.conj (y ^ 3) : MulAut ↥(adjointGroup Tag.E6 F)) = MulAut.conj 1 := by
      rw [map_pow, map_one]
      exact hy3
    have h2 : y ^ 3 ∈ Subgroup.center ↥(adjointGroup Tag.E6 F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun h1 g
      simp only [MulAut.conj_apply, MulAut.one_apply, inv_one, mul_one, one_mul] at this
      calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [this]
        _ = y ^ 3 * g := by group
    rwa [hZ, Subgroup.mem_bot] at h2
  set g : ↥(e6InndiagGL F) := ⟨(y : ModGL Tag.E6 F), adjointGroup_le_e6InndiagGL F y.2⟩ with hg
  have hconj : e6InndiagConj F g = MulAut.conj y :=
    MulEquiv.ext fun c => Subtype.ext (by simp [e6InndiagConj_apply, hg, MulAut.conj_apply])
  rw [← hconj]
  refine noL34Layer_e6InndiagConj_two hI hS hD hE hf hF g ?_ ?_
  · change ((y : ModGL Tag.E6 F)) ^ 3 = 1
    rw [← Subgroup.coe_pow, hy3']
    rfl
  · intro h1
    apply hy1
    have : y = 1 := Subtype.ext h1
    rw [this, map_one]

theorem up34C2OutDiag_E6_holds (hI : Char2Hrat Tag.E6 .inner) (hS : Char2Hrat Tag.E6 .suN)
    (hD : Char2Hrat Tag.E6 .twoD) (hE : Char2Hrat Tag.E6 .exc) : Up34C2OutDiag_E6 := by
  intro f K _ _ hf hK ψ hψd hψinn hp
  obtain ⟨hψ3, hψ1, hno⟩ := (up34Pumpup_iff ψ).1 hp
  by_cases hK4 : 4 ≤ Nat.card K
  · rw [← range_e6InndiagConj K] at hψd
    obtain ⟨g, rfl⟩ := hψd
    have hg3 : g ^ 3 = 1 := by
      apply e6InndiagConj_injective K hK4
      rw [map_pow, map_one]
      exact hψ3
    refine hno (noL34Layer_e6InndiagConj_two hI hS hD hE hf hK g ?_ ?_)
    · have := congrArg (fun x : ↥(e6InndiagGL K) => (x : ModGL Tag.E6 K)) hg3
      simpa using this
    · intro h1
      apply hψ1
      have : g = 1 := Subtype.ext h1
      rw [this, map_one]
  · exfalso
    have hf1 : f = 1 := by
      by_contra hne
      have h2 : 2 ≤ f := by omega
      have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
      apply hK4
      rw [hK]
      omega
    have hcard : Nat.card K = 2 := by rw [hK, hf1]; rfl
    have h3 : ¬ 3 ∣ Nat.card K - 1 := by rw [hcard]; decide
    rw [e6Inndiag_eq_innerAut_of_not_dvd K h3] at hψd
    exact hψinn hψd

end Diag

section Family

set_option linter.unusedSectionVars false


theorem up34C2Inn_E6_holds (hI : Char2Hrat Tag.E6 .inner) (hS : Char2Hrat Tag.E6 .suN)
    (hD : Char2Hrat Tag.E6 .twoD) (hE : Char2Hrat Tag.E6 .exc) : Up34Chev2Inn FamE6 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hp
  cases d with
  | E6 q =>
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_E6 q hv e
    have hU : UntwistedChevalleyModel S .E6 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE'⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE'.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
    rw [hq2] at hFcard
    have hp' := hp.of_congr θ
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at hp'
    obtain ⟨hy3, hy1, hno⟩ := (up34Pumpup_iff _).1 hp'
    exact hno (noL34Layer_conj_adjointE6_two hI hS hD hE q.exponent_pos hFcard (θ x) hy3 hy1)
  | _ => exact hF.elim

end Family

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
