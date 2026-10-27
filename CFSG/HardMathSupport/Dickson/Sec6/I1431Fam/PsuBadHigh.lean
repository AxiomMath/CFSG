module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBadRk
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split
public import CFSG.RankThree.PartOne.FOC.PSUModel
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBadCover

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.Sec66T

theorem odd_of_three_dvd_two_pow_add_one {f : ℕ} (h : 3 ∣ 2 ^ f + 1) : Odd f := by
  by_contra hf
  rw [Nat.not_odd_iff_even] at hf
  obtain ⟨k, rfl⟩ := hf
  have h1 : 2 ^ (k + k) % 3 = 1 := by
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  omega

@[expose] def FamPsuBadHigh : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => FamPsuBadRest t n p f ∧ 6 ≤ n

theorem y1431_noCfg_psuBadHigh (hGA : GriessAllModelsStatement) : Y1431NoCfgAt FamPsuBadHigh := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨⟨rfl, hn3, hdiv, hn6'⟩, hn6⟩ := hF
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨K, _, _, h, -, hq, ⟨e0⟩⟩ := CFSG.RankThree.PartOne.FOC.exists_psu_model hC
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  have hdvd : 3 ∣ p ^ f + 1 := (Nat.dvd_gcd_iff.1 hdiv).2
  have h2 : ¬(n = 6 ∧ p = 2 ∧ f = 1) := fun ⟨ha, hb, hc⟩ => hn6' ⟨ha, hb, by rw [hc]; exact odd_one⟩
  have hodd : ringChar K ≠ 2 ∨ 7 ≤ n := by
    by_cases hp : p = 2
    · right
      subst hp
      have hf := odd_of_three_dvd_two_pow_add_one hdvd
      by_contra hlt
      exact hn6' ⟨by omega, rfl, hf⟩
    · left
      haveI := h.charP
      rw [ringChar.eq K p]
      exact hp
  have h3K : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, mul_comm, pow_mul]
    have := Nat.sq_sub_sq (p ^ f) 1
    rw [one_pow] at this
    rw [this]
    exact Dvd.dvd.mul_right hdvd _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 := exists_prime_orderOf_dvd_card' 3 h3K
  let qY : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y)
  obtain ⟨ρ, hρ⟩ := exists_suHom_to_cover hGA h hC e0 (by omega) h2 qY
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le
  refine rkY_false_su c.rank h hn6 hdvd hodd hζ ρ qY
    (e0.symm.toMonoidHom.comp
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) hρ
    (fun y hy => (QuotientGroup.eq_one_iff y).2 hy) ?_
  intro g hg
  have hg' : e0.symm (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) g) = 1 := hg
  rw [map_eq_one_iff _ e0.symm.injective] at hg'
  exact (QuotientGroup.eq_one_iff g).1 hg'

end CFSG.HardMathSupport.Dickson.Sec6.I1431
