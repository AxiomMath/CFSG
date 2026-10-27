module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Cen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Ord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Prm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Thr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Tors

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

variable {V : Type} [CommGroup V] [Finite V] {u : MulAut V} {H : Subgroup (MulAut V)}
  {Bv : Subgroup V}

theorem exists_zeta (F : Ctx V u H Bv) {P M1 M2 : Subgroup (MulAut V)}
    (hPn : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P) (hPodd : Odd (Nat.card P))
    (hcommP : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) (hW : WreathMod H P M1 M2 u)
    (hdvd51 : Nat.card P ∣ 51) (q : ℕ) [Fact q.Prime] (hqd : q ∣ Nat.card P) (hq17 : q ≤ 17)
    (hq51 : ¬ q ^ 2 ∣ 51) :
    ∃ Q : Subgroup (MulAut V), Q ≤ P ∧ Nat.card Q = q ∧
      (∀ m ∈ M1, ∀ g ∈ Q, m * g = g * m) ∧ (∀ m ∈ M2, ∀ g ∈ Q, m * g = g * m) ∧
      ∃ ζ ∈ Q, ζ ≠ 1 ∧ ζ ^ q = 1 ∧ ∀ v : V, ζ v = v → v = 1 := by
  classical
  haveI : Finite (MulAut V) := inferInstance
  obtain ⟨Q, hQP, hQn, hQ1, hQexp⟩ := exists_torsion_subgroup H P hPn hcommP q hqd
  have hQodd : Odd (Nat.card Q) := hPodd.of_dvd_nat (Subgroup.card_dvd_of_le hQP)
  have hQcard : Nat.card Q = q :=
    card_eq_prime_of_torsion Q q 51 hQ1 hQexp ((Subgroup.card_dvd_of_le hQP).trans hdvd51) hq51
  have hcardAut : Nat.card (MulAut ↥Q) < 360 := card_mulAut_lt_of_card_prime Q q hQcard hq17
  have hN : ∀ n ∈ P, ∀ g ∈ Q, n * g = g * n := fun n hn g hg => hcommP n hn g (hQP hg)
  have hc1 := centralizes_of_quotEquivTo hW.le1 hQn hW.quot1 hcardAut hN
  have hc2 := centralizes_of_quotEquivTo hW.le2 hQn hW.quot2 hcardAut hN
  obtain ⟨⟨ζ, hζQ⟩, hζ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ1
  have hζ1' : ζ ≠ 1 := fun h => hζ1 (Subtype.ext h)
  have hQz : Q = Subgroup.zpowers ζ := eq_zpowers_of_card_eq_prime Q q hQcard hζQ hζ1'
  have hfpf : ∀ v : V, ζ v = v → v = 1 := by
    intro v hv
    refine fixed_eq_one F hQ1 hQodd hQn v (fun g hg => ?_)
    have hst : ζ ∈ MulAction.stabilizer (MulAut V) v := by
      rw [MulAction.mem_stabilizer_iff]
      exact hv
    have hg' : g ∈ MulAction.stabilizer (MulAut V) v :=
      (Subgroup.zpowers_le.mpr hst) (hQz ▸ hg)
    exact hg'
  exact ⟨Q, hQP, hQcard, hc1, hc2, ζ, hζQ, hζ1', hQexp ζ hζQ, hfpf⟩

theorem eq_bot_of_ctx (F : Ctx V u H Bv) {P M1 M2 : Subgroup (MulAut V)}
    (hPn : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P) (hPodd : Odd (Nat.card P))
    (hPu : ∀ p ∈ P, p * u = u * p → p = 1) (hW : WreathMod H P M1 M2 u) : P = ⊥ := by
  classical
  by_contra hP
  haveI : Finite (MulAut V) := inferInstance
  have hcommP : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p :=
    comm_of_fixedPointFree P u F.u_sq (fun p hp => hPn u F.u_mem p hp) hPu
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card P → p ∣ 255 := by
    intro p hp hpd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨Q, hQP, hQn, hQ1, hQexp⟩ := exists_torsion_subgroup H P hPn hcommP p hpd
    exact prime_dvd_255 F hQ1 (hPodd.of_dvd_nat (Subgroup.card_dvd_of_le hQP)) hQn p hQexp
  have hdvd51 : Nat.card P ∣ 51 :=
    dvd_51_of_dvd_prod hPodd hprime (sq_mul_card_dvd_aut F.sq F.card hW)
  have hP1 : Nat.card P ≠ 1 := fun h => hP (Subgroup.eq_bot_of_card_eq P h)
  have hcases : Nat.card P = 3 ∨ Nat.card P = 17 ∨ Nat.card P = 51 := by
    have hmem : Nat.card P ∈ Nat.divisors 51 := Nat.mem_divisors.2 ⟨hdvd51, by norm_num⟩
    have hdiv : Nat.divisors 51 = {1, 3, 17, 51} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have h17 : ¬ 17 ∣ Nat.card P := by
    intro hd
    haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    obtain ⟨Q, hQP, hQc, hc1, hc2, ζ, hζQ, hζ1, hζq, hfpf⟩ :=
      exists_zeta F hPn hPodd hcommP hW hdvd51 17 hd le_rfl (by norm_num)
    obtain ⟨x, hxM, hx2, hx1⟩ := exists_involution_of_quotEquivTo hW.quot1 hPodd
    exact false_of_order_seventeen F.sq F.card ζ x hζq hfpf hx2 hx1 (hc1 x hxM ζ hζQ).symm
  have h3 : Nat.card P = 3 := by
    rcases hcases with h | h | h
    · exact h
    · exact absurd (by omega) h17
    · exact absurd (by omega) h17
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Q, hQP, hQc, hc1, hc2, ζ, hζQ, hζ1, hζq, hfpf⟩ :=
    exists_zeta F hPn hPodd hcommP hW hdvd51 3 (by rw [h3]) (by norm_num) (by norm_num)
  have hQP' : Q = P := Subgroup.eq_of_le_of_card_ge hQP (by rw [hQc, h3])
  subst hQP'
  have hPc : ∀ p ∈ Q, ∀ m ∈ M1 ⊔ M2, m * p = p * m := by
    intro p hp m hm
    have hle : M1 ⊔ M2 ≤ Subgroup.centralizer ({p} : Set (MulAut V)) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (hc1 a ha p hp).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (hc2 a ha p hp).symm
    have := (Subgroup.mem_centralizer_iff.mp (hle hm)) p (Set.mem_singleton p)
    exact this.symm
  have hM12 := commute_of_central hW.p_le2 hW.comm hPc hcommP hW.quot2
  obtain ⟨x, hxM, hx2, hx1⟩ := exists_involution_of_quotEquivTo hW.quot1 hPodd
  exact false_of_order_three F.sq F.card ζ x hζq hfpf hx2 hx1 M2 Q (hW.p_le2 hζQ)
    (fun m hm => hc2 m hm ζ hζQ) (fun m hm => (hM12 x hxM m hm).symm) hcommP hW.quot2

end C10

end CFSG.OddStandard.SmallF3.Omega
