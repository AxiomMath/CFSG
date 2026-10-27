module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputs
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddCore
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnLift
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019A1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

private theorem dvd_mul_div' {a b c : ℕ} (hc : c ∣ b) : a ∣ a * b / c := by
  rw [Nat.mul_div_assoc a hc]
  exact dvd_mul_right a _

private theorem pow_dvd_orderA {r : ℕ} (hr : 1 ≤ r) : 3 ^ (r * (r + 1) / 2) ∣ orderA r 3 := by
  unfold orderA
  refine dvd_mul_div' ((Nat.gcd_dvd_right _ _).trans ?_)
  exact (show 3 - 1 ∣ 3 ^ 2 - 1 by norm_num).trans
    (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩))

private theorem pow_dvd_orderTwistedA {r : ℕ} (hr : 1 ≤ r) :
    3 ^ (r * (r + 1) / 2) ∣ orderTwistedA r 3 := by
  unfold orderTwistedA
  refine dvd_mul_div' ((Nat.gcd_dvd_right _ _).trans ?_)
  exact (show 3 + 1 ∣ (if Even 2 then 3 ^ 2 - 1 else 3 ^ 2 + 1) by decide).trans
    (Finset.dvd_prod_of_mem (fun i => if Even i then 3 ^ i - 1 else 3 ^ i + 1)
      (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩))

private theorem pow_dvd_orderBC {r : ℕ} (hr : 1 ≤ r) : 3 ^ (r * r) ∣ orderBC r 3 := by
  unfold orderBC
  refine dvd_mul_div' ((Nat.gcd_dvd_right _ _).trans ?_)
  exact (show 3 - 1 ∣ 3 ^ (2 * 1) - 1 by norm_num).trans
    (Finset.dvd_prod_of_mem (fun i => 3 ^ (2 * i) - 1) (Finset.mem_Icc.2 ⟨le_rfl, hr⟩))

private theorem pow_dvd_orderD (r : ℕ) : 3 ^ (r * (r - 1)) ∣ orderD r 3 := by
  unfold orderD
  rw [mul_assoc]
  exact dvd_mul_div' ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _))

private theorem pow_dvd_orderTwistedD (r : ℕ) : 3 ^ (r * (r - 1)) ∣ orderTwistedD r 3 := by
  unfold orderTwistedD
  rw [mul_assoc]
  exact dvd_mul_div' ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _))

private theorem not_sq_dvd_of_primes {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a b : ℕ)
    (l : List ℕ) (hl : ∀ r ∈ l, r.Prime) (hsq : ∀ r ∈ l, ¬ r ^ 2 ∣ l.prod) :
    ¬ p ^ 2 ∣ 2 ^ a * 3 ^ b * l.prod := by
  intro h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ a * 3 ^ b) := by
    refine Nat.Coprime.pow_left _ (Nat.Coprime.mul_right ?_ ?_)
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_three).2 (by omega))
  have h1 : p ^ 2 ∣ l.prod := hcop.dvd_of_dvd_mul_left h
  obtain ⟨r, hr, hpr⟩ := (Nat.Prime.prime hp).dvd_prod_iff.1 ((dvd_pow_self p two_ne_zero).trans h1)
  rw [(Nat.prime_dvd_prime_iff_eq hp (hl r hr)).1 hpr] at h1
  exact hsq r hr h1

private theorem card_le_of_not_sq_dvd {Y : Type} [Group Y] [Finite Y] {p k : ℕ} (hp : p.Prime)
    {A : Subgroup Y} (hk : Nat.card A = p ^ k) (h : ¬ p ^ 2 ∣ Nat.card Y) : Nat.card A ≤ p := by
  have hdvd : p ^ k ∣ Nat.card Y := hk ▸ Subgroup.card_subgroup_dvd_card A
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · rw [hk]
    interval_cases k
    · exact hp.one_lt.le
    · rw [pow_one]
  · exact absurd ((pow_dvd_pow p hk2).trans hdvd) h

private theorem three_pow_five_zmod : (3 : ZMod 11) ^ 5 = 1 := by decide

private theorem three_ne_one_zmod : (3 : ZMod 11) ≠ 1 := by decide

private theorem card_le_eleven_of_L5 {Y : Type} [Group Y] [Finite Y] (Q : PrimePower)
    (hv : (LieTypeIndex.A 4 Q).Valid) (e : Y ≃* (CFSGIndex.lie ⟨LieTypeIndex.A 4 Q, hv⟩).Group)
    (hchar : Q.p = 3) (hQe : Q.exponent = 1) {A : Subgroup Y} (hA : IsElemAbelian 11 A) :
    Nat.card A ≤ 11 := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hT := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA 4 Q hv
  have hcl : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL (4 + 1) 3 1 := by
    rcases hT.2 with h | ⟨h0, -⟩
    · rw [hchar, hQe] at h
      exact CFSG.QuasithinUnique.Setup.Family.statedClassicalModel_of_mulEquiv e.symm h
    · omega
  obtain ⟨K, _, _, hK, ⟨e₂⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (Or.inl ⟨by decide, hcl⟩)
  rw [pow_one] at hK
  have hAp : IsPGroup 11 A := CFSG.Open.IsElemAbelian.isPGroup hA
  set A' : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (4 + 1) K) :=
    A.map e₂.toMonoidHom with hA'def
  have hA'p : IsPGroup 11 A' := hAp.map _
  obtain ⟨P, hP, hPA⟩ := CFSG.RankThree.PartTwo.Sec4.L34Odd.exists_isPGroup_map_eq 11
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (4 + 1) K) A' hA'p (by
      rw [MonoidHom.range_eq_top.2
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective _ _)]
      exact le_top)
  let ι := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin (4 + 1)) K →* _)
  have hι : Function.Injective ι := Matrix.SpecialLinearGroup.toGL_injective
  obtain ⟨S, hS⟩ := (hP.map ι).exists_le_sylow
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : orderOf ((Nat.card K : ℕ) : ZMod 11) = 5 := by
    rw [hK, Nat.cast_ofNat]
    exact orderOf_eq_prime three_pow_five_zmod three_ne_one_zmod
  haveI hScyc : IsCyclic S := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isCyclic_sylow_gl_of_div
    (by decide) (by rw [hK]; norm_num) (by rw [h5]) S
  haveI : IsCyclic (P.map ι) := Subgroup.isCyclic_of_le hS
  haveI : IsCyclic P := isCyclic_of_injective (P.equivMapOfInjective ι hι).toMonoidHom
    (P.equivMapOfInjective ι hι).injective
  let f : ↥P →* ↥A' := ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (4 + 1) K).comp
    P.subtype).codRestrict A' fun x => by
      rw [← hPA]
      exact Subgroup.mem_map_of_mem _ x.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hPA] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  haveI : IsCyclic A' := isCyclic_of_surjective f hf
  haveI : IsCyclic A := isCyclic_of_injective (A.equivMapOfInjective e₂.toMonoidHom
    e₂.injective).toMonoidHom (A.equivMapOfInjective e₂.toMonoidHom e₂.injective).injective
  exact card_le_of_isCyclic_of_pow_eq_one (by norm_num)
    fun a => Subtype.ext (by simpa using hA.2 a a.2)

section Ten


theorem card_le_of_three_le_ten {Y : Type} [Group Y] [Finite Y] (d : LieTypeIndex)
    (hcat : catalogIs Y (onLie (· = d))) (hchar : d.characteristic = 3) (hfield : d.fieldOrder = 3)
    (h3 : (Nat.card Y).factorization 3 ≤ 10) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A : Subgroup Y} (hA : IsElemAbelian p A) : Nat.card A ≤ p := by
  classical
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d', hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  change d' = d at hi
  subst hi
  have hord : Nat.card Y = lieOrderFormula d' :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d', hv⟩ Y ⟨e⟩
  have hY0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have h11 : ¬ 3 ^ 11 ∣ Nat.card Y := fun h => by
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hY0).1 h
    omega
  have hAp : IsPGroup p A := CFSG.Open.IsElemAbelian.isPGroup hA
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hdup := ((LieTypeIndex.valid_iff _).1 hv).2
  have hQ : ∀ Q : PrimePower, Q.p = 3 → Q.card = 3 → Q.exponent = 1 := by
    intro Q hp3 hc3
    rw [PrimePower.card_def, hp3] at hc3
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simp only [hc3, pow_one])
  have hbig : ∀ N : ℕ, 11 ≤ N → 3 ^ N ∣ Nat.card Y → False := fun N hN h =>
    h11 ((pow_dvd_pow 3 hN).trans h)
  have hsmall : ∀ (a b : ℕ) (l : List ℕ), (∀ r ∈ l, r.Prime) → (∀ r ∈ l, ¬ r ^ 2 ∣ l.prod) →
      Nat.card Y = 2 ^ a * 3 ^ b * l.prod → Nat.card A ≤ p := fun a b l hl hsq hY =>
    card_le_of_not_sq_dvd hp hk (by rw [hY]; exact not_sq_dvd_of_primes hp hp5 a b l hl hsq)
  cases d' with
  | A r Q =>
    simp only [LieTypeIndex.characteristic_A, LieTypeIndex.fieldOrder_A] at hchar hfield
    have hO : lieOrderFormula (LieTypeIndex.A r Q) = orderA r 3 := by
      rw [← hfield]
      rfl
    rw [hO] at hord
    obtain ⟨hr1, hr4⟩ := hrange
    have hr2 : 2 ≤ r := by
      by_contra hr
      have := hr4 (by omega)
      omega
    by_cases hr5 : 5 ≤ r
    · refine (hbig (r * (r + 1) / 2) ?_ (hord ▸ pow_dvd_orderA hr1)).elim
      have : 30 ≤ r * (r + 1) := by nlinarith
      omega
    · interval_cases r
      · exact hsmall 4 3 [13] (by simp; norm_num) (by decide) (by rw [hord]; decide)
      · exact hsmall 7 6 [5, 13] (by simp; norm_num) (by decide) (by rw [hord]; decide)
      · by_cases hp11 : p = 11
        · subst hp11
          exact card_le_eleven_of_L5 Q hv e hchar (hQ Q hchar hfield) hA
        · refine card_le_of_not_sq_dvd hp hk ?_
          rw [hord, show orderA 4 3 = 2 ^ 9 * 3 ^ 10 * [5, 13].prod * 11 ^ 2 by decide]
          intro h
          have hcop : Nat.Coprime (p ^ 2) (11 ^ 2) :=
            Nat.Coprime.pow _ _ ((Nat.coprime_primes hp (by norm_num)).2 hp11)
          exact not_sq_dvd_of_primes hp hp5 9 10 [5, 13] (by simp; norm_num) (by decide)
            (hcop.dvd_of_dvd_mul_right h)
  | twistedA r Q =>
    simp only [LieTypeIndex.characteristic_twistedA, LieTypeIndex.fieldOrder_twistedA]
      at hchar hfield
    have hO : lieOrderFormula (LieTypeIndex.twistedA r Q) = orderTwistedA r 3 := by
      rw [← hfield]
      rfl
    rw [hO] at hord
    have hr2 : 2 ≤ r := hrange.1
    by_cases hr5 : 5 ≤ r
    · refine (hbig (r * (r + 1) / 2) ?_ (hord ▸ pow_dvd_orderTwistedA (by omega))).elim
      have : 30 ≤ r * (r + 1) := by nlinarith
      omega
    · interval_cases r
      · exact hsmall 5 3 [7] (by simp; norm_num) (by decide) (by rw [hord]; decide)
      · exact hsmall 7 6 [5, 7] (by simp; norm_num) (by decide) (by rw [hord]; decide)
      · exact hsmall 11 10 [5, 7, 61] (by simp; norm_num) (by decide) (by rw [hord]; decide)
  | B r Q =>
    simp only [LieTypeIndex.characteristic_B, LieTypeIndex.fieldOrder_B] at hchar hfield
    have hO : lieOrderFormula (LieTypeIndex.B r Q) = orderBC r 3 := by
      rw [← hfield]
      rfl
    rw [hO] at hord
    have hr3 : 3 ≤ r := by
      rcases hrange with ⟨hr2, -⟩
      by_contra hr
      apply hdup
      rw [LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨by omega, hfield⟩
    by_cases hr4 : 4 ≤ r
    · exact (hbig (r * r) (by nlinarith) (hord ▸ pow_dvd_orderBC (by omega))).elim
    · obtain rfl : r = 3 := by omega
      exact hsmall 9 9 [5, 7, 13] (by simp; norm_num) (by decide) (by rw [hord]; decide)
  | C r Q =>
    simp only [LieTypeIndex.characteristic_C, LieTypeIndex.fieldOrder_C] at hchar hfield
    have hO : lieOrderFormula (LieTypeIndex.C r Q) = orderBC r 3 := by
      rw [← hfield]
      rfl
    rw [hO] at hord
    have hr3 : 3 ≤ r := hrange.1
    by_cases hr4 : 4 ≤ r
    · exact (hbig (r * r) (by nlinarith) (hord ▸ pow_dvd_orderBC (by omega))).elim
    · obtain rfl : r = 3 := by omega
      exact hsmall 9 9 [5, 7, 13] (by simp; norm_num) (by decide) (by rw [hord]; decide)
  | D r Q =>
    simp only [LieTypeIndex.characteristic_D, LieTypeIndex.fieldOrder_D] at hchar hfield
    have hO : lieOrderFormula (LieTypeIndex.D r Q) = orderD r 3 := by
      rw [← hfield]
      rfl
    rw [hO] at hord
    have hr4 : 4 ≤ r := hrange
    refine (hbig (r * (r - 1)) ?_ (hord ▸ pow_dvd_orderD r)).elim
    have : 4 * 3 ≤ r * (r - 1) := Nat.mul_le_mul hr4 (by omega)
    omega
  | twistedD r Q =>
    simp only [LieTypeIndex.characteristic_twistedD, LieTypeIndex.fieldOrder_twistedD]
      at hchar hfield
    have hO : lieOrderFormula (LieTypeIndex.twistedD r Q) = orderTwistedD r 3 := by
      rw [← hfield]
      rfl
    rw [hO] at hord
    have hr4 : 4 ≤ r := hrange
    refine (hbig (r * (r - 1)) ?_ (hord ▸ pow_dvd_orderTwistedD r)).elim
    have : 4 * 3 ≤ r * (r - 1) := Nat.mul_le_mul hr4 (by omega)
    omega
  | G2 Q =>
    simp only [LieTypeIndex.characteristic_G2, LieTypeIndex.fieldOrder_G2] at hchar hfield
    have hO : lieOrderFormula (LieTypeIndex.G2 Q) = orderG2 3 := by
      rw [← hfield]
      rfl
    rw [hO] at hord
    exact hsmall 6 6 [7, 13] (by simp; norm_num) (by decide) (by rw [hord]; decide)
  | F4 Q =>
    simp only [LieTypeIndex.fieldOrder_F4] at hfield
    have hO : lieOrderFormula (LieTypeIndex.F4 Q) = orderF4 3 := by
      rw [← hfield]
      rfl
    exact (h11 (by rw [hord, hO]; decide)).elim
  | E6 Q =>
    simp only [LieTypeIndex.fieldOrder_E6] at hfield
    have hO : lieOrderFormula (LieTypeIndex.E6 Q) = orderE6 3 := by
      rw [← hfield]
      rfl
    exact (h11 (by rw [hord, hO]; decide)).elim
  | E7 Q =>
    simp only [LieTypeIndex.fieldOrder_E7] at hfield
    have hO : lieOrderFormula (LieTypeIndex.E7 Q) = orderE7 3 := by
      rw [← hfield]
      rfl
    exact (h11 (by rw [hord, hO]; decide)).elim
  | E8 Q =>
    simp only [LieTypeIndex.fieldOrder_E8] at hfield
    have hO : lieOrderFormula (LieTypeIndex.E8 Q) = orderE8 3 := by
      rw [← hfield]
      rfl
    exact (h11 (by rw [hord, hO]; decide)).elim
  | twistedE6 Q =>
    simp only [LieTypeIndex.fieldOrder_twistedE6] at hfield
    have hO : lieOrderFormula (LieTypeIndex.twistedE6 Q) = orderTwistedE6 3 := by
      rw [← hfield]
      rfl
    exact (h11 (by rw [hord, hO]; decide)).elim
  | trialityD4 Q =>
    simp only [LieTypeIndex.fieldOrder_trialityD4] at hfield
    have hO : lieOrderFormula (LieTypeIndex.trialityD4 Q) = orderTrialityD4 3 := by
      rw [← hfield]
      rfl
    exact (h11 (by rw [hord, hO]; decide)).elim
  | suzuki m => simp at hchar
  | reeG2 m =>
    simp only [LieTypeIndex.fieldOrder_reeG2] at hfield
    have hm : 1 ≤ m := hrange
    have : 3 ^ 3 ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  | reeF4 m => simp at hchar
  | tits => simp at hchar

theorem card_aut_le_of_three_le_ten (hout : S2019ChevOutThree) {Y : Type} [Group Y] [Finite Y]
    (d : LieTypeIndex) (hcat : catalogIs Y (onLie (· = d))) (hchar : d.characteristic = 3)
    (hfield : d.fieldOrder = 3) (h3 : (Nat.card Y).factorization 3 ≤ 10)
    (hZ : Subgroup.center Y = ⊥) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A : Subgroup (MulAut Y)} (hA : IsElemAbelian p A) : Nat.card A ≤ p := by
  classical
  have hker : (MulAut.conj : Y →* MulAut Y).ker = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    rw [← hZ, Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut Y => φ g) hy
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * y = (y * g * y⁻¹) * y := by rw [h1]
      _ = y * g := by group
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have hle : A ≤ (MulAut.conj : Y →* MulAut Y).range := by
    intro a ha
    obtain ⟨y, hy⟩ := hout Y d hcat hchar hfield h3 p hp hp5 a (hA.2 a ha)
    exact ⟨y, hy.symm⟩
  set A' : Subgroup Y := A.comap MulAut.conj with hA'
  have hmap : A'.map MulAut.conj = A := by rw [Subgroup.map_comap_eq, inf_eq_right.2 hle]
  have hcard : Nat.card A' = Nat.card A := by rw [← hmap, Subgroup.card_map_of_injective hinj]
  have hA'el : IsElemAbelian p A' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun y hy => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (hA.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
    · rw [map_pow, map_one]
      exact hA.2 _ hy
  rw [← hcard]
  exact card_le_of_three_le_ten d hcat hchar hfield h3 hp hp5 hA'el

end Ten

end CFSG.LocalAnalysis.GLTheoremA.S2019
