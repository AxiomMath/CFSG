module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrDispatch
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedMain
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinModelAut

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Generic

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem card_mulAut_eq_card_outer_mul (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) :
    Nat.card (MulAut Y) = Nat.card (Outer Y) * Nat.card Y := by
  have h1 := Subgroup.index_mul_card (inner Y)
  have h2 : Nat.card (inner Y) = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [h2] at h1
  exact h1.symm

theorem pow_three_dvd_card_of_relIndex {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {U Z : Subgroup G} (hU : IsPGroup p U) (hrel : p ^ 3 ≤ Z.relIndex U) :
    p ^ 3 ∣ Nat.card U := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hdvd : Z.relIndex U ∣ p ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card Z U
  obtain ⟨k, -, hko⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have h3 : 3 ≤ k := by
    by_contra hlt
    have h1 : p ^ k ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p ^ 3 ≤ p ^ 2 := hrel.trans (hko ▸ h1)
    have := hp.two_le
    nlinarith
  rw [hn]
  exact (pow_dvd_pow p h3).trans (hko ▸ hdvd)

theorem pow_three_dvd_card_of_outer_dvd_four
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hout : Nat.card (Outer Y) ∣ 4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U Z : Subgroup (MulAut Y)} (hU : IsPGroup p U) (hrel : p ^ 3 ≤ Z.relIndex U) :
    p ^ 3 ∣ Nat.card Y := by
  have h1 := pow_three_dvd_card_of_relIndex hp hU hrel
  have h2 : Nat.card U ∣ Nat.card (MulAut Y) := Subgroup.card_subgroup_dvd_card U
  rw [card_mulAut_eq_card_outer_mul hinj] at h2
  have hp4 : ¬ p ∣ 4 := by
    intro h
    have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hcop : Nat.Coprime (p ^ 3) (Nat.card (Outer Y)) :=
    Nat.Coprime.coprime_dvd_right hout
      (Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hp).2 hp4))
  exact hcop.dvd_of_dvd_mul_left (h1.trans h2)

end Generic

section Alt

theorem le_of_pow_three_dvd {M p B : ℕ} (hM : M ≠ 0) (h : p ^ 3 ∣ M) (hB : M < (B + 1) ^ 3) :
    p ≤ B := by
  by_contra hlt
  push Not at hlt
  have h1 : (B + 1) ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
  have h2 : p ^ 3 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) h
  omega

theorem not_pow_three_dvd_alt {n p : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 3 ∣ n.factorial / 2 := by
  intro h
  have hp3 : 2 ≤ p := hp.two_le
  rcases hn with rfl | rfl | rfl
  · have hb := le_of_pow_three_dvd (B := 3) (by norm_num [Nat.factorial]) h
      (by norm_num [Nat.factorial])
    interval_cases p
    all_goals try exact hp2 rfl
    all_goals try (norm_num at hp)
    all_goals (norm_num [Nat.factorial] at h)
  · have hb := le_of_pow_three_dvd (B := 7) (by norm_num [Nat.factorial]) h
      (by norm_num [Nat.factorial])
    interval_cases p
    all_goals try exact hp2 rfl
    all_goals try (norm_num at hp)
    all_goals (norm_num [Nat.factorial] at h)
  · have hb := le_of_pow_three_dvd (B := 27) (by norm_num [Nat.factorial]) h
      (by norm_num [Nat.factorial])
    interval_cases p
    all_goals try exact hp2 rfl
    all_goals try (norm_num at hp)
    all_goals (norm_num [Nat.factorial] at h)

theorem false_of_alt {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : Y ≃* alternatingGroup (Fin n)) (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U Z : Subgroup (MulAut Y)} (hU : IsPGroup p U)
    (hrel : p ^ 3 ≤ Z.relIndex U) : False := by
  have hn5 : 5 ≤ n := by omega
  have hout : Nat.card (Outer Y) ∣ 4 := by
    obtain ⟨e', -⟩ := CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism e
    obtain ⟨e'', -⟩ := e'
    rw [Nat.card_congr e''.toEquiv]
    exact CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n hn5
  have h := pow_three_dvd_card_of_outer_dvd_four hinj hout hp hp2 hU hrel
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hY : Nat.card Y = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  exact not_pow_three_dvd_alt hn hp hp2 (hY ▸ h)

end Alt

section SevenElements

theorem centralizes_of_card_27 {G : Type*} [Group G] [Finite G] {U : Subgroup G}
    (hU : Nat.card U = 27) {y : G} (hy : y ∈ Subgroup.normalizer (U : Set G)) {a : ℕ}
    (hya : y ^ 7 ^ a = 1) : ∀ u ∈ U, y * u = u * y := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fintype U := Fintype.ofFinite U
  let f : Function.End U := fun u => ⟨y * u * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy u).1 u.2⟩
  have hfpow : ∀ k : ℕ, ∀ u : U, ((f ^ k) u : G) = y ^ k * u * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp; rfl
    | succ k ih =>
      intro u
      rw [pow_succ]
      change ((f ^ k) (f u) : G) = _
      rw [ih]
      change y ^ k * (y * u * y⁻¹) * (y ^ k)⁻¹ = _
      group
  have hf1 : f ^ 7 ^ a = 1 := by
    funext u
    apply Subtype.ext
    rw [hfpow, hya]
    simp; rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := U) hf1
  set C : Subgroup G := U ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hfix : Fintype.card f.fixedPoints = Nat.card C := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun u => ⟨(u.1 : G), u.1.2, ?_⟩, fun c => ⟨⟨c.1, c.2.1⟩, ?_⟩, ?_, ?_⟩
    · have hu : f u.1 = u.1 := u.2
      have h1 : y * (u.1 : G) * y⁻¹ = u.1 := congrArg Subtype.val hu
      show (u.1 : G) ∈ Subgroup.centralizer ({y} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact (mul_inv_eq_iff_eq_mul.1 h1)
    · have h1 : y * (c.1 : G) = c.1 * y :=
        Subgroup.mem_centralizer_iff.1 c.2.2 y rfl
      show f ⟨c.1, c.2.1⟩ = ⟨c.1, c.2.1⟩
      apply Subtype.ext
      show y * (c.1 : G) * y⁻¹ = c.1
      rw [h1]; group
    · intro u; rfl
    · intro c; rfl
  have hCdvd : Nat.card C ∣ 27 := hU ▸ Subgroup.card_dvd_of_le inf_le_left
  have hC27 : Nat.card C = 27 := by
    have h27 : Fintype.card U = 27 := by rw [← Nat.card_eq_fintype_card]; exact hU
    rw [h27, hfix] at hmod
    have hdv : Nat.card C ∈ Nat.divisors 27 := Nat.mem_divisors.2 ⟨hCdvd, by norm_num⟩
    have : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [this] at hdv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdv
    rcases hdv with h | h | h | h <;> rw [h] at hmod ⊢ <;>
      first | rfl | (exfalso; revert hmod; decide)
  have hCU : C = U := Subgroup.eq_of_le_of_card_ge (inf_le_left : C ≤ U) (by rw [hU, hC27])
  intro u hu
  have : u ∈ C := hCU ▸ hu
  exact (Subgroup.mem_centralizer_iff.1 this.2 y rfl)

end SevenElements

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem exists_equiv_primeFormP_gen {Y : Type} [Group Y] {n p f : ℕ}
    (h : StatedClassicalModel Y .PSU n p f) :
    ∃ (K : Type) (_ : Field K) (hU : UnitaryFieldData p f K), ¬(n = 3 ∧ p ^ f = 2) ∧
      3 ≤ n ∧ Nonempty (Y ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.exists_mulEquiv_primeFormP h

theorem card_unitaryPSU_three_mul_gcd {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) :
    Nat.card (unitaryPSU h 3) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  rw [← CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three h,
    ← card_unitaryScalars h (by norm_num),
    (unitaryScalars h 3).card_eq_card_quotient_mul_card_subgroup]

theorem false_of_psu_three_three {Y : Type} [Group Y] [Finite Y]
    (h : StatedClassicalModel Y .PSU 3 3 1)
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) {U Z : Subgroup (MulAut Y)}
    {y : MulAut Y} (hU : IsPGroup p U) (hirr : IrrAct y U Z) (hrel : p ^ 3 ≤ Z.relIndex U)
    (hyU : y ∈ Subgroup.normalizer (U : Set (MulAut Y))) (hyr : ∃ a : ℕ, y ^ r ^ a = 1) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, hU3, hq, hn3, ⟨e⟩⟩ := exists_equiv_primeFormP_gen h
  obtain ⟨⟨eP⟩, -, -, hOutT, -⟩ := unitary_full_diagonal_outer_order hU3 hn3 hq
  have hOut : Nat.card (Outer Y) = 2 := by
    obtain ⟨⟨e', -⟩, -⟩ := (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism e)
    rw [Nat.card_congr e'.toEquiv, hOutT]
    norm_num
  have hY : Nat.card Y = 6048 := by
    have h1 := card_unitaryPSU_three_mul_gcd hU3
    rw [← Nat.card_congr (e.trans eP).toEquiv] at h1
    norm_num at h1
    exact h1
  have hAut : Nat.card (MulAut Y) = 12096 := by
    rw [card_mulAut_eq_card_outer_mul hinj, hOut, hY]
  have hU3dvd : p ^ 3 ∣ Nat.card U := pow_three_dvd_card_of_relIndex hp hU hrel
  have hUdvd : Nat.card U ∣ 12096 := hAut ▸ Subgroup.card_subgroup_dvd_card U
  have hp3d : p ^ 3 ∣ 12096 := hU3dvd.trans hUdvd
  have hpB : p ≤ 22 := le_of_pow_three_dvd (by norm_num) hp3d (by norm_num)
  have hp3 : p = 3 := by
    have hp2' : 2 ≤ p := hp.two_le
    interval_cases p
    all_goals try rfl
    all_goals try exact absurd rfl hp2
    all_goals try (norm_num at hp)
    all_goals (norm_num at hp3d)
  subst hp3
  obtain ⟨m, hm⟩ := hU.exists_card_eq
  have hm3 : m = 3 := by
    have h27 : 3 ^ 3 ∣ 3 ^ m := hm ▸ hU3dvd
    have hm_ge : 3 ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h27
    by_contra hne
    have : 3 ^ 4 ∣ 3 ^ m := pow_dvd_pow 3 (by omega)
    have h81 : 3 ^ 4 ∣ 12096 := this.trans (hm ▸ hUdvd)
    norm_num at h81
  have hU27 : Nat.card U = 27 := by rw [hm, hm3]; norm_num
  have hrel27 : Z.relIndex U = 27 := by
    have h1 : Z.relIndex U ∣ Nat.card U := Subgroup.relIndex_dvd_card Z U
    rw [hU27] at h1
    exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h1) (by simpa using hrel)
  have hZ1 : Z = ⊥ := by
    have h1 := Subgroup.card_mul_index (Z.subgroupOf U)
    rw [hU27] at h1
    have h2 : (Z.subgroupOf U).index = 27 := hrel27
    rw [h2] at h1
    have h3 : Nat.card (Z.subgroupOf U) = 1 := by omega
    have h4 : Z.subgroupOf U = ⊥ := Subgroup.eq_bot_of_card_eq _ h3
    refine (Subgroup.eq_bot_iff_forall Z).2 fun z hz => ?_
    have : (⟨z, hirr.1 hz⟩ : U) ∈ Z.subgroupOf U := hz
    rw [h4, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have h3U : 3 ∣ Nat.card U := by rw [hU27]; norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g, hg3⟩ := exists_prime_orderOf_dvd_card' 3 h3U
  have hcent : ∀ u ∈ U, y * u = u * y := by
    by_cases hy1 : y = 1
    · intro u _
      rw [hy1, one_mul, mul_one]
    · obtain ⟨a, ha⟩ := hyr
      have hord : orderOf y ∣ r ^ a := orderOf_dvd_of_pow_eq_one ha
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hr).1 hord
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hb
        exact hy1 (orderOf_eq_one_iff.1 hb)
      have hrdvd : r ∣ 12096 := by
        have : r ∣ orderOf y := hb ▸ dvd_pow_self r hb0
        exact (this.trans (orderOf_dvd_natCard y)).trans (hAut ▸ dvd_rfl)
      have hr7 : r = 7 := by
        have hr' : r ≤ 12096 := Nat.le_of_dvd (by norm_num) hrdvd
        have h12 : (12096 : ℕ) = 2 ^ 6 * 3 ^ 3 * 7 := by norm_num
        rw [h12] at hrdvd
        rcases (Nat.Prime.dvd_mul hr).1 hrdvd with h1 | h1
        · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
              (hr.dvd_of_dvd_pow h2)) hr2
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
              (hr.dvd_of_dvd_pow h2)) hr3
        · exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1
      subst hr7
      exact centralizes_of_card_27 hU27 hyU ha
  set g' : MulAut Y := (g : MulAut Y) with hg'
  have hg'3 : orderOf g' = 3 := by rw [hg', Subgroup.orderOf_coe]; exact hg3
  set V : Subgroup (MulAut Y) := Subgroup.zpowers g' with hV
  have hVU : V ≤ U := (Subgroup.zpowers_le).2 g.2
  have hyV : y ∈ Subgroup.normalizer (V : Set (MulAut Y)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hc := hcent h (hVU hh)
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    · intro hh
      have hc : y * (y * h * y⁻¹) = (y * h * y⁻¹) * y := hcent _ (hVU hh)
      have h1 : y * (y * h * y⁻¹) = y * h := by rw [hc]; group
      have h2 : y * h * y⁻¹ = h := mul_left_cancel h1
      rwa [h2] at hh
  rcases hirr.2 V (by rw [hZ1]; exact bot_le) hVU hyV with hVZ | hVU'
  · have hmem : g' ∈ V := Subgroup.mem_zpowers g'
    rw [hVZ, hZ1, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hg'3
    exact absurd hg'3 (by norm_num)
  · have h1 : Nat.card V = 3 := by rw [hV, Nat.card_zpowers, hg'3]
    rw [hVU', hU27] at h1
    exact absurd h1 (by norm_num)

end Unitary

section Final

theorem five_le_of_prime {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) : 5 ≤ r := by
  have h2 := hr.two_le
  by_contra hlt
  interval_cases r
  · exact hr2 rfl
  · exact hr3 rfl
  · exact absurd hr (by norm_num)

theorem yLevelIrrOn_small : YLevelIrrOn IsSmallTwo := by
  intro Y _ _ hC hinj p r hp hp2 hr hr2 hr3 hrp S₀ J hJ hcyc U Z y hU hZ hirr hrel hpow hyU hUJ
    hyJ hyr
  rcases hC with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨idx, hv⟩, hd, ⟨e⟩⟩
  · exact false_of_alt hn e hinj hp hp2 hU hrel
  · rcases hd with ⟨q, hq7, hd1⟩ | ⟨q, hq3, hd1⟩
    ·
      obtain rfl : idx = .A 1 q := hd1
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hpe : q.p = 7 ∧ q.exponent = 1 := by
        have h7 : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq7
        exact (Nat.Prime.pow_eq_iff (by norm_num)).1 h7
      rw [hpe.1, hpe.2] at h
      have h2 : StatedClassicalModel Y .PSL 3 2 1 :=
        CFSG.QuasithinUnique.Vol2Native.L239.statedClassicalModel_psl_three_two_of_psl_two_seven h
      exact false_of_two hinj (twoHub_of_model_psl h2) hp hr (five_le_of_prime hr hr2 hr3)
        (outPTwoGen_psl h2 hp hp2) (outPInner_psl_two h2 hr hr2) S₀ hJ hcyc hU hZ hirr hrel hpow
        hyU hUJ hyJ hyr
    ·
      obtain rfl : idx = .twistedA 2 q := hd1
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hpe : q.p = 3 ∧ q.exponent = 1 := by
        have h3 : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq3
        exact (Nat.Prime.pow_eq_iff (by norm_num)).1 h3
      rw [hpe.1, hpe.2] at h
      exact false_of_psu_three_three h hinj hp hp2 hr hr2 hr3 hU hirr hrel hyU hyr

end Final

end CFSG.AGLEmbedding.ParabAutIrr
