module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256m2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256p

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256m (IsGF4Type IsGF4Comp GF4CompsOn)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Orders

theorem defField_eq_kd264FieldSize (d : TauCeti.LieTypeIndex) :
    Inputs256c.defField d = CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d := by
  cases d <;> rfl

theorem three_dvd_two_pow_sub_one_of_even {f : ℕ} (hf : Even f) : 3 ∣ 2 ^ f - 1 := by
  obtain ⟨k, rfl⟩ := hf
  have h : (2 : ℕ) ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
  rw [h]
  simpa using Nat.sub_one_dvd_pow_sub_one 4 k

theorem not_three_dvd_two_pow_add_one_of_even {f : ℕ} (hf : Even f) : ¬ 3 ∣ 2 ^ f + 1 := by
  intro h
  have h1 := three_dvd_two_pow_sub_one_of_even hf
  have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : 3 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h h1
  rw [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at h2
  norm_num at h2

theorem three_dvd_sq_sub_one_of_even {f : ℕ} (hf : Even f) : 3 ∣ (2 ^ f) ^ 2 - 1 :=
  (three_dvd_two_pow_sub_one_of_even hf).trans (Nat.sub_one_dvd_pow_sub_one _ 2)

theorem three_dvd_div_of_mul_dvd {N g : ℕ} (hg : 0 < g) (h : g * 3 ∣ N) : 3 ∣ N / g := by
  obtain ⟨c, rfl⟩ := h
  rw [mul_assoc, Nat.mul_div_cancel_left _ hg]
  exact dvd_mul_right 3 c

theorem three_dvd_div_of_coprime {N g : ℕ} (h3 : 3 ∣ N) (hg : g ∣ N) (hcop : ¬ 3 ∣ g) : 3 ∣ N / g := by
  have hg0 : 0 < g := Nat.pos_of_ne_zero fun h0 => hcop (h0 ▸ dvd_zero 3)
  obtain ⟨c, rfl⟩ := hg
  rw [Nat.mul_div_cancel_left _ hg0]
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hcop).dvd_of_dvd_mul_left h3

theorem gcd_eq_one_of_odd_of_dvd_four {a b : ℕ} (ha : a ∣ 4) (hb : Odd b) : Nat.gcd a b = 1 := by
  have h1 : Nat.gcd a b ∣ 4 := (Nat.gcd_dvd_left a b).trans ha
  have h2 : Odd (Nat.gcd a b) := hb.of_dvd_nat (Nat.gcd_dvd_right a b)
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4] at h1
  obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rw [hgi] at h2 ⊢
  rcases i with _ | i
  · rfl
  · exact absurd h2 (by rw [Nat.not_odd_iff_even]; exact (Nat.even_pow' (by omega)).2 even_two)

theorem three_dvd_evenLieOrder_of_even {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hf : Even f) : 3 ∣ CFSG.SeitzReduction.F4Pilot.evenLieOrder t n f := by
  have hf1 : 1 ≤ f := hadm.2.1
  have hq2 := three_dvd_sq_sub_one_of_even hf
  have hq1 := three_dvd_two_pow_sub_one_of_even hf
  have hq1' := not_three_dvd_two_pow_add_one_of_even hf
  have hqe : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
  have hqo : Odd (2 ^ f - 1) := Nat.Even.sub_odd Nat.one_le_two_pow hqe odd_one
  have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  cases t with
  | PSL =>
    have hn : 2 ≤ n := hadm.2.2.1
    obtain ⟨j, hj⟩ := hf
    have h4 : (2 : ℕ) ^ f = 4 ^ j := by rw [hj, ← two_mul, pow_mul]; norm_num
    have hj1 : 1 ≤ j := by omega
    have h := Inputs256m.three_dvd_orderPSL_four_pow hj1 hn
    show 3 ∣ CFSG.Open.ordA (n - 1) (2 ^ f)
    unfold CFSG.Open.ordA
    rw [h4, show n - 1 + 1 = n by omega, show (n - 1) * n = n * (n - 1) from Nat.mul_comm _ _]
    exact h
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    show 3 ∣ CFSG.Open.ordTwistedA (n - 1) (2 ^ f)
    unfold CFSG.Open.ordTwistedA
    refine three_dvd_div_of_mul_dvd (Nat.gcd_pos_of_pos_left _ (by omega)) ?_
    have h2mem : 2 ∈ Finset.Icc 2 (n - 1 + 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
    have hfac : (((2 ^ f : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = (2 ^ f + 1) * (2 ^ f - 1) := by
      have h : (((2 ^ f : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = (((2 ^ f + 1) * (2 ^ f - 1) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hpos]
        ring
      rw [h, Int.toNat_natCast]
    have hg : Nat.gcd (n - 1 + 1) (2 ^ f + 1) * 3 ∣ (2 ^ f + 1) * (2 ^ f - 1) :=
      mul_dvd_mul (Nat.gcd_dvd_right _ _) hq1
    refine Dvd.dvd.mul_left (hg.trans ?_) _
    rw [← hfac]
    exact Finset.dvd_prod_of_mem (fun i => (((2 ^ f : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) h2mem
  | PSp =>
    have hn : 2 ≤ n := hadm.2.2.1
    show 3 ∣ CFSG.Open.ordBC n (2 ^ f)
    unfold CFSG.Open.ordBC
    rw [gcd_eq_one_of_odd_of_dvd_four (by norm_num) hqo, Nat.div_one]
    refine Dvd.dvd.mul_left ?_ _
    have h1mem : 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
    exact hq2.trans (Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) h1mem)
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    show 3 ∣ CFSG.Open.ordD n (2 ^ f)
    unfold CFSG.Open.ordD
    have hodd : Odd ((2 ^ f) ^ n - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) (hqe.pow_of_ne_zero (by omega)) odd_one
    rw [gcd_eq_one_of_odd_of_dvd_four dvd_rfl hodd, Nat.div_one]
    refine Dvd.dvd.mul_left ?_ _
    have h1mem : 1 ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
    exact hq2.trans (Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) h1mem)
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    show 3 ∣ CFSG.Open.ordTwistedD n (2 ^ f)
    unfold CFSG.Open.ordTwistedD
    have hodd : Odd ((2 ^ f) ^ n + 1) := (hqe.pow_of_ne_zero (by omega)).add_one
    rw [gcd_eq_one_of_odd_of_dvd_four dvd_rfl hodd, Nat.div_one]
    refine Dvd.dvd.mul_left ?_ _
    have h1mem : 1 ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
    exact hq2.trans (Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) h1mem)
  | G2 =>
    show 3 ∣ CFSG.Open.ordG2 (2 ^ f)
    exact Dvd.dvd.mul_left hq2 _
  | F4 =>
    show 3 ∣ CFSG.Open.ordF4 (2 ^ f)
    exact Dvd.dvd.mul_left hq2 _
  | E6 =>
    show 3 ∣ CFSG.Open.ordE6 (2 ^ f)
    unfold CFSG.Open.ordE6
    refine three_dvd_div_of_mul_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num)) ?_
    have hq6 : 3 ∣ (2 ^ f) ^ 6 - 1 := by
      have : (2 ^ f) ^ 6 = ((2 ^ f) ^ 2) ^ 3 := by ring
      rw [this]
      exact hq2.trans (Nat.sub_one_dvd_pow_sub_one _ 3)
    have h9 : Nat.gcd 3 (2 ^ f - 1) * 3 ∣ ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) :=
      mul_dvd_mul ((Nat.gcd_dvd_left _ _).trans hq6) hq2
    refine h9.trans ?_
    exact ⟨(2 ^ f) ^ 36 * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 9 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 5 - 1),
      by ring⟩
  | E7 =>
    show 3 ∣ CFSG.Open.ordE7 (2 ^ f)
    unfold CFSG.Open.ordE7
    rw [gcd_eq_one_of_odd_of_dvd_four (by norm_num) hqo, Nat.div_one]
    exact Dvd.dvd.mul_left hq2 _
  | E8 =>
    show 3 ∣ CFSG.Open.ordE8 (2 ^ f)
    exact Dvd.dvd.mul_left hq2 _
  | twistedE6 =>
    show 3 ∣ CFSG.Open.ordTwistedE6 (2 ^ f)
    unfold CFSG.Open.ordTwistedE6
    have h3N := Dvd.dvd.mul_left hq2 ((2 ^ f) ^ 36 * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 9 + 1) *
      ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 5 + 1))
    refine three_dvd_div_of_coprime h3N ((Nat.gcd_dvd_left _ _).trans h3N) ?_
    intro h
    exact hq1' (h.trans (Nat.gcd_dvd_right _ _))
  | trialityD4 =>
    show 3 ∣ CFSG.Open.ordTrialityD4 (2 ^ f)
    exact Dvd.dvd.mul_left hq2 _
  | twistedB2 => exact absurd hf (Nat.not_even_iff_odd.2 hadm.2.2.2.2.1)
  | twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  | twistedF4 => exact absurd hf (Nat.not_even_iff_odd.2 hadm.2.2.2.2.1)
  | Tits => exact absurd hf (by rw [hadm.2.2.2.2]; decide)

end Orders

section Commuting

theorem mem_iSup_of_twoElement_of_commute {G : Type*} [Group G] [Finite G] {ι : Type*} [Finite ι]
    (A P : ι → Subgroup G) (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (hP : ∀ i, ∀ a ∈ A i, (∃ n : ℕ, a ^ 2 ^ n = 1) → a ∈ P i)
    {y : G} (hy : y ∈ ⨆ i, A i) (hy2 : ∃ n : ℕ, y ^ 2 ^ n = 1) : y ∈ ⨆ i, P i := by
  classical
  haveI := Fintype.ofFinite ι
  have hcomm : Pairwise fun i j => ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y :=
    fun i j hij x y hx hy => hc i j hij x hx y hy
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm)] at hy
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨n, hn⟩ := hy2
  set N := Nat.card G with hN
  have hN0 : N ≠ 0 := Nat.card_pos.ne'
  set a := N.factorization 2 with ha
  have hcop : Nat.Coprime (2 ^ a) (N / 2 ^ a) :=
    Nat.Coprime.pow_left a (Nat.coprime_ordCompl Nat.prime_two hN0)
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hcop 1 0
  have hdvd : N / 2 ^ a ∣ k := Nat.modEq_zero_iff_dvd.1 hk0
  have hNk : N ∣ k * 2 ^ a := by
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨t, ?_⟩
    rw [ht, mul_comm (N / 2 ^ a) t, mul_assoc, Nat.div_mul_cancel (Nat.ordProj_dvd N 2)]
    ring
  have h2k : ∀ g : G, (g ^ k) ^ 2 ^ a = 1 := by
    intro g
    rw [← pow_mul]
    obtain ⟨t, ht⟩ := hNk
    rw [ht, pow_mul, pow_card_eq_one', one_pow]
  have hyk : (Subgroup.noncommPiCoprod hcomm z) ^ k = Subgroup.noncommPiCoprod hcomm z := by
    have ho : orderOf (Subgroup.noncommPiCoprod hcomm z) ∣ 2 ^ a := by
      obtain ⟨b, -, hob⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn)
      rw [hob]
      have h2N : 2 ^ b ∣ N := by
        rw [← hob]
        exact orderOf_dvd_natCard _
      exact pow_dvd_pow 2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).1 h2N)
    have hmod : k ≡ 1 [MOD orderOf (Subgroup.noncommPiCoprod hcomm z)] := Nat.ModEq.of_dvd ho hk1
    rw [pow_eq_pow_iff_modEq.2 hmod, pow_one]
  rw [← hyk, ← map_pow, Subgroup.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
  have hmem : (((z ^ k) i : A i) : G) = (z i : G) ^ k := by
    rw [Pi.pow_apply, SubgroupClass.coe_pow]
  rw [hmem]
  exact Subgroup.mem_iSup_of_mem i (hP i _ (pow_mem (z i).2 k) ⟨a, h2k _⟩)

theorem commutator_iSup_eq_self_of_perfect {G : Type*} [Group G] {ι : Type*} (P : ι → Subgroup G)
    (hP : ∀ i, ⁅P i, P i⁆ = P i) : ⁅⨆ i, P i, ⨆ i, P i⁆ = ⨆ i, P i := by
  refine le_antisymm ?_ (iSup_le fun i => ?_)
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
      (Subgroup.inv_mem _ hb)
  · calc P i = ⁅P i, P i⁆ := (hP i).symm
      _ ≤ ⁅⨆ i, P i, ⨆ i, P i⁆ := Subgroup.commutator_mono (le_iSup P i) (le_iSup P i)

theorem fixSubgroup_conj_eq_centralizer_gf4 {X : Type*} [Group X] (g : X) :
    fixSubgroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set X) := by
  ext h
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun e => e.symm, fun e => e.symm⟩

end Commuting

section Catalogue


theorem three_dvd_card_of_isGF4Type {X : Type} [Group X] (h : IsGF4Type X) : 3 ∣ Nat.card X := by
  obtain ⟨d', hd2, hk, ⟨e⟩⟩ := h
  obtain ⟨t, n, f, hM, hf, -⟩ := Inputs256m.exists_lieModel_two_even_of_gf4 d' hd2 hk e
  rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM]
  exact three_dvd_evenLieOrder_of_even (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hM) hf

theorem isAltFive_or_isGF4Type_of_catalogueOver {X : Type} [Group X] {j : ℕ} (hj : 1 ≤ j)
    (h : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.CatalogueOver 2 (4 ^ j) X) :
    MovingAround.IsAltType 5 (X ⧸ Subgroup.center X) ∨ IsGF4Type (X ⧸ Subgroup.center X) := by
  obtain ⟨i, ⟨φ⟩, hi⟩ := h
  have h4 : 4 ≤ 4 ^ j := Nat.le_self_pow (by omega) 4
  cases i with
  | lie e =>
    rcases hi with ⟨hch, hfs, -⟩ | ⟨-, h2, -⟩ | ⟨h3, -⟩
    · exact Or.inr ⟨e, hch, ⟨j, hj, (defField_eq_kd264FieldSize e.1).trans hfs⟩, ⟨φ⟩⟩
    · omega
    · omega
  | alternating n hn =>
    rcases hi with ⟨rfl, -⟩ | ⟨-, ⟨-, h2⟩ | ⟨h3, -⟩⟩ | ⟨-, -, h2⟩
    · exact Or.inl ⟨φ⟩
    · omega
    · omega
    · omega
  | cyclic p hp => exact hi.elim
  | sporadic s => exact hi.elim

theorem isGF4Comp_of_catalogueOver {S : Type} [Group S] {β : MulAut S} {K : Subgroup S}
    (hK : IsComponentOf K (fixSubgroup β)) {j : ℕ} (hj : 1 ≤ j)
    (h : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.CatalogueOver 2 (4 ^ j) ↥K) : IsGF4Comp β K := by
  have ht := isAltFive_or_isGF4Type_of_catalogueOver hj h
  refine ⟨hK.2.1, hK.2.2, ?_, ht⟩
  rcases ht with ⟨⟨φ⟩⟩ | hg
  · rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  · exact three_dvd_card_of_isGF4Type hg

theorem glaLayer_le_iSup_isGF4Comp {S : Type} [Group S] {β : MulAut S}
    (h : ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) → IsGF4Comp β K) :
    GLALayer (fixSubgroup β) ≤ ⨆ (J : Subgroup S) (_ : IsGF4Comp β J), J := by
  rw [CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_eq_sSup]
  exact sSup_le fun K hK =>
    le_iSup₂_of_le (f := fun (J : Subgroup S) (_ : IsGF4Comp β J) => J) K (h K hK) le_rfl

end Catalogue

section Symplectic

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem subsingleton_specialLinearGroup_of_le_one {m : ℕ} (hm : m ≤ 1) (E : Type) [Field E] :
    Subsingleton (Matrix.SpecialLinearGroup (Fin m) E) := by
  refine ⟨fun A B => Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
  rcases Nat.lt_or_ge m 1 with h0 | h1
  · exact absurd i.2 (by omega)
  · obtain rfl : m = 1 := by omega
    have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    subst hi
    subst hj
    have hA := A.2
    have hB := B.2
    rw [Matrix.det_fin_one] at hA hB
    rw [hA, hB]

theorem exists_perfect_twoElement_of_gl {G : Type*} [Group G] {A : Subgroup G} {m : ℕ} {E : Type}
    [Field E] [Finite E] (hE : ringChar E = 2) (h4 : 4 ≤ Nat.card E) (φ : A ≃* GL (Fin m) E) :
    ∃ P : Subgroup G, P ≤ A ∧ ⁅P, P⁆ = P ∧ ∀ a ∈ A, (∃ n : ℕ, a ^ 2 ^ n = 1) → a ∈ P := by
  classical
  haveI := Fintype.ofFinite E
  let θ : Matrix.SpecialLinearGroup (Fin m) E →* G :=
    A.subtype.comp (φ.symm.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL)
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) E) := by
    rcases Nat.lt_or_ge m 2 with hm | hm
    · haveI := subsingleton_specialLinearGroup_of_le_one (by omega : m ≤ 1) E
      infer_instance
    · exact ⟨(slFactorFacts_holds E m hm (fun _ => by rw [← Nat.card_eq_fintype_card]; exact h4)).perfect⟩
  refine ⟨θ.range, ?_, Subgroup.isPerfect_iff.1 (Group.IsPerfect.range θ), ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact (φ.symm (Matrix.SpecialLinearGroup.toGL g)).2
  · rintro a ha ⟨n, hn⟩
    set g : GL (Fin m) E := φ ⟨a, ha⟩ with hg
    have hgn : g ^ 2 ^ n = 1 := by
      have h1 : (⟨a, ha⟩ : A) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
      rw [hg, ← map_pow, h1, map_one]
    have hdet : Matrix.GeneralLinearGroup.det g = 1 := by
      refine Inputs256e.eq_one_of_coprime_card (Inputs256e.coprime_card_units Nat.prime_two hE) (n := n) ?_
      rw [← map_pow, hgn, map_one]
    have hdet' : (g : Matrix (Fin m) (Fin m) E).det = 1 := by
      have := congrArg Units.val hdet
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    refine ⟨⟨g, hdet'⟩, ?_⟩
    have hgl : Matrix.SpecialLinearGroup.toGL ⟨(g : Matrix (Fin m) (Fin m) E), hdet'⟩ = g := Units.ext rfl
    show A.subtype (φ.symm (Matrix.SpecialLinearGroup.toGL ⟨(g : Matrix (Fin m) (Fin m) E), hdet'⟩)) = a
    rw [hgl, hg, MulEquiv.symm_apply_apply]
    rfl

theorem exists_perfect_twoElement_spSupported {r : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks 2 2 3 x a)
    (O : reciprocalOrbits (spEnd x)) :
    ∃ P : Subgroup (StatedSp r K), P ≤ spSupported x (O : Set K[X]) ∧ ⁅P, P⁆ = P ∧
      ∀ g ∈ spSupported x (O : Set K[X]), (∃ n : ℕ, g ^ 2 ^ n = 1) → g ∈ P := by
  classical
  have hKchar : ringChar K = 2 := by
    haveI := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
    exact ringChar.eq K 2
  obtain ⟨O, h, hh, rfl⟩ := O
  by_cases hself : reciprocalPolynomial h = h
  · have hO : ({h, reciprocalPolynomial h} : Set K[X]) = {h} := by rw [hself, Set.pair_eq_singleton]
    show ∃ P : Subgroup (StatedSp r K), P ≤ spSupported x {h, reciprocalPolynomial h} ∧ ⁅P, P⁆ = P ∧
      ∀ g ∈ spSupported x {h, reciprocalPolynomial h}, (∃ n : ℕ, g ^ 2 ^ n = 1) → g ∈ P
    rw [hO]
    by_cases h1 : h = X - 1
    · subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hh
      haveI : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hh)
      obtain ⟨s, hs, ⟨e⟩⟩ := CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      have hs1 : 1 ≤ s := by
        have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
        omega
      haveI : Group.IsPerfect ↥(StatedSp s K) :=
        (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs1 (Or.inl (Or.inr (by rw [hK]; norm_num)))).1
      have hperf : Group.IsPerfect ↥(spSupported x {X - 1}) :=
        Group.IsPerfect.ofSurjective (f := (φ.trans e).symm.toMonoidHom) (φ.trans e).symm.surjective
      exact ⟨_, le_rfl, Subgroup.isPerfect_iff.1 hperf, fun g hg _ => hg⟩
    · exfalso
      obtain ⟨d, -, hpd, -⟩ := (blocks.selfDual ⟨h, hh⟩ h1 hself).exists_half
      refine not_three_dvd_two_pow_add_one_of_even (f := 2 * d) ⟨d, by ring⟩ ?_
      rwa [← pow_mul] at hpd
  · have hP := blocks.paired ⟨h, hh⟩ (fun e => hself e.symm)
    obtain ⟨φ⟩ := hP.matrixFactor
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
    have hEchar : ringChar (AdjoinRoot h) = 2 := (Algebra.ringChar_eq K (AdjoinRoot h)).symm.trans hKchar
    have hdeg : 1 ≤ h.natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors hh)
    have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
      have hc := hP.card_field
      simp only at hc
      rw [hc]
      calc 4 = (2 ^ 2) ^ 1 := by norm_num
        _ ≤ (2 ^ 2) ^ h.natDegree := Nat.pow_le_pow_right (by norm_num) hdeg
    exact exists_perfect_twoElement_of_gl hEchar h4 φ

theorem twoElement_mem_glaLayer_conj_sp {r : ℕ} (hr : 1 ≤ r) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (x : StatedSp r K) (hx : x ^ 3 = 1)
    (ha1 : SymplecticFlag.proj r K x ≠ 1) {s : StatedProj (StatedSp r K)}
    (hs : s ∈ fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))) (hs2 : ∃ n : ℕ, s ^ 2 ^ n = 1) :
    s ∈ GLALayer (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))) := by
  classical
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hker : (SymplecticFlag.proj r K).ker = ⊥ := by
    rw [SymplecticHigher.ker_proj, ← Subgroup.card_eq_one, card_spScalars_eq_gcd K hr, hK]
    norm_num
  have hx1 : x ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have ha : orderOf (SymplecticFlag.proj r K x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have hxp : orderOf x = 3 := orderOf_eq_prime hx hx1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two (by norm_num) hK'
    Nat.prime_three (by norm_num) (by norm_num) hr _ ha).2 x rfl hxp
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    haveI := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK'])
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    norm_num at h
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  choose P hPA hPperf hP2 using exists_perfect_twoElement_spSupported hK' hsq blocks
  have hs' : s ∈ (Subgroup.centralizer {x}).map (SymplecticFlag.proj r K) := by
    rw [← blocks.centralizer_eq, ← fixSubgroup_conj_eq_centralizer_gf4]
    exact hs
  obtain ⟨y, hy, rfl⟩ := hs'
  have hy2 : ∃ n : ℕ, y ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hs2
    refine ⟨n, ?_⟩
    have h1 : y ^ 2 ^ n ∈ (SymplecticFlag.proj r K).ker := by rw [MonoidHom.mem_ker, map_pow, hn]
    rwa [hker, Subgroup.mem_bot] at h1
  have hyD : y ∈ ⨆ O, P O := by
    refine mem_iSup_of_twoElement_of_commute
      (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X])) P
      (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hP2 ?_ hy2
    rw [hjoin]
    exact hy
  have hDperf : ⁅(⨆ O, P O).map (SymplecticFlag.proj r K), (⨆ O, P O).map (SymplecticFlag.proj r K)⁆ =
      (⨆ O, P O).map (SymplecticFlag.proj r K) := by
    rw [← Subgroup.map_commutator, commutator_iSup_eq_self_of_perfect P hPperf]
  have hDle : (⨆ O, P O).map (SymplecticFlag.proj r K) ≤
      fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x)) := by
    rw [fixSubgroup_conj_eq_centralizer_gf4, blocks.centralizer_eq, ← hjoin]
    exact Subgroup.map_mono (iSup_mono hPA)
  have hlayer := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_sp Nat.prime_two (by norm_num) hK' hr Nat.prime_three
    (by norm_num) (by norm_num) x hx _ hDle hDperf
  exact hlayer (Subgroup.mem_map_of_mem _ hyD)

end Symplectic

section SymplecticMain

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)


theorem isGF4Comp_of_isComponentOf_conj_sp {r : ℕ} (hr : 1 ≤ r) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (x : StatedSp r K) (hx : x ^ 3 = 1) {J : Subgroup (StatedProj (StatedSp r K))}
    (hJ : IsComponentOf J (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x)))) :
    IsGF4Comp (MulAut.conj (SymplecticFlag.proj r K x)) J := by
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  obtain ⟨X, inst, hfin, ⟨hX, -⟩, hfac, g, hg, hk⟩ :=
    (lieCompsCore_conj_sp_card (a6 := False) slFactorFacts_holds suFactorFacts_holds
      spFactorFacts_holds spFourTwoFacts_holds False.elim False.elim False.elim
      Nat.prime_three (by norm_num) Nat.prime_two (by norm_num) hK' hr (by norm_num) False.elim x hx).2 J hJ
  obtain ⟨j, hj, hcat⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.catalogueOver_of_spFactorOver (q := Nat.card K) hfac
  have hcatJ := hcat.of_surjective hX.perfect g hg hk
  rw [hK] at hcatJ
  exact isGF4Comp_of_catalogueOver hJ hj hcatJ

theorem gf4Gen_statedSp {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (β : MulAut (StatedProj (StatedSp r K))) (hβ : orderOf β = 3) :
    ∀ s : StatedProj (StatedSp r K), β s = s → (∃ n : ℕ, s ^ 2 ^ n = 1) →
      s ∈ ⨆ (J : Subgroup (StatedProj (StatedSp r K))) (_ : IsGF4Comp β J), J := by
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hβ3 : β ^ 3 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) Nat.prime_two (by norm_num : 1 ≤ 2) hr hK'
  have hodd : Odd (orderOf β) := by rw [hβ]; decide
  have hE : β ∈ SymplecticHigher.spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  have hD : β ∈ SymplecticHigher.spLinearAutGroup r K := by
    by_contra hD
    obtain ⟨h3, -⟩ := hO.descent 3 Nat.prime_three β hE hD hβ
    norm_num at h3
  haveI : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
  have hrel : (inner (StatedProj (StatedSp r K))).relIndex (SymplecticHigher.spLinearAutGroup r K) ∣ 2 :=
    hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
  obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
    Nat.prime_three (by norm_num) hD hβ3
  obtain ⟨hsimple, hperf⟩ :=
    CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr (by rw [hK]; omega)
  haveI := hsimple
  have hnc : ∃ u v : StatedProj (StatedSp r K), u * v ≠ v * u := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun u v => h u v⟩⟩
  have ht3 : t ^ 3 = 1 :=
    CFSG.mulAutConj_injective_of_center_eq_bot
      (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc)
      (by rw [map_pow, ht, hβ3, map_one])
  obtain ⟨x, hx, hx3⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
    (by omega) Nat.prime_three (by norm_num) ht3
  have hβx : β = MulAut.conj (SymplecticFlag.proj r K x) := by rw [← ht, hx]
  have ha1 : SymplecticFlag.proj r K x ≠ 1 := by
    intro h1
    rw [h1, map_one] at hβx
    rw [hβx, orderOf_one] at hβ
    norm_num at hβ
  subst hβx
  intro s hs hs2
  exact glaLayer_le_iSup_isGF4Comp (fun J hJ => isGF4Comp_of_isComponentOf_conj_sp (by omega) hK x hx3 hJ)
    (twoElement_mem_glaLayer_conj_sp (by omega) hK x hx3 ha1 hs hs2)

theorem gf4CompsOn_symplectic :
    GF4CompsOn fun d => ∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = .B r q ∧ q.card = 4 := by
  rintro S _ _ ⟨d, hv⟩ ⟨r, q, hdq, hq4⟩ ⟨eS⟩ β hβ
  simp only at hdq
  subst hdq
  obtain ⟨hp2, -⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
    Nat.prime_two (by norm_num) (hq4.trans (by norm_num))
  have hr2 : 2 ≤ r :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hKq : Nat.card (GaloisField 2 2) = q.card := hK.trans hq4.symm
  obtain ⟨eB⟩ : Nonempty (StatedProj (StatedSp r (GaloisField 2 2)) ≃*
      (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) := by
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj hv hKq
    · exact CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj hv hp2 hr3 hKq
  let e : S ≃* StatedProj (StatedSp r (GaloisField 2 2)) := eS.trans eB.symm
  have hβ' : orderOf (MulAut.congr e β) = 3 := by rw [MulEquiv.orderOf_eq, hβ]
  exact Inputs256m.gf4Gen_of_congr e β (gf4Gen_statedSp hr2 hK _ hβ')

end SymplecticMain

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256p

end
