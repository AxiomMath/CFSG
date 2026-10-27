module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
import CFSG.Timmesfeld.Orders.ClassicalLinearThree
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Yardstones.Md0ec50421ce4 Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel CFSG.StandardType.TableBUE
  CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType CFSG.StandardType.Line63.H5

theorem SGU6.card_mul_three_of_tyF {X : Type} [Group X] (h : catalogIs X (tyF 3)) :
    ∃ m, 1 ≤ m ∧ ((3 ∣ 2 ^ m - 1 ∧
        Nat.card X * 3 = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1))) ∨
      (3 ∣ 2 ^ m + 1 ∧
        Nat.card X * 3 = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)))) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases i with _ | _ | ⟨⟨l, hv⟩⟩ | _ <;> try exact (hi : False).elim
  cases l
  case A r q =>
    obtain ⟨hr, hq2, h3⟩ := (hi : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card - 1)
    obtain rfl : r = 2 := by omega
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hX : Nat.card X = Nat.card (CFSG.Open.StatedProj
        (CFSG.Open.StatedSL 3 (GaloisField q.p q.exponent))) :=
      Nat.card_congr ((e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 _)).toEquiv
    have hc := CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd
      (K := GaloisField q.p q.exponent)
    rw [← hX, GaloisField.card q.p q.exponent q.exponent_pos.ne', hq2] at hc
    rw [TauCeti.PrimePower.card_def, hq2] at h3
    exact ⟨q.exponent, q.exponent_pos, Or.inl ⟨h3, by rw [← hc, Nat.gcd_eq_left h3]⟩⟩
  case twistedA r q =>
    obtain ⟨hr, hq2, h3⟩ := (hi : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card + 1)
    obtain rfl : r = 2 := by omega
    obtain ⟨⟨hp, hm, -⟩, F, _, _, hFc, ⟨eT⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    have hX : Nat.card X = Nat.card (CFSG.Open.StatedProj
        (CFSG.Open.StatedSU 3 (q.p ^ q.exponent) F)) := Nat.card_congr eT.toEquiv
    have hc := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd hp hm hFc
    rw [← hX, hq2] at hc
    rw [TauCeti.PrimePower.card_def, hq2] at h3
    exact ⟨q.exponent, q.exponent_pos, Or.inr ⟨h3, by rw [← hc, Nat.gcd_eq_left h3]⟩⟩
  all_goals exact (hi : False).elim

private theorem two_pow_mul_odd_inj {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  have hu' : ¬ 2 ∣ u := by have := Nat.odd_iff.mp hu; omega
  have hv' : ¬ 2 ∣ v := by have := Nat.odd_iff.mp hv; omega
  have hab : a = b := by
    have h1 := congrArg (padicValNat 2) h
    rwa [padicValNat.mul (by positivity) hu.pos.ne', padicValNat.mul (by positivity) hv.pos.ne',
      padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hu',
      padicValNat.eq_zero_of_not_dvd hv', add_zero, add_zero] at h1
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

private theorem two_pow_odd_mod {k : ℕ} (hk : 1 ≤ k) :
    Odd (2 ^ k - 1) ∧ Odd (2 ^ k + 1) ∧ (3 ≤ k → (2 ^ k - 1) % 8 = 7 ∧ (2 ^ k + 1) % 8 = 1) := by
  have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  refine ⟨Nat.odd_iff.mpr (by omega), Nat.odd_iff.mpr (by omega), fun h3 => ?_⟩
  have h8 : 8 ∣ 2 ^ k := pow_dvd_pow 2 h3
  omega

private theorem pm_one_mul {x y : ℕ} (hx : x % 8 = 1 ∨ x % 8 = 7) (hy : y % 8 = 1 ∨ y % 8 = 7) :
    x * y % 8 = 1 ∨ x * y % 8 = 7 := by
  rw [Nat.mul_mod]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> norm_num

private theorem two_pow_mod_fifteen (n : ℕ) :
    2 ^ n % 15 = 1 ∨ 2 ^ n % 15 = 2 ∨ 2 ^ n % 15 = 4 ∨ 2 ^ n % 15 = 8 := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

private theorem toNat_even {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    ((q : ℤ) ^ i - (-1) ^ i).toNat = q ^ i - 1 := by
  have h : (q : ℤ) ^ i - (-1) ^ i = ((q ^ i - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (Nat.one_le_pow i q hq), hi.neg_one_pow] <;> ring
  rw [h, Int.toNat_natCast]

private theorem toNat_odd {q i : ℕ} (hi : Odd i) :
    ((q : ℤ) ^ i - (-1) ^ i).toNat = q ^ i + 1 := by
  have h : (q : ℤ) ^ i - (-1) ^ i = ((q ^ i + 1 : ℕ) : ℤ) := by
    push_cast [hi.neg_one_pow] <;> ring
  rw [h, Int.toNat_natCast]

private theorem card_psu_four_five {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) :
    Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 4 (2 ^ n) K)) =
        (2 ^ n) ^ 6 * (((2 ^ n) ^ 2 - 1) * (((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1))) ∧
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 5 (2 ^ n) K)) =
        (2 ^ n) ^ 10 * (((2 ^ n) ^ 2 - 1) * (((2 ^ n) ^ 3 + 1) * (((2 ^ n) ^ 4 - 1) *
          ((2 ^ n) ^ 5 + 1)))) := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hg4 : Nat.gcd 4 (2 ^ n + 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (two_pow_odd_mod hn).2.1)
  have hg5 : Nat.gcd 5 (2 ^ n + 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr fun h5 => by
      have := two_pow_mod_fifteen n
      omega
  constructor
  · rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hn hK
      (by norm_num : 2 ≤ 4), hg4, Nat.div_one, show 4 * (4 - 1) / 2 = 6 from rfl,
      show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num), toNat_even (i := 2) hq ⟨1, rfl⟩,
      toNat_odd (i := 3) ⟨1, rfl⟩, toNat_even (i := 4) hq ⟨2, rfl⟩]
  · rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hn hK
      (by norm_num : 2 ≤ 5), hg5, Nat.div_one, show 5 * (5 - 1) / 2 = 10 from rfl,
      show Finset.Icc 2 5 = {2, 3, 4, 5} by decide, Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_pair (by norm_num),
      toNat_even (i := 2) hq ⟨1, rfl⟩, toNat_odd (i := 3) ⟨1, rfl⟩,
      toNat_even (i := 4) hq ⟨2, rfl⟩, toNat_odd (i := 5) ⟨2, rfl⟩]

private theorem false_of_card_psu {n m N : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hN : N = (2 ^ n) ^ 6 * (((2 ^ n) ^ 2 - 1) * (((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1))) ∨
      N = (2 ^ n) ^ 10 * (((2 ^ n) ^ 2 - 1) * (((2 ^ n) ^ 3 + 1) * (((2 ^ n) ^ 4 - 1) *
        ((2 ^ n) ^ 5 + 1)))))
    (hQ : N * 3 = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ∨
      N * 3 = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1))) : False := by
  simp only [← pow_mul] at hN hQ
  have m2 := two_pow_odd_mod (k := m * 2) (by omega)
  have m3 := two_pow_odd_mod (k := m * 3) (by omega)
  obtain ⟨w, hwd, hwo, hw8, hQ⟩ : ∃ w, (w = (2 ^ (m * 2) - 1) * (2 ^ (m * 3) - 1) ∨
      w = (2 ^ (m * 2) - 1) * (2 ^ (m * 3) + 1)) ∧ Odd w ∧
      (2 ≤ m → w % 8 = 1 ∨ w % 8 = 7) ∧ N * 3 = 2 ^ (m * 3) * w := by
    rcases hQ with hQ | hQ
    · exact ⟨_, Or.inl rfl, m2.1.mul m3.1, fun _ => pm_one_mul
        (Or.inr (m2.2.2 (by omega)).1) (Or.inr (m3.2.2 (by omega)).1), hQ⟩
    · exact ⟨_, Or.inr rfl, m2.1.mul m3.2.1, fun _ => pm_one_mul
        (Or.inr (m2.2.2 (by omega)).1) (Or.inl (m3.2.2 (by omega)).2), hQ⟩
  have n2 := two_pow_odd_mod (k := n * 2) (by omega)
  have n3 := two_pow_odd_mod (k := n * 3) (by omega)
  have n4 := two_pow_odd_mod (k := n * 4) (by omega)
  have n5 := two_pow_odd_mod (k := n * 5) (by omega)
  rcases hN with rfl | rfl
  · obtain ⟨he, hu⟩ := two_pow_mul_odd_inj ((n2.1.mul (n3.2.1.mul n4.1)).mul (by decide))
      hwo ((mul_assoc _ _ _).symm.trans hQ)
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      obtain rfl : m = 2 := by omega
      norm_num at hu hwd
      omega
    · have hA := pm_one_mul (Or.inr (n2.2.2 (by omega)).1)
        (pm_one_mul (Or.inl (n3.2.2 (by omega)).2) (Or.inr (n4.2.2 (by omega)).1))
      have := hw8 (by omega)
      generalize (2 ^ (n * 2) - 1) * ((2 ^ (n * 3) + 1) * (2 ^ (n * 4) - 1)) = A at hu hA
      omega
  · obtain ⟨he, hu⟩ := two_pow_mul_odd_inj
      ((n2.1.mul (n3.2.1.mul (n4.1.mul n5.2.1))).mul (by decide)) hwo
      ((mul_assoc _ _ _).symm.trans hQ)
    have hA := pm_one_mul (Or.inr (n2.2.2 (by omega)).1) (pm_one_mul
      (Or.inl (n3.2.2 (by omega)).2) (pm_one_mul (Or.inr (n4.2.2 (by omega)).1)
        (Or.inl (n5.2.2 (by omega)).2)))
    have := hw8 (by omega)
    generalize (2 ^ (n * 2) - 1) * ((2 ^ (n * 3) + 1) * ((2 ^ (n * 4) - 1) *
      (2 ^ (n * 5) + 1))) = A at hu hA
    omega

variable {K : Type} [Field K] {n : ℕ}

private theorem level_cases [DecidableEq Kˣ] {τ : Fin 6 → Kˣ} (hτ : ∀ j, τ j ^ 3 = 1) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3) :
    (∃ (v : Kˣ) (S : Finset (Fin 6)), (∀ i, i ∈ S ↔ τ i = v) ∧ 4 ≤ S.card) ∨
      ((∀ (i : Fin 6) (S : Finset (Fin 6)), (∀ j, j ∈ S ↔ τ j = τ i) → S.card ≤ 3) ∧
        ∃ (v₁ v₂ : Kˣ) (S₁ S₂ : Finset (Fin 6)), v₁ ≠ v₂ ∧ (∀ i, i ∈ S₁ ↔ τ i = v₁) ∧
          (∀ i, i ∈ S₂ ↔ τ i = v₂) ∧ 2 ≤ S₁.card ∧ 2 ≤ S₂.card) := by
  have hval : ∀ j, τ j = 1 ∨ τ j = ζ ∨ τ j = ζ ^ 2 := by
    intro j
    obtain ⟨i, hi, hij⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity _ _).mpr (hτ j))
    interval_cases i
    · exact Or.inl (by rw [← hij, pow_zero])
    · exact Or.inr (Or.inl (by rw [← hij, pow_one]))
    · exact Or.inr (Or.inr hij.symm)
  have hne1 : (1 : Kˣ) ≠ ζ := fun h => by
    have := hζ.pow_inj (i := 0) (j := 1) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hne2 : (1 : Kˣ) ≠ ζ ^ 2 := fun h => by
    have := hζ.pow_inj (i := 0) (j := 2) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hne3 : ζ ≠ ζ ^ 2 := fun h => by
    have := hζ.pow_inj (i := 1) (j := 2) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hmem : ∀ u (i : Fin 6), i ∈ Finset.univ.filter (fun j => τ j = u) ↔ τ i = u :=
    fun u i => by simp
  obtain ⟨c, hc⟩ : ∃ c : Kˣ → ℕ, ∀ u, (Finset.univ.filter fun j => τ j = u).card = c u :=
    ⟨_, fun _ => rfl⟩
  have h6 := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := {1, ζ, ζ ^ 2})
    (f := τ) fun j _ => by rcases hval j with h | h | h <;> simp [h]
  rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_insert (by simp [hne3]),
    Finset.sum_singleton, Finset.card_univ, Fintype.card_fin] at h6
  simp only [hc] at h6
  by_cases hbig : 4 ≤ c 1 ∨ 4 ≤ c ζ ∨ 4 ≤ c (ζ ^ 2)
  · left
    rcases hbig with h | h | h
    · exact ⟨1, _, hmem 1, by rw [hc]; exact h⟩
    · exact ⟨ζ, _, hmem ζ, by rw [hc]; exact h⟩
    · exact ⟨ζ ^ 2, _, hmem (ζ ^ 2), by rw [hc]; exact h⟩
  simp only [not_or, not_le] at hbig
  obtain ⟨b1, b2, b3⟩ := hbig
  refine Or.inr ⟨fun i S hS => ?_, ?_⟩
  · have hSeq : S = Finset.univ.filter fun j => τ j = τ i := Finset.ext fun j => by simp [hS j]
    rw [hSeq, hc]
    rcases hval i with h | h | h <;> rw [h] <;> omega
  rcases (by omega : (2 ≤ c 1 ∧ 2 ≤ c ζ) ∨ (2 ≤ c 1 ∧ 2 ≤ c (ζ ^ 2)) ∨
      (2 ≤ c ζ ∧ 2 ≤ c (ζ ^ 2))) with h | h | h
  · exact ⟨1, ζ, _, _, hne1, hmem 1, hmem ζ, by rw [hc]; exact h.1, by rw [hc]; exact h.2⟩
  · exact ⟨1, ζ ^ 2, _, _, hne2, hmem 1, hmem (ζ ^ 2), by rw [hc]; exact h.1,
      by rw [hc]; exact h.2⟩
  · exact ⟨ζ, ζ ^ 2, _, _, hne3, hmem ζ, hmem (ζ ^ 2), by rw [hc]; exact h.1,
      by rw [hc]; exact h.2⟩

private theorem exists_diag_of_cube (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {U : GL (Fin 6) K} (hU : U ∈ primeFormUnitary hKd (idGram K 6)) (hU3 : U ^ 3 = 1) :
    ∃ P ∈ primeFormUnitary hKd (idGram K 6), ∃ τ : Fin 6 → Kˣ,
      P⁻¹ * U * P = diagHom 6 τ ∧ ∀ j, τ j ^ 3 = 1 := by
  let u : ↥(primeFormUnitary hKd (idGram K 6)) := ⟨U, hU⟩
  have hu3 : u ^ 3 = 1 := Subtype.ext hU3
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag hKd Nat.prime_three hpq
    (Subgroup.zpowers u) (fun a ha b hb => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self u i j).eq) (fun a ha => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
        _root_.zpow_natCast, hu3, _root_.one_zpow])
  obtain ⟨τ, hτ⟩ := exists_diagHom_of_isDiag (hP u (Subgroup.mem_zpowers u))
  have hτ' : (P : GL (Fin 6) K)⁻¹ * U * P = diagHom 6 τ := hτ
  exact ⟨P, P.2, τ, hτ', pow_eq_one_of_conj_diag hτ' hU3⟩

private theorem isComponentOf_map_blockSU_three (hKd : UnitaryFieldData 2 n K) {d : ℕ}
    {D : GL (Fin d) K} (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {τ : Fin d → Kˣ} (hDτ : D = diagHom d τ) {v : Kˣ} {S : Finset (Fin d)}
    (hS : ∀ i, i ∈ S ↔ τ i = v) (hS3 : 3 ≤ S.card) (hSq : (S.card, 2 ^ n) ≠ (3, 2)) :
    CFSG.Assembly.IsComponentOf ((blockSU (n := n) S).map (LargeEvenProjMk (unitarySU 2 n K d)))
      (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩)) := by
  classical
  subst hDτ
  set π := LargeEvenProjMk (unitarySU 2 n K d)
  set C := ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩)
  have hτS : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j := fun i hi j hj => by
    rw [(hS i).mp hi, (hS j).mp hj]
  have hNC : (blockSU (n := n) S).map π ≤ (cenSU (n := n) (diagHom d τ)).map π :=
    Subgroup.map_mono (blockSU_le_cenSU hτS)
  have hCC : (cenSU (n := n) (diagHom d τ)).map π ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    exact mk_mem_ggFix_of_mem_cenSU hD hs
  have hN : (((blockSU (n := n) S).map π).subgroupOf
      ((cenSU (n := n) (diagHom d τ)).map π)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨s, hs, hsg⟩ := g.2
    refine ⟨s * t * s⁻¹, conj_mem_blockSU_of_commute hS (mem_cenSU.mp hs) ht, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hsg, htx]
  have hC' : ((cenSU (n := n) (diagHom d τ)).map π).subgroupOf C |>.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨s, hsg⟩ := QuotientGroup.mk_surjective (g : LargeEvenProj (unitarySU 2 n K d))
    have hgC : (g : LargeEvenProj (unitarySU 2 n K d)) ∈ C := g.2
    rw [← hsg] at hgC
    obtain ⟨c, hs⟩ := exists_conj_eq_scalar_mul hD hgC
    have hπs : π s = (g : LargeEvenProj (unitarySU 2 n K d)) := hsg
    refine ⟨s * t * s⁻¹, conj_mem_cenSU hs ht, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hπs, htx]
  refine ⟨hNC.trans hCC, ?_, SUTorus.isQuasisimple_map_blockSU hKd ker_projMk_le_center hS3 hSq⟩
  exact CFSG.Assembly.IsSubnormal.step hNC hN
    (CFSG.Assembly.IsSubnormal.step hCC hC' (CFSG.Assembly.IsSubnormal.refl C))

private theorem card_layer_of_level (hKd : UnitaryFieldData 2 n K) {D : GL (Fin 6) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    {τ : Fin 6 → Kˣ} (hDτ : D = diagHom 6 τ) {v : Kˣ} {S : Finset (Fin 6)}
    (hS : ∀ i, i ∈ S ↔ τ i = v) (hS3 : 3 ≤ S.card) (hSq : (S.card, 2 ^ n) ≠ (3, 2))
    (hL : CFSG.Assembly.IsComponentOf
      (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨D, hD⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨D, hD⟩))) :
    Nat.card (↥(LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨D, hD⟩))) ⧸
        Subgroup.center ↥(LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨D, hD⟩)))) =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU S.card (2 ^ n) K)) := by
  have hN := isComponentOf_map_blockSU_three hKd hD hDτ hS hS3 hSq
  have hle : (blockSU (n := n) S).map (LargeEvenProjMk (unitarySU 2 n K 6)) ≤
      LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨D, hD⟩)) := le_sSup hN
  have hE := eq_of_isComponentOf_of_isQuasisimple (hN.of_le_of_le hle hL.1) hL.2.2
  obtain ⟨θ⟩ := SUTorus.nonempty_mulEquiv_quotient_center_blockSU hKd ker_projMk_le_center hS3 hSq
  rw [← hE]
  exact Nat.card_congr θ.toEquiv

private theorem layer_conj {R : Type*} [Group R] (σ a : MulAut R)
    (h : CFSG.Assembly.IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a)) :
    CFSG.Assembly.IsComponentOf (LargeEvenLayer (ggFix (σ⁻¹ * a * σ))) (ggFix (σ⁻¹ * a * σ)) ∧
      Nat.card (↥(LargeEvenLayer (ggFix (σ⁻¹ * a * σ))) ⧸
          Subgroup.center ↥(LargeEvenLayer (ggFix (σ⁻¹ * a * σ)))) =
        Nat.card (↥(LargeEvenLayer (ggFix a)) ⧸ Subgroup.center ↥(LargeEvenLayer (ggFix a))) := by
  have hf : Function.Injective (σ⁻¹ : MulAut R).toMonoidHom := (σ⁻¹ : MulAut R).injective
  rw [← map_ggFix_conj σ a, CFSG.StandardType.largeEvenLayer_map_of_injective _ hf]
  refine ⟨CFSG.StandardType.isComponentOf_map_of_injective _ hf h, Nat.card_congr ?_⟩
  let ε := ((LargeEvenLayer (ggFix a)).equivMapOfInjective _ hf).symm
  exact (QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)).toEquiv

theorem SGU6.false_of_cube_tyF (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {U : GL (Fin 6) K} (hU : U ∈ primeFormUnitary hKd (idGram K 6)) (hU3 : U ^ 3 = 1)
    (hUs : U ∉ LargeEvenScalars (Fin 6) K)
    (hUN : U ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hL : CFSG.Assembly.IsComponentOf
      (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨U, hUN⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨U, hUN⟩)))
    (hty : catalogIs (↥(LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨U, hUN⟩))) ⧸
      Subgroup.center ↥(LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨U, hUN⟩))))
      (tyF 3)) : False := by
  classical
  obtain ⟨P, hP, τ, hUP, hτ3⟩ := exists_diag_of_cube hKd hpq hU hU3
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 3 := by
    obtain ⟨ζ₀, hζ₀⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hKd Nat.prime_three hpq
    exact ⟨(hζ₀.isUnit (by norm_num)).unit,
      IsPrimitiveRoot.coe_units_iff.mp (by rwa [IsUnit.unit_spec])⟩
  rcases level_cases hτ3 hζ with ⟨v, S, hS, hS4⟩ | ⟨hb, htb⟩
  swap
  · exact not_isComponentOf_layer_ggFix_of_twoBlocks_all hKd hUN ⟨P, hP, τ, hUP, hb, htb⟩ hL
  have hS6 : S.card ≠ 6 := fun h6 => hUs <| by
    have hall : ∀ i, τ i = v := fun i =>
      (hS i).mp (by rw [Finset.eq_univ_of_card S (by simpa using h6)]; exact Finset.mem_univ i)
    have h2 : U = P * (P⁻¹ * U * P) * P⁻¹ := by group
    rw [hUP, diagHom_eq_scalar_iff.mpr hall] at h2
    refine ⟨v, ?_⟩
    rw [h2, (commute_scalar v P).eq]
    group
  have hSle : S.card ≤ 6 := by simpa using Finset.card_le_univ S
  have hSq : (S.card, 2 ^ n) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hPN : P ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    gu_subset_normalizer hKd (mem_guSet_of_mem_primeFormUnitary hKd hP)
  have hD : P⁻¹ * U * P ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    mul_mem (mul_mem (inv_mem hPN) hUN) hPN
  have e : TableB.projConj (unitarySU 2 n K 6) ⟨P⁻¹ * U * P, hD⟩ =
      (TableB.projConj (unitarySU 2 n K 6) ⟨P, hPN⟩)⁻¹ *
        TableB.projConj (unitarySU 2 n K 6) ⟨U, hUN⟩ *
          TableB.projConj (unitarySU 2 n K 6) ⟨P, hPN⟩ := by
    rw [show (⟨P⁻¹ * U * P, hD⟩ : Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) =
      ⟨P, hPN⟩⁻¹ * ⟨U, hUN⟩ * ⟨P, hPN⟩ from rfl, map_mul, map_mul, map_inv]
  obtain ⟨hLD, hcD⟩ := layer_conj (TableB.projConj (unitarySU 2 n K 6) ⟨P, hPN⟩) _ hL
  rw [← e] at hLD hcD
  have hc := card_layer_of_level hKd hD hUP hS (by omega) hSq hLD
  rw [hcD] at hc
  obtain ⟨m, hm, hQ⟩ := SGU6.card_mul_three_of_tyF hty
  rw [hc] at hQ
  have hK : Nat.card K = (2 ^ n) ^ 2 := by rw [hKd.card, ← pow_mul, mul_comm]
  obtain ⟨h4, h5⟩ := card_psu_four_five hKd.one_le hK hpq
  refine false_of_card_psu hKd.one_le hm ?_ (hQ.imp And.right And.right)
  rcases (by omega : S.card = 4 ∨ S.card = 5) with hs | hs <;> rw [hs]
  · exact Or.inl h4
  · exact Or.inr h5

end CFSG.LocalAnalysis.GLTheoremA.S265

end
