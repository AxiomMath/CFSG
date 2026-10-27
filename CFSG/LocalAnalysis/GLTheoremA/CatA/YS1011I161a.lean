module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreSix
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreExc
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCore
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSmall
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.LargeExtraspecial.DW2AOut
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Coker
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Torus
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I161a2
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LargeExtraspecial.DW2AOutInput
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement


namespace I161a

open CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Multiplier CFSG.Open

def tabOrd (lab : LargeEvenLabel) : ℕ :=
  (genericOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).1 *
    (genericOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).2 *
    ((exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).1 *
      (exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)).2)

theorem exc_dvd_sixteen (t : StatedLieTag) (n f : ℕ) :
    (exceptionalOrders t n 2 f).1 * (exceptionalOrders t n 2 f).2 ∣ 16 := by
  unfold exceptionalOrders
  split <;> first | omega | norm_num

theorem not_dvd_sixteen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 16 := by
  intro h
  have h2 : p ∣ 2 ^ 4 := by norm_num; exact h
  have := (Nat.Prime.dvd_of_dvd_pow hp h2)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

theorem tab_dvd_of_char2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (t : StatedLieTag) (n f : ℕ)
    (h : p ∣ (genericOrders t n 2 f).1 * (genericOrders t n 2 f).2 *
      ((exceptionalOrders t n 2 f).1 * (exceptionalOrders t n 2 f).2)) :
    p ∣ (genericOrders t n 2 f).1 * (genericOrders t n 2 f).2 := by
  have hcop : Nat.Coprime p ((exceptionalOrders t n 2 f).1 * (exceptionalOrders t n 2 f).2) :=
    Nat.Coprime.coprime_dvd_right (exc_dvd_sixteen t n f)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_sixteen hp hp2))
  exact hcop.dvd_of_dvd_mul_right h

theorem false_of_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : ℕ} (hX : X ∣ 4)
    (h : p ∣ X) : False :=
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow (n := 2)
    (by norm_num; exact h.trans hX)))

theorem gen_PSL (n f : ℕ) : (genericOrders .PSL n 2 f).1 * (genericOrders .PSL n 2 f).2 =
    Nat.gcd n (2 ^ f - 1) := by simp [genericOrders]

theorem gen_PSU (n f : ℕ) : (genericOrders .PSU n 2 f).1 * (genericOrders .PSU n 2 f).2 =
    Nat.gcd n (2 ^ f + 1) := by simp [genericOrders]

theorem gen_E6 (f : ℕ) : (genericOrders .E6 0 2 f).1 * (genericOrders .E6 0 2 f).2 =
    Nat.gcd 3 (2 ^ f - 1) := by simp [genericOrders]

theorem gen_twE6 (f : ℕ) : (genericOrders .twistedE6 0 2 f).1 * (genericOrders .twistedE6 0 2 f).2 =
    Nat.gcd 3 (2 ^ f + 1) := by simp [genericOrders]

theorem gen_PSp (n f : ℕ) : (genericOrders .PSp n 2 f).1 * (genericOrders .PSp n 2 f).2 ∣ 2 := by
  simp [genericOrders]; exact Nat.gcd_dvd_left _ _

theorem gen_E7 (n f : ℕ) : (genericOrders .E7 n 2 f).1 * (genericOrders .E7 n 2 f).2 ∣ 2 := by
  simp [genericOrders]; exact Nat.gcd_dvd_left _ _

theorem gen_POmegaMinus (n f : ℕ) :
    (genericOrders .POmegaMinus n 2 f).1 * (genericOrders .POmegaMinus n 2 f).2 ∣ 4 := by
  simp [genericOrders]; exact Nat.gcd_dvd_left _ _

theorem gen_PSL_four (f : ℕ) : (genericOrders .PSL 4 2 f).1 * (genericOrders .PSL 4 2 f).2 ∣ 4 := by
  rw [gen_PSL]; exact (Nat.gcd_dvd_left _ _)

theorem gen_PSL_two (f : ℕ) : (genericOrders .PSL 2 2 f).1 * (genericOrders .PSL 2 2 f).2 ∣ 2 := by
  rw [gen_PSL]; exact (Nat.gcd_dvd_left _ _)

theorem gen_PSU_four (f : ℕ) : (genericOrders .PSU 4 2 f).1 * (genericOrders .PSU 4 2 f).2 ∣ 4 := by
  rw [gen_PSU]; exact (Nat.gcd_dvd_left _ _)

theorem gen_default (t : StatedLieTag) (n f : ℕ) (ht : t = .E8 ∨ t = .F4 ∨ t = .G2 ∨
    t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedF4 ∨ t = .Tits) :
    (genericOrders t n 2 f).1 * (genericOrders t n 2 f).2 = 1 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [genericOrders]

theorem gen_POmegaPlus (n f : ℕ) (hf : 1 ≤ f) :
    (genericOrders .POmegaPlus n 2 f).1 * (genericOrders .POmegaPlus n 2 f).2 = 1 := by
  have : Even (2 ^ f) := (Nat.even_pow).2 ⟨even_two, by omega⟩
  simp [genericOrders, this]

theorem contra_of_dvd {p X : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hX : X ∣ 16) (h : p ∣ X) :
    False :=
  not_dvd_sixteen hp hp2 (h.trans hX)

theorem tabOrd_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hd : p ∣ tabOrd lab) : LargeEvenSplit16 p lab := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_PSL] at h1
    exact Or.inl ⟨show LargeEvenUntwisted .A from trivial, (Nat.dvd_gcd_iff.1 h1).2⟩
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_PSU] at h1
    exact Or.inr (Or.inl ⟨fun h => h, by simp, by simp, (Nat.dvd_gcd_iff.1 h1).2⟩)
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    exact (contra_of_dvd hp hp2 ((gen_PSp _ _).trans (by norm_num)) h1).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    exact (contra_of_dvd hp hp2 ((gen_PSp _ _).trans (by norm_num)) h1).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    split_ifs at hd with h3
    · have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
      rw [gen_PSL] at h1
      exact (contra_of_dvd hp hp2 ((Nat.gcd_dvd_left _ _).trans (by norm_num)) h1).elim
    · have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
      rw [gen_POmegaPlus _ _ hn] at h1
      exact (hp.one_lt.ne' (Nat.dvd_one.1 h1)).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    split_ifs at hd with h2 h3
    · have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
      rw [gen_PSL] at h1
      exact (contra_of_dvd hp hp2 ((Nat.gcd_dvd_left _ _).trans (by norm_num)) h1).elim
    · have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
      rw [gen_PSU] at h1
      exact (contra_of_dvd hp hp2 ((Nat.gcd_dvd_left _ _).trans (by norm_num)) h1).elim
    · have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
      exact (contra_of_dvd hp hp2 ((gen_POmegaMinus _ _).trans (by norm_num)) h1).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_E6] at h1
    exact Or.inl ⟨show LargeEvenUntwisted .E6 from trivial, (Nat.dvd_gcd_iff.1 h1).2⟩
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    exact (contra_of_dvd hp hp2 ((gen_E7 _ _).trans (by norm_num)) h1).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_default _ _ _ (by simp)] at h1
    exact (hp.one_lt.ne' (Nat.dvd_one.1 h1)).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_default _ _ _ (by simp)] at h1
    exact (hp.one_lt.ne' (Nat.dvd_one.1 h1)).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_twE6] at h1
    exact Or.inr (Or.inl ⟨fun h => h, by simp, by simp, (Nat.dvd_gcd_iff.1 h1).2⟩)
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_default _ _ _ (by simp)] at h1
    exact (hp.one_lt.ne' (Nat.dvd_one.1 h1)).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_default _ _ _ (by simp)] at h1
    exact (hp.one_lt.ne' (Nat.dvd_one.1 h1)).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_default _ _ _ (by simp)] at h1
    exact (hp.one_lt.ne' (Nat.dvd_one.1 h1)).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_default _ _ _ (by simp)] at h1
    exact (hp.one_lt.ne' (Nat.dvd_one.1 h1)).elim
  ·
    have h6 : tabOrd ⟨.B2der, l, n⟩ = 6 := by
      simp only [tabOrd, markTag, markRank, markChar, markDeg]; decide
    rw [h6] at hd
    have hl1 : n = 1 := hl.2
    have hp3 : p = 3 := by
      rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 from hd) with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
    exact Or.inr (Or.inr (Or.inr ⟨hl1, hp3⟩))
  ·
    have h1 : tabOrd ⟨.G2der, l, n⟩ = 1 := by
      simp only [tabOrd, markTag, markRank, markChar, markDeg]; decide
    rw [h1] at hd
    exact (hp.one_lt.ne' (Nat.dvd_one.1 hd)).elim
  ·
    unfold tabOrd at hd
    simp only [markTag, markRank, markChar, markDeg] at hd
    have h1 := tab_dvd_of_char2 hp hp2 _ _ _ hd
    rw [gen_default _ _ _ (by simp)] at h1
    exact (hp.one_lt.ne' (Nat.dvd_one.1 h1)).elim


theorem gen_PSp_eq (n f : ℕ) : (genericOrders .PSp n 2 f).1 * (genericOrders .PSp n 2 f).2 =
    Nat.gcd 2 (2 ^ f - 1) := by simp [genericOrders]

theorem gen_POmegaMinus_eq (n f : ℕ) :
    (genericOrders .POmegaMinus n 2 f).1 * (genericOrders .POmegaMinus n 2 f).2 =
      Nat.gcd 4 ((2 ^ f) ^ n + 1) := by simp [genericOrders]

theorem gen_E7_eq (n f : ℕ) : (genericOrders .E7 n 2 f).1 * (genericOrders .E7 n 2 f).2 =
    Nat.gcd 2 (2 ^ f - 1) := by simp [genericOrders]

theorem exc_pos (t : StatedLieTag) (n f : ℕ) :
    0 < (exceptionalOrders t n 2 f).1 * (exceptionalOrders t n 2 f).2 := by
  unfold exceptionalOrders
  split <;> first | omega | norm_num

theorem tabOrd_pos {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) : 0 < tabOrd lab := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t
  all_goals first
    | (unfold tabOrd; simp only [markTag, markRank, markChar, markDeg]
       (try split_ifs) <;> refine Nat.mul_pos ?_ (exc_pos _ _ _) <;>
         first
         | (rw [gen_PSL]; exact Nat.gcd_pos_of_pos_left _ (by omega))
         | (rw [gen_PSU]; exact Nat.gcd_pos_of_pos_left _ (by omega))
         | (rw [gen_PSp_eq]; exact Nat.gcd_pos_of_pos_left _ (by norm_num))
         | (rw [gen_E6]; exact Nat.gcd_pos_of_pos_left _ (by norm_num))
         | (rw [gen_twE6]; exact Nat.gcd_pos_of_pos_left _ (by norm_num))
         | (rw [gen_E7_eq]; exact Nat.gcd_pos_of_pos_left _ (by norm_num))
         | (rw [gen_POmegaMinus_eq]; exact Nat.gcd_pos_of_pos_left _ (by norm_num))
         | (rw [gen_POmegaPlus _ _ hn]; norm_num)
         | (rw [gen_default _ _ _ (by simp)]; norm_num)
         | (simp [genericOrders]))
    | (unfold tabOrd; simp only [markTag, markRank, markChar, markDeg]; decide)


section TwE6Even

open CFSG.StandardType.TableB.TwE6
open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem pow_sq_of_card [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (u : K) :
    u ^ (q ^ 2) = u := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [← hc]
  exact FiniteField.pow_card u

theorem edge_pow_five_mem [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ q) (g : Kˣ) :
    edge σ (g ^ ((5 : ℤ) - 4 * (q : ℤ))) ∈ torus₀ σ := by
  have hσσ := sigma_sigma hK hσ
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, c = g ^ 3 := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : Kˣ, α = g ^ (q + 1) := ⟨_, rfl⟩
  have hcK : ((c : K)) = (g : K) ^ 3 := by rw [hc, Units.val_pow_eq_pow_val]
  have hαK : ((α : K)) = (g : K) ^ (q + 1) := by rw [hα, Units.val_pow_eq_pow_val]
  have hσc : σ (c : K) = (c : K) ^ q := hσ _
  have hσα : σ (α : K) = (α : K) := by
    rw [hσ, hαK, ← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, pow_sq_of_card hK,
      ← pow_succ']
  have hrel : (c : K) ^ (q + 1) = (α : K) ^ 3 := by
    rw [hcK, hαK, ← pow_mul, ← pow_mul]; ring_nf
  have hx : c ^ 3 * (α ^ 4)⁻¹ = g ^ ((5 : ℤ) - 4 * (q : ℤ)) := by
    rw [hc, hα]
    group
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := rhoE6_values
  let s : Fin 6 → Kˣ := ![c ^ 2 * (α ^ 2)⁻¹, α, c, α ^ 2, Units.map σ.toMonoidHom c,
    Units.map σ.toMonoidHom (c ^ 2 * (α ^ 2)⁻¹)]
  have hσαu : Units.map σ.toMonoidHom α = α := Units.ext hσα
  have hσσu : ∀ u : Kˣ, Units.map σ.toMonoidHom (Units.map σ.toMonoidHom u) = u := by
    intro u; apply Units.ext; simp [hσσ]
  have hs : s ∈ compat σ := by
    rw [mem_compat]
    intro i
    fin_cases i
    · apply Units.ext; simp [s, r0]
    · apply Units.ext; simp [s, r1, hσα]
    · apply Units.ext; simp [s, r2]
    · apply Units.ext; simp [s, r3, hσα]
    · apply Units.ext; simp [s, r4, hσσ]
    · apply Units.ext; simp [s, r5, hσσ, hσα]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hα0 : (α : K) ≠ 0 := α.ne_zero
  have hcart : cartanHom s = edge σ (c ^ 3 * (α ^ 4)⁻¹) := by
    rw [cartanHom_eq, edge_apply]
    funext i
    fin_cases i
    · apply Units.ext
      simp [s, map_mul, map_pow, map_inv₀, hσc, hσα]
      field_simp
      try ring
    · apply Units.ext
      simp [s, hσα]
    · apply Units.ext
      simp [s, map_mul, map_pow, map_inv₀, hσc, hσα]
    · apply Units.ext
      simp [s, map_mul, map_pow, map_inv₀, hσc, hσα]
      field_simp
      linear_combination -hrel
    · apply Units.ext
      simp [s, map_mul, map_pow, map_inv₀, hσc, hσα]
      field_simp
      try ring
    · apply Units.ext
      simp [s, map_mul, map_pow, map_inv₀, hσc, hσα]
      field_simp
      try ring
  have hmem : cartanHom s ∈ torus₀ σ := Subgroup.mem_map.2 ⟨s, hs, rfl⟩
  rw [hcart, hx] at hmem
  exact hmem


theorem edge_mem_torus_even [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (hq3 : q % 3 = 1)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ q) (g : Kˣ) : edge σ g ∈ torus₀ σ := by
  obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
  have h5 := edge_pow_five_mem hK hσ g
  have h3 : edge σ (g ^ 3) ∈ torus₀ σ := edge_pow_three_mem (sigma_sigma hK hσ) g
  have key : g ^ ((5 : ℤ) - 4 * ((3 * t + 1 : ℕ) : ℤ)) * (g ^ 3) ^ (4 * t) = g := by
    rw [← pow_mul, ← zpow_natCast, ← zpow_add]
    have hexp : (5 : ℤ) - 4 * ((3 * t + 1 : ℕ) : ℤ) + ((3 * (4 * t) : ℕ) : ℤ) = 1 := by
      push_cast; ring
    rw [hexp, zpow_one]
  have e : edge σ g = edge σ (g ^ ((5 : ℤ) - 4 * ((3 * t + 1 : ℕ) : ℤ))) *
      (edge σ (g ^ 3)) ^ (4 * t) := by
    rw [← map_pow, ← map_mul, key]
  rw [e]
  exact (torus₀ σ).mul_mem h5 ((torus₀ σ).pow_mem h3 _)

theorem compat_subset_torus_even [Finite K] {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    (hq3 : q % 3 = 1) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ q) {b : Fin 6 → Kˣ}
    (hb : b ∈ compat σ) : b ∈ torus₀ σ := by
  obtain ⟨x, hx⟩ := exists_mul_edge_inv_mem hq hK hσ hb
  have hbe : b = (b * (edge σ x)⁻¹) * edge σ x := by group
  rw [hbe]
  exact (torus₀ σ).mul_mem hx (edge_mem_torus_even hK hq3 hσ x)



theorem two_pow_mod_three_of_even {n : ℕ} (hev : n % 2 = 0) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  rw [pow_mul]
  norm_num [Nat.pow_mod]


theorem diagRealizedOn_E6_even {n : ℕ} (hn : 1 ≤ n) (hev : n % 2 = 0) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    CFSG.StandardType.TableBExcSmallRest.DiagRealizedOn TwistTag.E6.tag.cartan TwistTag.E6.perm n
      K (IsRoot TwistTag.E6.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobenius K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := iterateFrobenius_def 2 n
  have hq : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq3 : 2 ^ n % 3 = 1 := two_pow_mod_three_of_even hev
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm
      n = graphFixedRootGroup TwistTag.E6 K σ := by
    rw [twistedH_eq_commutator K .E6 n σ hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ hσ).2.2.1
  intro a ha
  rw [hC] at ha ⊢
  have hconj : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      rootDiagUnit TwistTag.E6.tag a * g * (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈
        graphFixedRootGroup TwistTag.E6 K σ := by
    intro g hg
    obtain ⟨h', hh', e⟩ := ha g hg
    rw [markDiag_isRoot] at e
    rw [← eq_conj_of_mul_rootDiag e]
    exact hh'
  have hca : a ∈ compat σ := fun i => compat_of_forall_conj_mem hconj i
  obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.1 (compat_subset_torus_even hq hK hq3 hσ hca)
  refine ⟨rootDiagUnit TwistTag.E6.tag a, ?_, ?_⟩
  · rw [← hsa, cartanHom_apply]
    exact rootDiagUnit_cartanChar_mem ((mem_compat σ).1 hs)
  · rw [markDiag_isRoot]
    rfl


end TwE6Even


section TwE6Ids
open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType

theorem chevIDImage_twE6_even_subset {n : ℕ} (hn : 1 ≤ n) (hev : n % 2 = 0) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) ⊆
      (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K
        LargeEvenRhoE6 n) →* MulAut (LargeEvenCenterQuot
          (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))).range :=
  chevIDImage_subset_inn (TableBExcSmallRest.ggDiagRealizedInput_of_diagRealizedOn
    ((diagRealizedOn_E6_even hn hev hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm))

end TwE6Ids

section Labels

open CFSG.Assembly CFSG.StandardType

abbrev OutGuard (p : ℕ) : LargeEvenRawCont :=
  LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I

theorem canon_iff_legacy {lab : LargeEvenLabel}
    (hspec : lab.tag ≠ LargeEvenLieTag.G2der ∧ lab.tag ≠ LargeEvenLieTag.twF4der ∧
      lab.tag ≠ LargeEvenLieTag.twF4) (Q : LargeEvenRawCont) :
    CFSG.Assembly.LargeEvenRawDatum lab Q ↔ CFSG.StandardType.LargeEvenRawDatum lab Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals first
    | exact Iff.rfl
    | exact absurd rfl hspec.1
    | exact absurd rfl hspec.2.1
    | exact absurd rfl hspec.2.2

theorem canon_of_legacy {lab : LargeEvenLabel} {P : LargeEvenRawCont}
    (hiff : ∀ Q, CFSG.Assembly.LargeEvenRawDatum lab Q ↔ CFSG.StandardType.LargeEvenRawDatum lab Q)
    (h : CFSG.StandardType.LargeEvenLabelAll lab P) :
    CFSG.StandardType.Canonical.LargeEvenLabelAll lab P :=
  fun Q hQ => (hiff _).2 (h Q ((hiff Q).1 hQ))

theorem labelAll_of_iff {lab lab' : LargeEvenLabel} {P : LargeEvenRawCont}
    (e : ∀ Q, CFSG.Assembly.LargeEvenRawDatum lab Q ↔ CFSG.Assembly.LargeEvenRawDatum lab' Q)
    (h : CFSG.StandardType.Canonical.LargeEvenLabelAll lab' P) :
    CFSG.StandardType.Canonical.LargeEvenLabelAll lab P :=
  fun Q hQ => (e _).2 (h Q ((e Q).1 hQ))

theorem outGuard_of_subset_inn {p : ℕ} {lab : LargeEvenLabel}
    (h : CFSG.StandardType.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R)) :
    CFSG.StandardType.LargeEvenLabelAll lab (OutGuard p) :=
  CFSG.StandardType.LargeEvenLabelAll.mono
    (fun R _ I F hI hs hna φ hφ _ => hI hs hna hφ) h

theorem canon_twE6_three {n : ℕ} (hn : 1 ≤ n) (hev : n % 2 = 0) :
    CFSG.StandardType.Canonical.LargeEvenLabelAll ⟨LargeEvenLieTag.twE6, 0, n⟩ (OutGuard 3) := by
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, ⟨hQK, fun _ _ φ hφ _ => ?_⟩⟩
  exact chevIDImage_twE6_even_subset hn hev hK hφ

end Labels


section Canon

open CFSG.Assembly CFSG.StandardType

theorem three_dvd_two_pow_add_one_of_odd {n : ℕ} (hodd : n % 2 = 1) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  apply Nat.dvd_of_mod_eq_zero
  rw [pow_succ, pow_mul]
  norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

theorem canon_outdiag {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hns : ¬ LargeEvenSplit16 p lab) :
    CFSG.StandardType.Canonical.LargeEvenLabelAll lab (OutGuard p) := by
  have hp3 : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨t, l, n⟩ := lab
  cases t
  ·
    have hq : ¬ p ∣ 2 ^ n - 1 := fun h => hns (Or.inl ⟨trivial, h⟩)
    exact canon_of_legacy (fun Q => Iff.rfl)
      (CFSG.StandardType.LargeEvenLabelAll.mono (fun _ _ _ _ h _ _ => h)
        (NbrInnerMore.largeEvenLabelAll_outdiagPrime_linear hp hlab rfl hq))
  ·
    have hq : ¬ p ∣ 2 ^ n + 1 := fun h =>
      hns (Or.inr (Or.inl ⟨fun h' => h', by simp, by simp, h⟩))
    exact canon_of_legacy (fun Q => Iff.rfl)
      (CFSG.StandardType.LargeEvenLabelAll.mono (fun _ _ _ _ h _ _ => h)
        (NbrInnerMore.largeEvenLabelAll_outdiagPrime_unitary hp hlab rfl hq))
  ·
    exact canon_of_legacy (fun Q => Iff.rfl)
      (CFSG.StandardType.LargeEvenLabelAll.mono (fun _ _ _ _ h _ _ => h)
        (NbrInnerMore.largeEvenLabelAll_outdiagPrime_sp p hlab (Or.inl rfl)))
  ·
    exact canon_of_legacy (fun Q => Iff.rfl)
      (CFSG.StandardType.LargeEvenLabelAll.mono (fun _ _ _ _ h _ _ => h)
        (NbrInnerMore.largeEvenLabelAll_outdiagPrime_sp p hlab (Or.inr rfl)))
  ·
    by_cases h3 : l = 3
    · subst h3
      have hq : ¬ p ∣ 2 ^ n - 1 := fun h => hns (Or.inl ⟨trivial, h⟩)
      have hlA : LargeEvenInLambda2 ⟨LargeEvenLieTag.A, 3, n⟩ :=
        ⟨hlab.1, by norm_num, fun h => absurd h (by norm_num)⟩
      exact labelAll_of_iff (lab' := ⟨LargeEvenLieTag.A, 3, n⟩) (fun Q => Iff.rfl)
        (canon_of_legacy (fun Q => Iff.rfl)
          (CFSG.StandardType.LargeEvenLabelAll.mono (fun _ _ _ _ h _ _ => h)
            (NbrInnerMore.largeEvenLabelAll_outdiagPrime_linear hp hlA rfl hq)))
    · have hl3 : 3 ≤ l := hlab.2
      have hl4 : 4 ≤ l := by omega
      exact canon_of_legacy (fun Q => Iff.rfl)
        (CFSG.StandardType.LargeEvenLabelAll.mono (fun _ _ _ _ h _ _ => h)
          (NbrInnerMore.largeEvenLabelAll_outdiagPrime_orth p (Or.inl rfl) hl4))
  ·
    by_cases h2 : l = 2
    · subst h2
      have hq1 : ¬ p ∣ 2 ^ n - 1 := fun h => hns (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, h⟩)))
      have hq2 : ¬ p ∣ 2 ^ n + 1 := fun h => hns (Or.inr (Or.inl ⟨fun h' => h', by simp, by simp, h⟩))
      have hfac : 2 ^ (n * 2) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, by have := @Nat.one_le_two_pow n; omega⟩
        rw [pow_mul, hm, Nat.add_sub_cancel]
        exact Nat.sub_eq_of_eq_add (by ring)
      have hq : ¬ p ∣ 2 ^ (n * 2) - 1 := by
        rw [hfac]
        intro h
        rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
        · exact hq1 h'
        · exact hq2 h'
      have hn1 : 1 ≤ n := hlab.1
      have hlA : LargeEvenInLambda2 ⟨LargeEvenLieTag.A, 1, n * 2⟩ :=
        ⟨show 1 ≤ n * 2 by omega, show 1 ≤ 1 ∧ (1 = 1 → 2 ≤ n * 2) from ⟨le_rfl, fun _ => by omega⟩⟩
      have iff2 : ∀ Q, CFSG.Assembly.LargeEvenRawDatum ⟨LargeEvenLieTag.twD, 2, n⟩ Q ↔
          CFSG.Assembly.LargeEvenRawDatum ⟨LargeEvenLieTag.A, 1, n * 2⟩ Q := fun Q => by
        show LargeEvenRecipeLinear 2 ((2 ^ n) ^ 2) Q ↔ LargeEvenRecipeLinear (1 + 1) (2 ^ (n * 2)) Q
        rw [← pow_mul]
      exact labelAll_of_iff (lab' := ⟨LargeEvenLieTag.A, 1, n * 2⟩) iff2
        (canon_of_legacy (fun Q => Iff.rfl)
          (CFSG.StandardType.LargeEvenLabelAll.mono (fun _ _ _ _ h _ _ => h)
            (NbrInnerMore.largeEvenLabelAll_outdiagPrime_linear hp hlA rfl hq)))
    · by_cases h3 : l = 3
      · subst h3
        have hq : ¬ p ∣ 2 ^ n + 1 := fun h => hns (Or.inr (Or.inl ⟨fun h' => h', by simp, by simp, h⟩))
        have hlU : LargeEvenInLambda2 ⟨LargeEvenLieTag.twA, 3, n⟩ :=
          ⟨hlab.1, by norm_num, fun h => absurd h (by norm_num)⟩
        exact labelAll_of_iff (lab' := ⟨LargeEvenLieTag.twA, 3, n⟩) (fun Q => Iff.rfl)
          (canon_of_legacy (fun Q => Iff.rfl)
            (CFSG.StandardType.LargeEvenLabelAll.mono (fun _ _ _ _ h _ _ => h)
              (NbrInnerMore.largeEvenLabelAll_outdiagPrime_unitary hp hlU rfl hq)))
      · have hl2 : 2 ≤ l := hlab.2
        have hl4 : 4 ≤ l := by omega
        exact canon_of_legacy (fun Q => Iff.rfl)
          (CFSG.StandardType.LargeEvenLabelAll.mono (fun _ _ _ _ h _ _ => h)
            (NbrInnerMore.largeEvenLabelAll_outdiagPrime_orth p (Or.inr rfl) hl4))
  ·
    have hq : ¬ p ∣ 2 ^ n - 1 := fun h => hns (Or.inl ⟨trivial, h⟩)
    exact canon_of_legacy (fun Q => Iff.rfl)
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_E6 hp rfl hq)
  ·
    exact canon_of_legacy (fun Q => Iff.rfl)
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_E7 p hlab rfl)
  ·
    exact canon_of_legacy (fun Q => Iff.rfl)
      (outGuard_of_subset_inn
        (largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  ·
    exact canon_of_legacy (fun Q => Iff.rfl)
      (outGuard_of_subset_inn (largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inr (Or.inl rfl)))))
  ·
    by_cases hp3' : p = 3
    · subst hp3'
      have hn3 : ¬ 3 ∣ 2 ^ n + 1 := fun h => hns (Or.inr (Or.inl ⟨fun h' => h', by simp, by simp, h⟩))
      have hev : n % 2 = 0 := by
        by_contra hodd
        exact hn3 (three_dvd_two_pow_add_one_of_odd (by omega))
      obtain rfl : l = 0 := hlab.2
      exact canon_twE6_three hlab.1 hev
    · exact canon_of_legacy (fun Q => Iff.rfl)
        (NbrInnerMore.largeEvenLabelAll_outdiagPrime_twE6 hp hp3' hlab rfl)
  ·
    exact canon_of_legacy (fun Q => Iff.rfl)
      (outGuard_of_subset_inn (TableBExcSmallRest.largeEvenLabelAll_subset_inn_triD4 hlab rfl))
  ·
    exact canon_of_legacy (fun Q => Iff.rfl)
      (outGuard_of_subset_inn (largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inl rfl))))
  ·
    exact canon_of_legacy (fun Q => Iff.rfl)
      (outGuard_of_subset_inn
        (largeEvenLabelAll_subset_inn hlab (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  ·
    obtain ⟨rfl, hodd, hn3⟩ := hlab.2
    have hn3' : 3 ≤ n := hn3
    have ha : (n - 1) / 2 ≠ 0 := by omega
    have hiff : ∀ Q, CFSG.Assembly.LargeEvenRawDatum ⟨LargeEvenLieTag.twF4, 0, n⟩ Q ↔
        CFSG.StandardType.LargeEvenRawDatum ⟨LargeEvenLieTag.twF4, 0, n⟩ Q := fun Q => by
      show LargeEvenRecipeTwF4Inherited ((n - 1) / 2) Q ↔ LargeEvenRecipeTwF4 ((n - 1) / 2) Q
      unfold LargeEvenRecipeTwF4Inherited LargeEvenRecipeTwF4
      simp only [if_neg ha]
    exact canon_of_legacy hiff
      (outGuard_of_subset_inn (largeEvenLabelAll_subset_inn_twF4 hlab rfl))
  ·
    intro Q hQ
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, _, _, hK, hQK⟩ := hQ
    obtain ⟨e⟩ := nonempty_b2der_equiv_alternatingGroup hK
    exact ⟨K, inferInstance, inferInstance, hK,
      ⟨hQK, fun _ _ φ _ hφp => RawAut.mem_inner_of_isPGroup_outer (LargeExtraspecial.DW.isPGroup_outer_alt6 e) hp3 hφp⟩⟩
  ·
    intro Q hQ
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeG2Derived] at hQ ⊢
    obtain ⟨K, _, _, hK, hQK⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK,
      ⟨hQK, fun _ hna φ _ hφp => RawAutSmall.mem_inner_g2der hK hna hp3 hφp⟩⟩
  ·
    intro Q hQ
    obtain ⟨-, rfl⟩ := hlab.2
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at hQ ⊢
    obtain ⟨K, _, _, hK, hQK⟩ := hQ
    have h2 := RawAutSmall.isPGroup_outer_twF4der (a := (1 - 1) / 2) (by norm_num) hK
    exact ⟨K, inferInstance, inferInstance, hK,
      ⟨hQK, fun _ _ φ _ hφp => RawAut.mem_inner_of_isPGroup_outer h2 hp3 hφp⟩⟩

end Canon


section Main

open CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Multiplier CFSG.Open

theorem datum_facts {X : Type} [Group X] {P : LargeEvenMarkProp X}
    (h : CFSG.Assembly.LargeEvenMarking X P) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      CFSG.Assembly.LargeEvenMarking X (fun lab' _ _ _ _ _ => lab' = lab) ∧
      MarkedModel lab (X ⧸ Subgroup.center X) ∧ CFSG.Open.IsQuasisimple X := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hraw2 := CFSG.StandardType.Canonical.largeEvenRawDatum_markedModel hlab
    (fun R _ I F hq => hq.2.1) hraw
  obtain ⟨R, _, I, F, hq2⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw2
  obtain ⟨⟨hs, hna, θ, -⟩, hm⟩ := hq2
  refine ⟨lab, hlab, ⟨hX, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun R _ I F hq => ⟨hq.1, hq.2.1, by obtain ⟨θ, -⟩ := hq.2.2; exact ⟨θ, rfl⟩⟩) hraw⟩, ?_, ⟨hX, ?_⟩⟩
  · exact MarkedModel.of_mulEquiv θ.symm hm
  · exact (MulEquiv.isSimpleGroup_congr θ).mpr hs

theorem not_dvd_center_of_nosplit {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Subgroup G} (hK : IsChev2 K) (hNS : NoSplit16 p K) :
    ¬ p ∣ Nat.card (Subgroup.center ↥K) := by
  obtain ⟨lab, hlab, hLab, hm, hq⟩ := datum_facts hK
  have hns : ¬ LargeEvenSplit16 p lab := hNS lab hLab
  intro hpd
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  rcases h1 : genericOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab) with ⟨a, b⟩
  rcases h2 : exceptionalOrders (markTag lab) (markRank lab) (markChar lab) (markDeg lab)
    with ⟨c, d⟩
  have hne : a * b * (c * d) ≠ 0 := by
    have hpos := tabOrd_pos hlab
    unfold tabOrd at hpos
    rw [h1, h2] at hpos
    exact Nat.pos_iff_ne_zero.1 hpos
  have hm' : CFSG.Models.LieModel (↥K ⧸ Subgroup.center ↥K) (markTag lab) (markRank lab)
      (markChar lab) (markDeg lab) := I161aNames.lieModel_models_of_blueprint hm
  have hd := CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hq hm' h1 h2 hne
  have hpt : p ∣ tabOrd lab := by
    unfold tabOrd
    rw [h1, h2]
    exact hpd.trans hd
  exact hns (tabOrd_split hp hp2 hlab hpt)

theorem inducesInnerMod_of_marking {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K B : Subgroup G} (hNS : NoSplit16 p K) (hB : IsElemAbelian p B)
    (hBM : InnerDiagMarking B K) {b : G} (hb : b ∈ B) : InducesInnerMod p K b := by
  obtain ⟨hL, lab, hlab, hraw⟩ := hBM
  have hns : ¬ LargeEvenSplit16 p lab :=
    hNS lab ⟨hL, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F hq => ⟨hq.1, hq.2.1, by obtain ⟨θ, -⟩ := hq.2.2; exact ⟨θ, rfl⟩⟩) hraw⟩
  have hraw' := canon_outdiag hp hp2 hlab hns _ hraw
  obtain ⟨R, _, I, F, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw'
  obtain ⟨⟨hs, hna, θ, hBN, h3⟩, hG⟩ := hQ
  have hbN : b ∈ Subgroup.normalizer (K : Set G) := hBN hb
  have hφI : ggLAut K θ ⟨b, hbN⟩ ∈ I := ggLAut_mem_of_induces K θ hBN h3 hb
  have hpow : (ggLAut K θ ⟨b, hbN⟩) ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 := by
      ext
      simp [hB.2 b hb]
    rw [h1, map_one]
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 (hG hs hna _ hφI hpow)
  obtain ⟨k, hk, hkconj⟩ := NbrInnerMore.exists_conj_of_ggLAut_eq_conj hL θ hbN hr.symm
  refine ⟨k, hk, fun y hy => ?_⟩
  have hy' : b⁻¹ * y * b = k⁻¹ * y * k := hkconj y hy
  rw [hy', inv_mul_cancel]
  exact one_mem _

end Main

end I161a

theorem i161aAt_holds (G : Type) [Group G] [Finite G] : I161aAt G := by
  intro p hp hp2 K hK hNS
  exact ⟨I161a.not_dvd_center_of_nosplit hp hp2 hK hNS,
    fun B hB hBM b hb => I161a.inducesInnerMod_of_marking hp hp2 hNS hB hBM hb⟩

end CFSG.LocalAnalysis.GLTheoremA
