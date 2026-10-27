module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Defs
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open Subgroup
open scoped commutatorElement

private theorem p65cp_eq_one_of_coprime {M : Type*} [Group M] {σ : M} {a b : ℕ}
    (ha : σ ^ a = 1) (hb : σ ^ b = 1) (hab : Nat.Coprime a b) : σ = 1 := by
  have h1 : orderOf σ ∣ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf σ ∣ b := orderOf_dvd_of_pow_eq_one hb
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hab h1 h2)

private theorem p65cp_not_dvd_prod {f p : ℕ} (hf : f.Prime) (hp : p.Prime) (hf2 : f ≠ 2)
    (hfp : f < p) {d : ℕ} (hd : d ≤ 2) : ¬ p ∣ ∏ i : Fin d, (f ^ d - f ^ (i : ℕ)) := by
  have hf3 : 3 ≤ f := by
    have := hf.two_le
    omega
  have hpf : ¬ p ∣ f := fun h => by
    have := Nat.le_of_dvd hf.pos h
    omega
  have hpf1 : ¬ p ∣ f - 1 := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hpf2 : ¬ p ∣ f + 1 := fun h => by
    have h1 := Nat.le_of_dvd (by omega) h
    have h2 : p = f + 1 := by omega
    have hfodd : Odd f := hf.odd_of_ne_two hf2
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    rw [h2] at hpodd
    obtain ⟨k, hk⟩ := hfodd
    obtain ⟨l, hl⟩ := hpodd
    omega
  interval_cases d
  · simpa using hp.one_lt.ne'
  · simpa using hpf1
  · rw [Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · have : f ^ 2 - 1 = (f - 1) * (f + 1) := by
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
      rw [this] at h1
      rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · exact hpf1 h2
      · exact hpf2 h2
    · have : f ^ 2 - f = f * (f - 1) := by
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
      rw [this] at h1
      rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · exact hpf h2
      · exact hpf1 h2

private theorem p65cp_aut_elementary_trivial {f p : ℕ} [hf : Fact f.Prime] (hp : p.Prime)
    (hf2 : f ≠ 2) (hfp : f < p) {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ f = 1) {d : ℕ} (hd : d ≤ 2)
    (hcard : Nat.card W = f ^ d) {τ : MulAut W} {m : ℕ} (hτ : τ ^ p ^ m = 1) : τ = 1 := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hcard
  have h1 : Nat.card (MulAut W) = ∏ i : Fin d, (f ^ d - f ^ (i : ℕ)) := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  have h2 : τ ^ Nat.card (MulAut W) = 1 := pow_card_eq_one'
  refine p65cp_eq_one_of_coprime hτ h2 (Nat.Coprime.pow_left m ?_)
  rw [Nat.Prime.coprime_iff_not_dvd hp, h1]
  exact p65cp_not_dvd_prod hf.out hp hf2 hfp hd

private theorem p65cp_aut_trivial {f p : ℕ} [hf : Fact f.Prime] (hp : p.Prime) (hf2 : f ≠ 2)
    (hfp : f < p) {Y : Type*} [Group Y] [Finite Y] (hY : IsPGroup f Y)
    (hrank : CFSG.pRank f Y ≤ 2) {σ : MulAut Y} {m : ℕ} (hσ : σ ^ p ^ m = 1) : σ = 1 := by
  rcases subsingleton_or_nontrivial Y with _ | _
  · exact MulEquiv.ext fun y => Subsingleton.elim _ _
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hf2 hY
  have hcop : ∀ k : ℕ, Nat.Coprime (p ^ m) (f ^ k) := fun k =>
    Nat.Coprime.pow m k ((Nat.coprime_primes hp hf.out).2 (Nat.ne_of_gt hfp))
  set σD : MulAut D := CFSG.FiveTransitive.CharacteristicAutomorphism.restrict D σ with hσDdef
  have hσD : σD ^ p ^ m = 1 := by rw [hσDdef, ← map_pow, hσ, map_one]
  have hDp : IsPGroup f D := hY.to_subgroup D
  have hexp : ∀ x : D, x ^ f = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hclass : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    have hab : ⁅(a : Y), (b : Y)⁆ ∈ ⁅D, (⊤ : Subgroup Y)⁆ :=
      Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top _)
    have := Subgroup.mem_centralizer_iff.mp (hDcomm hab).2 d d.2
    simp only [commutatorElement_def] at this ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  have hrankD : CFSG.pRank f D ≤ 2 := by
    have h1 : CFSG.pRank f D ≤ CFSG.pRank f Y := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top f D,
        CFSG.SectionRank.pRank_eq_open_pRank_top f Y]
      exact CFSG.SectionRank.pRank_top_le_of_injective hf.out.one_lt D.subtype
        D.subtype_injective
    omega
  obtain ⟨hb1, -, -⟩ := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDp hexp hclass
  have hfc : frattini D = commutator D := CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hexp
  obtain ⟨-, hcommW, hpowW, -, d, hd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  have hd2 : d ≤ 2 := by
    have hd' : Nat.card (D ⧸ commutator D) = f ^ d := by
      rw [← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hfc).toEquiv]
      exact hd
    have h1 := hb1 hrankD
    rwa [CFSG.RankThree.PartTwo.pRank_eq_of_isMulCommutative hf.out
      (CFSG.RankThree.PartTwo.quotient_pow_eq_one hexp _)
      CFSG.RankThree.PartTwo.isMulCommutative_quotient_commutator hd'] at h1
  have hτ : (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini D) σD) ^
      p ^ m = 1 := by
    rw [← map_pow, hσD, map_one]
  have hτ1 := p65cp_aut_elementary_trivial hp hf2 hfp (fun a b => hcommW.is_comm.comm a b) hpowW
    hd2 hd hτ
  have hker : σD ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini D)).ker := hτ1
  obtain ⟨-, hkerp⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hDp
  obtain ⟨k, hk⟩ := hkerp ⟨σD, hker⟩
  have hσD1 : σD = 1 :=
    p65cp_eq_one_of_coprime hσD (congrArg Subtype.val hk : σD ^ f ^ k = 1) (hcop k)
  have hσfix : σ ∈ fixingSubgroup (MulAut Y) (D : Set Y) := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact congrArg (fun τ : MulAut D => ((τ ⟨x, hx⟩ : D) : Y)) hσD1
  obtain ⟨k', hk'⟩ := hDfix ⟨σ, hσfix⟩
  exact p65cp_eq_one_of_coprime hσ (congrArg Subtype.val hk' : σ ^ f ^ k' = 1) (hcop k')

private def p65cp_conjAut {A : Type*} [Group A] (Y : Subgroup A) (b : A)
    (hb : b ∈ normalizer (Y : Set A)) : MulAut Y where
  toFun y := ⟨b * y * b⁻¹, (mem_set_normalizer_iff.mp hb y).mp y.2⟩
  invFun y := ⟨b⁻¹ * y * b, (mem_set_normalizer_iff''.mp hb y).mp y.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private theorem p65cp_conjAut_pow {A : Type*} [Group A] (Y : Subgroup A) (b : A)
    (hb : b ∈ normalizer (Y : Set A)) (n : ℕ) (y : Y) :
    ((((p65cp_conjAut Y b hb) ^ n) y : Y) : A) = b ^ n * y * (b ^ n)⁻¹ := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih]
    have h1 : (((p65cp_conjAut Y b hb) y : Y) : A) = b * y * b⁻¹ := rfl
    rw [h1, pow_succ]
    group

theorem p65_coprime_rank_two : P65CoprimeRankTwo := by
  intro A _ _ p f Y B hp _ hf hf2 hfp hY hB hBN hrank
  haveI : Fact f.Prime := ⟨hf⟩
  intro b hb
  rw [mem_centralizer_iff]
  intro y hy
  have hbN := hBN hb
  obtain ⟨m, hm⟩ := hB ⟨b, hb⟩
  have hbm : b ^ p ^ m = 1 := congrArg Subtype.val hm
  have hσ : (p65cp_conjAut Y b hbN) ^ p ^ m = 1 := by
    ext z
    rw [p65cp_conjAut_pow, hbm]
    simp
  have hrankY : CFSG.pRank f Y ≤ 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hrank
  have h1 := p65cp_aut_trivial hp hf2 hfp hY hrankY hσ
  have h2 := congrArg (fun τ : MulAut Y => ((τ ⟨y, hy⟩ : Y) : A)) h1
  have h3 : b * y * b⁻¹ = y := h2
  calc y * b = b * y * b⁻¹ * b := by rw [h3]
    _ = b * y := by group

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
