module

public import Mathlib.GroupTheory.Frattini
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGenPower
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
import Mathlib.CategoryTheory.Category.Basic

public section

namespace CFSG.AGLEmbedding.ThompsonGen

open scoped commutatorElement

universe u

@[expose] def PCentral (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ z : K, z ^ p = 1 → ∀ g : K, g * z = z * g

theorem commutator_pow_eq_one_aux {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ (n : ℕ) (K : Type u) [Group K] [Finite K], Nat.card K = n → IsPGroup p K → PCentral p K →
      ∀ x g : K, x ^ p ^ 2 = 1 → ⁅x, g⁆ ^ p = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ hn hK hc x g hx
    obtain ⟨x', hx'⟩ : ∃ x' : K, x' = g * x * g⁻¹ := ⟨_, rfl⟩
    have hxpc : ∀ h : K, h * x ^ p = x ^ p * h := hc _ (by rw [← pow_mul, ← sq]; exact hx)
    by_cases htop : Subgroup.closure ({x, x'} : Set K) = ⊤
    · have hfr : _root_.commutator K ≤ frattini K := by
        have : Fact (IsPGroup p K) := ⟨hK⟩
        exact CFSG.commutator_le_frattini_of_isPGroup (p := p)
      have hle : Subgroup.closure ({x, x'} : Set K) ≤ Subgroup.zpowers x ⊔ frattini K := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
        · have h1 : ⁅x⁻¹, g⁆ ∈ frattini K :=
            hfr (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
          have : y = x * ⁅x⁻¹, g⁆ := by rw [hx']; simp only [commutatorElement_def]; group
          rw [SetLike.mem_coe, this]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
            (Subgroup.mem_sup_right h1)
      have hz : Subgroup.zpowers x = ⊤ := frattini_nongenerating (eq_top_iff.2 (htop ▸ hle))
      have hgx : g ∈ Subgroup.zpowers x := hz ▸ Subgroup.mem_top g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgx
      rw [(Commute.self_zpow x k).commutator_eq, one_pow]
    · have hxH : x ∈ Subgroup.closure ({x, x'} : Set K) := Subgroup.subset_closure (by simp)
      have hx'H : x' ∈ Subgroup.closure ({x, x'} : Set K) := Subgroup.subset_closure (by simp)
      have hHlt : Nat.card (Subgroup.closure ({x, x'} : Set K)) < n := by
        have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 htop)
        rwa [Subgroup.card_top, hn] at this
      have hHc : PCentral p (Subgroup.closure ({x, x'} : Set K)) := fun z hz g' => by
        apply Subtype.ext
        have := hc (z : K) (by simpa using congrArg Subtype.val hz) g'
        simpa using this
      have h1 := ih _ hHlt (Subgroup.closure ({x, x'} : Set K)) rfl (hK.to_subgroup _) hHc
        ⟨x, hxH⟩ ⟨x', hx'H⟩ (Subtype.ext (by simpa using hx))
      have hc' : ⁅x, x'⁆ ^ p = 1 := by
        have := congrArg Subtype.val h1
        simpa [commutatorElement_def] using this
      have hcen : ∀ h : K, h * ⁅x, x'⁆ = ⁅x, x'⁆ * h := hc _ hc'
      have hxa : ⁅x, x' * x⁻¹⁆ = ⁅x, x'⁆ := by simp only [commutatorElement_def]; group
      have hmul := mul_pow_prime_of_commutator (Fact.out : p.Prime) hp2 (x := x' * x⁻¹) (y := x)
        (by rw [hxa]; exact (hcen _).symm) (by rw [hxa]; exact (hcen _).symm)
        (by rw [hxa]; exact hc')
      have h2 : x' * x⁻¹ * x = x' := by group
      have h3 : x' ^ p = x ^ p := by
        rw [hx', conj_pow]
        calc g * x ^ p * g⁻¹ = x ^ p * g * g⁻¹ := by rw [hxpc g]
          _ = x ^ p := by group
      rw [h2, h3] at hmul
      have h4 : (x' * x⁻¹) ^ p = 1 := mul_eq_right.mp hmul.symm
      have h5 : ⁅g, x⁆ = x' * x⁻¹ := by rw [hx']; simp only [commutatorElement_def]
      rw [← commutatorElement_inv g x, inv_pow, h5, h4, inv_one]

private def pOmega {p : ℕ} {K : Type*} [Group K] (hc : PCentral p K) : Subgroup K where
  carrier := {z | z ^ p = 1}
  one_mem' := one_pow p
  mul_mem' := fun {a b} ha hb => by
    have hab : Commute a b := (hc a ha b : Commute b a).symm
    show (a * b) ^ p = 1
    rw [hab.mul_pow]
    exact by simp_all
  inv_mem' := fun {a} ha => by
    show a⁻¹ ^ p = 1
    simp_all

private theorem mem_pOmega {p : ℕ} {K : Type*} [Group K] (hc : PCentral p K) {z : K} :
    z ∈ pOmega hc ↔ z ^ p = 1 := Iff.rfl

private instance pOmega_normal {p : ℕ} {K : Type*} [Group K] (hc : PCentral p K) :
    (pOmega hc).Normal where
  conj_mem n hn g := by
    rw [mem_pOmega] at hn ⊢
    rw [conj_pow, hn]; simp

private theorem pcentral_quotient_pOmega {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type u}
    [Group K] [Finite K] (hK : IsPGroup p K) (hc : PCentral p K) :
    PCentral p (K ⧸ pOmega hc) := by
  intro z hz g
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_pOmega] at hz
  have hz2 : z ^ p ^ 2 = 1 := by rw [sq, pow_mul, hz]
  have h1 := commutator_pow_eq_one_aux hp2 (Nat.card K) K rfl hK hc z g hz2
  have h2 : ⁅z, g⁆ ∈ pOmega hc := h1
  have h3 : ((⁅z, g⁆ : K) : K ⧸ pOmega hc) = 1 := (QuotientGroup.eq_one_iff _).2 h2
  have h4 : ⁅(z : K ⧸ pOmega hc), (g : K ⧸ pOmega hc)⁆ = 1 := by
    rw [commutatorElement_def] at h3 ⊢
    simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h3
  exact (commutatorElement_eq_one_iff_mul_comm.1 h4).symm

theorem pow_inj_aux {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ (n : ℕ) (K : Type u) [Group K] [Finite K], Nat.card K = n → IsPGroup p K → PCentral p K →
      ∀ x y : K, x ^ p = y ^ p → (x⁻¹ * y) ^ p = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ hn hK hc x y hxy
    by_cases hsub : Subsingleton K
    · exact Subsingleton.elim _ _
    · rw [not_subsingleton_iff_nontrivial] at hsub
      have hdvd : p ∣ Nat.card K := by
        rcases hK.card_eq_or_dvd with h | h
        · exact absurd (Nat.card_eq_one_iff_unique.1 h).1 (not_subsingleton_iff_nontrivial.2 hsub)
        · exact h
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hzΩ : z ∈ pOmega hc := by rw [mem_pOmega, ← hz]; exact pow_orderOf_eq_one z
      have hz1 : z ≠ 1 := by
        intro h; rw [h, orderOf_one] at hz; exact (Fact.out : p.Prime).one_lt.ne hz
      have hΩnt : 1 < Nat.card (pOmega hc) := by
        rw [Nat.one_lt_iff_ne_zero_and_ne_one]
        refine ⟨Nat.card_pos.ne', fun h => hz1 ?_⟩
        have := (Nat.card_eq_one_iff_unique.1 h).1
        exact congrArg Subtype.val (Subsingleton.elim (⟨z, hzΩ⟩ : pOmega hc) 1)
      have hlt : Nat.card (K ⧸ pOmega hc) < n := by
        rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup (pOmega hc)]
        exact lt_mul_of_one_lt_right Nat.card_pos hΩnt
      have hbar := ih _ hlt (K ⧸ pOmega hc) rfl (hK.to_quotient _)
        (pcentral_quotient_pOmega hp2 hK hc) x y
        (by rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, hxy])
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
        QuotientGroup.eq_one_iff, mem_pOmega] at hbar
      have hw2 : (x⁻¹ * y) ^ p ^ 2 = 1 := by rw [sq, pow_mul, hbar]
      have h1 := commutator_pow_eq_one_aux hp2 (Nat.card K) K rfl hK hc (x⁻¹ * y) x hw2
      have hcen : ∀ h : K, h * ⁅x⁻¹ * y, x⁆ = ⁅x⁻¹ * y, x⁆ * h := hc _ h1
      have hmul := mul_pow_prime_of_commutator (Fact.out : p.Prime) hp2 (x := x) (y := x⁻¹ * y)
        (by exact (hcen _).symm) (by exact (hcen _).symm) h1
      rw [mul_inv_cancel_left, ← hxy] at hmul
      exact (mul_eq_left.mp hmul.symm)

theorem pow_rank_le_card_quotient_frattini {p : ℕ} [Fact p.Prime] {K : Type*} [Group K]
    [Finite K] (hK : IsPGroup p K) : p ^ Group.rank K ≤ Nat.card (K ⧸ frattini K) := by
  have : Fact (IsPGroup p K) := ⟨hK⟩
  have : CFSG.IsElementaryAbelian p (K ⧸ frattini K) :=
    CFSG.isElementaryAbelian_quotient_frattini
  rw [CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := p) (K ⧸ frattini K)]
  apply Nat.pow_le_pow_right (Fact.out : p.Prime).pos
  rw [← CFSG.generatorRank_eq_group_rank]
  exact CFSG.generatorRank_le_generatorRank_quotient_frattini (p := p) K

theorem pow_rank_le_card_omega {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type u} [Group K]
    [Finite K] (hK : IsPGroup p K) (hc : PCentral p K) :
    p ^ Group.rank K ≤ Nat.card {z : K // z ^ p = 1} := by
  have : Fact (IsPGroup p K) := ⟨hK⟩
  let r : K → K := fun x => Function.invFun (fun y : K => y ^ p) (x ^ p)
  have hr : ∀ x, (r x) ^ p = x ^ p := fun x =>
    Function.invFun_eq (f := fun y : K => y ^ p) ⟨x, rfl⟩
  let g : K → frattini K × {z : K // z ^ p = 1} := fun x =>
    (⟨x ^ p, CFSG.pth_power_mem_frattini_of_isPGroup x⟩,
      ⟨(r x)⁻¹ * x, pow_inj_aux hp2 (Nat.card K) K rfl hK hc (r x) x (hr x)⟩)
  have hg : Function.Injective g := by
    intro x x' h
    have h1 : x ^ p = x' ^ p := congrArg (fun t => ((t.1 : frattini K) : K)) h
    have h2 : (r x)⁻¹ * x = (r x')⁻¹ * x' :=
      congrArg (fun t => ((t.2 : {z : K // z ^ p = 1}) : K)) h
    have h3 : r x = r x' := by simp only [r, h1]
    rw [h3] at h2
    exact mul_left_cancel h2
  have h4 : Nat.card K ≤ Nat.card (frattini K) * Nat.card {z : K // z ^ p = 1} := by
    have := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_prod] at this
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini K), mul_comm] at h4
  exact (pow_rank_le_card_quotient_frattini hK).trans (Nat.le_of_mul_le_mul_left h4 Nat.card_pos)

end CFSG.AGLEmbedding.ThompsonGen
