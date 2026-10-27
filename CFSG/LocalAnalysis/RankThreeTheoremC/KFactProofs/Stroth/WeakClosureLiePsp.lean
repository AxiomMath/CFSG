module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieBlockFrame
public import CFSG.GroupTheory.WeirSylow.Symplectic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePspFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

@[expose] def spProj (n : ℕ) (K : Type) [Field K] : StatedSp n K →* StatedProj (StatedSp n K) :=
  QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K))

theorem sq_eq_one_of_mem_spScalars {n : ℕ} {K : Type} [Field K] {g : StatedSp n K}
    (hg : g ∈ (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) : g ^ 2 = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    have hall : ∀ x : Matrix.GeneralLinearGroup (Fin 0 ⊕ Fin 0) K, x = 1 := fun x =>
      Units.ext (Matrix.ext fun a => by rcases a with a | a <;> exact a.elim0)
    rw [show g = 1 from Subtype.ext (hall _), one_pow]
  · obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
    have hsp : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n K := by
      rw [hc]
      exact g.2
    have hc2 : c ^ 2 = 1 := (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hn c).1 hsp
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc, ← map_pow, hc2, map_one]

theorem spProj_comp_injective {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ} {K : Type} [Field K]
    {A : Type} [Group A] (T : A →* StatedSp n K) (hT : Function.Injective T)
    (hA : ∀ a : A, ∃ k : ℕ, a ^ p ^ k = 1) : Function.Injective ((spProj n K).comp T) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : (QuotientGroup.mk (T x) : StatedProj (StatedSp n K)) = 1 := hx
  have hmem : T x ∈ (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) :=
    (QuotientGroup.eq_one_iff (T x)).1 hx'
  obtain ⟨k, hk⟩ := hA x
  have h2 : T x ^ 2 = 1 := sq_eq_one_of_mem_spScalars hmem
  have hpk : T x ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hcop : Nat.Coprime 2 (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two Fact.out).2 hp2.symm)
  have h3 : orderOf (T x) ∣ Nat.gcd 2 (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hpk)
  rw [hcop.gcd_eq_one] at h3
  have h4 : T x = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  exact hT (by rw [map_one]; exact h4)

theorem factorization_card_projSp {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ} {K : Type}
    [Field K] [Finite K] :
    (Nat.card (StatedProj (StatedSp n K))).factorization p =
      (Nat.card (StatedSp n K)).factorization p := by
  have hp : p.Prime := Fact.out
  have hZ : ¬ p ∣ Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
    have hx2 : x ^ 2 = 1 := Subtype.ext (sq_eq_one_of_mem_spScalars x.2)
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hcard : Nat.card (StatedSp n K) =
      Nat.card (StatedProj (StatedSp n K)) *
        Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hP : Nat.card (StatedProj (StatedSp n K)) ≠ 0 := Nat.card_pos.ne'
  have hZ0 : Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) ≠ 0 :=
    Nat.card_pos.ne'
  rw [hcard, Nat.factorization_mul hP hZ0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hZ, add_zero]

theorem wcOn_projSp {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    (hpK : ¬ p ∣ Nat.card K) (n : ℕ) : WCOn p (StatedProj (StatedSp n K)) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hp : p.Prime := Fact.out
  have hp1 : Odd p := hp.odd_of_ne_two hp2
  have hpK' : ¬ p ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Fintype.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  obtain ⟨a, ha_def⟩ : ∃ a, padicValNat p (Fintype.card K ^ e - 1) = a := ⟨_, rfl⟩
  obtain ⟨r, hr_def⟩ : ∃ r, (if Even e then 2 * n else n) / e = r := ⟨_, rfl⟩
  have ha : 1 ≤ a := by
    rw [← ha_def, ← he]
    exact CrossNum.one_le_crossA hpK' hq1
  obtain ⟨F⟩ := nonempty_spFrame K hpK' n he ha_def hr_def
  have hcard : (Nat.card (StatedProj (StatedSp n K))).factorization p =
      a * r + r.factorial.factorization p := by
    rw [factorization_card_projSp hp2,
      CFSG.GroupTheory.WeirSylow.factorization_card_statedSp hp1 K hpK' n, he, ha_def,
      hr_def, Nat.factorization_def _ hp]
  have hinj : Function.Injective ((spProj n K).comp F.T) :=
    spProj_comp_injective hp2 F.T F.T_injective fun c => ⟨a, pow_pPow_eq_one_pi c⟩
  exact (F.map (spProj n K) hinj).wcOn hp2 ha hcard

theorem crossClassical_psp : CrossClassical .PSp 2 := by
  intro K _ _ n ℓ f p _ hp2 hpℓ _ _ h
  have hp := (Fact.out : p.Prime)
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := h
  have hℓ : ℓ.Prime := hadm.1
  have hpq : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
  exact WCOn.of_mulEquiv e (wcOn_projSp hp2 hpq n)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
