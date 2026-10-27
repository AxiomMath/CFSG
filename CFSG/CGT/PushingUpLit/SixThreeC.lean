module

public import CFSG.CGT.PushingUpLit.SixThreeShort
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeDoubleCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement Pointwise

namespace SixThree

variable {G : Type} [Group G]

theorem isPGroup_two_of_no_odd_prime_orderOf [Finite G] {A : Subgroup G}
    (h : ∀ x ∈ A, ∀ p : ℕ, p.Prime → p ≠ 2 → orderOf x ≠ p) : IsPGroup 2 A := by
  have hne : Nat.card A ≠ 0 := Nat.card_pos.ne'
  obtain ⟨k, hk⟩ : ∃ k, Nat.card A = 2 ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne ?_⟩
    intro p hp hpd
    by_contra hp2
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpd
    exact h x x.2 p hp hp2 (by rw [← hx, Subgroup.orderOf_coe])
  exact IsPGroup.of_card hk

@[expose] def stabSeries (V Q : Subgroup G) [V.Normal] : Subgroup G where
  carrier := {x | x ∈ Subgroup.centralizer (V : Set G) ∧ ∀ q ∈ Q, ⁅x, q⁆ ∈ V}
  one_mem' := ⟨one_mem _, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨mul_mem hx hy, fun q hq => ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact V.mul_mem
      (by simpa [mul_assoc] using (inferInstance : V.Normal).conj_mem _ (hy' q hq) x) (hx' q hq)
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨inv_mem hx, fun q hq => ?_⟩
    have := (inferInstance : V.Normal).conj_mem _ (V.inv_mem (hx' q hq)) x⁻¹
    rw [commutatorElement_inv_left, ← commutatorElement_inv]
    simpa using this

instance stabSeries_normal (V Q : Subgroup G) [V.Normal] [Q.Normal] : (stabSeries V Q).Normal where
  conj_mem x hx g := by
    obtain ⟨hxc, hxq⟩ := hx
    refine ⟨?_, fun q hq => ?_⟩
    · exact Subgroup.Normal.conj_mem inferInstance x hxc g
    · have h1 := hxq (g⁻¹ * q * g) (by simpa using (inferInstance : Q.Normal).conj_mem q hq g⁻¹)
      have h2 := (inferInstance : V.Normal).conj_mem _ h1 g
      have e : g * ⁅x, g⁻¹ * q * g⁆ * g⁻¹ = ⁅g * x * g⁻¹, q⁆ := by
        rw [conjugate_commutatorElement]
        have e1 : g * (g⁻¹ * q * g) * g⁻¹ = q := by group
        rw [e1]
      rw [← e]
      exact h2

theorem stabSeries_le [Finite G] {V Q : Subgroup G} [V.Normal] [Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hchar : Subgroup.centralizer (Q : Set G) ≤ Q)
    (hmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ Q) : stabSeries V Q ≤ Q := by
  refine hmax _ inferInstance ?_
  refine isPGroup_two_of_no_odd_prime_orderOf fun x hx p hp hp2 hord => ?_
  set R := Subgroup.zpowers x with hR
  have hRS : R ≤ stabSeries V Q := Subgroup.zpowers_le.mpr hx
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.normalizer_eq_top Q]
    exact le_top
  have hodd : Odd (orderOf x) := hord ▸ hp.odd_of_ne_two hp2
  have hcop := coprime_card_zpowers_of_odd hodd hQ2
  have hdouble : ⁅⁅Q, R⁆, R⁆ = ⊥ := by
    have h1 : ⁅Q, R⁆ ≤ V := by
      refine Subgroup.commutator_le.mpr fun q hq r hr => ?_
      rw [← commutatorElement_inv]
      exact V.inv_mem ((hRS hr).2 q hq)
    have h2 : ⁅V, R⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun r hr => (hRS hr).1
    exact eq_bot_iff.mpr ((Subgroup.commutator_mono h1 le_rfl).trans h2.le)
  have hbot := CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot Q R
    hRQ hcop hdouble
  have hxc : x ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hQR : Q ≤ Subgroup.centralizer (R : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    exact ((Subgroup.mem_centralizer_iff.mp (hQR hq)) x (Subgroup.mem_zpowers x)).symm
  have hxQ : x ∈ Q := hchar hxc
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨x, hxQ⟩
  rw [Subgroup.orderOf_mk, hord] at hk
  have := (Nat.Prime.pow_eq_iff hp).mp hk.symm
  exact hp2 this.1.symm

theorem commutator_le_stabSeries {Y Q V C : Subgroup G} [V.Normal] [Q.Normal] [C.Normal]
    (hQV : ⁅Q, Y⁆ ≤ V) (hCV : C ≤ Subgroup.centralizer (V : Set G)) :
    ⁅C, Y⁆ ≤ stabSeries V Q := by
  have hnorm : ∀ H : Subgroup G, H ≤ Subgroup.normalizer (V : Set G) := fun H => by
    rw [Subgroup.normalizer_eq_top V]
    exact le_top
  have hYQ : ⁅Y, Q⁆ ≤ V := by
    rw [Subgroup.commutator_comm]
    exact hQV
  have hVC : ⁅V, C⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hCV
  have h1 : ⁅⁅Y, Q⁆, C⁆ ≤ V :=
    ((Subgroup.commutator_mono hYQ le_rfl).trans hVC.le).trans bot_le
  have h2 : ⁅⁅Q, C⁆, Y⁆ ≤ V :=
    (Subgroup.commutator_mono (Subgroup.commutator_le_left Q C) le_rfl).trans hQV
  have h3 : ⁅⁅C, Y⁆, Q⁆ ≤ V :=
    CFSG.RankThree.PartTwo.Sec6.three_subgroups_mod (hnorm Y) (hnorm Q) (hnorm C) h1 h2
  refine Subgroup.commutator_le.mpr fun c hc y hy => ?_
  refine ⟨hCV (Subgroup.commutator_le_left C Y (Subgroup.commutator_mem_commutator hc hy)),
    fun q hq => h3 (Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator hc hy) hq)⟩

theorem le_normalizer_of_commutator_le [Finite G] {Y Q C : Subgroup G} [Q.Normal]
    (hNo : SubTwo.NoTwoQuotient Y) (hQ2 : IsPGroup 2 Q)
    (hQY : Q ≤ Subgroup.normalizer (Y : Set G)) (hCQ : ⁅C, Y⁆ ≤ Q) :
    C ≤ Subgroup.normalizer (Y : Set G) := by
  intro c hc
  have hconj : ∀ c ∈ C, ∀ b ∈ Y ⊔ Q, c * b * c⁻¹ ∈ Y ⊔ Q := by
    intro c hc b hb
    obtain ⟨y, hy, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
    have e : c * (y * q) * c⁻¹ = (⁅c, y⁆ * y) * (c * q * c⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_right
      (hCQ (Subgroup.commutator_mem_commutator hc hy))) (Subgroup.mem_sup_left hy))
      (Subgroup.mem_sup_right ((inferInstance : Q.Normal).conj_mem q hq c))
  have hcB : c ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff.mpr fun b => ⟨hconj c hc b, fun h => by
      have := hconj c⁻¹ (C.inv_mem hc) _ h
      simpa [mul_assoc] using this⟩
  refine SubTwo.mem_normalizer_of_normal_chain (B := Y ⊔ Q)
    (B' := Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) (P := Q) hNo le_sup_left
    (sup_le Subgroup.le_normalizer hQY) le_rfl hQ2 ?_ hcB
  intro b hb
  obtain ⟨y, hy, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
  exact ⟨y, hy, q, hq, Subgroup.mem_sup_right hq, rfl⟩

theorem le_centralizerModCore_of_commutator_le [Finite G] {Y Q C : Subgroup G} [Q.Normal]
    (hNo : SubTwo.NoTwoQuotient Y) (hQ2 : IsPGroup 2 Q)
    (hQY : Q ≤ Subgroup.normalizer (Y : Set G)) (hCQ : ⁅C, Y⁆ ≤ Q) :
    C ≤ centralizerModCore Y := by
  intro c hc
  have hcY := le_normalizer_of_commutator_le hNo hQ2 hQY hCQ hc
  refine ⟨hcY, fun x hx => ?_⟩
  have hYQ : Y ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.normalizer_eq_top Q]
    exact le_top
  have hN : Y ⊓ Q ≤ oTwoIn Y :=
    le_oTwoIn_of_isPGroup inf_le_left (hQ2.to_le inf_le_right)
      (le_trans (le_inf Subgroup.le_normalizer hYQ) Subgroup.inf_normalizer_le_normalizer_inf)
  refine hN ⟨?_, hCQ (Subgroup.commutator_mem_commutator hc hx)⟩
  have h1 : c * x * c⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hcY x).mp hx
  exact Y.mul_mem h1 (Y.inv_mem hx)

theorem step_three [Finite G] {Y Q V : Subgroup G} [Q.Normal] [V.Normal]
    (hNo : SubTwo.NoTwoQuotient Y) (hQ2 : IsPGroup 2 Q)
    (hchar : Subgroup.centralizer (Q : Set G) ≤ Q)
    (hmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ Q)
    (hQY : Q ≤ Subgroup.normalizer (Y : Set G)) (hQV : ⁅Q, Y⁆ ≤ V) :
    Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y :=
  le_centralizerModCore_of_commutator_le hNo hQ2 hQY
    ((commutator_le_stabSeries hQV le_rfl).trans (stabSeries_le hQ2 hchar hmax))

end SixThree

end CFSG.CGT.PushingUpLit
