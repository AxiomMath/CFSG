module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup
open scoped commutatorElement

namespace SolvNone

theorem closure_twoElements_eq_top {I₀ : Type} [Group I₀] [Finite I₀]
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀)) :
    Subgroup.closure {x : I₀ | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 I₀ with hN
  set S := {x : I₀ | ∃ k : ℕ, x ^ 2 ^ k = 1} with hS
  have hNS : ∀ n ∈ N, n ∈ S := fun n hn => by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := I₀)) ⟨n, hn⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hQ := IsSymThreeOrSUThreeTwo.closure_two
    CFSG.LocalAnalysis.RankThreeTheoremC.kFactSUThreeTwoShape_holds hb
  have hmap : (Subgroup.closure S).map (QuotientGroup.mk' N) = ⊤ := by
    refine eq_top_iff.mpr (hQ ▸ (Subgroup.closure_le _).mpr ?_)
    rintro x ⟨k, hk⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hyN : y ^ 2 ^ k ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      simpa using hk
    obtain ⟨m, hm⟩ := hNS _ hyN
    refine ⟨y, Subgroup.subset_closure ⟨k + m, ?_⟩, rfl⟩
    rw [pow_add, pow_mul, hm]
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.mp (hmap ▸ Subgroup.mem_top (QuotientGroup.mk' N g))
  have hsN : s⁻¹ * g ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    simp only [QuotientGroup.mk'_apply] at hsg
    rw [hsg, inv_mul_cancel]
  have h1 : s⁻¹ * g ∈ Subgroup.closure S := Subgroup.subset_closure (hNS _ hsN)
  simpa using (Subgroup.closure S).mul_mem hs h1

theorem eq_bot_of_twoElements_le_centralizer {G : Type*} [Group G] [Finite G] {Q P : Subgroup G}
    (hQ : Q ≤ Subgroup.closure {x | x ∈ Q ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}) (hPQ : P ≤ Q)
    (hP : IsPGroup 3 P) (hpow : ∀ q ∈ Q, ∃ a : ℕ, q ^ 2 ^ a ∈ P)
    (hcen : ∀ x ∈ Q, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ centralizer (P : Set G)) : P = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := {x | x ∈ Q ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} with hS
  have hSQ : Subgroup.closure S ≤ Q := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hQC : Q ≤ centralizer (P : Set G) :=
    hQ.trans ((Subgroup.closure_le _).mpr fun x hx => hcen x hx.1 hx.2)
  set P' : Subgroup Q := P.subgroupOf Q with hP'
  have hP'c : P' ≤ center Q := by
    intro p hp
    rw [mem_center_iff]
    intro q
    exact Subtype.ext ((mem_centralizer_iff.mp (hQC q.2)) p (mem_subgroupOf.mp hp)).symm
  haveI : P'.Normal := ⟨fun n hn g => by
    have hc := mem_center_iff.mp (hP'c hn) g
    rw [hc, mul_inv_cancel_right]
    exact hn⟩
  have hQP : IsPGroup 2 (Q ⧸ P') := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a, ha⟩ := hpow q q.2
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_subgroupOf.mpr (by simpa using ha)
  obtain ⟨m, hm⟩ := hQP.exists_card_eq
  have hidx : (center Q).index ∣ 2 ^ m := by
    rw [← hm, ← Subgroup.index]
    exact Subgroup.index_dvd_of_le hP'c
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidx
  have htr : ∀ q : Q, ∃ k : ℕ, (MonoidHom.transferCenterPow Q q) ^ 2 ^ k = 1 := by
    intro q
    have hq : (q : G) ∈ Subgroup.closure S := hQ q.2
    suffices h : ∀ (x : G) (hx : x ∈ Subgroup.closure S),
        ∃ k : ℕ, (MonoidHom.transferCenterPow Q ⟨x, hSQ hx⟩) ^ 2 ^ k = 1 from h q hq
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := hx.2
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have : (⟨x, hSQ (Subgroup.subset_closure hx)⟩ : Q) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hk)
      rw [this, map_one]
    | one => exact ⟨0, by rw [pow_zero, pow_one]; exact map_one (MonoidHom.transferCenterPow Q)⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨k, hk⟩ := ihx
      obtain ⟨l, hl⟩ := ihy
      refine ⟨k + l, ?_⟩
      have hxy : (⟨x * y, hSQ (Subgroup.mul_mem _ hx hy)⟩ : Q) =
          ⟨x, hSQ hx⟩ * ⟨y, hSQ hy⟩ := rfl
      set a := MonoidHom.transferCenterPow Q ⟨x, hSQ hx⟩ with ha
      set b := MonoidHom.transferCenterPow Q ⟨y, hSQ hy⟩ with hb
      have hc : Commute a b := Subtype.ext (mem_center_iff.mp b.2 (a : Q))
      rw [hxy, map_mul, ← ha, ← hb, hc.mul_pow, pow_add, pow_mul, hk, one_pow, one_mul,
        mul_comm (2 ^ k), pow_mul, hl, one_pow]
    | inv x hx ihx =>
      obtain ⟨k, hk⟩ := ihx
      refine ⟨k, ?_⟩
      have hxi : (⟨x⁻¹, hSQ (Subgroup.inv_mem _ hx)⟩ : Q) = (⟨x, hSQ hx⟩ : Q)⁻¹ := rfl
      rw [hxi, map_inv, inv_pow, hk, inv_one]
  rw [eq_bot_iff]
  intro p hp
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := htr ⟨p, hPQ hp⟩
  have h1 : p ^ (2 ^ j * 2 ^ k) = 1 := by
    have := congrArg (fun z : center Q => ((z : Q) : G)) hk
    simp only [SubgroupClass.coe_pow, MonoidHom.transferCenterPow_apply, OneMemClass.coe_one]
      at this
    rw [← hj, pow_mul]
    exact this
  obtain ⟨i, hi⟩ := hP ⟨p, hp⟩
  have h2 : p ^ 3 ^ i = 1 := by simpa using congrArg Subtype.val hi
  have hcop : Nat.Coprime (3 ^ i) (2 ^ j * 2 ^ k) := by
    rw [← pow_add]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have h3 := orderOf_dvd_of_pow_eq_one h1
  have h4 := orderOf_dvd_of_pow_eq_one h2
  have h5 : orderOf p = 1 := Nat.eq_one_of_dvd_coprimes hcop h4 h3
  exact orderOf_eq_one_iff.mp h5

theorem le_of_isSubnormal_of_fixedPointFree {G : Type*} [Group G] [Finite G] {D H W : Subgroup G}
    (hD : IsSubnormal D H) (hWH : W ≤ H) (hHW : H ≤ normalizer (W : Set G)) {x : G} (hxD : x ∈ D)
    (hfix : ∀ w ∈ W, x * w * x⁻¹ = w → w = 1) : W ≤ D := by
  have hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W := fun w hw =>
    (mem_normalizer_iff.mp (hHW (hD.le hxD)) w).mp hw
  have hcomm : W ≤ ⁅W, D⁆ := by
    let f : W → W := fun a => ⟨⁅(a : G), x⁆, by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact W.mul_mem a.2 (by simpa only [mul_assoc] using hxW _ (W.inv_mem a.2))⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h : (a : G) * x * (a : G)⁻¹ * x⁻¹ = (b : G) * x * (b : G)⁻¹ * x⁻¹ := by
        simpa only [f, commutatorElement_def] using congrArg Subtype.val hab
      have hu : (b : G)⁻¹ * a ∈ W := W.mul_mem (W.inv_mem b.2) a.2
      have h1 : x * (b : G)⁻¹ * x⁻¹ = (b : G)⁻¹ * a * (x * (a : G)⁻¹ * x⁻¹) := by
        calc x * (b : G)⁻¹ * x⁻¹ = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹ * x⁻¹) := by group
          _ = (b : G)⁻¹ * ((a : G) * x * (a : G)⁻¹ * x⁻¹) := by rw [h]
          _ = (b : G)⁻¹ * a * (x * (a : G)⁻¹ * x⁻¹) := by group
      have hfixed : x * ((b : G)⁻¹ * a) * x⁻¹ = (b : G)⁻¹ * a := by
        calc x * ((b : G)⁻¹ * a) * x⁻¹ = (x * (b : G)⁻¹ * x⁻¹) * (x * a * x⁻¹) := by group
          _ = (b : G)⁻¹ * a := by rw [h1]; group
      exact Subtype.ext (inv_mul_eq_one.mp (hfix _ hu hfixed)).symm
    intro w hw
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hf) ⟨w, hw⟩
    have : w = ⁅(a : G), x⁆ := (congrArg Subtype.val ha).symm
    rw [this]
    exact commutator_mem_commutator a.2 hxD
  have hiter : ∀ n : ℕ, W ≤ (fun X : Subgroup G => ⁅X, D⁆)^[n] W := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hcomm.trans (Subgroup.commutator_mono ih le_rfl)
  obtain ⟨d, hd⟩ := exists_iterate_commutator_le_of_isSubnormal hD hWH
  exact (hiter d).trans hd

end SolvNone

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
