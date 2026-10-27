module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Main

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem eq_one_of_two_power_of_odd_orderOf {x : G} (h2 : ∃ n : ℕ, orderOf x = 2 ^ n)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨n, hn⟩ := h2
  rcases n with _ | n
  · exact orderOf_eq_one_iff.mp (by rw [hn]; norm_num)
  · exfalso
    rw [hn] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero n⟩)

end Generic

namespace IsSetting25

variable {G : Type} [Group G] [Finite G] {A R X O : Subgroup G} {t : G}
  (S : IsSetting25 A R t X O)

include S

theorem mem_O_of_odd {y : G}
    (hy : y ∈ centralizer ((R ⊔ zpowers t : Subgroup G) : Set G)) (hodd : Odd (orderOf y)) :
    y ∈ O := by
  rw [← S.O_sup] at hy
  obtain ⟨o, ho, e, he, rfl⟩ := mem_sup_of_forall_comm (fun o ho _ he => S.O_comm ho he) hy
  have hcomm : Commute o e := S.O_comm ho he
  have h1 : o ^ (orderOf (o * e)) * e ^ (orderOf (o * e)) = 1 := by
    rw [← hcomm.mul_pow]
    exact pow_orderOf_eq_one _
  have h2 : e ^ (orderOf (o * e)) = 1 := by
    have hO : e ^ (orderOf (o * e)) ∈ O := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ ho _)
    have hE : e ^ (orderOf (o * e)) ∈ (R ⊔ zpowers t : Subgroup G) := Subgroup.pow_mem _ he _
    exact Subgroup.disjoint_def.mp S.disjoint_O_E hO hE
  have he1 : e = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp S.isPGroup_E ⟨e, he⟩
    rw [Subgroup.orderOf_mk] at hn
    have hdvd : orderOf e ∣ orderOf (o * e) := orderOf_dvd_of_pow_eq_one h2
    exact eq_one_of_two_power_of_odd_orderOf ⟨n, hn⟩ (hodd.of_dvd_nat hdvd)
  rw [he1, mul_one]
  exact ho

end IsSetting25

section OddCore

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G}

structure CaseB.OddCoreData (c : CaseB A R t) (O₁ : Subgroup G) : Prop where
  le_centralizer : O₁ ≤ centralizer (c.W : Set G)
  odd : Odd (Nat.card O₁)
  of_odd : ∀ x ∈ centralizer (c.W : Set G), Odd (orderOf x) → x ∈ O₁
  decomp : ∀ k ∈ centralizer (c.W : Set G), ∃ w ∈ c.W, ∃ o ∈ O₁, k = w * o

theorem CaseB.Factors.exists_oddCoreData {c : CaseB A R t} {M₁ M₂ : Subgroup G}
    (F : c.Factors M₁ M₂) : ∃ O₁ : Subgroup G, CaseB.OddCoreData c O₁ := by
  obtain ⟨O₁, h1, h2, -, h4, -, h6⟩ := F.exists_O₁
  exact ⟨O₁, ⟨h1, h2, h6, h4⟩⟩

namespace CaseB.OddCoreData

variable {c : CaseB A R t} {O₁ : Subgroup G} (hO : CaseB.OddCoreData c O₁)

include hO

theorem odd_orderOf {x : G} (hx : x ∈ O₁) : Odd (orderOf x) :=
  hO.odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O₁ hx)

theorem odd_card_inf : Odd (Nat.card ↥(O₁ ⊓ c.Ninf)) :=
  hO.odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem conj_mem {x : G} (hx : x ∈ c.N) {q : G} (hq : q ∈ O₁ ⊓ c.Ninf) :
    x * q * x⁻¹ ∈ O₁ ⊓ c.Ninf := by
  obtain ⟨hqO, hqN⟩ := mem_inf.mp hq
  refine mem_inf.mpr ⟨?_, prOf_conj_mem c.N hx hqN⟩
  have hqK : q ∈ centralizer (c.W : Set G) := hO.le_centralizer hqO
  have hxK : x * q * x⁻¹ ∈ centralizer (c.W : Set G) :=
    (mem_set_normalizer_iff.mp (normalizer_le_normalizer_centralizer_W c.W hx) q).mp hqK
  refine hO.of_odd _ hxK ?_
  rw [← (SemiconjBy.conj_mk x q).orderOf_eq]
  exact hO.odd_orderOf hqO

theorem le_inf_of_odd_normal (hW : c.W ≤ c.Ninf) {Q' : Subgroup G} (hQ'N : Q' ≤ c.Ninf)
    (hQ'n : ∀ n ∈ c.Ninf, ∀ q ∈ Q', n * q * n⁻¹ ∈ Q') (hQ'odd : Odd (Nat.card Q')) :
    Q' ≤ O₁ ⊓ c.Ninf := by
  have hWp : IsPGroup 2 c.W := IsPGroup.of_card (n := 8) c.W_card
  intro q hq
  refine mem_inf.mpr ⟨?_, hQ'N hq⟩
  refine hO.of_odd q ?_ (hQ'odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Q' hq))
  rw [mem_centralizer_iff]
  intro w hw
  have hqN : q ∈ c.N := prOf_le c.N (hQ'N hq)
  have hwq : w * q⁻¹ * w⁻¹ ∈ Q' := hQ'n w (hW hw) q⁻¹ (Q'.inv_mem hq)
  have hqw : q * w * q⁻¹ ∈ c.W := (mem_set_normalizer_iff.mp hqN w).mp hw
  have hxW : q * w * q⁻¹ * w⁻¹ ∈ c.W := c.W.mul_mem hqw (c.W.inv_mem hw)
  have hxQ : q * w * q⁻¹ * w⁻¹ ∈ Q' := by
    have := Q'.mul_mem hq hwq
    simpa [mul_assoc] using this
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hWp ⟨_, hxW⟩
  rw [Subgroup.orderOf_mk] at hn
  have hx1 : q * w * q⁻¹ * w⁻¹ = 1 :=
    eq_one_of_two_power_of_odd_orderOf ⟨n, hn⟩
      (hQ'odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Q' hxQ))
  calc w * q = (q * w * q⁻¹ * w⁻¹) * (w * q) := by rw [hx1, one_mul]
    _ = q * w := by group

theorem mem_centralizer_A_of_comm_t {y : G} (hy : y ∈ O₁) (hyt : y * t = t * y) :
    y ∈ centralizer (A : Set G) := by
  have hyK : y ∈ centralizer (c.W : Set G) := hO.le_centralizer hy
  have hle : (R ⊔ zpowers t : Subgroup G) ≤ centralizer ({y} : Set G) := by
    refine sup_le (fun r hr => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hyK r (c.R_le_W hr)
    · rw [mem_centralizer_singleton_iff]
      exact hyt.symm
  have hyE : y ∈ centralizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    exact mem_centralizer_singleton_iff.mp (hle he)
  exact c.H.sit.S.O_le_centralizer_A c.H.sit.F (c.H.sit.S.mem_O_of_odd hyE (hO.odd_orderOf hy))

end CaseB.OddCoreData

end OddCore

end CFSG.OddStandard.Seitz77
