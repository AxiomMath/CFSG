module

public import CFSG.Goldschmidt.Steps.Sec82a
import CFSG.Goldschmidt.Steps.Sec82Tools
import CFSG.Goldschmidt.Steps.Sec82b
import CFSG.Goldschmidt.Steps.Sec82c
import CFSG.Goldschmidt.Steps.Sec82f
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.G36Setup
import CFSG.Walter.Bender1970.S4.Rank
import CFSG.Walter.Bender1970.S38.JR

public section

namespace CFSG.Goldschmidt.Sec82

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G} {a : G}
  {H : Subgroup G} {p : ℕ} {M L : Subgroup G}

theorem odd_card_fittingSubgroupOf {M : Subgroup G} (hO2 : qCoreOf M 2 = ⊥) :
    Odd (Nat.card (CFSG.fittingSubgroupOf M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (CFSG.fittingSubgroupOf M) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.fittingSubgroupOf M) 2 h2
  have hx2 : IsPGroup 2 (Subgroup.zpowers (x : G)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one])
  have hxO := Walter.le_qCoreOf_of_le_fittingSubgroupOf Nat.prime_two
    (Subgroup.zpowers_le.mpr x.2) hx2 (Subgroup.mem_zpowers _)
  rw [hO2, Subgroup.mem_bot] at hxO
  have hx1 : x = 1 := Subtype.ext hxO
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem false_of_ctx (h31 : S_G31) (h35 : S_G35) (hE : componentLayerOf H = ⊥)
    (hO2 : qCoreOf M 2 = ⊥) (hcyc : ∀ q : ℕ, q.Prime → q ≠ 2 → IsCyclic (qCoreOf M q))
    (c : Ctx S A a H p M L) : False := by
  have hNM := normalizer_le h31 c
  have hEM := componentLayerOf_eq hE c
  have hFodd := odd_card_fittingSubgroupOf hO2
  have hFL := fittingSubgroupOf_le_centralizer c
  have hSF : ∀ s ∈ (S : Subgroup G),
      CFSG.fittingSubgroupOf M ≤ Subgroup.centralizer ({s} : Set G) := by
    intro s hs
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hsN : s ∈ Subgroup.normalizer (A : Set G) := Sec8.le_normalizer c.hset hs
    rw [(show CFSG.fittingSubgroupOf M = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf M)]
    refine iSup_le fun r => ?_
    have hr : r.1.1.Prime := Nat.prime_of_mem_primeFactors r.1.2
    by_cases hr2 : r.1.1 = 2
    · rw [hr2, hO2]
      exact bot_le
    · have hsC := mem_centralizer_of_noIndexTwo (fun Y hY => c.hset.noIndexTwo Y hY)
        (hcyc _ hr hr2) (hNM.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in M r.1.1)))
        hsN hk'
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hsC x hx)
  have hSL : (S : Subgroup G) ≤ L := by
    intro s hs
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨l, hl, y, hy, hly⟩ := exists_mul_eq_of_mem_centralizer h31 h35 c
      (Sec8.le_centralizer c.hset c.h4 hs) hk'
    subst hly
    have hyF : CFSG.fittingSubgroupOf M ≤ Subgroup.centralizer ({y} : Set G) := by
      intro f hf
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hSF _ hs hf)
      have h2 : l * f = f * l := Subgroup.mem_centralizer_iff.mp (hFL hf) l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc f * y = l⁻¹ * (l * f) * y := by group
        _ = l⁻¹ * (f * l) * y := by rw [h2]
        _ = l⁻¹ * (f * (l * y)) := by group
        _ = l⁻¹ * (l * y * f) := by rw [h1]
        _ = y * f := by group
    have hyL : L ≤ Subgroup.centralizer ({y} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hy.2 x hx)
    have hFs : generalizedFittingSubgroupOf M = CFSG.fittingSubgroupOf M ⊔ L := by
      rw [generalizedFittingSubgroupOf, hEM]
      rfl
    have hyC : y ∈ Subgroup.centralizer (generalizedFittingSubgroupOf M : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      rw [hFs] at hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (sup_le hyF hyL hx)
    have hyFs : y ∈ generalizedFittingSubgroupOf M :=
      Walter.inf_centralizer_generalizedFitting_le M ⟨hy.1, hyC⟩
    have hly : l * y ∈ L ⊔ CFSG.fittingSubgroupOf M := by
      rw [sup_comm, ← hFs]
      exact Subgroup.mul_mem _ (hFs ▸ Subgroup.mem_sup_right hl) hyFs
    exact mem_of_mem_sup_of_odd hFodd (fun l' hl' o ho =>
      Subgroup.mem_centralizer_iff.mp (hFL ho) l' hl') hly hk'
  have h4 := card_le_four h31 c hSL S.isPGroup'
  obtain ⟨B, -, hB, hB8⟩ := c.hset.rank
  have hBp : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa using hB.2 x x.2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hBP⟩ := hBp.exists_le_sylow
  have hPS : Nat.card (P : Subgroup G) = Nat.card (S : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have := Subgroup.card_le_of_le hBP
  omega

end CFSG.Goldschmidt.Sec82
