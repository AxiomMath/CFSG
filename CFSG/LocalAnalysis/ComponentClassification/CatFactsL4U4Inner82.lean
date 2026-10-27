module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inner82A
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OutU

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Inner82

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def DiagCase : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSimpleGroup ↥(generalizedFitting H) →
    centralizer (generalizedFitting H : Set H) = ⊥ →
    ((Blueprint.LieModel ↥(generalizedFitting H) .PSL 4 p f ∧ p ^ f % 4 = 1) ∨
      (Blueprint.LieModel ↥(generalizedFitting H) .PSU 4 p f ∧ p ^ f % 4 = 3)) →
    ∀ α β ξ : H, α * α = 1 → α = ⁅β, ξ⁆ →
    ∀ J₁ : Subgroup H, J₁ ≤ centralizer ({α} : Set H) →
      IsPComponent 2 (J₁.subgroupOf (centralizer ({α} : Set H))) →
      IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f →
      β ∈ coreActionKernel J₁ → ξ ∈ coreActionKernel J₁ → False

theorem center_eq_bot {H : Type} [Group H] {L : Subgroup H} [hs : IsSimpleGroup ↥L]
    (hC : centralizer (L : Set H) = ⊥) : center ↥L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥L) with h | h
  · exact h
  · exfalso
    have hL : L = ⊥ := by
      rw [eq_bot_iff, ← hC]
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      have hy' : (⟨y, hy⟩ : L) ∈ center ↥L := by rw [h]; exact mem_top _
      exact (congrArg Subtype.val (mem_center_iff.mp hy' ⟨x, hx⟩)).symm
    have : Nontrivial ↥L := hs.toNontrivial
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_pair_ne ↥L
    rw [hL, mem_bot] at ha hb
    exact hab (Subtype.ext (ha.trans hb.symm))

end Inner82

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank Inner82
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem cf82Inner_of_diagCase (hD : DiagCase) : CF82Inner := by
  intro H _ _ p f hp hp2 hf hsimp hC htype α β ξ hαα hαc J₁ hJC hcomp hJtype hβ hξ
  classical
  set L := generalizedFitting H with hLdef
  have : L.Normal := LocalCores.generalized_fitting_characteristic.2
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by obtain ⟨t, ht⟩ := hq; omega
  have hDcall := fun hcase => @hD H _ _ p f hp hp2 hf hsimp hC hcase α β ξ hαα hαc J₁ hJC hcomp
    hJtype hβ hξ
  have hout : ∀ u v : MulAut L, ⁅u, v⁆ ∈ (MulAut.conj : L →* MulAut L).range := by
    rcases htype with hL | hU | hA
    · rcases hq4 with h1 | h3
      · exact (hDcall (Or.inl ⟨hL, h1⟩)).elim
      obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
      let : Fintype F := Fintype.ofFinite F
      have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
      set e' : ↥L ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F :=
        eL.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
          (QuotientGroup.quotientMulEquivOfEq
            (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 F).symm))
      exact fun u v => commutator_mem_range_conj_of_mulEquiv e'
        (fun u v => LinearOut.out_comm_projectiveSL_four (by rw [hFq]; exact h3) u v) u v
    · rcases hq4 with h1 | h3
      swap
      · exact (hDcall (Or.inr ⟨hU, h3⟩)).elim
      obtain ⟨-, K', _, _, hK', ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
      have hUF : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K' :=
        ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
      exact fun u v => commutator_mem_range_conj_of_mulEquiv eU
        (fun u v => UnitaryOut.out_comm_statedSU_four hUF hp2 h1 u v) u v
    · obtain ⟨eA⟩ := hA
      exact fun u v => commutator_mem_range_conj_of_mulEquiv eA
        AZ.out_comm_alternatingGroup_ten u v
  have hperf : ∀ J : Subgroup H, ⁅J, J⁆ = J → J ≤ L := fun J hJ => AZ.le_of_perfect L hC hout hJ
  have hαL : α ∈ L := by
    rw [hαc]
    exact AZ.commutator_le_of_out_comm L hC hout
      (commutator_mem_commutator (mem_top β) (mem_top ξ))
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact false_of_isPComponent_one hp hp2 hf htype hperf hJC hcomp hJtype
  have hJp : ⁅J₁, J₁⁆ = J₁ := commutator_eq_self_of_isPComponent hJC hcomp
  have hJL := hperf J₁ hJp
  obtain ⟨s, hs, hs2, hsq, hsJ⟩ := AZ.exists_prime_dvd_card_of_isSec8JType hp hp2 hf hJtype
  have hsJ₁ : s ∣ Nat.card J₁ := hsJ.trans (Subgroup.card_quotient_dvd_card _)
  have := Fact.mk hs
  obtain ⟨⟨y, hy⟩, hys⟩ := exists_prime_orderOf_dvd_card' (G := J₁) s hsJ₁
  rw [Subgroup.orderOf_mk] at hys
  have hZ : center ↥L = ⊥ := center_eq_bot hC
  have hZ2 : IsPGroup 2 (center ↥L) := by
    rw [hZ]
    exact IsPGroup.of_card (n := 0) (by rw [card_bot, pow_zero])
  set ℓ : ↥L := ⟨α, hαL⟩ with hℓdef
  set y' : ↥L := ⟨y, hJL hy⟩ with hy'def
  have hℓZ : ℓ ∉ center ↥L := by
    rw [hZ, mem_bot]
    intro h1
    exact hα1 (congrArg Subtype.val h1)
  have hℓ2 : ℓ ^ 2 ∈ center ↥L := by
    rw [hZ, mem_bot, sq]
    exact Subtype.ext hαα
  have hy's : orderOf y' = s := by rw [hy'def, Subgroup.orderOf_mk, hys]
  have hyℓ : y' * ℓ = ℓ * y' :=
    Subtype.ext (mem_centralizer_singleton_iff.mp (hJC hy))
  set eZ : ↥L ⧸ center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot with heZ
  refine ⟨hαL, fun hL => ?_, fun hU => ?_⟩
  · obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
    let : Fintype F := Fintype.ofFinite F
    have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
    have := card_mod_four_of_inner_L4 hZ2 (hFq ▸ hq) (eZ.trans eL) hℓZ hℓ2 hs hs2
      (by rw [hFq]; exact hsq) hy's hyℓ
    rwa [hFq] at this
  · obtain ⟨-, K', _, _, hK', ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
    have hUF : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K' :=
      ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
    exact card_mod_four_of_inner_U4 hUF hZ2 hp2 (eZ.trans eU) hℓZ hℓ2 hs hs2 hsq hy's hyℓ

end CFSG.ComponentClassification.CatFactsL4U4
