module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Open.FusionDefs
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Subgroup CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section OddCore

variable {G : Type} [Group G] [Finite G] (S : Subgroup G) [S.Normal]

theorem fusionOddCore_eq_bot [IsSimpleGroup ↥S] (hna : ∃ a b : ↥S, a * b ≠ b * a)
    (hc : centralizer (S : Set G) = ⊥) : fusionOddCore G = ⊥ := by
  refine le_bot_iff.mp (sSup_le fun N hN => ?_)
  obtain ⟨hNn, hNodd⟩ := hN
  by_cases hSN : S ≤ N
  · exfalso
    have hodd : Odd (Nat.card ↥S) := Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hSN)
    obtain ⟨a, b, hab⟩ := hna
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd) a b)
  · have hbot : N ⊓ S = ⊥ := by
      haveI : (N.subgroupOf S).Normal := Subgroup.Normal.comap hNn S.subtype
      rcases Subgroup.Normal.eq_bot_or_eq_top (N.subgroupOf S) with h | h
      · rw [← disjoint_iff]
        exact Subgroup.subgroupOf_eq_bot.mp h
      · exact absurd (Subgroup.subgroupOf_eq_top.mp h) hSN
    have hcomm : ∀ n ∈ N, ∀ s ∈ S, s * n = n * s := by
      intro n hn s hs
      have h1 : n * s * n⁻¹ * s⁻¹ ∈ N ⊓ S := by
        refine ⟨?_, ?_⟩
        · have := N.mul_mem hn (hNn.conj_mem n⁻¹ (N.inv_mem hn) s)
          simpa [mul_assoc] using this
        · have := S.mul_mem (‹S.Normal›.conj_mem s hs n) (S.inv_mem hs)
          simpa [mul_assoc] using this
      rw [hbot, Subgroup.mem_bot] at h1
      calc s * n = (n * s * n⁻¹ * s⁻¹)⁻¹ * (n * s) := by group
        _ = n * s := by rw [h1, inv_one, one_mul]
    intro x hx
    have hxc : x ∈ centralizer (S : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun s hs => hcomm x hx s hs
    rw [hc] at hxc
    exact hxc

end OddCore

section Sigma

variable {G : Type} [Group G] {S : Subgroup G} [S.Normal]

theorem conjNormal_injective (hc : centralizer (S : Set G) = ⊥) :
    Function.Injective (MulAut.conjNormal : G →* MulAut ↥S) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := congrArg (fun φ : MulAut ↥S => ((φ ⟨s, hs⟩ : ↥S) : G)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mk] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rw [hc, Subgroup.mem_bot] at hmem
  exact hmem

theorem conjNormal_mem_range_iff (hc : centralizer (S : Set G) = ⊥) (g : G) :
    (MulAut.conjNormal g : MulAut ↥S) ∈ (MulAut.conj : ↥S →* MulAut ↥S).range ↔ g ∈ S := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp h
    have h2 : (MulAut.conjNormal g : MulAut ↥S) = MulAut.conjNormal (s : G) := by
      rw [MulAut.conjNormal_val]
      exact hs.symm
    rw [conjNormal_injective hc h2]
    exact s.2
  · intro hg
    exact MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, (MulAut.conjNormal_val (h := ⟨g, hg⟩)).symm⟩

theorem orderOf_conjNormal (hc : centralizer (S : Set G) = ⊥) {t : G} (ht : orderOf t = 2) :
    orderOf (MulAut.conjNormal t : MulAut ↥S) = 2 := by
  rw [orderOf_injective (MulAut.conjNormal : G →* MulAut ↥S) (conjNormal_injective hc) t, ht]

theorem mem_fixedSubgroup_conjNormal_iff (t : G) (s : ↥S) :
    s ∈ fixedSubgroup (MulAut.conjNormal t : MulAut ↥S) ↔
      (s : G) ∈ centralizer ({t} : Set G) := by
  show (MulAut.conjNormal t : MulAut ↥S) s = s ↔ _
  rw [Subtype.ext_iff, MulAut.conjNormal_apply, Subgroup.mem_centralizer_singleton_iff,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

end Sigma

@[expose] def OuterKlein {S : Type} [Group S] (σ : MulAut S) : Prop :=
  ∃ α β : MulAut S, α * σ = σ * α ∧ β * σ = σ * β ∧
    α * α ∈ (MulAut.conj : S →* MulAut S).range ∧ β * β ∈ (MulAut.conj : S →* MulAut S).range ∧
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : S →* MulAut S).range ∧
    α ∉ (MulAut.conj : S →* MulAut S).range ∧ β ∉ (MulAut.conj : S →* MulAut S).range ∧
    α * β ∉ (MulAut.conj : S →* MulAut S).range

theorem exists_three_of_index_gt_two {C : Type*} [Group C] [Finite C] (K : Subgroup C) [K.Normal]
    (h : 2 < K.index) : ∃ c₁ c₂ : C, c₁ ∉ K ∧ c₂ ∉ K ∧ c₁ * c₂ ∉ K := by
  by_contra hno
  push Not at hno
  have hK1 : K ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at h
    omega
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : C, c₁ ∉ K := by
    by_contra hall
    push Not at hall
    exact hK1 (Subgroup.eq_top_iff' K |>.mpr hall)
  let g : Bool → C ⧸ K := fun b => bif b then 1 else ((c₁⁻¹ : C) : C ⧸ K)
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨c₂, rfl⟩ := QuotientGroup.mk_surjective q
    by_cases h2 : c₂ ∈ K
    · refine ⟨true, ?_⟩
      show (1 : C ⧸ K) = (c₂ : C ⧸ K)
      exact ((QuotientGroup.eq_one_iff c₂).mpr h2).symm
    · refine ⟨false, ?_⟩
      have h12 : c₁ * c₂ ∈ K := hno c₁ c₂ hc₁ h2
      show ((c₁⁻¹ : C) : C ⧸ K) = (c₂ : C ⧸ K)
      rw [QuotientGroup.eq]
      simpa using h12
  have hle := Nat.card_le_card_of_surjective g hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hle
  have hidx : K.index = Nat.card (C ⧸ K) := Subgroup.index_eq_card K
  omega

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
