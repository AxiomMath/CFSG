module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenStd
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSym

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput LieOrderFormulasInput)

@[expose] def ShapeTwoTenL44Excl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (z u : G) (h : Setting G L 10)
    (d : Cyc L Q z) (_ : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 10)) (x : G)
    (hx : x ∈ centralizer ({z} : Set G)), (permOf h d e hx).IsSwap → ¬ IsConj z (z * x) →
      ∀ hzx : z ∈ centralizer ({x} : Set G),
        ¬ L44Outcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)

@[expose] def ShapeTwoTenNoSwapPartnerNoCentralStdHS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (z u : G) (h : Setting G L 10)
    (d : Cyc L Q z) (_ : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 10)),
    (∀ (y : G) (hy : y ∈ centralizer ({z} : Set G)), (permOf h d e hy).IsSwap → ¬ IsConj z y) →
    (∀ (y : G) (hy : y ∈ centralizer ({z} : Set G)), (permOf h d e hy).IsSwap →
      ¬ centralizer ({y} : Set G) ≤ centralizer ({z} : Set G)) →
      ∃ K : Subgroup G, CFSG.EvenSporadicStandard.StdHyp G K ∧ IsSporadic (K ⧸ center K) .HS

@[expose] def ShapeTwoTenSwapPartnerStdHS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (z u : G) (h : Setting G L 10)
    (d : Cyc L Q z) (_ : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 10)),
    (∃ (y : G) (hy : y ∈ centralizer ({z} : Set G)), (permOf h d e hy).IsSwap ∧ IsConj z y) →
      ∃ K : Subgroup G, CFSG.EvenSporadicStandard.StdHyp G K ∧ IsSporadic (K ⧸ center K) .HS

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {z u : G}

theorem card_cycleType_eq_five_of_central (h : Setting G L 10) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 10))
    (hcen : (∀ τ : Perm (Fin 10), τ.IsSwap →
        centralizer ({(swapIota h d T e τ : G)} : Set G) ≤ centralizer ({z} : Set G)) ∨
      (∀ τ : Perm (Fin 10), τ.IsSwap →
        centralizer ({z * (swapIota h d T e τ : G)} : Set G) ≤ centralizer ({z} : Set G)))
    {b : G} (hb : b ∈ centralizer ({z} : Set G)) (hbz : IsConj z b)
    (hk2 : 2 ≤ Multiset.card (permOf h d e hb).cycleType) :
    Multiset.card (permOf h d e hb).cycleType = 5 := by
  classical
  obtain ⟨c, hc⟩ := isConj_iff.1 hbz
  have hbg : b = c⁻¹⁻¹ * z * c⁻¹ := by rw [inv_inv, ← hc]
  have haC : c⁻¹⁻¹ * z * c⁻¹ ∈ centralizer ({z} : Set G) := hbg ▸ hb
  have hσ : permOf h d e haC = permOf h d e hb := permOf_congr' hbg.symm haC hb h d e
  have hk2' : 2 ≤ Multiset.card (permOf h d e haC).cycleType := by rw [hσ]; exact hk2
  have hσ2 : permOf h d e haC * permOf h d e haC = 1 := by
    have hb2' : c⁻¹⁻¹ * z * c⁻¹ * (c⁻¹⁻¹ * z * c⁻¹) = 1 := by
      calc c⁻¹⁻¹ * z * c⁻¹ * (c⁻¹⁻¹ * z * c⁻¹) = c⁻¹⁻¹ * (z * z) * c⁻¹ := by group
        _ = 1 := by rw [d.mul_self]; group
    exact permOf_mul_self h d e haC hb2'
  obtain ⟨τ, hτ⟩ : ((permOf h d e haC).cycleFactorsFinset).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, cycleFactorsFinset_eq_empty_iff]
    intro h1
    rw [h1, cycleType_one] at hk2'
    simp at hk2'
  have hτsw : τ.IsSwap :=
    card_support_eq_two.1 (card_supp_eq_two_of_mem_cycleFactorsFinset hσ2 hτ)
  have hτσ : τ * permOf h d e haC = permOf h d e haC * τ := (self_mem_cycle_factors_commute hτ).eq
  have key : ∃ (y : G) (hy : y ∈ centralizer ({z} : Set G)), permOf h d e hy = τ ∧ y * y = 1 ∧
      centralizer ({y} : Set G) ≤ centralizer ({z} : Set G) := by
    have hιC := swapIota_mem_centralizer h d T e τ
    have hιπ : permOf h d e hιC = τ := permOf_swapIota h d T e τ
    obtain ⟨hι2, -, -⟩ := swap_elt_facts h d T e hιC (by rw [hιπ]; exact hτsw)
    rcases hcen with hU | hW
    · exact ⟨_, hιC, hιπ, hι2, hU τ hτsw⟩
    · have hzι : z * (swapIota h d T e τ : G) ∈ centralizer ({z} : Set G) :=
        mul_mem (mem_centralizer_singleton_iff.2 rfl) hιC
      refine ⟨_, hzι, ?_, ?_, hW τ hτsw⟩
      · rw [permOf_mul h d e (mem_centralizer_singleton_iff.2 rfl) hιC hzι, permOf_self, one_mul,
          hιπ]
      · have hιz : (swapIota h d T e τ : G) * z = z * (swapIota h d T e τ : G) :=
          mem_centralizer_singleton_iff.1 hιC
        calc z * (swapIota h d T e τ : G) * (z * (swapIota h d T e τ : G)) =
            z * ((swapIota h d T e τ : G) * z) * (swapIota h d T e τ : G) := by group
          _ = z * (z * (swapIota h d T e τ : G)) * (swapIota h d T e τ : G) := by rw [hιz]
          _ = (z * z) * ((swapIota h d T e τ : G) * (swapIota h d T e τ : G)) := by group
          _ = 1 := by rw [d.mul_self, hι2, one_mul]
  obtain ⟨y, hy, hyπ, hy2, hle⟩ := key
  have hya : y * (c⁻¹⁻¹ * z * c⁻¹) = (c⁻¹⁻¹ * z * c⁻¹) * y := by
    rw [comm_iff_permOf_comm h d T e hy haC, hyπ]
    exact hτσ
  rw [← hσ]
  exact partner_type_five h d T e haC hk2' hτ hy hyπ hya hy2 hle

theorem false_of_central_of_wreathOutcome (h : Setting G L 10) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 10))
    (hcen : (∀ τ : Perm (Fin 10), τ.IsSwap →
        centralizer ({(swapIota h d T e τ : G)} : Set G) ≤ centralizer ({z} : Set G)) ∨
      (∀ τ : Perm (Fin 10), τ.IsSwap →
        centralizer ({z * (swapIota h d T e τ : G)} : Set G) ≤ centralizer ({z} : Set G)))
    {x : G} (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf h d e hx).IsSwap)
    (hfus : ¬ IsConj z (z * x)) (hzx : z ∈ centralizer ({x} : Set G))
    (hW : WreathOutcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)
      (twoSecComp e x (fixFin (permOf h d e hx))) 8) : False := by
  classical
  obtain ⟨b, hb, hbz, -, hfix⟩ :=
    exists_partner_of_wreathOutcome h d T e (by norm_num) hx hτ hfus hzx hW
  have hb2 : b * b = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hbz
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [d.mul_self]; group
  have hπ2 := permOf_mul_self h d e hb hb2
  have hsupp := card_support_eq_two_mul_card_cycleType hπ2
  have hadd := card_fixFin_add_card_support (permOf h d e hb)
  have h5 := card_cycleType_eq_five_of_central h d T e hcen hb hbz (by omega)
  omega

section Lookup

theorem twoSec_cases_ten (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf h d e hx).IsSwap) (hfus : ¬ IsConj z (z * x))
    (hzx : z ∈ centralizer ({x} : Set G)) :
    centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) ∨
      WreathOutcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)
        (twoSecComp e x (fixFin (permOf h d e hx))) 8 ∨
      SymOutcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) 8 ∨
      HSOutcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) ∨
      L44Outcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) := by
  obtain ⟨hx2, -, hx1⟩ := swap_elt_facts h d T e hx hτ
  have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hE : ExactShape (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)
      (twoSecComp e x (fixFin (permOf h d e hx))) 8 :=
    exactShape_twoSec h d T e (by norm_num) hx hτ hfus hzx
  have hO' := oddCore_twoSec_eq_bot h hxord
  rcases section_dichotomy hO' hE (by norm_num) with h1 | h1 | h1
  · exact Or.inl (centralizer_le_of_mem_center hx2 hfus hzx h1)
  · exact Or.inr (Or.inl h1)
  · rcases exactShape_almostSimple_eight hGLS hO (isKGroupCat_twoSec h hx1) hO' hE h1 with
      h2 | h2 | h2
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h2)))

theorem shapeTwoTenStdHS_of_parts'
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hL44 : ShapeTwoTenL44Excl) (hRes : ShapeTwoTenNoSwapPartnerNoCentralStdHS)
    (hNE : ShapeTwoTenSwapPartnerStdHS) : ShapeTwoTenStdHS := by
  classical
  intro G _ _ L Q z u h d T
  obtain ⟨e⟩ := h.iso
  by_cases hP : ∃ (y : G) (hy : y ∈ centralizer ({z} : Set G)), (permOf h d e hy).IsSwap ∧
      IsConj z y
  · exact hNE G L Q z u h d T e hP
  have hP' : ∀ (y : G) (hy : y ∈ centralizer ({z} : Set G)), (permOf h d e hy).IsSwap →
      ¬ IsConj z y := fun y hy hsw hc => hP ⟨y, hy, hsw, hc⟩
  by_cases hC : ∃ (y : G) (hy : y ∈ centralizer ({z} : Set G)), (permOf h d e hy).IsSwap ∧
      centralizer ({y} : Set G) ≤ centralizer ({z} : Set G)
  swap
  · exact hRes G L Q z u h d T e hP' fun y hy hsw hle => hC ⟨y, hy, hsw, hle⟩
  obtain ⟨y, hy, hysw, hle⟩ := hC
  have hz2 : z * z = 1 := d.mul_self
  set τ := permOf h d e hy with hτdef
  set x₁ : G := (swapIota h d T e τ : G) with hx₁
  have hx₁C : x₁ ∈ centralizer ({z} : Set G) := swapIota_mem_centralizer h d T e τ
  have hx₁π : permOf h d e hx₁C = τ := permOf_swapIota h d T e τ
  have hx₂C : z * x₁ ∈ centralizer ({z} : Set G) :=
    mul_mem (mem_centralizer_singleton_iff.2 rfl) hx₁C
  have hx₂π : permOf h d e hx₂C = τ := by
    rw [permOf_mul h d e (mem_centralizer_singleton_iff.2 rfl) hx₁C hx₂C, permOf_self, one_mul,
      hx₁π]
  have hz₁ : z ∈ centralizer ({x₁} : Set G) := by
    rw [mem_centralizer_singleton_iff]; exact (mem_centralizer_singleton_iff.1 hx₁C).symm
  have hz₂ : z ∈ centralizer ({z * x₁} : Set G) := by
    rw [mem_centralizer_singleton_iff]; exact (mem_centralizer_singleton_iff.1 hx₂C).symm
  have hfus₁ : ¬ IsConj z (z * x₁) := hP' _ hx₂C (by rw [hx₂π]; exact hysw)
  have hfus₂ : ¬ IsConj z (z * (z * x₁)) := by
    rw [← mul_assoc, hz2, one_mul]
    exact hP' _ hx₁C (by rw [hx₁π]; exact hysw)
  have key : ∀ (x : G) (hxC : x ∈ centralizer ({z} : Set G)), permOf h d e hxC = τ →
      ¬ IsConj z (z * x) → ∀ hzx : z ∈ centralizer ({x} : Set G),
      ((∀ σ : Perm (Fin 10), σ.IsSwap →
          centralizer ({(swapIota h d T e σ : G)} : Set G) ≤ centralizer ({z} : Set G)) ∨
        (∀ σ : Perm (Fin 10), σ.IsSwap →
          centralizer ({z * (swapIota h d T e σ : G)} : Set G) ≤ centralizer ({z} : Set G))) →
      (centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) → False) →
      ∃ K : Subgroup G, CFSG.EvenSporadicStandard.StdHyp G K ∧ IsSporadic (K ⧸ center K) .HS := by
    intro x hxC hxπ hfus hzx hcen hcx
    rcases twoSec_cases_ten hGLS hO h d T e hxC (by rw [hxπ]; exact hysw) hfus hzx with
      h1 | h1 | h1 | h1 | h1
    · exact (hcx h1).elim
    · exact (false_of_central_of_wreathOutcome h d T e hcen hxC (by rw [hxπ]; exact hysw) hfus
        hzx h1).elim
    · obtain ⟨b, hb, hbz, hb2⟩ := exists_double_partner_of_symOutcome h d T e hP' hxC
        (by rw [hxπ]; exact hysw) hfus hzx h1
      exact (false_of_double_partner h d T e hcen hb hbz hb2).elim
    · exact exists_stdHyp_of_hsOutcome h (orderOf_eq_prime (by
        rw [pow_two]; exact (swap_elt_facts h d T e hxC (by rw [hxπ]; exact hysw)).1)
        (swap_elt_facts h d T e hxC (by rw [hxπ]; exact hysw)).2.2) h1
    · exact (hL44 G L Q z u h d T e x hxC (by rw [hxπ]; exact hysw) hfus hzx h1).elim
  have hτsw : τ.IsSwap := hysw
  rcases eq_swapIota_or h d T e hy with hy1 | hy1
  ·
    have hU : ∀ σ : Perm (Fin 10), σ.IsSwap →
        centralizer ({(swapIota h d T e σ : G)} : Set G) ≤ centralizer ({z} : Set G) := by
      intro σ hσ
      refine centralizer_le_untwisted h d T e hτsw ?_ hσ
      rw [← hy1]; exact hle
    refine key (z * x₁) hx₂C hx₂π hfus₂ hz₂ (Or.inl hU) fun hc₂ => ?_
    refine false_of_centralizer_swap_le h d T e fun w hw hwsw => ?_
    rcases eq_swapIota_or h d T e hw with hw1 | hw1
    · rw [hw1]; exact hU _ hwsw
    · rw [hw1]; exact centralizer_le_twisted h d T e hτsw hc₂ hwsw
  ·
    have hW : ∀ σ : Perm (Fin 10), σ.IsSwap →
        centralizer ({z * (swapIota h d T e σ : G)} : Set G) ≤ centralizer ({z} : Set G) := by
      intro σ hσ
      refine centralizer_le_twisted h d T e hτsw ?_ hσ
      rw [← hy1]; exact hle
    refine key x₁ hx₁C hx₁π hfus₁ hz₁ (Or.inr hW) fun hc₁ => ?_
    refine false_of_centralizer_swap_le h d T e fun w hw hwsw => ?_
    rcases eq_swapIota_or h d T e hw with hw1 | hw1
    · rw [hw1]; exact centralizer_le_untwisted h d T e hτsw hc₁ hwsw
    · rw [hw1]; exact hW _ hwsw

end Lookup

end CFSG.OddStandard.AltStdSec
