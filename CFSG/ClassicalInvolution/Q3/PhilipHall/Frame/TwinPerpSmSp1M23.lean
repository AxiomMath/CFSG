module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSp1Base
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafM23Transport

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

set_option linter.unusedSectionVars false


theorem center_genFittingFStar_eq_bot {Y : Type} [Group Y] [IsSimpleGroup ↥(genFittingFStar Y)]
    (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) :
    Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(genFittingFStar Y)) with
    h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a)

theorem leaf_m23 {n : ℕ} :
    NoTwinS n (fun F _ => CFSG.Blueprint.NativeSporadic.IsSporadic F .M23) := by
  intro Y _ _ R S t h _ hF
  haveI := h.core.simple
  haveI hNn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  obtain ⟨ψ₀⟩ := hF
  have ψ : ↥(genFittingFStar Y) ≃* ↥CFSG.Blueprint.NativeSporadic.M23 := ψ₀
  have ht : orderOf t = 2 := h.core.datum.order
  have hodd : CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    CFSG.Sporadic.Schreier.oddCore_centralizer_eq_bot_of_normal
      CFSG.Sporadic.Schreier.m23_inner_oddCore
      (CFSG.Sporadic.Schreier.m23_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num)))
      CFSG.Sporadic.Schreier.m23_outer_oddCore (genFittingFStar Y) ψ hC t ht
  have hK2 : IsPGroup 2 ↥(tightCore R) := isPGroup_core_of_oddCore h hodd
  have hinn : CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(genFittingFStar Y) = ⊤ := by
    refine CFSG.Sporadic.Schreier.inner_eq_top_of_card_le
      (center_genFittingFStar_eq_bot h.core.nonab) ?_
    rw [Nat.card_congr (MulAut.congr ψ).toEquiv, Nat.card_congr ψ.toEquiv]
    exact CFSG.Sporadic.Schreier.m23_mulAut_card
  have hNtop : genFittingFStar Y = ⊤ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.eq_top_of_inner_eq_top hC hinn
  obtain ⟨g, hgc, hne, -, -⟩ := exists_twin h
  obtain ⟨-, -, h32⟩ := thirtytwo_le_card_oTwoPrimeTwo h hK2 hgc hne
  have hD2 : IsPGroup 2 ↥(oTwoPrimeTwo (Subgroup.centralizer ({t} : Set Y))) :=
    isPGroup_oTwoPrimeTwo (oTwoPrime_eq_bot hodd)
  have htN : t ∈ genFittingFStar Y := by
    rw [hNtop]
    exact Subgroup.mem_top t
  obtain ⟨hperf, hcard⟩ :=
    m23_centralizer_perfect_card (genFittingFStar Y) (MulEquiv.refl _) ψ htN ht
  set H := Subgroup.centralizer ({t} : Set Y) with hH
  set C := genFittingFStar Y ⊓ H with hCdef
  have hDC : oTwoPrimeTwo H ≤ C := by
    refine le_inf ?_ (oTwoPrimeTwo_le H)
    rw [hNtop]
    exact le_top
  haveI : ((oTwoPrimeTwo H).subgroupOf C).Normal :=
    ⟨fun x hx c => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simpa using conj_mem_oTwoPrimeTwo (Subgroup.mem_inf.1 c.2).2 hx⟩
  haveI := hperf
  let e := Subgroup.subgroupOfEquivOfLe hDC
  exact perfect_card_2688_false hcard ((oTwoPrimeTwo H).subgroupOf C) (hD2.of_equiv e.symm)
    (by rw [Nat.card_congr e.toEquiv]; exact thirtytwo_dvd_card hD2 h32)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1
