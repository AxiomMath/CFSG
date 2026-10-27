module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208P2
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208Sp

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4

theorem layer_eq_top_of_isQuasisimple' {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.layer Q = ⊤ :=
  CFSG.WholeGroup.layer_eq_top_of_isQuasisimple h

section Cen

variable {G : Type} [Group G] [Finite G] {z : G}

theorem twoElt_comm_oddCore (h4a : Thm4a (Cen z)) (hq : CFSG.IsQuasisimple (CentralizerBar z))
    {x : G} (hx : x ∈ Cen z) {k : ℕ} (hk : x ^ (2 ^ k) = 1) :
    ∀ a ∈ OddCore z, x * a = a * x := by
  have h1 : (layer ↥(Cen z)).map (toBar z) = layer (CentralizerBar z) := L208Key.map_layer_toBar h4a
  have h2 : layer (CentralizerBar z) = ⊤ := layer_eq_top_of_isQuasisimple' hq
  have hch : (layer ↥(Cen z)).Characteristic := CFSG.LocalCores.layer_characteristic
  have : (layer ↥(Cen z)).Normal := inferInstance
  have hx2 : ∃ a : ℕ, orderOf (⟨x, hx⟩ : ↥(Cen z)) = 2 ^ a := by
    have hd : orderOf (⟨x, hx⟩ : ↥(Cen z)) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact ⟨j, hj⟩
  have hmem : (⟨x, hx⟩ : ↥(Cen z)) ∈ layer ↥(Cen z) := by
    refine mem_of_twoElt_of_map_mem (toBar z) (layer ↥(Cen z)) hx2 (odd_card_ker_toBar z) ?_
    rw [h1, h2]
    exact mem_top _
  have hEm : x ∈ Em (Cen z) := by
    rw [Em_eq]
    exact ⟨⟨x, hx⟩, hmem, rfl⟩
  intro a ha
  have := Em_le_centralizer_odd (Cen z) hEm
  exact (Subgroup.mem_centralizer_iff.mp this a ha).symm

end Cen

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208Sp
