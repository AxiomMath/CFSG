module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQuasi
public import CFSG.Sporadic.Ly
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallMain

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ClassicalInvolution.LyProof CFSG.Sporadic.Ly
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall


theorem outTwoCyclic_ly : Nobq.OutTwoCyclic NativeSporadic.Ly := by
  have : Finite NativeSporadic.Ly := CFSG.Sporadic.Ly.fam_ly_simplicity.1
  have h := CFSG.Sporadic.LySchreier.outer_order_divides_two (T := NativeSporadic.Ly)
    ⟨MulEquiv.refl _⟩
  exact Nobq.OutTwoCyclic.of_card_le_two (Nat.le_of_dvd (by norm_num) h.1)

theorem not_twinPair_ly {F : Type} [Group F] (h : NativeSporadic.IsSporadic F .Ly) :
    ¬ TwinPair F := by
  obtain ⟨e₀⟩ := h
  have e₁ : F ≃* NativeSporadic.Ly := e₀
  have e : TLGrpEquiv F J := e₁.trans lyEquivJ
  have : Finite J := Finite.of_equiv _ lyEquivJ.toEquiv
  obtain ⟨hzz, hz1⟩ := z_facts
  obtain ⟨hCK, hq, hcen, -⟩ := K_facts
  obtain ⟨hSp, hidx⟩ := S_sylow
  obtain ⟨-, hcover⟩ := S_facts
  have hz₀ : orderOf zJ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hSr : ∀ s ∈ SJ, orderOf s = 2 → ∃ c ∈ (⊤ : Subgroup J), s = c * zJ * c⁻¹ := by
    intro s hs ho
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [ho, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at ho
      exact absurd ho (by norm_num)
    obtain ⟨C, hC⟩ := hcover s hs hss hs1
    exact ⟨C, Subgroup.mem_top C, hC⟩
  have hcov : ∀ z : J, orderOf z = 2 → ∃ c : J, c * zJ * c⁻¹ = z := fun z hz => by
    obtain ⟨c, -, hc⟩ := CFSG.ClassicalInvolution.cover_of_sylow ⊤ SJ hSp hidx zJ hSr z
      (Subgroup.mem_top z) hz
    exact ⟨c, hc.symm⟩
  have e₀' : TLGrpEquiv ↥(Subgroup.centralizer ({zJ} : Set J)) ↥KJ := MulEquiv.subgroupCongr hCK
  refine not_twinPair_of_quasi (G := J) e zJ ?_ e₀' ?_ ?_ ?_
  · exact hz₀
  · exact hq
  · exact hcen
  · exact hcov


theorem twinLeafR_ly {r n : ℕ} (hr : 4 ≤ r) :
    TwinLeafR r n fun F _ => NativeSporadic.IsSporadic F .Ly := by
  intro Y _ _ R S t hP _ hF
  haveI := hP.core.simple
  obtain ⟨e⟩ := hF
  have hcomm : SocleComm2 ↥(genFittingFStar Y) :=
    socleComm2_of_outTwoCyclic (Nobq.OutTwoCyclic.of_mulEquiv e outTwoCyclic_ly)
  exact not_twinPair_ly ⟨e⟩ (exists_twinPair_of_perp hr hP hcomm)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
