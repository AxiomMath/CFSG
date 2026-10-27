module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ITwist
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ITwModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {L : Subgroup G}

theorem sec4I_exists_twisted_of_hasType [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {s : G} (hss : s * s = 1)
    {y : ProjOrth Sec4IQ} (hy : Sec4IActs e s y) {r : ℕ} {α : ℤˣ} (hty : HasType y r α)
    (hr : r = 2 ∨ r = 4) :
    ∃ v : G, IsI4PlusIn L v ∧ v ∈ Subgroup.centralizer ({s} : Set G) ∧
      s * v ∈ conjClassIn L s := by
  obtain ⟨-, t, htt, htype, hyt⟩ := hty
  have htd : invDim t = r := congrArg Prod.fst htype
  obtain ⟨a, u, hu4, huu, hufix, hau⟩ := sec4I_exists_twist_model sec4IQ_nondegenerate
    sec4IQ_finrank htt (by rw [htd]; exact hr)
  have hα : ∀ l : ↥L, sec4ICover e (conjAut L hss hy.1 l) =
      projAut sec4IQ_nondegenerate t (sec4ICover e l) := by
    intro l
    apply Subtype.ext
    rw [coe_projAut, hyt]
    exact hy.2 l (conjAut L hss hy.1 l) rfl
  obtain ⟨v, hvL, hvv, hρv, hsv, b, hbL, hb⟩ := sec4I_exists_twisted_lift L (sec4ICover e)
    (sec4ICover_odd hL e) hss hy.1 (projAut sec4IQ_nondegenerate t) hα hufix huu hau
  have hv1 : v ≠ 1 := by
    intro h1
    have h2 : (⟨v, hvL⟩ : ↥L) = 1 := Subtype.ext h1
    rw [h2, map_one] at hρv
    exact hu4.1 (congrArg Subtype.val hρv.symm)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨v, (sec4I_isI4PlusIn_iff hL e).mpr ⟨hvL, orderOf_eq_prime (by rw [pow_two, hvv]) hv1,
    ?_⟩, Subgroup.mem_centralizer_singleton_iff.mpr hsv.symm, b⁻¹, L.inv_mem hbL, ?_⟩
  · rw [show (e (QuotientGroup.mk (⟨v, hvL⟩ : ↥L)) : Sec4IOmega) = u from
      (sec4ICover_apply e _).symm.trans hρv]
    exact hu4
  · rw [inv_inv, hb]
    exact hsv

theorem asc82Fact214_holds : Asc82Fact214 := by
  intro G _ _ L hL s hs2 hsN hsC
  obtain ⟨e⟩ := sec4I_exists_model hL
  have hss := mul_self_eq_one_of_orderOf_eq_two hs2
  obtain ⟨y, hy⟩ := exists_sec4IActs e hsN
  have hyy := hy.sq hss
  have hy1 : y ≠ 1 := fun h => hsC ((Sec4IActs.eq_one_iff hL hy).mp h)
  have h6 : (6 : ℕ) = 2 ∨ (6 : ℕ) = 4 ∨ (6 : ℕ) = 6 := Or.inr (Or.inr rfl)
  rcases hasType_of_involution_seven sec4IQ_nondegenerate sec4IQ_finrank sec4IQ_quadSign hyy
    hy1 with h | h | h | h | h | h
  · exact Or.inl (sec4I_exists_twisted_of_hasType hL e hss hy h (Or.inl rfl))
  · exact Or.inl (sec4I_exists_twisted_of_hasType hL e hss hy h (Or.inl rfl))
  · exact Or.inl (sec4I_exists_twisted_of_hasType hL e hss hy h (Or.inr rfl))
  · exact Or.inl (sec4I_exists_twisted_of_hasType hL e hss hy h (Or.inr rfl))
  · exact Or.inr ⟨1, (sec4I_inducesTypeSome_iff e h6).mpr ⟨y, hy, h⟩⟩
  · exact Or.inr ⟨-1, (sec4I_inducesTypeSome_iff e h6).mpr ⟨y, hy, h⟩⟩

end CFSG.OddStandard.SmallF3.Omega
