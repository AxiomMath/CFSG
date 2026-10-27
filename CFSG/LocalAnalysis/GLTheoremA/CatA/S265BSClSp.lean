module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTy
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClAsm
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClSpRep
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASpAct
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ChevBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.Classical (spEnd)
open scoped commutatorElement

private theorem isBOfTwo_of_tySp10 {G : Type} [Group G] (h : catalogIs G tySp10) :
    catalogIs G (S8.L84.isBOfTwo 5) := by
  obtain ⟨i, hi, he⟩ := h
  refine ⟨i, ?_, he⟩
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | B r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      all_goals first | exact hi.elim | exact ⟨rfl, hi⟩
    | _ => exact hi.elim
  | _ => exact hi.elim

theorem qsBRes_sp10 {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (hN : QSNL 3 S B T x D K) (hS : catalogIs (PSimple 3 S) tySp10)
    (hK : catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two)
    (hB : Nat.card B = 3 ^ 5)
    (hc : ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω)) : QSConcl 3 S B D K := by
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 hN.cfg.normal) ▸ Subgroup.mem_top g
  obtain ⟨eS⟩ := S8.L84.I1430ChevBridge.iso_sp_of_isBOfTwo (isBOfTwo_of_tySp10 hS)
  obtain ⟨ψ, h1, h2, -⟩ := S265A.exists_spHom (J := S) (n := 5) (by norm_num) eS
  refine qsConcl_of_section hN.cfg hK hB hc (eS := eS.toMonoidHom) eS.injective (W := ⊤)
    (ψ.comp (Subgroup.inclusion fun g _ => hSN g)) (fun w hw z => ?_) (fun w hw => h2 ⟨w, hw⟩)
    (fun b _ => Subgroup.mem_top b) (fun z _ => Subgroup.mem_top z)
    (fun y _ _ => Subgroup.mem_top y) fun A T₁ d y hA h81 hdA hd1 hy hy1 hdy hT hT1 hAT => ?_
  · have h3 := congrArg (fun γ : MulAut _ => γ (eS z)) (h1 ⟨w, hw⟩)
    have h4 : eS (chevAut 3 S ⟨w, hw⟩ z) = ψ ⟨w, hw⟩ * eS z * (ψ ⟨w, hw⟩)⁻¹ := by
      simpa [MulAut.congr_apply, MulAut.conj_apply] using h3
    exact h4
  · obtain ⟨e, heA, he8, hlay⟩ := exists_layer_pair_statedSp_five hA h81 hdA
      (ker_spEnd_sub_one_eq_bot_of_commute_eleven hd1 hy hy1 hdy) hT hT1 hAT
    exact ⟨e, heA, fun hcomm => finrank_ker_spEnd_sub_one_ne_eight hy hy1 hcomm he8,
      glaPLayer_comap_ne_bot_of_equiv eS hlay⟩

theorem qsBResSp10_holds : QSBResSp10 :=
  fun _ _ _ _ _ _ _ _ _ hN hS hK hB hc => qsBRes_sp10 hN hS hK hB hc

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
