module

public import CFSG.CGT.PushingUpLit.K1R.SporBase
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicSmall
public import CFSG.Sporadic.ONOddCore.LocalComp

public section

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem m11_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .M11 := by
  have hSL : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ∣ 48 := by
    intro n hn K _ _ hK h
    rw [card_sl2 hK] at h
    have := lt_of_sl2Order_dvd (by norm_num) (show 48 < 2 ^ 6 by norm_num) h
    interval_cases n <;> norm_num at h
  exact sporadicInner_of_comps (isoInvariant_card_dvd 48) hSL (fun _ _ _ ⟨e⟩ t ht =>
    compsSatisfy_centralizer_of_mulEquiv _ (isoInvariant_card_dvd 48) m11_centralizerIn_comps e t
      ht)

theorem m22_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .M22 := by
  have hSL : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ∣ 384 := by
    intro n hn K _ _ hK h
    rw [card_sl2 hK] at h
    have := lt_of_sl2Order_dvd (by norm_num) (show 384 < 2 ^ 9 by norm_num) h
    interval_cases n <;> norm_num at h
  exact sporadicInner_of_comps (isoInvariant_card_dvd 384) hSL (fun _ _ _ ⟨e⟩ t ht =>
    compsSatisfy_centralizer_of_mulEquiv _ (isoInvariant_card_dvd 384) m22_centralizerIn_comps e t
      ht)

theorem m23_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .M23 :=
  sporadicInner_of_comps isoInvariant_not_three_dvd sl2_fails_not_three_dvd (fun _ _ _ ⟨e⟩ t ht =>
    compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd m23_centralizerIn_comps e t
      ht)

theorem m24_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .M24 :=
  sporadicInner_of_comps isoInvariant_not_three_dvd sl2_fails_not_three_dvd (fun _ _ _ ⟨e⟩ t ht =>
    compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd m24_centralizerIn_comps e t
      ht)

theorem j4_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .J4 :=
  sporadicInner_of_comps (Qi := fun _ _ => False) (fun _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ h => h) (fun G _ _ hG t ht B hB => j4NoComponentsInput G hG t ht B hB)

theorem hs_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .HS := by
  refine InnerKernelSelector.of_false ?_
  intro D _ _ hD hs n hn K _ _ hK α hα hin S hSα hSn hSK _
  obtain ⟨t, ht, -, -, hcomp, -, hcard, -⟩ := innerRoot_setup hD hn hK hα hin hSα hSn hSK
  obtain ⟨-, -, h360⟩ :=
    CFSG.Sporadic.SmallOddCore.cti_hs_involution_local_components_simple_order_360 hs ht hcomp
  rw [hcard] at h360
  have := lt_of_sl2Order_eq (by omega) (show 360 < 2 ^ 9 by norm_num) h360
  interval_cases n <;> norm_num at h360

theorem mcl_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .McL := by
  have hSLi : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ⧸
        center (Matrix.SpecialLinearGroup (Fin 2) K) ≃* mclX) := by
    intro n hn K _ _ hK ⟨θ⟩
    have h1 := Nat.card_congr θ.toEquiv
    have hX : Nat.card mclX = 20160 := CFSG.Sporadic.SmallOddCore.card_mclX
    rw [card_sl2_quotient_center (by omega) hK, hX] at h1
    have := lt_of_sl2Order_eq (by omega) (show 20160 < 2 ^ 15 by norm_num) h1
    interval_cases n <;> norm_num at h1
  exact sporadicInner_of_comps (isoInvariant_quotient_center_equiv mclX) hSLi
    (fun G _ _ ⟨e⟩ t ht => mcl_inner_comps e t ht)

theorem he_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .He := by
  refine InnerKernelSelector.of_false ?_
  intro D _ _ hD hs n hn K _ _ hK α hα hin S hSα hSn hSK _
  obtain ⟨t, ht, -, -, hcomp, -, hcard, hZ⟩ := innerRoot_setup hD hn hK hα hin hSα hSn hSK
  have h20160 :=
    CFSG.Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order hs ht
      hcomp
  have hq : Nat.card (S ⧸ center S) = Nat.card S :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
  rw [hq, hcard] at h20160
  have := lt_of_sl2Order_eq (by omega) (show 20160 < 2 ^ 15 by norm_num) h20160
  interval_cases n <;> norm_num at h20160

theorem ru_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .Ru :=
  sporadicInner_of_comps isoInvariant_not_three_dvd sl2_fails_not_three_dvd (fun _ _ _ ⟨e⟩ t ht =>
    compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd ru_centralizerIn_comps
      (e.trans CFSG.Sporadic.RuSchreier.ruEquivP) t ht)

theorem suz_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .Suz := by
  refine InnerKernelSelector.of_false ?_
  intro D _ _ hD hs n hn K _ _ hK α hα hin S hSα hSn hSK _
  obtain ⟨e⟩ := hs
  refine inner_false_of_comps hD hn hK hα hin hSα hSn hSK
    (isoInvariant_card_quotient_center {20160}) (fun h' => ?_) (fun t ht B hB => ?_)
  · rw [Set.mem_singleton_iff, card_sl2_quotient_center (by omega) hK] at h'
    have := lt_of_sl2Order_eq (by omega) (show 20160 < 2 ^ 15 by norm_num) h'
    interval_cases n <;> norm_num at h'
  · exact CFSG.Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e
      t ht B hB

open CFSG.Sporadic.ONOddCore
  (cti_on_involution_local_components_projective_linear_quotient_order) in
theorem on_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .ONan := by
  refine InnerKernelSelector.of_false ?_
  intro D _ _ hD hs n hn K _ _ hK α hα hin S hSα hSn hSK _
  exact inner_false_of_comps hD hn hK hα hin hSα hSn hSK
    (isoInvariant_card_quotient_center {20160})
    (sl2_fails_card_quotient_center_mem (N := {20160}) (fun m hm h' =>
      sl2Order_ne_of_check (B := 15) (by norm_num) (by decide) m hm
        (Set.mem_singleton_iff.1 h')) n hn K hK) (fun t ht B hB => Set.mem_singleton_iff.2
      (cti_on_involution_local_components_projective_linear_quotient_order hs t ht B hB))

end CFSG.CGT.PushingUpLit.K1R
