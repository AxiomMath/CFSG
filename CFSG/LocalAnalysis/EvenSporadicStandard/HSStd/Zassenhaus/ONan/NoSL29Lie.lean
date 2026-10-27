module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.NoSL29Criterion
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21L52a
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21HSp44
public import CFSG.Quasithin.H13.NQCatA314SL3
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint

private theorem noPerfect720Centralizing_of_lieModel_psl_three_seven {N : Type} [Group N]
    [Finite N] (hN : LieModel N .PSL 3 7 1) : NoPerfect720Centralizing N := by
  refine noPerfect720Centralizing_of_forall fun z _ => Or.inl ?_
  intro hdvd
  have hSt : CFSG.Open.StatedClassicalModel N .PSL 3 7 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hN (by decide)
  have hNcard : Nat.card N = 1876896 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_seven hSt
  have hdvdN : 720 ∣ Nat.card N :=
    dvd_trans hdvd (Subgroup.card_subgroup_dvd_card (centralizer ({z} : Set N)))
  rw [hNcard] at hdvdN
  exact absurd hdvdN (by norm_num)

theorem noSL29_of_lieModel_psl_three_seven {N : Type} [Group N] [Finite N]
    (hN : LieModel N .PSL 3 7 1) (K : Type) [Group K] [Finite K] (hK : commutator K = ⊤)
    (hZ : Nat.card (center K) = 2) (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6)))
    (f : K →* N) (hf : Function.Injective f) : False :=
  false_of_injective_of_noPerfect720Centralizing
    (noPerfect720Centralizing_of_lieModel_psl_three_seven hN) K hK hZ hA f hf

private theorem orderOf_ne_ten_of_lieModel_psl_five_two {N : Type} [Group N]
    (hN : LieModel N .PSL 5 2 1) (g : N) : orderOf g ≠ 10 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hN
  have hK2 : Nat.card K = 2 := by simpa using hK
  let := CFSG.EvenSporadicStandard.M22Std.P21L52.charTwo hK2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  exact CFSG.EvenSporadicStandard.M22Std.P21L52.no_order_ten_of_equiv hK2 e g

private theorem noPerfect720Centralizing_of_lieModel_psl_five_two {N : Type} [Group N]
    [Finite N] (hN : LieModel N .PSL 5 2 1) : NoPerfect720Centralizing N := by
  intro z hz H hle _ hcard
  have h5dvd : 5 ∣ Nat.card H := by rw [hcard]; norm_num
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 h5dvd
  have hyN : orderOf (y : N) = 5 := by rw [← hy]; exact Subgroup.orderOf_coe y
  have hyc : (y : N) ∈ centralizer ({z} : Set N) := hle y.2
  have hcomm : Commute z (y : N) := (Subgroup.mem_centralizer_singleton_iff.1 hyc).symm
  have h10 : orderOf (z * (y : N)) = 10 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hz, hyN]; norm_num), hz, hyN]
  exact orderOf_ne_ten_of_lieModel_psl_five_two hN (z * (y : N)) h10

theorem noSL29_of_lieModel_psl_five_two {N : Type} [Group N] [Finite N]
    (hN : LieModel N .PSL 5 2 1) (K : Type) [Group K] [Finite K] (hK : commutator K = ⊤)
    (hZ : Nat.card (center K) = 2) (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6)))
    (f : K →* N) (hf : Function.Injective f) : False :=
  false_of_injective_of_noPerfect720Centralizing
    (noPerfect720Centralizing_of_lieModel_psl_five_two hN) K hK hZ hA f hf

private theorem exists_subgroup_card_nine_of_card_eq_720 {N : Type} [Group N] [Finite N]
    (H : Subgroup N) (hH : Nat.card H = 720) :
    ∃ P : Subgroup N, P ≤ H ∧ Nat.card P = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P', hP'⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 2) (by rw [hH]; norm_num)
  exact ⟨P'.map H.subtype, Subgroup.map_subtype_le P', by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hP']; norm_num⟩

private theorem noPerfect720Centralizing_of_lieModel_psp_two_two_two {N : Type} [Group N]
    [Finite N] (hN : LieModel N .PSp 2 2 2) : NoPerfect720Centralizing N := by
  intro z hz H hle _ hcard
  obtain ⟨P, hPH, hP⟩ := exists_subgroup_card_nine_of_card_eq_720 H hcard
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    norm_num at hz
  refine CFSG.EvenSporadicStandard.M22Std.P21H.no_involution_centralizes_nine_sp44
    hN z hzz hz1 P hP ?_
  intro x hx
  have hxH : x ∈ H := hPH hx
  have hxc : x ∈ centralizer ({z} : Set N) := hle hxH
  exact (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm

theorem noSL29_of_lieModel_psp_two_two_two {N : Type} [Group N] [Finite N]
    (hN : LieModel N .PSp 2 2 2) (K : Type) [Group K] [Finite K] (hK : commutator K = ⊤)
    (hZ : Nat.card (center K) = 2) (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6)))
    (f : K →* N) (hf : Function.Injective f) : False :=
  false_of_injective_of_noPerfect720Centralizing
    (noPerfect720Centralizing_of_lieModel_psp_two_two_two hN) K hK hZ hA f hf

private theorem noPerfect720Centralizing_of_lieModel_psu_three_five {N : Type} [Group N]
    [Finite N] (hN : LieModel N .PSU 3 5 1) : NoPerfect720Centralizing N := by
  refine noPerfect720Centralizing_of_forall fun z hz => Or.inr ?_
  refine ⟨⁅(centralizer ({z} : Set N)), (centralizer ({z} : Set N))⁆, ?_, ?_⟩
  · intro H hle hperf
    rw [← hperf]
    exact Subgroup.commutator_mono hle hle
  · have hSt : CFSG.Open.StatedClassicalModel N .PSU 3 5 1 :=
      CFSG.Blueprint.LieModel.statedClassicalModel hN (by decide)
    have hcard :=
      CFSG.Quasithin.H13.NQCat.A314D.cent_sl3five (X := N) ⟨false, Or.inl hSt⟩ z hz
    omega

theorem noSL29_of_lieModel_psu_three_five {N : Type} [Group N] [Finite N]
    (hN : LieModel N .PSU 3 5 1) (K : Type) [Group K] [Finite K] (hK : commutator K = ⊤)
    (hZ : Nat.card (center K) = 2) (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6)))
    (f : K →* N) (hf : Function.Injective f) : False :=
  false_of_injective_of_noPerfect720Centralizing
    (noPerfect720Centralizing_of_lieModel_psu_three_five hN) K hK hZ hA f hf

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
