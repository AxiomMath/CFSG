module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeM12
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3Sylow
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem false_of_threeNineHyp_J3
    (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .J3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  obtain ⟨e⟩ := hK
  dsimp only [CFSG.Blueprint.NativeSporadic.Carrier] at e
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have hfacts := CFSG.AGLEmbedding.kFactJ3Sylow ↥K ⟨e.trans b⟩
  have hcard : Nat.card ↥K = 50232960 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J3.card_J3
  have := CFSG.Sporadic.J3.isSimpleGroup_J3
  have hsimple : IsSimpleGroup ↥K := MulEquiv.isSimpleGroup (H := NativeSporadic.J3) e
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcard]; norm_num)
  have hOut : Nat.card (Outer ↥K) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.j3_outer_card_le
      (e.trans CFSG.Sporadic.Schreier.j3PermEquiv)
  haveI : Finite (MulAut ↥K) :=
    Finite.of_injective (fun f : MulAut ↥K => (f : ↥K → ↥K)) fun f g hfg =>
      MulEquiv.ext (congrFun hfg)
  have hOut0 : 0 < Nat.card (Outer ↥K) := Nat.card_pos
  have hd3 : 3 ≤ d := by
    have := h.d_prime.two_le
    have := h.d_ne_two
    omega
  have hdOut : ¬ d ∣ Nat.card (Outer ↥K) := fun hdv => by
    have := Nat.le_of_dvd hOut0 hdv
    omega
  have h3Out : ¬ 3 ∣ Nat.card (Outer ↥K) := fun hdv => by
    have := Nat.le_of_dvd hOut0 hdv
    omega
  obtain ⟨S, hS⟩ := h.exists_sylow_subgroupOf_eq_normalizer hZ h3Out
    fun S H hH => (hfacts S).maximal H hH
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hdOut
  obtain ⟨hdY, -⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
  rw [hS] at hdY
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer
    ((S : Subgroup ↥K) : Set ↥K))) d hdY
  obtain ⟨k, hk⟩ := (hfacts S).two_top (y : ↥K) y.2
  have hyd : orderOf (y : ↥K) = d := by rw [Subgroup.orderOf_coe, hy]
  have hcop : (orderOf (y : ↥K)).Coprime (2 ^ k) := by
    rw [hyd]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes h.d_prime Nat.prime_two).mpr h.d_ne_two)
  have hzd : orderOf ((y : ↥K) ^ 2 ^ k) = d := by rw [hcop.orderOf_pow, hyd]
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨(y : ↥K) ^ 2 ^ k, hk⟩
  have hdvd : d ∣ 3 ^ n := by
    rw [← hzd]
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hn
    simpa using this
  exact h.d_ne ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
    (h.d_prime.dvd_of_dvd_pow hdvd))

theorem threeNineThreeSpor_holds :
    ThreeNineThreeSpor := by
  intro X _ _ K E D X₁ d h hK
  rcases hK with hK | hK | hK
  · exact false_of_threeNineHyp_M11 h hK
  · exact false_of_threeNineHyp_M12 h hK
  · exact false_of_threeNineHyp_J3 h hK

end CFSG.LocalAnalysis.AGL81I.Section3
