module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223W21
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He12E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152U21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def StageLemma15221W_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Lemma15221ConclW T Mc M H H₁ H₂ B₀ I

section Main

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem lemma_15_2_21_two_W_F4 (h15208 : StageLemma15208_F4) (h15209 : StageNotation15209_F4)
    (hs : Setting152 T Mc M) (hH : IsHStar T M H) (h14 : Lemma15214Concl T Mc M B₀)
    (hK : conjClosure (oTwoUpper H) Mc = oTwoUpper H) :
    IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxM : (x : G) ∈ M := x.2.1
  have hxMc : (x : G) ∈ Mc := by
    have h1 : (x : G) ∈ M ⊓ Mc := by
      rw [h14.inf_eq.1, h14.inf_eq.2]
      exact Subgroup.mem_sup_left x.2
    exact h1.2
  exact He12.not_orderOf_three_of_mem_inf_F4 h15208 h15209 hs hH hK hxM hxMc hxG

end Main

theorem stageLemma15221W_of_F4 (h5 : StageLemma15205_F4) (h159 : StageLemma1519)
    (h8 : StageLemma15208_F4) (h11 : StageLemma15211_F4) (h12 : He12.StageLemma15212W_F4)
    (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4) (hN : StageNotation15209_F4)
    (h16 : StageLemma15216_F4) (h17 : StageLemma15217_F4) (hIrr : Input15209Irr_F4) (hJ : Input15112J_F4)
    (hKc : Input1210Kc_F4) (h3 : Input15221Three_F4) : StageLemma15221W_F4 := by
  intro G _ _ T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI
  have hD : Inputs152 T Mc M H B₀ I :=
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI, h17 G T Mc M hs B₀ hB₀ I hI⟩
  obtain ⟨B, hB⟩ := (hN G T Mc M hs H hH).sigmaPrime_nonempty
  have h12' := h12 G T Mc M hs H hH B hB
  exact ⟨fun hnot => lemma_15_2_21_one_W hs hH hP hB₀ hD h12' (hIrr G T Mc M hs H hH)
      (hJ G T Mc M hs H hH H₁ H₂ hP) (hKc G T Mc M hs B₀ hB₀ H hH) hnot,
    fun hK => lemma_15_2_21_two_W_F4 h8 hN hs hH hD.h14 hK,
    fun hL hii hY => h3 G T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI hL hii hY⟩

end CFSG.Quasithin
