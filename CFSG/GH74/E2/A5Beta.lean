module

public import CFSG.GH74.E2.LocalLeaves
public import CFSG.GH74.AS16.E2.Pump2

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.GLS CFSG.GH74.Generic

theorem no_terminal_A5
    {G : Type} [Group G] [Finite G] (hH : Hyp G) {t : G}
    (ht : orderOf t = 2) {K : Subgroup G} (hK : IsCompCen t K)
    (huniq : ∀ K' : Subgroup G, IsCompCen t K' → K' = K) (hsh : ShapeA5 ↥K)
    (hterm : IsTerminalPair 2 t K) (hQ : Nonempty (↥(Qt t) ≃* QuaternionGroup 2)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, h5 | h9⟩ := hH.restrictedEven.2.2.1 t K hterm 5 1 (by norm_num) (by norm_num)
    (CFSG.GH74.AS16.E2.lieModel_of_shapeA5 hsh)
  · obtain ⟨P, hPel, -⟩ := h5.2
    have hQc : Qt t ≤ Subgroup.centralizer (K : Set G) := fun q hq =>
      Subgroup.mem_centralizer_iff.2 fun k hk =>
        (Qt_commute_comp hH ht hK huniq q hq k hk).symm
    have hQN : Qt t ≤ normalizer (K : Set G) :=
      hQc.trans (Subgroup.centralizer_le_normalizer (K : Set G))
    have hQp : IsPGroup 2 ↥((Qt t).subgroupOf (normalizer (K : Set G))) :=
      (Qt_isPGroup t).of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
    obtain ⟨S, hS⟩ := hQp.exists_le_sylow
    have hP : ∀ x y : ↥(P : Subgroup ↥(normalizer (K : Set G))), x * y = y * x :=
      fun x y => hPel.toIsMulCommutative.is_comm.comm x y
    have hSc : ∀ a b : ↥(S : Subgroup ↥(normalizer (K : Set G))), a * b = b * a := by
      intro a b
      refine (Sylow.equiv P S).symm.injective ?_
      rw [map_mul, map_mul]
      exact hP _ _
    have hQcomm : ∀ x y : ↥(Qt t), x * y = y * x := by
      intro x y
      have hx : (⟨(x : G), hQN x.2⟩ : ↥(normalizer (K : Set G))) ∈
          (Qt t).subgroupOf (normalizer (K : Set G)) := x.2
      have hy : (⟨(y : G), hQN y.2⟩ : ↥(normalizer (K : Set G))) ∈
          (Qt t).subgroupOf (normalizer (K : Set G)) := y.2
      have h := hSc ⟨_, hS hx⟩ ⟨_, hS hy⟩
      apply Subtype.ext
      have h' := congrArg (fun z : ↥(S : Subgroup ↥(normalizer (K : Set G))) =>
        (((z : ↥(normalizer (K : Set G))) : G))) h
      exact h'
    obtain ⟨e⟩ := hQ
    have hnc : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
    apply hnc
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hQcomm _ _
  · exact absurd h9.1 (by norm_num)

theorem noCaseIIBetaA5_of
    (hComp : ComponentList) (hP : CFSG.GH74.AS16.E2.PumpUpData2)
    (hN : CFSG.GH74.AS16.E2.NoComponent2M12) : NoCaseIIBetaA5 := by
  intro G _ _ hH t t' a A B K hc hK hsh hQ hcard
  have ht := hc.order_t
  obtain ⟨-, huniq⟩ := hComp G hH t ht K hK
  by_cases hterm : CFSG.GH74.AS16.E2.Terminal K
  · refine no_terminal_A5 hH ht hK huniq hsh ⟨ht, hK, ?_, fun y hy hyK => hterm y hy hyK⟩ hQ
    obtain ⟨i, hiK, hi⟩ := AS16.exists_involution_of_isQuasisimple (isCompCen_quasisimple hK)
    have h2 : orderOf (⟨i, hiK⟩ : ↥K) = 2 := by rw [← Subgroup.orderOf_coe]; exact hi
    rw [← h2]
    exact orderOf_dvd_natCard _
  · obtain ⟨w, Kw, hw, hKw, hshw⟩ :=
      CFSG.GH74.AS16.E2.exists_m12_of_nonTerminal hComp hP hH ht hK hterm
    exact hN G hH w hw Kw hKw hshw

theorem s_restrictedEvenThin_of_localLeaves'
    (hGKF : GenericKnownFacts) (hF : E2ComponentFacts)
    (hD : K0Data) (hD3 : K0Data3) (hP : PumpUpData) (hP2 : CFSG.GH74.AS16.E2.PumpUpData2)
    (hM : M11Tables) (hL : L33Tables) (hN : CFSG.GH74.AS16.E2.NoComponent2M12)
    (hA6 : NoLocalA6) (hOut : NoLocalL33Outer) (hGL : NoLocalGL23)
    (hαL33 : NoCaseIIAlphaL33) (hαM11 : NoCaseIIAlphaM11) : S_restrictedEvenThin :=
  s_restrictedEvenThin_of_localLeaves hGKF hF hD hD3 hP hM hL hA6 hOut hGL hαL33 hαM11
    (noCaseIIBetaA5_of (evenType_components hGKF hF hD) hP2 hN)

end CFSG.GH74.E2
