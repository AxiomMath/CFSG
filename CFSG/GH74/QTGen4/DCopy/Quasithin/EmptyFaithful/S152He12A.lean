module

public import CFSG.Quasithin.EmptyFaithful.S152He12A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack12

namespace He12

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem mem_of_orderOf_three_F4 (h15208 : StageLemma15208_F4) (h15209 : StageNotation15209_F4)
    {T Mc M H : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hKK : conjClosure (oTwoUpper H) Mc = oTwoUpper H) {x : G} (hx : x ∈ Mc)
    (hx3 : orderOf x = 3) : x ∈ oTwoUpper H := by
  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hPMc : pCoreOf 2 Mc ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hs.qtfe.mc_max.1
  have hHMc : H ≤ Mc := (h15209 G T Mc M hs H hH).le_mc
  have hsylH : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  have hsylMc : IsSylowTwoOf T Mc := isSylowTwoOf_of_quasithinIsSylowTwo hs.qtfe.sylow hTMc
  have hKn : Mc ≤ Subgroup.normalizer ((oTwoUpper H : Subgroup G) : Set G) := by
    have := le_normalizer_conjClosure (oTwoUpper H) Mc
    rwa [hKK] at this
  have hrk : CFSG.Open.pRank 3 Mc ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot hs.qtfe.qtke hPMc Nat.prime_three (by norm_num)
  have hcube : x ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hx3]
  exact He8.mem_of_cube_eq_one φ hHMc hKn hrk hx hcube
    (He8.commutator_mem_of_three hsylH hsylMc hHMc φ hKn hx (k := 1) (by simpa using hx3))

theorem not_orderOf_three_of_mem_inf_F4 (h15208 : StageLemma15208_F4) (h15209 : StageNotation15209_F4)
    {T Mc M H : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hKK : conjClosure (oTwoUpper H) Mc = oTwoUpper H) {y : G} (hyM : y ∈ M) (hyMc : y ∈ Mc)
    (hy3 : orderOf y = 3) : False := by
  have hyK : y ∈ oTwoUpper H := mem_of_orderOf_three_F4 h15208 h15209 hs hH hKK hyMc hy3
  have hyH : y ∈ H := oTwoUpper_le H hyK
  have hyT : y ∈ T := by
    rw [(h15209 G T Mc M hs H hH).eq_inf]
    exact ⟨hyM, hyH⟩
  obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.mp hs.qtfe.sylow.1 ⟨y, hyT⟩
  have h3 : (3 : ℕ) = 2 ^ i := by
    have e : orderOf y = orderOf (⟨y, hyT⟩ : T) := Subgroup.orderOf_coe ⟨y, hyT⟩
    rw [← hy3, e, hi]
  rcases i with _ | i
  · simp at h3
  · have : 2 ∣ 2 ^ (i + 1) := dvd_pow_self 2 (by omega)
    omega

theorem coprime_three_orderOf_of_mem_inf_F4 (h15208 : StageLemma15208_F4) (h15209 : StageNotation15209_F4)
    {T Mc M H : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hKK : conjClosure (oTwoUpper H) Mc = oTwoUpper H) {y : G} (hyM : y ∈ M) (hyMc : y ∈ Mc) :
    Nat.Coprime 3 (orderOf y) := by
  by_contra h
  have h3 : 3 ∣ orderOf y := by
    rwa [Nat.Prime.coprime_iff_not_dvd Nat.prime_three, not_not] at h
  have hord : orderOf (y ^ (orderOf y / 3)) = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos y).ne' h3
  exact not_orderOf_three_of_mem_inf_F4 h15208 h15209 hs hH hKK (pow_mem hyM _) (pow_mem hyMc _) hord

theorem mem_centralizer_Z_of_threePower_F4 (h15208 : StageLemma15208_F4) (h15209 : StageNotation15209_F4)
    (h1519 : StageLemma1519) {T Mc M H : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hKK : conjClosure (oTwoUpper H) Mc = oTwoUpper H) {x : G} (hx : x ∈ Mc) {k : ℕ}
    (hk : orderOf x = 3 ^ k) : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hord : OrdLE T Mc M :=
    (h1519 G T Mc M hs.qtfe hs.mf hs.ce).two.2 Mc hs.qtfe.inM_mc
  have hcop : ∀ y ∈ M, y ∈ Mc → Nat.Coprime 3 (orderOf y) := fun y hyM hyMc =>
    coprime_three_orderOf_of_mem_inf_F4 h15208 h15209 hs hH hKK hyM hyMc
  exact Subgroup.centralizer_le (le_conjClosure (quasithinOmegaOneCenter T) Mc)
    (mem_centralizer_VZ_of_threePower hord hcop hx hk)

end He12

end CFSG.Quasithin
