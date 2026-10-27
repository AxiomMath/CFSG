module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem card_centralizer_mul_four_le_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4) {U : Subgroup G}
    (hUV : U ≤ V) (hU4 : Nat.card U = 4) (hne : U ≠ ch6ZS T L V) :
    Nat.card ↥(T ⊓ Subgroup.centralizer (U : Set G)) * 4 ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  obtain ⟨u, huU, huZ⟩ : ∃ u ∈ U, u ∉ ch6ZS T L V := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_of_le_of_card_ge hcon (by rw [hU4, h.card_ZS_four]))
  set X := T ⊓ Subgroup.centralizer (U : Set G) with hX
  have hSX : ch6S T L V ⊓ X ≤ ch6Q T V := by
    rintro s ⟨hsS, hsT, hsU⟩
    refine ⟨hsT, h.toHyp611Nat.mem_centralizer_V_of_mem_S_ch62 hsS (hUV huU) huZ ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hsU u huU).symm
  have h1 := Subgroup.relIndex_mul_card (ch6S T L V) X
  have h2 : (ch6S T L V).relIndex X ≤ (ch6S T L V).relIndex T :=
    Subgroup.relIndex_le_of_le_right inf_le_left Subgroup.index_ne_zero_of_finite
  have h3 : Nat.card ↥(ch6S T L V ⊓ X) ≤ Nat.card (ch6Q T V) := Subgroup.card_le_of_le hSX
  have h8 := h.relIndex_Q_T_F4 h331 h615
  have hQT : 8 * Nat.card ↥(ch6Q T V) = Nat.card ↥T := by
    have := Subgroup.relIndex_mul_card (ch6Q T V) T
    rw [h8, inf_of_le_left (inf_le_left : ch6Q T V ≤ T)] at this
    exact this
  have hS2 := h.relIndex_S_le_two
  have : Nat.card ↥X ≤ 2 * Nat.card (ch6Q T V) := by
    rw [← h1]
    exact Nat.mul_le_mul (h2.trans hS2) h3
  omega

theorem lemma_6_2_5_four_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) {g : G}
    (hg : ch6ZS T L V ≤ conjSubgroup V g) : conjSubgroup V g = V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := ch6ZS T L V with hZ

  set U₁ := conjSubgroup Z g⁻¹ with hU₁
  have hU₁V : U₁ ≤ V := by
    have := conjSubgroup_mono_left g⁻¹ hg
    rwa [conjSubgroup_conj_inv] at this
  have hU₁4 : Nat.card U₁ = 4 := by rw [card_conjSubgroup, h.card_ZS_four]
  have hU₁1 : U₁ ≠ ⊥ := by
    intro h0
    have : Nat.card U₁ = 1 := by rw [h0, Subgroup.card_bot]
    omega

  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 2 (bot_le : ⊥ ≤ M ⊓ Subgroup.normalizer (U₁ : Set G))
    IsPGroup.of_bot
  obtain ⟨m, hm, hPT⟩ := h.toHyp611.exists_conj_sylow
    (hP.le.trans (h.toHyp611Nat.normalizer_le hU₁1 hU₁V)) hP.isPGroup
  set U₂ := conjSubgroup U₁ m with hU₂
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hm.2
  have hmM : m ∈ M := hm.1
  have hU₂V : U₂ ≤ V := by
    have := conjSubgroup_mono_left m hU₁V
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hmV] at this
  have hU₂4 : Nat.card U₂ = 4 := by rw [card_conjSubgroup, hU₁4]
  have hU₂Z : U₂ = conjSubgroup Z (g⁻¹ * m) := by rw [hU₂, hU₁, conjSubgroup_conjSubgroup]

  have hNM : M ⊓ Subgroup.normalizer (U₂ : Set G) =
      conjSubgroup (M ⊓ Subgroup.normalizer (U₁ : Set G)) m := by
    rw [conjSubgroup_inf, conjSubgroup_normalizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hmM)]
  have hPm : conjSubgroup P m ≤ T := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hPT hx)
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have := congrArg (fun z => m⁻¹ * z * m) hyx
      simpa [mul_assoc] using this
    rw [← this]
    exact hy
  have hSyl₂ : IsSylowIn 2 (T ⊓ Subgroup.normalizer (U₂ : Set G))
      (M ⊓ Subgroup.normalizer (U₂ : Set G)) := by
    have hPm' : IsSylowIn 2 (conjSubgroup P m) (M ⊓ Subgroup.normalizer (U₂ : Set G)) := by
      rw [hNM]
      refine ⟨conjSubgroup_mono_left m hP.le, hP.isPGroup.map _, ?_⟩
      unfold conjSubgroup
      rw [Subgroup.relIndex_map_map_of_injective _ _
        (fun a b hab => (MulAut.conj m⁻¹).injective hab)]
      exact hP.not_dvd_relIndex
    refine ⟨inf_le_inf_right _ h.T_le, h.sylow.1.to_le inf_le_left, fun h2 =>
      hPm'.not_dvd_relIndex (h2.trans (Subgroup.relIndex_dvd_of_le_left _ ?_))⟩
    exact le_inf hPm (hPm'.le.trans inf_le_right)

  set T' := conjSubgroup T (g⁻¹ * m) with hT'
  have hT'N : T' ≤ Subgroup.normalizer (U₂ : Set G) := by
    rw [hU₂Z, hT', ← conjSubgroup_normalizer]
    exact conjSubgroup_mono_left _ (h.toHyp611Nat.T_le_normalizer_ZS)
  have hT'card : Nat.card T' = Nat.card T := card_conjSubgroup T _
  have hT'2 : IsPGroup 2 T' := h.sylow.1.map _

  have hU₂eq : U₂ = Z := by
    by_contra hne
    by_cases hC : Subgroup.centralizer (U₂ : Set G) ≤ Subgroup.normalizer (V : Set G)
    ·
      have hCM : Subgroup.centralizer (U₂ : Set G) ≤ M := hC.trans (h.normalizer_V_le_F4 h432)
      have hsylC : IsSylowIn 2 ((T ⊓ Subgroup.normalizer (U₂ : Set G)) ⊓
          (M ⊓ Subgroup.centralizer (U₂ : Set G))) (M ⊓ Subgroup.centralizer (U₂ : Set G)) :=
        A4.isSylowTwoOf_inf_normal hSyl₂ (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
          (fun x hx => A4.mem_normalizer_inf (Subgroup.le_normalizer hx.1)
            (mem_normalizer_centralizer_ch62 hx.2))
      have hTC : (T ⊓ Subgroup.normalizer (U₂ : Set G)) ⊓ (M ⊓ Subgroup.centralizer (U₂ : Set G)) =
          T ⊓ Subgroup.centralizer (U₂ : Set G) := by
        ext x
        simp only [Subgroup.mem_inf]
        exact ⟨fun hx => ⟨hx.1.1, hx.2.2⟩, fun hx => ⟨⟨hx.1, Subgroup.centralizer_le_normalizer _
          hx.2⟩, h.T_le hx.1, hx.2⟩⟩
      rw [hTC] at hsylC
      have h1 := card_le_of_isSylowIn_ch62 hsylC
        (P := T' ⊓ Subgroup.centralizer (U₂ : Set G))
        (fun x hx => ⟨hCM hx.2, hx.2⟩) (hT'2.to_le inf_le_left)
      have h2 := relIndex_centralizer_le_two_ch62 hT'2 hT'N hU₂4
        (fun x hx => h.toHyp611.isElemAbelian.2 x (hU₂V hx))
      have h3 := Subgroup.relIndex_mul_card (T' ⊓ Subgroup.centralizer (U₂ : Set G)) T'
      rw [inf_of_le_left (inf_le_left : T' ⊓ Subgroup.centralizer (U₂ : Set G) ≤ T')] at h3
      have h4 := h.card_centralizer_mul_four_le_F4 h331 h615 hU₂V hU₂4 hne
      have hpos : 0 < Nat.card T := Nat.card_pos
      nlinarith
    ·
      have hm2 : mQuot V U₂ = 2 := by
        have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
        have h1 := card_eq_two_pow_mul hV2 hU₂V
        rw [h.natural.card_eq, hU₂4] at h1
        have : 2 ^ mQuot V U₂ = 4 := by omega
        have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4] at this
        exact Nat.pow_right_injective le_rfl this
      obtain ⟨t, -, -, -, ⟨-, -, -, -, hNsyl, hidx⟩, -⟩ :=
        h.lemma_6_2_4_one_five_F4 h331 h432 h615 h6110 hE612 hU₂V hm2 hC hSyl₂
      have h1 := card_le_of_isSylowIn_ch62 hNsyl hT'N hT'2
      rw [hT'card] at h1
      have heq : T ⊓ Subgroup.normalizer (U₂ : Set G) = T :=
        Subgroup.eq_of_le_of_card_ge inf_le_left h1 |>.symm ▸ rfl
      rw [heq, Subgroup.relIndex_self] at hidx
      exact absurd hidx (by norm_num)

  have hgm : g⁻¹ * m ∈ Subgroup.normalizer (Z : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← hU₂Z, hU₂eq]
  have hgmV : g⁻¹ * m ∈ Subgroup.normalizer (V : Set G) := h.normalizer_ZS_le_F4 h432 hgm
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := by
    have := Subgroup.mul_mem _ hgmV (Subgroup.inv_mem _ hmV)
    simpa using Subgroup.inv_mem _ this
  exact conjSubgroup_eq_iff_mem_normalizer.mpr hgV

theorem lemma_6_2_5_six_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) {Y : Subgroup G} (hYV : Y ≤ V)
    (hY : Y.relIndex V = 2) {g : G} (hYg : Y ≤ conjSubgroup V g) : conjSubgroup V g = V := by
  obtain ⟨l, hl, hle⟩ := h.exists_conj_ZS_le_of_hyperplane hYV hY
  have h1 : ch6ZS T L V ≤ conjSubgroup V (g * l⁻¹) := by
    have := conjSubgroup_mono_left l⁻¹ (hle.trans hYg)
    rwa [conjSubgroup_conj_inv, conjSubgroup_conjSubgroup] at this
  have h2 := h.lemma_6_2_5_four_F4 h331 h432 h615 h6110 hE612 h1
  have hlV : l ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.L_le_normalizer hl
  calc conjSubgroup V g = conjSubgroup (conjSubgroup V (g * l⁻¹)) l := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
    _ = conjSubgroup V l := by rw [h2]
    _ = V := conjSubgroup_eq_iff_mem_normalizer.mpr hlV

end Hyp6Sec2

end CFSG.Quasithin.H13
