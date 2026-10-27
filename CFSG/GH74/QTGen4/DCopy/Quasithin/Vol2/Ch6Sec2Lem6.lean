module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem6A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem conjSub_eq_of_hyperplane_ch626_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) {y k : G} {F : Subgroup G} (hFY : F ≤ conjSub y V)
    (hF2 : F.relIndex (conjSub y V) = 2) (hFk : F ≤ conjSub k V) : conjSub k V = conjSub y V := by
  have hF'V : conjSub y⁻¹ F ≤ V := by
    have := conjSub_mono y⁻¹ hFY
    rwa [conjSub_conjSub_inv] at this
  have hF'2 : (conjSub y⁻¹ F).relIndex V = 2 := by
    have := relIndex_conjSub_ch62 y⁻¹ F (conjSub y V)
    rw [conjSub_conjSub_inv] at this
    rw [this, hF2]
  have hF'k : conjSub y⁻¹ F ≤ conjSubgroup V (y⁻¹ * k)⁻¹ := by
    rw [conjSubgroup_eq_conjSub_ch62, inv_inv, conjSub_mul]
    exact conjSub_mono _ hFk
  have h1 := h.lemma_6_2_5_six_F4 h331 h432 h615 h6110 hE612 hF'V hF'2 hF'k
  rw [conjSubgroup_eq_conjSub_ch62, inv_inv] at h1
  calc conjSub k V = conjSub y (conjSub (y⁻¹ * k) V) := by
        rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub y V := by rw [h1]

theorem exists_ne_one_inf_pair626_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) {x y : G}
    (hA : (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)).relIndex (conjSub y V) = 2)
    (hU : (conjSub x V ⊓ Subgroup.normalizer (conjSub y V : Set G)).relIndex (conjSub x V) = 2) :
    ∃ c ∈ conjSub x V ⊓ conjSub y V, c ≠ 1 := by
  obtain ⟨a, ha, haC⟩ := IsConcreteLE.not_le_iff_exists.mp
    (h.not_le_centralizer_pair626_F4 h331 h432 h615 h6110 hE612 hA hU)
  by_contra hcon
  push Not at hcon
  have hle : conjSub x V ⊓ Subgroup.normalizer (conjSub y V : Set G) ≤
      conjSub x V ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro u hu
    refine ⟨hu.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := hcon _ (Pair626.comm_mem_B' ha hu)
    calc u * a = u * a * u⁻¹ * a⁻¹ * (a * u) := by group
      _ = a * u := by rw [h1, one_mul]
  have h4 := h.card_fix_conj_le_four_F4 h432 x ha.2 haC
  have h8 := Subgroup.card_le_of_le hle
  rw [h.card_A_pair626 hU] at h8
  omega

theorem relIndex_two_or_four_pair626_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) {x y : G}
    (hA : (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)).relIndex (conjSub y V) = 2)
    (hU : (conjSub x V ⊓ Subgroup.normalizer (conjSub y V : Set G)).relIndex (conjSub x V) = 2) :
    (Subgroup.centralizer (conjSub x V : Set G)).relIndex
        (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)) = 2 ∨
      (Subgroup.centralizer (conjSub x V : Set G)).relIndex
        (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := conjSub x V with hX
  set Y := conjSub y V with hY
  set A := Y ⊓ Subgroup.normalizer (X : Set G) with hAdef
  have hX2 : IsElemAbelian 2 X := h.isElemAbelian_conjSub_V x
  have hY2 : IsPGroup 2 Y := B2F.isPGroup_of_isElemAbelian (h.isElemAbelian_conjSub_V y)
  have hAc : Nat.card A = 8 := h.card_A_pair626 hA
  obtain ⟨c, hc, hc1⟩ := h.exists_ne_one_inf_pair626_F4 h331 h432 h615 h6110 hE612 hA hU
  have hcA : c ∈ Subgroup.centralizer (X : Set G) ⊓ A :=
    ⟨Subgroup.mem_centralizer_iff.mpr fun z hz => B2F.isElemAbelian_comm hX2 hz hc.1,
      hc.2, Subgroup.le_normalizer hc.1⟩
  have h2 : 2 ≤ Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ A) := by
    have hne : Subgroup.centralizer (X : Set G) ⊓ A ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.mem_bot] at hcA
      exact hc1 hcA
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (X : Set G)) (K := A)
  rw [hAc] at h1
  have hne : (Subgroup.centralizer (X : Set G)).relIndex A ≠ 1 := fun h0 =>
    h.not_le_centralizer_pair626_F4 h331 h432 h615 h6110 hE612 hA hU
      (Subgroup.relIndex_eq_one.mp h0)
  have hpow := relIndex_eq_two_pow (hY2.to_le inf_le_left : IsPGroup 2 A)
    (Subgroup.centralizer (X : Set G))
  rw [hpow] at h1 hne ⊢
  rcases Nat.lt_or_ge (mQuot A (Subgroup.centralizer (X : Set G))) 3 with hlt | hge
  · interval_cases hm : mQuot A (Subgroup.centralizer (X : Set G))
    · simp at hne
    · left; rfl
    · right; rfl
  · exfalso
    have h8 : 2 ^ 3 ≤ 2 ^ mQuot A (Subgroup.centralizer (X : Set G)) :=
      Nat.pow_le_pow_right (by norm_num) hge
    have : 2 ^ 3 * 2 ≤ 2 ^ mQuot A (Subgroup.centralizer (X : Set G)) *
        Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ A) := Nat.mul_le_mul h8 h2
    omega

theorem pair626_of_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) {x y : G}
    (hA : (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)).relIndex (conjSub y V) = 2)
    (hU : (conjSub x V ⊓ Subgroup.normalizer (conjSub y V : Set G)).relIndex (conjSub x V) = 2)
    (hA4 : (Subgroup.centralizer (conjSub x V : Set G)).relIndex
      (conjSub y V ⊓ Subgroup.normalizer (conjSub x V : Set G)) = 4) :
    Pair626 (conjSub x V) (conjSub y V) := by
  have hU4 : (Subgroup.centralizer (conjSub y V : Set G)).relIndex
      (conjSub x V ⊓ Subgroup.normalizer (conjSub y V : Set G)) = 4 := by
    rcases h.relIndex_two_or_four_pair626_F4 h331 h432 h615 h6110 hE612 hU hA with h2 | h4
    · have := h.relIndex_two_pair626_F4 h331 h432 h615 h6110 hE612 hU hA h2
      rw [hA4] at this
      norm_num at this
    · exact h4
  set X := conjSub x V with hX
  set Y := conjSub y V with hY
  have hXel : IsElemAbelian 2 X := h.isElemAbelian_conjSub_V x
  have hYel : IsElemAbelian 2 Y := h.isElemAbelian_conjSub_V y
  have hCA : Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓
      (Y ⊓ Subgroup.normalizer (X : Set G))) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (X : Set G))
      (K := Y ⊓ Subgroup.normalizer (X : Set G))
    rw [hA4, h.card_A_pair626 hA] at h1
    omega
  have hCU : Nat.card ↥(Subgroup.centralizer (Y : Set G) ⊓
      (X ⊓ Subgroup.normalizer (Y : Set G))) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (Y : Set G))
      (K := X ⊓ Subgroup.normalizer (Y : Set G))
    rw [hU4, h.card_A_pair626 hU] at h1
    omega
  have hBA : X ⊓ Y ≤ Subgroup.centralizer (X : Set G) ⊓ (Y ⊓ Subgroup.normalizer (X : Set G)) :=
    fun b hb => ⟨Subgroup.mem_centralizer_iff.mpr fun z hz => B2F.isElemAbelian_comm hXel hz hb.1,
      hb.2, Subgroup.le_normalizer hb.1⟩
  have hBU : X ⊓ Y ≤ Subgroup.centralizer (Y : Set G) ⊓ (X ⊓ Subgroup.normalizer (Y : Set G)) :=
    fun b hb => ⟨Subgroup.mem_centralizer_iff.mpr fun z hz => B2F.isElemAbelian_comm hYel hz hb.2,
      hb.1, Subgroup.le_normalizer hb.2⟩
  obtain ⟨c, hc, hc1⟩ := h.exists_ne_one_inf_pair626_F4 h331 h432 h615 h6110 hE612 hA hU
  have hB2 : 2 ≤ Nat.card ↥(X ⊓ Y) := by
    have hne : X ⊓ Y ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.mem_bot] at hc
      exact hc1 hc
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hBc : Nat.card ↥(X ⊓ Y) = 2 :=
    le_antisymm ((Subgroup.card_le_of_le hBA).trans hCA.le) hB2
  have hBeqA := Subgroup.eq_of_le_of_card_ge hBA (by rw [hCA, hBc])
  have hBeqU := Subgroup.eq_of_le_of_card_ge hBU (by rw [hCU, hBc])
  refine
    { elemX := hXel
      elemY := hYel
      cardX := h.card_conjSub_V x
      cardY := h.card_conjSub_V y
      idxA := hA
      idxU := hU
      cardB := hBc
      centA := fun a ha haC => ?_
      centU := fun u hu huC => ?_
      fixX := fun a ha haC => h.card_fix_conj_le_four_F4 h432 x ha.2 haC
      fixY := fun u hu huC => h.card_fix_conj_le_four_F4 h432 y hu.2 huC
      uniqX := fun k hk => ?_
      uniqY := fun k hk => ?_
      conjXY := ⟨y * x⁻¹, by rw [hX, hY, conjSub_mul, conjSub_conjSub_inv]⟩ }
  · have : a ∈ X ⊓ Y := by rw [hBeqA]; exact ⟨haC, ha⟩
    exact this.1
  · have : u ∈ X ⊓ Y := by rw [hBeqU]; exact ⟨huC, hu⟩
    exact this.2
  · have := h.conjSub_eq_of_hyperplane_ch626_F4 h331 h432 h615 h6110 hE612 (y := x) (k := k * x)
      inf_le_left hU (by rw [conjSub_mul]; exact hk)
    rwa [conjSub_mul] at this
  · have := h.conjSub_eq_of_hyperplane_ch626_F4 h331 h432 h615 h6110 hE612 (y := y) (k := k * y)
      inf_le_left hA (by rw [conjSub_mul]; exact hk)
    rwa [conjSub_mul] at this

end Hyp6Sec2

theorem stmt6_2_6_of_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) : Stmt6_2_6_F4 := by
  intro G _ _ T M L V h g
  dsimp only
  intro hA hU
  have e1 : conjSub 1 V = V := conjSub_one V
  have e2 : conjSub g⁻¹ V = conjSubgroup V g := (conjSubgroup_eq_conjSub_ch62 V g).symm
  have hA' : (conjSub g⁻¹ V ⊓ Subgroup.normalizer (conjSub 1 V : Set G)).relIndex
      (conjSub g⁻¹ V) = 2 := by rw [e1, e2]; exact hA
  have hU' : (conjSub 1 V ⊓ Subgroup.normalizer (conjSub g⁻¹ V : Set G)).relIndex
      (conjSub 1 V) = 2 := by rw [e1, e2]; exact hU
  have hV2 : IsElemAbelian 2 V := h.toHyp611.isElemAbelian
  have hVg2 : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup hV2 g
  rcases h.relIndex_two_or_four_pair626_F4 h331 h432 h615 h6110 hE612 hA' hU' with h2 | h4
  · left
    have h2U := h.relIndex_two_pair626_F4 h331 h432 h615 h6110 hE612 hA' hU' h2
    obtain ⟨hmA, hHA⟩ := h.fieldType_data_pair626 hA' hU' h2
    obtain ⟨hmU, hHU⟩ := h.fieldType_data_pair626 hU' hA' h2U
    rw [e1, e2] at h2 h2U hmA hHA hmU hHU
    have hAV : (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ⊓
        Subgroup.centralizer (V : Set G) ≤ conjSubgroup V g := inf_le_left.trans inf_le_left
    have hUV : (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) ⊓
        Subgroup.centralizer (conjSubgroup V g : Set G) ≤ V := inf_le_left.trans inf_le_left
    refine ⟨by rw [Subgroup.inf_relIndex_left]; exact h2,
      by rw [Subgroup.inf_relIndex_left]; exact h2U,
      h.isFieldType_conj_F4 h331 h432 h615 h6110 hE612 g hAV hmA hHA,
      h.isFieldType_one_F4 h331 h432 h615 h6110 hE612 hUV hmU hHU, ?_⟩

    set U₀ := (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) ⊓
      Subgroup.centralizer (conjSubgroup V g : Set G) with hU₀
    have hVO := h.le_pCoreOf_centralizer_of_fieldType_F4 h331 h432 h615 h6110 hE612 hUV hmU hHU
    have hVgC : conjSubgroup V g ≤ Subgroup.centralizer (U₀ : Set G) := fun z hz =>
      Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_iff.mp hu.2 z hz).symm
    have hVgN : conjSubgroup V g ≤
        Subgroup.normalizer (pCoreOf 2 (Subgroup.centralizer (U₀ : Set G)) : Set G) :=
      hVgC.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 _))
    have hP := IsPGroup.to_sup_of_normal_left'
      (pCoreOf_isPGroup 2 (Subgroup.centralizer (U₀ : Set G)))
      (B2F.isPGroup_of_isElemAbelian hVg2) hVgN
    exact hP.to_le (sup_le_sup_right hVO _)
  · right
    have hp := h.pair626_of_F4 h331 h432 h615 h6110 hE612 hA' hU' h4
    rw [e1, e2] at hp h4
    obtain ⟨φ, hφ, hker⟩ := hp.exists_surjective_perm_three
    refine ⟨by rw [Subgroup.inf_relIndex_left]; exact h4, fun u hu v hv => ?_,
      h.not_autOn_le_pair626 hp,
      ⟨(V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) ⊔
          (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)),
        sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right),
        hp.sup_le_normalizer_Q, hp.isExtraspecialPlus, φ, hφ, hker⟩,
      hp.commutator_eq, hp.cardB, hp.pCoreOf_le_oTwoUpper⟩
    have huv : u * v = v * u := B2F.isElemAbelian_comm hVg2 hu.1 hv.1
    have hu2 : u ^ 2 = 1 := hVg2.2 u hu.1
    refine ⟨?_, ?_⟩
    · have e : u * v * u⁻¹ * v⁻¹ = 1 := by rw [huv]; group
      rw [e]
      exact Subgroup.one_mem _
    · rw [hu2]
      exact Subgroup.one_mem _

end CFSG.Quasithin.H13
