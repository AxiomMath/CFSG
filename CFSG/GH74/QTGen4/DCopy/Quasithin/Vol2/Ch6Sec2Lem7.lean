module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem11
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem7A
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7B
public import CFSG.Quasithin.Vol2.Ch6Sec2Residuals

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem exists_frame_sylow_ch62_F4 (h331 : Stmt3_3_1_F4) (h6110 : Stmt6_1_10_F4) {g₀ : G}
    (hVT : V ≤ conjSubgroup T g₀) (hnc : ⁅V, conjSubgroup V g₀⁆ ≠ ⊥) :
    ∃ g : G, V ≤ conjSubgroup T g ∧ ⁅V, conjSubgroup V g⁆ ≠ ⊥ ∧
      IsSylowIn 2 (T ⊓ Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) : Subgroup G) : Set G))
        (M ⊓ Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
  set U₁ := V ⊓ Subgroup.centralizer (conjSubgroup V g₀ : Set G) with hU₁
  have hU₁V : U₁ ≤ V := inf_le_left
  obtain ⟨-, hm2, -⟩ := h.frame627_F4 h331 h6110 hVT hnc
  have hU₁1 : U₁ ≠ ⊥ := by
    intro h0
    have h1 := card_eq_two_pow_mul hV2 hU₁V
    rw [hm2, h0, Subgroup.card_bot, h.natural.card_eq] at h1
    norm_num at h1
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 2 (bot_le : ⊥ ≤ M ⊓ Subgroup.normalizer (U₁ : Set G))
    IsPGroup.of_bot
  obtain ⟨m, hm, hPT⟩ := h.toHyp611.exists_conj_sylow
    (hP.le.trans (h.toHyp611Nat.normalizer_le hU₁1 hU₁V)) hP.isPGroup
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hm.2
  have hmM : m ∈ M := hm.1
  have hVm : conjSubgroup V m = V := conjSubgroup_eq_iff_mem_normalizer.mpr hmV
  refine ⟨g₀ * m, ?_, ?_, ?_⟩
  · rw [← conjSubgroup_conjSubgroup]
    have := conjSubgroup_mono_left m hVT
    rwa [hVm] at this
  · intro h0
    apply hnc
    have h1 := conjSubgroup_commutator V (conjSubgroup V g₀) m
    rw [hVm, conjSubgroup_conjSubgroup, h0] at h1
    have h2 := congrArg (fun X => conjSubgroup X m⁻¹) h1
    simp only [conjSubgroup_conj_inv, conjSubgroup_bot] at h2
    exact h2
  ·
    have hU₂ : V ⊓ Subgroup.centralizer (conjSubgroup V (g₀ * m) : Set G) = conjSubgroup U₁ m := by
      rw [hU₁, conjSubgroup_inf, conjSubgroup_centralizer, hVm, conjSubgroup_conjSubgroup]
    rw [hU₂]
    have hNM : M ⊓ Subgroup.normalizer (conjSubgroup U₁ m : Set G) =
        conjSubgroup (M ⊓ Subgroup.normalizer (U₁ : Set G)) m := by
      rw [conjSubgroup_inf M, conjSubgroup_normalizer U₁ m,
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
    have hPm' : IsSylowIn 2 (conjSubgroup P m)
        (M ⊓ Subgroup.normalizer (conjSubgroup U₁ m : Set G)) := by
      rw [hNM]
      refine ⟨conjSubgroup_mono_left m hP.le, hP.isPGroup.map _, ?_⟩
      rw [relIndex_conjSubgroup]
      exact hP.not_dvd_relIndex
    refine ⟨inf_le_inf_right _ h.T_le, h.sylow.1.to_le inf_le_left, fun h2 =>
      hPm'.not_dvd_relIndex (h2.trans (Subgroup.relIndex_dvd_of_le_left _ ?_))⟩
    exact le_inf hPm (hPm'.le.trans inf_le_right)

theorem false_of_frame627_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) (hRes : Res627FF) {g : G}
    (hVT : V ≤ conjSubgroup T g) (hnc : ⁅V, conjSubgroup V g⁆ ≠ ⊥)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) : Subgroup G) : Set G))
        (M ⊓ Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) : Subgroup G) : Set G))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV := h.toHyp611.isElemAbelian
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  obtain ⟨-, hm2, -, -, -, -, hBg⟩ := h.frame627_F4 h331 h6110 hVT hnc
  obtain ⟨A, hA⟩ : ∃ A : Subgroup G, conjSubgroup V g = A := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Subgroup G, V ⊓ Subgroup.centralizer (A : Set G) = U := ⟨_, rfl⟩
  rw [hA, hU] at hSyl hm2
  rw [hA] at hnc hBg
  have hUV : U ≤ V := hU ▸ inf_le_left

  have hTA : conjSubgroup T g ≤ Subgroup.normalizer (A : Set G) := by
    rw [← hA, ← conjSubgroup_normalizer]
    exact conjSubgroup_mono_left g h.toHyp611.T_le_normalizer
  have hVA : V ≤ Subgroup.normalizer (A : Set G) := hVT.trans hTA
  have hAV : ¬ A ≤ Subgroup.normalizer (V : Set G) := by
    intro hle
    apply hnc
    rw [← hA] at hle hVA ⊢
    exact stmt6_2_3_F4 h432 (stmt6_1_11_F4 h432 h6110) G T M L V h g hVA hle
  have hAH : A ≤ Subgroup.centralizer (U : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rw [← hU] at hu
    exact (Subgroup.mem_centralizer_iff.mp hu.2 a ha).symm
  have hHN : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    fun hle => hAV (hAH.trans hle)

  obtain ⟨t, htT, ht, hUt, ⟨hchar, hRsyl, hRJ, hJM, hTUsyl, hTU2⟩, hW0R,
      ⟨hUHel, hUHO, hUHc, hCUH, hred⟩, ⟨hLU3, hLUO⟩⟩ :=
    h.lemma_6_2_4_one_five_F4 h331 h432 h615 h6110 hE612 hUV hm2 hHN hSyl
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set UH := conjClosure V H with hUHdef
  have hVUH : V ≤ UH := le_conjClosure V H
  have hHUH : H ≤ Subgroup.normalizer (UH : Set G) := le_normalizer_conjClosure V H

  have hBUH : ⁅V, A⁆ ≤ UH := by
    rw [Subgroup.commutator_le]
    intro v hv a ha
    rw [commutatorElement_def]
    have h1 : a * v⁻¹ * a⁻¹ ∈ UH :=
      (Subgroup.mem_normalizer_iff.mp (hHUH (hAH ha)) _).mp (UH.inv_mem (hVUH hv))
    have h2 := UH.mul_mem (hVUH hv) h1
    simpa [mul_assoc] using h2
  have hUHB : UH ≤ Subgroup.centralizer ((⁅V, A⁆ : Subgroup G) : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => B2F.isElemAbelian_comm hUHel (hBUH hb) hu

  have hNB : Subgroup.normalizer ((⁅V, A⁆ : Subgroup G) : Set G) ≤
      Subgroup.normalizer (A : Set G) := by
    rw [hBg, ← conjSubgroup_normalizer, ← hA, ← conjSubgroup_normalizer]
    exact conjSubgroup_mono_left g (h.normalizer_ZS_le_F4 h432)
  have hUHN : UH ≤ Subgroup.normalizer (A : Set G) :=
    hUHB.trans ((Subgroup.centralizer_le_normalizer _).trans hNB)

  have hTtop : IsSylowIn 2 T ⊤ :=
    ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
  have hTgtop : IsSylowIn 2 (conjSubgroup T g) ⊤ := by
    refine ⟨le_top, isPGroup_conjSubgroup h.sylow.1 g, ?_⟩
    rw [← conjSubgroup_top g, relIndex_conjSubgroup]
    exact hTtop.not_dvd_relIndex
  have hTgA : IsSylowIn 2 (conjSubgroup T g) (Subgroup.normalizer (A : Set G)) :=
    E6.isSylowIn_of_le hTgtop hTA le_top
  obtain ⟨x, hxA, hxUH⟩ := F7.isSylowTwoOf_exists_conj_le hTgA hUHN
    (B2F.isPGroup_of_isElemAbelian hUHel)
  set g' := g * x⁻¹ with hg'
  have hAg' : conjSubgroup V g' = A := by
    rw [hg', ← conjSubgroup_conjSubgroup, hA]
    exact conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ hxA)
  have hUHT : UH ≤ conjSubgroup T g' := by
    intro u hu
    have h1 := hxUH hu
    rw [CFSG.Quasithin.mem_conjSub] at h1
    rw [hg', ← conjSubgroup_conjSubgroup, mem_conjSubgroup_iff]
    simpa using h1
  have hVT' : V ≤ conjSubgroup T g' := hVUH.trans hUHT
  have hnc' : ⁅V, conjSubgroup V g'⁆ ≠ ⊥ := by rw [hAg']; exact hnc
  obtain ⟨-, -, hC3, hC5, hC6, hC7, hB'⟩ := h.frame627_F4 h331 h6110 hVT' hnc'
  rw [hAg'] at hC3 hC5 hC7 hB'

  have hBA : ⁅V, A⁆ ≤ A := by
    rw [hB', ← hAg']
    exact conjSubgroup_mono_left g' inf_le_left
  have hBcard : Nat.card (⁅V, A⁆ : Subgroup G) = 4 := by rw [hB', card_conjSubgroup, h.card_ZS_four]

  have hUHS : UH ≤ conjSubgroup (ch6S T L V) g' := by
    intro u hu
    rw [conjSubgroup_inf, conjSubgroup_centralizer, ← hB']
    exact ⟨hUHT hu, hUHB hu⟩
  have hdec : ∀ u ∈ UH, ∃ v ∈ V, ∃ c ∈ UH ⊓ Subgroup.centralizer (A : Set G), u = v * c := by
    intro u hu
    obtain ⟨v, hv, q, hq, huq⟩ := hC6 u (hUHS hu)
    have hqC : q ∈ Subgroup.centralizer (A : Set G) := by
      rw [conjSubgroup_inf, conjSubgroup_centralizer, hAg'] at hq
      exact hq.2
    have hqUH : q ∈ UH := by
      have := UH.mul_mem (UH.inv_mem (hVUH hv)) hu
      rwa [huq, inv_mul_cancel_left] at this
    exact ⟨v, hv, q, ⟨hqUH, hqC⟩, huq⟩
  have hUHeq : UH = V ⊔ (UH ⊓ Subgroup.centralizer (A : Set G)) := by
    apply le_antisymm
    · intro u hu
      obtain ⟨v, hv, c, hc, rfl⟩ := hdec u hu
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hc)
    · exact sup_le hVUH inf_le_left

  have hcommUH : ⁅UH, A⁆ = ⁅V, A⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro u hu a ha
      obtain ⟨v, hv, c, hc, rfl⟩ := hdec u hu
      have hca : c * a = a * c := (Subgroup.mem_centralizer_iff.mp hc.2 a ha).symm
      have e : ⁅v * c, a⁆ = ⁅v, a⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc v * c * a * (v * c)⁻¹ * a⁻¹ = v * (c * a) * c⁻¹ * v⁻¹ * a⁻¹ := by group
          _ = v * (a * c) * c⁻¹ * v⁻¹ * a⁻¹ := by rw [hca]
          _ = v * a * v⁻¹ * a⁻¹ := by group
      rw [e]
      exact Subgroup.commutator_mem_commutator hv ha
    · exact Subgroup.commutator_mono hVUH le_rfl

  have hUcard : Nat.card U = 4 := by
    have h1 := card_eq_two_pow_mul hV2 hUV
    rw [hm2, h.natural.card_eq] at h1
    omega
  have hmUH : mQuot UH (UH ⊓ Subgroup.centralizer (A : Set G)) = 2 := by
    set C := UH ⊓ Subgroup.centralizer (A : Set G) with hC
    have hCV : C ≤ Subgroup.normalizer (V : Set G) := by
      refine le_trans (fun c hc => ?_) (Subgroup.centralizer_le_normalizer (V : Set G))
      exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
        B2F.isElemAbelian_comm hUHel (hVUH hv) hc.1
    have h1 := card_sup_mul_card_inf_ch62 hCV
    have hVC : V ⊓ C = U := by
      rw [← hU, hC, ← inf_assoc, inf_of_le_left hVUH]
    rw [← hUHeq, hVC, hUcard, h.natural.card_eq] at h1
    have h2 := Subgroup.relIndex_mul_card (H := C) (K := UH)
    rw [inf_of_le_left (inf_le_left : C ≤ UH)] at h2
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have h4 : C.relIndex UH = 4 := by
      have : C.relIndex UH * Nat.card C * 4 = 4 * Nat.card C * 4 := by
        rw [h2]; linarith
      have h5 : C.relIndex UH * Nat.card C = 4 * Nat.card C := by omega
      exact Nat.eq_of_mul_eq_mul_right hCpos h5
    unfold mQuot
    rw [h4, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]

  have hU0 : ∀ U₀ : Subgroup G, UH ⊓ Subgroup.centralizer (A : Set G) < U₀ → U₀ ≤ UH →
      A ⊓ Subgroup.centralizer (U₀ : Set G) = ⁅V, A⁆ := by
    intro U₀ hlt hle
    obtain ⟨u₀, hu₀, hu₀C⟩ := IsConcreteLE.exists_of_lt hlt
    obtain ⟨v, hv, c, hc, rfl⟩ := hdec u₀ (hle hu₀)
    have hvC : v ∉ Subgroup.centralizer (A : Set G) := fun hvC' =>
      hu₀C ⟨hle hu₀, Subgroup.mul_mem _ hvC' hc.2⟩
    apply le_antisymm
    · rintro a ⟨ha, haC⟩
      have h1 : v * c * a = a * (v * c) := (Subgroup.mem_centralizer_iff.mp haC _ hu₀)
      have h2 : c * a = a * c := (Subgroup.mem_centralizer_iff.mp hc.2 a ha).symm
      have h3 : v * a = a * v := by
        have : v * a * c = a * v * c := by
          calc v * a * c = v * (a * c) := by group
            _ = v * (c * a) := by rw [h2]
            _ = v * c * a := by group
            _ = a * (v * c) := h1
            _ = a * v * c := by group
        exact mul_right_cancel this
      rw [hB']
      exact hC3 v hv hvC a ha h3
    · intro b hb
      refine ⟨hBA hb, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact B2F.isElemAbelian_comm hUHel (hle hy) (hBUH hb)

  have hNAV : A ⊓ Subgroup.normalizer (V : Set G) = ⁅V, A⁆ := by
    apply le_antisymm
    · rintro a ⟨ha, haN⟩
      by_contra haB
      rw [hB'] at haB
      have hBV : conjSubgroup (ch6ZS T L V) g' ≤ V := by
        intro z hz
        obtain ⟨v, hv, hvz⟩ := hC5 a ha haB z hz
        rw [← hvz]
        have h1 : a * v⁻¹ * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp haN _).mp (V.inv_mem hv)
        have h2 := V.mul_mem hv h1
        simpa [mul_assoc] using h2
      have hZV : ch6ZS T L V ≤ conjSubgroup V g'⁻¹ := by
        have := conjSubgroup_mono_left g'⁻¹ hBV
        rwa [conjSubgroup_conj_inv] at this
      have h1 := h.lemma_6_2_5_four_F4 h331 h432 h615 h6110 hE612 hZV
      have h2 : g' ∈ Subgroup.normalizer (V : Set G) := by
        have := conjSubgroup_eq_iff_mem_normalizer.mp h1
        simpa using Subgroup.inv_mem _ this
      apply hAV
      rw [← hAg', conjSubgroup_eq_iff_mem_normalizer.mpr h2]
      exact Subgroup.le_normalizer
    · intro b hb
      refine ⟨hBA hb, ?_⟩
      have : b ∈ A ⊓ Subgroup.centralizer (V : Set G) := by rw [hC7, ← hB']; exact hb
      exact Subgroup.centralizer_le_normalizer _ this.2

  have hO2R : pCoreOf 2 H ≤ ch6Q T V ⊔ Subgroup.zpowers t := pCoreOf_le_of_isSylowIn hRsyl
  have hRT : ch6Q T V ⊔ Subgroup.zpowers t ≤ T :=
    sup_le inf_le_left (Subgroup.zpowers_le.mpr htT)
  have hCA : A ⊓ centralizerMod U H UH = ⁅V, A⁆ := by
    apply le_antisymm
    · rintro a ⟨ha, haC⟩
      rw [hCUH] at haC
      rw [← hNAV]
      exact ⟨ha, h.toHyp611.T_le_normalizer (hRT (hO2R haC))⟩
    · intro b hb
      refine ⟨hBA hb, mem_centralizerMod.mpr ⟨hAH (hBA hb), ?_, fun u hu => ?_⟩⟩
      · exact Subgroup.centralizer_le_normalizer _ (hAH (hBA hb))
      · rw [B2F.isElemAbelian_comm hUHel (hBUH hb) hu, mul_inv_cancel_right, mul_inv_cancel]
        exact U.one_mem

  set LU := oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G)) with hLUdef
  have h3dvd : 3 ∣ Nat.card LU := ⟨_, hLU3⟩
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  set d : G := (x₃ : G) with hd
  have hdo : orderOf d = 3 := by rw [hd, Subgroup.orderOf_coe, hx₃]
  have hdLU : d ∈ LU := x₃.2
  have hdLN : d ∈ L ⊓ Subgroup.normalizer (U : Set G) := oTwoUpper_le _ hdLU
  have hd3 : d ^ 3 = 1 := by rw [← hdo]; exact pow_orderOf_eq_one d
  have hdC : d ∉ Subgroup.centralizer (V : Set G) := by
    intro hdC'
    have hdH : d ∈ H := Subgroup.centralizer_le (show (U : Set G) ⊆ V from hUV) hdC'
    have hdO : d ∈ pCoreOf 2 LU := by rw [hLUO]; exact ⟨hdLU, hdH⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 LU) ⟨d, hdO⟩
    have hdk : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : 3 ∣ 2 ^ k := hdo ▸ orderOf_dvd_of_pow_eq_one hdk
    have h2 : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have := Nat.Coprime.eq_one_of_dvd h2 h1
    omega
  have hdV : d ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.L_le_normalizer hdLN.1
  have hfree : ∀ w ∈ V, d * w = w * d → w = 1 := fun w hw hdw =>
    h.toHyp611Nat.eq_one_of_commute_of_pow_three_ch62 hdLN.1 hd3 hdC hw hdw
  have hVd : ∀ v ∈ V, ∃ w ∈ V, w * d * w⁻¹ * d⁻¹ = v := fun v hv =>
    exists_eq_commutator_of_free_ch62 hV hdV hfree hv
  set D := Subgroup.zpowers d with hDdef
  have hDLU : D ≤ LU := Subgroup.zpowers_le.mpr hdLU
  have hDcard : Nat.card D = 3 := by rw [hDdef, Nat.card_zpowers, hdo]
  have hVD : ⁅V, D⁆ = V := by
    apply le_antisymm
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hdV)
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := hVd v hv
      have := Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers d)
      rwa [commutatorElement_def] at this

  have hdUH : d ∈ Subgroup.normalizer (UH : Set G) :=
    mem_normalizer_conjClosure_ch62 hdV (mem_normalizer_centralizer_ch62 hdLN.2)
  have hclaim : ∀ K : Subgroup G, K ≤ H → A ≤ K →
      (∀ k ∈ K, ∀ d' ∈ D, k * d' * k⁻¹ * d'⁻¹ ∈
        centralizerMod U (Subgroup.normalizer (U : Set G)) UH) →
      ¬ ⁅⁅UH, K⁆, D⁆ ≤ U := by
    intro K hKH hAK hKD hcomm
    exact hAV (hAK.trans (le_normalizer_of_commutator_le_ch62 hUHel hVUH hUV
      (hKH.trans hHUH) (Subgroup.mem_zpowers d) hdUH hVd hKD hcomm))

  subst hUt
  exact hRes G T M L V h t A D g' htT ht hSyl hchar hRsyl hRJ hJM hTUsyl hTU2 hW0R hUHel hUHO
    hUHc hCUH hred hLU3 hLUO hAg'.symm hVA hAV hU hAH hUHT hB' hBcard hNAV hUHN hUHeq hcommUH
    hmUH hU0 hCA hDLU hDcard hVD hclaim

theorem wClos_le_Q_ch62_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) (hRes : Res627FF) : wClos V 0 T ≤ ch6Q T V := by
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
  refine wClos_le_of_forall fun X hX => ?_
  obtain ⟨hXT, g₀, hXg, hm0⟩ := hX
  have hXeq : X = conjSubgroup V g₀ :=
    (mQuot_eq_zero_iff (isPGroup_conjSubgroup hV2 g₀) hXg).mp hm0
  subst hXeq
  refine le_inf hXT ?_
  by_contra hXC
  have hVT : V ≤ conjSubgroup T g₀⁻¹ := by
    have := conjSubgroup_mono_left g₀⁻¹ hXT
    rwa [conjSubgroup_conj_inv] at this
  have hnc : ⁅V, conjSubgroup V g₀⁻¹⁆ ≠ ⊥ := by
    intro h0
    apply hXC
    have h1 := conjSubgroup_commutator V (conjSubgroup V g₀⁻¹) g₀
    rw [h0, conjSubgroup_bot, conjSubgroup_inv_conj] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1.symm
  obtain ⟨g, hVT', hnc', hSyl⟩ := h.exists_frame_sylow_ch62_F4 h331 h6110 hVT hnc
  exact h.false_of_frame627_F4 h331 h432 h615 h6110 hE612 hRes hVT' hnc' hSyl

end Hyp6Sec2

theorem stmt6_2_7_of_res_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) (hRes : Res627FF) : Stmt6_2_7_F4 := by
  intro G _ _ T M L V h
  have hWQ := h.wClos_le_Q_ch62_F4 h331 h432 h615 h6110 hE612 hRes
  refine ⟨hWQ, h.toHyp611.centralizer_eq, ?_⟩
  have hU := h.toHyp611.isUniqueM_F4 h432
  have hQ := h.toHyp611.centralizer_eq
  have hQ1 : ch6Q T V ≠ ⊥ := by rw [hQ]; exact h.maximal.1.2.2.2
  have hQ2 : IsPGroup 2 (ch6Q T V) := h.sylow.1.to_le inf_le_left
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [hQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hNQ : IsUniqueM (Subgroup.normalizer (ch6Q T V : Set G)) M :=
    ⟨⟨h.maxTwoLocal, le_of_isUniqueM_of_le_twoLocal hU hLTQ ⟨_, hQ1, hQ2, rfl⟩⟩,
      fun M' hM' => hU.2 M' ⟨hM'.1, hLTQ.trans hM'.2⟩⟩
  have hVW : V ≤ wClos V 0 T :=
    le_wClos (mem_gammaSet_iff.mpr ⟨h.toHyp611.le_T, 1, (conjSubgroup_one V).ge,
      by rw [conjSubgroup_one, mQuot_self]⟩)
  have hW0 : wClos V 0 T ≠ ⊥ := fun h0 => h.toHyp611.ne_bot (eq_bot_iff.mpr (h0 ▸ hVW))
  have hTT : IsSylowIn 2 T T :=
    E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
      le_rfl le_top
  exact (e3_16_one hTT inf_le_left hQ2 hWQ hW0 hNQ).2

end CFSG.Quasithin.H13
