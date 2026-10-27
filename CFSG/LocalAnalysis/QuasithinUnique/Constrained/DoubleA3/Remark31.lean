module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma30Five
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraConfining

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

section A4

variable {G : Type} [Group G]

theorem IsA4Block.le_normalizer {L U : Subgroup G} (h : IsA4Block L U) :
    L ≤ normalizer (U : Set G) := by
  obtain ⟨c, -, -, hcN, -, hLc⟩ := h.exists_c
  rw [hLc]; exact sup_le Subgroup.le_normalizer (zpowers_le.mpr hcN)

theorem IsA4Block.mem_of_commute [Finite G] {L U : Subgroup G} (h : IsA4Block L U) {l w : G}
    (hl : l ∈ L) (hw : w ∈ U) (hw1 : w ≠ 1) (hc : l * w = w * l) : l ∈ U := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hlmem : l ∈ ((zpowers c ⊔ U : Subgroup G) : Set G) := by
    have : l ∈ zpowers c ⊔ U := by rw [sup_comm, ← hLc]; exact hl
    exact this
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (zpowers c) U (zpowers_le.mpr hcN)] at hlmem
  obtain ⟨y, hy, u', hu', hyu0⟩ := hlmem
  have hyu : y * u' = l := hyu0
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hck : c ^ k * w = w * c ^ k := by
    have h2 : u' * w = w * u' := h.comm_U u' hu' w hw
    have h3 : (c ^ k * u') * w = w * (c ^ k * u') := by rw [hyu]; exact hc
    have h4 : (c ^ k * w) * u' = (w * c ^ k) * u' := by
      calc (c ^ k * w) * u' = c ^ k * (w * u') := by group
        _ = c ^ k * (u' * w) := by rw [h2]
        _ = (c ^ k * u') * w := by group
        _ = w * (c ^ k * u') := h3
        _ = (w * c ^ k) * u' := by group
    exact mul_right_cancel h4
  have hk : c ^ k = c ^ (k % 3) := by
    have := zpow_mod_orderOf c k
    rw [hc3] at this
    simpa using this.symm
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h0 | h0
  · have : c ^ k = 1 := by rw [hk, h0, zpow_zero]
    rw [← hyu, this, one_mul]
    exact hu'
  · exfalso
    have hcc : c * w = w * c := by
      rwa [hk, h0, zpow_one] at hck
    apply hcfp w hw hw1
    calc c * w * c⁻¹ = w * c * c⁻¹ := by rw [hcc]
      _ = w := by group
  · exfalso
    have hcc2 : c ^ 2 * w = w * c ^ 2 := by
      rw [hk, h0] at hck
      simpa [zpow_two, pow_two] using hck
    have hc4 : c = c ^ 2 * c ^ 2 := by
      calc c = c * c ^ 3 := by rw [hc3', mul_one]
        _ = c ^ 2 * c ^ 2 := by group
    apply hcfp w hw hw1
    have hcc : c * w = w * c := by
      calc c * w = (c ^ 2 * c ^ 2) * w := by rw [← hc4]
        _ = c ^ 2 * (c ^ 2 * w) := by group
        _ = c ^ 2 * (w * c ^ 2) := by rw [hcc2]
        _ = (c ^ 2 * w) * c ^ 2 := by group
        _ = (w * c ^ 2) * c ^ 2 := by rw [hcc2]
        _ = w * (c ^ 2 * c ^ 2) := by group
        _ = w * c := by rw [← hc4]
    calc c * w * c⁻¹ = w * c * c⁻¹ := by rw [hcc]
      _ = w := by group

theorem charTwo_sup_of_a4 [Finite G] {Y U B Q W : Subgroup G} (hY : IsA4Block Y U)
    (R1 : C5.Rank1 B Q U W 2) (hB2 : IsPGroup 2 B) (hBY : B ≤ normalizer (Y : Set G)) :
    CharTwo (Y ⊔ B) ∧ pCoreOf 2 (Y ⊔ B) ≠ ⊥ := by
  have hUB : U ≤ B := R1.U_le_B
  set P₀ : Subgroup G := U ⊔ (B ⊓ centralizer (Y : Set G)) with hP₀
  have hP₀B : P₀ ≤ B := sup_le hUB inf_le_left
  have hP₀2 : IsPGroup 2 ↥P₀ := hB2.to_le hP₀B
  have hYU : Y ≤ normalizer (U : Set G) := hY.le_normalizer
  have hYC : Y ≤ normalizer ((B ⊓ centralizer (Y : Set G) : Subgroup G) : Set G) :=
    C5.le_normalizer_of_commute fun y hy a ha => Subgroup.mem_centralizer_iff.mp ha.2 y hy
  have hBU : B ≤ normalizer (U : Set G) := R1.B_le_normU
  have hBC : B ≤ normalizer ((B ⊓ centralizer (Y : Set G) : Subgroup G) : Set G) := fun r hr =>
    C5.mem_normalizer_inf (Subgroup.le_normalizer hr) (C5.mem_normalizer_centralizer (hBY hr))
  have hXN : Y ⊔ B ≤ normalizer (P₀ : Set G) := by
    refine sup_le (fun y hy => ?_) (fun r hr => ?_)
    · exact C1.mem_normalizer_sup (hYU hy) (hYC hy)
    · exact C1.mem_normalizer_sup (hBU hr) (hBC hr)
  have hP₀X : P₀ ≤ Y ⊔ B := hP₀B.trans le_sup_right
  have hP₀P : P₀ ≤ pCoreOf 2 (Y ⊔ B) := le_pCoreOf_of_normalizes hP₀X hXN hP₀2
  have hUne : U ≠ ⊥ := by
    intro h
    have := hY.card_U
    rw [h, Subgroup.card_bot] at this
    omega
  refine ⟨?_, fun hbot => hUne (le_bot_iff.mp ((le_sup_left.trans hP₀P).trans hbot.le))⟩
  unfold CharTwo
  rintro y ⟨hyX, hyC⟩
  have hyU : ∀ u ∈ U, y * u = u * y := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp hyC u (hP₀P (mem_sup_left hu))).symm
  have hy' : y ∈ ((B ⊔ Y : Subgroup G) : Set G) := by rw [sup_comm]; exact hyX
  rw [Subgroup.coe_mul_of_left_le_normalizer_right B Y hBY] at hy'
  obtain ⟨r, hr, l, hl, hrl0⟩ := hy'
  have hrl : r * l = y := hrl0
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hcon
    have hWbot : W = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      by_contra hg1
      exact hcon ⟨g, hg, fun h => hg1 (by rw [h]; exact one_mem _)⟩
    have h1 := R1.idx_W
    have h2 := C5.card_eq_card_mul_relIndex R1.W_le_U
    rw [h1, hWbot, Subgroup.card_bot, hY.card_U] at h2
    omega
  have hwU : w ∈ U := R1.W_le_U hwW
  have hrw : w * r = r * w := by
    by_cases hrQ : r ∈ Q
    · exact R1.Q_cent r hrQ w hwU
    · exact (R1.cent_y r hr hrQ w hwU).mp hwW
  have hlw : l * w = w * l := by
    have h1 : r * l * w = w * (r * l) := by rw [hrl]; exact hyU w hwU
    calc l * w = r⁻¹ * (r * l * w) := by group
      _ = r⁻¹ * (w * (r * l)) := by rw [h1]
      _ = r⁻¹ * (w * r) * l := by group
      _ = r⁻¹ * (r * w) * l := by rw [hrw]
      _ = w * l := by group
  have hlU : l ∈ U := hY.mem_of_commute hl hwU hw1 hlw
  have hrU : ∀ u ∈ U, r * u = u * r := by
    intro u hu
    have h1 : r * l * u = u * (r * l) := by rw [hrl]; exact hyU u hu
    have h2 : l * u = u * l := hY.comm_U l hlU u hu
    calc r * u = r * l * u * l⁻¹ := by
          calc r * u = r * (u * l) * l⁻¹ := by group
            _ = r * (l * u) * l⁻¹ := by rw [h2]
            _ = r * l * u * l⁻¹ := by group
      _ = u * (r * l) * l⁻¹ := by rw [h1]
      _ = u * r := by group
  obtain ⟨u₀, hu₀U, hu₀⟩ := hY.exists_inner (hBY hr) hrU
  have hcent : u₀⁻¹ * r ∈ B ⊓ centralizer (Y : Set G) := by
    refine ⟨mul_mem (B.inv_mem (hUB hu₀U)) hr, Subgroup.mem_centralizer_iff.mpr fun l' hl' => ?_⟩
    have h1 := hu₀ l' hl'
    calc l' * (u₀⁻¹ * r) = u₀⁻¹ * (u₀ * l' * u₀⁻¹) * r := by group
      _ = u₀⁻¹ * (r * l' * r⁻¹) * r := by rw [h1]
      _ = (u₀⁻¹ * r) * l' := by group
  have hyP : y ∈ P₀ := by
    have : y = u₀ * (u₀⁻¹ * r) * l := by rw [← hrl]; group
    rw [this]
    exact mul_mem (mul_mem (mem_sup_left hu₀U) (mem_sup_right hcent)) (mem_sup_left hlU)
  exact hP₀P hyP

end A4

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s x z₁ z₂ : G}

structure Basic31 (T M H S L : Subgroup G) (s : G) : Prop where
  idx_T : S.relIndex T = 2
  idx_R : (baum S).relIndex S = 2
  S_eq : S = baum S ⊔ zpowers s
  card_T : Nat.card T = 4 * Nat.card (baum S)
  hbJ : baum S = thompsonJ S
  hJT : thompsonJ S = thompsonJ T
  hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L)
  hbD : baumD S L = blockD S L
  hQ : pCoreOf 2 H = blockD S L ⊔ blockU0 S L
  N_eq : S ⊓ normalizer (L : Set G) = baum S
  Q_le_R : pCoreOf 2 H ≤ baum S
  card_R_Q : Nat.card ↥(baum S) = 4 * Nat.card ↥(pCoreOf 2 H)

theorem basic31 (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hcfg : A3A3 T M H S L s) : Basic31 T M H S L s := by
  have hcs := hcfg.cs
  have h3 := hcfg.a3
  have hne : conjJoin S L ≠ L := hcfg.conjJoin_ne
  obtain ⟨hidx, hbJ, hJT⟩ := h27_1 G T M H S L hcs h3 hne
  obtain ⟨hU0, -, hbD, hQ, -, -, -⟩ := hD G T M H S L hcs h3 hne T hcs.le_T le_rfl hidx
  have hQ' : pCoreOf 2 H = blockD S L ⊔ blockU0 S L := by rw [← hbD]; exact hQ
  obtain ⟨hN, hRQ⟩ := normalizer_eq_baum hD hcfg hU0 hbD hQ' hidx
  obtain ⟨hRS, hSeq, hcardT⟩ := lemma2_4_30_five hD h27_1 G T M H S L s hcfg
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hcfg.s_mem
  have hU₂B : blockU2 L s ≤ baum S :=
    (C5.conjSubgroup_mono hUB s).trans (le_of_eq (C5.conjSubgroup_eq_self hsB))
  have hDB : blockD S L ≤ baum S := by rw [← hbD]; exact inf_le_left
  have hQR : pCoreOf 2 H ≤ baum S := by
    rw [hQ']
    exact sup_le hDB (by rw [hcfg.blockU0_eq hU0]; exact sup_le hUB hU₂B)
  exact ⟨hidx, hRS, hSeq, hcardT, hbJ, hJT, hU0, hbD, hQ', hN, hQR, hRQ⟩

theorem isConfining_baum (hcs : ConstrainedSetting G T M H S L) (hB : Basic31 T M H S L s) :
    pCoreOf 2 M ⊓ centralizer (baum S : Set G) ≤ baum S ∧ IsConfining M (baum S) := by
  have hC := hcs.gamma0.pCore_centralizer_le_of_charTwo hcs.setting hcs.sylow_inf hcs.charTwo
    hB.Q_le_R
  exact ⟨hC, IsGamma0.isConfining_of_relIndex_two hcs.setting hcs.gamma0 hcs.sylow_inf
    hB.hbJ.ge inf_le_left hB.idx_R hC⟩

theorem isWitnessPair_baum_sup {Y U Q W : Subgroup G}
    (hβ : IsConfining M (baum S)) (hB2 : IsPGroup 2 (baum S)) (hY : IsA4Block Y U)
    (R1 : C5.Rank1 (baum S) Q U W 2) (hBY : baum S ≤ normalizer (Y : Set G)) (hYM : ¬ Y ≤ M) :
    IsWitnessPair M (baum S) (Y ⊔ baum S) := by
  obtain ⟨hct, hcore⟩ := charTwo_sup_of_a4 hY R1 hB2 hBY
  exact ⟨hβ, le_sup_right, hcore, hct, fun h => hYM (le_sup_left.trans h)⟩

section Elements

variable (hA : A3A3x T M H S L s x z₁ z₂)
include hA

theorem A3A3x.z₁_mem : z₁ ∈ blockU L ∧ z₁ ∈ centralizer (baum S : Set G) := by
  have : z₁ ∈ blockU L ⊓ centralizer (baum S : Set G) := by
    rw [← hA.z₁_gen]; exact Subgroup.mem_zpowers z₁
  exact this

theorem A3A3x.sq₁ : z₁ ^ 2 = 1 := hA.isA4.sq_U z₁ hA.z₁_mem.1

theorem A3A3x.z₂_mem : z₂ ∈ blockU2 L s ∧ z₂ ∈ centralizer (baum S : Set G) := by
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hA.s_mem
  have hz₂ : z₂ = s⁻¹ * z₁ * s := hA.z₂_def
  refine ⟨?_, ?_⟩
  · refine mem_conjR.mpr ?_
    have : s * z₂ * s⁻¹ = z₁ := by rw [hz₂]; group
    rw [this]; exact hA.z₁_mem.1
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : s * h * s⁻¹ ∈ baum S := (Subgroup.mem_normalizer_iff.mp hsB h).mp hh
    have e : (s * h * s⁻¹) * z₁ = z₁ * (s * h * s⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hA.z₁_mem.2 _ hh'
    rw [hz₂]
    calc h * (s⁻¹ * z₁ * s) = s⁻¹ * ((s * h * s⁻¹) * z₁) * s := by group
      _ = s⁻¹ * (z₁ * (s * h * s⁻¹)) * s := by rw [e]
      _ = s⁻¹ * z₁ * s * h := by group

theorem A3A3x.sq₂ : z₂ ^ 2 = 1 := by
  have h1 : z₁ * z₁ = 1 := by simpa [pow_two] using hA.sq₁
  have : z₂ * z₂ = s⁻¹ * (z₁ * z₁) * s := by rw [hA.z₂_def]; group
  rw [pow_two, this, h1]; group

theorem A3A3x.z₂_ne : z₂ ≠ 1 := by
  intro h
  apply hA.z₁_ne
  have : z₁ = s * z₂ * s⁻¹ := by rw [hA.z₂_def]; group
  rw [this, h]; group

theorem A3A3x.comm₁₂ : z₁ * z₂ = z₂ * z₁ :=
  hA.comm_elem z₁ (hA.isA4.le hA.z₁_mem.1) z₂ (hA.isA4s.le hA.z₂_mem.1)

theorem A3A3x.z_ne : z₁ * z₂ ≠ 1 := by
  intro h
  have hz : z₂ = z₁ := by
    have h1 : z₂ = z₁⁻¹ := by
      calc z₂ = z₁⁻¹ * (z₁ * z₂) := by group
        _ = z₁⁻¹ := by rw [h]; group
    rw [h1]
    have : z₁ * z₁ = 1 := by simpa [pow_two] using hA.sq₁
    exact inv_eq_of_mul_eq_one_right this
  have hbot : blockU L ⊓ blockU2 L s = ⊥ :=
    le_bot_iff.mp ((inf_le_inf hA.isA4.le hA.isA4s.le).trans (le_of_eq hA.inf_Ls))
  have : z₁ ∈ blockU L ⊓ blockU2 L s := ⟨hA.z₁_mem.1, hz ▸ hA.z₂_mem.1⟩
  rw [hbot] at this
  exact hA.z₁_ne (Subgroup.mem_bot.mp this)

theorem A3A3x.sq_z : (z₁ * z₂) ^ 2 = 1 := by
  have h1 : z₁ * z₁ = 1 := by simpa [pow_two] using hA.sq₁
  have h2 : z₂ * z₂ = 1 := by simpa [pow_two] using hA.sq₂
  calc (z₁ * z₂) ^ 2 = z₁ * z₂ * (z₁ * z₂) := pow_two _
    _ = z₁ * (z₂ * z₁) * z₂ := by group
    _ = z₁ * (z₁ * z₂) * z₂ := by rw [hA.comm₁₂]
    _ = (z₁ * z₁) * (z₂ * z₂) := by group
    _ = 1 := by rw [h1, h2]; group

end Elements

theorem s_mul_self_mem_baum (hB : Basic31 T M H S L s)
    (hcfg : A3A3 T M H S L s) : s ∉ baum S ∧ s * s ∈ baum S := by
  have hcs := hcfg.cs
  obtain ⟨hBL, -⟩ := (C56.baumann_A3_cs hcs hcfg.a3).2
  have hs : s ∉ baum S := fun h => hcfg.s_ne (conjSubgroup_eq_iff_mem_normalizer.mpr (hBL h))
  exact ⟨hs, mul_self_mem_of_relIndex_two hB.idx_R hcfg.s_mem hs⟩

theorem z_central (hB : Basic31 T M H S L s)
    (hA : A3A3x T M H S L s x z₁ z₂) :
    z₁ * z₂ ∈ T ⊓ centralizer (T : Set G) := by
  have hcs := hA.cs
  obtain ⟨hs, hss⟩ := s_mul_self_mem_baum hB hA.toA3A3
  have hxz₁ : x * z₁ = z₁ * x := hA.x_comm₁
  have hxz₂ : x * z₂ = z₂ * x := hA.x_comm₂
  have hz₂ : z₂ = s⁻¹ * z₁ * s := hA.z₂_def
  have hRz₁ : ∀ r ∈ baum S, r * z₁ = z₁ * r := fun r hr =>
    Subgroup.mem_centralizer_iff.mp hA.z₁_mem.2 r hr
  have hRz₂ : ∀ r ∈ baum S, r * z₂ = z₂ * r := fun r hr =>
    Subgroup.mem_centralizer_iff.mp hA.z₂_mem.2 r hr
  have hsz₂ : s * z₂ * s⁻¹ = z₁ := by rw [hz₂]; group
  have hsz₁ : s * z₁ * s⁻¹ = z₂ := by
    have h1 : (s * s) * z₂ * (s * s)⁻¹ = z₂ := by
      have := hRz₂ (s * s) hss
      calc (s * s) * z₂ * (s * s)⁻¹ = (z₂ * (s * s)) * (s * s)⁻¹ := by rw [this]
        _ = z₂ := by group
    calc s * z₁ * s⁻¹ = s * (s * z₂ * s⁻¹) * s⁻¹ := by rw [hsz₂]
      _ = (s * s) * z₂ * (s * s)⁻¹ := by group
      _ = z₂ := h1
  have hszz : s * (z₁ * z₂) * s⁻¹ = z₁ * z₂ := by
    calc s * (z₁ * z₂) * s⁻¹ = (s * z₁ * s⁻¹) * (s * z₂ * s⁻¹) := by group
      _ = z₂ * z₁ := by rw [hsz₁, hsz₂]
      _ = z₁ * z₂ := hA.comm₁₂.symm
  have hTle : T ≤ (baum S ⊔ zpowers s) ⊔ zpowers x := by
    have := le_sup_zpowers_of_relIndex_two hB.idx_T hA.x_mem hA.x_not_mem
    rwa [← hB.S_eq]
  have hle : (baum S ⊔ zpowers s) ⊔ zpowers x ≤ centralizer ({z₁ * z₂} : Set G) := by
    refine sup_le (sup_le (fun r hr => ?_) ?_) ?_
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc r * (z₁ * z₂) = (r * z₁) * z₂ := by group
        _ = (z₁ * r) * z₂ := by rw [hRz₁ r hr]
        _ = z₁ * (r * z₂) := by group
        _ = z₁ * (z₂ * r) := by rw [hRz₂ r hr]
        _ = (z₁ * z₂) * r := by group
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc s * (z₁ * z₂) = (s * (z₁ * z₂) * s⁻¹) * s := by group
        _ = (z₁ * z₂) * s := by rw [hszz]
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc x * (z₁ * z₂) = (x * z₁) * z₂ := by group
        _ = (z₁ * x) * z₂ := by rw [hxz₁]
        _ = z₁ * (x * z₂) := by group
        _ = z₁ * (z₂ * x) := by rw [hxz₂]
        _ = (z₁ * z₂) * x := by group
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hA.s_mem
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hA.a3
  have hU₂B : blockU2 L s ≤ baum S :=
    (C5.conjSubgroup_mono hUB s).trans (le_of_eq (C5.conjSubgroup_eq_self hsB))
  have hz₁T : z₁ ∈ T := hcs.le_T ((inf_le_left : baum S ≤ S) (hUB hA.z₁_mem.1))
  have hz₂T : z₂ ∈ T := hcs.le_T ((inf_le_left : baum S ≤ S) (hU₂B hA.z₂_mem.1))
  exact ⟨T.mul_mem hz₁T hz₂T, Subgroup.mem_centralizer_iff.mpr fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle (hTle ht))⟩

omit [Finite G] in
theorem pCoreOf_centralizerElem_ne_bot {z : G} (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    pCoreOf 2 (centralizerElem z) ≠ ⊥ := by
  intro hbot
  have hzmem : z ∈ centralizerElem z := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz
  have hP : IsPGroup 2 ↥(zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]; norm_num
  have hN : centralizerElem z ≤ normalizer ((zpowers z : Subgroup G) : Set G) :=
    C5.le_normalizer_of_commute fun g hg a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      exact (Commute.zpow_right (show Commute g z from hgz) k).eq
  have hle := le_pCoreOf_of_normalizes (zpowers_le.mpr hzmem) hN hP
  rw [hbot] at hle
  exact hz (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers z)))

theorem isGamma2_centralizer (hcs : ConstrainedSetting G T M H S L) (hB : Basic31 T M H S L s)
    {z : G} (hz : z ≠ 1) (hz2 : z ^ 2 = 1) {Y S₁ : Subgroup G}
    (hpair : IsWitnessPair M (baum S) (Y ⊔ baum S)) (hY : Y ≤ centralizerElem z)
    (hR : baum S ≤ centralizerElem z) (hS₁T : S₁ ≤ T) (hS₁R : baum S < S₁)
    (hS₁z : S₁ ≤ centralizerElem z) :
    IsGamma2 M (centralizerElem z) ∧ IsSylowTwoOf S₁ (centralizerElem z) ∧
      IsSylowTwoOf S₁ (centralizerElem z ⊓ M) := by
  have hS₁2 : IsPGroup 2 ↥S₁ := hcs.setting.isPGroup.to_le hS₁T
  have hΓ : IsGamma M (centralizerElem z) :=
    ⟨pCoreOf_centralizerElem_ne_bot hz hz2, baum S, Y ⊔ baum S, hpair, sup_le hY hR⟩
  have hcardT : Nat.card T = 2 * Nat.card S := by
    have := C5.card_eq_card_mul_relIndex hcs.le_T
    rw [hB.idx_T] at this
    omega
  have hcardS : Nat.card S = 2 * Nat.card (baum S) :=
    GammaExtra.card_eq_two_mul_of_relIndex_eq_two inf_le_left hB.idx_R
  have h1 : Nat.card S ≤ Nat.card S₁ := by
    have := GammaExtra.two_mul_card_le_of_lt hS₁R
    omega
  have h2 : Nat.card S₁ ≤ twoPart (centralizerElem z) := card_le_twoPart hS₁z hS₁2
  obtain ⟨-, hext⟩ := hcs.gamma0.isGamma2_of_card_eq_two_mul hcs.setting hcs.sylow_inf hcardT
  obtain ⟨hcard, hΓ2⟩ := hext _ hΓ (h1.trans h2)
  have hS₁eq : Nat.card S₁ = twoPart (centralizerElem z) := by omega
  refine ⟨hΓ2, isSylowTwoOf_of_card_eq hS₁z hS₁2 hS₁eq, ?_⟩
  have hS₁M : S₁ ≤ M := hS₁T.trans hcs.setting.le
  have hle : twoPart (centralizerElem z ⊓ M) ≤ twoPart (centralizerElem z) :=
    twoPart_mono inf_le_left
  have hge : Nat.card S₁ ≤ twoPart (centralizerElem z ⊓ M) :=
    card_le_twoPart (le_inf hS₁z hS₁M) hS₁2
  exact isSylowTwoOf_of_card_eq (le_inf hS₁z hS₁M) hS₁2 (by omega)

section Centralizers

variable (hA : A3A3x T M H S L s x z₁ z₂)
include hA

theorem A3A3x.sOne_le_T : sOne S x ≤ T :=
  sup_le ((inf_le_left : baum S ≤ S).trans hA.cs.le_T) (zpowers_le.mpr hA.x_mem)

theorem A3A3x.baum_lt_sOne : baum S < sOne S x := by
  refine lt_of_le_of_ne le_sup_left fun h => hA.x_not_mem ?_
  have : x ∈ baum S := by
    rw [h]; exact mem_sup_right (Subgroup.mem_zpowers x)
  exact (inf_le_left : baum S ≤ S) this

theorem A3A3x.baum_le_cent₁ : baum S ≤ centralizerElem z₁ := fun r hr =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hA.z₁_mem.2 r hr)

theorem A3A3x.baum_le_cent₂ : baum S ≤ centralizerElem z₂ := fun r hr =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hA.z₂_mem.2 r hr)

theorem A3A3x.sOne_le_cent₁ : sOne S x ≤ centralizerElem z₁ :=
  sup_le hA.baum_le_cent₁
    (zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hA.x_comm₁))

theorem A3A3x.sOne_le_cent₂ : sOne S x ≤ centralizerElem z₂ :=
  sup_le hA.baum_le_cent₂
    (zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hA.x_comm₂))

theorem A3A3x.L_le_cent₂ : L ≤ centralizerElem z₂ := fun l hl =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (hA.comm_elem l hl z₂ (hA.isA4s.le hA.z₂_mem.1))

theorem A3A3x.Ls_le_cent₁ : conjR L s ≤ centralizerElem z₁ := fun l hl =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (hA.comm_elem z₁ (hA.isA4.le hA.z₁_mem.1) l hl).symm

theorem A3A3x.not_Ls_le : ¬ conjR L s ≤ M := by
  intro h
  apply hA.cs.not_le
  have h1 : conjSubgroup (conjSubgroup L s) s⁻¹ ≤ conjSubgroup M s⁻¹ :=
    C5.conjSubgroup_mono h s⁻¹
  have e : conjSubgroup (conjSubgroup L s) s⁻¹ = L := C5.conjSubgroup_conjSubgroup_inv L s
  have hsM : s ∈ normalizer (M : Set G) :=
    Subgroup.le_normalizer (hA.cs.setting.le (hA.cs.le_T hA.s_mem))
  rw [e, C5.conjSubgroup_eq_self (inv_mem hsM)] at h1
  exact h1

end Centralizers

theorem remark31_G₂ (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hA : A3A3x T M H S L s x z₁ z₂) :
    IsGamma2 M (centralizerElem z₂) ∧ IsSylowTwoOf (sOne S x) (centralizerElem z₂) ∧
      IsSylowTwoOf (sOne S x) (centralizerElem z₂ ⊓ M) := by
  have hcs := hA.cs
  have hB := basic31 hD h27_1 hA.toA3A3
  obtain ⟨w₁, w₂, -, -, -, -, R1, -⟩ := rank1_blocks hD hA.toA3A3
  obtain ⟨hBL, -⟩ := (C56.baumann_A3_cs hcs hA.a3).2
  have hβ := (isConfining_baum hcs hB).2
  have hpair := isWitnessPair_baum_sup hβ (isPGroup_baum hcs) hA.isA4 R1 hBL hcs.not_le
  exact isGamma2_centralizer hcs hB hA.z₂_ne hA.sq₂ hpair hA.L_le_cent₂ hA.baum_le_cent₂
    hA.sOne_le_T hA.baum_lt_sOne hA.sOne_le_cent₂

theorem remark31_G₁ (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hA : A3A3x T M H S L s x z₁ z₂) :
    IsGamma2 M (centralizerElem z₁) ∧ IsSylowTwoOf (sOne S x) (centralizerElem z₁) ∧
      IsSylowTwoOf (sOne S x) (centralizerElem z₁ ⊓ M) := by
  have hcs := hA.cs
  have hB := basic31 hD h27_1 hA.toA3A3
  obtain ⟨w₁, w₂, -, -, -, -, -, R2⟩ := rank1_blocks hD hA.toA3A3
  obtain ⟨hBL, -⟩ := (C56.baumann_A3_cs hcs hA.a3).2
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hA.s_mem
  have hBLs : baum S ≤ normalizer (conjR L s : Set G) := C5.le_normalizer_conj hsB hBL
  have hβ := (isConfining_baum hcs hB).2
  have hpair := isWitnessPair_baum_sup hβ (isPGroup_baum hcs) hA.isA4s R2 hBLs hA.not_Ls_le
  exact isGamma2_centralizer hcs hB hA.z₁_ne hA.sq₁ hpair hA.Ls_le_cent₁ hA.baum_le_cent₁
    hA.sOne_le_T hA.baum_lt_sOne hA.sOne_le_cent₁

end CFSG.QuasithinUnique.DoubleA3
