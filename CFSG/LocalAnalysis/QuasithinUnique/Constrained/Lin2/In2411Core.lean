module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411L34
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411Cover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Easy
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeFive
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedW
public import CFSG.Quasithin.Background.KnownMultL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Module

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

section Signalizer

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.pCoreOf_le_centerOf (h8 : Lemma2_4_8) (h246 : Lemma246Chi)
    (hcfg : Lin2Cfg G T M H S L n D) {X : Subgroup G} (hLX : L ≤ X)
    (hXN : ¬ X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G)) : pCoreOf 2 X ≤ centerOf L := by
  obtain ⟨-, ⟨hQL, hUH⟩, -⟩ := h8 G T M H S L D n hcfg
  have hQL' : pCoreOf 2 L = pCoreOf 2 H := hQL.trans hUH
  have hN : Subgroup.normalizer (pCoreOf 2 H : Set G) = Subgroup.normalizer (L : Set G) := by
    apply le_antisymm
    · exact h246 G T M H S L hcfg.cs hcfg.single (Or.inl ⟨n, hcfg.one_lt, hcfg.lin2⟩)
    · intro g hg
      rw [← conjR_eq_self_iff] at hg ⊢
      rw [← hQL', ← conjR_pCoreOf, hg]
  set P := pCoreOf 2 X with hPdef
  set Q := pCoreOf 2 H with hQdef
  have hXP : X ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X
  have hLN : L ≤ Subgroup.normalizer (Q : Set G) := by rw [hN]; exact Subgroup.le_normalizer
  have hQLle : Q ≤ L := by
    rw [← hQL']
    exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  have hsig : IsSignalizer (Subgroup.normalizer (Q : Set G)) L
      (P ⊓ Subgroup.normalizer (Q : Set G)) :=
    ⟨inf_le_right, hP2.to_inf_left, fun g hg =>
      A4.mem_normalizer_inf (hXP (hLX hg)) (Subgroup.le_normalizer (hLN hg))⟩
  have hP₀Q : P ⊓ Subgroup.normalizer (Q : Set G) ≤ Q := hcfg.le_pCoreOf_of_isSignalizer hN hsig
  have hQNP : Q ≤ Subgroup.normalizer (P : Set G) := hQLle.trans (hLX.trans hXP)
  have hPQ : P ≤ Q := by
    by_contra hnle
    have hW2 : IsPGroup 2 (Q ⊔ P : Subgroup G) :=
      isPGroup_sup_of_le_normalizer_two hQNP
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H) hP2
    rw [sup_comm] at hW2
    have hlt : Q < P ⊔ Q :=
      lt_of_le_of_ne le_sup_right fun heq => hnle (le_sup_left.trans heq.ge)
    obtain ⟨w, hw, hwN, hwQ⟩ := A4.exists_mem_normalizer_not_mem hW2 hlt
    obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff_of_le_normalizer hQNP).1 hw
    have hpN : p ∈ Subgroup.normalizer (Q : Set G) := by
      have : p = (p * q) * q⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hwN (Subgroup.inv_mem _ (Subgroup.le_normalizer hq))
    exact hwQ (Q.mul_mem (hP₀Q ⟨hp, hpN⟩) hq)
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := hLX.trans hXP
  have hPU : P ≤ blockU L := by rw [hUH]; exact hPQ
  rcases le_blockZ_or_eq_blockU hcfg.short hQL hPU hLP with hPZ | hPU'
  · rwa [blockZ_eq_centerOf hcfg.charTwo_L hQL] at hPZ
  · exfalso
    apply hXN
    have : P = Q := hPU'.trans hUH
    rw [← this]
    exact hXP

theorem Lin2Cfg.exists_fixed_vertex (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D)
    (hZ : centerOf L ≠ ⊥) : ∃ v ∈ centerOf L, v ≠ 1 ∧ ∀ s ∈ S, s * v = v * s := by
  obtain ⟨-, ⟨hQL, hUH⟩, -⟩ := h8 G T M H S L D n hcfg
  have hZS : centerOf L ≤ S := by
    have h1 : centerOf L ≤ blockU L := by
      rw [← blockZ_eq_centerOf hcfg.charTwo_L hQL]
      exact blockZ_le_blockU L
    rw [hUH] at h1
    exact h1.trans hcfg.Q_le_S
  have hSn : S ≤ Subgroup.normalizer (centerOf L : Set G) := by
    intro g hg
    rw [← conjR_eq_self_iff]
    exact centerOf_normalized (hcfg.S_le_normalizer hg)
  obtain ⟨z, hz, hz1, hzc⟩ := exists_mem_inf_center_of_normal hcfg.S_isPGroup hZS hSn hZ
  exact ⟨z, hz, hz1, fun s hs => Subgroup.mem_centralizer_iff.1 hzc s hs⟩

end Signalizer

section Parabolic

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.card_blockU (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D)
    (hZ : centerOf L ≠ ⊥) : Nat.card (blockU L) = 2 ^ (3 * n) := by
  obtain ⟨-, ⟨hOL, -⟩, -, h4, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨x, hxT, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨-, hreg⟩ := h4 x hxT hxS
  obtain ⟨-, hZcard, -⟩ := hreg.resolve_left hZ
  have h := lin2_card_U hcfg.lin2
  rw [blockZ_eq_centerOf hcfg.charTwo_L hOL, hZcard] at h
  rw [h]
  ring

theorem Lin2Cfg.false_of_l34 (h8 : Lemma2_4_8)
    (hN : Subgroup.normalizer (pCoreOf 2 H : Set G) = Subgroup.normalizer (L : Set G))
    (hcfg : Lin2Cfg G T M H S L n D) (hZ : centerOf L ≠ ⊥)
    {K P : Subgroup G} {N : Subgroup ↥K} [N.Normal] (hNP : ∀ k : ↥K, k ∈ N ↔ (k : G) ∈ P)
    (hLK : L ≤ K) (hPZ : P ≤ centerOf L) (hY : L34Props (↥K ⧸ N)) : False := by
  obtain ⟨⟨-, -, hTnR⟩, ⟨hOL, hUQ⟩, ⟨-, hRsyl, h3⟩, h4, -, -, h7, -, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨x, hxT, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hRUU, hZR, -, -⟩ := h3 x hxT hxS
  obtain ⟨-, hreg⟩ := h4 x hxT hxS
  obtain ⟨hZel, hZcard, -⟩ := hreg.resolve_left hZ
  obtain ⟨hUel, hUxel, -⟩ := h7 x hxT hxS
  have hRL : thompsonJ S ≤ L := hRsyl.1
  have hUR : blockU L ≤ thompsonJ S := by rw [hRUU]; exact le_sup_left
  have hU'R : conjR (blockU L) x ≤ thompsonJ S := by rw [hRUU]; exact le_sup_right
  have hRx : conjR (thompsonJ S) x = thompsonJ S := conjR_eq_of_mem_normalizer (hTnR hxT)
  have hZeq : blockZ L = centerOf L := blockZ_eq_centerOf hcfg.charTwo_L hOL
  have hUcard : Nat.card (blockU L) = 2 ^ (3 * n) := hcfg.card_blockU h8 hZ
  have hRcard : Nat.card (thompsonJ S) = 2 ^ (4 * n) := by
    have h := lin2_card_sylow hcfg.lin2 hRsyl
    rw [hOL, hUcard] at h
    rw [h]
    ring
  have hRK : thompsonJ S ≤ K := hRL.trans hLK
  have hZL : centerOf L ≤ L := inf_le_left
  have hPK : P ≤ K := (hPZ.trans hZL).trans hLK
  have hKcard : Nat.card K = 20160 * Nat.card P := l34_card hNP hPK hY
  have hPdvd : Nat.card P ∣ 2 ^ n := by
    have := Subgroup.card_dvd_of_le hPZ
    rwa [hZcard] at this
  obtain ⟨a, han, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hPdvd
  have hdiv : 2 ^ (4 * n) ∣ 20160 * Nat.card P := by
    have := Subgroup.card_dvd_of_le hRK
    rwa [hRcard, hKcard] at this
  have h2 : 2 ^ (4 * n) ∣ 2 ^ (6 + a) := by
    have h20160 : 20160 * Nat.card P = 315 * 2 ^ (6 + a) := by
      rw [ha]
      ring
    rw [h20160] at hdiv
    exact (Nat.Coprime.pow_left (4 * n) (by norm_num : Nat.Coprime 2 315)).dvd_of_dvd_mul_left hdiv
  have h3' : 4 * n ≤ 6 + a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
  have hn1 := hcfg.one_lt
  have hn : n = 2 := by omega
  have ha2 : a = 2 := by omega
  subst hn
  have hP4 : Nat.card P = 4 := by
    rw [ha, ha2]
    norm_num
  have hPeq : P = centerOf L :=
    eq_of_le_of_card_le' hPZ (by rw [hZcard, hP4]; norm_num)
  have hZR' : centerOf L ≤ centerOf (thompsonJ S) := by
    intro z hz
    have hzU : z ∈ blockU L := by
      have : z ∈ blockZ L := by rw [hZeq]; exact hz
      exact blockZ_le_blockU L this
    exact ⟨hUR hzU, Subgroup.mem_centralizer_iff.2 fun r hr =>
      Subgroup.mem_centralizer_iff.1 hz.2 r (hRL hr)⟩
  have hPQ : P ≤ conjR (blockU L) x := by
    rw [hPeq]
    intro z hz
    have : z ∈ blockU L ⊓ conjR (blockU L) x := by rw [hZR]; exact hZR' hz
    exact this.2
  have hQK : conjR (blockU L) x ≤ K := hU'R.trans hRK
  have hQcard : Nat.card (conjR (blockU L) x) = Nat.card P * 16 := by
    rw [card_conjR, hUcard, hP4]
    norm_num
  obtain ⟨-, hfin, hfix⟩ := l34_transfer hNP hPQ hQK hUxel hQcard hY
  have hNQ : Subgroup.normalizer (conjR (blockU L) x : Set G) =
      Subgroup.normalizer (conjR L x : Set G) := by
    rw [conjR_normalizer, conjR_normalizer, hUQ, hN]
  have hRW : thompsonJ S ≤ conjR L x := by
    have := conjR_mono hRL x
    rwa [hRx] at this
  have hRN : thompsonJ S ≤ K ⊓ Subgroup.normalizer (conjR (blockU L) x : Set G) :=
    le_inf hRK (by rw [hNQ]; exact hRW.trans Subgroup.le_normalizer)
  have hQR : conjR (blockU L) x < thompsonJ S := by
    refine lt_of_le_of_ne hU'R fun h => ?_
    have := congrArg (fun X : Subgroup G => Nat.card X) h
    simp only [card_conjR, hUcard, hRcard] at this
    norm_num at this
  have hNW := hfin (thompsonJ S) (conjR L x) hQR hRN hRW (by
    intro g hg w hw
    exact (Subgroup.mem_normalizer_iff.1 (by rw [← hNQ]; exact hg.2) w).1 hw)
  have hZx : conjR (centerOf L) x ≤ P := by
    intro z hz
    have hzQ : z ∈ conjR (blockU L) x := by
      refine conjR_mono ?_ x hz
      rw [← hZeq]
      exact blockZ_le_blockU L
    refine hfix z hzQ fun g hg => ?_
    have hgW : x * g * x⁻¹ ∈ L := mem_conjR.1 (hNW hg)
    have hzc : x * z * x⁻¹ ∈ centerOf L := mem_conjR.1 hz
    have hcomm := Subgroup.mem_centralizer_iff.1 hzc.2 _ hgW
    have e1 : x * (g * z) * x⁻¹ = x * (z * g) * x⁻¹ := by
      calc x * (g * z) * x⁻¹ = (x * g * x⁻¹) * (x * z * x⁻¹) := by group
        _ = (x * z * x⁻¹) * (x * g * x⁻¹) := hcomm
        _ = x * (z * g) * x⁻¹ := by group
    have e2 : g * z = z * g := mul_left_cancel (mul_right_cancel e1)
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [e2]
      _ = z := by group
  have hZx' : conjR (centerOf L) x = centerOf L :=
    eq_of_le_of_card_le' (hPeq ▸ hZx) (by rw [card_conjR])
  have hxN : x ∈ Subgroup.normalizer (centerOf L : Set G) := conjR_eq_self_iff.1 hZx'
  have hZS : centerOf L ≤ S := by
    have h1 : centerOf L ≤ blockU L := by
      rw [← hZeq]
      exact blockZ_le_blockU L
    rw [hUQ] at h1
    exact h1.trans hcfg.Q_le_S
  have hHN : H ≤ Subgroup.normalizer (centerOf L : Set G) := by
    rw [hcfg.H_eq]
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · rw [← conjR_eq_self_iff]
      exact centerOf_normalized (Subgroup.le_normalizer hg)
    · rw [← conjR_eq_self_iff]
      exact centerOf_normalized (hcfg.S_le_normalizer hg)
  have h244 := lemma244 G T M H S L hcfg.cs (centerOf L) hZ hZS hHN
  exact hxS (h244 ▸ ⟨hxT, hxN⟩)

end Parabolic

section Main

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

@[expose] def ListedOTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S K : Subgroup G) (z : G), CFSG.IsQuasisimple ↥K →
    IsListedComponent M S K z → pCoreOf 2 K ≠ ⊥ →
      StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 2

theorem lemma2_4_11_core_of_inputs
    (h246 : Lemma246Chi) (h8 : Lemma2_4_8)
    (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat)
    (hlist : Lemma2_3_9_7_listedW) (hOTwo : ListedOTwo) (hl34 : L34Fact)
    (hm22 : M22CoverCyclic) : Lemma2_4_11_core := by
  intro G _ _ T M H S L D n hcfg hZ v hvZ hv1
  obtain ⟨-, ⟨hOL, hUQ⟩, -, h4, -, -, h7, -, -⟩ := h8 G T M H S L D n hcfg
  have hN : Subgroup.normalizer (pCoreOf 2 H : Set G) = Subgroup.normalizer (L : Set G) := by
    apply le_antisymm
    · exact h246 G T M H S L hcfg.cs hcfg.single (Or.inl ⟨n, hcfg.one_lt, hcfg.lin2⟩)
    · intro g hg
      rw [← conjR_eq_self_iff] at hg ⊢
      rw [← hUQ, ← hOL, ← conjR_pCoreOf, hg]
  obtain ⟨x, hxT, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hDx, hreg⟩ := h4 x hxT hxS
  obtain ⟨hZel, hZcard, hZreg⟩ := hreg.resolve_left hZ
  obtain ⟨v₀, hv₀Z, hv₀1, hv₀S⟩ := hcfg.exists_fixed_vertex h8 hZ
  suffices hX0 : Subgroup.centralizer ({v₀} : Set G) ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) by
    obtain ⟨b, hb, hbv⟩ := hZreg.2.1 v₀ ⟨hv₀Z, hv₀1⟩ v ⟨hvZ, hv1⟩
    intro g hg
    have hbN : b ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := hN ▸ hDx hb
    have hgv : g * v = v * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    have hy : b * g * b⁻¹ ∈ Subgroup.centralizer ({v₀} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : v₀ = b * v * b⁻¹ := by rw [← hbv]; group
      rw [e]
      calc b * g * b⁻¹ * (b * v * b⁻¹) = b * (g * v) * b⁻¹ := by group
        _ = b * (v * g) * b⁻¹ := by rw [hgv]
        _ = b * v * b⁻¹ * (b * g * b⁻¹) := by group
    have h1 := hX0 hy
    have : g = b⁻¹ * (b * g * b⁻¹) * b := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hbN) h1) hbN
  by_contra hXN
  set X : Subgroup G := Subgroup.centralizer ({v₀} : Set G) with hX
  have hLX : L ≤ X := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hv₀Z.2 y hy)
  have hSX : S ≤ X := fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hv₀S s hs)
  have hHX : H ≤ X := by rw [hcfg.H_eq]; exact sup_le hLX hSX
  have hv₀2 : v₀ ^ 2 = 1 := hZel.2 v₀ hv₀Z
  have hv₀X : v₀ ∈ X := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzp : IsPGroup 2 (Subgroup.zpowers v₀) := by
    have hE := isElemAbelian_zpowers_of_sq_eq_one hv₀2
    exact fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  have hXn : X ≤ Subgroup.normalizer ((Subgroup.zpowers v₀ : Subgroup G) : Set G) := by
    refine le_normalizer_of_commute fun a ha b hb => ?_
    have hc : X = Subgroup.centralizer ((Subgroup.zpowers v₀ : Subgroup G) : Set G) := by
      rw [hX, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hc] at hb
    exact Subgroup.mem_centralizer_iff.1 hb a ha
  have hv₀P : v₀ ∈ pCoreOf 2 X :=
    le_pCoreOf_of_normalizes (Subgroup.zpowers_le.2 hv₀X) hXn hzp (Subgroup.mem_zpowers v₀)
  have hPX : pCoreOf 2 X ≠ ⊥ := fun h => hv₀1 (by
    have := hv₀P
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hΓX : IsGamma M X := hcfg.cs.witness.isGamma_of_le hHX hPX
  obtain ⟨hX0, hSX', hSXM, -, -⟩ :=
    hcfg.cs.gamma0.overgroup_of_le hcfg.cs.setting hcfg.cs.sylow_inf hΓX hHX
  obtain ⟨T', z, hT', hST', hz, hz1, hz2⟩ :=
    hcfg.cs.gamma0.exists_central_involution hcfg.cs.setting hcfg.cs.sylow_inf
  have hPZ : pCoreOf 2 X ≤ centerOf L := hcfg.pCoreOf_le_centerOf h8 h246 hLX hXN
  have hLc : L ∈ cComp H :=
    L238.mem_cComp_of_isChi0Block_nonsolvable hcfg.cs.block.1
      (Or.inl ⟨n, hcfg.one_lt, hcfg.lin2⟩)
  have hLfam : L ∈ lFamily S := cComp_subset_lFamily hcfg.cs.sylow.le hLc
  have hlocal : LocalSQTK G := hcfg.cs.setting.qtke.1
  obtain ⟨K, hK, hLK⟩ := lemma_1_2_4_exists hlocal h37 h39 hPX hSX' hLX hLfam
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKX : K ≤ X := le_of_mem_cComp hK
  have hXP : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  have hLP : L ≤ Subgroup.centralizer (pCoreOf 2 X : Set G) := fun ℓ hℓ =>
    Subgroup.mem_centralizer_iff.2 fun p hp =>
      (Subgroup.mem_centralizer_iff.1 (hPZ hp).2 ℓ hℓ).symm
  have hKP : K ≤ Subgroup.centralizer (pCoreOf 2 X : Set G) :=
    le_centralizer_of_mem_cComp hK hLK (ne_bot_of_mem_cComp hLc) (perfect_of_mem_cComp hLc) hXP hLP
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 X := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  have hZK : pCoreOf 2 K ≤ centerOf K := fun y hy =>
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K hy,
      Subgroup.mem_centralizer_iff.2 fun k hk =>
        (Subgroup.mem_centralizer_iff.1 (hKP hk) y (hOK hy)).symm⟩
  have hUK : blockU L ≤ K := (blockU_le L).trans hLK
  obtain ⟨hUel, -, -⟩ := h7 x hxT hxS
  have hm : 1 < CFSG.Open.pRank 2 K := by
    have hmem : 3 * n ∈ {k | ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
      ⟨blockU L, hUK, hUel, hcfg.card_blockU h8 hZ⟩
    have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
      refine ⟨Nat.card G, fun k hk => ?_⟩
      obtain ⟨E, -, -, hEc⟩ := hk
      have h1 : 2 ^ k ≤ Nat.card G := hEc ▸ Subgroup.card_le_card_group E
      exact (Nat.lt_two_pow_self.trans_le h1).le
    have := hcfg.one_lt
    exact lt_of_lt_of_le (by omega) (le_csSup hbdd hmem)
  have hq : CFSG.IsQuasisimple ↥K :=
    lemma_1_2_1_five_core hlocal h36 CFSG.Quasithin.l2MultiplierFact hPX hK hZK hm
  have hKc : IsComponentIn K X := by
    refine ⟨hKX, ?_, ?_⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX).symm hq
    · have := A3.subnormal_comap X.subtype (subnormal_of_mem_cComp hK)
      rw [show X.comap X.subtype = ⊤ from Subgroup.subgroupOf_self X] at this
      exact A3.subnormal_top_iff.mp this
  have hKlW : IsListedComponentW M S K z :=
    hlist G T M hcfg.cs.setting X S T' z hX0 hSXM hT' hST' hz hz1 hz2 K hKc
  have hv₀L : v₀ ∈ L := hv₀Z.1
  have hv₀K : v₀ ∈ pCoreOf 2 K :=
    le_pCoreOf_of_normalizes (Subgroup.zpowers_le.2 (hLK hv₀L)) (hKX.trans hXn) hzp
      (Subgroup.mem_zpowers v₀)
  have hKO : pCoreOf 2 K ≠ ⊥ := fun h => hv₀1 (by
    have := hv₀K
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hNP : ∀ k : ↥K, k ∈ CFSG.pCore 2 ↥K ↔ (k : G) ∈ pCoreOf 2 K := by
    intro k
    constructor
    · intro hk
      exact ⟨k, by assumption, rfl⟩
    · rintro ⟨y, hy, hyk⟩
      have : y = k := Subtype.ext hyk
      rw [this] at hy
      exact hy
  rcases hKlW.old_or_cover with hKl | ⟨⟨e⟩, -⟩
  · have hmodel := hOTwo G M S K z hq hKl hKO
    have hY := hl34 (↥K ⧸ CFSG.pCore 2 ↥K) hmodel
    exact hcfg.false_of_l34 h8 hN hZ hNP hLK (hOK.trans hPZ) hY
  ·
    have hperf : Group.IsPerfect ↥K := hq.1
    have hNc : CFSG.pCore 2 ↥K ≤ Subgroup.center ↥K := fun k hk =>
      Subgroup.mem_center_iff.2 fun y => Subtype.ext
        (Subgroup.mem_centralizer_iff.1 (hZK ((hNP k).1 hk)).2 (y : G) y.2)
    have hZU : centerOf L ≤ blockU L := by
      rw [← blockZ_eq_centerOf hcfg.charTwo_L hOL]
      exact blockZ_le_blockU L
    exact false_of_m22_cover hm22 hcfg.one_lt e hNc hUK hUel (hcfg.card_blockU h8 hZ) hZU hZel
      hZcard fun k hk => (hOK.trans hPZ) ((hNP k).1 hk)

end Main

end CFSG.QuasithinUnique.Lin2
