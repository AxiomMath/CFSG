module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHParaK
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBasic

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3)
open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique

section Outer

variable {X : Type} [Group X] [Finite X]

theorem eq_one_or_inv_of_centralizes {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (hK : IsLinThreeFour K) {E : Subgroup X}
    (hEK : E ≤ K) (hE : Nat.card E = 9) :
    ∃ y ∈ K, orderOf y = 3 ∧ ∀ t : X, ¬ 3 ∣ orderOf t → (∀ e ∈ E, t * e = e * t) →
      t = 1 ∨ t * y * t⁻¹ = y⁻¹ := by
  have hE' : Nat.card (E.subgroupOf K) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hE]
  obtain ⟨y, hy3, -, hy⟩ := CFSG.AGLEmbeddingD2.L34BetaHPara.exists_orderThree_inverted hK hE'
  refine ⟨(y : X), y.2, by rw [Subgroup.orderOf_coe, hy3], fun t ht hte => ?_⟩
  set α : MulAut K := MulAut.conjNormal t with hα
  have hfix : ∀ e ∈ E.subgroupOf K, α e = e := fun e he => by
    apply Subtype.ext
    rw [hα, MulAut.conjNormal_apply]
    have := hte e (Subgroup.mem_subgroupOf.mp he)
    rw [this, mul_inv_cancel_right]
  have hord : ¬ 3 ∣ orderOf α := fun h3 =>
    ht (h3.trans (orderOf_map_dvd (MulAut.conjNormal (H := K)) t))
  rcases hy α hfix hord with h | h
  · left
    have hcent : t ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨k, hk⟩)
      rw [hα, MulAut.conjNormal_apply] at h1
      change t * k * t⁻¹ = k at h1
      calc k * t = (t * k * t⁻¹) * t := by rw [h1]
        _ = t * k := by group
    rw [hC, Subgroup.mem_bot] at hcent
    exact hcent
  · right
    have h1 := congrArg Subtype.val h
    rw [hα, MulAut.conjNormal_apply] at h1
    exact h1

theorem eq_of_ne_one_of_centralizes {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (hK : IsLinThreeFour K) {E : Subgroup X}
    (hEK : E ≤ K) (hE : Nat.card E = 9) {N : Subgroup X} (hN : Nat.Coprime 3 (Nat.card N))
    (hNE : ∀ t ∈ N, ∀ e ∈ E, t * e = e * t) :
    ∀ s ∈ N, ∀ t ∈ N, s ≠ 1 → t ≠ 1 → s = t := by
  obtain ⟨y, -, hy3, hy⟩ := eq_one_or_inv_of_centralizes hC hK hEK hE
  have h3 : ∀ t ∈ N, ¬ 3 ∣ orderOf t := fun t ht h3 =>
    absurd (Nat.Coprime.coprime_dvd_right (h3.trans (Subgroup.orderOf_dvd_natCard N ht)) hN)
      (by norm_num)
  intro s hs t ht hs1 ht1
  have hsy := (hy s (h3 s hs) (hNE s hs)).resolve_left hs1
  have hty := (hy t (h3 t ht) (hNE t ht)).resolve_left ht1
  have hu : t⁻¹ * s ∈ N := N.mul_mem (N.inv_mem ht) hs
  have huE : ∀ e ∈ E, t⁻¹ * s * e = e * (t⁻¹ * s) := by
    intro e he
    have h1 := hNE s hs e he
    have h2 := hNE t ht e he
    calc t⁻¹ * s * e = t⁻¹ * (e * s) := by rw [mul_assoc, h1]
      _ = t⁻¹ * e * s := by rw [mul_assoc]
      _ = e * t⁻¹ * s := by
        congr 1
        calc t⁻¹ * e = t⁻¹ * (e * t) * t⁻¹ := by group
          _ = t⁻¹ * (t * e) * t⁻¹ := by rw [h2]
          _ = e * t⁻¹ := by group
      _ = e * (t⁻¹ * s) := by rw [mul_assoc]
  have hyc : (t⁻¹ * s) * y * (t⁻¹ * s)⁻¹ = y := by
    have e1 : (t⁻¹ * s) * y * (t⁻¹ * s)⁻¹ = t⁻¹ * (s * y * s⁻¹) * t := by group
    rw [e1, hsy]
    have e2 : t * y * t⁻¹ = y⁻¹ := hty
    calc t⁻¹ * y⁻¹ * t = t⁻¹ * (t * y * t⁻¹) * t := by rw [e2]
      _ = y := by group
  rcases hy (t⁻¹ * s) (h3 _ hu) huE with h | h
  · calc s = t * (t⁻¹ * s) := by group
      _ = t := by rw [h, mul_one]
  · exfalso
    rw [hyc] at h
    have hy2 : y ^ 2 = 1 := by
      calc y ^ 2 = y * y := pow_two y
        _ = y * y⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel y
    have := orderOf_dvd_of_pow_eq_one hy2
    rw [hy3] at this
    norm_num at this

end Outer

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_of_isSylowIn {P Y : Subgroup G}
    (h : CFSG.DihedralBlueprint.IsSylowIn 2 P Y) : IsSylowTwoOf P Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := (CFSG.DihedralBlueprint.isSylowIn_iff_exists_sylow 2 P Y).mp h
  refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
  exact Q.not_dvd_index

section Conf

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.exists_twoCore_inf_not_mem (hc : D2L34BetaConf3 d P M A H R Rbar K) :
    ∃ u ∈ pCoreOf 2 (H ⊓ M), u ∉ GLBPrimeCore 3 H := by
  by_contra hcon
  push Not at hcon
  apply hc.ne
  set T₀ := pCoreOf 2 (H ⊓ M) with hT₀
  set W := GLBPrimeCore 3 H with hW
  have hT₀W : T₀ ≤ W := fun u hu => hcon u hu
  have hWH : W ≤ H := glbPrimeCore_le 3 H
  have hWM : W ≤ M := hc.esc.primeCore_le
  have hT₀n : H ⊓ M ≤ Subgroup.normalizer (T₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
  have hT₀2 : IsPGroup 2 T₀ := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)
  have h1 : T₀ ≤ pCoreOf 2 W :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hT₀W
      ((le_inf hWH hWM).trans hT₀n) hT₀2
  have h2 : pCoreOf 2 W ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 W).trans hWH)
      ((le_normalizer_glbPrimeCore 3 H).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W))
      (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 W)
  have h3 : pCoreOf 2 H ≤ T₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) hc.esc.twoCore_le)
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  exact le_antisymm (h1.trans h2) h3

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.exists_isSylowTwoOf_glbPrimeCore_inf
    (hc : D2L34BetaConf3 d P M A H R Rbar K) :
    ∃ V : Subgroup G, IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)) ∧
      A ≤ Subgroup.normalizer (V : Set G) := by
  have hAHM : A ≤ H ⊓ M :=
    le_inf (hc.esc.A_le.trans hc.esc.le_H) (hc.esc.A_le.trans hc.esc.le_M)
  obtain ⟨V, hV, hVA⟩ := CFSG.DihedralBlueprint.normalized_exists_sylow 3 2 Nat.prime_three
    Nat.prime_two A (GLBPrimeCore 3 (H ⊓ M)) (IsPGroup.of_card (n := 2) hc.esc.card_A)
    (hAHM.trans (le_normalizer_glbPrimeCore 3 (H ⊓ M))) (glbPrimeCore_coprime 3 (H ⊓ M))
  exact ⟨V, isSylowTwoOf_of_isSylowIn hV, hVA⟩

theorem D2L34BetaConf.exists_isSylowTwoOf_glbPrimeCore_inf
    (hc : D2L34BetaConf d P M A H R Rbar K) :
    ∃ V : Subgroup G, IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)) ∧
      A ≤ Subgroup.normalizer (V : Set G) :=
  hc.toConf3.exists_isSylowTwoOf_glbPrimeCore_inf

end Conf

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.map_commute_of_coprime (hc : D2L34BetaConf3 d P M A H R Rbar K)
    {D : Subgroup G} (hDHM : D ≤ H ⊓ M) (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (hD3 : Nat.Coprime 3 (Nat.card D)) {x a : G} (hx : x ∈ D) (ha : a ∈ A) (hxH : x ∈ H)
    (haH : a ∈ H) :
    QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hxH⟩ *
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, haH⟩ =
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, haH⟩ *
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hxH⟩ := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hX₀ := hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  set c := x * a * x⁻¹ * a⁻¹ with hc_def
  have hcD : c ∈ D := by
    have h1 : a * x⁻¹ * a⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hAD ha) x⁻¹).mp (D.inv_mem hx)
    have := D.mul_mem hx h1
    simpa [hc_def, mul_assoc] using this
  have hcH : c ∈ H := H.mul_mem (H.mul_mem (H.mul_mem hxH haH) (H.inv_mem hxH)) (H.inv_mem haH)
  have hxX₀ : π ⟨x, hxH⟩ ∈ Subgroup.normalizer
      (((A.subgroupOf H).map π : Subgroup _) : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [← hX₀]
    exact ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr (hDHM hx), rfl⟩
  have haA : π ⟨a, haH⟩ ∈ (A.subgroupOf H).map π :=
    ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have he : π ⟨c, hcH⟩ = π ⟨x, hxH⟩ * π ⟨a, haH⟩ * (π ⟨x, hxH⟩)⁻¹ * (π ⟨a, haH⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have hcA : π ⟨c, hcH⟩ ∈ (A.subgroupOf H).map π := by
    rw [he]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hxX₀ _).mp haA)
      (Subgroup.inv_mem _ haA)
  have hAbar : Nat.card ((A.subgroupOf H).map π) = 3 ^ 2 := hc.almostSimple.card_A
  have h1 : orderOf (π ⟨c, hcH⟩) ∣ 3 ^ 2 := by
    rw [← hAbar]
    exact Subgroup.orderOf_dvd_natCard _ hcA
  have h2 : orderOf (π ⟨c, hcH⟩) ∣ Nat.card D := by
    refine (orderOf_map_dvd π _).trans ?_
    have := Subgroup.orderOf_dvd_natCard D hcD
    rwa [← Subgroup.orderOf_mk c hcH] at this
  have hcop : Nat.Coprime (orderOf (π ⟨c, hcH⟩)) (Nat.card D) :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left 2 hD3)
  have hc1 : π ⟨c, hcH⟩ = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h2)
  rw [he] at hc1
  calc π ⟨x, hxH⟩ * π ⟨a, haH⟩
      = (π ⟨x, hxH⟩ * π ⟨a, haH⟩ * (π ⟨x, hxH⟩)⁻¹ * (π ⟨a, haH⟩)⁻¹) *
          (π ⟨a, haH⟩ * π ⟨x, hxH⟩) := by group
    _ = π ⟨a, haH⟩ * π ⟨x, hxH⟩ := by rw [hc1, one_mul]

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.le_glbPrimeCore_sup_of_coprime (hc : D2L34BetaConf3 d P M A H R Rbar K)
    {D : Subgroup G} (hDHM : D ≤ H ⊓ M) (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (hD3 : Nat.Coprime 3 (Nat.card D)) (hT₀D : pCoreOf 2 (H ⊓ M) ≤ D) :
    D ≤ GLBPrimeCore 3 H ⊔ pCoreOf 2 (H ⊓ M) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hDH : D ≤ H := hDHM.trans inf_le_left
  have := hc.almostSimple.normal
  have hL : IsLinThreeFour K := isLinThreeFour_of_l34Index hc.l34 hc.iso
  set Dbar := (D.subgroupOf H).map π with hDbar
  have hDbar3 : Nat.Coprime 3 (Nat.card Dbar) := by
    have h1 : Nat.card Dbar ∣ Nat.card (D.subgroupOf H) := Subgroup.card_map_dvd _ _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv] at h1
    exact Nat.Coprime.coprime_dvd_right h1 hD3
  have hDbarE : ∀ t ∈ Dbar, ∀ e ∈ (A.subgroupOf H).map π, t * e = e * t := by
    rintro _ ⟨⟨x, hxH⟩, hx, rfl⟩ _ ⟨⟨a, haH⟩, ha, rfl⟩
    exact D2L34BetaConf3.map_commute_of_coprime hc hDHM hAD hD3 (Subgroup.mem_subgroupOf.mp hx)
      (Subgroup.mem_subgroupOf.mp ha) hxH haH
  have huniq := eq_of_ne_one_of_centralizes hc.almostSimple.centralizer_eq_bot hL hc.le_K
    (by rw [hc.almostSimple.card_A]; norm_num) hDbar3 hDbarE
  obtain ⟨u, huT, huW⟩ := D2L34BetaConf3.exists_twoCore_inf_not_mem hc
  have huH : u ∈ H := (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M) huT).1
  have hu1 : π ⟨u, huH⟩ ≠ 1 := fun h =>
    huW ((mk'_primeComplementCore_eq_one_iff 3 ⟨u, huH⟩).mp h)
  have huD : π ⟨u, huH⟩ ∈ Dbar := ⟨⟨u, huH⟩, Subgroup.mem_subgroupOf.mpr (hT₀D huT), rfl⟩
  intro x hx
  have hxH : x ∈ H := hDH hx
  have hxD : π ⟨x, hxH⟩ ∈ Dbar := ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  by_cases hx1 : π ⟨x, hxH⟩ = 1
  · exact Subgroup.mem_sup_left ((mk'_primeComplementCore_eq_one_iff 3 ⟨x, hxH⟩).mp hx1)
  · have heq := huniq _ hxD _ huD hx1 hu1
    have hw : π ((⟨u, huH⟩ : H)⁻¹ * ⟨x, hxH⟩) = 1 := by
      rw [map_mul, map_inv, heq, inv_mul_cancel]
    have hwW := (mk'_primeComplementCore_eq_one_iff 3 _).mp hw
    have e : x = u * (u⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right huT) (Subgroup.mem_sup_left hwW)

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.glbPrimeCore_inf_le (hc : D2L34BetaConf3 d P M A H R Rbar K) :
    GLBPrimeCore 3 (H ⊓ M) ≤ GLBPrimeCore 3 H ⊔ pCoreOf 2 (H ⊓ M) := by
  have hAHM : A ≤ H ⊓ M :=
    le_inf (hc.esc.A_le.trans hc.esc.le_H) (hc.esc.A_le.trans hc.esc.le_M)
  have hT₀2 : IsPGroup 2 (pCoreOf 2 (H ⊓ M)) :=
    RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)
  have hT₀D : pCoreOf 2 (H ⊓ M) ≤ GLBPrimeCore 3 (H ⊓ M) := by
    refine le_glbPrimeCore (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)) ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT₀2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  exact D2L34BetaConf3.le_glbPrimeCore_sup_of_coprime hc (glbPrimeCore_le 3 (H ⊓ M))
    (hAHM.trans (le_normalizer_glbPrimeCore 3 (H ⊓ M))) (glbPrimeCore_coprime 3 (H ⊓ M)) hT₀D

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.isBetaBase_of_isSylowTwoOf (hc : D2L34BetaConf3 d P M A H R Rbar K)
    {V : Subgroup G} (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M))) : IsBetaBase H M V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W₁ := GLBPrimeCore 3 (H ⊓ M) with hW₁
  have hW₁HM : W₁ ≤ H ⊓ M := glbPrimeCore_le 3 (H ⊓ M)
  have hWeq : (primeComplementCore (G := H) 3).map H.subtype = GLBPrimeCore 3 H := by
    rw [← glbPrimeCore_subgroupOf 3 H, Subgroup.map_subgroupOf_eq_of_le (glbPrimeCore_le 3 H)]
  have hcop2 : ∀ {Q : Subgroup G}, IsPGroup 2 Q → Nat.Coprime 3 (Nat.card Q) := by
    intro Q hQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hS2 := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hHS := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hSW₁ : pCoreOf 2 H ≤ W₁ :=
    le_glbPrimeCore (le_inf (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) hc.esc.twoCore_le)
      (inf_le_left.trans hHS) (hcop2 hS2)
  have hSV : pCoreOf 2 H ≤ V :=
    hV.le_of_normalizes hSW₁ (hW₁HM.trans (inf_le_left.trans hHS)) hS2
  have hT₀2 := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)
  have hHMT₀ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
  have hT₀W₁ : pCoreOf 2 (H ⊓ M) ≤ W₁ :=
    le_glbPrimeCore (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)) hHMT₀ (hcop2 hT₀2)
  have hT₀V : pCoreOf 2 (H ⊓ M) ≤ V := hV.le_of_normalizes hT₀W₁ (hW₁HM.trans hHMT₀) hT₀2
  refine ⟨hV.2.1, hSV, ?_, ?_⟩
  · rw [hWeq]
    exact hV.1.trans (D2L34BetaConf3.glbPrimeCore_inf_le hc)
  · rw [hWeq]
    intro hVW
    obtain ⟨u, huT, huW⟩ := D2L34BetaConf3.exists_twoCore_inf_not_mem hc
    exact huW (hVW (hT₀V huT))

theorem D2L34BetaConf.isBetaBase_of_isSylowTwoOf (hc : D2L34BetaConf d P M A H R Rbar K)
    {V : Subgroup G} (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M))) : IsBetaBase H M V :=
  hc.toConf3.isBetaBase_of_isSylowTwoOf hV

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.isSylowTwoOf_inf_glbPrimeCore_of_normalizer_le
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {V : Subgroup G}
    (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M))) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hNV : Subgroup.normalizer (V : Set G) ≤ H) :
    IsSylowTwoOf (V ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W₁ := GLBPrimeCore 3 (H ⊓ M) with hW₁
  set O := GLBPrimeCore 3 M with hO
  have hW₁HM : W₁ ≤ H ⊓ M := glbPrimeCore_le 3 (H ⊓ M)
  have hVM : V ≤ M := hV.1.trans (hW₁HM.trans inf_le_right)
  have hAM : A ≤ M := hc.esc.A_le.trans hc.esc.le_M
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hOM : O ≤ M := glbPrimeCore_le 3 M
  have hMO : M ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glbPrimeCore 3 M
  set Y := O ⊔ V with hY
  have hYM : Y ≤ M := sup_le hOM hVM
  have hcop2 : ∀ {Q : Subgroup G}, IsPGroup 2 Q → Nat.Coprime 3 (Nat.card Q) := by
    intro Q hQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hY3 : Nat.Coprime 3 (Nat.card Y) := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (hVM.trans hMO)
    have hdvd : Nat.card Y ∣ Nat.card O * Nat.card V := ⟨_, h.symm⟩
    exact Nat.Coprime.coprime_dvd_right hdvd
      (Nat.Coprime.mul_right (glbPrimeCore_coprime 3 M) (hcop2 hV.2.1))
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hY, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMO (hAM ha)),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAV ha)]
  obtain ⟨Q, hQ, hVQ, hQA⟩ := CFSG.DihedralBlueprint.normalized_sylow_containing 3 2
    Nat.prime_three Nat.prime_two A Y V (IsPGroup.of_card (n := 2) hc.esc.card_A) hAY hY3
    le_sup_right hV.2.1 hAV
  have hQY : Q ≤ Y := hQ.1
  have hQ2 : IsPGroup 2 Q := hQ.2.1
  set D := Q ⊓ Subgroup.normalizer (V : Set G) with hD
  have hDHM : D ≤ H ⊓ M := le_inf (inf_le_right.trans hNV) (inf_le_left.trans (hQY.trans hYM))
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := fun a ha =>
    mem_normalizer_inf (hQA ha) (Subgroup.le_normalizer (hAV ha))
  have hD2 : IsPGroup 2 D := hQ2.to_le inf_le_left
  have hT₀2 := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)
  have hHMT₀ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
  have hT₀W₁ : pCoreOf 2 (H ⊓ M) ≤ W₁ :=
    le_glbPrimeCore (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)) hHMT₀ (hcop2 hT₀2)
  have hT₀V : pCoreOf 2 (H ⊓ M) ≤ V := hV.le_of_normalizes hT₀W₁ (hW₁HM.trans hHMT₀) hT₀2
  have hVD : V ≤ D := le_inf hVQ Subgroup.le_normalizer
  have hWW₁ : GLBPrimeCore 3 H ≤ W₁ :=
    le_glbPrimeCore (le_inf (glbPrimeCore_le 3 H) hc.esc.primeCore_le)
      (inf_le_left.trans (le_normalizer_glbPrimeCore 3 H)) (glbPrimeCore_coprime 3 H)
  have hDW₁ : D ≤ W₁ :=
    (D2L34BetaConf3.le_glbPrimeCore_sup_of_coprime hc hDHM hAD (hcop2 hD2) (hT₀V.trans hVD)).trans
      (sup_le hWW₁ hT₀W₁)
  have hDV : D ≤ V := by
    have hVp : IsPGroup 2 (V.subgroupOf W₁) :=
      hV.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hV.1).symm
    let S : Sylow 2 W₁ := hVp.toSylow hV.2.2
    have hDp : IsPGroup 2 (D.subgroupOf W₁) :=
      hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hDW₁).symm
    have hle : (S : Subgroup W₁) ≤ D.subgroupOf W₁ := Subgroup.comap_mono hVD
    have heq : D.subgroupOf W₁ = V.subgroupOf W₁ := S.is_maximal' hDp hle
    intro x hx
    have : (⟨x, hDW₁ hx⟩ : W₁) ∈ V.subgroupOf W₁ := heq ▸ Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp this
  have hQV : Q ≤ V := by
    refine CFSG.AGLEmbeddingD2.le_of_normalizer_inf_le hQ2 ?_
    rw [inf_of_le_right hVQ]
    exact hDV
  have hQeq : Q = V := le_antisymm hQV hVQ
  rw [hQeq] at hQ
  exact L34FF.isSylowTwoOf_inf_of_le_of_normalizes (isSylowTwoOf_of_isSylowIn hQ) le_sup_left
    (hVM.trans hMO)

theorem D2L34BetaConf.isSylowTwoOf_inf_glbPrimeCore_of_normalizer_le
    (hc : D2L34BetaConf d P M A H R Rbar K) {V : Subgroup G}
    (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M))) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hNV : Subgroup.normalizer (V : Set G) ≤ H) :
    IsSylowTwoOf (V ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) :=
  hc.toConf3.isSylowTwoOf_inf_glbPrimeCore_of_normalizer_le hV hAV hNV

@[expose] def D2L34BetaPushUpCover : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → ∀ V : Subgroup G, IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)) →
    A ≤ Subgroup.normalizer (V : Set G) →
    ∃ C : Subgroup G, C ≤ V ∧ C ≠ ⊥ ∧ (C.subgroupOf V).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k

@[expose] def D2L34BetaPushUpCoverSyl : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → ∀ T : Subgroup G, IsSylowTwoOf T (H ⊓ M) →
    ∃ C : Subgroup G, C ≤ T ∧ C ≠ ⊥ ∧ (C.subgroupOf T).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k

theorem D2L34BetaConf.isSylowTwoOf_of_cover (hcov : D2L34BetaPushUpCoverSyl)
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    IsSylowTwoOf T M ∧ Subgroup.normalizer (T : Set G) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hCT, hC1, hchar, hcovC⟩ := hcov d G P M A H R Rbar K hc hstr T hT
  have hNT := D2L34BetaConf.normalizer_le_of_char_cover' hc hstr hOnly hT.2.1 hCT hC1 hchar
    hcovC
  refine ⟨?_, hNT⟩
  have hTM : T ≤ M := hT.1.trans inf_le_right
  obtain ⟨S, hTS, hS⟩ := exists_isSylowTwoOf_of_le hTM hT.2.1
  have hST : S ≤ T := by
    refine CFSG.AGLEmbeddingD2.le_of_normalizer_inf_le hS.2.1 ?_
    rw [inf_of_le_right hTS]
    have hle : S ⊓ Subgroup.normalizer (T : Set G) ≤ H ⊓ M :=
      le_inf (inf_le_right.trans hNT) (inf_le_left.trans hS.1)
    exact (hT.eq_of_le (le_inf hTS Subgroup.le_normalizer) hle (hS.2.1.to_le inf_le_left)).le
  rwa [le_antisymm hST hTS] at hS

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
