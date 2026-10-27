module

public import CFSG.GH74.GLS.LU.Local.FiveL83e

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L83f

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {X₁ : Subgroup G}

abbrev YW (z t u : G) (X₁ : Subgroup G) : Subgroup G := WW t X₁ ⊓ centralizer ({z * u} : Set G)

theorem Cfg2W.card_Y (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t))
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) : Nat.card ↥(YW z t u X₁) = 25 := by
  have hBW := c.bw_U (K := WW t X₁) (c.TT_le_normalizer_W c.z_mem_TT) c.u_mem_normalizer_W
    (odd_card_pPrimeCoreOf _)
  rw [hz.cent, hz.inf_Cu, c.W_inf_Cu hz ht hzt] at hBW
  simp only [Subgroup.card_bot, one_pow, mul_one] at hBW
  rw [c.card_W hq hz ht hzt, hz.card] at hBW
  show Nat.card ↥(WW t X₁ ⊓ centralizer ({z * u} : Set G)) = 25
  omega

theorem Cfg2W.XX_inf_Y (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : XX t X₁ ⊓ YW z t u X₁ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxX, hxW, hxY⟩
  have h1 : x * (z * u) = (z * u) * x := Subgroup.mem_centralizer_singleton_iff.mp hxY
  have hzx : z * x = x * z := (Subgroup.mem_centralizer_singleton_iff.mp (c.XX_le_Cz hxX)).symm
  have hux : u * x * u⁻¹ = x⁻¹ := c.u_inv_XX x hxX
  have h2 : x = x⁻¹ := by
    calc x = (z * u) * x * (z * u)⁻¹ := by
          calc x = (x * (z * u)) * (z * u)⁻¹ := by group
            _ = ((z * u) * x) * (z * u)⁻¹ := by rw [h1]
        _ = z * (u * x * u⁻¹) * z⁻¹ := by group
        _ = z * x⁻¹ * z⁻¹ := by rw [hux]
        _ = (z * x * z⁻¹)⁻¹ := by group
        _ = x⁻¹ := by
          have : z * x * z⁻¹ = x := by
            calc z * x * z⁻¹ = (x * z) * z⁻¹ := by rw [hzx]
              _ = x := by group
          rw [this]
  have hsq : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel x
  have hx5 : x ^ 5 = 1 := c.XX_pow x hxX
  have : x = 1 := by
    calc x = x ^ 5 * ((x * x)⁻¹) ^ 2 := by group
      _ = 1 := by rw [hx5, hsq]; simp
  rw [this]; exact Subgroup.one_mem _

theorem Cfg2W.XX_sup_Y (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t))
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) : XX t X₁ ⊔ YW z t u X₁ = WW t X₁ := by
  have hXX := c.XX_eq_Xz hq hz
  have hXXW : XX t X₁ ≤ WW t X₁ := c.XX_le_W hq hz
  have hle : XX t X₁ ⊔ YW z t u X₁ ≤ WW t X₁ := sup_le hXXW inf_le_left
  have hcomm : ∀ a ∈ XX t X₁, ∀ b ∈ YW z t u X₁, a * b = b * a := fun a ha b hb =>
    c.W_comm hz ht hzt a (hXXW ha) b hb.1
  have hcard : Nat.card ↥(XX t X₁ ⊔ YW z t u X₁) = 625 := by
    rw [card_sup_of_commute_disjoint hcomm c.XX_inf_Y, c.XX_card2, c.card_Y hq hz ht hzt]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, c.card_W hq hz ht hzt])

theorem Cfg2W.W_H (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t))
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) : ∀ h ∈ H, cjL h (WW t X₁) = WW t X₁ := by
  intro h hh
  have hXX := c.XX_eq_Xz hq hz
  have hXXW : XX t X₁ ≤ WW t X₁ := c.XX_le_W hq hz
  set D := centralizer ((XX t X₁ : Subgroup G) : Set G) with hD
  have hDh : cjL h D = D := by rw [hD, cjL_centralizer, c.hinv_XX h hh]
  have hW'h : cjL h (pPrimeCoreOf 2 D) = pPrimeCoreOf 2 D := by rw [← pPrimeCoreOf_cjL, hDh]
  have hWD : WW t X₁ ≤ D := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact c.W_comm hz ht hzt b (hXXW hb) a ha
  have hDC0 : D ≤ CZ t X₁ := Subgroup.centralizer_le (fun a ha => c.XZ_le_XX ha)
  have hWnorm : ((WW t X₁).subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWD).mpr
      (fun d hd => mem_normalizer_pPrimeCoreOf (hDC0 hd))
  have hWW' : WW t X₁ ≤ pPrimeCoreOf 2 D :=
    le_pPrimeCoreOf_of_normal hWD hWnorm (odd_card_pPrimeCoreOf _)
  have hzD : z ∈ D := Subgroup.mem_centralizer_iff.mpr (fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (c.XX_le_Cz ha))
  have htD : cjL t D = D := by rw [hD, cjL_centralizer, c.t_XX]
  have hzW' : z ∈ normalizer ((pPrimeCoreOf 2 D : Subgroup G) : Set G) :=
    mem_normalizer_pPrimeCoreOf hzD
  have htW' : t ∈ normalizer ((pPrimeCoreOf 2 D : Subgroup G) : Set G) := by
    apply mem_normalizer_of_cjL_eq
    rw [← pPrimeCoreOf_cjL, htD]
  have hBW := c.bw_T hzW' htW' (odd_card_pPrimeCoreOf D)
  have hW'le : pPrimeCoreOf 2 D ≤ CZ t X₁ := (pPrimeCoreOf_le' D).trans hDC0
  have hbound : ∀ {s : G} {Xs : Subgroup G}, XsData z t u X₁ s Xs →
      Nat.card ↥(pPrimeCoreOf 2 D ⊓ centralizer ({s} : Set G)) ≤ 25 := by
    intro s Xs h
    have hle : pPrimeCoreOf 2 D ⊓ centralizer ({s} : Set G) ≤ Xs := by
      rintro x ⟨hxW', hxs⟩
      have hxC : x ∈ centralizer ({s} : Set G) ⊓ CZ t X₁ := ⟨hxs, hW'le hxW'⟩
      rw [h.inf_C0] at hxC
      have hodd := odd_card_pPrimeCoreOf D
      have hx5 : x ^ Nat.card ↥(pPrimeCoreOf 2 D) = 1 := pow_card_eq_one_of_mem hxW'
      exact odd_mem_of_two_normalizes h.norm_T c.TT_sq hxC hodd hx5
    calc Nat.card ↥(pPrimeCoreOf 2 D ⊓ centralizer ({s} : Set G)) ≤ Nat.card ↥Xs :=
          Subgroup.card_le_of_le hle
      _ = 25 := h.card
  have hXZle : XZ t X₁ ≤ pPrimeCoreOf 2 D ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := by
    intro x hx
    have hxX : x ∈ XX t X₁ := c.XZ_le_XX hx
    exact ⟨⟨hWW' (hXXW hxX), c.XX_le_Cz hxX⟩, hx.2⟩
  have h5 : 5 ≤ Nat.card ↥(pPrimeCoreOf 2 D ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) := by
    rw [← c.XZ_card]; exact Subgroup.card_le_of_le hXZle
  have hb1 := hbound hz
  have hb2 := hbound ht
  have hb3 := hbound hzt
  have hle625 : Nat.card ↥(pPrimeCoreOf 2 D) ≤ 625 := by
    generalize Nat.card ↥(pPrimeCoreOf 2 D) = n at hBW ⊢
    generalize Nat.card ↥(pPrimeCoreOf 2 D ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) = m
      at hBW h5
    generalize Nat.card ↥(pPrimeCoreOf 2 D ⊓ centralizer ({z} : Set G)) = a at hBW hb1
    generalize Nat.card ↥(pPrimeCoreOf 2 D ⊓ centralizer ({t} : Set G)) = b at hBW hb2
    generalize Nat.card ↥(pPrimeCoreOf 2 D ⊓ centralizer ({z * t} : Set G)) = e at hBW hb3
    have hm2 : 25 ≤ m ^ 2 := by nlinarith
    have habc : a * b * e ≤ 25 * 25 * 25 := Nat.mul_le_mul (Nat.mul_le_mul hb1 hb2) hb3
    have h1 : n * 25 ≤ n * m ^ 2 := Nat.mul_le_mul_left n hm2
    omega
  have hW625 : Nat.card ↥(WW t X₁) = 625 := c.card_W hq hz ht hzt
  have hWeq : WW t X₁ = pPrimeCoreOf 2 D :=
    Subgroup.eq_of_le_of_card_ge hWW' (by rw [hW625]; exact hle625)
  rw [hWeq]
  exact hW'h

theorem Cfg2W.Y_H (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t))
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) : ∀ h ∈ H, cjL h (YW z t u X₁) = YW z t u X₁ := by
  intro h hh
  have hcent : h ∈ centralizer ({z * u} : Set G) := by
    obtain ⟨h1, h2⟩ := c.b66.H_cent h hh
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    calc h * (z * u) = (h * z) * u := by group
      _ = (z * h) * u := by rw [h1]
      _ = z * (h * u) := by group
      _ = z * (u * h) := by rw [h2]
      _ = (z * u) * h := by group
  rw [YW, cjL_inf, c.W_H hq hz ht hzt h hh, cjL_eq_of_mem_normalizer (Subgroup.le_normalizer hcent)]

theorem Cfg2W.card_Y_inf_Ct (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t))
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) :
    Nat.card ↥(YW z t u X₁ ⊓ centralizer ({t} : Set G)) = 5 := by
  have hXX := c.XX_eq_Xz hq hz
  have hWinv := c.W_inv hz ht hzt
  have hzt' : z * u = u * z := c.hs.zu_comm
  have hB : ∀ a, a ∈ XZ t X₁ ↔ a ∈ Xt ∧ z * a * z⁻¹ = a := by
    intro a
    constructor
    · intro ha
      have haX : a ∈ XX t X₁ := c.XZ_le_XX ha
      have hat : t * a * t⁻¹ = a := ((c.mem_XZ).1 ha).2
      refine ⟨?_, ?_⟩
      · rw [← ht.cent]
        refine ⟨c.XX_le_W hq hz haX, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc a * t = (t * a * t⁻¹) * t := by rw [hat]
          _ = t * a := by group
      · have := Subgroup.mem_centralizer_singleton_iff.mp (c.XX_le_Cz haX)
        calc z * a * z⁻¹ = (a * z) * z⁻¹ := by rw [this]
          _ = a := by group
    · rintro ⟨haXt, haz⟩
      have haWt : a ∈ WW t X₁ ⊓ centralizer ({t} : Set G) := by rw [ht.cent]; exact haXt
      have haXz : a ∈ Xz := by
        rw [← hz.cent]
        refine ⟨haWt.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc a * z = (z * a * z⁻¹) * z := by rw [haz]
          _ = z * a := by group
      rw [c.mem_XZ]
      refine ⟨by rw [hXX]; exact haXz, ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp haWt.2
      calc t * a * t⁻¹ = (a * t) * t⁻¹ := by rw [this]
        _ = a := by group
  have hcomm : ∀ a ∈ Xt, ∀ b ∈ Xt, a * b = b * a := fun a ha b hb =>
    c.W_comm hz ht hzt a (ht.le_W ha) b (ht.le_W hb)
  have hnormz : ∀ a ∈ Xt, z * a * z⁻¹ ∈ Xt := fun a ha => ht.norm_T z c.z_mem_TT a ha
  have hu2 : u * u = 1 := c.hs.u_sq
  have hui2 : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
  set I := YW z t u X₁ ⊓ centralizer ({t} : Set G) with hI
  have hI' : ∀ a, a ∈ I ↔ a ∈ Xt ∧ z * a * z⁻¹ = a⁻¹ := by
    intro a
    constructor
    · rintro ⟨⟨haW, haZU⟩, hat⟩
      refine ⟨by rw [← ht.cent]; exact ⟨haW, hat⟩, ?_⟩
      have h1 : a * (z * u) = (z * u) * a := Subgroup.mem_centralizer_singleton_iff.mp haZU
      have h2 : u * a * u⁻¹ = a⁻¹ := hWinv a haW
      have h3 : z * a⁻¹ * z⁻¹ = a := by
        calc z * a⁻¹ * z⁻¹ = z * (u * a * u⁻¹) * z⁻¹ := by rw [h2]
          _ = ((z * u) * a) * (z * u)⁻¹ := by group
          _ = (a * (z * u)) * (z * u)⁻¹ := by rw [h1]
          _ = a := by group
      calc z * a * z⁻¹ = (z * a⁻¹ * z⁻¹)⁻¹ := by group
        _ = a⁻¹ := by rw [h3]
    · rintro ⟨haXt, haz⟩
      have haWt : a ∈ WW t X₁ ⊓ centralizer ({t} : Set G) := by rw [ht.cent]; exact haXt
      refine ⟨⟨haWt.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, haWt.2⟩
      have h2 : u * a * u⁻¹ = a⁻¹ := hWinv a haWt.1
      have h3 : (z * u) * a * (z * u)⁻¹ = a := by
        calc (z * u) * a * (z * u)⁻¹ = z * (u * a * u⁻¹) * z⁻¹ := by group
          _ = z * a⁻¹ * z⁻¹ := by rw [h2]
          _ = (z * a * z⁻¹)⁻¹ := by group
          _ = a := by rw [haz, inv_inv]
      calc a * (z * u) = ((z * u) * a * (z * u)⁻¹) * (z * u) := by rw [h3]
        _ = (z * u) * a := by group
  have hcard := card_eq_fixed_mul_inv5 (A := Xt) (B := XZ t X₁) (I := I) (g := z) c.hs.z_sq hnormz
    hcomm ht.pow hB hI'
  rw [ht.card, c.XZ_card] at hcard
  omega

theorem Cfg2W.exists_Y83 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t)) :
    ∃ Y : Subgroup G, Five83 z t u H X₁ Y := by
  obtain ⟨Xz, Xt, Xzt, hz, ht, hzt⟩ := c.three_Xs hq
  have hW := c.XX_sup_Y hq hz ht hzt
  have hWcard := c.card_W hq hz ht hzt
  have hWpow := c.W_pow hq hz ht hzt
  have hWcomm := c.W_comm hz ht hzt
  have hWinv := c.W_inv hz ht hzt
  refine ⟨YW z t u X₁, ?_⟩
  have hYW : YW z t u X₁ ≤ WW t X₁ := inf_le_left
  have hel : IsElemAb 5 (XX t X₁ ⊔ YW z t u X₁) := by
    rw [hW]; exact ⟨hWcomm, hWpow⟩
  have hCzu : Nat.card ↥(centralizer ({z * u} : Set G)) = 28800 := c.card_cent_of_conj c.zu_conj
  refine ⟨c.card_Y hq hz ht hzt, ⟨fun a ha b hb => hWcomm a (hYW ha) b (hYW hb),
    fun a ha => hWpow a (hYW ha)⟩, hel, ?_, c.XX_inf_Y, hW.symm, ?_, ?_, c.Y_H hq hz ht hzt,
    c.card_Y_inf_Ct hq hz ht hzt, ?_⟩
  · rw [hW, hWcard]; norm_num
  · intro w hw
    rw [hW] at hw
    exact hWinv w hw
  · refine ⟨inf_le_right, ?_, ?_⟩
    · exact IsPGroup.of_card (n := 2) (by rw [c.card_Y hq hz ht hzt]; norm_num)
    · have h1 := Subgroup.index_mul_card ((YW z t u X₁).subgroupOf (centralizer ({z * u} : Set G)))
      have h2 : Nat.card ↥((YW z t u X₁).subgroupOf (centralizer ({z * u} : Set G))) = 25 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
          c.card_Y hq hz ht hzt]
      rw [h2, hCzu] at h1
      intro h5
      omega
  · have h := hq.five_val
    rw [hWcard] at h
    have : (625 : ℕ).factorization 5 = 4 := by
      have h4 : (625 : ℕ) = 5 ^ 4 := by norm_num
      rw [h4, Nat.Prime.factorization_pow Nat.prime_five]
      simp
    omega

end L83f

end CFSG.GH74.GLS.LU.Local.Five
