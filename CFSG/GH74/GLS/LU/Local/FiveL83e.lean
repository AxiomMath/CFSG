module

public import CFSG.GH74.GLS.LU.Local.FiveL83d

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L83e

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {X₁ : Subgroup G}

theorem Cfg2W.z_mem_TT (_c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : z ∈ TT z t :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers z)

theorem Cfg2W.t_mem_TT (_c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : t ∈ TT z t :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem Cfg2W.W_inf_Cu (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁)
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) :
    WW t X₁ ⊓ centralizer ({u} : Set G) = ⊥ := by
  set P := WW t X₁ ⊓ centralizer ({u} : Set G) with hP
  have hzu : z ∈ centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr c.hs.zu_comm
  have htu : t ∈ centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr c.hs.ut.symm
  have hzP : z ∈ normalizer (P : Set G) :=
    mem_normalizer_inf (c.TT_le_normalizer_W c.z_mem_TT) (Subgroup.le_normalizer hzu)
  have htP : t ∈ normalizer (P : Set G) :=
    mem_normalizer_inf (c.TT_le_normalizer_W c.t_mem_TT) (Subgroup.le_normalizer htu)
  have hodd : Odd (Nat.card ↥P) :=
    Odd.of_dvd_nat (odd_card_pPrimeCoreOf (CZ t X₁)) (Subgroup.card_dvd_of_le inf_le_left)
  have hPs : ∀ {s : G} {Xs : Subgroup G}, XsData z t u X₁ s Xs → P ⊓ centralizer ({s} : Set G) = ⊥ := by
    intro s Xs h
    rw [eq_bot_iff]
    rintro x ⟨⟨hxW, hxu⟩, hxs⟩
    have hx : x ∈ Xs := by rw [← h.cent]; exact ⟨hxW, hxs⟩
    have := h.inf_Cu
    rw [eq_bot_iff] at this
    exact this ⟨hx, hxu⟩
  have hBW := c.bw_T hzP htP hodd
  rw [hPs hz, hPs ht, hPs hzt, bot_inf_eq] at hBW
  simp only [Subgroup.card_bot, one_pow, mul_one] at hBW
  exact Subgroup.eq_bot_of_card_eq _ hBW

theorem Cfg2W.W_inv (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁)
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) : ∀ w ∈ WW t X₁, u * w * u⁻¹ = w⁻¹ :=
  CFSG.Walter.J1.inv_of_inf_centralizer_eq_bot c.hs.u_sq c.u_mem_normalizer_W (c.W_inf_Cu hz ht hzt)

theorem Cfg2W.W_comm (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁)
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) : ∀ a ∈ WW t X₁, ∀ b ∈ WW t X₁, a * b = b * a := by
  intro a ha b hb
  have h := CFSG.Walter.J1.le_centralizer_of_inv (c.W_inv hz ht hzt) ha
  exact (Subgroup.mem_centralizer_iff.mp h b hb).symm

theorem Cfg2W.W_eq_R (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t))
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) : Xz ⊔ Xt ⊔ Xzt = WW t X₁ := by
  have hXX := c.XX_eq_Xz hq hz
  have hRW : Xz ⊔ Xt ⊔ Xzt ≤ WW t X₁ := sup_le (sup_le hz.le_W ht.le_W) hzt.le_W
  have hRodd : Odd (Nat.card ↥(Xz ⊔ Xt ⊔ Xzt)) :=
    Odd.of_dvd_nat (odd_card_pPrimeCoreOf (CZ t X₁)) (Subgroup.card_dvd_of_le hRW)
  have hnormT : ∀ g ∈ TT z t, g ∈ normalizer ((Xz ⊔ Xt ⊔ Xzt : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_of_cjL_eq
    rw [cjL_sup, cjL_sup, cjL_eq_of_mem_normalizer (hz.mem_normalizer hg),
      cjL_eq_of_mem_normalizer (ht.mem_normalizer hg),
      cjL_eq_of_mem_normalizer (hzt.mem_normalizer hg)]
  have key : ∀ {s : G} {Xs : Subgroup G}, XsData z t u X₁ s Xs → Xs ≤ Xz ⊔ Xt ⊔ Xzt →
      (Xz ⊔ Xt ⊔ Xzt) ⊓ centralizer ({s} : Set G) = Xs := by
    intro s Xs h hle
    apply le_antisymm
    · intro x hx
      rw [← h.cent]
      exact ⟨hRW hx.1, hx.2⟩
    · intro x hx
      have hx' : x ∈ WW t X₁ ⊓ centralizer ({s} : Set G) := by rw [h.cent]; exact hx
      exact ⟨hle hx, hx'.2⟩
  have hkz := key hz (le_sup_left.trans le_sup_left)
  have hkt := key ht (le_sup_right.trans le_sup_left)
  have hkzt := key hzt le_sup_right
  have hBW := c.bw_T (K := Xz ⊔ Xt ⊔ Xzt) (hnormT z c.z_mem_TT) (hnormT t c.t_mem_TT) hRodd
  have hC : Nat.card ↥(Xz ⊓ centralizer ({t} : Set G)) = 5 := by
    rw [← hXX]; exact c.XZ_card
  rw [hkz, hkt, hkzt, hC, hz.card, ht.card, hzt.card] at hBW
  norm_num at hBW
  have hR : Nat.card ↥(Xz ⊔ Xt ⊔ Xzt) = 625 := by omega
  have hW : Nat.card ↥(WW t X₁) = 625 := c.card_W hq hz ht hzt
  exact Subgroup.eq_of_le_of_card_ge hRW (by rw [hR, hW])

theorem Cfg2W.W_pow (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t))
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) : ∀ w ∈ WW t X₁, w ^ 5 = 1 := by
  have hcomm := c.W_comm hz ht hzt
  have h1 : ∀ a ∈ Xz ⊔ Xt, ∀ b ∈ Xzt, a * b = b * a := fun a ha b hb =>
    hcomm a ((sup_le hz.le_W ht.le_W) ha) b (hzt.le_W hb)
  have h2 : ∀ a ∈ Xz, ∀ b ∈ Xt, a * b = b * a := fun a ha b hb =>
    hcomm a (hz.le_W ha) b (ht.le_W hb)
  rw [← c.W_eq_R hq hz ht hzt]
  exact sup_pow_eq_one h1 (sup_pow_eq_one h2 hz.pow ht.pow) hzt.pow

end L83e

end CFSG.GH74.GLS.LU.Local.Five
