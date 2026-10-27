module

public import CFSG.GH74.GLS.LU.Local.FiveL83c

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L83d

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {X₁ : Subgroup G}

abbrev WW (t : G) (X₁ : Subgroup G) : Subgroup G := pPrimeCoreOf 2 (CZ t X₁)

structure C0Quot (C T : Subgroup G) : Prop where
  five_mem : ∀ x ∈ C, x ^ 5 = 1 → ∀ s ∈ T, s ≠ 1 → s * x = x * s → x ∈ pPrimeCoreOf 2 C
  five_val : (Nat.card ↥C).factorization 5 ≤ (Nat.card ↥(pPrimeCoreOf 2 C)).factorization 5 + 1

structure XsData (z t u : G) (X₁ : Subgroup G) (s : G) (Xs : Subgroup G) : Prop where
  le_W : Xs ≤ WW t X₁
  ab : ∀ a ∈ Xs, ∀ b ∈ Xs, a * b = b * a
  pow : ∀ a ∈ Xs, a ^ 5 = 1
  card : Nat.card ↥Xs = 25
  u_inv : ∀ x ∈ Xs, u * x * u⁻¹ = x⁻¹
  norm_T : ∀ τ ∈ TT z t, ∀ x ∈ Xs, τ * x * τ⁻¹ ∈ Xs
  cent : WW t X₁ ⊓ centralizer ({s} : Set G) = Xs
  inf_C0 : centralizer ({s} : Set G) ⊓ CZ t X₁ = Xs ⊔ TT z t

theorem Cfg2W.xsData (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t)) {s : G}
    (hs : s ∈ TT z t) (hs1 : s ≠ 1) : ∃ Xs, XsData z t u X₁ s Xs := by
  obtain ⟨Xs, -, hXsab, hXscard, hXsinv, hXscent, -, hXsnorm⟩ := c.b82.C0_struct s hs hs1
  have hsT : ∀ τ ∈ TT z t, τ ∈ centralizer ({s} : Set G) ⊓ CZ t X₁ := fun τ hτ =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (c.TT_comm τ hτ s hs), c.T_le_C0 hτ⟩
  have hXsle : ∀ x ∈ Xs, x ∈ centralizer ({s} : Set G) ⊓ CZ t X₁ := fun x hx => by
    rw [hXscent]; exact Subgroup.mem_sup_left hx
  have hXsW : Xs ≤ WW t X₁ := by
    intro x hx
    obtain ⟨hxs, hxC⟩ := hXsle x hx
    exact hq.five_mem x hxC (hXsab.2 x hx) s hs hs1
      (Subgroup.mem_centralizer_singleton_iff.mp hxs).symm
  refine ⟨Xs, hXsW, hXsab.1, hXsab.2, hXscard, hXsinv,
    fun τ hτ x hx => hXsnorm τ (hsT τ hτ) x hx, ?_, hXscent⟩
  apply le_antisymm
  · rintro w ⟨hwW, hws⟩
    have hwC : w ∈ centralizer ({s} : Set G) ⊓ CZ t X₁ := ⟨hws, pPrimeCoreOf_le' _ hwW⟩
    rw [hXscent] at hwC
    have hodd := odd_card_pPrimeCoreOf (CZ t X₁)
    have hw5 : w ^ Nat.card ↥(WW t X₁) = 1 := pow_card_eq_one_of_mem hwW
    exact odd_mem_of_two_normalizes (fun τ hτ a ha => hXsnorm τ (hsT τ hτ) a ha) c.TT_sq hwC hodd hw5
  · intro x hx
    exact ⟨hXsW hx, (hXsle x hx).1⟩

theorem Cfg2W.zt_mem_TT (_c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : z * t ∈ TT z t :=
  mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

theorem Cfg2W.zt_ne_one (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : z * t ≠ 1 := by
  intro h
  have h1 : t = z⁻¹ := eq_inv_of_mul_eq_one_right h
  have h2 : z⁻¹ = z := inv_eq_of_mul_eq_one_right c.hs.z_sq
  exact c.t_ne_z (h1.trans h2)

theorem Cfg2W.three_Xs (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t)) :
    ∃ Xz Xt Xzt, XsData z t u X₁ z Xz ∧ XsData z t u X₁ t Xt ∧ XsData z t u X₁ (z * t) Xzt := by
  obtain ⟨Xz, hz⟩ := c.xsData hq (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)) c.z_ne_one
  obtain ⟨Xt, ht⟩ := c.xsData hq (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) c.t_ne_one
  obtain ⟨Xzt, hzt⟩ := c.xsData hq c.zt_mem_TT c.zt_ne_one
  exact ⟨Xz, Xt, Xzt, hz, ht, hzt⟩

theorem Cfg2W.bw_T (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) {K : Subgroup G}
    (hz : z ∈ normalizer (K : Set G)) (ht : t ∈ normalizer (K : Set G)) (hodd : Odd (Nat.card ↥K)) :
    Nat.card ↥K * Nat.card ↥(K ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) ^ 2 =
      Nat.card ↥(K ⊓ centralizer ({z} : Set G)) * Nat.card ↥(K ⊓ centralizer ({t} : Set G)) *
        Nat.card ↥(K ⊓ centralizer ({z * t} : Set G)) :=
  CFSG.Walter.J1.card_mul_card_sq_eq_mul c.hs.z_sq c.t_sq c.z_ne_one c.t_ne_one c.t_ne_z.symm
    c.tz_comm.symm K hz ht hodd

theorem Cfg2W.u_ne_one (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : u ≠ 1 := by
  intro h
  have := c.hs.u_ord
  rw [h, orderOf_one] at this
  omega

theorem Cfg2W.bw_U (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) {K : Subgroup G}
    (hz : z ∈ normalizer (K : Set G)) (hu : u ∈ normalizer (K : Set G)) (hodd : Odd (Nat.card ↥K)) :
    Nat.card ↥K * Nat.card ↥(K ⊓ centralizer ({z} : Set G) ⊓ centralizer ({u} : Set G)) ^ 2 =
      Nat.card ↥(K ⊓ centralizer ({z} : Set G)) * Nat.card ↥(K ⊓ centralizer ({u} : Set G)) *
        Nat.card ↥(K ⊓ centralizer ({z * u} : Set G)) :=
  CFSG.Walter.J1.card_mul_card_sq_eq_mul c.hs.z_sq c.hs.u_sq c.z_ne_one c.u_ne_one
    (fun h => c.hs.u_ne h.symm) c.hs.zu_comm K hz hu hodd

theorem Cfg2W.TT_le_normalizer_W (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) {τ : G} (hτ : τ ∈ TT z t) :
    τ ∈ normalizer ((WW t X₁ : Subgroup G) : Set G) :=
  mem_normalizer_pPrimeCoreOf (c.T_le_C0 hτ)

theorem Cfg2W.u_mem_normalizer_C0 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    u ∈ normalizer ((CZ t X₁ : Subgroup G) : Set G) :=
  CFSG.Walter.J1.mem_normalizer_of_conj_mem c.u_norm_C0

theorem Cfg2W.u_cjL_W (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : cjL u (WW t X₁) = WW t X₁ := by
  have h : cjL u (CZ t X₁) = CZ t X₁ := cjL_eq_of_mem_normalizer c.u_mem_normalizer_C0
  have := pPrimeCoreOf_cjL u (CZ t X₁)
  rw [h] at this
  exact this.symm

theorem Cfg2W.u_mem_normalizer_W (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    u ∈ normalizer ((WW t X₁ : Subgroup G) : Set G) :=
  mem_normalizer_of_cjL_eq c.u_cjL_W

section XsLemmas

variable (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁)

theorem XsData.mem_normalizer {s : G} {Xs : Subgroup G} (h : XsData z t u X₁ s Xs) {τ : G}
    (hτ : τ ∈ TT z t) : τ ∈ normalizer (Xs : Set G) :=
  CFSG.Walter.J1.mem_normalizer_of_conj_mem (fun x hx => h.norm_T τ hτ x hx)

omit [Finite G] in
theorem XsData.inf_Cu {s : G} {Xs : Subgroup G} (h : XsData z t u X₁ s Xs) :
    Xs ⊓ centralizer ({u} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxu⟩
  have h1 : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxu
  have h2 : u * x * u⁻¹ = x⁻¹ := h.u_inv x hx
  have h3 : u * x * u⁻¹ = x := by
    calc u * x * u⁻¹ = (x * u) * u⁻¹ := by rw [h1]
      _ = x := by group
  have hxx : x = x⁻¹ := h3.symm.trans h2
  have hsq : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← hxx]
      _ = 1 := mul_inv_cancel x
  have hx5 : x ^ 5 = 1 := h.pow x hx
  have : x = 1 := by
    calc x = x ^ 5 * ((x * x)⁻¹) ^ 2 := by group
      _ = 1 := by rw [hx5, hsq]; simp
  rw [this]; exact Subgroup.one_mem _

end XsLemmas

theorem Cfg2W.XX_eq_Xz (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t))
    {Xz : Subgroup G} (hz : XsData z t u X₁ z Xz) : XX t X₁ = Xz := by
  have hzT : z ∈ TT z t := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have hle : XX t X₁ ≤ Xz := by
    intro x hx
    have hxW : x ∈ WW t X₁ :=
      hq.five_mem x (c.XX_le_C0 hx) (c.XX_pow x hx) z hzT c.z_ne_one
        (Subgroup.mem_centralizer_singleton_iff.mp (c.XX_le_Cz hx)).symm
    rw [← hz.cent]
    exact ⟨hxW, c.XX_le_Cz hx⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hz.card, c.XX_card2])

theorem Cfg2W.XX_le_W (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t))
    {Xz : Subgroup G} (hz : XsData z t u X₁ z Xz) : XX t X₁ ≤ WW t X₁ := by
  rw [c.XX_eq_Xz hq hz]; exact hz.le_W

theorem Cfg2W.card_W (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) (hq : C0Quot (CZ t X₁) (TT z t))
    {Xz Xt Xzt : Subgroup G} (hz : XsData z t u X₁ z Xz) (ht : XsData z t u X₁ t Xt)
    (hzt : XsData z t u X₁ (z * t) Xzt) : Nat.card ↥(WW t X₁) = 625 := by
  have hBW := c.bw_T (K := WW t X₁) (c.TT_le_normalizer_W (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)))
    (c.TT_le_normalizer_W (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
    (odd_card_pPrimeCoreOf _)
  have hC : Nat.card ↥(Xz ⊓ centralizer ({t} : Set G)) = 5 := by
    rw [← c.XX_eq_Xz hq hz]; exact c.XZ_card
  rw [hz.cent, ht.cent, hzt.cent, hC, hz.card, ht.card, hzt.card] at hBW
  norm_num at hBW
  omega

end L83d

end CFSG.GH74.GLS.LU.Local.Five
