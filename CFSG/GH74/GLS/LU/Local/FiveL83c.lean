module

public import CFSG.GH74.GLS.LU.Local.FiveL83b
public import CFSG.GH74.GLS.LU.Local.FiveL83a

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L83c

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {X₁ : Subgroup G}

theorem Cfg2W.X1_comm_XB (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ a ∈ X₁, ∀ b ∈ XB t X₁, a * b = b * a := fun a ha b hb =>
  c.hc.comm a (c.b82.X₁_syl.1 ha) b (c.X2_le_K2 hb)

theorem Cfg2W.XX_comm2 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ a ∈ XX t X₁, ∀ b ∈ XX t X₁, a * b = b * a :=
  commute_sup (comm_of_card_five c.b82.X₁_card) (comm_of_card_five c.card_X2) c.X1_comm_XB

theorem Cfg2W.XX_pow (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : ∀ a ∈ XX t X₁, a ^ 5 = 1 :=
  sup_pow_eq_one c.X1_comm_XB (fun _ ha => pow_five_of_card c.b82.X₁_card ha)
    (fun _ ha => pow_five_of_card c.card_X2 ha)

theorem Cfg2W.X1_inf_XB (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : X₁ ⊓ XB t X₁ = ⊥ := by
  have h := c.five_inf_K2 c.b82.X₁_syl.1 c.b82.X₁_card
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ X₁ ⊓ K₂ := ⟨hx.1, c.X2_le_K2 hx.2⟩
  rw [h] at this
  exact this

theorem Cfg2W.XX_card2 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : Nat.card ↥(XX t X₁) = 25 := by
  rw [XX, card_sup_of_commute_disjoint c.X1_comm_XB c.X1_inf_XB, c.b82.X₁_card, c.card_X2]

theorem Cfg2W.XX_le_Cz (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    XX t X₁ ≤ centralizer ({z} : Set G) := by
  refine sup_le ?_ ?_
  · intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (c.hc.cz₁ (c.b82.X₁_syl.1 ha))
  · intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (c.hc.cz₂ (c.X2_le_K2 ha))

theorem Cfg2W.t_normXX (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ a ∈ XX t X₁, t * a * t⁻¹ ∈ XX t X₁ := by
  intro a ha
  have := mem_cjL_self (g := t) ha
  rwa [c.t_XX] at this

theorem Cfg2W.XZ_le_XX (_c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : XZ t X₁ ≤ XX t X₁ := inf_le_left

theorem Cfg2W.mem_XZ (_c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) {a : G} :
    a ∈ XZ t X₁ ↔ a ∈ XX t X₁ ∧ t * a * t⁻¹ = a := by
  constructor
  · rintro ⟨ha, hat⟩
    refine ⟨ha, ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp hat
    calc t * a * t⁻¹ = (a * t) * t⁻¹ := by rw [h]
      _ = a := by group
  · rintro ⟨ha, hat⟩
    refine ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc a * t = (t * a * t⁻¹) * t := by rw [hat]
      _ = t * a := by group

theorem Cfg2W.XZ_card (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : Nat.card ↥(XZ t X₁) = 5 := by
  have hcomm := c.XX_comm2
  set I := invSub (XX t X₁) t hcomm with hI
  have hcard := card_eq_fixed_mul_inv5 (A := XX t X₁) (B := XZ t X₁) (I := I) (g := t) c.t_sq
    c.t_normXX hcomm c.XX_pow (fun _ => c.mem_XZ) (fun _ => mem_invSub)
  rw [c.XX_card2] at hcard
  obtain ⟨x₁, hx₁, hx₁1⟩ := exists_ne_one_of_card_gt_one (A := X₁) (by rw [c.b82.X₁_card]; norm_num)
  have hx₂ : t * x₁ * t⁻¹ ∈ XB t X₁ := mem_cjL_self hx₁
  have hx₁XX : x₁ ∈ XX t X₁ := Subgroup.mem_sup_left hx₁
  have hx₂XX : t * x₁ * t⁻¹ ∈ XX t X₁ := Subgroup.mem_sup_right hx₂
  have hdd : t * (t * x₁ * t⁻¹) * t⁻¹ = x₁ := by
    calc t * (t * x₁ * t⁻¹) * t⁻¹ = (t * t) * x₁ * (t⁻¹ * t⁻¹) := by group
      _ = x₁ := by
        have : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, c.t_sq, inv_one]
        rw [c.t_sq, this]; group
  have hcm : x₁ * (t * x₁ * t⁻¹) = (t * x₁ * t⁻¹) * x₁ := hcomm _ hx₁XX _ hx₂XX
  have hB : x₁ * (t * x₁ * t⁻¹) ∈ XZ t X₁ := by
    rw [c.mem_XZ]
    refine ⟨mul_mem hx₁XX hx₂XX, ?_⟩
    calc t * (x₁ * (t * x₁ * t⁻¹)) * t⁻¹ = (t * x₁ * t⁻¹) * (t * (t * x₁ * t⁻¹) * t⁻¹) := by group
      _ = (t * x₁ * t⁻¹) * x₁ := by rw [hdd]
      _ = x₁ * (t * x₁ * t⁻¹) := hcm.symm
  have hBne : x₁ * (t * x₁ * t⁻¹) ≠ 1 := by
    intro h1
    have h2 : x₁ = (t * x₁ * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : x₁ ∈ X₁ ⊓ XB t X₁ := ⟨hx₁, by rw [h2]; exact Subgroup.inv_mem _ hx₂⟩
    rw [c.X1_inf_XB] at h3
    exact hx₁1 (Subgroup.mem_bot.mp h3)
  have hI1 : x₁ * (t * x₁ * t⁻¹)⁻¹ ∈ I := by
    rw [hI, mem_invSub]
    refine ⟨mul_mem hx₁XX (inv_mem hx₂XX), ?_⟩
    calc t * (x₁ * (t * x₁ * t⁻¹)⁻¹) * t⁻¹
        = (t * x₁ * t⁻¹) * (t * (t * x₁ * t⁻¹) * t⁻¹)⁻¹ := by group
      _ = (t * x₁ * t⁻¹) * x₁⁻¹ := by rw [hdd]
      _ = (x₁ * (t * x₁ * t⁻¹)⁻¹)⁻¹ := by group
  have hIne : x₁ * (t * x₁ * t⁻¹)⁻¹ ≠ 1 := by
    intro h1
    have h2 : x₁ = t * x₁ * t⁻¹ := by
      have := eq_of_mul_inv_eq_one h1
      exact this
    have h3 : x₁ ∈ X₁ ⊓ XB t X₁ := ⟨hx₁, by rw [h2]; exact hx₂⟩
    rw [c.X1_inf_XB] at h3
    exact hx₁1 (Subgroup.mem_bot.mp h3)
  have hBgt : 1 < Nat.card ↥(XZ t X₁) := by
    by_contra hle
    have h1 : Nat.card ↥(XZ t X₁) = 1 := le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle))
      Nat.card_pos
    have hbot := Subgroup.eq_bot_of_card_eq _ h1
    rw [hbot] at hB
    exact hBne (Subgroup.mem_bot.mp hB)
  have hIgt : 1 < Nat.card ↥I := by
    by_contra hle
    have h1 : Nat.card ↥I = 1 := le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle))
      Nat.card_pos
    have hbot := Subgroup.eq_bot_of_card_eq _ h1
    rw [hbot] at hI1
    exact hIne (Subgroup.mem_bot.mp hI1)
  have hdvd : Nat.card ↥(XZ t X₁) ∣ 25 := Dvd.intro _ hcard.symm
  have hle : Nat.card ↥(XZ t X₁) ≤ 25 := Nat.le_of_dvd (by norm_num) hdvd
  generalize Nat.card ↥(XZ t X₁) = b at hcard hBgt hdvd hle
  generalize Nat.card ↥I = i at hcard hIgt
  interval_cases b <;> omega

theorem Cfg2W.XX_le_C0 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : XX t X₁ ≤ CZ t X₁ := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact c.XX_comm2 h (c.XZ_le_XX hh) x hx

theorem Cfg2W.T_le_C0 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : TT z t ≤ CZ t X₁ := by
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (c.XX_le_Cz (c.XZ_le_XX hh))
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp hh.2

theorem Cfg2W.card_C0_two (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    (Nat.card ↥(CZ t X₁)).factorization 2 = 2 := by
  obtain ⟨hle, -, hnd⟩ := c.b82.T_syl
  have h1 := Subgroup.index_mul_card ((TT z t).subgroupOf (CZ t X₁))
  have h2 : Nat.card ↥((TT z t).subgroupOf (CZ t X₁)) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, c.card_TT]
  rw [h2] at h1
  rw [← h1, Nat.factorization_mul (by
    intro h0; rw [h0] at hnd; exact hnd (dvd_zero 2)) (by norm_num)]
  simp only [Finsupp.add_apply]
  rw [Nat.factorization_eq_zero_of_not_dvd hnd]
  have : (4 : ℕ).factorization 2 = 2 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  rw [this]

theorem Cfg2W.u_comm_TT (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : ∀ a ∈ TT z t, u * a = a * u := by
  have : TT z t ≤ centralizer ({u} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr c.hs.zu_comm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr c.hs.ut.symm
  intro a ha
  exact (Subgroup.mem_centralizer_singleton_iff.mp (this ha)).symm

theorem Cfg2W.u_inv_XX (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ x ∈ XX t X₁, u * x * u⁻¹ = x⁻¹ := by
  have hz : z ∈ TT z t := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  obtain ⟨Xs, -, -, hXscard, hXsinv, hXscent, -, hXsnorm⟩ := c.b82.C0_struct z hz c.z_ne_one
  have hTz : ∀ τ ∈ TT z t, τ ∈ centralizer ({z} : Set G) ⊓ CZ t X₁ := fun τ hτ =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (c.TT_comm τ hτ z hz), c.T_le_C0 hτ⟩
  have hXXle : XX t X₁ ≤ Xs := by
    intro x hx
    have hxC : x ∈ centralizer ({z} : Set G) ⊓ CZ t X₁ := ⟨c.XX_le_Cz hx, c.XX_le_C0 hx⟩
    rw [hXscent] at hxC
    exact odd_mem_of_two_normalizes (fun τ hτ a ha => hXsnorm τ (hTz τ hτ) a ha) c.TT_sq hxC
      (m := 5) (by decide) (c.XX_pow x hx)
  have hXXeq : XX t X₁ = Xs :=
    Subgroup.eq_of_le_of_card_ge hXXle (by rw [hXscard, c.XX_card2])
  intro x hx
  rw [hXXeq] at hx
  exact hXsinv x hx

theorem Cfg2W.u_normXX (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ x ∈ XX t X₁, u * x * u⁻¹ ∈ XX t X₁ := by
  intro x hx
  rw [c.u_inv_XX x hx]
  exact inv_mem hx

theorem Cfg2W.u_norm_XZ (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ x ∈ XZ t X₁, u * x * u⁻¹ ∈ XZ t X₁ := by
  intro x hx
  rw [c.mem_XZ] at hx ⊢
  refine ⟨c.u_normXX x hx.1, ?_⟩
  have hut : u * t = t * u := c.hs.ut
  calc t * (u * x * u⁻¹) * t⁻¹ = u * (t * x * t⁻¹) * u⁻¹ := by
        calc t * (u * x * u⁻¹) * t⁻¹ = (t * u) * x * (t * u)⁻¹ := by group
          _ = (u * t) * x * (u * t)⁻¹ := by rw [hut]
          _ = u * (t * x * t⁻¹) * u⁻¹ := by group
    _ = u * x * u⁻¹ := by rw [hx.2]

theorem Cfg2W.u_norm_C0 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ x ∈ CZ t X₁, u * x * u⁻¹ ∈ CZ t X₁ := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hu2 : u * u = 1 := c.hs.u_sq
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hh' : u⁻¹ * h * u ∈ XZ t X₁ := by
    have := c.u_norm_XZ h hh
    rw [hui] at this ⊢
    exact this
  have h1 := (Subgroup.mem_centralizer_iff.mp hx) _ hh'
  calc h * (u * x * u⁻¹) = u * ((u⁻¹ * h * u) * x) * u⁻¹ := by group
    _ = u * (x * (u⁻¹ * h * u)) * u⁻¹ := by rw [h1]
    _ = (u * x * u⁻¹) * h := by
        calc u * (x * (u⁻¹ * h * u)) * u⁻¹ = (u * x * u⁻¹) * (u * u⁻¹ * h * (u * u⁻¹)) := by group
          _ = (u * x * u⁻¹) * h := by simp

theorem Cfg2W.u_not_mem_C0 (c : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁) : u ∉ CZ t X₁ := by
  intro hu
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_gt_one (A := XZ t X₁)
    (by rw [c.XZ_card]; norm_num)
  have h1 : x * u = u * x := (Subgroup.mem_centralizer_iff.mp hu) x hx
  have h2 : u * x * u⁻¹ = x⁻¹ := c.u_inv_XX x (c.XZ_le_XX hx)
  have h3 : u * x * u⁻¹ = x := by
    calc u * x * u⁻¹ = (x * u) * u⁻¹ := by rw [h1]
      _ = x := by group
  have hxx : x = x⁻¹ := h3.symm.trans h2
  have hsq : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← hxx]
      _ = 1 := mul_inv_cancel x
  have hx5 : x ^ 5 = 1 := c.XX_pow x (c.XZ_le_XX hx)
  apply hx1
  calc x = x ^ 5 * ((x * x)⁻¹) ^ 2 := by group
    _ = 1 := by rw [hx5, hsq]; simp

end L83c

end CFSG.GH74.GLS.LU.Local.Five
