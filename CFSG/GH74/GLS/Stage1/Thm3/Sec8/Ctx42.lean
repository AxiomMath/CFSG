module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx41
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic10
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic11
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic12
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx40

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem Nh_conj_h (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {d : G}
    (hd : d ∈ Nh S h) : d * h * d⁻¹ = h ∨ d * h * d⁻¹ = h⁻¹ := by
  obtain ⟨m, hm⟩ := hs.h_order
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.1 (hs.S_pgroup hII)) ⟨d, hd.1⟩
  have he' : orderOf d = 2 ^ e := by
    rw [← Subgroup.orderOf_mk d hd.1]
    exact he
  have hd2 : d ^ (2 ^ e) = 1 := by
    rw [← he']
    exact pow_orderOf_eq_one d
  have hn : d * h * d⁻¹ ∈ zpowers h :=
    (Subgroup.mem_normalizer_iff.1 hd.2 h).1 (Subgroup.mem_zpowers h)
  exact Basic.normalizing_two_power_inv hm hd2 hn

theorem W_Nh_comm (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G}
    (hxW : x ∈ Wsub S U) (hxD : x ∈ Nh S h) : x * h = h * x := by
  rcases hs.Nh_conj_h hII hxD with h1 | h1
  · calc x * h = (x * h * x⁻¹) * x := by group
      _ = h * x := by rw [h1]
  · exfalso
    have h2 : h * x⁻¹ * h⁻¹ ∈ Wsub S U :=
      ((Subgroup.mem_normalizer_iff.1 hs.h_W x⁻¹).1 (inv_mem hxW))
    have hc : x * h * x⁻¹ * h⁻¹ ∈ Wsub S U := by
      have e : x * h * x⁻¹ * h⁻¹ = x * (h * x⁻¹ * h⁻¹) := by group
      rw [e]
      exact mul_mem hxW h2
    rw [h1] at hc
    have hh : h⁻¹ * h⁻¹ ∈ Wsub S U ⊓ zpowers h :=
      Subgroup.mem_inf.2 ⟨hc, mul_mem (inv_mem (Subgroup.mem_zpowers h))
        (inv_mem (Subgroup.mem_zpowers h))⟩
    rw [hs.W_inf_h hII, Subgroup.mem_bot] at hh
    apply hs.h_sq_ne
    calc h * h = (h⁻¹ * h⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      _ = 1 := by rw [hh]; exact inv_one

theorem Nh_not_W_inv (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {d : G}
    (hd : d ∈ Nh S h) (hdW : d ∉ Wsub S U) : d * h * d⁻¹ = h⁻¹ := by
  rcases hs.Nh_conj_h hII hd with h1 | h1
  · exfalso
    have hdu := hs.conj_u_of_not_mem_W hII hd.1 hdW
    have hz1 := hs.conj_z₁ hII hd.1 hdu
    have hdz : d * z * d⁻¹ = z := by rw [← hs.z_comm hII hd.1]; group
    have hdh : d * h⁻¹ * d⁻¹ = h⁻¹ := by
      have : d * h⁻¹ * d⁻¹ = (d * h * d⁻¹)⁻¹ := by group
      rw [this, h1]
    have h2 : d * (h⁻¹ * z * h) * d⁻¹ = h⁻¹ * z * h := by
      calc d * (h⁻¹ * z * h) * d⁻¹ = (d * h⁻¹ * d⁻¹) * (d * z * d⁻¹) * (d * h * d⁻¹) := by group
        _ = h⁻¹ * z * h := by rw [hdh, hdz, h1]
    rw [h2] at hz1
    apply hs.z_ne
    exact (mul_eq_left.1 hz1.symm)
  · exact h1

theorem mem_Nh_of_comm {c : G} (hcS : c ∈ S) (hch : h * c = c * h) : c ∈ Nh S h := by
  refine mem_Nh.2 ⟨hcS, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hcx : ∀ x ∈ zpowers h, c * x * c⁻¹ = x := by
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hcom : Commute c h := hch.symm
    have h1 := (hcom.zpow_right i).eq
    calc c * h ^ i * c⁻¹ = (c * h ^ i) * c⁻¹ := rfl
      _ = (h ^ i * c) * c⁻¹ := by rw [h1]
      _ = h ^ i := by group
  constructor
  · intro hx
    rw [hcx x hx]
    exact hx
  · intro hx
    have hy := hcx _ hx
    have hxy : x = c * x * c⁻¹ := by
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = c⁻¹ * (c * (c * x * c⁻¹) * c⁻¹) * c := by rw [hy]
        _ = c * x * c⁻¹ := by group
    rw [hxy]
    exact hx

theorem exists_YData (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : 2 ^ 7 ≤ Nat.card ↥S) (h85 : Lemma8_5) :
    ∃ Y : Subgroup G, YData S K₁ W₂ U h Y := by
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  have hA16 : Nat.card ↥(Aof S K₁ W₂ h) = 16 := by
    rw [hs.card_A hII hq hrec hk]
    norm_num
  have hSW := hs.card_S_eq_two_W hII hq hk
  have hS8 : Nat.card ↥S ≤ 2 ^ 8 := by
    obtain ⟨-, hcases⟩ := hs.cases8_aux hII hq hrec hP8
    rcases hcases with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> rw [h1] <;> norm_num
  have hWA : Nat.card ↥(Wsub S U) ≤ 8 * Nat.card ↥(Aof S K₁ W₂ h) := by
    rw [hA16]
    omega
  have hAW : Aof S K₁ W₂ h ≤ Wsub S U := hs.A_le_W hII hq hrec (le_refl _) hk
  obtain ⟨w₀, hw₀W, hw₀⟩ := h85 G z S K₁ K₂ W₁ W₂ U u h hs hP8 hS7
  rw [commutatorElement_def] at hw₀
  obtain ⟨Y, hAY, hYW, hYcard, hYh, hYfix, hYdec, hYconj⟩ := Basic.exists_norm_kernel (Wsub S U)
    (Aof S K₁ W₂ h) h hAW (fun w hw a ha => hs.A_normS hII hq hrec hw.1 ha)
    (fun w hw w' hw' => hs.W_comm_mem_A hII hq hrec hk hw hw')
    (fun w hw => hs.W_sq_mem_A hII hq hrec hk hw)
    (fun w hw => hs.W_conj_h hw) (fun a ha => (hs.A_conj hII hq hrec hk ha).2) hs.h_cube
    ⟨w₀, hw₀W, hw₀⟩ hWA
  have hMN : Wsub S U ⊔ zpowers h ≤ S ⊔ zpowers h := sup_le_sup W_le_S le_rfl
  have hfr := Basic.exists_mul_mem_normalizer (p := 3) hMN (hs.M₁_norm hII hq hk)
    (le_sup_right : zpowers h ≤ Wsub S U ⊔ zpowers h) hs.h_three
    (by rw [hs.relIndex_h_M₁ hII]; exact hs.not_three_dvd_card_W hII)
  have hSWD : ∀ s ∈ S, ∃ w ∈ Wsub S U, ∃ d ∈ Nh S h, s = w * d := by
    intro s hsS
    obtain ⟨m, hm, x, hx, hsx⟩ := hfr s (Subgroup.mem_sup_left hsS)
    obtain ⟨b, hb, a, ha, hmba⟩ := Basic.mem_sup_of_le_normalizer' (A := zpowers h)
      (B := Wsub S U) hs.h_le_normalizer_W (sup_comm (Wsub S U) (zpowers h) ▸ hm)
    have hbN : b ∈ normalizer (zpowers h : Set G) :=
      (Subgroup.zpowers_le.2 h_mem_normalizer_zpowers) hb
    have hw'' : b * a * b⁻¹ ∈ Wsub S U :=
      (Subgroup.mem_normalizer_iff.1 (hs.h_le_normalizer_W hb) a).1 ha
    refine ⟨b * a * b⁻¹, hw'', b * x, mem_Nh.2 ⟨?_, mul_mem hbN hx⟩, ?_⟩
    · have e : b * x = (b * a * b⁻¹)⁻¹ * s := by rw [hsx, hmba]; group
      rw [e]
      exact mul_mem (inv_mem hw''.1) hsS
    · rw [hsx, hmba]
      group
  have hlift : ∀ w ∈ Wsub S U, ∃ y ∈ Y, ∃ c ∈ Wsub S U, h * c = c * h ∧ w = y * c := by
    intro w hw
    obtain ⟨y, hy, c, hc, hcA, rfl⟩ := hYdec w hw
    have heA : (h⁻¹ * c * h) * c⁻¹ ∈ Aof S K₁ W₂ h := hcA
    obtain ⟨a, ha, hθ⟩ := hs.theta_surj hII hq hrec hk _ (inv_mem heA)
    have hcomm : (h⁻¹ * c * h * c⁻¹) * a = a * (h⁻¹ * c * h * c⁻¹) :=
      hs.A_comm hII hq hrec _ heA a ha
    have hfix : h⁻¹ * (a * c) * h = a * c := by
      have e1 : h⁻¹ * a * h = ((h⁻¹ * c * h) * c⁻¹)⁻¹ * a := by
        calc h⁻¹ * a * h = ((h⁻¹ * a * h) * a⁻¹) * a := by group
          _ = ((h⁻¹ * c * h) * c⁻¹)⁻¹ * a := by rw [hθ]
      calc h⁻¹ * (a * c) * h = (h⁻¹ * a * h) * (h⁻¹ * c * h) := by group
        _ = (((h⁻¹ * c * h) * c⁻¹)⁻¹ * a) * (((h⁻¹ * c * h) * c⁻¹) * c) := by rw [e1]; group
        _ = ((h⁻¹ * c * h * c⁻¹)⁻¹ * (a * (h⁻¹ * c * h * c⁻¹))) * c := by group
        _ = ((h⁻¹ * c * h * c⁻¹)⁻¹ * ((h⁻¹ * c * h * c⁻¹) * a)) * c := by rw [hcomm]
        _ = a * c := by group
    refine ⟨y * a⁻¹, mul_mem hy (inv_mem (hAY ha)), a * c, mul_mem (hAW ha) hc, ?_, by group⟩
    have e : (a * c) * h = h * (h⁻¹ * (a * c) * h) := by group
    rw [hfix] at e
    exact e.symm
  have hDW : ∀ d ∈ Nh S h, ∀ w ∈ Wsub S U, d * w * d⁻¹ ∈ Wsub S U := fun d hd w hw =>
    hs.W_normS hd.1 hw
  refine ⟨Y, ⟨hAY, hYW, by rw [hYcard, hA16], hYh, ?_, ?_, ?_⟩⟩
  · intro y hy hc
    have hyA := hYfix y hy hc
    apply hs.A_fixed_trivial hII hq hrec hk hyA
    calc h⁻¹ * y * h = h⁻¹ * (y * h) := by group
      _ = h⁻¹ * (h * y) := by rw [hc]
      _ = y := by group
  · intro s hsS
    obtain ⟨w, hw, d, hd, rfl⟩ := hSWD s hsS
    obtain ⟨y, hy, c, hc, hch, rfl⟩ := hlift w hw
    exact ⟨y, hy, c * d, mul_mem (mem_Nh_of_comm hc.1 hch) hd, by group⟩
  · intro d hd y hy
    exact hYconj d (hs.Nh_conj_h hII hd) (hDW d hd)
      (fun a ha => hs.A_normS hII hq hrec hd.1 ha) y hy

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
