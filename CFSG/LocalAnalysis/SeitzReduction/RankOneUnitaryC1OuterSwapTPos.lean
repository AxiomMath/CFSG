module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterSwapTBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterSwapTwo

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapTwo G L f t T R₂ D d V U U₁ w s P)
include hW

theorem mem_map_of_commute {c : G} (hcT : ∀ τ ∈ T, c * τ * c⁻¹ ∈ swapS₂ P U T) {z : G}
    (hz : z ∈ swapS₂ P U T) (hzx : z * (c * t * c⁻¹) = (c * t * c⁻¹) * z) :
    z ∈ T.map (MulAut.conj c).toMonoidHom :=
  ⟨c⁻¹ * z * c, hW.conj_mem_T_of_commute hcT hz hzx, by simp; group⟩

theorem exists_of_mem_map {c z : G} (hz : z ∈ T.map (MulAut.conj c).toMonoidHom) :
    ∃ τ ∈ T, z = c * τ * c⁻¹ := by
  obtain ⟨τ, hτ, rfl⟩ := hz
  exact ⟨τ, hτ, by simp⟩

theorem commute_of_mem_map {c z : G} (hz : z ∈ T.map (MulAut.conj c).toMonoidHom) :
    z * (c * t * c⁻¹) = (c * t * c⁻¹) * z := by
  obtain ⟨τ, hτ, rfl⟩ := hW.exists_of_mem_map hz
  have hτt := mem_centralizer_singleton_iff.mp (hW.step.start.le hτ)
  calc c * τ * c⁻¹ * (c * t * c⁻¹) = c * (τ * t) * c⁻¹ := by group
    _ = c * (t * τ) * c⁻¹ := by rw [hτt]
    _ = c * t * c⁻¹ * (c * τ * c⁻¹) := by group

theorem card_map (c : G) : Nat.card (T.map (MulAut.conj c).toMonoidHom) = 4 * (2 ^ f) ^ 3 := by
  rw [card_map_of_injective (MulAut.conj c).injective, hW.card_T]

theorem map_le {c : G} (hcT : ∀ τ ∈ T, c * τ * c⁻¹ ∈ swapS₂ P U T) :
    T.map (MulAut.conj c).toMonoidHom ≤ swapS₂ P U T := fun z hz => by
  obtain ⟨τ, hτ, rfl⟩ := hW.exists_of_mem_map hz
  exact hcT τ hτ

theorem false_of_conj_mem_U₁ {c : G} (hcT : ∀ τ ∈ T, c * τ * c⁻¹ ∈ swapS₂ P U T)
    (hx : c * t * c⁻¹ ∈ U₁) : False := by
  have hS := hW.step
  have hL := hW.level
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  obtain ⟨-, hA₁card, -, -, -, -, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  have hcommA := hL.muOne_comm_mem_szA₁ hS hc hW.mu hK hμ
  set x := c * t * c⁻¹ with hxdef
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hS.start.two_le
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hbound := card_le_card_centralizer_mul_card_of_comm_mem (H := U₁)
    (A := szA₁ (szT₁ L T)) (x := x) fun z hz => hcommA z hz x hx
  rw [hL.muOne_card_U₁ hS, hA₁card] at hbound
  have hCcard : (2 ^ f) ^ 4 ≤ Nat.card ((centralizer ({x} : Set G)).subgroupOf U₁) := by
    have h2 : (2 ^ f) ^ 4 * 2 ^ f ≤ Nat.card ((centralizer ({x} : Set G)).subgroupOf U₁) *
        2 ^ f := by rw [← pow_succ]; exact hbound
    exact Nat.le_of_mul_le_mul_right h2 hq0
  set C : Subgroup G := centralizer ({x} : Set G) ⊓ U₁ with hCdef
  have hCcard' : (2 ^ f) ^ 4 ≤ Nat.card C := by
    rw [hCdef, ← subgroupOf_map_subtype, card_map_of_injective U₁.subtype_injective]
    exact hCcard
  set H := T.map (MulAut.conj c).toMonoidHom with hHdef
  have hCH : C ≤ H := fun z hz => hW.mem_map_of_commute hcT
    (hW.le_S₂ (mem_sup_left (hL.U₁_le (mem_inf.mp hz).2)))
    (mem_centralizer_singleton_iff.mp (mem_inf.mp hz).1)
  have hHcard := hW.card_map c
  have hle : Nat.card H ≤ Nat.card C := by
    rw [hHcard]
    calc 4 * (2 ^ f) ^ 3 ≤ 2 ^ f * (2 ^ f) ^ 3 := Nat.mul_le_mul_right _ hq4
      _ = (2 ^ f) ^ 4 := by ring
      _ ≤ Nat.card C := hCcard'
  have hCeq : C = H := eq_of_le_of_card_ge hCH hle
  refine hL.muOne_false_of_conj_mem_U₁ hS hc hW.mu hK hμ (g := c) (fun τ hτ => ?_) hx
  have h1 : c * τ * c⁻¹ ∈ H := ⟨τ, hτ, by simp⟩
  rw [← hCeq] at h1
  exact mem_sup_left (hL.U₁_le (mem_inf.mp h1).2)

theorem card_le_of_comm_of_le_map {c : G} {B : Subgroup G}
    (hBH : B ≤ T.map (MulAut.conj c).toMonoidHom) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card B ≤ 2 * (2 ^ f) ^ 2 := by
  set B' : Subgroup G := B.map (MulAut.conj c⁻¹).toMonoidHom with hB'def
  have hB'card : Nat.card B' = Nat.card B := card_map_of_injective (MulAut.conj c⁻¹).injective
  have hB'T : B' ≤ T := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨τ, hτ, rfl⟩ := hW.exists_of_mem_map (hBH hb)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show c⁻¹ * (c * τ * c⁻¹) * c = τ by group]
    exact hτ
  have hB'ab : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc c⁻¹ * a * c * (c⁻¹ * b * c) = c⁻¹ * (a * b) * c := by group
      _ = c⁻¹ * (b * a) * c := by rw [hBab a ha b hb]
      _ = c⁻¹ * b * c * (c⁻¹ * a * c) := by group
  rw [← hB'card]
  exact hW.step.start.swapT_card_le_of_comm hW.step.card_sylow hW.idx hB'T hB'ab

theorem false_of_conj_mem_tw {c : G} (hcT : ∀ τ ∈ T, c * τ * c⁻¹ ∈ swapS₂ P U T)
    (hx : c * t * c⁻¹ * (t * w)⁻¹ ∈ U₁) : False := by
  have hS := hW.step
  have hL := hW.level
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  set x := c * t * c⁻¹ with hxdef
  have hw₁T : t * w ∈ T := mul_mem hW.t_mem hW.w_mem
  have hw₁2 : (t * w) ^ 2 = 1 := by
    rw [Commute.mul_pow hW.wt_comm.symm 2, hS.start.sq_eq_one, hW.w_sq, one_mul]
  have hw₁S : t * w ∉ szT₁ L T ⊔ zpowers t := fun hm => hW.w_not_mem (by
    rw [show w = t⁻¹ * (t * w) by group]
    exact mul_mem (inv_mem (mem_sup_right (mem_zpowers t))) hm)
  have hw₁V : ∀ r ∈ V, t * w * r * (t * w)⁻¹ = r⁻¹ := fun r hr => by
    rw [show t * w * r * (t * w)⁻¹ = t * (w * r * w⁻¹) * t⁻¹ by group, hW.w_cent r hr]
    exact hS.conf.inv r hr
  obtain ⟨W, hWT₁, -, -, hWab, -, -, hWiff⟩ :=
    hS.start.exists_W_of_card_sylow hS.card_sylow hw₁T hw₁2 hw₁S
  have hCW : ∀ z ∈ U₁, z * x = x * z → z ∈ W ⊔ V := fun z hz hzx =>
    hL.muOne_mem_sup_of_commute_inv hS hc hW.mu hK hμ hw₁T hw₁V hWiff hx hz hzx
  have hWN : W ≤ normalizer (V : Set G) := hWT₁.trans (hL.muOne_T₁_le_normalizer hS)
  have hMab : ∀ a ∈ W ⊔ V, ∀ b ∈ W ⊔ V, a * b = b * a := by
    intro a ha b hb
    obtain ⟨y, hy, r, hr, rfl⟩ := ncyc_exists_mul_of_mem_sup hWN ha
    obtain ⟨y', hy', r', hr', rfl⟩ := ncyc_exists_mul_of_mem_sup hWN hb
    have c1 := hL.muOne_T₁_comm hS (hWT₁ hy) hr'
    have c2 := hL.muOne_T₁_comm hS (hWT₁ hy') hr
    have c3 := hWab y hy y' hy'
    have c4 := hS.conf.comm r hr r' hr'
    calc y * r * (y' * r') = y * (r * y') * r' := by group
      _ = y * (y' * r) * r' := by rw [c2]
      _ = (y * y') * (r * r') := by group
      _ = (y' * y) * (r' * r) := by rw [c3, c4]
      _ = y' * (y * r') * r := by group
      _ = y' * (r' * y) * r := by rw [c1]
      _ = y' * r' * (y * r) := by group
  set H := T.map (MulAut.conj c).toMonoidHom with hHdef
  set N := U₁ ⊓ H with hNdef
  have hHS := hW.map_le hcT
  have h1 := relIndex_mul_card (H := U₁) (K := H)
  rw [hW.card_map c] at h1
  have h8 := Subgroup.relIndex_le_of_le_right hHS (by rw [hW.relIndex_U₁_S₂]; norm_num)
  rw [hW.relIndex_U₁_S₂] at h8
  have hN : (2 ^ f) ^ 3 ≤ 2 * Nat.card N := by
    have h2 : 4 * (2 ^ f) ^ 3 ≤ 8 * Nat.card N := by
      rw [← h1]
      exact Nat.mul_le_mul_right _ h8
    omega
  have hxH : x ∈ H := ⟨t, hW.t_mem, by simp [hxdef]⟩
  have hNx : ∀ n ∈ N, n * x = x * n := fun n hn => hW.commute_of_mem_map (mem_inf.mp hn).2
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
    hMab a (hCW a (mem_inf.mp ha).1 (hNx a ha)) b (hCW b (mem_inf.mp hb).1 (hNx b hb))
  have htt : t * t = 1 := by rw [← sq, hS.start.sq_eq_one]
  have hxx : x * x = 1 := by
    rw [hxdef, show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, htt, mul_one,
      mul_inv_cancel]
  have hxU₁ : x ∉ U₁ := fun h' => hW.not_mem_U₁_of_mem_T hw₁T hW.tw_not_mem_T₁ (by
    rw [show t * w = (x * (t * w)⁻¹)⁻¹ * x by group]
    exact mul_mem (inv_mem hx) h')
  have hxN : x ∉ N := fun h' => hxU₁ (mem_inf.mp h').1
  have hxNorm : x ∈ normalizer (N : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun n hn => by
      have hnx := hNx n hn
      rw [show x⁻¹ * n * x = n by
        calc x⁻¹ * n * x = x⁻¹ * (n * x) := by group
          _ = x⁻¹ * (x * n) := by rw [hnx]
          _ = n := by group]
      exact hn
  set B := zpowers x ⊔ N with hBdef
  have hB2 := RankOne.Endings.relIndex_sup_zpowers_eq_two hxN hxNorm hxx
  have hBcard := relIndex_mul_card (H := N) (K := N ⊔ zpowers x)
  rw [hB2, inf_of_le_left le_sup_left, sup_comm] at hBcard
  have hca : ∀ a ∈ zpowers x, ∀ n ∈ N, a * n = n * a := by
    intro a ha n hn
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (Commute.symm (hNx n hn)) k).eq
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₁, ha₁, n₁, hn₁, rfl⟩ := ncyc_exists_mul_of_mem_sup (zpowers_le.mpr hxNorm) ha
    obtain ⟨a₂, ha₂, n₂, hn₂, rfl⟩ := ncyc_exists_mul_of_mem_sup (zpowers_le.mpr hxNorm) hb
    have e1 := hca a₂ ha₂ n₁ hn₁
    have e2 := hca a₁ ha₁ n₂ hn₂
    have e3 := hNab n₁ hn₁ n₂ hn₂
    have e4 : a₁ * a₂ = a₂ * a₁ := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha₁
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha₂
      exact (Commute.zpow_zpow_self x i j).eq
    calc a₁ * n₁ * (a₂ * n₂) = a₁ * (n₁ * a₂) * n₂ := by group
      _ = a₁ * (a₂ * n₁) * n₂ := by rw [e1]
      _ = (a₁ * a₂) * (n₁ * n₂) := by group
      _ = (a₂ * a₁) * (n₂ * n₁) := by rw [e4, e3]
      _ = a₂ * (a₁ * n₂) * n₁ := by group
      _ = a₂ * (n₂ * a₁) * n₁ := by rw [e2]
      _ = a₂ * n₂ * (a₁ * n₁) := by group
  have hBH : B ≤ H := sup_le (zpowers_le.mpr hxH) inf_le_right
  have hle := hW.card_le_of_comm_of_le_map hBH hBab
  rw [← hBcard] at hle
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hS.start.two_le
  have hq3 : 4 * (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 3 := by
    calc 4 * (2 ^ f) ^ 2 ≤ 2 ^ f * (2 ^ f) ^ 2 := Nat.mul_le_mul_right _ hq4
      _ = (2 ^ f) ^ 3 := by ring
  have hq2 : 0 < (2 ^ f) ^ 2 := pow_pos (pow_pos (by norm_num) f) 2
  omega

end U3C1OuterSwapTwo

end CFSG.SeitzReduction.RankOne
