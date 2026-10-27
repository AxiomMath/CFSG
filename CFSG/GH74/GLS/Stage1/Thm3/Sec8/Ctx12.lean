module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx11
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx10
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx6

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem exists_vq (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hx : x ∈ S1 S K₁)
    (hxV : ∀ a ∈ conjugate (Vof S K₁ W₂) h, x * a = a * x) :
    ∃ v ∈ conjugate (Vof S K₁ W₂) h, ∃ q ∈ Qof S K₂, x = v * q := by
  have hcard := hs.card_S1_eq hII hq hrec
  have h8 : 8 * Nat.card ↥(Qof S K₂) ≤ Nat.card ↥(S1 S K₁) := by
    have h1 := hs.V₁h_card hII hq
    have h2 : 8 ≤ Nat.card ↥(Pof S K₁) := (hs.gq_P hII hq (Or.inl rfl)).eight_le_card
    rw [hcard, h1]
    exact Nat.mul_le_mul_right _ h2
  obtain ⟨hN, a, b, hab⟩ := hs.nab_quot (K := K₂) (Or.inr rfl) (hs.Q₂_le_S1 hII) h8
  exact Basic.mem_sup_of_centralizes (S₁ := S1 S K₁) (Q := Qof S K₂)
    (V := conjugate (Vof S K₁ W₂) h) (hs.Q₂_le_S1 hII) (hs.V₁h_le_S1 hII hq hrec)
    (hs.V₁h_inf_Q hII hq (Or.inr rfl)) hs.cyc_V_comm hcard ⟨a, b, hab⟩ hx hxV

theorem cent_S1_w (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {w : G} (hwS : w ∈ S) (hwn : w ∉ S1 S K₁)
    (hVw : conjugate (Vof S K₁ W₂) h ≤ zpowers w) {x : G} (hx : x ∈ S1 S K₁) (hxw : x * w = w * x) :
    ∃ v ∈ conjugate (Vof S K₁ W₂) h, ∃ c ∈ zpowers z, x = v * c := by
  have hxV : ∀ a ∈ conjugate (Vof S K₁ W₂) h, x * a = a * x := by
    intro a ha
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hVw ha)
    rw [← hm]
    exact ((Commute.zpow_right (show Commute x w from hxw) m)).eq
  obtain ⟨v, hvV, q, hqQ, hxvq⟩ := hs.exists_vq hII hq hrec hx hxV
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hVw hvV)
  have hwv : w * v = v * w := by
    rw [← hm]; exact ((Commute.refl w).zpow_right m).eq
  have hq₁ : w * q * w⁻¹ ∈ Qof S K₁ := hs.swap_Q₂ hII hwS hwn hqQ
  have hxw' : w * x * w⁻¹ = x := by rw [← hxw]; group
  have h1 : w * x * w⁻¹ = v * (w * q * w⁻¹) := by
    rw [hxvq]
    calc w * (v * q) * w⁻¹ = (w * v * w⁻¹) * (w * q * w⁻¹) := by group
      _ = v * (w * q * w⁻¹) := by rw [hwv]; group
  have h2 : q = w * q * w⁻¹ := by
    have : v * q = v * (w * q * w⁻¹) := by
      calc v * q = x := hxvq.symm
        _ = w * x * w⁻¹ := hxw'.symm
        _ = v * (w * q * w⁻¹) := h1
    exact mul_left_cancel this
  have hq₁' : q ∈ Qof S K₁ := by rw [h2]; exact hq₁
  refine ⟨v, hvV, q, ?_, hxvq⟩
  have : q ∈ Qof S K₁ ⊓ Qof S K₂ := ⟨hq₁', hqQ⟩
  rwa [hs.Q_inf_Q hII] at this

theorem card_V_sup_z (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    Nat.card ↥(conjugate (Vof S K₁ W₂) h ⊔ zpowers z) ≤ 2 * 2 ^ k := by
  have hcomm : ∀ a ∈ conjugate (Vof S K₁ W₂) h, ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hb
    have haS : a ∈ S := (hs.V₁h_le_S1 hII hq hrec ha).1
    have h1 : a * z = z * a := (hs.z_comm hII haS).symm
    rw [← hm]
    exact ((Commute.zpow_right (show Commute a z from h1) m)).eq
  have h1 := M.card_sup_mul_card_inf (A := conjugate (Vof S K₁ W₂) h) (B := zpowers z)
    (M.le_normalizer_of_commute hcomm)
  rw [conjugate_card, hk, M.card_zpowers_of_sq hs.z_sq hs.z_ne] at h1
  have hpos : 0 < Nat.card ↥(conjugate (Vof S K₁ W₂) h ⊓ zpowers z) := Nat.card_pos
  have h2 : Nat.card ↥(conjugate (Vof S K₁ W₂) h ⊔ zpowers z) ≤
      Nat.card ↥(conjugate (Vof S K₁ W₂) h ⊔ zpowers z) *
        Nat.card ↥(conjugate (Vof S K₁ W₂) h ⊓ zpowers z) := Nat.le_mul_of_pos_right _ hpos
  omega

theorem card_cent_w_le (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {w : G}
    (hwS : w ∈ S) (hwn : w ∉ S1 S K₁) (hVw : conjugate (Vof S K₁ W₂) h ≤ zpowers w) :
    Nat.card ↥(Wsub S U ⊓ centralizer ({w} : Set G)) ≤ 2 * (2 * 2 ^ k) := by
  have hCS : Wsub S U ⊓ centralizer ({w} : Set G) ≤ S := inf_le_left.trans inf_le_left
  have hsub : S1 S K₁ ⊓ (Wsub S U ⊓ centralizer ({w} : Set G)) ≤
      conjugate (Vof S K₁ W₂) h ⊔ zpowers z := by
    intro x hx
    have hxw : x * w = w * x :=
      ((Subgroup.mem_centralizer_iff.1 hx.2.2) w (Set.mem_singleton w)).symm
    obtain ⟨v, hv, c, hc, hxvc⟩ := hs.cent_S1_w hII hq hrec hwS hwn hVw hx.1 hxw
    rw [hxvc]
    exact Subgroup.mul_mem_sup hv hc
  have h1 : Nat.card ↥(S1 S K₁ ⊓ (Wsub S U ⊓ centralizer ({w} : Set G))) ≤ 2 * 2 ^ k :=
    (Subgroup.card_le_of_le hsub).trans (hs.card_V_sup_z hII hq hrec hk)
  have h2 := Basic.card_mul_relIndex_of_le (A := S1 S K₁ ⊓ (Wsub S U ⊓ centralizer ({w} : Set G)))
    (B := Wsub S U ⊓ centralizer ({w} : Set G)) inf_le_right
  have h3 : (S1 S K₁ ⊓ (Wsub S U ⊓ centralizer ({w} : Set G))).relIndex
      (Wsub S U ⊓ centralizer ({w} : Set G)) =
        (S1 S K₁).relIndex (Wsub S U ⊓ centralizer ({w} : Set G)) := Subgroup.inf_relIndex_right _ _
  have h4 : (S1 S K₁).relIndex (Wsub S U ⊓ centralizer ({w} : Set G)) ≤ (S1 S K₁).relIndex S :=
    Subgroup.relIndex_le_of_le_right hCS (Basic.relIndex_ne_zero' _ _)
  have h5 : (S1 S K₁).relIndex S ≤ 2 := hs.fused.p66.2.1.1
  rw [h3] at h2
  calc Nat.card ↥(Wsub S U ⊓ centralizer ({w} : Set G))
      = Nat.card ↥(S1 S K₁ ⊓ (Wsub S U ⊓ centralizer ({w} : Set G))) *
          (S1 S K₁).relIndex (Wsub S U ⊓ centralizer ({w} : Set G)) := h2.symm
    _ ≤ (2 * 2 ^ k) * 2 := Nat.mul_le_mul h1 (h4.trans h5)
    _ = 2 * (2 * 2 ^ k) := by ring

theorem W₂V₂_le_C (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    W₂ ⊔ Vof S K₂ W₁ ≤ Wsub S U ⊓ centralizer (W₂ : Set G) := by
  have hcomm : ∀ a ∈ W₂, ∀ b ∈ Vof S K₂ W₁, a * b = b * a :=
    fun a ha b hb => hs.Q_comm_P hII (Or.inr rfl) a (hs.W₂_le_Q₂ ha) b hb.2
  apply sup_le
  · intro a ha
    exact Subgroup.mem_inf.2 ⟨hs.W₂_le_W hII hq ha,
      Subgroup.mem_centralizer_iff.2 (fun y hy => Basic.cyclic_comm hs.W₂_max.2.1 y hy a ha)⟩
  · intro b hb
    exact Subgroup.mem_inf.2 ⟨hs.V₂_le_W hII hq hb,
      Subgroup.mem_centralizer_iff.2 (fun y hy => hcomm y hy b hb)⟩

theorem card_W₂V₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Nat.card ↥W₂ * Nat.card ↥(Vof S K₂ W₁) ≤ 2 * Nat.card ↥(W₂ ⊔ Vof S K₂ W₁) := by
  have hcomm : ∀ a ∈ W₂, ∀ b ∈ Vof S K₂ W₁, a * b = b * a :=
    fun a ha b hb => hs.Q_comm_P hII (Or.inr rfl) a (hs.W₂_le_Q₂ ha) b hb.2
  have h1 := M.card_sup_mul_card_inf (A := W₂) (B := Vof S K₂ W₁) (M.le_normalizer_of_commute hcomm)
  have hle2 : W₂ ⊓ Vof S K₂ W₁ ≤ zpowers z := by
    intro x hx
    have : x ∈ Qof S K₁ ⊓ Qof S K₂ := ⟨hs.P₂_le_Q₁ hII hx.2.2, hs.W₂_le_Q₂ hx.1⟩
    rwa [hs.Q_inf_Q hII] at this
  have h2 : Nat.card ↥(W₂ ⊓ Vof S K₂ W₁) ≤ 2 := by
    have := Subgroup.card_le_of_le hle2
    rwa [M.card_zpowers_of_sq hs.z_sq hs.z_ne] at this
  calc Nat.card ↥W₂ * Nat.card ↥(Vof S K₂ W₁)
      = Nat.card ↥(W₂ ⊔ Vof S K₂ W₁) * Nat.card ↥(W₂ ⊓ Vof S K₂ W₁) := h1.symm
    _ ≤ Nat.card ↥(W₂ ⊔ Vof S K₂ W₁) * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Nat.card ↥(W₂ ⊔ Vof S K₂ W₁) := by ring

theorem card_cent_W₂_le (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {w : G} (hw : w ∈ conjugate W₂ h) :
    Nat.card ↥(Wsub S U ⊓ centralizer (W₂ : Set G)) ≤
      Nat.card ↥(Wsub S U ⊓ centralizer ({w} : Set G)) := by
  have hle : conjugate (Wsub S U ⊓ centralizer (W₂ : Set G)) h ≤
      Wsub S U ⊓ centralizer ({w} : Set G) := by
    intro x hx
    have hx' : h * x * h⁻¹ ∈ Wsub S U ⊓ centralizer (W₂ : Set G) := mem_conjugate_iff.1 hx
    have hxW : x ∈ Wsub S U := ((Subgroup.mem_normalizer_iff.1 hs.h_W) x).2 hx'.1
    refine Subgroup.mem_inf.2 ⟨hxW, Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)⟩
    have hy' : y = w := Set.mem_singleton_iff.1 hy
    rw [hy']
    have hwW₂ : h * w * h⁻¹ ∈ W₂ := mem_conjugate_iff.1 hw
    have key := (Subgroup.mem_centralizer_iff.1 hx'.2) (h * w * h⁻¹) hwW₂
    have e1 : h * w * h⁻¹ * (h * x * h⁻¹) = h * (w * x) * h⁻¹ := by group
    have e2 : h * x * h⁻¹ * (h * w * h⁻¹) = h * (x * w) * h⁻¹ := by group
    rw [e1, e2] at key
    exact mul_left_cancel (mul_right_cancel key)
  have := Subgroup.card_le_of_le hle
  rwa [conjugate_card] at this

theorem k_eq_two_of_e2 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hq2 : Nat.card ↥(Qof S K₂) = 2 * Nat.card ↥(Pof S K₁))
    {k : ℕ} (hk2 : 2 ≤ k) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    k = 2 ∧ W₂ ⊔ Vof S K₂ W₁ = Wsub S U ⊓ centralizer (W₂ : Set G) ∧
      Nat.card ↥(Wsub S U ⊓ centralizer (W₂ : Set G)) ≤ 16 := by
  have hWc : IsCyclic ↥(conjugate W₂ h) := by
    rw [conjugate_eq_comap]
    exact Basic.cyclic_comap_conj _ hs.W₂_max.2.1 h
  obtain ⟨w, hwW, hgen⟩ := Basic.exists_generator_of_cyclic hWc
  have hwn : w ∉ S1 S K₁ := by
    intro hw
    refine hs.false_of_W₂h_le_S1 hII hq hrec hq2 ?_
    rw [hgen, Subgroup.zpowers_le]
    exact hw
  have hwS : w ∈ S := (hs.W₂h_le_W hII hq hwW).1
  have hVw : conjugate (Vof S K₁ W₂) h ≤ zpowers w := by
    intro x hx
    have hx' : h * x * h⁻¹ ∈ Vof S K₁ W₂ := mem_conjugate_iff.1 hx
    have : x ∈ conjugate W₂ h := mem_conjugate_iff.2 hx'.1
    rwa [hgen] at this
  have hα := hs.card_W₂V₂ hII
  have hβ := hs.card_cent_W₂_le hII hq hwW
  have hγ := hs.card_cent_w_le hII hq hrec hk hwS hwn hVw
  have hle := hs.W₂V₂_le_C hII hq
  have hδ := Subgroup.card_le_of_le hle
  have hV₂ := hs.V₂_card_eq hII hq hrec hk
  have hW₂c : Nat.card ↥W₂ = 2 * 2 ^ k := by
    have h1 := hs.card_W₂ hII
    have h2 := hs.card_V₁ hII hq
    omega
  rw [hV₂, hW₂c] at hα
  have hpos : 0 < 2 ^ k := by positivity
  have h2k : 2 ^ k ≤ 4 := by
    have h1 : (2 * 2 ^ k) * 2 ^ k ≤ 8 * 2 ^ k := by omega
    have h2 : 2 * 2 ^ k * 2 ^ k = (2 ^ k) * (2 * 2 ^ k) := by ring
    have h3 : 8 * 2 ^ k = 4 * (2 * 2 ^ k) := by ring
    rw [h3, h2] at h1
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  have hk2' : k = 2 := by
    by_contra hne
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hk2'
  refine ⟨rfl, ?_, by omega⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  omega

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
