module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinFrame
public import CFSG.GH74.L5U5.ModelsBridge

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution QuaternionGroup
open scoped MatrixGroups

variable {Y : Type} [Group Y] {L : Subgroup Y} {F' : Type} [Field F'] {x t : Y}
  {J₂ J₄ : Subgroup Y}

theorem eq_one_or_of_central [Finite F'] (hodd : Odd (Nat.card F')) {J : Subgroup Y}
    (e : J ≃* SL(2, F')) {u : Y} (hu : u ∈ J) (hu2 : orderOf u = 2) {z : Y} (hz : z ∈ J)
    (hc : ∀ a ∈ J, a * z = z * a) : z = 1 ∨ z = u := by
  have hZ : (⟨z, hz⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  rw [mem_center_iff_of_equiv_sl2 e, mem_center_sl2_iff] at hZ
  have hu' : (⟨u, hu⟩ : J) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp (by rw [Subgroup.orderOf_mk, hu2])
  rcases hZ with h | h
  · left
    have : (⟨z, hz⟩ : J) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨z, hz⟩ : J) = ⟨u, hu⟩ := by rw [hu', ← h, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val this

theorem Frame.inter_eq_one [Finite F'] (hfr : Frame L F' x t J₂ J₄) (hodd : Odd (Nat.card F'))
    (ht : orderOf t = 2) {z : Y} (hz₂ : z ∈ J₂) (hz₄ : z ∈ J₄) : z = 1 := by
  obtain ⟨e₂⟩ := hfr.equiv₂
  obtain ⟨e₄⟩ := hfr.equiv₄
  rcases eq_one_or_of_central hodd e₂ hfr.mem₂ ht hz₂ (fun a ha => hfr.comm a ha z hz₄) with
    h | h
  · exact h
  rcases eq_one_or_of_central hodd e₄ hfr.mem₄ hfr.orderOf_xt hz₄
    (fun b hb => (hfr.comm z hz₂ b hb).symm) with h' | h'
  · exact h'
  · exfalso
    apply hfr.ne_one
    have : x * t = 1 * t := by rw [← h', h, one_mul]
    exact mul_right_cancel this

theorem Frame.exists_q8q8 [Finite F'] (hfr : Frame L F' x t J₂ J₄) (hodd : Odd (Nat.card F'))
    (ht : orderOf t = 2) :
    ∃ Φ : QuaternionGroup 2 × QuaternionGroup 2 →* Y, Function.Injective Φ ∧
      ∀ a b, Φ (a, b) = Φ (a, 1) * Φ (1, b) ∧ Φ (a, 1) ∈ J₂ ∧ Φ (1, b) ∈ J₄ := by
  obtain ⟨e₂⟩ := hfr.equiv₂
  obtain ⟨e₄⟩ := hfr.equiv₄
  obtain ⟨φ₂, hi₂, hr₂, -⟩ := exists_q8_of_mulEquiv_sl2 hodd J₂ e₂
  obtain ⟨φ₄, hi₄, hr₄, -⟩ := exists_q8_of_mulEquiv_sl2 hodd J₄ e₄
  have hc : ∀ a b, Commute (φ₂ a) (φ₄ b) := fun a b => hfr.comm _ (hr₂ a) _ (hr₄ b)
  let Φ := φ₂.noncommCoprod φ₄ hc
  have hΦ : ∀ a b, Φ (a, b) = φ₂ a * φ₄ b := fun _ _ => rfl
  refine ⟨Φ, ?_, fun a b => ⟨by rw [hΦ, hΦ, hΦ, map_one, map_one, mul_one, one_mul], ?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    rw [hΦ] at h
    have h4 : φ₂ a = φ₄ b⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
    have h1 : φ₂ a = 1 := hfr.inter_eq_one hodd ht (hr₂ a) (h4 ▸ hr₄ _)
    have ha : a = 1 := hi₂ (h1.trans (map_one φ₂).symm)
    subst ha
    rw [map_one, one_mul] at h
    have hb : b = 1 := hi₄ (h.trans (map_one φ₄).symm)
    rw [hb]
    rfl
  · rw [hΦ, map_one, mul_one]
    exact hr₂ a
  · rw [hΦ, map_one, one_mul]
    exact hr₄ b

theorem q8q8_central_sq : ∀ g : QuaternionGroup 2 × QuaternionGroup 2,
    (∀ a, g * a = a * g) → g * g = 1 := by
  decide

theorem Frame.false_of_q8 [Finite Y] [Finite F'] (hfr : Frame L F' x t J₂ J₄)
    (hodd : Odd (Nat.card F')) (ht : orderOf t = 2) {φ : QuaternionGroup 2 →* Y}
    (hφL : ∀ q, φ q ∈ L) (hφt : φ (a 1) ^ 2 = t) (h₂ : ∀ q, ∀ j ∈ J₂, φ q * j = j * φ q)
    (h₄ : ∀ q, ∀ j ∈ J₄, φ q * j = j * φ q) (hgen : GH74.Gen4 ↥L) : False := by
  obtain ⟨Φ, hΦi, hΦ⟩ := hfr.exists_q8q8 hodd ht
  have hΦL : ∀ g, Φ g ∈ L := fun g => by
    rw [(hΦ g.1 g.2).1]
    exact L.mul_mem (hfr.le₂ (hΦ g.1 g.2).2.1) (hfr.le₄ (hΦ g.1 g.2).2.2)
  let Φ' := Φ.codRestrict L hΦL
  let φ' := φ.codRestrict L hφL
  have hΦ'i : Function.Injective Φ' := fun a b h => hΦi (congrArg Subtype.val h)
  have hQ : IsPGroup 2 (QuaternionGroup 2) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hT : IsPGroup 2 φ'.range := by
    rw [MonoidHom.range_eq_map]
    exact (hQ.to_subgroup ⊤).map φ'
  have hcomm : ∀ (g : QuaternionGroup 2 × QuaternionGroup 2) (s : ↥L), s ∈ φ'.range →
      Φ' g * s = s * Φ' g := by
    rintro ⟨g, g'⟩ s ⟨q, rfl⟩
    apply Subtype.ext
    show Φ (g, g') * φ q = φ q * Φ (g, g')
    rw [(hΦ g g').1, mul_assoc, ← h₄ q _ (hΦ g g').2.2, ← mul_assoc, ← h₂ q _ (hΦ g g').2.1,
      mul_assoc]
  obtain ⟨g, hg, hgc⟩ := GH74.L5U5.q8q8_commuting_two_subgroup_le_center hgen Φ' hΦ'i
    φ'.range hT hcomm (φ' (a 1)) ⟨a 1, rfl⟩
  have h1 : φ' (a 1) * φ' (a 1) = 1 := by rw [← hg, ← map_mul, q8q8_central_sq g hgc, map_one]
  have h2 : t = 1 := by
    rw [← hφt, sq]
    exact congrArg Subtype.val h1
  rw [h2, orderOf_one] at ht
  exact absurd ht (by norm_num)

variable {R : Subgroup Y} {S : Sylow 2 R}

theorem Frame.false_of_outer [Finite Y] [Finite F'] (hfr : Frame L F' x t J₂ J₄) [L.Normal]
    (hodd : Odd (Nat.card F')) (hD : TightDatum R S t) (hR₂ : ∀ r ∈ R, ∀ j ∈ J₂, r * j = j * r)
    (hR₄ : ∀ r ∈ R, ∀ j ∈ J₄, r * j = j * r) (hgen : GH74.Gen4 ↥L)
    (hCL : ∀ y : Y, (∀ l ∈ L, y * l = l * y) → y ∈ L)
    (hRC : ∀ r ∈ R, (∀ l ∈ L, r * l = l * r) → r = 1)
    (hA : FrameOuterQ8Free ↥L (J₂.subgroupOf L) (J₄.subgroupOf L)) : False := by
  obtain ⟨φ, hφi, hφR, hφt⟩ := datum_exists_q8 hD
  by_cases hφL : ∀ q, φ q ∈ L
  · exact hfr.false_of_q8 hodd hD.order hφL hφt (fun q => hR₂ _ (hφR q))
      (fun q => hR₄ _ (hφR q)) hgen
  push Not at hφL
  obtain ⟨q₀, hq₀⟩ := hφL
  let ψ : QuaternionGroup 2 →* MulAut ↥L := MulAut.conjNormal.comp φ
  have hψ : ∀ q (l : ↥L), ((ψ q l : ↥L) : Y) = φ q * l * (φ q)⁻¹ := fun _ _ => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have h1 : φ q = 1 := hRC _ (hφR q) fun l hl => by
      have := congrArg Subtype.val (DFunLike.congr_fun hq ⟨l, hl⟩)
      rw [hψ] at this
      calc φ q * l = φ q * l * (φ q)⁻¹ * φ q := by group
        _ = l * φ q := by rw [this]; rfl
    exact hφi (h1.trans (map_one φ).symm)
  have hfix : ∀ {J : Subgroup Y}, (∀ r ∈ R, ∀ j ∈ J, r * j = j * r) →
      ∀ q, ∀ j ∈ J.subgroupOf L, ψ q j = j := fun hRJ q j hj => Subtype.ext (by
    rw [hψ, hRJ _ (hφR q) _ (Subgroup.mem_subgroupOf.mp hj), mul_assoc, mul_inv_cancel, mul_one])
  obtain ⟨k, hk⟩ := hA ψ hinj (hfix hR₂) (hfix hR₄) q₀
  have hc : ∀ l ∈ L, ((k : Y)⁻¹ * φ q₀) * l = l * ((k : Y)⁻¹ * φ q₀) := fun l hl => by
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hk ⟨l, hl⟩)
    rw [hψ] at h1
    have h2 : φ q₀ * l * (φ q₀)⁻¹ = k * l * (k : Y)⁻¹ := h1
    calc (k : Y)⁻¹ * φ q₀ * l = (k : Y)⁻¹ * (φ q₀ * l * (φ q₀)⁻¹) * φ q₀ := by group
      _ = (k : Y)⁻¹ * (k * l * (k : Y)⁻¹) * φ q₀ := by rw [h2]
      _ = l * ((k : Y)⁻¹ * φ q₀) := by group
  apply hq₀
  rw [show φ q₀ = k * ((k : Y)⁻¹ * φ q₀) by group]
  exact L.mul_mem k.2 (hCL _ hc)

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
