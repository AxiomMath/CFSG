module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step110Dih

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Lag

variable {K : Type} [Group K] [Finite K] {z : K}

omit [Finite K] in
theorem commute_of_mem_zpowers_of_mem_center (hz : z ∈ center K) {e : K} (he : e ∈ zpowers z)
    (k : K) : k * e = e * k := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
  exact ((Commute.zpow_right (show Commute k z from mem_center_iff.mp hz k) n)).eq

omit [Finite K] in
theorem mul_self_eq_one_of_mem_zpowers (hzo : orderOf z = 2) {e : K} (he : e ∈ zpowers z) :
    e * e = 1 := by
  rcases (ExtraIn.mem_zpowers_iff_of_order hzo).mp he with rfl | rfl
  · exact mul_one 1
  · rw [← sq, ← hzo, pow_orderOf_eq_one]

omit [Finite K] in
theorem conj_comm_eq_inv (hz : z ∈ center K) {x₀ d : K} (hx : x₀ * x₀ ∈ zpowers z) :
    x₀⁻¹ * (x₀ * d * x₀⁻¹ * d⁻¹) * x₀ = (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ := by
  have hxi : x₀⁻¹ * x₀⁻¹ ∈ zpowers z := by
    have := inv_mem hx
    rwa [mul_inv_rev] at this
  have h1 : d * x₀⁻¹ * d⁻¹ = x₀⁻¹ * (x₀ * d * x₀⁻¹ * d⁻¹) := by group
  have h2 : (d * x₀⁻¹ * d⁻¹) * (d * x₀⁻¹ * d⁻¹) = x₀⁻¹ * x₀⁻¹ := by
    calc (d * x₀⁻¹ * d⁻¹) * (d * x₀⁻¹ * d⁻¹) = d * (x₀⁻¹ * x₀⁻¹) * d⁻¹ := by group
      _ = x₀⁻¹ * x₀⁻¹ := by
        rw [commute_of_mem_zpowers_of_mem_center hz hxi d, mul_inv_cancel_right]
  rw [h1] at h2
  calc x₀⁻¹ * (x₀ * d * x₀⁻¹ * d⁻¹) * x₀
      = (x₀⁻¹ * (x₀ * d * x₀⁻¹ * d⁻¹) * (x₀⁻¹ * (x₀ * d * x₀⁻¹ * d⁻¹))) *
          (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ * (x₀ * x₀) := by group
    _ = (x₀⁻¹ * x₀⁻¹) * (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ * (x₀ * x₀) := by rw [h2]
    _ = (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ * (x₀⁻¹ * x₀⁻¹) * (x₀ * x₀) := by
        rw [← commute_of_mem_zpowers_of_mem_center hz hxi]
    _ = (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ := by group

theorem conj_eq_cube_of_lagrangian {Y B₁ D₀ : Subgroup K} (hz : z ∈ center K)
    (hzo : orderOf z = 2) (hY2 : ∀ y ∈ Y, y * y ∈ zpowers z) (hBY : B₁ ≤ Y) (hzB : z ∈ B₁)
    (hD1 : ∀ d ∈ D₀, ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ B₁)
    (hD2 : ∀ d ∈ D₀, ∀ b ∈ B₁, b * d * b⁻¹ * d⁻¹ ∈ zpowers z)
    (hD3 : ∀ d ∈ D₀, d ∉ zpowers z → ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ zpowers z → y ∈ B₁)
    (hD4 : Nat.card B₁ ≤ Nat.card D₀) {x₀ : K} (hx₀ : x₀ ∈ Y) (hx₀B : x₀ ∉ B₁) {b : K}
    (hb : b ∈ B₁) : x₀⁻¹ * b * x₀ = b * b * b := by
  have := zpowers_normal_of_mem_center hz
  have hcent := fun {e : K} (he : e ∈ zpowers z) (k : K) =>
    commute_of_mem_zpowers_of_mem_center hz he k
  have hcardz : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hzo]
  have hdb : ∀ d ∈ D₀, ∀ c ∈ B₁, barMap z (d * c * d⁻¹) = barMap z c := by
    intro d hd c hcB
    have h1 : (d * c * d⁻¹)⁻¹ * c = c⁻¹ * (c * d * c⁻¹ * d⁻¹) * c := by group
    have h2 : (d * c * d⁻¹)⁻¹ * c ∈ zpowers z := by
      rw [h1, mul_assoc, ← hcent (hD2 d hd c hcB) c, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hD2 d hd c hcB
    exact QuotientGroup.eq.mpr h2
  let φ : ↥D₀ →* K ⧸ zpowers z :=
    { toFun := fun d => barMap z (x₀ * d * x₀⁻¹ * (d : K)⁻¹)
      map_one' := by simp
      map_mul' := fun d e => by
        have h1 : x₀ * ((d : K) * e) * x₀⁻¹ * ((d : K) * e)⁻¹ =
            (x₀ * d * x₀⁻¹ * (d : K)⁻¹) *
              ((d : K) * (x₀ * e * x₀⁻¹ * (e : K)⁻¹) * (d : K)⁻¹) := by group
        simp only [Subgroup.coe_mul]
        rw [h1, map_mul, hdb d d.2 _ (hD1 e e.2 x₀ hx₀)] }
  have hrange : φ.range ≤ B₁.map (barMap z) := by
    rintro _ ⟨d, rfl⟩
    exact ⟨_, hD1 d d.2 x₀ hx₀, rfl⟩
  have hker : φ.ker.map D₀.subtype ≤ zpowers z := by
    rintro _ ⟨d, hd, rfl⟩
    by_contra hdz
    have h1 : x₀ * d * x₀⁻¹ * (d : K)⁻¹ ∈ (barMap z).ker := MonoidHom.mem_ker.mpr hd
    rw [ker_barMap] at h1
    exact hx₀B (hD3 d d.2 hdz x₀ hx₀ h1)
  have hD : Nat.card D₀ ≤ 2 * Nat.card φ.range := by
    have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
    have h2 := card_le_of_le hker
    rw [card_map_of_injective D₀.subtype_injective, hcardz] at h2
    rw [h1, mul_comm 2]
    exact Nat.mul_le_mul_left _ h2
  have hB : Nat.card B₁ = 2 * Nat.card (B₁.map (barMap z)) := by
    rw [← hcardz, ← card_comap_barMap, comap_map_barMap hzB]
  have heq : φ.range = B₁.map (barMap z) := eq_of_le_of_card_ge hrange (by omega)
  obtain ⟨d, hd⟩ : barMap z b ∈ φ.range := heq ▸ ⟨b, hb, rfl⟩
  change barMap z (x₀ * d * x₀⁻¹ * (d : K)⁻¹) = barMap z b at hd
  have he : (x₀ * d * x₀⁻¹ * (d : K)⁻¹)⁻¹ * b ∈ zpowers z := QuotientGroup.eq.mp hd
  have hcc := hY2 _ (hBY (hD1 d d.2 x₀ hx₀))
  have hconj := conj_comm_eq_inv hz (d := (d : K)) (hY2 x₀ hx₀)
  have hb' : b = (x₀ * d * x₀⁻¹ * (d : K)⁻¹) * ((x₀ * d * x₀⁻¹ * (d : K)⁻¹)⁻¹ * b) := by group
  rw [hb']
  generalize x₀ * d * x₀⁻¹ * (d : K)⁻¹ = c at he hcc hconj
  generalize c⁻¹ * b = e at he
  have hcinv : c⁻¹ = c * c * c := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc c * (c * c * c) = (c * c) * (c * c) := by group
      _ = 1 := mul_self_eq_one_of_mem_zpowers hzo hcc
  have hee := mul_self_eq_one_of_mem_zpowers hzo he
  have hex : x₀⁻¹ * e * x₀ = e := by
    rw [mul_assoc, ← hcent he x₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have hce : Commute c e := hcent he c
  calc x₀⁻¹ * (c * e) * x₀ = (x₀⁻¹ * c * x₀) * (x₀⁻¹ * e * x₀) := by group
    _ = c ^ 3 * e ^ 3 := by
        rw [hconj, hex, hcinv, pow_three', pow_three', hee, one_mul]
    _ = (c * e) * (c * e) * (c * e) := by
        rw [← hce.mul_pow, pow_three']

theorem false_of_lagrangian {Y B₁ D₀ : Subgroup K} (hz : z ∈ center K) (hzo : orderOf z = 2)
    (hY2 : ∀ y ∈ Y, y * y ∈ zpowers z) (hBY : B₁ ≤ Y) (hzB : z ∈ B₁) (hBne : ¬ Y ≤ B₁)
    (hC : Nat.card (Y ⊓ centralizer (B₁ : Set K) : Subgroup K) * Nat.card B₁ ≤ 2 * Nat.card Y)
    (h8 : 8 ≤ Nat.card B₁)
    (hD1 : ∀ d ∈ D₀, ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ B₁)
    (hD2 : ∀ d ∈ D₀, ∀ b ∈ B₁, b * d * b⁻¹ * d⁻¹ ∈ zpowers z)
    (hD3 : ∀ d ∈ D₀, d ∉ zpowers z → ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ zpowers z → y ∈ B₁)
    (hD4 : Nat.card B₁ ≤ Nat.card D₀) : False := by
  have hstar := fun {x₀ : K} (hx₀ : x₀ ∈ Y) (hx₀B : x₀ ∉ B₁) {b : K} (hb : b ∈ B₁) =>
    conj_eq_cube_of_lagrangian hz hzo hY2 hBY hzB hD1 hD2 hD3 hD4 hx₀ hx₀B hb
  obtain ⟨x₀, hx₀, hx₀B⟩ := IsConcreteLE.not_le_iff_exists.mp hBne
  have hsub : (Y : Set K) ⊆ (B₁ : Set K) ∪
      (fun c => c * x₀) '' ((Y ⊓ centralizer (B₁ : Set K) : Subgroup K) : Set K) := by
    intro x hx
    by_cases hxB : x ∈ B₁
    · exact Or.inl hxB
    · refine Or.inr ⟨x * x₀⁻¹, ⟨Y.mul_mem hx (Y.inv_mem hx₀),
        mem_centralizer_iff.mpr fun b hb => ?_⟩, by simp⟩
      have h1 := hstar hx₀ hx₀B hb
      have h2 := hstar hx hxB hb
      calc b * (x * x₀⁻¹) = x * (x⁻¹ * b * x) * x₀⁻¹ := by group
        _ = x * (x₀⁻¹ * b * x₀) * x₀⁻¹ := by rw [h2, h1]
        _ = x * x₀⁻¹ * b := by group
  have hcardY : Nat.card Y ≤
      Nat.card B₁ + Nat.card (Y ⊓ centralizer (B₁ : Set K) : Subgroup K) := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (B₁ : Set K)
      ((fun c => c * x₀) '' ((Y ⊓ centralizer (B₁ : Set K) : Subgroup K) : Set K))
    have h3 := Set.ncard_image_le (f := fun c => c * x₀)
      (s := ((Y ⊓ centralizer (B₁ : Set K) : Subgroup K) : Set K)) (Set.toFinite _)
    have e1 : Nat.card Y = (Y : Set K).ncard := Nat.card_coe_set_eq (Y : Set K)
    have e2 : Nat.card B₁ = (B₁ : Set K).ncard := Nat.card_coe_set_eq (B₁ : Set K)
    have e3 : Nat.card (Y ⊓ centralizer (B₁ : Set K) : Subgroup K) =
        ((Y ⊓ centralizer (B₁ : Set K) : Subgroup K) : Set K).ncard :=
      Nat.card_coe_set_eq _
    omega
  have hdvd : 2 * Nat.card B₁ ≤ Nat.card Y := by
    obtain ⟨k, hk⟩ := card_dvd_of_le hBY
    have hne : Nat.card B₁ ≠ Nat.card Y := fun h =>
      hBne (eq_of_le_of_card_ge hBY h.ge).ge
    have hpos : 0 < Nat.card B₁ := Nat.card_pos
    rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with h | h | h
    · rw [h, mul_zero] at hk
      exact absurd hk (Nat.card_pos).ne'
    · rw [h, mul_one] at hk
      exact absurd hk.symm hne
    · rw [hk]
      nlinarith
  have hcpos : 0 < Nat.card (Y ⊓ centralizer (B₁ : Set K) : Subgroup K) := Nat.card_pos
  have e1 : Nat.card Y ≤ 2 * Nat.card (Y ⊓ centralizer (B₁ : Set K) : Subgroup K) := by omega
  have e2 : Nat.card (Y ⊓ centralizer (B₁ : Set K) : Subgroup K) * Nat.card B₁ ≤
      Nat.card (Y ⊓ centralizer (B₁ : Set K) : Subgroup K) * 4 := by linarith
  have e3 := Nat.le_of_mul_le_mul_left e2 hcpos
  omega

end Lag

section Natural

variable {K : Type} [Group K] [Finite K] {z : K} {X : Subgroup K} {g : K}

namespace Conf110

variable (hc : Conf110 z X g)
include hc

theorem card_eq_four_mul_of_Q8 (h8 : Nat.card (tim77I X g) = 8) {H : Subgroup K}
    (hIH : tim77I X g ≤ H) (hH : ∀ h ∈ H, ∀ j ∈ tim77I X g, j * h * j⁻¹ * h⁻¹ ∈ zpowers z) :
    Nat.card H = 4 * Nat.card (H ⊓ centralizer (tim77I X g : Set K) : Subgroup K) := by
  obtain ⟨a, ha, b, hb, hab⟩ := hc.exists_gens h8
  have e1 := card_le_two_mul_inf_centralizer_of_comm (H := H) (a := a) hc.extra.order
    (fun h _ => hc.commute_z h) (fun h hh => hH h hh a ha)
  have e2 := card_le_two_mul_inf_centralizer_of_comm (H := H ⊓ centralizer ({a} : Set K))
    (a := b) hc.extra.order (fun h _ => hc.commute_z h) (fun h hh => hH h (mem_inf.mp hh).1 b hb)
  have e3 : H ⊓ centralizer ({a} : Set K) ⊓ centralizer ({b} : Set K) ≤
      H ⊓ centralizer (tim77I X g : Set K) := by
    intro d hd
    obtain ⟨hd', hdb⟩ := mem_inf.mp hd
    obtain ⟨hdH, hda⟩ := mem_inf.mp hd'
    refine ⟨hdH, mem_centralizer_iff.mpr fun j hj => ?_⟩
    have hle : zpowers a ⊔ zpowers b ≤ centralizer ({d} : Set K) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hda).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hdb).symm))
    exact mem_centralizer_singleton_iff.mp (hle (hab hj))
  have e4 := card_le_of_le e3
  have hprod := card_sup_mul_card_inf (H := tim77I X g)
    (R := H ⊓ centralizer (tim77I X g : Set K))
    (inf_le_right.trans (centralizer_le_normalizer _))
  have hinf : tim77I X g ⊓ (H ⊓ centralizer (tim77I X g : Set K)) ≤ zpowers z := by
    intro c hc'
    obtain ⟨hcI, hcR⟩ := mem_inf.mp hc'
    exact hc.center_I_le h8 hcI fun j hj => mem_centralizer_iff.mp (mem_inf.mp hcR).2 j hj
  have hinf2 := card_le_of_le hinf
  rw [hc.card_zpowers_z] at hinf2
  have h5 := card_le_of_le (sup_le hIH inf_le_left :
    tim77I X g ⊔ (H ⊓ centralizer (tim77I X g : Set K)) ≤ H)
  rw [h8] at hprod
  have h6 := Nat.mul_le_mul_left
    (Nat.card (tim77I X g ⊔ (H ⊓ centralizer (tim77I X g : Set K)) : Subgroup K)) hinf2
  have h7 : 4 * Nat.card (H ⊓ centralizer (tim77I X g : Set K) : Subgroup K) ≤ Nat.card H := by
    linarith
  omega

theorem mem_zpowers_of_comm_of_Q8 (h8 : Nat.card (tim77I X g) = 8) {d : K}
    (hd : d ∈ tim77D X g ⊓ centralizer (tim77I X g : Set K))
    (hYd : ∀ y ∈ X ⊓ centralizer (tim77I X g : Set K), y * d * y⁻¹ * d⁻¹ ∈ zpowers z) :
    d ∈ zpowers z := by
  have hsup := hc.sup_eq_of_eight h8
  have := zpowers_normal_of_mem_center hc.center
  have hW : X ≤ (centralizer ({barMap z d} : Set (K ⧸ zpowers z))).comap (barMap z) := by
    refine hsup.symm.le.trans (sup_le (fun i hi => mem_comap_centralizer_barMap.mpr ?_)
      (fun y hy => mem_comap_centralizer_barMap.mpr (hYd y hy)))
    have hid : i * d = d * i := mem_centralizer_iff.mp (mem_inf.mp hd).2 i hi
    rw [hid, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hdI := hc.mem_I_of_comm (mem_inf.mp hd).1
    fun x hx => mem_comap_centralizer_barMap.mp (hW hx)
  exact hc.center_I_le h8 hdI fun j hj => mem_centralizer_iff.mp (mem_inf.mp hd).2 j hj

theorem card_centralizer_le_of_Q8' (h8 : Nat.card (tim77I X g) = 8) :
    Nat.card ((X ⊓ centralizer (tim77I X g : Set K)) ⊓
      centralizer ((tim77B X g ⊓ centralizer (tim77I X g : Set K) : Subgroup K) : Set K) :
        Subgroup K) * Nat.card (tim77B X g ⊓ centralizer (tim77I X g : Set K) : Subgroup K) ≤
      2 * Nat.card (X ⊓ centralizer (tim77I X g : Set K) : Subgroup K) := by
  have hBX : tim77B X g ≤ X := inf_le_left
  have hY : Nat.card (X ⊓ centralizer (tim77I X g : Set K) : Subgroup K) *
      Nat.card (tim77I X g) = 2 * Nat.card X :=
    hc.extra.card_centralizer (inf_le_left : tim77I X g ≤ X) hc.z_mem_I
  rw [h8] at hY
  have hUX : tim77B X g ⊓ centralizer (tim77I X g : Set K) ≤ X := inf_le_left.trans hBX
  have hIU : tim77I X g ⊔ (tim77B X g ⊓ centralizer (tim77I X g : Set K)) ≤ X :=
    sup_le inf_le_left hUX
  have h := hc.extra.card_centralizer hIU ((le_sup_left : tim77I X g ≤ _) hc.z_mem_I)
  have hprod := card_sup_mul_card_inf (H := tim77I X g)
    (R := tim77B X g ⊓ centralizer (tim77I X g : Set K))
    (inf_le_right.trans (centralizer_le_normalizer _))
  have hinf : tim77I X g ⊓ (tim77B X g ⊓ centralizer (tim77I X g : Set K)) ≤ zpowers z := by
    intro c hc'
    obtain ⟨hcI, hcU⟩ := mem_inf.mp hc'
    exact hc.center_I_le h8 hcI fun j hj => mem_centralizer_iff.mp (mem_inf.mp hcU).2 j hj
  have hinf2 := card_le_of_le hinf
  rw [hc.card_zpowers_z] at hinf2
  rw [h8] at hprod
  have hle : (X ⊓ centralizer (tim77I X g : Set K)) ⊓
      centralizer ((tim77B X g ⊓ centralizer (tim77I X g : Set K) : Subgroup K) : Set K) ≤
      X ⊓ centralizer ((tim77I X g ⊔ (tim77B X g ⊓ centralizer (tim77I X g : Set K)) :
        Subgroup K) : Set K) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
    exact ⟨(mem_inf.mp hy1).1, mem_centralizer_sup (mem_inf.mp hy1).2 hy2⟩
  have hv := card_le_of_le hle
  have e1 := Nat.mul_le_mul_left (Nat.card (tim77I X g ⊔ (tim77B X g ⊓
    centralizer (tim77I X g : Set K)) : Subgroup K)) hinf2
  have e2 : 4 * Nat.card (tim77B X g ⊓ centralizer (tim77I X g : Set K) : Subgroup K) ≤
      Nat.card (tim77I X g ⊔ (tim77B X g ⊓ centralizer (tim77I X g : Set K)) :
        Subgroup K) := by linarith
  have e3 := Nat.mul_le_mul_left (Nat.card (X ⊓ centralizer ((tim77I X g ⊔ (tim77B X g ⊓
    centralizer (tim77I X g : Set K)) : Subgroup K) : Set K) : Subgroup K)) e2
  have e4 := Nat.mul_le_mul_right
    (Nat.card (tim77B X g ⊓ centralizer (tim77I X g : Set K) : Subgroup K)) hv
  nlinarith

end Conf110

end Natural

end CFSG.ComponentClassification.AS81
