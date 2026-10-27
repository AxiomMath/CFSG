module

public import CFSG.LocalAnalysis.EvenBN.U4.CenterUThree
public import CFSG.LocalAnalysis.EvenBN.U4.LayersTwo
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusSeven

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf card_sup_mul_card_inf_eq)

noncomputable abbrev miyamotoD0G {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) : Subgroup G :=
  ((powMonoidHom (2 ^ f + 1) : Kˣ →* Kˣ).ker).map (miyamotoDHom h L η)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem exists_I2_mul_IN2 (hS : Setting h L η t Q T) {i : G} (hi : i ∈ miyamotoIG h L η) :
    ∃ i₂ ∈ miyamotoI2G h L η, ∃ d ∈ miyamotoIN2G h L η, i = i₂ * d := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  obtain ⟨p, hp, rfl⟩ := hS.exists_torusElt_eq hi
  have hs := (miyamotoIParam_eq_one_iff h p).1 hp
  obtain ⟨x, hx⟩ := Common.exists_units_sq_eq p.1
  have hx0 : (x : K) ≠ 0 := x.ne_zero
  have hy0 : (x : K) ^ (2 ^ f - 1) ≠ 0 := pow_ne_zero _ hx0
  have hbx : h.bar (x : K) = (x : K) ^ (2 ^ f - 1) * x := by
    rw [h.bar_apply, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
  set u : Kˣ := (x ^ (2 ^ f - 1))⁻¹ * p.2 with hu
  have hubar : h.bar (u : K) = u := by
    have e1 : ((p.1 : Kˣ) : K) = (x : K) ^ 2 := by rw [← hx, Units.val_pow_eq_pow_val]
    rw [e1, map_mul, map_pow, hbx] at hs
    have key : (x : K) ^ 2 * ((x : K) ^ (2 ^ f - 1) * ((x : K) ^ (2 ^ f - 1) * h.bar p.2)) =
        (x : K) ^ 2 * p.2 := by
      rw [← hs]
      ring
    have key' := mul_left_cancel₀ (pow_ne_zero 2 hx0) key
    simp only [hu, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul,
      map_inv₀, bar_pow_sub_one h hx0, inv_inv]
    rw [eq_inv_mul_iff_mul_eq₀ hy0]
    exact key'
  have hp₂ : miyamotoIParam h (x ^ 2, x ^ (2 ^ f - 1)) = 1 :=
    (miyamotoIHom_mem_miyamotoI_iff h _).1 (miyamotoI2_le_I h ((mem_miyamotoI2 h).2 ⟨x, rfl⟩))
  have hpu : miyamotoIParam h (1, u) = 1 := miyamotoIParam_one_eq_one h hubar
  refine ⟨hS.torusElt _ hp₂, hS.torusElt_mem_pull _ hp₂ ((mem_miyamotoI2 h).2 ⟨x, rfl⟩),
    hS.torusElt (1, u) hpu, mem_inf.2 ⟨hS.torusElt_mem_IG _ hpu,
      hS.torusElt_mem_pull _ hpu (miyamotoIHom_one_mem_N2 h hubar)⟩, ?_⟩
  rw [hS.torusElt_mul]
  have e : p = (x ^ 2, x ^ (2 ^ f - 1)) * (1, u) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, mul_one, hx]
    · simp only [Prod.snd_mul, hu, mul_inv_cancel_left]
  have key : ∀ (p p' : Kˣ × Kˣ) (hp : miyamotoIParam h p = 1)
      (hp' : miyamotoIParam h p' = 1), p = p' → hS.torusElt p hp = hS.torusElt p' hp' := by
    rintro p p' hp hp' rfl
    rfl
  exact key _ _ _ _ e

theorem R1G_conj_miyamotoDHom (_hS : Setting h L η t Q T) (α : Kˣ) :
    (miyamotoR1G h L η)⁻¹ * miyamotoDHom h L η α * miyamotoR1G h L η =
      miyamotoDHom h L η α⁻¹ := by
  simp only [miyamotoR1G, miyamotoDHom, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
  rw [← L.coe_inv, ← L.coe_mul, ← L.coe_mul, ← map_inv, ← map_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_miyamotoDHomSU]
  rw [miyamotoR1_conj_miyamotoIHom]
  simp

theorem miyamotoDHom_commute_ZG (_hS : Setting h L η t Q T) {α : Kˣ}
    (hα : (α : K) * h.bar α = 1) {z : G} (hz : z ∈ miyamotoZG h L η) :
    miyamotoDHom h L η α * z = z * miyamotoDHom h L η α := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hz
  obtain ⟨d, -, hgd⟩ := (mem_Z h).1 hg
  have hw : ((miyamotoWeightZ h (α, α⁻¹) : Kˣ) : K) = 1 := by
    rw [coe_miyamotoWeightZ]
    exact hα
  have key : miyamotoIHom h (α, α⁻¹) * (g : GL (Fin 4) K) = g * miyamotoIHom h (α, α⁻¹) := by
    have e := miyamotoIHom_conj_Z h (α, α⁻¹) d
    rw [hw, one_mul, ← hgd] at e
    calc miyamotoIHom h (α, α⁻¹) * (g : GL (Fin 4) K) =
        miyamotoIHom h (α, α⁻¹) * ((miyamotoIHom h (α, α⁻¹))⁻¹ * g * miyamotoIHom h (α, α⁻¹)) :=
          by rw [e]
      _ = g * miyamotoIHom h (α, α⁻¹) := by group
  have e2 : miyamotoDHomSU h α * g = g * miyamotoDHomSU h α :=
    Subtype.ext (by simpa only [Subgroup.coe_mul, coe_miyamotoDHomSU] using key)
  simp only [miyamotoDHom, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom]
  rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, e2]

theorem normOne_le_DG (_hS : Setting h L η t Q T) : miyamotoD0G h L η ≤ miyamotoDG h L η := by
  rintro _ ⟨α, -, rfl⟩
  exact miyamotoDHom_mem h L η α

theorem normOne_le_centralizer_ZG (hS : Setting h L η t Q T) :
    miyamotoD0G h L η ≤ centralizer (miyamotoZG h L η : Set G) := by
  rintro _ ⟨α, hα, rfl⟩
  rw [mem_centralizer_iff]
  intro z hz
  have hN : (α : K) * h.bar α = 1 := by
    rw [h.bar_apply]
    have e : ((α ^ (2 ^ f + 1) : Kˣ) : K) = 1 := by
      rw [show α ^ (2 ^ f + 1) = 1 from hα, Units.val_one]
    rw [Units.val_pow_eq_pow_val] at e
    calc (α : K) * (α : K) ^ 2 ^ f = (α : K) ^ (2 ^ f + 1) := by ring
      _ = 1 := e
  exact (hS.miyamotoDHom_commute_ZG hN hz).symm

theorem card_normOne (_hS : Setting h L η t Q T) : Nat.card (miyamotoD0G h L η) = 2 ^ f + 1 := by
  have : Finite K := h.finite
  rw [card_map_of_injective (miyamotoDHom_injective h L η)]
  refine Common.card_ker_powMonoidHom_of_dvd ?_
  rw [Nat.card_units, h.card_eq_sq]
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ f = m + 1 := ⟨2 ^ f - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  rw [hm]
  refine ⟨m, ?_⟩
  rw [show (m + 1) ^ 2 = (m + 1 + 1) * m + 1 by ring, Nat.add_sub_cancel]

theorem E_r1_le_F1 (hS : Setting h L η t Q T) :
    (miyamotoEG h L η Q).map (MulAut.conj (miyamotoR1G h L η)⁻¹).toMonoidHom ≤
      miyamotoF1G h L η t := by
  rintro _ ⟨e, he, rfl⟩
  have hr := hS.N1_le_normalizer_F1 (inv_mem hS.R1G_mem_N1)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact (mem_normalizer_iff.1 hr e).1 (hS.E_le_F1 he)

theorem E_r1_le_normalizer_F (hS : Setting h L η t Q T) :
    (miyamotoEG h L η Q).map (MulAut.conj (miyamotoR1G h L η)⁻¹).toMonoidHom ≤
      normalizer (miyamotoFG h L η t Q : Set G) := fun _ hx =>
  mem_normalizer_of_mem_centralizer' (mem_centralizer_iff.2 fun _ hy =>
    hS.F1_comm (hS.F_le_F1 hy) (hS.E_r1_le_F1 hx))

theorem F1_eq_F_sup_E_r1 (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t = miyamotoFG h L η t Q ⊔
      (miyamotoEG h L η Q).map (MulAut.conj (miyamotoR1G h L η)⁻¹).toMonoidHom := by
  have h1 := card_sup_mul_card_inf_eq hS.E_r1_le_normalizer_F
  rw [inf_comm, hS.E_r1_inf_F, card_bot, mul_one, hS.card_F,
    card_map_of_injective (MulAut.conj (miyamotoR1G h L η)⁻¹).injective, hS.card_E] at h1
  refine (Subgroup.eq_of_le_of_card_ge (sup_le hS.F_le_F1 hS.E_r1_le_F1) ?_).symm
  rw [h1, hS.card_F1]
  ring_nf
  exact le_rfl

theorem commutator_mem_F_of_mem_DG (hS : Setting h L η t Q T) {d x : G}
    (hd : d ∈ miyamotoDG h L η) (hdE : d ∈ centralizer (miyamotoEG h L η Q : Set G))
    (hx : x ∈ miyamotoF1G h L η t) : d * x * d⁻¹ * x⁻¹ ∈ miyamotoFG h L η t Q := by
  set r := miyamotoR1G h L η with hr
  have hrr : r * r = 1 := hS.R1G_mul_self
  have hdI : d ∈ miyamotoIG h L η := (mem_inf.1 hd).1
  obtain ⟨α, rfl⟩ : ∃ α, miyamotoDHom h L η α = d := by
    rw [← range_miyamotoDHom h L η] at hd
    exact hd
  set D := miyamotoDHom h L η α with hD
  have hrd : r⁻¹ * D * r = D⁻¹ := by rw [hD, hS.R1G_conj_miyamotoDHom, map_inv]
  have h2 : D = r⁻¹ * D⁻¹ * r := by
    calc D = (r * r)⁻¹ * D * (r * r) := by rw [hrr]; group
      _ = r⁻¹ * (r⁻¹ * D * r) * r := by group
      _ = r⁻¹ * D⁻¹ * r := by rw [hrd]
  rw [hS.F1_eq_F_sup_E_r1] at hx
  obtain ⟨y, hy, e', he', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hS.E_r1_le_normalizer_F hx
  obtain ⟨e, he, rfl⟩ := he'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have h1 : e * D = D * e := mem_centralizer_iff.1 hdE e he
  have h1' : D⁻¹ * e = e * D⁻¹ := by
    calc D⁻¹ * e = D⁻¹ * (e * D) * D⁻¹ := by group
      _ = D⁻¹ * (D * e) * D⁻¹ := by rw [h1]
      _ = e * D⁻¹ := by group
  have hcomm : D * (r⁻¹ * e * r) = (r⁻¹ * e * r) * D := by
    calc D * (r⁻¹ * e * r) = (r⁻¹ * D⁻¹ * r) * (r⁻¹ * e * r) := by rw [← h2]
      _ = r⁻¹ * (D⁻¹ * e) * r := by group
      _ = r⁻¹ * (e * D⁻¹) * r := by rw [h1']
      _ = (r⁻¹ * e * r) * (r⁻¹ * D⁻¹ * r) := by group
      _ = (r⁻¹ * e * r) * D := by rw [← h2]
  have hcomm' : (r⁻¹ * e * r) * D⁻¹ = D⁻¹ * (r⁻¹ * e * r) := by
    calc (r⁻¹ * e * r) * D⁻¹ = D⁻¹ * (D * (r⁻¹ * e * r)) * D⁻¹ := by group
      _ = D⁻¹ * ((r⁻¹ * e * r) * D) * D⁻¹ := by rw [hcomm]
      _ = D⁻¹ * (r⁻¹ * e * r) := by group
  have e3 : D * (y * (r⁻¹ * e * r)) * D⁻¹ * (y * (r⁻¹ * e * r))⁻¹ = D * y * D⁻¹ * y⁻¹ := by
    calc D * (y * (r⁻¹ * e * r)) * D⁻¹ * (y * (r⁻¹ * e * r))⁻¹ =
        D * y * ((r⁻¹ * e * r) * D⁻¹) * (r⁻¹ * e * r)⁻¹ * y⁻¹ := by group
      _ = D * y * (D⁻¹ * (r⁻¹ * e * r)) * (r⁻¹ * e * r)⁻¹ * y⁻¹ := by rw [hcomm']
      _ = D * y * D⁻¹ * y⁻¹ := by group
  rw [e3]
  exact mul_mem ((mem_normalizer_iff.1 (hS.IG_le_normalizer_F hdI) y).1 hy) (inv_mem hy)

theorem mem_centralizer_V2_of_commutator_mem_F (hS : Setting h L η t Q T) {j : G}
    (hjF2 : j ∈ normalizer (miyamotoF2G h L η t Q : Set G))
    (hjV : j ∈ normalizer ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) :
      Subgroup G) : Set G))
    (hc : ∀ x ∈ miyamotoF1G h L η t, j * x * j⁻¹ * x⁻¹ ∈ miyamotoFG h L η t Q) :
    j ∈ centralizer ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) :
      Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  intro v hv
  obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG (mem_inf.1 hv).1
  have hwF2 : w ∈ miyamotoF2G h L η t Q := hS.W_le_F2 hw
  have h1 : j * (w * y) * j⁻¹ * (w * y)⁻¹ ∈ miyamotoF2G h L η t Q := by
    have e : j * (w * y) * j⁻¹ * (w * y)⁻¹ = (j * w * j⁻¹) * (j * y * j⁻¹ * y⁻¹) * w⁻¹ := by
      group
    rw [e]
    exact mul_mem (mul_mem ((mem_normalizer_iff.1 hjF2 w).1 hwF2) (hS.F_le_F2 (hc y hy)))
      (inv_mem hwF2)
  have h2 : j * (w * y) * j⁻¹ * (w * y)⁻¹ ∈
      miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) :=
    mul_mem ((mem_normalizer_iff.1 hjV _).1 hv) (inv_mem hv)
  have h3 : j * (w * y) * j⁻¹ * (w * y)⁻¹ = 1 := by
    have := mem_inf.2 ⟨h1, (mem_inf.1 h2).2⟩
    rw [hS.F2_inf_centralizer_I2] at this
    exact this
  have h4 : j * (w * y) * j⁻¹ = w * y := mul_inv_eq_one.1 h3
  exact (mul_inv_eq_iff_eq_mul.1 h4).symm

theorem normalizer_RG_le_normalizer_E (hS : Setting h L η t Q T) :
    normalizer (miyamotoRG h L η t Q : Set G) ≤ normalizer (miyamotoEG h L η Q : Set G) := by
  rw [← hS.centerIn_RG]
  exact normalizer_le_normalizer_centerIn _

theorem normalizer_RG_le_normalizer_F (hS : Setting h L η t Q T) :
    normalizer (miyamotoRG h L η t Q : Set G) ≤ normalizer (miyamotoFG h L η t Q : Set G) := by
  have key : ∀ n ∈ normalizer (miyamotoRG h L η t Q : Set G), ∀ x ∈ miyamotoFG h L η t Q,
      n * x * n⁻¹ ∈ miyamotoFG h L η t Q := by
    intro n hn x hx
    have hxR := hS.F_le_RG hx
    have hnx : n * x * n⁻¹ ∈ miyamotoRG h L η t Q := (mem_normalizer_iff.1 hn x).1 hxR
    refine (hS.mem_F_iff_of_mem_RG hnx).2 fun r hr => ?_
    have hr' : n⁻¹ * r * n ∈ miyamotoRG h L η t Q := by
      have := (mem_normalizer_iff.1 (inv_mem hn) r).1 hr
      rwa [inv_inv] at this
    have hc := (hS.mem_F_iff_of_mem_RG hxR).1 hx _ hr'
    have hE := (mem_normalizer_iff.1 (hS.normalizer_RG_le_normalizer_E hn) _).1 hc
    have e : n * (x * (n⁻¹ * r * n) * x⁻¹ * (n⁻¹ * r * n)⁻¹) * n⁻¹ =
        n * x * n⁻¹ * r * (n * x * n⁻¹)⁻¹ * r⁻¹ := by group
    rwa [e] at hE
  intro n hn
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hx
  rwa [inv_inv, show n⁻¹ * (n * x * n⁻¹) * n = x by group] at this

theorem normalizer_RG_le_normalizer_F1 (hS : Setting h L η t Q T) :
    normalizer (miyamotoRG h L η t Q : Set G) ≤ normalizer (miyamotoF1G h L η t : Set G) := by
  rw [← hS.RG_inf_centralizer_F]
  intro n hn
  exact mem_normalizer_inf hn (mem_normalizer_centralizer (hS.normalizer_RG_le_normalizer_F hn))

theorem M2G_le_centralizer_E (hS : Setting h L η t Q T) :
    miyamotoM2G h L η t Q ≤ centralizer (miyamotoEG h L η Q : Set G) := by
  set H := miyamotoH2G h L η t Q with hH
  set C := centralizer (miyamotoEG h L η Q : Set G) with hC
  have hN : (C.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ normalizer (miyamotoEG h L η Q : Set G) :=
      hS.normalizer_F2_le_normalizer_E (mem_inf.1 g.2).1
    have := mem_normalizer_centralizer hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.1 this n).1 hn
  have hle : (((miyamotoN2G h L η).subgroupOf H : Subgroup H) : Set H) ⊆ C.subgroupOf H :=
    fun x hx => hS.N2G_le_centralizer_E hx
  have hcl := normalClosure_le_normal hle
  rintro _ ⟨x, hx, rfl⟩
  exact hcl hx

theorem R1G_not_mem_centralizer_ZG (hS : Setting h L η t Q T) :
    miyamotoR1G h L η ∉ centralizer (miyamotoZG h L η : Set G) := by
  intro hr
  have hZ : miyamotoZG h L η = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    rw [← hS.E_r1_inf_F]
    refine mem_inf.2 ⟨?_, hS.E_le_F (hS.ZP_le_E hz)⟩
    rw [mem_map_conj_inv_iff]
    have hc : z * miyamotoR1G h L η = miyamotoR1G h L η * z := mem_centralizer_iff.1 hr z hz
    rw [← hc, mul_inv_cancel_right]
    exact hS.ZP_le_E hz
  have hcard : Nat.card (miyamotoZG h L η) = 2 ^ f := card_miyamotoZG h L η
  rw [hZ, card_bot] at hcard
  have : 2 ≤ 2 ^ f := Nat.le_self_pow (by have := hS.two_le; omega) 2
  omega

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
