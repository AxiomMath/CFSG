module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DFull
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DThree

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace D13

variable {x : G} {T V H : Subgroup G} {f : G} (d : D13 x T V H f)
include d

theorem exists_moved : ∃ v ∈ V, f * v * f⁻¹ ≠ v := by
  by_contra hcon
  push Not at hcon
  apply d.hI.f_C
  rw [mem_centralizer_iff]
  intro v hv
  have := hcon v hv
  calc v * f = (f * v * f⁻¹) * f := by rw [this]
    _ = f * v := by group

theorem R_inf_cent [Finite G] {R : Subgroup G} (hR2 : IsPGroup 2 ↥R) (hRM : R ≤ Mm V H)
    (hHR : H ≤ R) : R ⊓ centralizer ({x} : Set G) = EV x V := by
  apply le_antisymm
  · apply d.out.cent_E_le (hR2.to_le inf_le_left)
    intro g hg
    exact d.out.centralizes_EV (hRM hg.1).1 hg.2
  · refine le_inf (d.hI.E_le.trans hHR) (fun e he => ?_)
    show e ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact d.out.EV_comm x_mem_EV he

theorem cls_R_full [Finite G] {R : Subgroup G} (hR : SylowIn 2 R (Mm V H)) (hHR : H < R) :
    ∀ q ∈ Hzero H f, q * x ∈ cls R x := by
  obtain ⟨n, hn1, hn, hRc, hX⟩ := d.cls_full hR hHR
  have hxR : x ∈ R := hHR.le d.hI.x_mem
  have hcard := card_cls_mul R hxR
  rw [d.R_inf_cent hR.isPGroup hR.le hHR.le, d.out.card_EV, hRc] at hcard
  have h4 : Nat.card (cls R x) = 4 ^ n := by
    have : 2 ^ (2 * n + 3) = 8 * 4 ^ n := by rw [pow_add, pow_mul]; norm_num; ring
    rw [this] at hcard
    omega
  have hsub : cls R x ⊆ (fun q => q * x) '' (Hzero H f : Set G) := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := hy
    obtain ⟨q, hq, hq'⟩ := d.cls_sub (y := r * x * r⁻¹) ⟨r, hR.le hr, rfl⟩
    exact ⟨q, hq, hq'.symm⟩
  have hnc : ((fun q => q * x) '' (Hzero H f : Set G)).ncard = 4 ^ n := by
    rw [Set.ncard_image_of_injective _ (mul_left_injective x), ← hn]
    exact (Nat.card_coe_set_eq (Hzero H f : Set G)).symm
  have hle : ((fun q => q * x) '' (Hzero H f : Set G)).ncard ≤ (cls R x).ncard := by
    rw [hnc, ← Nat.card_coe_set_eq, h4]
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  intro q hq
  rw [heq]
  exact ⟨q, hq, rfl⟩

theorem exists_f3 [Finite G] {R : Subgroup G} (hR : SylowIn 2 R (Mm V H)) (hHR : H < R) :
    ∃ g : G, g ∈ normalizer (R : Set G) ∧ g ∈ normalizer (V : Set G) ∧
      g ∈ normalizer (H : Set G) ∧ g * x * g⁻¹ = x ∧ ∀ z ∈ V, g * z * g⁻¹ = f * z * f⁻¹ := by
  obtain ⟨n, hn, hnR⟩ := sylowIn_frattini hR
    (M := normalizer (V : Set G) ⊓ normalizer (H : Set G))
    (fun m hm n hn => conj_mem_Mm hm.1 hm.2 hn) ⟨d.hI.f_N, d.hI.f_H⟩
  have hnV : n ∈ normalizer (V : Set G) := centralizer_le_normalizer _ hn.1
  have hf₂V : n⁻¹ * f ∈ normalizer (V : Set G) :=
    (normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).inv_mem hnV) d.hI.f_N
  have hf₂H : n⁻¹ * f ∈ normalizer (H : Set G) :=
    (normalizer (H : Set G)).mul_mem ((normalizer (H : Set G)).inv_mem hn.2) d.hI.f_H
  obtain ⟨q, hq, hqx⟩ := d.conj_mem hf₂V hf₂H
  obtain ⟨r, hr, hrx⟩ := d.cls_R_full hR hHR q hq
  have hrM : r ∈ Mm V H := hR.le hr
  have hrV : r ∈ normalizer (V : Set G) := centralizer_le_normalizer _ hrM.1
  refine ⟨r⁻¹ * (n⁻¹ * f), ?_, ?_, ?_, ?_, ?_⟩
  · exact (normalizer (R : Set G)).mul_mem
      ((normalizer (R : Set G)).inv_mem (le_normalizer hr)) hnR
  · exact (normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).inv_mem hrV) hf₂V
  · exact (normalizer (H : Set G)).mul_mem ((normalizer (H : Set G)).inv_mem hrM.2) hf₂H
  · calc r⁻¹ * (n⁻¹ * f) * x * (r⁻¹ * (n⁻¹ * f))⁻¹
        = r⁻¹ * ((n⁻¹ * f) * x * (n⁻¹ * f)⁻¹) * r := by group
      _ = r⁻¹ * (q * x) * r := by rw [hqx]
      _ = r⁻¹ * (r * x * r⁻¹) * r := by rw [hrx]
      _ = x := by group
  · intro z hz
    have hw : f * z * f⁻¹ ∈ V := (mem_normalizer_iff.1 d.hI.f_N z).1 hz
    have hm : r⁻¹ * n⁻¹ ∈ centralizer (V : Set G) :=
      (centralizer (V : Set G)).mul_mem ((centralizer (V : Set G)).inv_mem hrM.1)
        ((centralizer (V : Set G)).inv_mem hn.1)
    have hc := mem_centralizer_iff.1 hm _ hw
    calc r⁻¹ * (n⁻¹ * f) * z * (r⁻¹ * (n⁻¹ * f))⁻¹
        = (r⁻¹ * n⁻¹) * (f * z * f⁻¹) * (r⁻¹ * n⁻¹)⁻¹ := by group
      _ = f * z * f⁻¹ := by
        rw [← hc]; group

theorem exists_f' [Finite G] {R : Subgroup G} (hR : SylowIn 2 R (Mm V H)) (hHR : H < R) :
    ∃ f' : G, Is3Element f' ∧ f' ∈ normalizer (R : Set G) ∧ f' ∈ normalizer (V : Set G) ∧
      f' * x = x * f' ∧ ∀ z ∈ V, f' * z * f'⁻¹ = f * z * f⁻¹ := by
  obtain ⟨g, hgR, hgV, -, hgx, hgact⟩ := d.exists_f3 hR hHR
  obtain ⟨c, hc3, hfc⟩ := exists_three_part g f d.hI.f3
  have hfV : ∀ z ∈ V, f * z * f⁻¹ ∈ V := fun z hz => (mem_normalizer_iff.1 d.hI.f_N z).1 hz
  refine ⟨g ^ c, hc3, pow_mem hgR c, pow_mem hgV c, ?_, ?_⟩
  · have hcomm : Commute g x := mul_inv_eq_iff_eq_mul.1 hgx
    exact (hcomm.pow_left c).eq
  · intro z hz
    rw [(pow_act hfV hgact c z hz).1, hfc]

end D13

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
