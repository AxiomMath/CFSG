module

public import CFSG.LargeExtraspecial.S8FusD
public import CFSG.LargeExtraspecial.S8Comm
public import CFSG.LargeExtraspecial.S8FusC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Claim

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {Q : QuadraticForm (ZMod 2) (Vt S g t)}
  (hQ : Q.polarBilin.Nondegenerate)
  (hpol : Q.polarBilin = beta H C ht ht1 hVQ) (hE : LmodN S g t = pointRadical Q (aV ht))
  (hQa : Q (aV ht) = 0)
  (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
  (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
    S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
  (hA : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
    2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width)
  (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
  {h : S.M} (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
  (hPab : S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t)
  (hNc : ∀ x ∈ Nbar S g t, ∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t)
  (hNsq : ∀ x ∈ Nbar S g t, x * x ∈ zpowers t)
  (hgen : PairGen S g t) (hN0 : Nbar S g t = N0bar S g t)
  (h3 : 3 ≤ finrank (ZMod 2) (Vt S g t))
include H C ht ht1 hVQ hQ hpol hE hQa hsing hfus hA hN hh hb hPab hNc hNsq hgen hN0 h3

omit hQ hpol hE hQa hsing hA hN hh hb hPab hNc hNsq hgen hN0 h3 in
theorem not_mem_orbit_of_fusion_beta {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → τ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    ∀ d ∈ Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt), d ∉ orbit S g t := by
  rintro d ⟨-, hdτ⟩ hd
  obtain ⟨k, hk, rfl⟩ := exists_of_mem_orbit hd H.conj_mem
  have hV1eq : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [hxτ, commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  rw [hV1eq] at hdτ
  obtain ⟨v, hv, hvd⟩ := hdτ
  obtain ⟨k₁, hk₁⟩ := MonoidHom.mem_range.mp (S.Mbar.mul_mem (inv_mem hxM) (Rbar_le_Mbar hk))
  have hv1 : v = S.cl ((k₁ : G) * g * S.z * ((k₁ : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S k₁ H.conj_mem, hk₁]
    change v = ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ k : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g * S.z * g⁻¹)))
    rw [ρ_cl_conj_z S k H.conj_mem, ← hvd]
    exact (inv_apply_apply_O x v).symm
  have hvorb := hfus k₁ (hv1 ▸ hv)
  rw [← hv1] at hvorb
  obtain ⟨k₂, hk₂, hk₂v⟩ := exists_of_mem_orbit hvorb H.conj_mem
  obtain ⟨k₃, hk₃⟩ := MonoidHom.mem_range.mp (S.Mbar.mul_mem hxM (Rbar_le_Mbar hk₂))
  have hcl : S.cl ((k₃ : G) * g * S.z * ((k₃ : G) * g)⁻¹) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S k₃ H.conj_mem, hk₃]
    change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ k₂ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g * S.z * g⁻¹))) = _
    rw [ρ_cl_conj_z S k₂ H.conj_mem, ← hk₂v]
    exact hvd
  have hLeq := Lbar_eq_of_cl_eq S (conj_mem_QG' S k.2 H.conj_mem) (conj_ne_z' S k.2 H.conj_ne)
    (conj_mem_QG' S k₃.2 H.conj_mem) hcl
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have hτk : τ ∈ S.Lbar ((k : G) * g) := by
    rw [← hLeq]
    have h1 := conj_mem_Lbar_mul S k₃ ht
    have e : S.ρ k₃ * t * (S.ρ k₃)⁻¹ = τ := by
      rw [hk₃, hxτ, mul_inv_rev]
      have hc := commute_of_mem_Rbar H.conj_mem hk₂
      calc x * S.ρ k₂ * t * ((S.ρ k₂)⁻¹ * x⁻¹) = x * (S.ρ k₂ * t) * (S.ρ k₂)⁻¹ * x⁻¹ := by
            group
        _ = x * (t * S.ρ k₂) * (S.ρ k₂)⁻¹ * x⁻¹ := by rw [hc]
        _ = x * t * x⁻¹ := by group
    rwa [e] at h1
  exact hβ k hk ⟨hτk, mem_Nbar.mpr ⟨Lbar_mul_le_Rbar htk hτk, hτV⟩⟩

theorem fusion_claim {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹)
    (hτt' : τ * t = t * τ) (hτt : τ ≠ t)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hτW : ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    ∃ n ∈ Nbar S g t, n * τ * n⁻¹ = τ * t := by
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hconjN : ∀ {k : S.M}, S.ρ k ∈ Rbar S g t → ∀ n ∈ Nbar S g t,
      S.ρ k * n * (S.ρ k)⁻¹ ∈ Nbar S g t := fun {k} hk n hn =>
    conj_mem_Nbar H.conj_mem (commute_of_mem_Rbar H.conj_mem hk) hn
  have hconjN' : ∀ {k : S.M}, S.ρ k ∈ Rbar S g t → ∀ n ∈ Nbar S g t,
      (S.ρ k)⁻¹ * n * S.ρ k ∈ Nbar S g t := fun {k} hk n hn => by
    have h1 : S.ρ k⁻¹ ∈ Rbar S g t := by rw [map_inv]; exact inv_mem hk
    have := hconjN h1 n hn
    rwa [map_inv, inv_inv] at this
  by_cases hα : ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧ τ ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t
  · obtain ⟨k, hk, hτk⟩ := hα
    have hkt := commute_of_mem_Rbar H.conj_mem hk
    have hτ'A : (S.ρ k)⁻¹ * τ * S.ρ k ∈ S.Lbar g ⊓ Nbar S g t :=
      ⟨(mem_Lbar_mul_iff S k g).mp hτk.1, hconjN' hk τ hτk.2⟩
    have hτ'x : (S.ρ k)⁻¹ * τ * S.ρ k = ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by
      rw [hxτ]; group
    have hτ't : (S.ρ k)⁻¹ * τ * S.ρ k ≠ t := by
      intro he
      apply hτt
      calc τ = S.ρ k * ((S.ρ k)⁻¹ * τ * S.ρ k) * (S.ρ k)⁻¹ := by group
        _ = S.ρ k * t * (S.ρ k)⁻¹ := by rw [he]
        _ = t := by rw [hkt, mul_inv_cancel_right]
    obtain ⟨n, hn, hnτ⟩ := fusion_alpha H C ht ht1 hVQ hpol hE hQa hA hN hh hb hPab hNc hτ'A
      (S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hk)) hxM) hτ'x hτ't
    refine ⟨S.ρ k * n * (S.ρ k)⁻¹, hconjN hk n hn, ?_⟩
    calc S.ρ k * n * (S.ρ k)⁻¹ * τ * (S.ρ k * n * (S.ρ k)⁻¹)⁻¹ =
        S.ρ k * (n * ((S.ρ k)⁻¹ * τ * S.ρ k) * n⁻¹) * (S.ρ k)⁻¹ := by group
      _ = S.ρ k * ((S.ρ k)⁻¹ * τ * S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hnτ]
      _ = τ * (S.ρ k * t * (S.ρ k)⁻¹) := by group
      _ = τ * t := by rw [hkt, mul_inv_cancel_right]
  push Not at hα
  by_contra hcon
  push Not at hcon
  have hcN : ∀ n ∈ Nbar S g t, n * τ = τ * n := by
    intro n hn
    have h1 := comm_mem_zpowers_of_mem_Nbar H C ht ht1 hVQ hgen hN0 h3 hN hτM hτt' hτV hτW hn
    have htt := mul_self_of_mem_Lbar S H.conj_mem ht
    rcases eq_one_or_eq_of_mem_zpowers htt h1 with h2 | h2
    · calc n * τ = (τ * n * τ⁻¹ * n⁻¹)⁻¹ * (τ * n) := by group
        _ = τ * n := by rw [h2, inv_one, one_mul]
    · exfalso
      apply hcon n hn
      calc n * τ * n⁻¹ = (τ * n * τ⁻¹ * n⁻¹)⁻¹ * τ := by group
        _ = t * τ := by rw [h2, inv_eq_of_mul_eq_one_right htt]
        _ = τ * t := hτt'.symm
  have hV1W := commSpace_le_Wt_of_fix (g := g) hτV
  have hanis := not_mem_orbit_of_fusion_beta H C ht ht1 hVQ hfus hxM hxτ hτV hα
  obtain ⟨d₀, hd₀, hd⟩ := exists_center_of_fusion_beta H C ht ht1 hVQ hQ hsing hfus hN hNsq
    hxM hxτ hcN hV1W hanis
  obtain ⟨k, hk, hkfix⟩ := exists_Abar_fix_of_fusion_beta H C ht ht1 hVQ hV1W hd₀ hd
  set r := S.ρ k with hr
  have hrinv : r⁻¹ ∈ Rbar S g t := inv_mem hk
  have hV1eq : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [hxτ, commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  have hV1' : commSpace ((r⁻¹ * τ * r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
        ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [← commSpace_conj, inv_inv]
  refine false_of_fusion_beta H C ht ht1 hVQ hA hN hh hb hPab (τ := r⁻¹ * τ * r)
    (fun v hv => ?_) ?_ (fun n hn => ?_) ?_ ?_
  · change ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = v
    rw [hτV _ (apply_mem_Vt_of_mem_Rbar H.conj_mem hk hv), inv_apply_apply_O]
  · rw [hV1', LinearEquiv.finrank_map_eq, hV1eq, LinearEquiv.finrank_map_eq]
  · have h1 := hcN _ (hconjN hk n hn)
    calc n * (r⁻¹ * τ * r) = r⁻¹ * ((r * n * r⁻¹) * τ) * r := by group
      _ = r⁻¹ * (τ * (r * n * r⁻¹)) * r := by rw [h1]
      _ = r⁻¹ * τ * r * n := by group
  · rintro d ⟨hdV, hdτ⟩ hdorb
    rw [hV1'] at hdτ
    obtain ⟨w, hw, rfl⟩ := hdτ
    have hrw : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w :=
      apply_inv_apply_O r w
    have h1 := apply_mem_Vt_of_mem_Rbar H.conj_mem hk hdV
    have h2 := apply_mem_orbit hk hdorb
    change (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ _ at h1 h2
    rw [hrw] at h1 h2
    exact hanis w ⟨h1, hw⟩ h2
  · intro a' ha' w hw
    rw [hV1'] at hw
    obtain ⟨w₁, hw₁, rfl⟩ := hw
    have hrar : r * a' * r⁻¹ ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t :=
      ⟨conj_mem_Lbar_mul S k ha'.1, hconjN hk a' ha'.2⟩
    have h1 := hkfix _ hrar w₁ hw₁
    change ((r * a' * r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ = w₁ at h1
    change (a' : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁) =
      ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁
    have h2 : (a' : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁) =
        ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (((r * a' * r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁) := by
      change _ = ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((a' : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁)))
      rw [inv_apply_apply_O]
    rw [h2, h1]

end Claim

end CFSG.LargeExtraspecial.S8
