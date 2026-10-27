module

public import CFSG.LargeExtraspecial.S3bEleven
public import CFSG.LargeExtraspecial.S8Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem apply_mem_clSub_of_apply_cl_eq (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {x : S.O} (hxM : x ∈ S.Mbar)
    (hxa : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hxM
  have h1 := apply_mem_clSub_Qa_mul k hv
  have hkQ : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S k.2 haQ
  have e : S.QG ⊓ S.Qa ((k : G) * g) = S.QG ⊓ S.Qa g := by
    refine QG_inf_Qa_eq_of_cl_eq haQ hne hkQ ?_
    rw [← ρ_cl_conj_z S k haQ]
    exact hxa
  rwa [e] at h1

theorem sub_mem_Vt_of_commute_Abar (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hA : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
      2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width)
    {z : S.O} (hzN : z ∈ Nbar S g t) (hzA : ∀ α ∈ S.Lbar g ⊓ Nbar S g t, α * z = z * α)
    {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    (z : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t := by
  have haQ := H.conj_mem
  have hne := H.conj_ne
  have hza : (z : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    (mem_Nbar.mp hzN).2 _ (aV ht).2
  have hzv : (z : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) :=
    apply_mem_clSub_of_apply_cl_eq haQ hne (Rbar_le_Mbar (Nbar_le_Rbar hzN)) hza hv
  have hmem : (z : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
      S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) := by
    refine ⟨(S.clSub (S.QG ⊓ S.Qa g)).sub_mem hzv hv, (mem_fixSub S).mpr fun α hα => ?_⟩
    have h1 := S.sub_mem_span_of_mem_clSub hα.1 hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    have hαv : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + c • S.cl (g * S.z * g⁻¹) := by
      rw [hc]; abel
    have hαz : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) ((z : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        (z : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
      rw [← coe_mul_apply, ← coe_mul_apply, hzA α hα]
    rw [map_sub, hαz, hαv, map_add, map_smul, hza]
    abel
  rw [clSub_inf_fixSub_Abar H C ht ht1 hVQ hA] at hmem
  exact hmem.2

theorem exists_clSub_sub_eq (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    ∃ p ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)),
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  by_contra hcon
  push Not at hcon
  apply ht1
  refine (C.mul k).faithful t htk fun v hv => ?_
  have h1 := S.sub_mem_span_of_mem_clSub htk hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul] at hc
    exact (sub_eq_zero.mp hc.symm)
  · rw [one_smul] at hc
    exact absurd hc.symm (hcon v hv)

theorem eq_top_of_le (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {K : Submodule (ZMod 2) S.Qt}
    (hWK : Wt S g t ≤ K)
    (hPK : ∀ k : S.M, S.ρ k ∈ Rbar S g t → S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ≤ K) :
    K = ⊤ := by
  set χ := chi H C ht ht1 hVQ with hχ
  set Kχ : Submodule (ZMod 2) (Vt S g t) :=
    (K.map (Wt S g t).mkQ).map (χ : (S.Qt ⧸ Wt S g t) →ₗ[ZMod 2] Vt S g t) with hKχ
  have hspan : Kχ = ⊤ := by
    rw [eq_top_iff, ← span_orbitOf_RmodN H ht, Submodule.span_le]
    intro v hv
    have hvorb := (mem_orbitOf_RmodN_iff H.conj_mem ht).mp hv
    obtain ⟨k, hk, hkv⟩ := exists_of_mem_orbit hvorb H.conj_mem
    obtain ⟨p, hp, hpt⟩ := exists_clSub_sub_eq H C ht ht1 hk
    refine ⟨Submodule.Quotient.mk p, ⟨p, hPK k hk hp, rfl⟩, Subtype.ext ?_⟩
    change ((χ (Submodule.Quotient.mk p) : Vt S g t) : S.Qt) = v
    rw [hχ, coe_chi_apply_mk, hpt, hkv]
  rw [eq_top_iff]
  intro x _
  have hx : χ (Submodule.Quotient.mk x) ∈ Kχ := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hx
  have hxy : x - y ∈ Wt S g t := by
    rw [← Submodule.Quotient.eq]
    exact (χ.injective hyx).symm
  have := K.add_mem hy (hWK hxy)
  rwa [add_sub_cancel] at this

theorem sub_mem_Vt_of_mem_center (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hA : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
      2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width)
    (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    {z : S.O} (hzN : z ∈ Nbar S g t) (hzc : ∀ n ∈ Nbar S g t, n * z = z * n) (q : S.Qt) :
    (z : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ Vt S g t := by
  set K := (Vt S g t).comap ((z : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) with hK
  suffices hKtop : K = ⊤ by
    have : q ∈ K := by rw [hKtop]; exact Submodule.mem_top
    exact this
  refine eq_top_of_le H C ht ht1 hVQ (fun w hw => hN z hzN w hw) fun k hk v hv => ?_
  have haQ := H.conj_mem
  set r := S.ρ k with hr
  have hrt := commute_of_mem_Rbar haQ hk
  have hk' : S.ρ k⁻¹ ∈ Rbar S g t := by rw [map_inv]; exact inv_mem hk
  have hz' : r⁻¹ * z * r ∈ Nbar S g t := by
    have h := conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hk') hzN
    rwa [map_inv, inv_inv] at h
  have hz'c : ∀ α ∈ S.Lbar g ⊓ Nbar S g t, α * (r⁻¹ * z * r) = (r⁻¹ * z * r) * α := by
    intro α hα
    have hα' : r * α * r⁻¹ ∈ Nbar S g t := conj_mem_Nbar haQ hrt hα.2
    have h1 := hzc _ hα'
    calc α * (r⁻¹ * z * r) = r⁻¹ * ((r * α * r⁻¹) * z) * r := by group
      _ = r⁻¹ * (z * (r * α * r⁻¹)) * r := by rw [h1]
      _ = (r⁻¹ * z * r) * α := by group
  have hv' : ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) :=
    (mem_clSub_Qa_mul_iff k).mp hv
  have h1 := sub_mem_Vt_of_commute_Abar H C ht ht1 hVQ hA hz' hz'c hv'
  have h2 := apply_mem_Vt_of_mem_Rbar haQ hk h1
  change (z : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t
  have e : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((((r⁻¹ * z * r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) - ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (z : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v := by
    rw [map_sub, apply_inv_apply_O]
    congr 1
    change (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((z : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)))) = _
    rw [apply_inv_apply_O, apply_inv_apply_O]
  rwa [e] at h2

end CFSG.LargeExtraspecial.S8
