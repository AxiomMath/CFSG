module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S3bTenB
public import CFSG.LargeExtraspecial.S4FiveA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem clSub_eq_of_cl_eq {g₁ g₂ : G} (h₁ : g₁ * S.z * g₁⁻¹ ∈ S.QG)
    (hz₁ : g₁ * S.z * g₁⁻¹ ≠ S.z) (h₂ : g₂ * S.z * g₂⁻¹ ∈ S.QG)
    (he : S.cl (g₁ * S.z * g₁⁻¹) = S.cl (g₂ * S.z * g₂⁻¹)) :
    S.clSub (S.QG ⊓ S.Qa g₂) = S.clSub (S.QG ⊓ S.Qa g₁) := by
  rcases (S.cl_eq_cl_iff h₁ h₂).mp he with e | e
  · rw [S.Qa_eq_of_conj_eq e]
  · obtain ⟨q, hq, hqa⟩ := S.exists_conj_eq_mul_z h₁ (conj_z_ne_one S g₁) hz₁
    have e2 : g₂ * S.z * g₂⁻¹ = (q * g₁) * S.z * (q * g₁)⁻¹ := by
      rw [e, ← hqa]; group
    rw [S.Qa_eq_of_conj_eq e2, S.Qa_mul g₁ q]
    have hqM : q ∈ S.M := S.QG_le_M hq
    have hmap : S.QG ⊓ (S.Qa g₁).map (MulAut.conj q).toMonoidHom =
        (S.QG ⊓ S.Qa g₁).map (MulAut.conj ((⟨q, hqM⟩ : S.M) : G)).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj q).injective, S.QG_map_conj hqM]
    rw [hmap]
    ext v
    rw [mem_clSub_map_conj_iff ⟨q, hqM⟩ inf_le_left]
    have hρ : S.ρ ⟨q, hqM⟩ = 1 := (S.ρ_eq_one_iff _).mpr hq
    rw [hρ, inv_one]
    rfl

theorem mem_Qa_iff_cl_mem {g' : G} (hbQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hbz : g' * S.z * g'⁻¹ ≠ S.z) {c : G} (hc : c ∈ S.QG) :
    c ∈ S.Qa g' ↔ S.cl c ∈ S.clSub (S.QG ⊓ S.Qa g') := by
  constructor
  · intro h
    exact S.cl_mem_clSub ⟨hc, h⟩ hc
  · intro h
    obtain ⟨x, hx, hxQ, hxc⟩ := S.mem_clSub_iff.mp h
    rcases (S.cl_eq_cl_iff hxQ hc).mp hxc with e | e
    · rw [e]; exact hx.2
    · rw [e]; exact mul_mem hx.2 (S.z_mem_Qa hbQ hbz)

theorem exists_Lbar_apply_eq_add {g' : G} (hbQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hbz : g' * S.z * g'⁻¹ ≠ S.z) {c : G} (hc : c ∈ S.QG ⊓ S.Qa g')
    (hcb : S.cl c ∉ (ZMod 2) ∙ S.cl (g' * S.z * g'⁻¹)) :
    ∃ l ∈ S.Lbar g', (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl c) =
      S.cl c + S.cl (g' * S.z * g'⁻¹) := by
  set T := S.conjBy g' with hT
  have hTz : T.z = g' * S.z * g'⁻¹ := rfl
  have hTQ : T.QG = S.Qa g' := rfl
  have hzT : S.z ∈ T.QG := S.z_mem_Qa hbQ hbz
  have hcT : c ∈ T.QG := hc.2
  have hc0 : S.cl c ≠ 0 := fun h => hcb (by rw [h]; exact zero_mem _)
  have hcb' : S.cl c ≠ S.cl (g' * S.z * g'⁻¹) := fun h =>
    hcb (by rw [h]; exact Submodule.mem_span_singleton_self _)
  have hc1 : c ≠ 1 := fun h => hc0 (by rw [h, S.cl_one])
  have hcz : c ≠ S.z := fun h => hc0 (by rw [h, S.cl_z])
  have hcb2 : c ≠ T.z := fun h => hcb' (by rw [h, hTz])
  have hzc : S.z ≠ c * T.z := fun h => hcb' (by
    have e : c = S.z * (T.z)⁻¹ := by rw [h]; group
    rw [e, hTz, S.cl_mul S.z_mem_QG (S.QG.inv_mem hbQ), S.cl_z, zero_add, S.cl_inv hbQ])
  obtain ⟨u, hu, huz, huc⟩ := T.exists_conj_eq_mul_z_of_commute hcT hzT hc1 hcb2 hcz.symm hzc
  have huM : u ∈ S.M := S.mem_M_iff.mpr huz
  have huL : (⟨u, huM⟩ : S.M) ∈ (S.L0 g').subgroupOf S.M := by
    rw [mem_subgroupOf]
    exact ⟨hu, huM⟩
  refine ⟨S.ρ ⟨u, huM⟩, ⟨_, huL, rfl⟩, ?_⟩
  rw [S.ρ_cl ⟨u, huM⟩ hc.1]
  change S.cl (u * c * u⁻¹) = _
  rw [huc, hTz, S.cl_mul hc.1 hbQ]

theorem isWeaklyClosed_Lbar {g : G} (C : Cons311 S g) :
    IsWeaklyClosedInNormalizer ((S.Lbar g).subgroupOf S.Mbar) := by
  intro x hx
  have hLM : S.Lbar g ≤ S.Mbar := S.Lbar_le_Mbar g
  obtain ⟨h, hh⟩ : ∃ h : S.M, S.ρ h = (x : S.O) := MonoidHom.mem_range.mp x.2
  have hmem : ∀ y : S.Mbar, y ∈ ((S.Lbar g).subgroupOf S.Mbar).map (MulAut.conj x).toMonoidHom ↔
      (y : S.O) ∈ S.Lbar ((h : G) * g) := by
    intro y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_subgroupOf, mem_Lbar_mul_iff S h g,
      hh]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hle : S.Lbar ((h : G) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    intro y hy
    have hyM : y ∈ S.Mbar := S.Lbar_le_Mbar _ hy
    have hyN := hx ((hmem ⟨y, hyM⟩).mpr hy)
    rw [mem_normalizer_iff] at hyN ⊢
    intro w
    constructor
    · intro hw
      exact mem_subgroupOf.mp ((hyN ⟨w, hLM hw⟩).mp (mem_subgroupOf.mpr hw))
    · intro hw
      have hwM : w ∈ S.Mbar := by
        have e : w = y⁻¹ * (y * w * y⁻¹) * y := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hyM) (hLM hw)) hyM
      exact mem_subgroupOf.mp ((hyN ⟨w, hwM⟩).mpr (mem_subgroupOf.mpr hw))
  have heq := C.weaklyClosed (h : G) h.2 hle
  ext y
  rw [hmem, heq, mem_subgroupOf]

theorem Lbar_eq_of_le_pGroup {g : G} (C : Cons311 S g) {T : Subgroup S.O} (hT : IsPGroup 2 T)
    (hLT : S.Lbar g ≤ T) {h : S.M} (hLT' : S.Lbar ((h : G) * g) ≤ T) :
    S.Lbar ((h : G) * g) = S.Lbar g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : S.Lbar g ≤ S.Mbar := S.Lbar_le_Mbar g
  have hT' : IsPGroup 2 (T.subgroupOf S.Mbar) := hT.comap_of_injective _ (subtype_injective _)
  have hN := le_normalizer_of_isWeaklyClosed (isWeaklyClosed_Lbar C) hT'
    (fun x hx => mem_subgroupOf.mpr (hLT (mem_subgroupOf.mp hx)))
  refine C.weaklyClosed (h : G) h.2 fun y hy => ?_
  have hyM : y ∈ S.Mbar := S.Lbar_le_Mbar _ hy
  have hyN := hN (mem_subgroupOf.mpr (hLT' hy) : (⟨y, hyM⟩ : S.Mbar) ∈ T.subgroupOf S.Mbar)
  rw [mem_normalizer_iff] at hyN ⊢
  intro w
  constructor
  · intro hw
    exact mem_subgroupOf.mp ((hyN ⟨w, hLM hw⟩).mp (mem_subgroupOf.mpr hw))
  · intro hw
    have hwM : w ∈ S.Mbar := by
      have e : w = y⁻¹ * (y * w * y⁻¹) * y := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hyM) (hLM hw)) hyM
    exact mem_subgroupOf.mp ((hyN ⟨w, hwM⟩).mpr (mem_subgroupOf.mpr hw))

theorem exists_Rbar_Lbar_eq {g : G} (H : Hyp4 S g) (C : Cons311 S g) {τ : S.O}
    (hτ : τ ∈ S.Lbar g) {h : S.M} (hτh : τ ∈ S.Lbar ((h : G) * g)) :
    ∃ m : S.M, S.ρ m ∈ Rbar S g τ ∧ S.Lbar ((h : G) * g) = S.Lbar ((m : G) * g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := Rbar S g τ with hR
  have hLR : S.Lbar g ≤ R := Lbar_le_Rbar hτ
  have hLR' : S.Lbar ((h : G) * g) ≤ R := Lbar_mul_le_Rbar hτh
  have hA : IsPGroup 2 ((S.Lbar g).subgroupOf R) :=
    (isPGroup_Lbar S H.conj_mem).comap_of_injective _ (subtype_injective _)
  have hB : IsPGroup 2 ((S.Lbar ((h : G) * g)).subgroupOf R) :=
    (isPGroup_Lbar S (conj_mem_QG' S h.2 H.conj_mem)).comap_of_injective _ (subtype_injective _)
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  obtain ⟨P', hBP⟩ := hB.exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R P P'
  obtain ⟨m, hm⟩ : ∃ m : S.M, S.ρ m = (r : S.O) := MonoidHom.mem_range.mp (Rbar_le_Mbar r.2)
  refine ⟨m, hm ▸ r.2, ?_⟩
  set T : Subgroup S.O := (P : Subgroup R).map R.subtype with hT
  have hTp : IsPGroup 2 T := P.isPGroup'.map _
  have hLT : S.Lbar g ≤ T := fun x hx => ⟨⟨x, hLR hx⟩, hAP (mem_subgroupOf.mpr hx), rfl⟩
  have hLT' : S.Lbar (((m⁻¹ * h : S.M) : G) * g) ≤ T := by
    intro x hx
    rw [Subgroup.coe_mul, mul_assoc, mem_Lbar_mul_iff S m⁻¹, map_inv, inv_inv] at hx
    have hy : S.ρ m * x * (S.ρ m)⁻¹ ∈ S.Lbar ((h : G) * g) := by simpa [mul_assoc] using hx
    have hy' : (⟨S.ρ m * x * (S.ρ m)⁻¹, hLR' hy⟩ : R) ∈ (P' : Subgroup R) :=
      hBP (mem_subgroupOf.mpr hy)
    rw [← hr, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply] at hy'
    refine ⟨_, hy', ?_⟩
    simp [← hm, mul_assoc]
  have heq := Lbar_eq_of_le_pGroup C hTp hLT hLT'
  rw [Subgroup.coe_mul, mul_assoc, Lbar_mul S m⁻¹] at heq
  rw [Lbar_mul S m, ← heq, map_inv, Subgroup.map_map]
  ext x
  simp [mul_assoc]

theorem exists_Rbar_apply_eq {g : G} (H : Hyp4 S g) (C : Cons311 S g) {τ : S.O}
    (hτ : τ ∈ S.Lbar g) {h : S.M} (hτh : τ ∈ S.Lbar ((h : G) * g)) :
    ∃ r ∈ Rbar S g τ, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
  obtain ⟨m, hmR, hL⟩ := exists_Rbar_Lbar_eq H C hτ hτh
  refine ⟨S.ρ m, hmR, ?_⟩
  rw [ρ_cl_conj_z S m H.conj_mem]
  have h1 := (H.mul h).fixSub_eq
  have h2 := (H.mul m).fixSub_eq
  rw [hL, h2] at h1
  have hmem : S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∈
      (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    rw [← h1]; exact Submodule.mem_span_singleton_self _
  rcases mem_span_cl_iff.mp hmem with h0 | h0
  · exact absurd h0 (cl_conj_z_ne_zero S (conj_mem_QG' S m.2 H.conj_mem)
      (conj_ne_z' S m.2 H.conj_ne))
  · exact h0

end CFSG.LargeExtraspecial.S13
