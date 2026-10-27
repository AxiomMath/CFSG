module

public import CFSG.GF2Type.Smith1980Orth.S4CaseU
public import CFSG.GF2Type.Smith1980Orth.S4ThetaU

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable (D : S2Data S)

local notation "ρV" => D.resC

theorem exists_v (h0 : SixAt S) {x w : G} (hxM : x ∈ S.M) (hwM : w ∈ S.M) (hx : IsConj S.z x)
    (hw : IsConj S.z w) (h3 : (x * w) ^ 3 = 1) {c₀ : D.Cbar}
    (hc₀ : IsTypeA D.QV (ρV c₀) 2)
    (hxc : S.ρ ⟨x, hxM⟩ * c₀ = c₀ * S.ρ ⟨x, hxM⟩) (hwc : S.ρ ⟨w, hwM⟩ * c₀ = c₀ * S.ρ ⟨w, hwM⟩)
    (hC : ∀ q ∈ S.QG, (x * w) * q * (x * w)⁻¹ = q → ∀ (v' : G) (hv'M : v' ∈ S.M),
      IsConj S.z v' → S.ρ ⟨v', hv'M⟩ = c₀ → q * v' * q⁻¹ = v') :
    ∃ kv : G, ∃ hvM : kv * S.z * kv⁻¹ ∈ S.M, S.ρ ⟨_, hvM⟩ = c₀ ∧
      Commute x (kv * S.z * kv⁻¹) ∧ Commute (x * w) (kv * S.z * kv⁻¹) := by
  have hθM : x * w ∈ S.M := S.M.mul_mem hxM hwM
  obtain ⟨y₀, hy₀M, hy₀, hy₀ρ⟩ := D.exists_conj_of_siegel h0.six_le c₀.2 hc₀
  have hc₀1 : (c₀ : S.O) ≠ 1 := by
    intro h
    apply hc₀.2.1
    have : c₀ = 1 := Subtype.ext h
    rw [this, map_one]
  have hy₀Q : y₀ ∉ S.QG := fun hQ => hc₀1 (by rw [← hy₀ρ]; exact (S.ρ_eq_one_iff _).mpr hQ)
  have hxx : x * x = 1 := S14.SmithQ.mul_self_eq_one_of_isConj S hx
  have hww : w * w = 1 := S14.SmithQ.mul_self_eq_one_of_isConj S hw
  have hxθ : x * (x * w) * x⁻¹ = (x * w)⁻¹ := by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    rw [mul_inv_rev, hxi, hwi, ← mul_assoc, hxx, one_mul]
  have hρθ : S.ρ ⟨x * w, hθM⟩ = S.ρ ⟨x, hxM⟩ * S.ρ ⟨w, hwM⟩ := by
    rw [← map_mul]
    rfl
  have hθy : S.ρ ⟨x * w, hθM⟩ * S.ρ ⟨y₀, hy₀M⟩ = S.ρ ⟨y₀, hy₀M⟩ * S.ρ ⟨x * w, hθM⟩ := by
    rw [hρθ, hy₀ρ, mul_assoc, hwc, ← mul_assoc, hxc, mul_assoc]
  have hxy : S.ρ ⟨x, hxM⟩ * S.ρ ⟨y₀, hy₀M⟩ = S.ρ ⟨y₀, hy₀M⟩ * S.ρ ⟨x, hxM⟩ := by
    rw [hy₀ρ, hxc]
  have hC' : ∀ q ∈ S.QG, (x * w) * q * (x * w)⁻¹ = q → ∀ q' ∈ S.QG,
      (x * w) * (q' * y₀ * q'⁻¹) * (x * w)⁻¹ = q' * y₀ * q'⁻¹ →
        q * (q' * y₀ * q'⁻¹) * q⁻¹ = q' * y₀ * q'⁻¹ := by
    intro q hq hqθ q' hq' _
    have hq'M : q' ∈ S.M := S.QG_le_M hq'
    have hv'M : q' * y₀ * q'⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hq'M hy₀M) (S.M.inv_mem hq'M)
    refine hC q hq hqθ _ hv'M (hy₀.trans (isConj_iff.mpr ⟨q', rfl⟩)) ?_
    have : (⟨q' * y₀ * q'⁻¹, hv'M⟩ : S.M) = ⟨q', hq'M⟩ * ⟨y₀, hy₀M⟩ * (⟨q', hq'M⟩ : S.M)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, (S.ρ_eq_one_iff ⟨q', hq'M⟩).mpr hq', one_mul, inv_one,
      mul_one, hy₀ρ]
  obtain ⟨q₀, hq₀, hθv, hxv⟩ := h0.exists_fixed_conj hθM h3 hxM hxθ hy₀ hy₀M hy₀Q hθy hxy hC'
  obtain ⟨g₀, rfl⟩ := isConj_iff.mp hy₀
  have he : q₀ * (g₀ * S.z * g₀⁻¹) * q₀⁻¹ = (q₀ * g₀) * S.z * (q₀ * g₀)⁻¹ := by group
  have hq₀M : q₀ ∈ S.M := S.QG_le_M hq₀
  have hvM : (q₀ * g₀) * S.z * (q₀ * g₀)⁻¹ ∈ S.M := by
    rw [← he]
    exact S.M.mul_mem (S.M.mul_mem hq₀M hy₀M) (S.M.inv_mem hq₀M)
  refine ⟨q₀ * g₀, hvM, ?_, ?_, ?_⟩
  · have : (⟨_, hvM⟩ : S.M) = ⟨q₀, hq₀M⟩ * ⟨_, hy₀M⟩ * (⟨q₀, hq₀M⟩ : S.M)⁻¹ :=
      Subtype.ext (he.symm.trans rfl)
    rw [this, map_mul, map_mul, map_inv, (S.ρ_eq_one_iff ⟨q₀, hq₀M⟩).mpr hq₀, one_mul, inv_one,
      mul_one, hy₀ρ]
  · rw [← he]
    show x * _ = _ * x
    calc x * (q₀ * (g₀ * S.z * g₀⁻¹) * q₀⁻¹) =
        x * (q₀ * (g₀ * S.z * g₀⁻¹) * q₀⁻¹) * x⁻¹ * x := by group
      _ = _ := by rw [hxv]
  · rw [← he]
    show (x * w) * _ = _ * (x * w)
    calc (x * w) * (q₀ * (g₀ * S.z * g₀⁻¹) * q₀⁻¹) =
        (x * w) * (q₀ * (g₀ * S.z * g₀⁻¹) * q₀⁻¹) * (x * w)⁻¹ * (x * w) := by group
      _ = _ := by rw [hθv]

private theorem conj_conjBy (kv gw : G) :
    (gw * kv⁻¹) * (S.conjBy kv).z * (gw * kv⁻¹)⁻¹ = gw * S.z * gw⁻¹ := by
  show (gw * kv⁻¹) * (kv * S.z * kv⁻¹) * (gw * kv⁻¹)⁻¹ = gw * S.z * gw⁻¹
  group

theorem card_Qa_inf_of_types {kv gw : G} (Hv : SixAt (S.conjBy kv)) (Dv : S2Data (S.conjBy kv))
    (hwMv : gw * S.z * gw⁻¹ ∈ (S.conjBy kv).M) (hwQv : gw * S.z * gw⁻¹ ∉ (S.conjBy kv).QG) :
    (Dv.IsTInv ((S.conjBy kv).ρ ⟨_, hwMv⟩) →
      Nat.card (S.Qa kv ⊓ S.Qa gw : Subgroup G) = 2 ^ S.width) ∧
    (Dv.IsUInv ((S.conjBy kv).ρ ⟨_, hwMv⟩) →
      Nat.card (S.Qa kv ⊓ S.Qa gw : Subgroup G) = 2 ^ 4) := by
  have hM : (gw * kv⁻¹) * (S.conjBy kv).z * (gw * kv⁻¹)⁻¹ ∈ (S.conjBy kv).M := by
    rw [conj_conjBy]
    exact hwMv
  have hQ : (gw * kv⁻¹) * (S.conjBy kv).z * (gw * kv⁻¹)⁻¹ ∉ (S.conjBy kv).QG := by
    rw [conj_conjBy]
    exact hwQv
  have he : (⟨_, hM⟩ : (S.conjBy kv).M) = ⟨_, hwMv⟩ := Subtype.ext (conj_conjBy kv gw)
  have hz := Hv.e34a _ (isConj_iff.mpr ⟨_, rfl⟩) hM hQ
  have hΔ := Hv.Dl_ne_bot hM hQ
  have hQa : (S.conjBy kv).QG ⊓ (S.conjBy kv).Qa (gw * kv⁻¹) = S.Qa kv ⊓ S.Qa gw := by
    rw [S.Qa_conjBy, inv_mul_cancel_right]
    rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← he] at h
    have := Dv.card_Dl_of_isTInv hM hQ hz hΔ h
    rwa [hQa, S.width_conjBy] at this
  · rw [← he] at h
    have := Dv.card_Dl_of_isUInv hM hQ hz hΔ h
    rwa [hQa] at this

theorem exists_of_isTInv (hS : ∀ g : G, SixAt (S.conjBy g)) (h0 : SixAt S) {x gw ky : G}
    (hx : IsConj S.z x) (hxM : x ∈ S.M) (hwM : gw * S.z * gw⁻¹ ∈ S.M)
    (hwy : Commute (gw * S.z * gw⁻¹) (ky * S.z * ky⁻¹))
    (h3 : orderOf (x * (gw * S.z * gw⁻¹)) = 3) (h3' : orderOf (S.z * (ky * S.z * ky⁻¹)) = 3)
    (hwQ : gw * S.z * gw⁻¹ ∉ S.QG)
    (hxT : D.IsTInv (S.ρ ⟨x, hxM⟩)) (hwT : D.IsTInv (S.ρ ⟨_, hwM⟩)) :
    ∃ v, IsConj S.z v ∧ Commute x v ∧ Commute v (ky * S.z * ky⁻¹) := by
  have hw : IsConj S.z (gw * S.z * gw⁻¹) := isConj_iff.mpr ⟨gw, rfl⟩
  have hy : IsConj S.z (ky * S.z * ky⁻¹) := isConj_iff.mpr ⟨ky, rfl⟩
  have h3p : (x * (gw * S.z * gw⁻¹)) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have hρne := rho_ne_of_orderOf_eq_three hx hxM hwM h3
  obtain ⟨c₀, hc₀⟩ := D.exists_siegel h0.six_le
  obtain ⟨kv, hvM, hvρ, hxv, hθv⟩ := D.exists_v h0 hxM hwM hx hw h3p hc₀
    (D.comm_of_isTInv_of_mem_Cbar hxT c₀.2) (D.comm_of_isTInv_of_mem_Cbar hwT c₀.2)
    (fun q hq hqθ v' hv'M _ _ => by
      have hqθ' : (x * (gw * S.z * gw⁻¹)) * q = q * (x * (gw * S.z * gw⁻¹)) := by
        calc (x * (gw * S.z * gw⁻¹)) * q =
            (x * (gw * S.z * gw⁻¹)) * q * (x * (gw * S.z * gw⁻¹))⁻¹ *
              (x * (gw * S.z * gw⁻¹)) := by group
          _ = q * (x * (gw * S.z * gw⁻¹)) := by rw [hqθ]
      rcases D.eq_one_or_z_of_commute_of_isTInv hxM hwM hxT hwT hρne hq hqθ' with rfl | rfl
      · group
      · rw [← S.z_comm hv'M, mul_inv_cancel_right])
  have hvC : S.ρ ⟨_, hvM⟩ ∈ D.Cbar := hvρ ▸ c₀.2
  have hvU : IsTypeA D.QV (ρV ⟨_, hvC⟩) 2 := by
    have : (⟨_, hvC⟩ : D.Cbar) = c₀ := Subtype.ext hvρ
    rw [this]
    exact hc₀
  have hxx : x * x = 1 := S14.SmithQ.mul_self_eq_one_of_isConj S hx
  have hwv : Commute (gw * S.z * gw⁻¹) (kv * S.z * kv⁻¹) := by
    have : gw * S.z * gw⁻¹ = x * (x * (gw * S.z * gw⁻¹)) := by rw [← mul_assoc, hxx, one_mul]
    rw [this]
    exact hxv.mul_left hθv
  have Hv := hS kv
  obtain ⟨Dv⟩ := Hv.s2
  have hxMv : x ∈ (S.conjBy kv).M := mem_centralizer_singleton_iff.mpr hxv.eq
  have hwMv : gw * S.z * gw⁻¹ ∈ (S.conjBy kv).M := mem_centralizer_singleton_iff.mpr hwv.eq
  have hxv' : IsConj (S.conjBy kv).z x := (S.isConj_conjBy_z_iff kv).mpr hx
  have hwv' : IsConj (S.conjBy kv).z (gw * S.z * gw⁻¹) := (S.isConj_conjBy_z_iff kv).mpr hw
  obtain ⟨-, hwQv, htv⟩ := Dv.types_of_orderOf_eq_three (Hv.types Dv) hxv' hwv' hxMv hwMv h3
  have hUv : Dv.IsUInv ((S.conjBy kv).ρ ⟨_, hwMv⟩) := by
    rcases htv with ⟨hxTv, hwTv⟩ | ⟨-, hwUv⟩
    · exfalso
      refine D.false_of_isTInv_at h0 hxM hwM hxT hwT h3p hvM hvC hvU hθv (fun q hq hqθ => ?_)
      exact Dv.eq_one_or_z_of_commute_of_isTInv hxMv hwMv hxTv hwTv
        (rho_ne_of_orderOf_eq_three hxv' hxMv hwMv h3) hq hqθ
    · exact hwUv
  have hcv := (card_Qa_inf_of_types Hv Dv hwMv hwQv).2 hUv
  have hwz := h0.e34a _ hw hwM hwQ
  have hcz := D.card_Dl_of_isTInv hwM hwQ hwz (h0.Dl_ne_bot hwM hwQ) hwT
  have hne : Nat.card (S.QG ⊓ S.Qa gw : Subgroup G) ≠ Nat.card (S.Qa kv ⊓ S.Qa gw : Subgroup G) := by
    rw [hcz, hcv]
    have := h0.six_le
    intro h
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  have hzw : Commute S.z (gw * S.z * gw⁻¹) := (mem_centralizer_singleton_iff.mp hwM).symm
  have h3vy := SixAt.orderOf_ne_three_of_card_ne hS hzw hwy hwv h3' hne
  exact h0.exists_of_not_three hx hw hy (isConj_iff.mpr ⟨kv, rfl⟩) hwy hwv hxv.symm h3vy

private theorem eichler_apply_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {e f v : V} (he : Q e = 0) (hef : polar Q e f = 0)
    (h1 : polar Q v e = 0) (h2 : polar Q v f = 0) : eichler Q e f v = v := by
  rw [eichler_apply_zmod2 he hef, h1, h2, zero_smul, add_zero, mul_zero, add_zero, zero_smul,
    add_zero]

private theorem commute_of_fix (h0 : SixAt S) {θ : G} (hθM : θ ∈ S.M)
    (hθC : S.ρ ⟨θ, hθM⟩ ∈ D.Cbar) {c₀ : D.Cbar}
    (hfix : ∀ v, ρV ⟨_, hθC⟩ v = v → ρV c₀ v = v) {q : G} (hq : q ∈ S.QG)
    (hqθ : θ * q * θ⁻¹ = q) {v' : G} (hv'M : v' ∈ S.M) (hv' : IsConj S.z v')
    (hv'ρ : S.ρ ⟨v', hv'M⟩ = c₀) (hc₀ : (c₀ : S.O) ≠ 1) : q * v' * q⁻¹ = v' := by
  obtain ⟨g', rfl⟩ := isConj_iff.mp hv'
  have hv'Q : g' * S.z * g'⁻¹ ∉ S.QG := fun hQ =>
    hc₀ (by rw [← hv'ρ]; exact (S.ρ_eq_one_iff _).mpr hQ)
  have hvz := h0.e34a _ (isConj_iff.mpr ⟨g', rfl⟩) hv'M hv'Q
  have hfixv := SMK.fixQt_eq_of_not_isConj S hv'M hvz
  obtain ⟨⟨a, b⟩, hab⟩ := D.coord.surjective (S.cl q)
  have hθq : ((S.ρ ⟨θ, hθM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, b)) = D.coord (a, b) := by
    rw [hab, S.ρ_cl ⟨θ, hθM⟩ hq]
    exact congrArg S.cl hqθ
  obtain ⟨ha, hb⟩ := (D.coord_mem_fixSpace_Cbar_iff ⟨_, hθC⟩ a b).mp (mem_fixSpace.mpr hθq)
  have hmem : S.cl q ∈ S.fixQt (g' * S.z * g'⁻¹) := by
    rw [S.fixQt_of_mem hv'M, ← hab]
    have : D.coord (a, b) ∈ fixSpace ((c₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      (D.coord_mem_fixSpace_Cbar_iff c₀ a b).mpr
        ⟨mem_fixSpace.mpr (hfix a (mem_fixSpace.mp ha)),
          mem_fixSpace.mpr (hfix b (mem_fixSpace.mp hb))⟩
    rwa [← hv'ρ] at this
  rw [hfixv] at hmem
  obtain ⟨u, hu, huQ, hcl⟩ := S.mem_clSub_iff.mp hmem
  have hux : u * (g' * S.z * g'⁻¹) = (g' * S.z * g'⁻¹) * u := mem_centralizer_singleton_iff.mp hu.2
  have hzx : S.z * (g' * S.z * g'⁻¹) = (g' * S.z * g'⁻¹) * S.z := (S.z_comm hv'M).symm
  rcases (S.cl_eq_cl_iff huQ hq).mp hcl with e | e
  · rw [e, hux, mul_inv_cancel_right]
  · rw [e]
    calc u * S.z * (g' * S.z * g'⁻¹) * (u * S.z)⁻¹ =
        u * (S.z * (g' * S.z * g'⁻¹) * S.z⁻¹) * u⁻¹ := by group
      _ = u * (g' * S.z * g'⁻¹) * u⁻¹ := by rw [hzx, mul_inv_cancel_right]
      _ = g' * S.z * g'⁻¹ := by rw [hux, mul_inv_cancel_right]

theorem exists_of_isUInv (hS : ∀ g : G, SixAt (S.conjBy g)) (h0 : SixAt S) {x gw ky : G}
    (hx : IsConj S.z x) (hxM : x ∈ S.M) (hwM : gw * S.z * gw⁻¹ ∈ S.M)
    (hwy : Commute (gw * S.z * gw⁻¹) (ky * S.z * ky⁻¹))
    (h3 : orderOf (x * (gw * S.z * gw⁻¹)) = 3) (h3' : orderOf (S.z * (ky * S.z * ky⁻¹)) = 3)
    (hwQ : gw * S.z * gw⁻¹ ∉ S.QG)
    (hxU : D.IsUInv (S.ρ ⟨x, hxM⟩)) (hwU : D.IsUInv (S.ρ ⟨_, hwM⟩)) :
    ∃ v, IsConj S.z v ∧ Commute x v ∧ Commute v (ky * S.z * ky⁻¹) := by
  obtain ⟨hxC, hxA⟩ := hxU
  obtain ⟨hwC, hwA⟩ := hwU
  have hw : IsConj S.z (gw * S.z * gw⁻¹) := isConj_iff.mpr ⟨gw, rfl⟩
  have hy : IsConj S.z (ky * S.z * ky⁻¹) := isConj_iff.mpr ⟨ky, rfl⟩
  have hθM : x * (gw * S.z * gw⁻¹) ∈ S.M := S.M.mul_mem hxM hwM
  have hρθ : S.ρ ⟨_, hθM⟩ = S.ρ ⟨x, hxM⟩ * S.ρ ⟨_, hwM⟩ := by
    rw [← map_mul]
    rfl
  have hθC : S.ρ ⟨_, hθM⟩ ∈ D.Cbar := by
    rw [hρθ]
    exact D.Cbar.mul_mem hxC hwC
  have hθρV : ρV ⟨_, hθC⟩ = ρV ⟨_, hxC⟩ * ρV ⟨_, hwC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hρθ
  have hθ3 : (x * (gw * S.z * gw⁻¹)) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have h3V : (ρV ⟨_, hxC⟩ * ρV ⟨_, hwC⟩) ^ 3 = 1 := by
    rw [← hθρV, ← map_pow]
    have : (⟨_, hθC⟩ : D.Cbar) ^ 3 = 1 := Subtype.ext (by
      show S.ρ ⟨_, hθM⟩ ^ 3 = 1
      rw [← map_pow]
      have : (⟨_, hθM⟩ : S.M) ^ 3 = 1 := Subtype.ext hθ3
      rw [this, map_one])
    rw [this, map_one]
  have h1V : ρV ⟨_, hxC⟩ * ρV ⟨_, hwC⟩ ≠ 1 := by
    rw [← hθρV]
    intro h
    have h1 : (⟨_, hθC⟩ : D.Cbar) = 1 := D.resC_injective (h.trans (map_one _).symm)
    have hQ := (S.ρ_eq_one_iff _).mp (congrArg Subtype.val h1)
    have h4 := orderOf_dvd_of_pow_eq_one (S.pow_four_eq_one hQ)
    rw [h3] at h4
    norm_num at h4
  obtain ⟨hdim, e, f, he, hf, hef, hli, hσρ, hσρ', hfixθ, hfpf, -, -⟩ :=
    exists_siegel_of_pow_three D.QV_nondegenerate hxA hwA h3V h1V
  obtain ⟨hσA, hσP⟩ := eichler_isTypeA D.QV_nondegenerate he hef hli hf
  obtain ⟨c₀, hc₀⟩ := D.exists_Cbar_resC_eq_eichler e f
  have hc₀A : IsTypeA D.QV (ρV c₀) 2 := hc₀ ▸ hσA
  have hc₀1 : (c₀ : S.O) ≠ 1 := by
    intro h
    apply hc₀A.2.1
    have : c₀ = 1 := Subtype.ext h
    rw [this, map_one]
  have hcomm : ∀ {a : S.O} (ha : a ∈ D.Cbar),
      eichler D.QV e f * ρV ⟨a, ha⟩ = ρV ⟨a, ha⟩ * eichler D.QV e f → a * c₀ = c₀ * a := by
    intro a ha h
    rw [← hc₀, ← map_mul, ← map_mul] at h
    exact (congrArg Subtype.val (D.resC_injective h)).symm
  have hfixσ : ∀ v, ρV ⟨_, hθC⟩ v = v → ρV c₀ v = v := by
    intro v hv
    rw [hθρV] at hv
    obtain ⟨h1, h2⟩ := hfixθ v hv
    rw [hc₀]
    exact eichler_apply_eq he hef h1 h2
  obtain ⟨kv, hvM, hvρ, hxv, hθv⟩ := D.exists_v h0 hxM hwM hx hw hθ3 hc₀A (hcomm hxC hσρ)
    (hcomm hwC hσρ') (fun q hq hqθ v' hv'M hv' hv'ρ =>
      D.commute_of_fix h0 hθM hθC hfixσ hq hqθ hv'M hv' hv'ρ hc₀1)
  have hvC : S.ρ ⟨_, hvM⟩ ∈ D.Cbar := hvρ ▸ c₀.2
  have hvc : (⟨_, hvC⟩ : D.Cbar) = c₀ := Subtype.ext hvρ
  have hvU : IsTypeA D.QV (ρV ⟨_, hvC⟩) 2 := by
    rw [hvc]
    exact hc₀A
  have hxx : x * x = 1 := S14.SmithQ.mul_self_eq_one_of_isConj S hx
  have hwv : Commute (gw * S.z * gw⁻¹) (kv * S.z * kv⁻¹) := by
    have : gw * S.z * gw⁻¹ = x * (x * (gw * S.z * gw⁻¹)) := by rw [← mul_assoc, hxx, one_mul]
    rw [this]
    exact hxv.mul_left hθv
  have Hv := hS kv
  obtain ⟨Dv⟩ := Hv.s2
  have hxMv : x ∈ (S.conjBy kv).M := mem_centralizer_singleton_iff.mpr hxv.eq
  have hwMv : gw * S.z * gw⁻¹ ∈ (S.conjBy kv).M := mem_centralizer_singleton_iff.mpr hwv.eq
  have hxv' : IsConj (S.conjBy kv).z x := (S.isConj_conjBy_z_iff kv).mpr hx
  have hwv' : IsConj (S.conjBy kv).z (gw * S.z * gw⁻¹) := (S.isConj_conjBy_z_iff kv).mpr hw
  obtain ⟨-, hwQv, htv⟩ := Dv.types_of_orderOf_eq_three (Hv.types Dv) hxv' hwv' hxMv hwMv h3
  have hTv : Dv.IsTInv ((S.conjBy kv).ρ ⟨_, hwMv⟩) := by
    rcases htv with ⟨-, hwTv⟩ | ⟨hxUv, hwUv⟩
    · exact hwTv
    · exfalso
      have hzMv : S.z ∈ (S.conjBy kv).M :=
        mem_centralizer_singleton_iff.mpr (S.z_comm hvM).symm
      have hzθ : S.z * (x * (gw * S.z * gw⁻¹)) = (x * (gw * S.z * gw⁻¹)) * S.z :=
        (S.z_comm hθM).symm
      have hUv := Dv.card_centralizer_theta_ge hxMv hwMv hxUv hwUv h3 hzMv S.z_sq hzθ
      rw [S.width_conjBy] at hUv
      have hσv : ρV ⟨_, hvC⟩ = eichler D.QV e f := by rw [hvc, hc₀]
      refine D.false_of_isUInv_at h0 hvM hvC hvU hθM hθC hθ3 hθv ?_ ?_ ?_ hUv
      · intro v hv hθv'
        rw [hσv, hσP] at hv
        rw [hθρV] at hθv'
        exact hfpf v hv hθv'
      · intro v hv
        rw [mem_fixSpace] at hv ⊢
        rw [hvc]
        exact hfixσ v hv
      · rw [hθρV]
        exact hdim
  have hcv := (card_Qa_inf_of_types Hv Dv hwMv hwQv).1 hTv
  have hwz := h0.e34a _ hw hwM hwQ
  have hcz := D.card_Dl_of_isUInv hwM hwQ hwz (h0.Dl_ne_bot hwM hwQ) ⟨hwC, hwA⟩
  have hne : Nat.card (S.QG ⊓ S.Qa gw : Subgroup G) ≠
      Nat.card (S.Qa kv ⊓ S.Qa gw : Subgroup G) := by
    rw [hcz, hcv]
    have := h0.six_le
    intro h
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  have hzw : Commute S.z (gw * S.z * gw⁻¹) := (mem_centralizer_singleton_iff.mp hwM).symm
  have h3vy := SixAt.orderOf_ne_three_of_card_ne hS hzw hwy hwv h3' hne
  exact h0.exists_of_not_three hx hw hy (isConj_iff.mpr ⟨kv, rfl⟩) hwy hwv hxv.symm h3vy

end S2Data

theorem oe421Three_of_sixAt {S : Setting G} (hS : ∀ g : G, SixAt (S.conjBy g)) (h0 : SixAt S) :
    OE421Three S := by
  intro x w y hx hw hy hxz hzw hwy _ _ _ h3 h3'
  obtain ⟨D⟩ := h0.s2
  have hxM : x ∈ S.M := mem_centralizer_singleton_iff.mpr hxz.eq
  have hwM : w ∈ S.M := mem_centralizer_singleton_iff.mpr hzw.symm.eq
  obtain ⟨gw, rfl⟩ := isConj_iff.mp hw
  obtain ⟨ky, rfl⟩ := isConj_iff.mp hy
  obtain ⟨-, hwQ, htypes⟩ := D.types_of_orderOf_eq_three (h0.types D) hx hw hxM hwM h3
  rcases htypes with ⟨hxT, hwT⟩ | ⟨hxU, hwU⟩
  · exact D.exists_of_isTInv hS h0 hx hxM hwM hwy h3 h3' hwQ hxT hwT
  · exact D.exists_of_isUInv hS h0 hx hxM hwM hwy h3 h3' hwQ hxU hwU

end CFSG.GF2Type.Smith1980Orth
