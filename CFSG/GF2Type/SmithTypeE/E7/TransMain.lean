module

public import CFSG.GF2Type.SmithTypeE.E7.TrInv
public import CFSG.GF2Type.SmithTypeE.E7.TrSocle
public import CFSG.GF2Type.SmithTypeE.E7.IdMod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup Module QuadraticMap CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.SmithTypeE.DMod CFSG.RankThree.OrthogonalInvolutions CFSG.SmithD6

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Main

variable
  [IsSimpleGroup G]

theorem smithE7E33_of_model (hrank : ∀ E : Subgroup S.O, E ≤ S.Mbar →
      CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 15)
    (hw : S.width = 16) {φ : S.Qt ≃ₗ[ZMod 2] V} (ψ : S.Mbar ≃* TD6)
    (hψ : ∀ m : S.M, Phi S φ m = rhoMod (ψ ⟨S.ρ m, m, rfl⟩))
    (hcl2 : ∀ i < 75735, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = wtV i)
    (hiso : ∀ u v, polar (S.q.comp (φ.symm : V →ₗ[ZMod 2] S.Qt)) u v = fModel u v) (g : G)
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG) :
    ∃ v : G, IsConj S.z v ∧ v ∈ S.QG ∧ v ∈ S.Qa g := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  obtain ⟨xm, hxm⟩ : ∃ xm : S.M, xm = ⟨g * S.z * g⁻¹, hxM⟩ := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : TD6, a = ψ ⟨S.ρ xm, xm, rfl⟩ := ⟨_, rfl⟩
  have hρxx : S.ρ xm * S.ρ xm = 1 := by
    rw [← map_mul, hxm]
    have : ((⟨g * S.z * g⁻¹, hxM⟩ : S.M) * ⟨g * S.z * g⁻¹, hxM⟩ : S.M) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, hx2]; rfl)
    rw [this, map_one]
  have haa : a * a = 1 := by
    rw [ha, ← map_mul]
    have : (⟨S.ρ xm, xm, rfl⟩ * ⟨S.ρ xm, xm, rfl⟩ : S.Mbar) = 1 := Subtype.ext hρxx
    rw [this, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply hxQ
    rw [ha] at h
    have h1 : (⟨S.ρ xm, xm, rfl⟩ : S.Mbar) = 1 := ψ.injective (h.trans (map_one ψ).symm)
    have h2 : S.ρ xm = 1 := congrArg Subtype.val h1
    have h3 := (S.ρ_eq_one_iff xm).mp h2
    rw [hxm] at h3
    exact h3
  have hPhi : Phi S φ xm = rhoMod a := by rw [ha]; exact hψ xm
  have hint : ∀ v, Phi S φ xm (φ v) = φ (((S.ρ xm : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun v => by
    rw [Phi_apply, LinearEquiv.symm_apply_apply]
  have hcs : commSpace (rhoMod a) = (S.commQt (g * S.z * g⁻¹)).map (φ : S.Qt →ₗ[ZMod 2] V) := by
    rw [← hPhi, commSpace_eq_map_of_intertwine φ hint, S.commQt_of_mem hxM, hxm]
  have hdim : finrank (ZMod 2) (commSpace (rhoMod a)) =
      finrank (ZMod 2) (S.commQt (g * S.z * g⁻¹)) := by
    rw [hcs, LinearEquiv.finrank_map_eq]
  have hconc := involutionFacts7 a haa ha1
  by_cases hxz : IsConj S.z (g * S.z * g⁻¹ * S.z)
  ·
    have hl5 : 5 ≤ finrank (ZMod 2) (S.commQt (g * S.z * g⁻¹)) := hdim ▸ hconc.1
    exact exists_isConj_mem_Dl hrank hw hxM hxQ hl5 hxz
  ·
    have hsing := S.q_eq_zero_of_mem_commQt hxM hx2 (fixQt_eq_of_not_isConj S hxM hxz)
    have hwt : ∀ i < 75735, (S.q.comp (φ.symm : V →ₗ[ZMod 2] S.Qt)) (wtV i) = 0 := by
      intro i hi
      obtain ⟨c, hc, hcQ, hcw⟩ := hcl2 i hi
      rw [comp_apply, LinearEquiv.coe_coe, ← hcw, LinearEquiv.symm_apply_apply,
        S.q_cl_eq_zero_iff hcQ]
      obtain ⟨h, rfl⟩ := isConj_iff.mp hc
      rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
    have hsing' : ∀ v ∈ commSpace (rhoMod a),
        (S.q.comp (φ.symm : V →ₗ[ZMod 2] S.Qt)) v = 0 := by
      intro v hv
      rw [hcs] at hv
      obtain ⟨w, hw', rfl⟩ := hv
      rw [comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hsing w hw'
    refine exists_isConj_mem_Dl_of_socle hrank hw hxM hxQ hxz φ {w | ∃ i < 75735, w = wtV i}
      (fun w ⟨i, hi, hw'⟩ => hw' ▸ wtV_ne_zero hi)
      (fun w ⟨i, hi, hw'⟩ => hw' ▸ hcl2 i hi)
      {r : S.O | ∃ k : ℕ, k < 365211 ∧ tvElt k * a = a * tvElt k ∧
        r = ((ψ.symm (tvElt k) : S.Mbar) : S.O)} ?_ ?_
    ·
      rintro r ⟨k, hk, hcomm, rfl⟩
      refine ⟨(ψ.symm (tvElt k)).2, ?_⟩
      have h1 : ψ.symm a = ⟨S.ρ xm, xm, rfl⟩ := by rw [ha]; exact ψ.symm_apply_apply _
      have h2 : ψ.symm (tvElt k) * ψ.symm a = ψ.symm a * ψ.symm (tvElt k) := by
        rw [← map_mul, ← map_mul, hcomm]
      have h3 := congrArg Subtype.val h2
      rw [h1, hxm] at h3
      exact h3
    · intro N hN hle hinv
      have hle' : N ≤ commSpace (rhoMod a) := by rw [hcs]; exact hle
      obtain ⟨i, hi, hiN⟩ := hconc.2 _ hiso hwt hsing' N hN hle' (fun k hk hcomm n hn => by
        obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (ψ.symm (tvElt k)).2
        have hr := hinv ((ψ.symm (tvElt k) : S.Mbar) : S.O) ⟨k, hk, hcomm, rfl⟩ n hn
        have hψm : ψ ⟨S.ρ m, m, rfl⟩ = tvElt k := by
          have : (⟨S.ρ m, m, rfl⟩ : S.Mbar) = ψ.symm (tvElt k) := Subtype.ext hm
          rw [this, ψ.apply_symm_apply]
        have hPm : Phi S φ m = tvEquiv k := by
          rw [hψ m, hψm]
          unfold tvElt
          rw [dif_pos hk]
          exact rhoMod_tvP ⟨k, hk⟩
        rw [← hPm, Phi_apply]
        rw [← hm] at hr
        exact hr)
      exact ⟨wtV i, ⟨i, hi, rfl⟩, hiN⟩

end Main

end CFSG.GF2Type.SmithTypeE.E7
