module

public import CFSG.GF2Type.SmithTypeE.E8.TrInv
public import CFSG.GF2Type.SmithTypeE.E8.TrSocle

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup Module QuadraticMap CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

variable {G : Type} [Group G] [Finite G]

@[expose] def TwoRankMbar8 (S : Setting G) : Prop :=
  ∀ E : Subgroup S.O, E ≤ S.Mbar → CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 27

section Main

variable {S : Setting G}
  [IsSimpleGroup G]

theorem commSp_eq_map_commQt {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}
    {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))} (hE : SmithE8Equiv S φ ψ) {x : G}
    (hx : x ∈ S.M) :
    commSp (ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩) = (S.commQt x).map (φ : S.Qt →ₗ[ZMod 2] _) := by
  have hint : ∀ v : S.Qt, e7Rep56 (ZMod 2) (ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩) (φ v) =
      φ (((S.ρ ⟨x, hx⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun v =>
    (hE ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ v).symm
  ext v
  rw [Submodule.mem_map, mem_commSp, S.commQt_of_mem hx]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨((S.ρ ⟨x, hx⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (φ.symm y) - φ.symm y,
      CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.2 ⟨φ.symm y, rfl⟩, ?_⟩
    have h := hint (φ.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [LinearEquiv.coe_coe, map_sub, ← h, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.1 hw
    refine ⟨φ y, ?_⟩
    rw [hint, LinearEquiv.coe_coe, map_sub]

theorem smithE8E33_of_model (hrank : TwoRankMbar8 S) (hw : S.width = 28)
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)} {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))}
    (hE : SmithE8Equiv S φ ψ)
    (hcl2 : ∀ w ∈ weightVec, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = w)
    (hiso : ∀ u v, polar (S.q.comp (φ.symm : (Fin e7Data.d →₀ ZMod 2) →ₗ[ZMod 2] S.Qt)) u v =
      F.ff u v) (g : G)
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG) :
    ∃ v : G, IsConj S.z v ∧ v ∈ S.QG ∧ v ∈ S.Qa g := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  obtain ⟨xm, hxm⟩ : ∃ xm : S.M, xm = ⟨g * S.z * g⁻¹, hxM⟩ := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ↥(adjointGroup .E7 (ZMod 2)), a = ψ ⟨S.ρ xm, xm, rfl⟩ := ⟨_, rfl⟩
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
  have hcs : commSp a = (S.commQt (g * S.z * g⁻¹)).map (φ : S.Qt →ₗ[ZMod 2] _) := by
    rw [ha, hxm]
    exact commSp_eq_map_commQt hE hxM
  have hdim : finrank (ZMod 2) (commSp a) = finrank (ZMod 2) (S.commQt (g * S.z * g⁻¹)) := by
    rw [hcs, LinearEquiv.finrank_map_eq]
  have hconc := involutionFacts8 a haa ha1
  by_cases hxz : IsConj S.z (g * S.z * g⁻¹ * S.z)
  ·
    have hl5 : 5 ≤ finrank (ZMod 2) (S.commQt (g * S.z * g⁻¹)) := hdim ▸ hconc.five_le
    exact exists_isConj_mem_Dl hrank hw hxM hxQ hl5 hxz
  ·
    have hsing := S.q_eq_zero_of_mem_commQt hxM hx2 (E7.fixQt_eq_of_not_isConj S hxM hxz)
    have hwt : ∀ w ∈ weightVec,
        (S.q.comp (φ.symm : (Fin e7Data.d →₀ ZMod 2) →ₗ[ZMod 2] S.Qt)) w = 0 := by
      intro w hw'
      obtain ⟨c, hc, hcQ, hcw⟩ := hcl2 w hw'
      rw [comp_apply, LinearEquiv.coe_coe, ← hcw, LinearEquiv.symm_apply_apply,
        S.q_cl_eq_zero_iff hcQ]
      obtain ⟨h, rfl⟩ := isConj_iff.mp hc
      rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
    have hsing' : ∀ v ∈ commSp a,
        (S.q.comp (φ.symm : (Fin e7Data.d →₀ ZMod 2) →ₗ[ZMod 2] S.Qt)) v = 0 := by
      intro v hv
      rw [hcs] at hv
      obtain ⟨w, hw', rfl⟩ := hv
      rw [comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hsing w hw'
    have hsoc := hconc.socle_of_ts _ hiso hwt hsing'
    refine exists_isConj_mem_Dl_of_socle hrank hw hxM hxQ hxz φ weightVec
      (fun w hw' => F.wt_ne_zero_core hw') hcl2
      {r : S.O | ∃ c : ↥(adjointGroup .E7 (ZMod 2)), c * a = a * c ∧
        r = ((ψ.symm c : S.Mbar) : S.O)} ?_ ?_
    ·
      rintro r ⟨c, hc, rfl⟩
      refine ⟨(ψ.symm c).2, ?_⟩
      have h1 : ψ.symm a = ⟨S.ρ xm, xm, rfl⟩ := by rw [ha]; exact ψ.symm_apply_apply _
      have h2 : ψ.symm c * ψ.symm a = ψ.symm a * ψ.symm c := by
        rw [← map_mul, ← map_mul, hc]
      have h3 := congrArg Subtype.val h2
      rw [h1, hxm] at h3
      exact h3
    · intro N hN hle hinv
      have hle' : N ≤ commSp a := by rw [hcs]; exact hle
      exact hsoc N hN hle' (fun c hc n hn => by
        have hr := hinv _ ⟨c, hc, rfl⟩ n hn
        have h4 : e7Rep56 (ZMod 2) c n =
            φ ((((ψ.symm c : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (φ.symm n)) := by
          have h5 := hE (ψ.symm c) (φ.symm n)
          rw [MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h5
          exact h5.symm
        rw [h4]
        exact hr)

end Main

end CFSG.GF2Type.SmithTypeE.E8
