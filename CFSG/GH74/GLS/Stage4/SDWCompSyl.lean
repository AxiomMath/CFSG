module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.QuasiDihedralFusion.Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem sdw_exists_sylow_cent {X : Type} [Group X] [Finite X]
    (hQD : CFSG.QuasiDihedralFusion.IsQDGroup X) {z : X}
    (hz : orderOf z = 2) {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hQz : ∀ q ∈ Q, q * z = z * q) :
    ∃ S : Sylow 2 X, Q ≤ (S : Subgroup X) ∧ ∀ s ∈ (S : Subgroup X), s * z = z * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz]; simp
  obtain ⟨S₀, hS₀z⟩ := hzp.exists_le_sylow
  have hzS₀ : z ∈ (S₀ : Subgroup X) := hS₀z (Subgroup.mem_zpowers z)
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have : Nontrivial ↥(S₀ : Subgroup X) := ⟨⟨⟨z, hzS₀⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  have : Nontrivial ↥(Subgroup.center ↥(S₀ : Subgroup X)) := S₀.isPGroup'.center_nontrivial
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center ↥(S₀ : Subgroup X)) := by
    obtain ⟨n, hn⟩ := (S₀.isPGroup'.to_subgroup (Subgroup.center ↥(S₀ : Subgroup X))).exists_card_eq
    rw [hn]
    have hn0 : n ≠ 0 := by
      rintro rfl
      have : Nat.card ↥(Subgroup.center ↥(S₀ : Subgroup X)) = 1 := by simpa using hn
      exact (Subgroup.nontrivial_iff_ne_bot _ |>.1 inferInstance) (Subgroup.card_eq_one.1 this)
    exact dvd_pow_self 2 hn0
  obtain ⟨ζ₀, hζ₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥(S₀ : Subgroup X))) 2 h2
  set ζ : X := (((ζ₀ : ↥(Subgroup.center ↥(S₀ : Subgroup X))) : ↥(S₀ : Subgroup X)) : X) with hζdef
  have hζ2 : orderOf ζ = 2 := by
    rw [hζdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hζ₀
  have hζc : ∀ s ∈ (S₀ : Subgroup X), s * ζ = ζ * s := by
    intro s hs
    have := Subgroup.mem_center_iff.1 ζ₀.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  obtain ⟨c, hc⟩ := isConj_iff.1 (hQD.involutions_isConj ζ z hζ2 hz)
  have hS₁C : ((c • S₀ : Sylow 2 X) : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
    intro s' hs'
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hc]
    have := hζc s hs
    simp only [MulAut.smul_def, MulAut.conj_apply]
    calc c * s * c⁻¹ * (c * ζ * c⁻¹) = c * (s * ζ) * c⁻¹ := by group
      _ = c * (ζ * s) * c⁻¹ := by rw [this]
      _ = c * ζ * c⁻¹ * (c * s * c⁻¹) := by group
  have hQC : Q ≤ Subgroup.centralizer ({z} : Set X) :=
    fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hQz q hq)
  have hQ' : IsPGroup 2 (Q.subgroupOf (Subgroup.centralizer ({z} : Set X))) :=
    hQ.of_injective (Subgroup.subgroupOfEquivOfLe hQC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQC).injective
  obtain ⟨P, hP⟩ := hQ'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(Subgroup.centralizer ({z} : Set X))
    ((c • S₀).subtype hS₁C) P
  refine ⟨(g : X) • (c • S₀), ?_, ?_⟩
  · intro q hq
    have h1 : (⟨q, hQC hq⟩ : ↥(Subgroup.centralizer ({z} : Set X))) ∈ P := hP hq
    rw [← hg, Sylow.smul_subtype hS₁C g] at h1
    exact h1
  · intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.1 (Sylow.smul_le hS₁C g hs)

end CFSG.GH74.GLS.Stage4.Rest
