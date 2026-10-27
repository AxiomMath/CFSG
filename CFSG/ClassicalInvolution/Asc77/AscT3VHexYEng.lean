module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate8AEng
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement Pointwise

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20G.v_hexY (d : Std20G K K' J S R R' W V z t) :
    ∃ X : Subgroup G, X = (J ⊓ Subgroup.normalizer (K : Set G)) ⊔
        (K ⊓ Subgroup.normalizer (J : Set G)) ∧
      X ≤ pairNormalizers K J z t ∧
      pairNormalizers K J z t ≤ Subgroup.normalizer (X : Set G) ∧
      X = oddCoreOf X ⊔ W ∧
      pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) ≤ X ∧
      (∃ r ∈ K ⊓ (S : Subgroup G), ∃ r' ∈ K' ⊓ (S : Subgroup G),
        r ∈ pairNormalizers K J z t ∧ r' ∈ pairNormalizers K J z t ∧ r * t * r⁻¹ = z * t ∧
        (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧
        pairNormalizers K J z t ⊓ Subgroup.centralizer
            ((Subgroup.closure {z, t} : Subgroup G) : Set G) = X ⊔ Subgroup.zpowers (r * r')) ∧
      ∃ φ : ↥(pairNormalizers K J z t) →* DihedralGroup 6, Function.Surjective φ ∧
        φ.ker = X.subgroupOf (pairNormalizers K J z t) := by
  have hJW := d.late_JW
  have hWeq := d.late_hW
  have c := d.late_cfg98 hJW
  obtain ⟨u, v, T, hu, hv, tor⟩ := c.exists_tor Sec6Gen.l6_4ThreeGenAll
  have hUV : (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) = W := by
    rw [hu, hv, inf_comm K W, inf_comm J W]
    exact hWeq.symm
  obtain ⟨r, hr, r', hr', hinv, hrt⟩ := d.late_tor hJW hWeq
  have hrK : r ∈ K ⊓ (S : Subgroup G) := d.late_R_eq ▸ hr
  have hr'K : r' ∈ K' ⊓ (S : Subgroup G) := d.late_R'_eq ▸ hr'
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have hru : r ∉ Subgroup.zpowers u := by
    intro h
    have huW : Subgroup.zpowers u ≤ W := hu ▸ inf_le_right
    have hc : r * t = t * r := d.late_hWc r (huW h) t d.late_t_mem_W
    have : r * t * r⁻¹ = t := by rw [hc]; group
    rw [hrt] at this
    exact hz1 (by simpa using this)
  have hr't : r' ∉ Subgroup.centralizer ({t} : Set G) := by
    intro h
    have hc : r' * t = t * r' := Subgroup.mem_centralizer_singleton_iff.mp h
    have h1 := hinv t d.late_t_mem_W
    have h2 : (r * r') * t * (r * r')⁻¹ = r * t * r⁻¹ := by
      calc (r * r') * t * (r * r')⁻¹ = r * (r' * t * r'⁻¹) * r⁻¹ := by group
        _ = r * t * r⁻¹ := by rw [hc]; group
    have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [h2, hrt, ht] at h1
    exact hz1 (by simpa using h1)
  obtain ⟨hcW, hcent⟩ := tor.hcent r hrK hru r' hr'K hr't
  have h64 := Sec6Gen.l6_4ThreeGen G (CoreAssembly.conjClass K) d.late_hΩ K d.late_mem_K J
    d.late_mem_J d.late_inA z t d.viol.hzK d.viol.hzJ
    ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)))
    (pairNormalizers K J z t) rfl rfl
  obtain ⟨u₁, v₁, r₁, t₁, Ks, u₂, r₂, h64'⟩ := h64
  obtain ⟨φ, hφs, hφk⟩ := h64'.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨_, rfl, tor.hXY, tor.hYX, ?_, ?_, ⟨r, hrK, r', hr'K, ?_, ?_, hrt, hinv, hcent⟩, φ, hφs,
    hφk⟩
  · have := tor.hXeq
    rwa [hUV] at this
  · have := tor.hf
    rwa [hUV] at this
  · exact tor.hRY _ tor.hR tor.huR tor.hRN hrK
  · exact tor.hR'Y _ tor.hR' tor.hR'N hr'K

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
