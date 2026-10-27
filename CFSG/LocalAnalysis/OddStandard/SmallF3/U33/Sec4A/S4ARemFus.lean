module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AFusA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem not_conj_z_of_ctx (h : Ctx t L S x₁ x₂ lam rho tau) :
    ¬ ∃ g : G, g * t * g⁻¹ = (x₁ * x₂) ^ 2 := by
  rintro ⟨g, hg⟩
  let z : G := (x₁ * x₂) ^ 2
  have hzg : z = g * t * g⁻¹ := hg.symm
  let E : Subgroup G := closure {t, z}
  have hzE : z ∈ E := Subgroup.subset_closure (by simp)
  have hzC : z ∈ Subgroup.centralizer (S : Set G) :=
    (Subgroup.mem_inf.mp (h.center_ge hzE)).2
  have hS_le : S ≤ invCent z := by
    intro s hs
    rw [mem_invCent_iff (t := z)]
    exact Subgroup.mem_centralizer_iff.mp hzC s hs
  have hmap : (invCent t).map (MulAut.conj g).toMonoidHom = invCent z := by
    ext k
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_invCent_iff (t := t),
      mem_invCent_iff (t := z), hzg]
    constructor
    · intro hk
      calc k * (g * t * g⁻¹)
          = (g * (g⁻¹ * k * g) * g⁻¹) * (g * t * g⁻¹) := by group
        _ = g * ((g⁻¹ * k * g) * t) * g⁻¹ := by group
        _ = g * (t * (g⁻¹ * k * g)) * g⁻¹ := by rw [hk]
        _ = (g * t * g⁻¹) * (g * (g⁻¹ * k * g) * g⁻¹) := by group
        _ = (g * t * g⁻¹) * k := by group
    · intro hk
      calc (g⁻¹ * k * g) * t
          = g⁻¹ * (k * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * k) * g := by rw [hk]
        _ = t * (g⁻¹ * k * g) := by group
  have hSH : S.map (MulAut.conj g).toMonoidHom ≤ invCent z := by
    rw [← hmap]
    exact Subgroup.map_mono h.toCtx0.le_invCent
  have hSi : ¬ 2 ∣ (S.map (MulAut.conj g).toMonoidHom).relIndex (invCent z) := by
    have hnot := not_two_dvd_relIndex_map_conj (H := invCent t) (S := S) g h.toCtx0.relIndex_odd
    rwa [hmap] at hnot
  have hS0 : IsPGroup 2 (S.map (MulAut.conj g).toMonoidHom) :=
    h.toCtx0.isPGroup.map (MulAut.conj g).toMonoidHom
  obtain ⟨k, hkH, hkconj⟩ := exists_conj_le_of_isPGroup (H := invCent z)
    (S := S.map (MulAut.conj g).toMonoidHom) (Q := S) hS_le h.toCtx0.isPGroup hSH hS0 hSi
  have hmS : ∀ q ∈ S, (g⁻¹ * k) * q * (g⁻¹ * k)⁻¹ ∈ S := by
    intro q hq
    obtain ⟨x, hxS, hxeq⟩ := Subgroup.mem_map.mp (hkconj q hq)
    have hxeq' : g * x * g⁻¹ = k * q * k⁻¹ := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxeq
    have hmem : (g⁻¹ * k) * q * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * q * k⁻¹) * g := by group
    rw [hmem]
    have heq : g⁻¹ * (k * q * k⁻¹) * g = x := by
      rw [← hxeq']
      group
    rw [heq]
    exact hxS
  have hmN : g⁻¹ * k ∈ normalizer (S : Set G) := mem_normalizer_of_conj_mem hmS
  have hnN : k⁻¹ * g ∈ normalizer (S : Set G) := by
    have h := (normalizer (S : Set G)).inv_mem hmN
    simpa only [mul_inv_rev, inv_inv] using h
  have hnE : k⁻¹ * g ∈ normalizer (E : Set G) :=
    normalizer_S_le_normalizer_E h hnN
  have hnz : (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ = z :=
    normalizer_fixes_z h.toCtx0 hnE
  have hkz : k * z = z * k := (mem_invCent_iff (t := z)).mp hkH
  have hnt : (k⁻¹ * g) * t * (k⁻¹ * g)⁻¹ = z := by
    calc (k⁻¹ * g) * t * (k⁻¹ * g)⁻¹
        = k⁻¹ * (g * t * g⁻¹) * k := by group
      _ = k⁻¹ * z * k := by rw [hzg]
      _ = z := by
          calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
            _ = k⁻¹ * (k * z) := by rw [← hkz]
            _ = z := by group
  have htz : t = z := by
    have hcancel : (k⁻¹ * g) * t * (k⁻¹ * g)⁻¹ = (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ :=
      hnt.trans hnz.symm
    calc t = (k⁻¹ * g)⁻¹ * ((k⁻¹ * g) * t * (k⁻¹ * g)⁻¹) * (k⁻¹ * g) := by group
      _ = (k⁻¹ * g)⁻¹ * ((k⁻¹ * g) * z * (k⁻¹ * g)⁻¹) * (k⁻¹ * g) := by rw [hcancel]
      _ = z := by group
  have hzL : z ∈ L := by
    change (x₁ * x₂) ^ 2 ∈ L
    exact (y_z_mem_L h.toCtx0).2
  exact t_not_mem_L h.hyp (by rw [htz]; exact hzL)

private lemma false_of_conj_eq_of_conj_z (h : Ctx t L S x₁ x₂ lam rho tau) {v c : G}
    (hcL : c ∈ L) (hcv : c * (x₁ * x₂) ^ 2 * c⁻¹ = v) {g : G}
    (hconj : g * t * g⁻¹ = v) : False :=
  not_conj_z_of_ctx h ⟨c⁻¹ * g, by
    calc (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹
        = c⁻¹ * (g * t * g⁻¹) * c := by group
      _ = c⁻¹ * v * c := by rw [hconj]
      _ = c⁻¹ * (c * (x₁ * x₂) ^ 2 * c⁻¹) * c := by rw [← hcv]
      _ = (x₁ * x₂) ^ 2 := by group⟩

theorem tG_inf_four_of_ctx (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ g : G, ∀ v ∈ fourGrp x₁ x₂, g * t * g⁻¹ ≠ v := by
  intro g v hv hconj
  have hv' : v ∈ closure {x₁ ^ 2, (x₁ * x₂) ^ 2} := hv
  have hcases := mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2)
    (y_commute_z h.wreath) (y_mul_self_ne_one h.wreath).1
    (z_mul_self_ne_one h.toCtx0).1 hv'
  rcases hcases with h1 | h1 | h1 | h1
  ·
    rw [h1] at hconj
    exact t_ne_one h.hyp (by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [hconj]; group)
  ·
    rw [h1] at hconj
    obtain ⟨c, hcL, hcz⟩ := h.invol_L (x₁ ^ 2) (y_z_mem_L h.toCtx0).1
      (y_mul_self_ne_one h.wreath).1 (y_mul_self_ne_one h.wreath).2
    exact false_of_conj_eq_of_conj_z h hcL hcz hconj
  ·
    rw [h1] at hconj
    exact not_conj_z_of_ctx h ⟨g, hconj⟩
  ·
    rw [h1] at hconj
    obtain ⟨c, hcL, hcz⟩ := h.invol_L (x₁ ^ 2 * (x₁ * x₂) ^ 2)
      (L.mul_mem (y_z_mem_L h.toCtx0).1 (y_z_mem_L h.toCtx0).2)
      (yz_mul_self_ne_one h.wreath).1 (yz_mul_self_ne_one h.wreath).2
    exact false_of_conj_eq_of_conj_z h hcL hcz hconj

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
