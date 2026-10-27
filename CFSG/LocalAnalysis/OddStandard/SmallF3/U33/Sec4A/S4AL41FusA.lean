module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41GPh
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenC

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem l41_center_ge (h : L41GPh1 t L S x₁ x₂ lam rho) :
    closure {t, (x₁ * x₂) ^ 2} ≤ S ⊓ centralizer (S : Set G) := by
  rw [h.basic.center_S]
  refine (Subgroup.closure_le _).mpr ?_
  intro g hg
  rcases hg with hg | hg
  · rw [hg]
    exact Subgroup.mem_sup_left h.hyp.mem_twoCore
  · rw [Set.mem_singleton_iff.mp hg]
    exact Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2)

theorem mul_self_eq_one_of_mem_closure_t_z (h : Ctx0 t L S x₁ x₂ lam rho) {g : G}
    (hg : g ∈ closure {t, (x₁ * x₂) ^ 2}) : g * g = 1 := by
  rcases mem_closure_t_z h hg with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact t_mul_self h.hyp
  · exact (z_mul_self_ne_one h).1
  · have hcomm : Commute t ((x₁ * x₂) ^ 2) := t_commute_z h
    have ht2 : t ^ 2 = 1 := by rw [pow_two, t_mul_self h.hyp]
    have hz2 : ((x₁ * x₂) ^ 2) ^ 2 = 1 := by rw [pow_two, (z_mul_self_ne_one h).1]
    calc t * (x₁ * x₂) ^ 2 * (t * (x₁ * x₂) ^ 2) = (t * (x₁ * x₂) ^ 2) ^ 2 :=
          (pow_two _).symm
      _ = t ^ 2 * ((x₁ * x₂) ^ 2) ^ 2 := hcomm.mul_pow 2
      _ = 1 := by rw [ht2, hz2, mul_one]

theorem l41_normalizer_S_le_normalizer_E (h : L41GPh1 t L S x₁ x₂ lam rho) {n : G}
    (hn : n ∈ normalizer (S : Set G)) :
    n ∈ normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro g hg
  have hgS : g ∈ S := (Subgroup.mem_inf.mp (l41_center_ge h hg)).1
  have hgC : g ∈ Subgroup.centralizer (S : Set G) :=
    (Subgroup.mem_inf.mp (l41_center_ge h hg)).2
  have hgnS : n * g * n⁻¹ ∈ S :=
    ((Subgroup.mem_set_normalizer_iff).mp hn g).mp hgS
  have hmemC : n * g * n⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : n⁻¹ * s * n ∈ S :=
      ((Subgroup.mem_set_normalizer_iff'').mp hn s).mp hs
    have hcomm : (n⁻¹ * s * n) * g = g * (n⁻¹ * s * n) :=
      Subgroup.mem_centralizer_iff.mp hgC (n⁻¹ * s * n) hs'
    calc s * (n * g * n⁻¹) = n * (n⁻¹ * s * n) * g * n⁻¹ := by group
      _ = n * ((n⁻¹ * s * n) * g) * n⁻¹ := by group
      _ = n * (g * (n⁻¹ * s * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * g * n⁻¹) * s := by group
  have hsq : (n * g * n⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    calc (n * g * n⁻¹) * (n * g * n⁻¹) = n * (g * g) * n⁻¹ := by group
      _ = 1 := by rw [mul_self_eq_one_of_mem_closure_t_z h.toCtx0 hg]; group
  exact h.basic.center_omega (n * g * n⁻¹) ⟨hgnS, hmemC⟩ hsq

theorem l41_conj_t_cases (h : L41GPh1 t L S x₁ x₂ lam rho) {n : G}
    (hn : n ∈ normalizer (S : Set G)) :
    n * t * n⁻¹ = t ∨ n * t * n⁻¹ = t * (x₁ * x₂) ^ 2 := by
  have hnE : n ∈ normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G) :=
    l41_normalizer_S_le_normalizer_E h hn
  have hz := normalizer_fixes_z h.toCtx0 hnE
  have hnt : n * t * n⁻¹ ∈ closure {t, (x₁ * x₂) ^ 2} :=
    ((Subgroup.mem_set_normalizer_iff).mp hnE t).mp (Subgroup.subset_closure (by simp))
  rcases mem_closure_t_z h.toCtx0 hnt with h1 | h1 | h1 | h1
  · exfalso
    have ht1 : t = 1 := by
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    exact t_ne_one h.hyp ht1
  · exact Or.inl h1
  · exfalso
    have htz : t = (x₁ * x₂) ^ 2 := by
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = n⁻¹ * (n * (x₁ * x₂) ^ 2 * n⁻¹) * n := by rw [h1, hz]
        _ = (x₁ * x₂) ^ 2 := by group
    exact t_not_mem_L h.hyp (htz ▸ (y_z_mem_L h.toCtx0).2)
  · exact Or.inr h1

theorem l41_sylow_inf_invCent_eq (h : L41GPh1 t L S x₁ x₂ lam rho) (𝒮 : Sylow 2 G)
    (h𝒮 : S < (𝒮 : Subgroup G)) : invCent t ⊓ (𝒮 : Subgroup G) = S :=
  eq_of_isPGroup_of_odd_relIndex (H := invCent t)
    (fun s hs => ⟨h.toCtx0.le_invCent hs, h𝒮.le hs⟩) inf_le_left
    ((show IsPGroup 2 (𝒮 : Subgroup G) from 𝒮.isPGroup').to_le inf_le_right)
    h.toCtx0.relIndex_odd

theorem l41_exists_conj_swap (h : L41GPh1 t L S x₁ x₂ lam rho) (𝒮 : Sylow 2 G)
    (h𝒮 : S < (𝒮 : Subgroup G)) :
    ∃ a ∈ normalizer (S : Set G) ⊓ (𝒮 : Subgroup G),
      a * t * a⁻¹ = t * (x₁ * x₂) ^ 2 := by
  obtain ⟨a, haSyl, haN, ha_notS⟩ :=
    exists_mem_normalizer_not_mem (show IsPGroup 2 (𝒮 : Subgroup G) from 𝒮.isPGroup') h𝒮
  refine ⟨a, ⟨haN, haSyl⟩, ?_⟩
  rcases l41_conj_t_cases h haN with h1 | h1
  · exfalso
    have haInv : a ∈ invCent t := mem_invCent_iff.mpr (by
      calc a * t = (a * t * a⁻¹) * a := by group
        _ = t * a := by rw [h1])
    have hEq := l41_sylow_inf_invCent_eq h 𝒮 h𝒮
    exact ha_notS (hEq ▸ ⟨haInv, haSyl⟩)
  · exact h1

theorem l41_exists_swap (h : L41GPh1 t L S x₁ x₂ lam rho) (h2 : 2 ∣ S.index) :
    ∃ n ∈ normalizer (S : Set G), n * t * n⁻¹ = t * (x₁ * x₂) ^ 2 := by
  obtain ⟨𝒮, h𝒮⟩ := exists_sylow_gt h.toCtx0.isPGroup h2
  obtain ⟨n, hn, hnt⟩ := l41_exists_conj_swap h 𝒮 h𝒮
  exact ⟨n, hn.1, hnt⟩

theorem l41_not_conj_z (h : L41GPh1 t L S x₁ x₂ lam rho) :
    ¬ ∃ g : G, g * t * g⁻¹ = (x₁ * x₂) ^ 2 := by
  rintro ⟨g, hg⟩
  let z : G := (x₁ * x₂) ^ 2
  have hzg : z = g * t * g⁻¹ := hg.symm
  let E : Subgroup G := closure {t, z}
  have hzE : z ∈ E := Subgroup.subset_closure (by simp)
  have hzC : z ∈ Subgroup.centralizer (S : Set G) :=
    (Subgroup.mem_inf.mp (l41_center_ge h hzE)).2
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
    l41_normalizer_S_le_normalizer_E h hnN
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

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
