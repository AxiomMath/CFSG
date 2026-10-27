module

public import CFSG.GroupTheory.CoprimeNilpotentExtension
public import CFSG.GroupTheory.SteinbergBSFixedPointFree

public section

namespace CFSG.GroupTheory

universe u v

variable {G : Type u} {P : Type v}

theorem exists_fixed_of_transitive_of_nilpotent
    [Group G] [Group.IsNilpotent G] [MulAction G P] [Nonempty P]
    (htrans : ∀ p q : P, ∃ g : G, g • p = q)
    (hcube : Function.Bijective (fun g : G => g ^ 3))
    (hstab : ∀ p : P, Function.Bijective (fun n : MulAction.stabilizer G p => n ^ 3))
    (α : MulAut G) (hα : α ^ 3 = 1)
    (F : P → P) (hF : ∀ p : P, F (F (F p)) = p)
    (hequiv : ∀ (g : G) (p : P), F (g • p) = α g • F p) :
    ∃ p : P, F p = p := by
  classical
  let p : P := Classical.choice (inferInstance : Nonempty P)
  obtain ⟨u, hup⟩ := htrans p (F p)
  let N : Subgroup G := MulAction.stabilizer G p
  let β : MulAut G := MulAut.conj (u⁻¹) * α
  have hβ_apply : ∀ x : G, β x = u⁻¹ * α x * u := by
    intro x
    simp [β, MulAut.mul_apply]
  let dG : G := u⁻¹ * α (u⁻¹) * α (α (u⁻¹))
  have hβ3 : ∀ x : G, (β ^ 3) x = dG * x * dG⁻¹ := by
    intro x
    rw [show β ^ 3 = β * β * β by rw [pow_succ, pow_succ, pow_one]]
    rw [MulAut.mul_apply, MulAut.mul_apply]
    dsimp only [dG]
    simp only [hβ_apply, map_mul, map_inv,
      apply_three_eq_self_of_pow_three_eq_one α hα]
    group
  have hβd : β dG = dG := by
    dsimp only [dG]
    simp only [hβ_apply, map_mul, map_inv,
      apply_three_eq_self_of_pow_three_eq_one α hα]
    group
  let F' : P → P := fun x => u⁻¹ • F x
  have hF'_fix : F' p = p := by
    dsimp only [F']
    rw [← hup, inv_smul_smul]
  have hF'_equiv : ∀ (g : G) (x : P), F' (g • x) = β g • F' x := by
    intro g x
    calc
      F' (g • x) = u⁻¹ • F (g • x) := rfl
      _ = u⁻¹ • (α g • F x) := by rw [hequiv]
      _ = (u⁻¹ * α g) • F x := by rw [mul_smul]
      _ = (u⁻¹ * α g * u) • (u⁻¹ • F x) := by
            rw [← mul_smul]
            rw [show (u⁻¹ * α g * u) * u⁻¹ = u⁻¹ * α g by group]
      _ = β g • F' x := by rw [hβ_apply g]
  have hF_inj : Function.Injective F := by
    intro x y hxy
    have h := congrArg (fun z => F (F z)) hxy
    simpa [hF] using h
  have hF'_inj : Function.Injective F' := by
    intro x y hxy
    dsimp only [F'] at hxy
    have h1 : F x = F y := by
      have := congrArg (fun z => u • z) hxy
      simpa [smul_inv_smul] using this
    exact hF_inj h1
  have hβN_iff : ∀ n : G, β n ∈ N ↔ n ∈ N := by
    intro n
    constructor
    · intro hβn
      have h1 : F' (n • p) = F' p := by
        rw [hF'_equiv, hF'_fix, MulAction.mem_stabilizer_iff.mp hβn]
      exact MulAction.mem_stabilizer_iff.mpr (hF'_inj h1)
    · intro hn
      have h2 : β n • p = p := by
        calc
          β n • p = β n • F' p := by rw [hF'_fix]
          _ = F' (n • p) := (hF'_equiv n p).symm
          _ = F' p := by rw [MulAction.mem_stabilizer_iff.mp hn]
          _ = p := hF'_fix
      exact MulAction.mem_stabilizer_iff.mpr h2
  have hβ_map : N.map β.toMonoidHom = N := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact (hβN_iff x).mpr hx
    · intro x hx
      rw [Subgroup.mem_map]
      refine ⟨β⁻¹ x, ?_, ?_⟩
      · apply (hβN_iff (β⁻¹ x)).mp
        simpa [MulAut.apply_inv_self] using hx
      · simp
  let βN : MulAut N := CFSG.GroupTheory.SteinbergBS.invariantRestrict β N hβ_map
  have hβN_coe : ∀ n : N, ((βN n : N) : G) = β (n : G) := by
    intro n
    dsimp only [βN]
    have h := CFSG.GroupTheory.SteinbergBS.coe_invariantRestrict_pow β N hβ_map 1 n
    simpa using h
  have hβN2_coe : ∀ n : N, ((βN (βN n) : N) : G) = β (β (n : G)) := by
    intro n
    rw [hβN_coe (βN n), hβN_coe n]
  have hF'3 : ∀ x : P, F' (F' (F' x)) = dG • x := by
    intro x
    dsimp only [F', dG]
    simp only [hequiv, hF, mul_smul, map_inv]
  have hdN : dG ∈ N := by
    have h := hF'3 p
    have h' : dG • p = p := by simpa [hF'_fix] using h.symm
    exact MulAction.mem_stabilizer_iff.mpr h'
  let dN : N := ⟨dG, hdN⟩
  have hβN3 : ∀ n : N, βN (βN (βN n)) = dN * n * dN⁻¹ := by
    intro n
    apply Subtype.ext
    have hcoe3 : ((βN (βN (βN n)) : N) : G) = (β ^ 3) n := by
      have h := CFSG.GroupTheory.SteinbergBS.coe_invariantRestrict_pow β N hβ_map 3 n
      rw [show βN ^ 3 = βN * βN * βN by rw [pow_succ, pow_succ, pow_one]] at h
      rw [MulAut.mul_apply, MulAut.mul_apply] at h
      exact h
    rw [hcoe3, hβ3 (n : G)]
    rfl
  have hcN : βN dN = dN := by
    apply Subtype.ext
    rw [hβN_coe dN, hβd]
  obtain ⟨w, hw⟩ :=
    exists_norm_mul_eq_one_of_pow_three_eq_conj βN dN (hstab p) hβN3 hcN
  let a : G := (w : G) * u⁻¹
  have hnorm_id : a * α a * α (α a) =
      (w : G) * β (w : G) * β (β (w : G)) * dG := by
    dsimp only [a, dG]
    simp only [hβ_apply, map_mul, map_inv]
    group
  have hwG : (w : G) * β (w : G) * β (β (w : G)) * dG = 1 := by
    have h := congrArg Subtype.val hw
    simpa [hβN_coe, hβN2_coe, dN] using h
  have ha_norm : a * α a * α (α a) = 1 := by
    rw [hnorm_id, hwG]
  have ha_fix : a • F p = p := by
    dsimp only [a]
    rw [← hup, mul_smul, inv_smul_smul]
    exact MulAction.mem_stabilizer_iff.mp w.2
  obtain ⟨b, hb⟩ :=
    exists_inv_mul_aut_of_norm_one_of_nilpotent α hα hcube (u := a) ha_norm
  have hb_fix : α b • F p = b • p := by
    have h1 : b⁻¹ • (α b • F p) = p := by
      have h := ha_fix
      rw [hb, mul_smul] at h
      exact h
    calc
      α b • F p = b • (b⁻¹ • (α b • F p)) := by rw [smul_inv_smul]
      _ = b • p := by rw [h1]
  refine ⟨b • p, ?_⟩
  calc
    F (b • p) = α b • F p := hequiv b p
    _ = b • p := hb_fix

end CFSG.GroupTheory
