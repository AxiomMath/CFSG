module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMnorm

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell CFSG.SL2MinimalFaithful
open scoped LinearAlgebra.Projectivization

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k]
  {S : Sylow 2 G} {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k}
  {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

theorem normalizer_le_Mnorm_J (h : IsSeed S ρ (Ecore G) ψ) {Z' : Subgroup G}
    (hZ' : ∀ s ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G), ∀ z ∈ Z', s * z = z * s)
    (hnc : ¬ Hone S ≤ Subgroup.centralizer (Z' : Set G)) {y : G}
    (hy : y ∈ Subgroup.normalizer (Z' : Set G)) : y ∈ Mnorm S ρ := by
  by_contra hyM
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  rw [mem_Mnorm_iff hℓ] at hyM
  set Y : Subgroup G := Subgroup.normalizer (Z' : Set G) with hY
  have hJY : CFSG.Quasithin.thompsonJ (S : Subgroup G) ≤ Y := by
    intro s hs
    have hsc : s ∈ Subgroup.centralizer (Z' : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => (hZ' s hs z hz).symm
    exact Subgroup.centralizer_le_normalizer _ hsc
  have h1 : rootGrp ℓ ≤ Y.map ρ := by
    rw [← hℓ, ← JS_map_eq h]
    exact Subgroup.map_mono hJY
  have h2 : rootGrp (ρ y • ℓ) ≤ Y.map ρ := by
    rw [rootGrp_smul_eq_map]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨u', hu', rfl⟩ := h1 hu
    exact ⟨y * u' * y⁻¹, Y.mul_mem (Y.mul_mem hy hu') (Y.inv_mem hy),
      by simp [MulAut.conj_apply, map_mul, map_inv]⟩
  have hsup := h.sup_core_eq_top (fun e => hyM e.symm) h1 h2
  apply hnc
  unfold Hone
  rw [Subgroup.normalClosure]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  obtain ⟨t, ht, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
  have hc : c ∈ Y ⊔ CFSG.pCore 2 G := by rw [hsup]; trivial
  obtain ⟨j, hj, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hc
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro z hz
  have ht' : q * t * q⁻¹ ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    thompsonJ_conj_mem_sylow (core_le_sylow S hq) ht
  have hz' : j⁻¹ * z * j ∈ Z' := by
    have := (Subgroup.mem_normalizer_iff.mp (Y.inv_mem hj) z).mp hz
    simpa using this
  have hcomm := hZ' _ ht' _ hz'
  calc z * (j * q * t * (j * q)⁻¹)
      = j * ((j⁻¹ * z * j) * (q * t * q⁻¹)) * j⁻¹ := by group
    _ = j * ((q * t * q⁻¹) * (j⁻¹ * z * j)) * j⁻¹ := by rw [← hcomm]
    _ = j * q * t * (j * q)⁻¹ * z := by group

end CFSG.QuasithinUnique.Setup.CampbellJ

end
