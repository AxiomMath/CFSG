module

public import CFSG.GF2Type.Smith1980Orth.S3Good
public import CFSG.GF2Type.Smith1980Orth.S4Siegel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal (eichler HypPair)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private instance instFiniteDimensionalVtSiegelD (g : G) (t : S.O) :
    FiniteDimensional (ZMod 2) (Vt S g t) :=
  Module.Finite.of_finite

private theorem projZ_of_mem_perp {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (P : HypPair Q) (τ : P.perp) :
    HypPerp.projZ P (τ : V) = τ := by
  refine Subtype.ext ?_
  obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp τ.2
  rw [HypPerp.coe_projZ, HypPair.proj, polar_comm Q (τ : V) P.f, polar_comm Q (τ : V) P.e, h1, h2]
  simp

namespace S2Data

variable (D : S2Data S)

private theorem exists_eq_eichler_of_isTypeA {a : Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t}
    (ha : IsTypeA D.QV a 2) :
    ∃ e f : Vt S D.g D.t, D.QV e = 0 ∧ D.QV f = 0 ∧ polar D.QV e f = 0 ∧
      LinearIndependent (ZMod 2) ![e, f] ∧ a = eichler D.QV e f := by
  obtain ⟨e, he, he0⟩ : ∃ e ∈ commSpace a, e ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
    have h2 := ha.2.2.2.1
    rw [h, finrank_bot] at h2
    omega
  obtain ⟨f, hli, hspan⟩ := OrthoF2.exists_pair_of_mem_of_finrank_eq_two ha.2.2.2.1 he he0
  obtain ⟨hQe, hQf, hef, hE⟩ :=
    OrthoF2.eq_eichler_of_isTypeA D.QV_nondegenerate ha hli hspan.symm
  exact ⟨e, f, hQe, hQf, hef, hli, hE⟩

private theorem exists_Cbar_conj_of_isTypeA (hw6 : 6 ≤ S.width) {u σ : S.O} (hu : u ∈ D.Cbar)
    (hσ : σ ∈ D.Cbar)
    (huA : IsTypeA D.QV (D.resC ⟨u, hu⟩) 2)
    (hσA : IsTypeA D.QV (D.resC ⟨σ, hσ⟩) 2) :
    ∃ c : S.O, c ∈ D.Cbar ∧ c * u * c⁻¹ = σ := by
  obtain ⟨e, f, he, hf, hef, hli, hE⟩ := D.exists_eq_eichler_of_isTypeA huA
  obtain ⟨e', f', he', hf', hef', hli', hE'⟩ := D.exists_eq_eichler_of_isTypeA hσA
  have h6 : 6 ≤ finrank (ZMod 2) (Vt S D.g D.t) := by
    rw [D.finrank_Vt]
    exact hw6
  obtain ⟨g, hg, hgE⟩ :=
    exists_omega_conj_eichler D.QV_nondegenerate h6 he hf hef hli he' hf' hef' hli'
  obtain ⟨c, hc⟩ := D.exists_Cbar_resC_eq (D.RmodN_eq_omegaGroup.ge hg)
  have h2 : D.resC (c * ⟨u, hu⟩ * c⁻¹) =
      D.resC ⟨σ, hσ⟩ := by
    rw [map_mul, map_mul, map_inv, hc, hE, hE']
    exact hgE
  exact ⟨c, c.2, congrArg Subtype.val (D.resC_injective h2)⟩

namespace Rebase

variable {D : S2Data S} (T : Rebase D)

private theorem exists_singular_perp (hw6 : 6 ≤ S.width) :
    ∃ τ : T.P.perp, (τ : Vt S D.g D.t) ≠ 0 ∧ D.QV (τ : Vt S D.g D.t) = 0 := by
  obtain ⟨x, hx, hx0, hxQ⟩ :=
    S45Q.exists_singular_mem (Q := D.QV) (W := T.P.perp) (T.three_le_finrank_Z hw6)
  exact ⟨⟨x, hx⟩, hx0, hxQ⟩

include T in
private theorem exists_isUInv_conj (hw6 : 6 ≤ S.width) :
    ∃ x : G, ∃ hx : x ∈ S.M, IsConj S.z x ∧ D.IsUInv (S.ρ ⟨x, hx⟩) := by
  obtain ⟨τ, hτ0, hτQ⟩ := T.exists_singular_perp hw6
  obtain ⟨y, hyQ, hyH, hcl⟩ := T.exists_pre (T.coord_zero_mem_perp τ)
  have hy0 : S.cl y ≠ 0 := by
    rw [hcl]
    exact fun h => hτ0 (congrArg Prod.snd (D.coord.injective (h.trans (map_zero _).symm)))
  have hyz : y ≠ S.z := fun h => hy0 (by rw [h, S.cl_z])
  have hconj : IsConj S.z y :=
    (D.isConj_z_iff_coord hyQ hyz).mpr ⟨τ, hτ0, hτQ, Or.inr (Or.inl hcl)⟩
  have hproj : HypPerp.projZ T.P (τ : Vt S D.g D.t) ≠ 0 := by
    rw [projZ_of_mem_perp]
    exact fun h => hτ0 (congrArg Subtype.val h)
  exact ⟨T.g₁ * y * T.g₁⁻¹, (T.mem_H.mp hyH).2, hconj.trans (isConj_iff.mpr ⟨T.g₁, rfl⟩),
    T.isUInv_Psi hw6 hyQ hyH hcl (by rw [polar_zero_left]) hproj hτQ⟩

end Rebase

theorem exists_conj_of_siegel (hw6 : 6 ≤ S.width) {σ : S.O} (hσ : σ ∈ D.Cbar)
    (hσA : IsTypeA D.QV (D.resC ⟨σ, hσ⟩) 2) :
    ∃ y : G, ∃ hyM : y ∈ S.M, IsConj S.z y ∧ S.ρ ⟨y, hyM⟩ = σ := by
  obtain ⟨T⟩ := D.nonempty_rebase
  obtain ⟨x, hxM, hxc, hu, huA⟩ := T.exists_isUInv_conj hw6
  obtain ⟨c, hcC, hc⟩ := D.exists_Cbar_conj_of_isTypeA hw6 hu hσ huA hσA
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (D.Cbar_le_Mbar hcC)
  have hyM : (m : G) * x * (m : G)⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem m.2 hxM) (S.M.inv_mem m.2)
  refine ⟨_, hyM, hxc.trans (isConj_iff.mpr ⟨m, rfl⟩), ?_⟩
  have e : (⟨(m : G) * x * (m : G)⁻¹, hyM⟩ : S.M) = m * ⟨x, hxM⟩ * m⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, hm]
  exact hc

end S2Data

end CFSG.GF2Type.Smith1980Orth
