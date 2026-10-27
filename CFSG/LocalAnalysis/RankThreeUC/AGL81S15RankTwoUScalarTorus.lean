module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.GroupTheory.SylowTwoEquiv

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open

private theorem exists_fixing_aut_of_map_eq {G G' : Type} [Group G] [Group G']
    (φ : G ≃* G') {U : Subgroup G} {α' : MulAut G'}
    (hα' : (U.map φ.toMonoidHom).map α'.toMonoidHom = U.map φ.toMonoidHom) :
    ∃ α : MulAut G, U.map α.toMonoidHom = U ∧ (∀ x : G, φ (α x) = α' (φ x)) ∧
      (α * α = 1 ↔ α' * α' = 1) := by
  let α : MulAut G := (MulAut.congr φ).symm α'
  have hαapply : ∀ x : G, α x = φ.symm (α' (φ x)) := by
    intro x
    rw [show α = φ.trans (α'.trans φ.symm) from MulAut.congr_symm_apply φ α']
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hkey : ∀ x : G, φ (α x) = α' (φ x) := by
    intro x
    rw [hαapply x, MulEquiv.apply_symm_apply]
  have hα : U.map α.toMonoidHom = U := by
    have hcomp : α.toMonoidHom =
        φ.symm.toMonoidHom.comp (α'.toMonoidHom.comp φ.toMonoidHom) := by
      ext x
      exact hαapply x
    rw [hcomp, ← Subgroup.map_map, ← Subgroup.map_map, hα']
    exact (Subgroup.map_symm_eq_iff_map_eq (K := U) (H := U.map φ.toMonoidHom)
      (e := φ)).mpr rfl
  have hsq : α * α = (MulAut.congr φ).symm (α' * α') :=
    ((MulAut.congr φ).symm.map_mul α' α').symm
  refine ⟨α, hα, hkey, ?_⟩
  constructor
  · intro h
    have h1 : (MulAut.congr φ) (α * α) = 1 := by rw [h, map_one]
    rwa [hsq, MulEquiv.apply_symm_apply] at h1
  · intro h
    rw [hsq, h, (MulAut.congr φ).symm.map_one]

theorem IsScalarTorus.map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') {q : ℕ}
    {U E : Subgroup G} (h : IsScalarTorus q U E) :
    IsScalarTorus q (U.map φ.toMonoidHom) (E.map φ.toMonoidHom) := by
  obtain ⟨hEnorm, hEel, hEcard, hEaut⟩ := h
  obtain ⟨hEcomm, hEexp⟩ := hEel
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_mono (f := φ.toMonoidHom) hEnorm).trans
      (Subgroup.le_normalizer_map φ.toMonoidHom)
  · refine ⟨?_, ?_⟩
    · exact @Subgroup.map_isMulCommutative G G' _ _ E φ.toMonoidHom hEcomm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      rw [← map_pow φ.toMonoidHom e q, hEexp e he, map_one]
  · rw [Subgroup.card_map_of_injective φ.injective, hEcard]
  · intro α' hα'
    obtain ⟨α, hα, hkey, hα2iff⟩ := exists_fixing_aut_of_map_eq φ hα'
    obtain ⟨hpow, hinv⟩ := hEaut α hα
    refine ⟨?_, ?_⟩
    · obtain ⟨j, hj⟩ := hpow
      refine ⟨j, ?_⟩
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      change α' (φ x) * ((φ x) ^ j)⁻¹ ∈ Subgroup.map φ.toMonoidHom U
      rw [← hkey x, ← map_pow φ x j, ← map_inv φ (x ^ j),
        ← map_mul φ (α x) ((x ^ j)⁻¹)]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom (hj x hx)
    · intro hα'2 y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      change α' (φ x) * (φ x)⁻¹ ∈ Subgroup.map φ.toMonoidHom U
      rw [← hkey x, ← map_inv φ x, ← map_mul φ (α x) x⁻¹]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom (hinv (hα2iff.mpr hα'2) x hx)

theorem HasScalarTorus.of_isSylowTwoOf {G : Type} [Group G] [Finite G] {q : ℕ}
    {U₀ U : Subgroup G} (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (h : HasScalarTorus G q U₀) :
    HasScalarTorus G q U := by
  obtain ⟨E, hE⟩ := h
  obtain ⟨g, -, hg⟩ := CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj hU₀ hU
  refine ⟨E.map (MulAut.conj g).toMonoidHom, ?_⟩
  rw [hg]
  exact IsScalarTorus.map (MulAut.conj g) hE

theorem HasScalarTorus.of_mulEquiv {G G' : Type} [Group G] [Group G'] [Finite G']
    (φ : G ≃* G') {q : ℕ} {U₀ : Subgroup G} (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤)
    (h : HasScalarTorus G q U₀) {U : Subgroup G'}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) : HasScalarTorus G' q U := by
  have hfin : Finite G := Finite.of_injective (φ : G → G') φ.injective
  have hU₀' : CFSG.QuasithinUnique.IsSylowTwoOf (U₀.map φ.toMonoidHom) ⊤ := by
    have := @CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv G G' _ _ hfin _ U₀ ⊤ φ hU₀
    simpa using this
  obtain ⟨E, hE⟩ := h
  exact HasScalarTorus.of_isSylowTwoOf hU₀' hU
    ⟨E.map φ.toMonoidHom, IsScalarTorus.map φ hE⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

end
