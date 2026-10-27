module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Model
public import CFSG.ClassicalInvolution.AschTight.S19KUniStd

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

theorem ker_comp_le_center {G₁ G₂ X : Type} [Group G₁] [Group G₂] [Group X] (ψ : G₂ →* X)
    (hψ : ψ.ker ≤ Subgroup.center G₂) (e : G₁ ≃* G₂) :
    (ψ.comp e.toMonoidHom).ker ≤ Subgroup.center G₁ := by
  intro x hx
  have h1 : e x ∈ Subgroup.center G₂ := hψ hx
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact h1 (e y)

theorem exists_theta_psl {p e : ℕ} [Fact p.Prime] {E : Type} [Group E] {Ω : Set (Subgroup E)}
    (M : Ih8Model p e Ω .PSL 3 e) {L : Subgroup E} (hL : L ∈ Ω) :
    ∃ θ : SL(3, GaloisField p e) →* E, Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center SL(3, GaloisField p e) ∧
      L = (Models.rootSL2 (GaloisField p e) (n := 3) (by norm_num)).map θ := by
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff L).mp hL
  have hRl := RouteD.fundamentalSubgroups_psl_subset (F := GaloisField p e) (m := 2)
    (by norm_num) (M.cls_sub hR)
  obtain ⟨g, hg⟩ := (Models.mem_longRootSet_iff _).mp hRl
  let ψ : SL(3, GaloisField p e) →* E := M.ψ
  have hψ : ψ.ker ≤ Subgroup.center SL(3, GaloisField p e) := M.ker_le_center
  refine ⟨ψ.comp (MulAut.conj g).toMonoidHom, M.surj.comp (MulAut.conj g).surjective,
    ker_comp_le_center ψ hψ (MulAut.conj g), ?_⟩
  change R.map ψ = _
  rw [hg, Subgroup.map_map]

theorem exists_theta_psu {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {E : Type} [Group E]
    {Ω : Set (Subgroup E)} (M : Ih8Model p e Ω .PSU 3 e) {L : Subgroup E} (hL : L ∈ Ω) :
    ∃ θ : Phan.Su (GaloisField p (2 * e)) p e 3 →* E, Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center (Phan.Su (GaloisField p (2 * e)) p e 3) ∧
      L = (rootU (GaloisField p (2 * e)) p e).map θ := by
  obtain ⟨e₁, he₁⟩ := RouteD.psu_model_equiv hp2 M.admissible
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff L).mp hL
  obtain ⟨i, g, hg, -⟩ := (he₁ R).mp (M.cls_sub hR)
  refine ⟨M.ψ.comp (e₁.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom),
    M.surj.comp (e₁.symm.surjective.comp (MulAut.conj g).surjective), ?_, ?_⟩
  · have h1 := ker_comp_le_center M.ψ M.ker_le_center e₁.symm
    exact ker_comp_le_center _ h1 (MulAut.conj g)
  · have hR' : R = (R.map e₁.toMonoidHom).map e₁.symm.toMonoidHom := by
      rw [Subgroup.map_map]
      ext x
      simp
    rw [hR', hg, Subgroup.map_map, Subgroup.map_map]
    rfl

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
