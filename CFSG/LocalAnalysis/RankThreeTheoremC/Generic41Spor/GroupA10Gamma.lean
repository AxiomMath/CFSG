module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10GammaPerm
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Five

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

namespace A10Perm

theorem a10g_gamma_map_le {K K' : Type} [Group K] [Group K'] (ψ : K ≃* K') (S : Subgroup K) :
    (A10Gamma K S).map ψ.toMonoidHom ≤ A10Gamma K' (S.map ψ.toMonoidHom) := by
  unfold A10Gamma
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨g, ⟨B, hBS, hB1, hg⟩, rfl⟩
  refine ⟨B.map ψ.toMonoidHom, Subgroup.map_mono hBS, ?_, ?_⟩
  · obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨ψ b, Subgroup.mem_map_of_mem _ hbB⟩, ?_⟩
    intro h
    apply hb1
    apply Subtype.ext
    apply ψ.injective
    simpa using congrArg Subtype.val h
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have h1 := Subgroup.mem_normalizer_iff.1 hg (ψ.symm y)
    simpa [map_mul, map_inv] using h1

end A10Perm

theorem a10g_exists_iso_gamma {K : Type} [Group K] [Finite K] (hK : IsA10Type 5 K) (S : Sylow 5 K) :
    ∃ ψ : K ≃* A10Perm.A10, (∀ x : K, x ∈ (S : Subgroup K) ↔ ψ x ∈ A10Perm.S₀) ∧
      (A10Gamma K (S : Subgroup K)).map ψ.toMonoidHom = A10Perm.a10gHat := by
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨ψ, hψ⟩ := A10Perm.exists_iso_sylow (e : K ≃* alternatingGroup (Fin 10)) S
  refine ⟨ψ, hψ, ?_⟩
  have hS : (S : Subgroup K).map ψ.toMonoidHom = A10Perm.S₀ := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simpa using hψ (ψ.symm x)
  have hS' : A10Perm.S₀.map ψ.symm.toMonoidHom = (S : Subgroup K) := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simpa using (hψ x).symm
  have h1 : (A10Gamma K (S : Subgroup K)).map ψ.toMonoidHom ≤ A10Perm.a10gGamma := by
    have := A10Perm.a10g_gamma_map_le ψ (S : Subgroup K)
    rwa [hS] at this
  have h2 : A10Perm.a10gGamma.map ψ.symm.toMonoidHom ≤ A10Gamma K (S : Subgroup K) := by
    have := A10Perm.a10g_gamma_map_le ψ.symm A10Perm.S₀
    rwa [hS'] at this
  have h3 : A10Perm.a10gGamma ≤ (A10Gamma K (S : Subgroup K)).map ψ.toMonoidHom := by
    intro x hx
    refine ⟨ψ.symm x, h2 (Subgroup.mem_map_of_mem _ hx), ?_⟩
    simp
  rw [le_antisymm h1 h3]
  exact A10Perm.a10g_gamma_eq_hat

theorem a10_gammaMax : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → A10GammaMax K := by
  intro K _ _ hK S H hH
  obtain ⟨ψ, -, hΓ⟩ := a10g_exists_iso_gamma hK S
  have hHm : A10Perm.a10gHat ≤ H.map ψ.toMonoidHom := hΓ ▸ Subgroup.map_mono hH
  rcases A10Perm.a10g_hat_max hHm with h | h
  · left
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [h, hΓ]
  · right
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [h]
    exact (Subgroup.map_top_of_surjective _ ψ.surjective).symm

theorem a10Ext_holds : A10Ext := ⟨a10_scalars, a10_gammaMax⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
