module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieLiftGood
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144PSimple
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem exists_quot_component {Γ : Type} [Group Γ] [Finite Γ] {K W : Subgroup Γ}
    (hK : CFSG.Open.IsQuasisimple ↥K) (hWN : W ≤ Subgroup.normalizer (K : Set Γ))
    (hW : IsElemAbelian 3 W) (hW27 : Nat.card ↥W = 3 ^ 3)
    (hWK : Nat.card ↥(W ⊓ Subgroup.centralizer (K : Set Γ)) = 3)
    {T : Type} [Group T] (eK : ↥K ⧸ Subgroup.center ↥K ≃* T)
    {J : Subgroup Γ} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer (W : Set Γ)) J) :
    ∃ A : Subgroup (MulAut T), IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 ∧
      ∃ I : Subgroup T, GLAPComponent 3 (⨅ f ∈ A, fixSubgroup f) I ∧
        Nonempty (PSimple 3 J ≃* PSimple 3 I) := by
  classical
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.2 hK.1
  haveI : Finite (↥K ⧸ Subgroup.center ↥K) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center ↥K))
      (QuotientGroup.mk'_surjective _)
  haveI : Finite T := Finite.of_surjective eK.toMonoidHom eK.surjective
  set ρ : ↥W →* MulAut T := kd264Rho hWN eK with hρ
  set A : Subgroup (MulAut T) := ρ.range with hA
  have hAtop : IsElemAbelian 3 (⊤ : Subgroup ↥W) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · apply Subtype.ext; apply Subtype.ext
      exact isElemAbelian_commute hW a.val.2 b.val.2
    · apply Subtype.ext
      simpa using hW.2 x.val x.2
  have hAea : IsElemAbelian 3 A := by
    rw [hA, ← Subgroup.map_top ρ]
    exact hAtop.map ρ
  have hAcard : Nat.card A = 3 ^ 2 := by
    have h := card_range_kd264Rho_mul (B := W) hperf hWN eK
    rw [← hρ, ← hA] at h
    have h27 : Nat.card ↥W = 27 := by norm_num [hW27]
    rw [h27, hWK] at h
    have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [h9]
    omega
  have hF'top : A.comap ρ = ⊤ := by
    rw [hA]
    exact MonoidHom.comap_range_self ρ
  have hF'map : (A.comap ρ).map W.subtype = W := by
    rw [hF'top, Subgroup.map_top, Subgroup.range_subtype]
  have hFix : (⨅ b : ↥(A.comap ρ), fixSubgroup
      (normalizerConjAutOfMem K W hWN (b : ↥W))) =
      (K ⊓ Subgroup.centralizer (W : Set Γ)).subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [map_iInf_fixSubgroup_normalizerConjAutOfMem hWN (A.comap ρ), hF'map,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  set J' : Subgroup ↥K := J.subgroupOf K with hJ'def
  have hJ' : GLAPComponent 3 (⨅ b : ↥(A.comap ρ), fixSubgroup
      (normalizerConjAutOfMem K W hWN (b : ↥W))) J' := by
    rw [hFix]
    simpa only [hJ'def] using glaPComponent_subgroupOf Nat.prime_three inf_le_left hJ
  set π : ↥K →* T := eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)) with hπ
  have hπsurj : Function.Surjective π :=
    eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker ≤ Subgroup.center ↥K := by
    rw [hπ, MonoidHom.ker_comp_of_injective _ _ eK.injective,
      show (QuotientGroup.mk' (Subgroup.center ↥K)).ker = Subgroup.center ↥K from
        QuotientGroup.ker_mk' _]
  have hαβ : ∀ (b : ↥(A.comap ρ)) (k : ↥K),
      π (normalizerConjAutOfMem K W hWN (b : ↥W) k) = ρ (b : ↥W) (π k) := by
    intro b k
    simp only [hπ, hρ, kd264Rho, MonoidHom.comp_apply, MulAut.congr_apply,
      normalizerConjAutOfMem_comp_mk, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.coe_toMonoidHom]
  have hβeq : (⨅ b : ↥(A.comap ρ), fixSubgroup (ρ (b : ↥W))) = ⨅ f ∈ A, fixSubgroup f :=
    iInf_fixSubgroup_comap ρ (by rw [hA])
  have hJπ : GLAPComponent 3 (⨅ b : ↥(A.comap ρ), fixSubgroup (ρ (b : ↥W))) (J'.map π) :=
    glaPComponent_map_iInf_fixSubgroup π hπker
      (fun b : ↥(A.comap ρ) => normalizerConjAutOfMem K W hWN (b : ↥W))
      (fun b : ↥(A.comap ρ) => ρ (b : ↥W)) hαβ hπsurj Nat.prime_three hJ'
  set I : Subgroup T := J'.map π with hI
  have hJπ' : GLAPComponent 3 (⨅ f ∈ A, fixSubgroup f) I := by
    rw [← hβeq, hI]
    exact hJπ
  refine ⟨A, hAea, hAcard, I, hJπ', ?_⟩
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.K144.pSimple_subgroupOf_equiv (p := 3) hJK
  obtain ⟨e₂⟩ := nonempty_pSimple_equiv_map (p := 3) Nat.prime_three π hJ' hJπ
  exact ⟨e₁.symm.trans e₂⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

end
