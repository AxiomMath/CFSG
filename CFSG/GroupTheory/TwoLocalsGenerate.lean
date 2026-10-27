module

public import CFSG.RankThree.PartOne.S12.Sec15Final
public import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.GroupTheory

open CFSG

variable {G : Type} [Group G] [Finite G]

theorem eq_top_of_sylow_unique_maximal_two_local {M : Subgroup G} {T₀ T : Sylow 2 G}
    {R₁ R₂ : Subgroup G}
    (huniq : ∀ M' : Subgroup G, IsMaximalTwoLocal M' → (T₀ : Subgroup G) ≤ M' → M' = M)
    (hR₁ : R₁ ≠ ⊥) (hR₂ : R₂ ≠ ⊥) (hp₁ : IsPGroup 2 R₁) (hp₂ : IsPGroup 2 R₂)
    (hn₁ : (T : Subgroup G) ≤ Subgroup.normalizer (R₁ : Set G))
    (hn₂ : (T : Subgroup G) ≤ Subgroup.normalizer (R₂ : Set G))
    (hsup : Subgroup.normalizer (R₁ : Set G) ⊔ Subgroup.normalizer (R₂ : Set G) = ⊤) :
    M = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T₀ T
  have hfun : MulDistribMulAction.toMonoidEnd (MulAut G) G (MulAut.conj g) =
      (MulAut.conj g).toMonoidHom := by
    ext x
    rfl
  have hTmap : (T : Subgroup G) = (T₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hfun]
  have huniq' : ∀ M' : Subgroup G, IsMaximalTwoLocal M' → (T : Subgroup G) ≤ M' →
      M' = M.map (MulAut.conj g).toMonoidHom := by
    intro M' hM' hTM'
    have hconj : IsMaximalTwoLocal (M'.map (MulAut.conj g⁻¹).toMonoidHom) :=
      CFSG.CGT.PushingUp.isMaximalTwoLocal_map_conj hM' g⁻¹
    have hle : (T₀ : Subgroup G) ≤ M'.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro x hx
      refine ⟨g * x * g⁻¹, hTM' ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      rw [hTmap]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have heq : M'.map (MulAut.conj g⁻¹).toMonoidHom = M := huniq _ hconj hle
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    calc M' = (M'.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.map_map, hcomp, Subgroup.map_id]
      _ = M.map (MulAut.conj g).toMonoidHom := by rw [heq]
  have hN₁ : Subgroup.normalizer (R₁ : Set G) ≤ M.map (MulAut.conj g).toMonoidHom :=
    CFSG.RankThree.PartOne.Sec15Final.normalizer_le_of_forall_maximal hR₁ hp₁ hn₁
      fun M' hM' => (huniq' M' hM'.1 hM'.2).le
  have hN₂ : Subgroup.normalizer (R₂ : Set G) ≤ M.map (MulAut.conj g).toMonoidHom :=
    CFSG.RankThree.PartOne.Sec15Final.normalizer_le_of_forall_maximal hR₂ hp₂ hn₂
      fun M' hM' => (huniq' M' hM'.1 hM'.2).le
  have htop : (⊤ : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom := by
    rw [← hsup]
    exact sup_le hN₁ hN₂
  have hMtop : M.map (MulAut.conj g).toMonoidHom = ⊤ := top_unique htop
  have htop' : (⊤ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  exact Subgroup.map_injective (MulAut.conj g).injective (hMtop.trans htop'.symm)

end CFSG.GroupTheory
