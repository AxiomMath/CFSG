module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem exists_pocket_chain_of_block (hQ : Q.Nondegenerate) (z : omegaGroup hQ)
    (hs : (z : OGroup Q) * z = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp (z : OGroup Q)))
    (hW : 0 < Module.finrank (ZMod 3) (fixSp (z : OGroup Q)))
    {K₁ : Subgroup (OGroup (Q.restrict (commSp (z : OGroup Q))))}
    (hπ : piOrth (Q.restrict (commSp (z : OGroup Q))) ∈ K₁)
    (hK₁Ω : K₁ ≤ omegaGroup (nondegenerate_restrict_commSp hQ hs))
    (hK₁n : (K₁.subgroupOf (omegaGroup (nondegenerate_restrict_commSp hQ hs))).Normal)
    (hK₁ : Nonempty (K₁ ≃* SL2F3)) :
    ∃ K M : Subgroup (omegaGroup hQ), z ∈ K ∧ K ≤ M ∧
      M ≤ Subgroup.centralizer ({z} : Set (omegaGroup hQ)) ∧
      (∀ h ∈ K, ∀ l ∈ M, l * h * l⁻¹ ∈ K) ∧
      (∀ l ∈ M, ∀ c ∈ Subgroup.centralizer ({z} : Set (omegaGroup hQ)), c * l * c⁻¹ ∈ M) ∧
      IsSL23Mod K ∧ ∀ k ∈ K, (k : OGroup Q) ≠ piOrth Q := by
  obtain ⟨f⟩ := hK₁
  have hR := nondegenerate_restrict_commSp hQ hs
  have hle : K₁.map (blockInr hs) ≤ omegaGroup hQ := by
    rintro _ ⟨b, hb, rfl⟩
    exact blockInr_mem_omegaGroup hQ hs hU (hK₁Ω hb)
  refine ⟨(K₁.map (blockInr hs)).subgroupOf (omegaGroup hQ),
    ((omegaGroup hR).map (blockInr hs)).subgroupOf (omegaGroup hQ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨_, hπ, blockInr_piOrth hs⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨b, hb, hbx⟩ := hx
    exact ⟨b, hK₁Ω hb, hbx⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨b, -, hbx⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ hs b)
    simp only [Subgroup.coe_mul]
    rw [← hbx]
    exact hc
  · intro h hh l hl
    rw [Subgroup.mem_subgroupOf] at hh hl ⊢
    obtain ⟨b₁, hb₁, hb₁h⟩ := hh
    obtain ⟨b₂, hb₂, hb₂l⟩ := hl
    have hmem : b₂ * b₁ * b₂⁻¹ ∈ K₁ := by
      have hc := hK₁n.conj_mem ⟨b₁, hK₁Ω hb₁⟩ (Subgroup.mem_subgroupOf.mpr hb₁) ⟨b₂, hb₂⟩
      exact Subgroup.mem_subgroupOf.mp hc
    refine ⟨b₂ * b₁ * b₂⁻¹, hmem, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hb₁h, hb₂l]
  · intro l hl c hc
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    obtain ⟨b₂, hb₂, hb₂l⟩ := hl
    have hcc : (c : OGroup Q) ∈ Subgroup.centralizer ({(z : OGroup Q)} : Set (OGroup Q)) := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa using congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) h1
    obtain ⟨c₂, hc₂⟩ := blockInr_conj hQ hs hcc b₂
    refine ⟨c₂ * b₂ * c₂⁻¹, (omegaGroup_normal hR).conj_mem b₂ hb₂ c₂, ?_⟩
    rw [← hc₂, hb₂l]
    rfl
  · refine isSL23Mod_of_mulEquiv ?_ isSL23Mod_sl2f3
    exact f.symm.trans ((Subgroup.equivMapOfInjective K₁ (blockInr hs)
      (blockInr_injective hs)).trans (Subgroup.subgroupOfEquivOfLe hle).symm)
  · intro k hk hkπ
    rw [Subgroup.mem_subgroupOf] at hk
    obtain ⟨b, -, hbk⟩ := hk
    have h1 : blockHom hs (1, b) = blockHom hs (piOrth (Q.restrict (fixSp (z : OGroup Q))),
        piOrth (Q.restrict (commSp (z : OGroup Q)))) := by
      rw [blockHom_piOrth_piOrth hs]
      exact hbk.trans hkπ
    exact piOrth_ne_one hW (congrArg Prod.fst (blockHom_injective hs h1)).symm

end CFSG.OddStandard.SmallF3.Omega
