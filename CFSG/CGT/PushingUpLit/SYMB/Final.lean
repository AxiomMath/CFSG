module

public import CFSG.CGT.PushingUpLit.BHS7.BlockV
public import CFSG.CGT.PushingUpLit.SYMB.Setting

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ} {n : ℕ}
  {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(G6.coreMod n)} {T' : Set (Equiv.Perm (Fin n))}

omit [Finite Γ] in
theorem sym_le_sup_of_alt (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ}
    (hAE : alternatingGroup (Fin n) ≤ imgG G φ E) :
    G ≤ baum T ⊔ E ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) := by
  classical
  intro g hg
  have hEC : E ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) ≤
      baum T ⊔ E ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) :=
    sup_le (le_sup_of_le_left le_sup_right) le_sup_right
  have key : ∀ (g' : Γ) (hg' : g' ∈ G), φ ⟨g', hg'⟩ ∈ alternatingGroup (Fin n) →
      g' ∈ E ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) := by
    intro g' hg' hA
    obtain ⟨e, heG, heE, heφ⟩ := mem_imgG.1 (hAE hA)
    have hk : e⁻¹ * g' ∈ G ⊓ Subgroup.centralizer (V : Set Γ) := by
      refine ⟨G.mul_mem (G.inv_mem heG) hg', ?_⟩
      have h1 : φ ⟨e⁻¹ * g', G.mul_mem (G.inv_mem heG) hg'⟩ = 1 := by
        have e' : (⟨e⁻¹ * g', G.mul_mem (G.inv_mem heG) hg'⟩ : ↥G) =
            ⟨e, heG⟩⁻¹ * ⟨g', hg'⟩ := rfl
        rw [e', map_mul, map_inv, heφ]
        simp
      have h2 : (⟨e⁻¹ * g', G.mul_mem (G.inv_mem heG) hg'⟩ : ↥G) ∈ φ.ker := h1
      rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
      exact h2.2
    have e2 : g' = e * (e⁻¹ * g') := by group
    rw [e2]
    exact Subgroup.mul_mem_sup heE hk
  rcases Int.units_eq_one_or (Equiv.Perm.sign (φ ⟨g, hg⟩)) with h1 | h1
  · exact hEC (key g hg (Equiv.Perm.mem_alternatingGroup.2 h1))
  · obtain ⟨t₀, ht₀⟩ := S.nonempty
    have ht₀B : t₀ ∈ imgG G φ (baum T) := by
      rw [S.baum]
      exact Subgroup.subset_closure ht₀
    obtain ⟨b, hbG, hbB, hbφ⟩ := mem_imgG.1 ht₀B
    have hodd : Equiv.Perm.sign t₀ = -1 := by
      obtain ⟨a, a', haa, rfl⟩ := S.swaps t₀ ht₀
      exact Equiv.Perm.sign_swap haa
    have hbg : φ ⟨b⁻¹ * g, G.mul_mem (G.inv_mem hbG) hg⟩ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      have e' : (⟨b⁻¹ * g, G.mul_mem (G.inv_mem hbG) hg⟩ : ↥G) = ⟨b, hbG⟩⁻¹ * ⟨g, hg⟩ := rfl
      rw [e', map_mul, map_inv, hbφ, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hodd, h1]
      decide
    have h3 := hEC (key _ (G.mul_mem (G.inv_mem hbG) hg) hbg)
    have e2 : g = b * (b⁻¹ * g) := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hbB)) h3

theorem sym_comm_le_of_block (S : SymSetting G T V n φ ψ T') (h4 : 4 ≤ n) {F : Subgroup Γ}
    (hF : IsBTBlock G T F) (hFn : ¬ F ≤ cStarIn G T) :
    ⁅F, omegaOneCenterOf (baum T)⁆ ≤ V := by
  classical
  have hVQ : V ≤ pCoreOf 2 G := S.vQ.trans (C1GN.omegaOneCenterOf_le_self _)
  have hEV : F ≤ Subgroup.normalizer (V : Set Γ) := hF.le.trans S.data.normal
  have hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ cStarIn G T :=
    (inf_le_inf_left G (Subgroup.centralizer_le fun x hx => S.vT hx)).trans
      (centralizer_le_cStarIn G T)
  have hne : ⁅F, V⁆ ≠ ⊥ := fun h0 =>
    hFn ((le_inf hF.le (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0)).trans hC)
  have hTS : IsSylowOf 2 T G := S.sylow
  have hWV : pCoreOf 2 F ≤ V := by
    have h1 := commutator_eq_blockW S.charTwo hTS hF hVQ hEV hne
    rw [blockW_eq_pCoreOf hF] at h1
    rw [← h1, Subgroup.commutator_le]
    intro f hf v hv
    have h2 : f * v⁻¹ * f⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hEV hf) v⁻¹).mp (V.inv_mem hv)
    have e : ⁅f, v⁆ = (f * v * f⁻¹) * v⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hEV hf) v).mp hv) (V.inv_mem hv)
  rw [Subgroup.commutator_le]
  intro f hf z hz
  have hzK : z ∈ kerG G φ := sym_omegaOneCenter_baum_le_ker S h4 hz
  obtain ⟨hzG, hz1⟩ := mem_kerG.1 hzK
  have hzB : z ∈ baum T := C1GN.omegaOneCenterOf_le_self _ hz
  have hfG : f ∈ G := hF.le hf
  have hzN : z ∈ Subgroup.normalizer (F : Set Γ) := baum_le_normalizer_of_isBTBlock hF hzB
  have hc1 : ⁅f, z⁆ ∈ F := by
    have h2 : z * f⁻¹ * z⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hzN f⁻¹).mp (F.inv_mem hf)
    have e : ⁅f, z⁆ = f * (z * f⁻¹ * z⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact F.mul_mem hf h2
  have hcG : ⁅f, z⁆ ∈ G := by
    have e : ⁅f, z⁆ = f * (z * f⁻¹ * z⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact G.mul_mem hfG (G.mul_mem (G.mul_mem hzG (G.inv_mem hfG)) (G.inv_mem hzG))
  have hc2 : ⁅f, z⁆ ∈ Subgroup.centralizer (V : Set Γ) := by
    have h1 : φ ⟨⁅f, z⁆, hcG⟩ = 1 := by
      have e : (⟨⁅f, z⁆, hcG⟩ : ↥G) = ⟨f, hfG⟩ * ⟨z, hzG⟩ * ⟨f, hfG⟩⁻¹ * ⟨z, hzG⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hz1]
      simp
    have h2 : (⟨⁅f, z⁆, hcG⟩ : ↥G) ∈ φ.ker := h1
    rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
    exact h2.2
  have hmem : ⁅f, z⁆ ∈ F ⊓ Subgroup.centralizer (V : Set Γ) := ⟨hc1, hc2⟩
  rw [inf_centralizer_eq_pCoreOf S.charTwo hTS hF hVQ hEV hne] at hmem
  exact hWV hmem

theorem sym_conclusion_of_block (S : SymSetting G T V n φ ψ T') (h4 : 4 ≤ n)
    {F : Subgroup Γ} (hF : IsBTBlock G T F) (hFn : ¬ F ≤ cStarIn G T)
    (hFφ : imgG G φ F = alternatingGroup (Fin n)) :
    G ≤ baum T ⊔ F ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) ∧
      ⁅F, omegaOneCenterOf (baum T)⁆ ≤ V :=
  ⟨sym_le_sup_of_alt S hFφ.ge, sym_comm_le_of_block S h4 hF hFn⟩

end CFSG.CGT.PushingUpLit.SYMB
