module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26MCMain
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26SCON
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26AutMain
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Vac
public import CFSG.HardMathSupport.Solomon.Proving.LBLayerConj
public import CFSG.HardMathSupport.Solomon.Coordinator.ONGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

section Layers

variable {X : Type} [Group X] [Finite X]

theorem i2326m_layer_mono {S L : Subgroup X} (hSL : S ≤ L)
    (hn : L ≤ Subgroup.normalizer (S : Set X)) (e : X) :
    GLAPLayer 3 (S ⊓ Subgroup.centralizer ({e} : Set X)) ≤
      GLAPLayer 3 (L ⊓ Subgroup.centralizer ({e} : Set X)) := by
  have hle : S ⊓ Subgroup.centralizer ({e} : Set X) ≤ L ⊓ Subgroup.centralizer ({e} : Set X) :=
    inf_le_inf_right _ hSL
  have hnorm : L ⊓ Subgroup.centralizer ({e} : Set X) ≤
      Subgroup.normalizer ((S ⊓ Subgroup.centralizer ({e} : Set X) : Subgroup X) : Set X) :=
    fun g hg => i183_mem_normalizer_inf (hn hg.1) (Subgroup.le_normalizer hg.2)
  exact Proving.glaPLayer_le_of_normal_overgroup Nat.prime_three hle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hnorm)

theorem i2326m_normalizes {L : Subgroup X} {𝒦 : Set (Subgroup X)}
    (h𝒦 : ∀ K ∈ 𝒦, IsComponentOf K ⊤) (hL : L = ⨆ K ∈ 𝒦, K) {Kc : Subgroup X}
    (hKc : IsComponentOf Kc ⊤) : L ≤ Subgroup.normalizer (Kc : Set X) := by
  rw [hL]
  refine iSup₂_le fun K' hK' => ?_
  rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute (h𝒦 K' hK') hKc with h | h
  · rw [h]
    exact Subgroup.le_normalizer
  · intro x hx
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    rw [show (x : X) * n * (x : X)⁻¹ = n by
      rw [mul_inv_eq_iff_eq_mul]
      exact h x hx n hn]
    exact hn

end Layers

theorem lemma55_input23_26_of_inputs (hONG : UniquenessMaximal.InputONGroup) (hOut : ONOuterTwo)
    (hA : BGLFieldPairGeneration) (hB : ONGeneration) :
    LocalBalance.Lemma55Ns.Input23_26 := by
  have hP := autL3ElemStructure_holds
  have hV := autL3NoE27OffType_holds
  intro X _ _ L E 𝒦 h𝒦 hL hE h27 hEN
  have hcomp : ∀ K ∈ 𝒦, IsComponentOf K ⊤ := fun K hK => (h𝒦 K hK).1
  refine le_antisymm ?_ ?_
  swap
  · exact iSup_le fun e => iSup_le fun _ => iSup_le fun _ =>
      (i183_glaPLayer_le 3 _).trans inf_le_left
  refine hL.le.trans (iSup₂_le fun K hK => ?_)
  obtain ⟨hKc, hty⟩ := h𝒦 K hK
  have hKL : K ≤ L := hL ▸ (le_iSup₂ (f := fun K' (_ : K' ∈ 𝒦) => K') K hK)
  have h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := i2326c_three_dvd_of_type hONG hty
  have hnormK : L ≤ Subgroup.normalizer (K : Set X) := i2326m_normalizes hcomp hL hKc
  have hmem : ∀ e ∈ E, e ≠ 1 → GLAPLayer 3 (L ⊓ Subgroup.centralizer ({e} : Set X)) ≤
      ⨆ (e : X) (_ : e ∈ E) (_ : e ≠ 1), GLAPLayer 3 (L ⊓ Subgroup.centralizer ({e} : Set X)) :=
    fun e he hne => le_iSup_of_le e (le_iSup_of_le he (le_iSup_of_le hne le_rfl))
  by_cases hz : ∃ z ∈ E, z ≠ 1 ∧ ∀ k ∈ K, z * k = k * z
  · obtain ⟨z, hzE, hz1, hzc⟩ := hz
    exact (i2326c_le_layer_centralizer hKc hKL h3 hzc).trans (hmem z hzE hz1)
  have hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k = k * e) → e = 1 := fun e he hc =>
    by_contra fun hne => hz ⟨e, he, hne, hc⟩
  by_cases hEK : E ≤ Subgroup.normalizer (K : Set X)
  · have hsc : K ≤ ⨆ (e : X) (_ : e ∈ E) (_ : e ≠ 1),
        GLAPLayer 3 (K ⊓ Subgroup.centralizer ({e} : Set X)) := by
      rcases hty with ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ | ⟨F, hFf, hFfin, q, hF, hq, hq8, ⟨e⟩⟩ | hON
      · exact i2326s_sc_L3 hA hP hV hKc (Or.inl ⟨F, hFf, hFfin, hF, ⟨e⟩⟩) hE h27 hEK hfaith
      · exact i2326s_sc_L3 hA hP hV hKc (Or.inr ⟨F, hFf, hFfin, q, hF, hq, hq8, ⟨e⟩⟩) hE h27 hEK
          hfaith
      · exact i2326o_sc_ON hB hOut hKc hON hE h27 hEK hfaith
    refine hsc.trans (iSup_le fun e => iSup_le fun he => iSup_le fun hne => ?_)
    exact (i2326m_layer_mono hKL hnormK e).trans (hmem e he hne)
  · have hmc := mc_generation hKc h3 hE h27 hEK hfaith
    have hKg : ∀ g ∈ E, IsComponentOf (GLBConj g K) ⊤ := fun g _ =>
      i25_isComponentOf_gLBConj hKc (Subgroup.le_normalizer (Subgroup.mem_top g))
    have hPiL : (⨆ g ∈ E, GLBConj g K) ≤ L := iSup₂_le fun g hg => by
      calc GLBConj g K ≤ GLBConj g L := gLBConj_mono g hKL
        _ = L := gLBConj_eq_of_mem_normalizer (hEN hg)
    have hPin : L ≤ Subgroup.normalizer ((⨆ g ∈ E, GLBConj g K : Subgroup X) : Set X) := by
      intro l hl
      rw [mem_normalizer_iff_gLBConj_eq]
      have h1 : GLBConj l (⨆ g ∈ E, GLBConj g K) = ⨆ g ∈ E, GLBConj l (GLBConj g K) := by
        unfold GLBConj
        simp [Subgroup.map_iSup]
      rw [h1]
      exact iSup_congr fun g => iSup_congr fun hg =>
        gLBConj_eq_of_mem_normalizer (i2326m_normalizes hcomp hL (hKg g hg) hl)
    refine hmc.trans (iSup_le fun e => iSup_le fun he => iSup_le fun hne => ?_)
    exact (i2326m_layer_mono hPiL hPin e).trans (hmem e he hne)

theorem lemma55_input23_26_of_residuals
    (hA : BGLFieldPairGeneration) (hB : ONGeneration) :
    LocalBalance.Lemma55Ns.Input23_26 :=
  lemma55_input23_26_of_inputs inputONGroup_holds onOuterTwo_holds hA hB

end CFSG.HardMathSupport.Solomon.Coordinator
