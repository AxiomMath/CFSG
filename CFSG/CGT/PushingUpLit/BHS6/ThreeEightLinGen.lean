module

public import CFSG.CGT.PushingUpLit.BHS6.PushUpGen
public import CFSG.CGT.PushingUpLit.BHS.ThreeEight

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Lift.Piece
  CFSG.CGT.PushingUpLit.BHS
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem three_eight_linear_gen {G T V M : Subgroup Γ}
    (hG : CharTwo G) (hT : IsSylowTwoOf T G) (hMG : M ≤ G) (hne : M ≠ G)
    (hN : G ⊓ Subgroup.normalizer (T : Set Γ) ≤ M)
    (hchN : ∀ C : Subgroup Γ, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      G ⊓ Subgroup.normalizer (C : Set Γ) ≤ M)
    (hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ M)
    (hZ : G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ) ≤ M)
    (hVn : G ≤ Subgroup.normalizer (V : Set Γ))
    (hVQ : V ≤ omegaOneCenterOf (pCoreOf 2 G))
    (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβe : ∀ (g : ↥G) (v v' : ↥V), (v' : Γ) = g * v * g⁻¹ →
      Multiplicative.toAdd (β v') =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer (G : Set Γ)).subgroupOf V) :
    ∃ E P' : Subgroup Γ, P' ≤ G ∧ baum T ≤ P' ∧ V ≤ P' ∧ IsSylowTwoOf (baum T) P' ∧
      IsMinParabolic2 (baum T) P' ∧ CharTwo P' ∧ (P'.subgroupOf G).map α = ⊤ ∧
      NoCharNormal (baum T) P' ∧
      (∀ t ∈ T, ∃ b ∈ baum T, b⁻¹ * t ∈ Subgroup.centralizer (V : Set Γ)) ∧
      ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (V : Set Γ) ∧
      E = twoResidual P' ∧ IsChi0Block P' E ∧
      (∃ n : ℕ, 1 ≤ n ∧ Nat.card F = 2 ^ n ∧ (1 < n → IsLin2Type E n) ∧
        (n = 1 → IsAltType E 3)) ∧
      ⁅pCoreOf 2 P', E⁆ ≤ V ∧ ⁅E, omegaOneCenterOf (baum T)⁆ ≤ V ∧
      ¬ E ≤ Subgroup.centralizer (omegaOneCenterOf T : Set Γ) ∧
      G ≤ baum T ⊔ E ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) := by
  classical
  obtain ⟨P', hP'G, hSP', hVP', hSylP', hminP', hcharP', hαP', hnc, hTSC, hJS⟩ :=
    exists_pushUp_parabolics_gen hG hT hMG hne hN hchN hC hVn hVQ α hα hαk β hβ hβe hβk
  have hT2 : IsPGroup 2 T := hT.2.1
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_le' hVQ (isElemAbelian_omegaOneCenterOf' _)
  have hVnP' : P' ≤ Subgroup.normalizer (V : Set Γ) := hP'G.trans hVn
  obtain ⟨hαP'', hαkP', hβeP', hβkP'⟩ := natural_data_restrict α hαk β hβe hβk hP'G hαP'
  obtain ⟨M', ρ', hρ', hset⟩ := exists_natQuotSetting_of_isMinParabolic2 hminP' hVP' hVe hVnP'
    (α.comp (Subgroup.inclusion hP'G)) hαP'' hαkP' β hβ hβeP' hβkP'
  have hchar : CharTwo (⊤ : Subgroup ↥P') := charTwo_top_of_charTwo' hcharP'
  have hnc' : NoCharNormal ((baum T).subgroupOf P') (⊤ : Subgroup ↥P') :=
    noCharNormal_top_subgroupOf' hSP' hnc
  have hJ' : ⁅elemThompsonIn 2 ((baum T).subgroupOf P'), V.subgroupOf P'⁆ ≠ ⊥ :=
    commutator_thompson_ne_bot hSP' hVP' hJS
  obtain ⟨n, hn, hcard⟩ := card_eq_two_pow (k := F)
  have hBB : elemBaumannIn 2 ((baum T).subgroupOf P') = (baum T).subgroupOf P' := by
    have h1 := C56.elemBaumannIn_subgroupOf_map hSP'
    rw [C1GN.baum_baum] at h1
    have h2 : ((baum T).subgroupOf P').map P'.subtype = baum T :=
      Subgroup.map_subgroupOf_eq_of_le hSP'
    exact Subgroup.map_injective P'.subtype_injective (h1.trans h2.symm)
  have hGb : baumannOvergroup ((baum T).subgroupOf P') = ⊤ := by
    unfold baumannOvergroup
    rw [hBB]
    apply Subgroup.map_injective P'.subtype_injective
    rw [Subgroup.map_sup, map_oddOrderSubgroup_top, Subgroup.map_subgroupOf_eq_of_le hSP',
      ← twoResidual_eq_oddOrderSubgroup, sup_comm, sup_twoResidual_eq hSylP']
    exact (Subgroup.range_subtype P').symm.trans (MonoidHom.range_eq_map _)
  obtain ⟨hchi, hlin, halt, hQL, -⟩ :=
    natural_chi0_block_ext hset hchar hnc' hJ' hn hcard hGb
  set L' : Subgroup ↥P' := oddOrderSubgroup (⊤ : Subgroup ↥P') with hL'
  have hf : Function.Injective P'.subtype := P'.subtype_injective
  have hEeq : L'.map P'.subtype = twoResidual P' := by
    rw [hL', map_oddOrderSubgroup_top, twoResidual_eq_oddOrderSubgroup]
  have htop : (⊤ : Subgroup ↥P').map P'.subtype = P' :=
    (MonoidHom.range_eq_map _).symm.trans (Subgroup.range_subtype P')
  have hchiG : IsChi0Block P' (twoResidual P') := by
    have := IsChi0Block.map_of_injective P'.subtype hf hchi
    rwa [htop, hEeq] at this
  have hYS : omegaOneCenterOf (baum T) ≤ baum T := C1GN.omegaOneCenterOf_le_self _
  have hYc : omegaOneCenterOf (baum T) ≤ Subgroup.centralizer (baum T : Set Γ) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1.2
  have hQS : pCoreOf 2 P' ≤ baum T := hSylP'.pCoreOf_le
  have hYQ : omegaOneCenterOf (baum T) ≤ pCoreOf 2 P' := fun y hy =>
    hcharP' ⟨hSP' (hYS hy), Subgroup.centralizer_le (fun x hx => hQS hx) (hYc hy)⟩
  have hQP' : pCoreOf 2 P' ≤ P' := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 P'
  have hV'n : (V.subgroupOf P').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVP').mpr hVnP'
  have hQn : ((pCoreOf 2 P').subgroupOf P').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP').mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P')
  have hQ'' : (pCoreOf 2 P').subgroupOf P' ≤ pCoreOf 2 (⊤ : Subgroup ↥P') :=
    le_pCoreOf_of_normalizes (p := 2) le_top (top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr
      hQn)) ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 P').of_equiv
        (Subgroup.subgroupOfEquivOfLe hQP').symm)
  have hcomm1 : ⁅(pCoreOf 2 P').subgroupOf P', L'⁆ ≤ V.subgroupOf P' := by
    calc ⁅(pCoreOf 2 P').subgroupOf P', L'⁆ ≤ ⁅pCoreOf 2 (⊤ : Subgroup ↥P'), L'⁆ :=
          Subgroup.commutator_mono hQ'' le_rfl
      _ = ⁅V.subgroupOf P', L'⁆ := hQL
      _ ≤ V.subgroupOf P' := Subgroup.commutator_le_left _ _
  have hcomm2 : ⁅pCoreOf 2 P', twoResidual P'⁆ ≤ V := by
    have h3 := Subgroup.map_mono (f := P'.subtype) hcomm1
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQP', hEeq,
      Subgroup.map_subgroupOf_eq_of_le hVP'] at h3
  have hGK : ∀ g ∈ G, g ∈ P' ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) := by
    intro g hg
    have hmem : α ⟨g, hg⟩ ∈ (P'.subgroupOf G).map α := hαP' ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyg⟩ := hmem
    have hy' : (y : Γ) ∈ P' := Subgroup.mem_subgroupOf.mp hy
    have h1 : α (y⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hyg, inv_mul_cancel]
    have h2 : ((y : Γ)⁻¹ * g) ∈ Subgroup.centralizer (V : Set Γ) :=
      (map_eq_one_iff_centralizer α hαk (G.mul_mem (G.inv_mem y.2) hg)).mp h1
    have e : g = (y : Γ) * ((y : Γ)⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hy' ⟨G.mul_mem (G.inv_mem y.2) hg, h2⟩
  have hGfin : G ≤ baum T ⊔ twoResidual P' ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) := by
    intro g hg
    have h1 := hGK g hg
    have e : P' = baum T ⊔ twoResidual P' := (sup_twoResidual_eq hSylP').symm
    rw [e] at h1
    exact h1
  refine ⟨twoResidual P', P', hP'G, hSP', hVP', hSylP', hminP', hcharP', hαP', hnc, hTSC, hJS, rfl,
    hchiG,
    ⟨n, hn, hcard, fun h => hEeq ▸ IsLin2Type.map_of_injective P'.subtype hf (hlin h),
      fun h => hEeq ▸ IsAltType.map_of_injective P'.subtype hf (halt h).1⟩, hcomm2,
    (Subgroup.commutator_mono le_rfl hYQ).trans (by rw [Subgroup.commutator_comm]; exact hcomm2),
    ?_, hGfin⟩
  intro hEc
  apply hne
  refine le_antisymm hMG fun g hg => ?_
  have hTM : T ≤ M := fun t ht => hN ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  have hbM : baum T ≤ M := (inf_le_left : baum T ≤ T).trans hTM
  have hEM : twoResidual P' ≤ M := fun x hx =>
    hZ ⟨(twoResidual_le P').trans hP'G hx, hEc hx⟩
  have hall : baum T ⊔ twoResidual P' ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) ≤ M :=
    sup_le (sup_le hbM hEM) hC
  exact hall (hGfin hg)

end CFSG.CGT.PushingUpLit.BHS6
