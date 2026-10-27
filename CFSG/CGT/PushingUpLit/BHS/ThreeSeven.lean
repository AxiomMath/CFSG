module

public import CFSG.CGT.PushingUpLit.BHS.PushUpData
public import CFSG.Quasithin.Background.C118Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannSetting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSeed

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

theorem map_oddOrderSubgroup_top {Γ : Type*} [Group Γ] (H : Subgroup Γ) :
    (oddOrderSubgroup (⊤ : Subgroup H)).map H.subtype = oddOrderSubgroup H := by
  unfold oddOrderSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩
    exact ⟨x.2, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]; exact hx⟩
  · rintro ⟨hyH, hy⟩
    exact ⟨⟨y, hyH⟩, ⟨Subgroup.mem_top _, by rw [Subgroup.orderOf_mk]; exact hy⟩, rfl⟩

variable {Γ : Type} [Group Γ] [Finite Γ] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem three_seven_linear {P T V : Subgroup Γ} (hmin : IsMinParabolic2 T P)
    (hVP : V ≤ P) (hVe : IsElemAbelian 2 V) (hVn : P ≤ Subgroup.normalizer (V : Set Γ))
    (α : ↥P →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hαk : α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf P)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβe : ∀ (g : ↥P) (v v' : ↥V), (v' : Γ) = g * v * g⁻¹ →
      Multiplicative.toAdd (β v') =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)))
    (hβk : β.ker = (Subgroup.centralizer (P : Set Γ)).subgroupOf V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ)) :
    IsSylowTwoOf (baum T) (twoResidual P ⊔ baum T) ∧ V ≤ twoResidual P ⊔ baum T ∧
      (∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
        ∃ x : ↥P, (x : Γ) ∈ twoResidual P ⊔ baum T ∧ α x = A) ∧
      ∀ t ∈ T, ∃ b ∈ baum T, b⁻¹ * t ∈ Subgroup.centralizer (V : Set Γ) := by
  classical
  obtain ⟨M, ρ, hρ, hset⟩ := exists_natQuotSetting_of_isMinParabolic2 hmin hVP hVe hVn α hα hαk β
    hβ hβe hβk
  have hTP : T ≤ P := hmin.1.1
  have hR2 : IsPGroup 2 T := hmin.1.2.1
  have hRH : T ≤ P := hTP
  have hJ' : ⁅elemThompsonIn 2 (T.subgroupOf P), (V.subgroupOf P)⁆ ≠ ⊥ := by
    intro hbot
    apply hJ
    intro j hj
    rw [← C56.elemThompsonIn_subgroupOf_map hRH] at hj
    obtain ⟨j', hj', rfl⟩ := hj
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have hmem : ⁅j', (⟨u, hVP hu⟩ : ↥P)⁆ ∈
        ⁅elemThompsonIn 2 (T.subgroupOf P), V.subgroupOf P⁆ :=
      Subgroup.commutator_mem_commutator hj' (Subgroup.mem_subgroupOf.mpr hu)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact (congrArg Subtype.val hmem).symm
  obtain ⟨ℓ, hSyl, -, -, hBρ, hLS, -, -, -⟩ := hset.Baumann_Sylow hJ'
  have hBmap := C56.elemBaumannIn_subgroupOf_map hRH
  have hLmap : (oddOrderSubgroup (⊤ : Subgroup ↥P)).map P.subtype = oddOrderSubgroup P :=
    map_oddOrderSubgroup_top P
  have hBR : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 (baum T) := hR2.to_le hBR
  have hSylG : IsSylowTwoOf (baum T) (twoResidual P ⊔ baum T) := by
    obtain ⟨-, -, h3⟩ := hSyl
    refine ⟨le_sup_right, hB2, ?_⟩
    have := Subgroup.relIndex_map_map_of_injective (elemBaumannIn 2 (T.subgroupOf P))
      (oddOrderSubgroup (⊤ : Subgroup ↥P) ⊔ elemBaumannIn 2 (T.subgroupOf P))
      P.subtype_injective
    rw [Subgroup.map_sup, hLmap, hBmap, ← twoResidual_eq_oddOrderSubgroup] at this
    show ¬ 2 ∣ (baum T).relIndex (twoResidual P ⊔ baum T)
    rw [this]
    exact h3
  have hρmemSL : ∀ x : ↥P, ρ x ∈ slGamma F := fun x => mem_slGamma_iff.mpr ⟨α x, hρ x⟩
  set R : Subgroup ↥P := T.subgroupOf P with hR
  have hBle : elemBaumannIn 2 R ≤ R := elemBaumannIn_le 2 R
  have hmapB : (elemBaumannIn 2 R).map ρ = R.map ρ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hBle) ?_
    have hRp : IsPGroup 2 (R.map ρ) :=
      (hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hTP).symm).map ρ
    have h1 := card_le_of_isPGroup_of_le_slGamma (R.map ρ)
      (by rintro _ ⟨x, -, rfl⟩; exact hρmemSL x) hRp
    rw [hBρ, card_rootGamma]
    exact h1
  have hVH₀ : V ≤ twoResidual P ⊔ baum T := by
    intro v hv
    have h1 : (⟨v, hVP hv⟩ : ↥P) ∈ oddOrderSubgroup (⊤ : Subgroup ↥P) ⊔ elemBaumannIn 2 R :=
      hset.V_le_baumannOvergroup hJ' (Subgroup.mem_subgroupOf.mpr hv)
    have h2 : v ∈ (oddOrderSubgroup (⊤ : Subgroup ↥P) ⊔ elemBaumannIn 2 R).map P.subtype :=
      ⟨_, h1, rfl⟩
    rwa [Subgroup.map_sup, hLmap, hBmap, ← twoResidual_eq_oddOrderSubgroup] at h2
  have hαH₀ : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ x : ↥P, (x : Γ) ∈ twoResidual P ⊔ baum T ∧ α x = A := by
    intro A
    have h1 : ((slGammaEquiv F A : slGamma F) : Gamma F) ∈
        (oddOrderSubgroup (⊤ : Subgroup ↥P) ⊔ elemBaumannIn 2 R).map ρ := by
      rw [hLS]
      exact (slGammaEquiv F A).2
    obtain ⟨x, hx, hxA⟩ := h1
    refine ⟨x, ?_, ?_⟩
    · have h2 : (x : Γ) ∈ (oddOrderSubgroup (⊤ : Subgroup ↥P) ⊔ elemBaumannIn 2 R).map P.subtype :=
        ⟨x, hx, rfl⟩
      rwa [Subgroup.map_sup, hLmap, hBmap, ← twoResidual_eq_oddOrderSubgroup] at h2
    · apply slPerm_injective (k := F)
      rw [← hρ x, hxA, slGammaEquiv_apply]
  refine ⟨hSylG, hVH₀, hαH₀, fun t ht => ?_⟩
  have htP : t ∈ P := hTP ht
  have hmem : ρ ⟨t, htP⟩ ∈ (elemBaumannIn 2 R).map ρ := by
    rw [hmapB]
    exact ⟨⟨t, htP⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  obtain ⟨b', hb', hb'ρ⟩ := hmem
  refine ⟨(b' : Γ), ?_, ?_⟩
  · have : (b' : Γ) ∈ (elemBaumannIn 2 R).map P.subtype := ⟨b', hb', rfl⟩
    rwa [hBmap] at this
  · have hρ1 : ρ (b'⁻¹ * ⟨t, htP⟩) = 1 := by rw [map_mul, map_inv, hb'ρ, inv_mul_cancel]
    have hα1 : α (b'⁻¹ * ⟨t, htP⟩) = 1 := by
      apply slPerm_injective (k := F)
      rw [← hρ, map_one, hρ1]
      rfl
    have h2 : (b'⁻¹ * ⟨t, htP⟩ : ↥P) ∈ α.ker := hα1
    rw [hαk, Subgroup.mem_subgroupOf] at h2
    simpa using h2

end CFSG.CGT.PushingUpLit.BHS
