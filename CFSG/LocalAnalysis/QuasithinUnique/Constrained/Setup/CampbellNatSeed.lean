module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellStruct1

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.Quasithin.B6 CFSG.Quasithin.BlueprintB2
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Offender
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

section Restrict

variable {H : Type*} [Group H] {k : Type*} [Field k]

@[expose] noncomputable def restrictSL (ρ : H →* Gamma k) (H₀ : Subgroup H)
    (hmem : ∀ x : H₀, ρ (x : H) ∈ slGamma k) : H₀ →* Matrix.SpecialLinearGroup (Fin 2) k :=
  (slGammaEquiv k).symm.toMonoidHom.comp ((ρ.comp H₀.subtype).codRestrict (slGamma k) hmem)

theorem slPerm_restrictSL (ρ : H →* Gamma k) (H₀ : Subgroup H)
    (hmem : ∀ x : H₀, ρ (x : H) ∈ slGamma k) (x : H₀) :
    slPerm k (restrictSL ρ H₀ hmem x) = ((ρ (x : H) : Gamma k) : Equiv.Perm (Fin 2 → k)) := by
  have h := (slGammaEquiv k).apply_symm_apply ((ρ.comp H₀.subtype).codRestrict (slGamma k) hmem x)
  have h2 := congrArg (fun y : slGamma k => ((y : Gamma k) : Equiv.Perm (Fin 2 → k))) h
  rw [← slGammaEquiv_apply]
  exact h2

theorem restrictSL_apply_smul (ρ : H →* Gamma k) (H₀ : Subgroup H)
    (hmem : ∀ x : H₀, ρ (x : H) ∈ slGamma k) (x : H₀) (w : Fin 2 → k) :
    ((ρ (x : H) : Gamma k) : Equiv.Perm (Fin 2 → k)) w =
      (restrictSL ρ H₀ hmem x : Matrix (Fin 2) (Fin 2) k).mulVec w := by
  rw [← slPerm_restrictSL ρ H₀ hmem x, slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
  rfl

theorem ker_restrictSL (ρ : H →* Gamma k) (H₀ : Subgroup H)
    (hmem : ∀ x : H₀, ρ (x : H) ∈ slGamma k) :
    (restrictSL ρ H₀ hmem).ker = ρ.ker.subgroupOf H₀ := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have h1 := slPerm_restrictSL ρ H₀ hmem x
    rw [hx, map_one] at h1
    exact Subtype.ext h1.symm
  · intro hx
    apply slPerm_injective (k := k)
    rw [slPerm_restrictSL ρ H₀ hmem x, map_one]
    exact congrArg (fun g : Gamma k => (g : Equiv.Perm (Fin 2 → k))) hx

theorem restrictSL_surjective (ρ : H →* Gamma k) (H₀ : Subgroup H)
    (hmem : ∀ x : H₀, ρ (x : H) ∈ slGamma k) (hρ : H₀.map ρ = slGamma k) :
    Function.Surjective (restrictSL ρ H₀ hmem) := by
  intro A
  have hA : (⟨slPerm k A, slPerm_mem_Gamma A⟩ : Gamma k) ∈ H₀.map ρ := by
    rw [hρ]; exact slPerm_mem_slGamma A
  obtain ⟨x, hx, hxA⟩ := hA
  refine ⟨⟨x, hx⟩, ?_⟩
  apply slPerm_injective (k := k)
  rw [slPerm_restrictSL ρ H₀ hmem ⟨x, hx⟩]
  exact congrArg (fun g : Gamma k => (g : Equiv.Perm (Fin 2 → k))) hxA

variable {V : Subgroup H} [V.Normal]

@[expose] def restrictPsi (φ : V →* Multiplicative (Fin 2 → k)) (H₀ : Subgroup H) (hVH : V ≤ H₀) :
    V.subgroupOf H₀ →* Multiplicative (Fin 2 → k) :=
  φ.comp (Subgroup.subgroupOfEquivOfLe hVH).toMonoidHom

omit [V.Normal] in
theorem restrictPsi_apply (φ : V →* Multiplicative (Fin 2 → k)) (H₀ : Subgroup H) (hVH : V ≤ H₀)
    (x : V.subgroupOf H₀) : restrictPsi φ H₀ hVH x = φ ⟨((x : H₀) : H), x.2⟩ := rfl

end Restrict

section Facts

variable {H : Type*} [Group H] [Finite H] {k : Type*} [Field k] [Finite k] [CharP k 2]

theorem elemCenterIn_le_elemThompsonIn {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (R : Subgroup G) : elemCenterIn p R ≤ elemThompsonIn p R := by
  obtain ⟨A, hA⟩ := elemThompsonFamily_nonempty R p
  have hA' : A.map R.subtype ∈ elemFamilyIn p R := ⟨A, hA, rfl⟩
  exact (elemCenterIn_le hA').trans (le_elemThompsonIn hA')

theorem elemThompsonIn_eq_of_le {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    {R S : Subgroup G} (hJS : elemThompsonIn p R ≤ S) (hSR : S ≤ R) :
    elemThompsonIn p S = elemThompsonIn p R := by
  set Y : Subgroup R := S.subgroupOf R with hY
  have hJY : elemThompson R p ≤ Y := fun x hx => Subgroup.mem_subgroupOf.mpr (hJS ⟨x, hx, rfl⟩)
  have h1 := BlueprintB2.elemThompson_map_subtype (p := p) hJY
  have hS : S = Y.map R.subtype := (Subgroup.map_subgroupOf_eq_of_le hSR).symm
  rw [hS, elemThompsonIn_map_of_injective p R.subtype R.subtype_injective Y]
  show ((elemThompson Y p).map Y.subtype).map R.subtype = (elemThompson R p).map R.subtype
  rw [h1]

namespace IsNatQuotSetting

variable {R M V : Subgroup H} {ρ : H →* Gamma k} {φ : V →* Multiplicative (Fin 2 → k)}

theorem map_baumannOvergroup (h : IsNatQuotSetting R M V ρ φ) (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    (baumannOvergroup R).map ρ = slGamma k := by
  obtain ⟨ℓ, -, -, -, -, hρH₀, -⟩ := h.Baumann_Sylow hJ
  exact hρH₀

theorem rho_mem_baumannOvergroup (h : IsNatQuotSetting R M V ρ φ)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) (x : baumannOvergroup R) : ρ (x : H) ∈ slGamma k := by
  have h1 := h.map_baumannOvergroup hJ
  rw [← h1]
  exact Subgroup.mem_map_of_mem ρ x.2

theorem isSylowIn_baumannOvergroup (h : IsNatQuotSetting R M V ρ φ)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    IsSylowIn 2 (elemBaumannIn 2 R) (baumannOvergroup R) := by
  obtain ⟨ℓ, hsyl, -⟩ := h.Baumann_Sylow hJ
  exact hsyl

theorem inf_centralizer_le_elemCenterIn (h : IsNatQuotSetting R M V ρ φ)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    V ⊓ Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H) ≤
      elemCenterIn 2 R := by
  obtain ⟨ℓ, -, -, -, -, -, -, hcomm, -⟩ := h.Baumann_Sylow hJ
  intro x hx
  have hxR : x ∈ R := h.V_le_R hx.1
  have hx2 : x ^ 2 = 1 := h.reduced.2.2.1.2 x hx.1
  have hxJ : ∀ j ∈ elemThompsonIn 2 R, j * x = x * j := fun j hj =>
    mul_comm_of_commutator_eq_bot hcomm hj hx
  exact mem_elemCenterIn_iff_centralizer.mpr ⟨hxR, hx2, hxJ⟩

theorem inf_centralizer_le_elemBaumannIn (h : IsNatQuotSetting R M V ρ φ)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    V ⊓ Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H) ≤
      elemBaumannIn 2 R := by
  intro x hx
  have hxE := h.inf_centralizer_le_elemCenterIn hJ hx
  refine mem_elemBaumannIn_iff.mpr ⟨h.V_le_R hx.1, fun e he => ?_⟩
  exact (mem_elemCenterIn_iff_centralizer.mp hxE).2.2 e (elemCenterIn_le_elemThompsonIn 2 R he)

theorem phi_commutator_surjective (h : IsNatQuotSetting R M V ρ φ)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) (w : Fin 2 → k) :
    ∃ u : H, u ∈ ⁅oddOrderSubgroup (⊤ : Subgroup H), V⁆ ∧ ∃ hu : u ∈ V,
      Multiplicative.toAdd (φ ⟨u, hu⟩) = w := by
  classical
  have hVn : V.Normal := h.normal_V
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  have hVH := h.not_le_centralizer hJ
  obtain ⟨hHLR, -⟩ := minimal_parabolic_reduced_module_Frattini_kernel_production h.sylow
    h.nonnormal h.le_M h.M_lt h.M_max h.reduced hVH
  obtain ⟨ℓ, -, -, hJρ, -⟩ := h.Baumann_Sylow hJ
  obtain ⟨g, hgL, B, hgB, hBℓ⟩ := h.exists_L_moves_line hHLR hJρ
  set C : Subgroup H := ⁅oddOrderSubgroup (⊤ : Subgroup H), V⁆ with hC
  have hCn : C.Normal := Subgroup.commutator_normal _ _
  let T : Set (Fin 2 → k) :=
    {w | ∃ u : H, u ∈ C ∧ ∃ hu : u ∈ V, Multiplicative.toAdd (φ ⟨u, hu⟩) = w}
  have hTinv : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) k) (w : Fin 2 → k), w ∈ T → A • w ∈ T := by
    rintro A w ⟨u, hu, huV, rfl⟩
    obtain ⟨x, hx⟩ := h.sl_le A
    refine ⟨x * u * x⁻¹, hCn.conj_mem u hu x, hVn.conj_mem u huV x, ?_⟩
    have := h.φ_equiv x ⟨u, huV⟩ ⟨x * u * x⁻¹, hVn.conj_mem u huV x⟩ rfl
    rw [this, hx, slPerm_apply]
  obtain ⟨w₁, hw₁0, hℓ⟩ : ∃ w₁ : Fin 2 → k, ∃ hw : w₁ ≠ 0, ℓ = Projectivization.mk k w₁ hw :=
    ⟨ℓ.rep, ℓ.rep_nonzero, (Projectivization.mk_rep ℓ).symm⟩
  have hBw : B • w₁ ≠ w₁ := by
    intro hfix
    apply hBℓ
    rw [hℓ, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    exact ⟨1, by simp [hfix]⟩
  obtain ⟨v₁, hv₁⟩ := h.φ_surj (Multiplicative.ofAdd w₁)
  set w₂ : Fin 2 → k := B • w₁ - w₁ with hw₂
  have hw₂0 : w₂ ≠ 0 := sub_ne_zero.mpr hBw
  have hw₂T : w₂ ∈ T := by
    have hu : ⁅g, (v₁ : H)⁆ ∈ C := Subgroup.commutator_mem_commutator hgL v₁.2
    have hgv : g * (v₁ : H) * g⁻¹ ∈ V := hVn.conj_mem _ v₁.2 g
    have huV : ⁅g, (v₁ : H)⁆ ∈ V := by
      have : ⁅g, (v₁ : H)⁆ = (g * (v₁ : H) * g⁻¹) * (v₁ : H)⁻¹ := by
        simp only [commutatorElement_def]
      rw [this]
      exact mul_mem hgv (inv_mem v₁.2)
    refine ⟨⁅g, (v₁ : H)⁆, hu, huV, ?_⟩
    have e1 := h.φ_equiv g v₁ ⟨g * (v₁ : H) * g⁻¹, hgv⟩ rfl
    have e2 : (⟨⁅g, (v₁ : H)⁆, huV⟩ : V) = ⟨g * (v₁ : H) * g⁻¹, hgv⟩ * v₁⁻¹ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e2, map_mul, map_inv, toAdd_mul, toAdd_inv, e1, hv₁, hgB, slPerm_apply]
    simp [hw₂, sub_eq_add_neg]
  obtain ⟨A₁, hA₁⟩ := exists_smul_e0 hw₂0
  by_cases hw : w = 0
  · subst hw
    refine ⟨1, one_mem _, one_mem _, ?_⟩
    have h1 : (⟨1, one_mem V⟩ : V) = 1 := rfl
    rw [h1, map_one]
    rfl
  · obtain ⟨A₂, hA₂⟩ := exists_smul_e0 hw
    have e3 : (A₂ * A₁⁻¹) • w₂ = w := by
      rw [← hA₁, mul_smul, inv_smul_smul, hA₂]
    obtain ⟨u, hu, huV, huφ⟩ := hTinv (A₂ * A₁⁻¹) w₂ hw₂T
    rw [e3] at huφ
    exact ⟨u, hu, huV, huφ⟩

theorem V_le_baumannOvergroup (h : IsNatQuotSetting R M V ρ φ)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) : V ≤ baumannOvergroup R := by
  have hVn : V.Normal := h.normal_V
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  intro v hv
  obtain ⟨u, huC, huV, huφ⟩ := h.phi_commutator_surjective hJ
    (Multiplicative.toAdd (φ ⟨v, hv⟩))
  have hker : (⟨v, hv⟩ : V) * (⟨u, huV⟩ : V)⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have : φ ⟨u, huV⟩ = φ ⟨v, hv⟩ := Multiplicative.toAdd.injective huφ
    rw [this, mul_inv_cancel]
  rw [h.φ_ker, Subgroup.mem_subgroupOf] at hker
  have hvuV : v * u⁻¹ ∈ V := V.mul_mem hv (V.inv_mem huV)
  have hS : v * u⁻¹ ∈ elemBaumannIn 2 R :=
    h.inf_centralizer_le_elemBaumannIn hJ ⟨hvuV, hker⟩
  have hvu : v = (v * u⁻¹) * u := by group
  have hCL : u ∈ oddOrderSubgroup (⊤ : Subgroup H) := Subgroup.commutator_le_left _ _ huC
  rw [hvu]
  exact mul_mem (Subgroup.mem_sup_right hS) (Subgroup.mem_sup_left hCL)

@[expose] noncomputable def actualRho (h : IsNatQuotSetting R M V ρ φ)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    baumannOvergroup R →* Matrix.SpecialLinearGroup (Fin 2) k :=
  restrictSL ρ (baumannOvergroup R) (h.rho_mem_baumannOvergroup hJ)

@[expose] def actualPsi (h : IsNatQuotSetting R M V ρ φ) (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    V.subgroupOf (baumannOvergroup R) →* Multiplicative (Fin 2 → k) :=
  haveI : V.Normal := h.normal_V
  restrictPsi φ (baumannOvergroup R) (h.V_le_baumannOvergroup hJ)

@[expose] noncomputable def actualSylow (h : IsNatQuotSetting R M V ρ φ)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) : Sylow 2 (baumannOvergroup R) :=
  (h.isSylowIn_baumannOvergroup hJ).toSylow

theorem coe_actualSylow (h : IsNatQuotSetting R M V ρ φ) (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    ((h.actualSylow hJ : Sylow 2 (baumannOvergroup R)) : Subgroup (baumannOvergroup R)) =
      (elemBaumannIn 2 R).subgroupOf (baumannOvergroup R) :=
  IsSylowIn.coe_toSylow _

theorem slPerm_actualRho (h : IsNatQuotSetting R M V ρ φ) (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥)
    (x : baumannOvergroup R) :
    slPerm k (h.actualRho hJ x) = ((ρ (x : H) : Gamma k) : Equiv.Perm (Fin 2 → k)) :=
  slPerm_restrictSL ρ _ _ x

theorem ker_actualRho (h : IsNatQuotSetting R M V ρ φ) (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    (h.actualRho hJ).ker = ρ.ker.subgroupOf (baumannOvergroup R) :=
  ker_restrictSL ρ _ _

theorem actual_Baumann_whole_center_natural_module (h : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H)) (hnc : NoCharNormal R ⊤)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    IsSylowTwoOf (elemBaumannIn 2 R) (baumannOvergroup R) ∧ CharTwo (baumannOvergroup R) ∧
      NoCharNormal (elemBaumannIn 2 R) (baumannOvergroup R) ∧
      (baumannOvergroup R).map ρ = slGamma k ∧
      (ρ.ker.subgroupOf (baumannOvergroup R)).map
          (QuotientGroup.mk' (CFSG.pCore 2 (baumannOvergroup R))) =
        frattini (baumannOvergroup R ⧸ CFSG.pCore 2 (baumannOvergroup R)) ∧
      elemThompsonIn 2 (elemBaumannIn 2 R) = elemThompsonIn 2 R ∧
      IsSeed (h.actualSylow hJ) (h.actualRho hJ) (V.subgroupOf (baumannOvergroup R))
        (h.actualPsi hJ) ∧
      Ecore (baumannOvergroup R) = V.subgroupOf (baumannOvergroup R) ⊔
        (Ecore (baumannOvergroup R) ⊓ Subgroup.center (baumannOvergroup R)) ∧
      (∃ ψE : Ecore (baumannOvergroup R) →* Multiplicative (Fin 2 → k), Function.Surjective ψE ∧
        (∀ (g : baumannOvergroup R) (e e' : Ecore (baumannOvergroup R)),
          (e' : baumannOvergroup R) = g * e * g⁻¹ →
          Multiplicative.toAdd (ψE e') =
            (h.actualRho hJ g : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (ψE e))) ∧
        ψE.ker = (Ecore (baumannOvergroup R) ⊓ Subgroup.center (baumannOvergroup R)).subgroupOf
          (Ecore (baumannOvergroup R)) ∧
        ∀ (x : V.subgroupOf (baumannOvergroup R)) (e : Ecore (baumannOvergroup R)),
          (e : baumannOvergroup R) = x → ψE e = h.actualPsi hJ x) ∧
      (Kodd (baumannOvergroup R)).map (baumannOvergroup R).subtype =
        oddOrderSubgroup (⊤ : Subgroup H) ∧
      Vmod (baumannOvergroup R) =
        ⁅V.subgroupOf (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ := by
  classical
  have hVn : V.Normal := h.normal_V
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  have hVH := h.not_le_centralizer hJ
  obtain ⟨hHLR, -, hQC, -, -, -, -⟩ := minimal_parabolic_reduced_module_Frattini_kernel_production
    h.sylow h.nonnormal h.le_M h.M_lt h.M_max h.reduced hVH
  obtain ⟨h1, h2, h3, h4, hQ₀map, hQSeq, hfrat, -, h9, h10⟩ :=
    h.Baumann_Stellmacher_hypotheses hchar hnc hJ
  obtain ⟨ℓ, hsyl, -, hJρ, -, hρH₀, -, hcomm, -⟩ := h.Baumann_Sylow hJ
  have hRQ : R ⊓ ρ.ker = CFSG.pCore 2 H := h.inf_ker_eq hVH
  set L : Subgroup H := oddOrderSubgroup (⊤ : Subgroup H) with hLdef
  set S : Subgroup H := elemBaumannIn 2 R with hSdef
  set Q : Subgroup H := CFSG.pCore 2 H with hQdef
  set H₀ : Subgroup H := baumannOvergroup R with hH₀def
  have hSR : S ≤ R := elemBaumannIn_le 2 R
  have hLH₀ : L ≤ H₀ := le_sup_left
  have hSH₀ : S ≤ H₀ := le_sup_right
  have hVH₀ : V ≤ H₀ := h.V_le_baumannOvergroup hJ
  have hQker : Q ≤ ρ.ker := fun x hx => (hRQ ▸ hx : x ∈ R ⊓ ρ.ker).2
  have hJS : elemThompsonIn 2 R ≤ S := elemThompsonIn_le_elemBaumannIn 2 R
  have hJeq : elemThompsonIn 2 S = elemThompsonIn 2 R := elemThompsonIn_eq_of_le 2 hJS hSR
  have hQ₁ : ∀ x : H₀, x ∈ CFSG.pCore 2 ↥H₀ ↔ (x : H) ∈ Q := by
    intro x
    have hiff : (x : H) ∈ (CFSG.pCore 2 ↥H₀).map H₀.subtype ↔ (x : H) ∈ Q ⊓ H₀ := by
      rw [hQ₀map]
    constructor
    · intro hx
      exact (hiff.mp ⟨x, hx, rfl⟩).1
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hiff.mpr ⟨hx, x.2⟩
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ hy
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by
    have := h.reduced.2.2.1.2 (v : H) v.2
    apply Subtype.ext
    simpa using this⟩
  have hVQ : V ≤ Q := le_sSup ⟨hVn, hV2⟩
  have hVE : V.subgroupOf H₀ ≤ Ecore H₀ := by
    intro x hx
    have hxV : (x : H) ∈ V := hx
    rw [Ecore, mem_centerTorsion_iff]
    refine ⟨(hQ₁ x).mpr (hVQ hxV), fun q hq => ?_, ?_⟩
    · have hqQ : (q : H) ∈ Q := (hQ₁ q).mp hq
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hQC hqQ) (x : H) hxV).symm
    · exact Subtype.ext (by simpa using h.reduced.2.2.1.2 (x : H) hxV)
  have hρH₀' : H₀.map ρ = slGamma k := hρH₀
  have hmem := h.rho_mem_baumannOvergroup hJ
  have hseed : IsSeed (h.actualSylow hJ) (h.actualRho hJ) (V.subgroupOf H₀) (h.actualPsi hJ) := by
    refine
      { card_k := card_eq_two_pow (k := k)
        surj := restrictSL_surjective ρ H₀ hmem hρH₀'
        core_le := ?_
        frattini_le := ?_
        normal := inferInstance
        le_E := hVE
        ψ_surj := h.φ_surj.comp (Subgroup.subgroupOfEquivOfLe hVH₀).surjective
        ψ_equiv := ?_
        ψ_ker := ?_
        not_le := ?_ }
    · rw [ker_actualRho]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hQker ((hQ₁ x).mp hx))
    · rw [ker_actualRho]
      exact hfrat.le
    · intro g x x' hx
      have := h.φ_equiv (g : H) ⟨((x : H₀) : H), x.2⟩ ⟨((x' : H₀) : H), x'.2⟩
        (congrArg Subtype.val hx)
      show Multiplicative.toAdd (φ ⟨((x' : H₀) : H), x'.2⟩) =
        (h.actualRho hJ g : Matrix (Fin 2) (Fin 2) k).mulVec
          (Multiplicative.toAdd (φ ⟨((x : H₀) : H), x.2⟩))
      rw [this]
      exact restrictSL_apply_smul ρ H₀ hmem g _
    · ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have hker : (⟨((x : H₀) : H), x.2⟩ : V) ∈ φ.ker := hx
        rw [h.φ_ker, Subgroup.mem_subgroupOf] at hker
        have hxE := h.inf_centralizer_le_elemCenterIn hJ ⟨x.2, hker⟩
        refine ⟨x.2, Subgroup.mem_center_iff.mpr ?_⟩
        have hLc : L ≤ Subgroup.centralizer ({((x : H₀) : H)} : Set H) := by
          intro l hl
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff.mp hy]
          exact (Subgroup.mem_centralizer_iff.mp hker l hl).symm
        have hSc : S ≤ Subgroup.centralizer ({((x : H₀) : H)} : Set H) := by
          intro s hs
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff.mp hy]
          exact (mem_elemBaumannIn_iff.mp hs).2 _ hxE
        have hH₀c : H₀ ≤ Subgroup.centralizer ({((x : H₀) : H)} : Set H) := sup_le hLc hSc
        intro g
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hH₀c g.2) _ rfl).symm)
      · intro hx
        have hxc := Subgroup.mem_center_iff.mp hx.2
        show φ ⟨((x : H₀) : H), x.2⟩ = 1
        have : (⟨((x : H₀) : H), x.2⟩ : V) ∈ φ.ker := by
          rw [h.φ_ker, Subgroup.mem_subgroupOf]
          rw [Subgroup.mem_centralizer_iff]
          intro l hl
          exact congrArg Subtype.val (hxc ⟨l, hLH₀ hl⟩)
        exact this
    · intro hle
      have hS₀ : ((h.actualSylow hJ : Sylow 2 ↥H₀) : Subgroup ↥H₀) = S.subgroupOf H₀ :=
        h.coe_actualSylow hJ
      rw [hS₀] at hle
      have hJmap : (thompsonJ (S.subgroupOf H₀)).map H₀.subtype = elemThompsonIn 2 R := by
        have hbridge : thompsonJ (S.subgroupOf H₀) = elemThompsonIn 2 (S.subgroupOf H₀) :=
          (elemThompson_map_subtype_eq_thompsonJ (S.subgroupOf H₀)).symm
        rw [hbridge, ← elemThompsonIn_map_of_injective 2 H₀.subtype H₀.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le hSH₀, hJeq]
      have hJQ : elemThompsonIn 2 R ≤ Q := by
        rw [← hJmap]
        intro y hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact ((hQ₁ z).mp (hle hz))
      have hbot : (elemThompsonIn 2 R).map ρ = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        exact fun y hy => hQker (hJQ hy)
      rw [hJρ] at hbot
      have hcard := card_rootGamma (k := k) ℓ
      rw [hbot, Subgroup.card_bot] at hcard
      have : 1 < Nat.card k := Finite.one_lt_card
      omega
  obtain ⟨hEeq, ⟨ψE, hψEs, hψEq, hψEk, hψEx⟩, -⟩ :=
    hseed.natural_seed_exhausts_elementary_core_center
  have hKodd : (Kodd H₀).map H₀.subtype = L := by
    have hLclosure : L = Subgroup.closure {x : H | Nat.Coprime (orderOf x) 2} := by
      rw [hLdef, oddOrderSubgroup]
      congr 1
      ext x
      simp [Nat.coprime_two_right]
    have hset : (H₀.subtype '' {x : H₀ | x ∈ (⊤ : Subgroup H₀) ∧ (orderOf x).Coprime 2}) =
        {x : H | Nat.Coprime (orderOf x) 2} := by
      ext y
      constructor
      · rintro ⟨x, ⟨-, hx⟩, rfl⟩
        simpa [Subgroup.orderOf_coe] using hx
      · intro hy
        have hyL : y ∈ L := by
          rw [hLclosure]
          exact Subgroup.subset_closure hy
        refine ⟨⟨y, hLH₀ hyL⟩, ⟨trivial, ?_⟩, rfl⟩
        simpa [Subgroup.orderOf_coe] using hy
    unfold Kodd pPrimeGen
    rw [MonoidHom.map_closure, hset, ← hLclosure]
  have hVmod : Vmod H₀ = ⁅V.subgroupOf H₀, Kodd H₀⁆ := by
    apply le_antisymm
    · unfold Vmod
      rw [hEeq]
      refine commutator_sup_of_commute (fun x _ y hy => ?_) (fun y hy w _ => ?_)
      · exact (Subgroup.mem_center_iff.mp hy.2 x)
      · exact (Subgroup.mem_center_iff.mp hy.2 w).symm
    · exact Subgroup.commutator_mono hVE le_rfl
  refine ⟨h1, h3, h10, hρH₀', hfrat, hJeq, hseed, hEeq, ⟨ψE, hψEs, hψEq, hψEk, ?_⟩, hKodd, hVmod⟩
  intro x e hex
  have := hψEx x
  rw [← this]
  congr 1
  exact Subtype.ext hex

end IsNatQuotSetting

end Facts

end CFSG.QuasithinUnique.Setup.Campbell
