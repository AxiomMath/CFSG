module

public import CFSG.LocalAnalysis.ComponentClassification.BMCaseJbar
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseTwoCentralizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.ComponentClassification.OuterAutomorphisms

theorem DQ_mul_DQ (δ ε : Cocode) : DQ δ * DQ ε = DQ (δ + ε) := by
  rw [DQ_eq, DQ_eq, DQ_eq, ← map_mul]
  congr 1
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, pair_zero_left, add_zero]
  · simp only [SpinCoord.mul_a, add_zero]
  · simp only [SpinCoord.mul_δ]

@[expose] def e0Cocode : Cocode := Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2))

theorem rho_e0_mem_Jstar : rhoEquiv (DQ e0Cocode) ∈ Jstar := by
  refine ⟨odd_cocode_inverts_triality.2.2.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hc : DQ e0Cocode * rStar = rStar * DQ e0Cocode := by
    change DQ e0Cocode * DQ (deltaPair 0 1) = DQ (deltaPair 0 1) * DQ e0Cocode
    rw [DQ_mul_DQ, DQ_mul_DQ, add_comm]
  exact rho_commute hc

@[expose] def hC : Cgen := ⟨rhoEquiv (DQ e0Cocode), Jstar_le_Cgen rho_e0_mem_Jstar⟩

@[expose] def hbar : Cbar := kappa hC

theorem hbar_mem_Jbar : hbar ∈ Jbar :=
  ⟨hC, Subgroup.mem_subgroupOf.2 rho_e0_mem_Jstar, rfl⟩

theorem hbar_conj_mul : hbar * (taubar * hbar * taubar⁻¹) = taubar := by
  have h : hC * (tauC * hC * tauC⁻¹) = tauC :=
    Subtype.ext odd_cocode_inverts_triality.2.2.2.1
  have := congrArg kappa h
  rwa [map_mul, map_mul, map_mul, map_inv] at this

theorem closure_Jbar_taubar : Subgroup.closure ((Jbar : Set Cbar) ∪ {taubar}) = ⊤ := by
  have hS : Subgroup.closure (((↑) : Cgen → SpaceB ≃ₗ[ℚ] SpaceB) ⁻¹'
      (insert tauB (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB)))) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hmap : (Subgroup.closure (((↑) : Cgen → SpaceB ≃ₗ[ℚ] SpaceB) ⁻¹'
      (insert tauB (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB))))).map kappa ≤
        Subgroup.closure ((Jbar : Set Cbar) ∪ {taubar}) := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with hg | hg
    · have hgt : g = tauC := Subtype.ext hg
      rw [hgt]
      exact Subgroup.subset_closure (Or.inr rfl)
    · exact Subgroup.subset_closure (Or.inl ⟨g, Subgroup.mem_subgroupOf.2 hg, rfl⟩)
  rw [eq_top_iff]
  intro c _
  obtain ⟨g, rfl⟩ := kappa_surjective c
  exact hmap ⟨g, hS ▸ Subgroup.mem_top g, rfl⟩

theorem conj_mem_zpowers_iff_mem_Ebar {h : Cbar} (hh : h ∈ Jbar) :
    (∀ q ∈ Ebar, h * q * h⁻¹ * q⁻¹ ∈ Subgroup.zpowers xbar) ↔ h ∈ Ebar := by
  constructor
  · intro hq
    have hJ := mem_ebarJ_of_conj ⟨h, hh⟩ fun q hqE => by
      rw [map_center_ebarJ]
      have h1 := hq q (Subgroup.mem_subgroupOf.1 hqE)
      rw [← map_subtype_zpowers_xJ] at h1
      obtain ⟨y, hy, hye⟩ := h1
      have : y = ⟨h, hh⟩ * q * (⟨h, hh⟩ : Jbar)⁻¹ * q⁻¹ := Subtype.ext (by simpa using hye)
      exact this ▸ hy
    exact Subgroup.mem_subgroupOf.1 hJ
  · intro hE q hq
    have hc : (⟨h, hE⟩ : Ebar) * ⟨q, hq⟩ * (⟨h, hE⟩ : Ebar)⁻¹ * (⟨q, hq⟩ : Ebar)⁻¹ ∈
        Subgroup.center Ebar := by
      rw [← Ebar_extraspecial.1.2.1]
      have := Subgroup.commutator_mem_commutator (G := Ebar) (Subgroup.mem_top (⟨h, hE⟩ : Ebar))
        (Subgroup.mem_top ⟨q, hq⟩)
      rwa [commutatorElement_def] at this
    rw [← map_center_Ebar]
    exact ⟨_, hc, rfl⟩

@[expose] def centXbarEquiv : Subgroup.centralizer ({xbar} : Set Cbar) ≃* Jbar :=
  MulEquiv.subgroupCongr centralizer_xbar

theorem cbar_inner : ∀ α : MulAut Cbar, ∃ g : Cbar, α = MulAut.conj g := by
  have hQH : Ebar ≤ Subgroup.centralizer ({xbar} : Set Cbar) := centralizer_xbar ▸ Ebar_le_Jbar
  have hQn : (Ebar.subgroupOf (Subgroup.centralizer ({xbar} : Set Cbar))).Normal := by
    rw [centralizer_xbar]
    infer_instance
  have hCQ : Subgroup.centralizer ({xbar} : Set Cbar) ⊓ Subgroup.centralizer (Ebar : Set Cbar) =
      Subgroup.zpowers xbar := by
    rw [centralizer_xbar]
    exact centralizer_Ebar
  have hker : ∀ h ∈ Subgroup.centralizer ({xbar} : Set Cbar),
      (∀ q ∈ Ebar, h * q * h⁻¹ * q⁻¹ ∈ Subgroup.zpowers xbar) ↔ h ∈ Ebar := fun h hh =>
    conj_mem_zpowers_iff_mem_Ebar (centralizer_xbar ▸ hh)
  have hautH : ∀ β : MulAut (Subgroup.centralizer ({xbar} : Set Cbar)), ∃ h, β = MulAut.conj h :=
    inner_of_equiv centXbarEquiv jbar_perfect_and_inner.2
  have hgen : Subgroup.closure
      ((Subgroup.centralizer ({xbar} : Set Cbar) : Set Cbar) ∪ {taubar}) = ⊤ := by
    rw [centralizer_xbar]
    exact closure_Jbar_taubar
  exact global_inner_of_centralizer orderOf_xbar hQH hQn Ebar_extraspecial.1 map_center_Ebar hCQ
    hker hautH conj_xbar_mem_Ebar conj_xbar_not_mem_zpowers hgen
    (centralizer_xbar ▸ hbar_mem_Jbar) hbar_conj_mul

theorem native_B_generated_quotient_Schreier : Group.IsSolvable (Outer Cbar) :=
  isSolvable_outer_of_inner cbar_inner

theorem isPGroup_ebarJ : IsPGroup 2 (Ebar.subgroupOf Jbar) :=
  IsPGroup.of_card ((Nat.card_congr ebarJEquiv.toEquiv).trans Ebar_extraspecial.2)

theorem natCard_jbarQuot : Nat.card (Jbar ⧸ Ebar.subgroupOf Jbar) = 42305421312000 :=
  (Nat.card_congr jbarQuotKvEquiv.toEquiv).trans Kstab_rStar_simple.2

theorem isSimpleGroup_jbarQuot : IsSimpleGroup (Jbar ⧸ Ebar.subgroupOf Jbar) :=
  @MulEquiv.isSimpleGroup _ _ _ _ Kstab_rStar_simple.1 jbarQuotKvEquiv

theorem center_jbarQuot : Subgroup.center (Jbar ⧸ Ebar.subgroupOf Jbar) = ⊥ := by
  have := isSimpleGroup_jbarQuot
  exact center_eq_bot_of_isSimpleGroup
    (exists_mul_ne_mul_of_not_prime (by rw [natCard_jbarQuot]; norm_num))

theorem native_B_visible_centralizer_Schreier :
    Group.IsSolvable (Outer Jbar) ∧
      (∀ α : MulAut Jbar, ∃ g : Jbar, ∃ r ∈ quotKerAut (Ebar.subgroupOf Jbar),
        α = MulAut.conj g * r) ∧
      ∃ F : Subgroup (quotKerAut (Ebar.subgroupOf Jbar)), ∃ _ : F.Normal, IsPGroup 2 F ∧
        IsPGroup 3 (quotKerAut (Ebar.subgroupOf Jbar) ⧸ F) :=
  ⟨isSolvable_outer_of_inner jbar_perfect_and_inner.2,
    quotKerAut_of_inner isPGroup_ebarJ center_jbarQuot jbar_perfect_and_inner.2⟩

end CFSG.ComponentClassification.BMCase
