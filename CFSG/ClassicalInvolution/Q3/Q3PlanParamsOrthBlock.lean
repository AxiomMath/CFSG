module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsOrthLow
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsOrthComp
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthElem
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open (IsSubnormal)
open QuadraticMap TauCeti.QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalGroups.Orthogonal.Small (HasAnisoPerp hasAnisoPerp_of_three_le_finrank
  mem_scalars_of_commute_eichler nondegenerate_comp_subtype)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Orth (elemOn layerGenOn resAux
  eichler_mem_elemOn conj_mem_elemOn resAux_eichler support_of_mem_elemOn elemOn_le_elementaryGroup
  comm_of_scalar_elemOn)
open CFSG.ClassicalInvolution.ModelFacts (plusSp minusSp mem_plusSp mem_minusSp
  isCompl_plusSp_minusSp polar_plusSp_minusSp map_mem_plusSp map_mem_minusSp
  inv_mul_eq_mul_inv_of)
open CFSG.ComponentClassification.CatalogueBOddQuadratic (exists_isotropic_of_three_le
  two_ne_zero_of_odd_card)

section Restriction

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] noncomputable def blockRes (S : Submodule F V) (C : Subgroup (V ≃ₗ[F] V))
    (hC : ∀ g ∈ C, ∀ x, x ∈ S ↔ g x ∈ S) : ↥C →* (S ≃ₗ[F] S) where
  toFun g := resAux g.1 (hC g g.2)
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

theorem coe_blockRes (S : Submodule F V) (C : Subgroup (V ≃ₗ[F] V))
    (hC : ∀ g ∈ C, ∀ x, x ∈ S ↔ g x ∈ S) (g : ↥C) (s : S) :
    ((blockRes S C hC g s : S) : V) = g.1 s := rfl

end Restriction

section Scalar

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {S : Submodule F V}

theorem resAux_mem_scalars_of_commute_elemOn [Finite F] (hodd : Odd (Nat.card F))
    (hS : (polarBilin (Q.restrict S)).Nondegenerate) (h3 : 3 ≤ Module.finrank F S)
    {g : V ≃ₗ[F] V} (hg : g ∈ orthogonalGroup Q) (hgS : ∀ x, x ∈ S ↔ g x ∈ S)
    (hcomm : ∀ h ∈ elemOn Q S, g * h = h * g) : resAux g hgS ∈ scalars F S := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hA : HasAnisoPerp (Q.restrict S) := hasAnisoPerp_of_three_le_finrank hS h3
  obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_three_le hodd (Q.restrict S) hS h3
  obtain ⟨P, -⟩ := exists_hypPair hS hvQ hv0
  refine mem_scalars_of_commute_eichler h2 hS hA P
    (mem_orthogonalGroup_iff.mpr fun s => mem_orthogonalGroup_iff.mp hg (s : V)) ?_
  intro u w _ _
  have hE : eichler Q (u : V) (w : V) ∈ elemOn Q S := eichler_mem_elemOn u.2 w.2
  have hES := (support_of_mem_elemOn hE).1
  have h1 : resAux (eichler Q (u : V) (w : V)) hES = eichler (Q.restrict S) u w :=
    resAux_eichler u.2 w.2
  have hgE := hcomm _ hE
  have hx1 : ∀ y : S, ((eichler (Q.restrict S) u w y : S) : V) =
      eichler Q (u : V) (w : V) (y : V) := fun y =>
    (congrArg Subtype.val (LinearEquiv.congr_fun h1 y)).symm
  refine LinearEquiv.ext fun x => Subtype.ext ?_
  change g ((eichler (Q.restrict S) u w x : S) : V) =
    ((eichler (Q.restrict S) u w (resAux g hgS x) : S) : V)
  rw [hx1 x, hx1 (resAux g hgS x)]
  exact LinearEquiv.congr_fun hgE (x : V)

end Scalar

section Block

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {S : Submodule F V}

theorem commute_on_block (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hS : (polarBilin (Q.restrict S)).Nondegenerate) {C : Subgroup (V ≃ₗ[F] V)}
    (hCO : C ≤ orthogonalGroup Q) (hCS : ∀ g ∈ C, ∀ x, x ∈ S ↔ g x ∈ S)
    (hEC : elemOn Q S ≤ C) {M : Subgroup (V ≃ₗ[F] V)} (hMs : IsSubnormal M C)
    (hsolv : Group.IsSolvable M) (hodd' : IsOddGenerated M) :
    ∀ x ∈ M, ∀ y ∈ M, ∀ v ∈ S, x (y v) = y (x v) := by
  have hMC : M ≤ C := CFSG.ClassicalInvolution.isSubnormal_le hMs
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  by_cases h3 : 3 ≤ Module.finrank F S
  · obtain ⟨𝓗, h𝓗, hcover⟩ := layerGenOn hodd h5 hS h3
    have hEn : ∀ c ∈ C, ∀ e ∈ elemOn Q S, c * e * c⁻¹ ∈ elemOn Q S := fun c hc e he =>
      conj_mem_elemOn (hCO hc) (hCS c hc) he
    have hcomm : ∀ x ∈ M, ∀ h ∈ elemOn Q S, x * h = h * x := by
      intro x hx
      have hle : elemOn Q S ≤ Subgroup.centralizer ({x} : Set (V ≃ₗ[F] V)) := by
        refine hcover.trans (iSup₂_le fun H hH => ?_)
        obtain ⟨hHE, hHq, hHn⟩ := h𝓗 H hH
        intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commute_of_isSubnormal_of_isSolvable_of_normal hHq hHE hHn hEC hEn hMs hsolv x hx
          a ha).symm
      intro h hh
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hh)).symm
    intro x hx y hy v hv
    obtain ⟨c, hc⟩ := mem_scalars.mp (resAux_mem_scalars_of_commute_elemOn hodd hS h3
      (hCO (hMC hx)) (hCS x (hMC hx)) (hcomm x hx))
    have hxv : ∀ s ∈ S, x s = c • s := fun s hs => congrArg Subtype.val (hc ⟨s, hs⟩)
    have hyv : y v ∈ S := (hCS y (hMC hy) v).mp hv
    rw [hxv _ hyv, hxv v hv, map_smul]
  · have hdim : Module.finrank F S ≤ 2 := by omega
    have key := commute_map_of_isOddGenerated h2 hS hdim (blockRes S C hCS)
      (fun g => mem_orthogonalGroup_iff.mpr fun s => mem_orthogonalGroup_iff.mp (hCO g.2) (s : V))
      (isOddGenerated_subgroupOf hMC hodd')
    intro x hx y hy v hv
    have hxy := key ⟨x, hMC hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hMC hy⟩
      (Subgroup.mem_subgroupOf.mpr hy)
    exact congrArg Subtype.val (LinearEquiv.congr_fun hxy ⟨v, hv⟩)

theorem commute_of_isSubnormal_centralizer_involution (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q).Nondegenerate) {Ω : Subgroup (V ≃ₗ[F] V)}
    (hΩO : Ω ≤ orthogonalGroup Q) (hΩE : elementaryGroup Q ≤ Ω) {i : V ≃ₗ[F] V}
    (hiO : i ∈ orthogonalGroup Q) (hii : i * i = 1) {M : Subgroup (V ≃ₗ[F] V)}
    (hMs : IsSubnormal M (Ω ⊓ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V))))
    (hsolv : Group.IsSolvable M) (hodd' : IsOddGenerated M) :
    ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hc := isCompl_plusSp_minusSp h2 hii
  have hCO : Ω ⊓ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)) ≤ orthogonalGroup Q :=
    fun g hg => hΩO hg.1
  have hCi : ∀ g ∈ Ω ⊓ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)), g * i = i * g :=
    fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg.2
  have hCP : ∀ g ∈ Ω ⊓ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)), ∀ x,
      x ∈ plusSp i ↔ g x ∈ plusSp i := fun g hg x =>
    ⟨fun hx => map_mem_plusSp (hCi g hg) hx, fun hx => by
      simpa using map_mem_plusSp (inv_mul_eq_mul_inv_of (hCi g hg)) hx⟩
  have hCM : ∀ g ∈ Ω ⊓ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)), ∀ x,
      x ∈ minusSp i ↔ g x ∈ minusSp i := fun g hg x =>
    ⟨fun hx => map_mem_minusSp (hCi g hg) hx, fun hx => by
      simpa using map_mem_minusSp (inv_mul_eq_mul_inv_of (hCi g hg)) hx⟩
  have hPn : (polarBilin (Q.restrict (plusSp i))).Nondegenerate :=
    nondegenerate_comp_subtype hQ hc fun u hu w hw => polar_plusSp_minusSp h2 hiO hu hw
  have hMn : (polarBilin (Q.restrict (minusSp i))).Nondegenerate :=
    nondegenerate_comp_subtype hQ hc.symm fun u hu w hw => by
      rw [polar_comm]
      exact polar_plusSp_minusSp h2 hiO hw hu
  have hEP : elemOn Q (plusSp i) ≤ Ω ⊓ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)) :=
    fun h hh => ⟨hΩE (elemOn_le_elementaryGroup hh), Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_scalar_elemOn hiO (ε := 1) (by simp) (fun x hx => by
        rw [mem_plusSp.mp hx, one_smul]) hh).symm⟩
  have hEM : elemOn Q (minusSp i) ≤ Ω ⊓ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)) :=
    fun h hh => ⟨hΩE (elemOn_le_elementaryGroup hh), Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_scalar_elemOn hiO (ε := -1) (by simp) (fun x hx => by
        rw [mem_minusSp.mp hx, neg_one_smul]) hh).symm⟩
  have hbP := commute_on_block hodd h5 hPn hCO hCP hEP hMs hsolv hodd'
  have hbM := commute_on_block hodd h5 hMn hCO hCM hEM hMs hsolv hodd'
  intro x hx y hy
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ plusSp i ⊔ minusSp i := by
    rw [hc.sup_eq_top]
    trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_add, map_add, map_add, map_add,
    hbP x hx y hy a ha, hbM x hx y hy b hb]

end Block

end CFSG.ClassicalInvolution.Q3
