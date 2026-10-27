module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBLift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphTools
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4BurgDc

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.BurgD

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne
open CFSG.ComponentClassification.Burgoyne.B CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U
open scoped MatrixGroups

theorem eq_of_projH_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H : Subgroup (GL ι K)} (hH : Group.IsPerfect H) (f₁ f₂ : H →* H)
    (hf : ∀ g, projH H (f₁ g) = projH H (f₂ g)) (g : H) : f₁ g = f₂ g := by
  have hz : ∀ g, (f₂ g)⁻¹ * f₁ g ∈ center H := fun g =>
    scalars_subgroupOf_le_center (projH_eq_projH_iff.1 (hf g).symm)
  let z : H →* center H :=
    { toFun := fun g => ⟨(f₂ g)⁻¹ * f₁ g, hz g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (f₂ (a * b))⁻¹ * f₁ (a * b) = ((f₂ a)⁻¹ * f₁ a) * ((f₂ b)⁻¹ * f₁ b)
        rw [map_mul, map_mul, _root_.mul_inv_rev]
        have hc := mem_center_iff.1 (hz a) (f₂ b)⁻¹
        calc (f₂ b)⁻¹ * (f₂ a)⁻¹ * (f₁ a * f₁ b) = ((f₂ b)⁻¹ * ((f₂ a)⁻¹ * f₁ a)) * f₁ b := by
              group
          _ = (((f₂ a)⁻¹ * f₁ a) * (f₂ b)⁻¹) * f₁ b := by rw [hc]
          _ = ((f₂ a)⁻¹ * f₁ a) * ((f₂ b)⁻¹ * f₁ b) := by group) }
  have hle : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ z.ker := by
    rw [commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact mem_center_iff.1 (z b).2 (z a))
  have htop : ⁅(⊤ : Subgroup H), ⊤⁆ = ⊤ := hH.commutator_eq_top
  have hz1 : z g = 1 := hle (htop.symm ▸ mem_top g)
  have h1 : (f₂ g)⁻¹ * f₁ g = 1 := congrArg Subtype.val hz1
  exact (inv_mul_eq_one.1 h1).symm

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)

theorem center_statedSU [Finite F] [Fact p.Prime] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    center (StatedSU 4 (p ^ f) F) =
      (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (p ^ f) F) :=
  (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF (by norm_num)
    (fun e => by
      have h2 : p ^ f = 2 := (Prod.mk.inj e).2
      have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
      rw [h2] at hodd
      exact (by decide : ¬ Odd 2) hodd)).2

@[expose] noncomputable def uDescend [Finite F] [Fact p.Prime] (hF : Nat.card F = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) (γ : MulAut (StatedSU 4 (p ^ f) F)) :
    MulAut (StatedProj (StatedSU 4 (p ^ f) F)) :=
  QuotientGroup.congr _ _ γ (by rw [← center_statedSU hF hp2]; exact map_center_eq γ)

theorem uDescend_proj [Finite F] [Fact p.Prime] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (γ : MulAut (StatedSU 4 (p ^ f) F)) (g : StatedSU 4 (p ^ f) F) :
    uDescend hF hp2 γ (projH _ g) = projH _ (γ g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

theorem eq_uLift [Finite F] [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (γ : MulAut (StatedSU 4 (p ^ f) F)) {B : uU h 4} {φ : F ≃+* F}
    (hγ : uDescend h.card_eq_sq hp2 γ = uConjAut h (by norm_num) B * uFieldAut h (by norm_num) φ)
    (g : StatedSU 4 (p ^ f) F) : γ g = uLift h B φ g := by
  have hperf : Group.IsPerfect (StatedSU 4 (p ^ f) F) :=
    (isQuasisimple_statedSU_of_two_le hp2 h.card_eq_sq (k := 4) (by norm_num)
      (Or.inl (by norm_num))).1
  exact eq_of_projH_eq hperf γ.toMonoidHom (uLift h B φ) (fun g => by
    change projH _ (γ g) = _
    rw [← uDescend_proj h.card_eq_sq hp2, hγ, uLift_proj]) g

variable {K : Type} [Field K]

theorem inner_trivial_gen {G₀ L : Type*} [Group G₀] [Group L] [Finite L] (e : G₀ ≃* L)
    (ι₀ : G₀ →* Matrix (Fin 4) (Fin 4) K) (h2 : (2 : K) ≠ 0) {J : Finset (Fin 4)}
    (hJ : Odd J.card) {Q : Subgroup L} {F₁ : Type*} [Field F₁] (h2F : (2 : F₁) ≠ 0)
    (e₁ : Q ⧸ pPrimeCore 2 Q ≃* SL(2, F₁)) {γ : L → L}
    (hγ : ∀ g, ι₀ (e.symm (γ (e g))) = PSL.signMat K J * ι₀ g * PSL.signMat K J)
    (hγQ : ∀ a ∈ Q, γ a ∈ Q) (B : GL (Fin 4) K)
    (hBS : (B : Matrix (Fin 4) (Fin 4) K) * PSL.signMat K J = PSL.signMat K J * B) {l : K}
    (hl : (B : Matrix (Fin 4) (Fin 4) K) * B = l • 1)
    (hns : ∀ c : K, (B : Matrix (Fin 4) (Fin 4) K) ≠ c • 1)
    (hQB : ∀ a ∈ Q, ι₀ (e.symm a) * B = B * ι₀ (e.symm a))
    {g₀ : G₀} (hg₀ : ι₀ g₀ = -1) (hg₀2 : orderOf g₀ = 2) (hcQ : e g₀ ∈ Q) :
    ∀ a ∈ Q, γ a * a⁻¹ ∈ (pPrimeCore 2 Q).map Q.subtype := by
  have hdet : IsUnit (B : Matrix (Fin 4) (Fin 4) K).det :=
    ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit)
  obtain ⟨P, ε, hP, hP0, hε, hSP, -, hcomm⟩ := exists_proj h2 hJ hBS hl hdet hns
  set ι : Q →* Matrix (Fin 4) (Fin 4) K := ι₀.comp (e.symm.toMonoidHom.comp Q.subtype) with hιdef
  have hιa : ∀ a : Q, ι a = ι₀ (e.symm a) := fun a => rfl
  have hι : ∀ a, ι a * P = P * ι a := fun a => by rw [hιa]; exact hcomm _ (hQB a a.2)
  refine mul_inv_mem_of_rep h2F e₁ hγQ (projHom ι hP hι) (fun a ha => ?_) hcQ ?_ ?_
  · rw [projHom_apply, projHom_apply, hιa, hιa]
    congr 1
    change ι₀ (e.symm (γ a)) * P = _
    have h1 : ι₀ (e.symm (γ a)) = PSL.signMat K J * ι₀ (e.symm a) * PSL.signMat K J := by
      have := hγ (e.symm a)
      rwa [e.apply_symm_apply] at this
    rw [h1]
    exact sign_conj_mul_proj hε hSP (hcomm _ (hQB _ ha))
  · rw [MulEquiv.orderOf_eq]
    exact hg₀2
  · rw [projHom_apply, hιa]
    change ι₀ (e.symm (e g₀)) * P + (1 - P) ≠ 1
    rw [e.symm_apply_apply, hg₀, neg_one_mul]
    intro h'
    apply hP0
    have h'' : (2 : K) • P = 0 := by
      rw [two_smul]
      have := congrArg (fun M => 1 - M) h'
      simp only [sub_self] at this
      rw [← this]
      abel
    exact (smul_eq_zero.1 h'').resolve_left h2

theorem sq_eq_sq_of_commute_graph (h2 : (2 : F) ≠ 0) {J : Finset (Fin 4)} (hJ : Odd J.card)
    (B : uU h 4) (α β : Fˣ) (hα : h.norm (α : F) = 1) (hβ : h.norm (β : F) = 1)
    (hαβ : (α : F) ≠ β)
    (hc : uConjAut h (by norm_num) (uDiagJ h J α β hα hβ) *
        (uConjAut h (by norm_num) B * uFieldAut h (by norm_num) (barEq h)) =
      (uConjAut h (by norm_num) B * uFieldAut h (by norm_num) (barEq h)) *
        uConjAut h (by norm_num) (uDiagJ h J α β hα hβ)) :
    (α : F) * α = β * β := by
  obtain ⟨κ, hκ⟩ := exists_scalar_of_commute_graph h (by norm_num) hc
  have hα0 : (α : F) ≠ 0 := α.ne_zero
  have hβ0 : (β : F) ≠ 0 := β.ne_zero
  have hbarα : h.bar (α : F) = (α : F)⁻¹ := by
    rw [UnitaryFieldData.norm] at hα
    exact eq_inv_of_mul_eq_one_right hα
  have hbarβ : h.bar (β : F) = (β : F)⁻¹ := by
    rw [UnitaryFieldData.norm] at hβ
    exact eq_inv_of_mul_eq_one_right hβ
  have hDbar : ((uDiagJ h J α β hα hβ : uU h 4) : GL (Fin 4) F).val.map h.bar =
      diagonal fun i => if i ∈ J then (α : F)⁻¹ else (β : F)⁻¹ := by
    change (diagonal fun i => if i ∈ J then (α : F) else β).map h.bar = _
    rw [diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs
    · exact hbarα
    · exact hbarβ
  rw [hDbar, coe_uDiagJ] at hκ
  set Bm : Matrix (Fin 4) (Fin 4) F := ((B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hBm
  set Bi : Matrix (Fin 4) (Fin 4) F := (((B : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) with hBi
  have hBBi : Bm * Bi = 1 := by rw [hBm, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hκ0 : (κ : F) ≠ 0 := κ.ne_zero
  set D : Matrix (Fin 4) (Fin 4) F := diagonal fun i => if i ∈ J then (α : F) else β with hD
  set D' : Matrix (Fin 4) (Fin 4) F := diagonal fun i => if i ∈ J then (α : F)⁻¹ else (β : F)⁻¹
    with hD'
  have h5 : Bm * D' * Bi = ((κ : F)⁻¹) • D := by
    have e1 : Bm * D' = ((κ : F)⁻¹) • (D * Bm) := by
      rw [hκ, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
    rw [e1, Matrix.smul_mul, Matrix.mul_assoc, hBBi, Matrix.mul_one]
  have hinv : (α : F)⁻¹ ≠ (β : F)⁻¹ := fun h' => hαβ (inv_injective h')
  obtain ⟨ha, hb⟩ := spectral h2 hJ hinv hαβ (B : GL (Fin 4) F) h5
  have hca : (κ : F)⁻¹ * α * α = 1 := by rw [ha, inv_mul_cancel₀ hα0]
  have hcb : (κ : F)⁻¹ * β * β = 1 := by rw [hb, inv_mul_cancel₀ hβ0]
  apply mul_left_cancel₀ (inv_ne_zero hκ0)
  rw [← mul_assoc, ← mul_assoc, hca, hcb]

end CFSG.ComponentClassification.CatFactsL4U4.BurgD
