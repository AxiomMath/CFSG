module

public import CFSG.ClassicalInvolution.Q3.Q3SPN3Lift
public import CFSG.ClassicalInvolution.Q3.Q3SPN3Stmt
public import CFSG.ClassicalInvolution.Asc77.AscSPN12
public import CFSG.ClassicalInvolution.Asc77.AscT7PF
public import CFSG.ClassicalInvolution.Q3.Q3PBranch
public import CFSG.ClassicalInvolution.Q3.Q3WStd

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3SPN3

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.SPN CFSG.ClassicalInvolution.Balance
open scoped commutatorElement MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Generation

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)}

theorem spinGroup_eq_fixed_sup_centralizer3 (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c)
    (fr : OFrame Q) (hV : 7 ≤ Module.finrank F (ι → F)) {x : spinGroup Q}
    (hx : spinAction Q x = fr.La (-1)) (α : spinGroup Q ≃* spinGroup Q)
    {w : (ι → F) ≃ₗ[F] (ι → F)} (hwiso : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hww : w * w = 1) (hwspan : ∀ y ∈ fr.span, w y = y)
    (hθw : ∀ y, spinAction Q (α y) = w * spinAction Q y * w⁻¹) (hM : minusSp w ≠ ⊥)
    (hN : plusSp w ⊓ fr.perp ≠ ⊥) :
    fixedGroup α ⊔ Subgroup.centralizer ({x} : Set (spinGroup Q)) = ⊤ := by
  classical
  have hθker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have h₁ : elemOn Q (plusSp w) ≤ (fixedGroup α).map (spinAction Q) :=
    elemOn_le_map_fixedGroup3 hF3 hrange hZ3 α hθw
      (fun n hn => comm_of_scalar_elemOn hwiso (by simp : (1 : F) * 1 = 1)
        (fun y hy => by rw [mem_plusSp.mp hy, one_smul]) hn)
  have hθxO : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hx]
    exact fr.La_mem_orthogonalGroup (-1)
  have h₂ : elemOn Q fr.perp ≤
      (Subgroup.centralizer ({x} : Set (spinGroup Q))).map (spinAction Q) :=
    elemOn_le_map_centralizer3 hF3 hrange hZ3 hθxO
      (fun y hy => by rw [hx]; exact La_neg_one_of_mem_perp fr hy)
  have hHO : (fixedGroup α ⊔ Subgroup.centralizer ({x} : Set (spinGroup Q))).map
      (spinAction Q) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨y, -, rfl⟩
    have : spinAction Q y ∈ (spinAction Q).range := ⟨y, rfl⟩
    rw [hrange] at this
    exact elementaryGroup_le_orthogonalGroup Q this
  have hE : (spinAction Q).range ≤ (fixedGroup α ⊔
      Subgroup.centralizer ({x} : Set (spinGroup Q))).map (spinAction Q) := by
    rw [hrange]
    exact elementaryGroup_le_of_involution hodd hQ fr hwiso hww hwspan hV hM hN hHO
      (h₁.trans (Subgroup.map_mono le_sup_left)) (h₂.trans (Subgroup.map_mono le_sup_right))
  exact eq_top_of_range_le_map (spinAction Q) hθker hE

end Generation

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem spinGen_core3 (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c)
    (fr : OFrame Q) (hV : 7 ≤ Module.finrank F (ι → F)) {ψ : spinGroup Q →* H}
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) {x : spinGroup Q}
    (hx : spinAction Q x = fr.La (-1)) (s : H) (hs : s ∈ Subgroup.normalizer (ψ.range : Set H))
    (hss : s * s = 1)
    (hlift : LiftSimAt Q ψ (toInducedAutOn ψ.range ⟨s, hs⟩ : MulAut ↥ψ.range))
    (hv : ∀ g : spinGroup Q, spinAction Q g ∈ fr.La.range ⊔ fr.swap.La.range →
      toInducedAutOn ψ.range ⟨s, hs⟩ * toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ =
        toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ *
          toInducedAutOn ψ.range ⟨s, hs⟩) :
    (∀ y ∈ ψ.range, s * y = y * s) ∨ (∀ y ∈ ψ.range, s * y * s⁻¹ = ψ x * y * (ψ x)⁻¹) ∨
      (∀ q ∈ ψ.range, q ∈ Subgroup.closure ({q | q ∈ ψ.range ∧ s * q = q * s} ∪
        {q | q ∈ ψ.range ∧ ψ x * q = q * ψ x})) := by
  classical
  set v : ↥(inducedAutOn ψ.range) := toInducedAutOn ψ.range ⟨s, hs⟩ with hvdef
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd hodd
  have h3 : 3 ≤ Module.finrank F (ι → F) := by omega
  obtain ⟨e, he, hker, hnorm, hcent⟩ := exists_hom_spin hodd hQ h3 hrange ψ hψ
  have hσ : ∀ g : spinGroup Q, spinAction Q g ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict g * ℓ * (ψ.rangeRestrict g)⁻¹) =
        ψ.rangeRestrict g * (v : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict g)⁻¹ := by
    intro g hg ℓ
    have h := congrArg (fun a : ↥(inducedAutOn ψ.range) => ((a : MulAut ↥ψ.range) ℓ : ↥ψ.range))
      (hv g hg)
    exact Subtype.ext (congrArg Subtype.val h)
  obtain ⟨α, w, hαψ, hwiso, hwspan, hθw⟩ :=
    Q3TLK.exists_isometry_of_centralizing_at3 hodd hF3 hrange hZ3 fr hψ (v : MulAut ↥ψ.range)
      hlift hσ
  have hy_mem : w * w ∈ elementaryGroup Q := sq_mem_of_frame hodd hQ fr hV hwiso
  have hspan_y : ∀ x ∈ fr.span, (w * w) x = x := fun x hx => by
    rw [LinearEquiv.mul_apply, hwspan x hx, hwspan x hx]
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift hrange α hy_mem hθw
  have hey : e ⟨w * w, hy_mem⟩ = v * v := e_sq_eq e he v α hαψ hy_mem hŷ hαα
  have hvv : v * v = 1 := by
    rw [hvdef, ← map_mul]
    have : (⟨s, hs⟩ * ⟨s, hs⟩ : ↥(Subgroup.normalizer (ψ.range : Set H))) = 1 :=
      Subtype.ext hss
    rw [this, map_one]
  have hww : w * w = 1 := eq_one_of_e_eq_one e hker fr hy_mem hspan_y (by rw [hey, hvv])
  have hψα : ∀ g, ψ (α g) = s * ψ g * s⁻¹ := fun g => congrArg Subtype.val (hαψ g)
  by_cases hM : minusSp w = ⊥
  ·
    left
    have hw1 : w = 1 := eq_one_of_minusSp_eq_bot h2 hww hM
    have hαid : (α : spinGroup Q →* spinGroup Q) = MonoidHom.id _ := by
      refine hom_eq_of_central_diff _ _ fun g => ?_
      apply ker_spinAction_le_center Q
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (spinAction Q g)⁻¹ * spinAction Q (α g) = 1
      rw [hθw, hw1, inv_one, one_mul, mul_one, inv_mul_cancel]
    rintro _ ⟨g, rfl⟩
    have h1 := hψα g
    have h2' : α g = g := DFunLike.congr_fun hαid g
    rw [h2'] at h1
    calc s * ψ g = (s * ψ g * s⁻¹) * s := by group
      _ = ψ g * s := by rw [← h1]
  by_cases hN : plusSp w ⊓ fr.perp = ⊥
  ·
    right
    left
    have hneg := mul_La_neg_one_eq_neg h2 fr hwiso hww hwspan hN
    have hττ : fr.La (-1) * fr.La (-1) = 1 := fr.La_neg_one_mul_self
    have hwτ : w = LinearEquiv.neg F * fr.La (-1) := by
      calc w = w * (fr.La (-1) * fr.La (-1)) := by rw [hττ, mul_one]
        _ = (w * fr.La (-1)) * fr.La (-1) := by rw [mul_assoc]
        _ = LinearEquiv.neg F * fr.La (-1) := by rw [hneg]
    have hnegc : ∀ h : (ι → F) ≃ₗ[F] (ι → F), LinearEquiv.neg F * h = h * LinearEquiv.neg F :=
      fun h => commute_of_mem_scalars (mem_scalars.mpr ⟨-1, fun v => by simp⟩) h
    have hθα : ∀ g, spinAction Q (α g) = fr.La (-1) * spinAction Q g * (fr.La (-1))⁻¹ := by
      intro g
      rw [hθw, hwτ]
      calc LinearEquiv.neg F * fr.La (-1) * spinAction Q g *
            (LinearEquiv.neg F * fr.La (-1))⁻¹
          = LinearEquiv.neg F * (fr.La (-1) * spinAction Q g * (fr.La (-1))⁻¹) *
            (LinearEquiv.neg F)⁻¹ := by group
        _ = (fr.La (-1) * spinAction Q g * (fr.La (-1))⁻¹) * LinearEquiv.neg F *
            (LinearEquiv.neg F)⁻¹ := by rw [hnegc]
        _ = fr.La (-1) * spinAction Q g * (fr.La (-1))⁻¹ := by group
    have hαconj : (α : spinGroup Q →* spinGroup Q) = (MulAut.conj x).toMonoidHom := by
      refine hom_eq_of_central_diff _ _ fun g => ?_
      apply ker_spinAction_le_center Q
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (spinAction Q (x * g * x⁻¹))⁻¹ * spinAction Q (α g) = 1
      rw [hθα, map_mul, map_mul, map_inv, hx, inv_mul_cancel]
    rintro _ ⟨g, rfl⟩
    have h1 := hψα g
    have h2' : α g = x * g * x⁻¹ := DFunLike.congr_fun hαconj g
    rw [h2', map_mul, map_mul, map_inv] at h1
    exact h1.symm
  right
  right
  have htop := spinGroup_eq_fixed_sup_centralizer3 hodd hF3 hQ hrange hZ3 fr hV hx α hwiso hww
    hwspan hθw hM hN
  have hle : (fixedGroup α ⊔ Subgroup.centralizer ({x} : Set (spinGroup Q))).map ψ ≤
      Subgroup.closure ({q | q ∈ ψ.range ∧ s * q = q * s} ∪
        {q | q ∈ ψ.range ∧ ψ x * q = q * ψ x}) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      refine Subgroup.subset_closure (Or.inl ⟨⟨a, rfl⟩, ?_⟩)
      have h1 := hψα a
      rw [mem_fixedGroup.mp ha] at h1
      calc s * ψ a = (s * ψ a * s⁻¹) * s := by group
        _ = ψ a * s := by rw [← h1]
    · rintro _ ⟨b, hb, rfl⟩
      refine Subgroup.subset_closure (Or.inr ⟨⟨b, rfl⟩, ?_⟩)
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hb
      rw [← map_mul, ← map_mul, h1]
  rintro _ ⟨g, rfl⟩
  rw [htop] at hle
  exact hle ⟨g, Subgroup.mem_top g, rfl⟩

end Core

end CFSG.ClassicalInvolution.Q3.Q3SPN3
