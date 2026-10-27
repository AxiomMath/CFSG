module

public import CFSG.LieType.Chevalley.C2E6FieldExtensionFirst
public import CFSG.LieType.Chevalley.C2E6FieldExtensionFourth

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FieldExtension

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.CosetBuilding CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open FourthResidue (V0 Qminus sMinus rhoMinus fourthJ two_mem_fourthJ)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem _root_.CFSG.LieType.Chevalley.C2E6Std.standard_field_extension_and_full_residue_actions :
    (∀ g : stdGroup, ((betaG g : stdGroup) : ModGL Tag.E6 K) = betaGL g) ∧
    (∀ g : ModGL Tag.E6 K,
      (betaGL g : Module.End K (RootModule Tag.E6 K)) = entrywise barHom g) ∧
    (∀ c : K, barHom c = c ^ 2) ∧
    orderOf betaG = 2 ∧
    (∀ g : stdGroup, betaG ≠ MulAut.conj g) ∧
    (∀ b : MulAut stdGroup, b ∈ betaGroup ↔ b = 1 ∨ b = betaG) ∧
    (∀ (γ : GStar) (x : stdGroup), γ • (x : stdChamber) =
      ((γ.left * (γ.right : MulAut stdGroup) x : stdGroup) : stdChamber)) ∧
    (∀ γ : GStar, (∀ q : stdChamber, γ • q = q) → γ = 1) ∧
    (∀ (γ : GStar) (x y : stdChamber), stdDistance (γ • x) (γ • y) = stdDistance x y) ∧
    (∀ (γ : GStar) (J : Set (Fin 4)) (x : stdChamber),
      (γ • ·) '' residue nativeCoxeterSystem stdDistance J x =
        residue nativeCoxeterSystem stdDistance J (γ • x)) ∧
    Nat.card GStar = 153064959367549707878400 ∧
    (∀ (J : Set (Fin 4)) (g : stdGroup),
      (g : stdChamber) ∈ baseResidue J ↔ (g : ModGL Tag.E6 K) ∈ nativeParabolic J) ∧
    (∀ (J : Set (Fin 4)) (γ : GStar),
      (γ • ·) '' baseResidue J = baseResidue J ↔ γ ∈ parStar J) ∧
    (∀ (J : Set (Fin 4)) (γ : GStar),
      γ ∈ parStar J ↔ (γ.left : ModGL Tag.E6 K) ∈ nativeParabolic J) ∧
    (∀ (J : Set (Fin 4)) (γ : parStar J) (p : nativeParabolic J),
      parSmul γ (QuotientGroup.mk p) = QuotientGroup.mk (parMap γ p) ∧
        (parMap γ p : ModGL Tag.E6 K) = ((γ.1.left * (γ.1.right : MulAut stdGroup)
          ⟨p, nativeParabolic_le_stdGroup J p.2⟩ : stdGroup) : ModGL Tag.E6 K)) ∧
    (∀ J : Set (Fin 4), Function.Injective (FourthResidue.chamberOf J) ∧
      Set.range (FourthResidue.chamberOf J) = baseResidue J) ∧
    (∀ (J : Set (Fin 4)) (γ : parStar J) (y : ParabolicCosets J),
      FourthResidue.chamberOf J (parSmul γ y) = γ.1 • FourthResidue.chamberOf J y) ∧
    (∀ γ : parStar firstJ, (∀ x ∈ baseResidue firstJ, γ.1 • x = x) ↔
      (γ.1.right : MulAut stdGroup) = 1 ∧ (γ.1.left : ModGL Tag.E6 K) ∈ stdRadical firstJ) ∧
    (∀ γ : parStar fourthJ, (∀ x ∈ baseResidue fourthJ, γ.1 • x = x) ↔
      (γ.1.right : MulAut stdGroup) = 1 ∧ (γ.1.left : ModGL Tag.E6 K) ∈ stdRadical fourthJ) ∧
    (∀ h : SU6, frobAut (h : SU6 ⧸ ZSU) = (barSU h : SU6 ⧸ ZSU)) ∧
    orderOf frobAut = 2 ∧
    (∀ f : MulAut (SU6 ⧸ ZSU), f ∈ frobGroup ↔ f = 1 ∨ f = frobAut) ∧
    (∀ (h : SU6) (F : IsoFlag6), (⟨(h : SU6 ⧸ ZSU), 1⟩ : SUFrob) • F = h • F) ∧
    (∀ (h : SU6) (F : IsoFlag6),
      (⟨(h : SU6 ⧸ ZSU), ⟨frobAut, Subgroup.mem_zpowers _⟩⟩ : SUFrob) • F = h • frobFlag F) ∧
    (∀ (F : IsoFlag6) (k : Fin 3), (frobFlag F).sub k = (F.sub k).map frob6) ∧
    (∀ (v : Fin 6 → K) (i : Fin 6), frob6 v i = bar (v i)) ∧
    (∀ a : SUFrob, (∀ F : IsoFlag6, a • F = F) → a = 1) ∧
    (∀ γ : parStar firstJ,
      (thetaFirst γ).left = leviSUEquiv (leviProj two_mem_firstJ (parLeft γ)) ∧
      ((γ.1.right : MulAut stdGroup) = 1 → (thetaFirst γ).right = 1) ∧
      ((γ.1.right : MulAut stdGroup) = betaG →
        ((thetaFirst γ).right : MulAut (SU6 ⧸ ZSU)) = frobAut)) ∧
    Function.Surjective thetaFirst ∧
    (∀ γ : parStar firstJ, thetaFirst γ = 1 ↔
      (γ.1.right : MulAut stdGroup) = 1 ∧ (γ.1.left : ModGL Tag.E6 K) ∈ stdRadical firstJ) ∧
    (∀ (γ : parStar firstJ) (y : ParabolicCosets firstJ),
      residueFlag (parSmul γ y) = thetaFirst γ • residueFlag y) ∧
    (∀ g : V0 ≃ₗ[ZMod 2] V0, g ∈ TauCeti.QuadraticMap.orthogonalGroup Qminus →
      (∀ W ∈ singularFlags Qminus 3, ∀ k, (W k).map (g : V0 →ₗ[ZMod 2] V0) = W k) → g = 1) ∧
    (∀ γ : parStar fourthJ,
      ((γ.1.right : MulAut stdGroup) = 1 →
        (thetaFour γ : V0 ≃ₗ[ZMod 2] V0) = rhoMinus (leviProj two_mem_fourthJ (parLeft γ))) ∧
      ((γ.1.right : MulAut stdGroup) = betaG → (thetaFour γ : V0 ≃ₗ[ZMod 2] V0) =
        rhoMinus (leviProj two_mem_fourthJ (parLeft γ)) * sMinus)) ∧
    Function.Surjective thetaFour ∧
    (∀ γ : parStar fourthJ, thetaFour γ = 1 ↔
      (γ.1.right : MulAut stdGroup) = 1 ∧ (γ.1.left : ModGL Tag.E6 K) ∈ stdRadical fourthJ) ∧
    (∀ (γ : parStar fourthJ) (y : ParabolicCosets fourthJ) (k : Fin 3),
      (FourthResidue.residueFlag (parSmul γ y) : Fin 3 → Submodule (ZMod 2) V0) k =
        ((FourthResidue.residueFlag y : Fin 3 → Submodule (ZMod 2) V0) k).map
          ((thetaFour γ : V0 ≃ₗ[ZMod 2] V0) : V0 →ₗ[ZMod 2] V0)) :=
  ⟨coe_betaG_apply, betaGL_apply, fun _ => rfl, orderOf_betaG, betaG_ne_conj,
    fun _ => mem_betaGroup_iff, smul_mk, fun _ => eq_one_of_forall_smul_eq_star,
    stdDistance_smul, image_smul_residue, card_GStar, mem_baseResidue_iff,
    fun J γ => image_smul_baseResidue_iff γ J, fun _ _ => Iff.rfl,
    fun _ _ _ => ⟨rfl, rfl⟩,
    fun J => ⟨FourthResidue.chamberOf_injective J, range_chamberOf J⟩, fun _ => chamberOf_parSmul,
    forall_smul_eq_iff_first, forall_smul_eq_iff_four, frobAut_mk, orderOf_frobAut,
    fun _ => mem_frobGroup_iff, SUFrob_smul_one, SUFrob_smul_frob, fun _ _ => rfl,
    fun _ _ => rfl, fun _ => eq_one_of_forall_smul_SUFrob,
    fun _ => ⟨rfl, thetaFirst_right_of_eq_one, thetaFirst_right_of_eq_betaG⟩,
    thetaFirst_surjective, thetaFirst_eq_one_iff, residueFlag_parSmul_first,
    fun _ hgO hg => FourthResidue.eq_one_of_forall_smul_flag hgO hg,
    fun _ => ⟨coe_thetaFour_of_eq_one, coe_thetaFour_of_eq_betaG⟩, thetaFour_surjective,
    thetaFour_eq_one_iff, residueFlag_parSmul_four⟩

end CFSG.LieType.Chevalley.C2E6Std.FieldExtension
