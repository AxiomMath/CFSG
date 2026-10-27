module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Lift
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs61
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

private theorem elemAbelian_of_comm_exp' {M : Type} [Group M] {p : ℕ} {E : Subgroup M}
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hp : ∀ x ∈ E, x ^ p = 1) : IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩

theorem isElemAbelian_actImage_gen {G : Type} [Group G] {p : ℕ} {B J : Subgroup G}
    (hB : IsElemAbelian p B) (hBJ : B ≤ Subgroup.normalizer (J : Set G)) :
    IsElemAbelian p (actImage p J B) := by
  refine elemAbelian_of_comm_exp' ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isElemAbelian_commute hB (Subgroup.mem_subgroupOf.1 hx)
      (Subgroup.mem_subgroupOf.1 hy))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (hB.2 _ (Subgroup.mem_subgroupOf.1 hx))
    rw [this, map_one]

theorem card_le_of_actImage {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {X L B : Subgroup G}
    (hL : GLAPComponent p X L) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (h : Nat.card ↥(actImage p L B) ≤ p * Nat.card ↥(actImage p L B ⊓ Inn (PSimple p L))) :
    Nat.card ↥B ≤ p * Nat.card ↥(B ⊓ innerModSubgroup p L) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hN
  set φ : ↥N →* MulAut (PSimple p L) := actHom p L with hφ
  set Bn : Subgroup ↥N := B.subgroupOf N with hBn
  set P : Subgroup (MulAut (PSimple p L)) := actImage p L B with hP
  set g : ↥Bn →* MulAut (PSimple p L) := φ.comp Bn.subtype with hg
  have hrange : g.range = P := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype, hP]
    rfl
  have hBcard : Nat.card ↥B = Nat.card ↥Bn :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv).symm
  have hsplit : Nat.card ↥Bn = Nat.card g.range * Nat.card g.ker :=
    card_eq_range_mul_ker g
  have hOcard : Nat.card ↥(B ⊓ innerModSubgroup p L) =
      Nat.card ↥((P ⊓ Inn (PSimple p L)).comap g) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨⟨x.1, hBL x.2.1⟩, Subgroup.mem_subgroupOf.2 x.2.1⟩, ?_⟩
        invFun := fun y => ⟨(y.1 : G), ?_, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    ·
      rw [Subgroup.mem_comap]
      refine ⟨?_, ?_⟩
      · exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.2 x.2.1)
      · exact (chevAut_mem_inner_iff hp hL (hBL x.2.1)).2 x.2.2
    · exact Subgroup.mem_subgroupOf.1 y.1.2
    · have hy := y.2
      rw [Subgroup.mem_comap] at hy
      exact (chevAut_mem_inner_iff hp hL y.1.1.2).1 hy.2
  have hcomap : Nat.card ↥((P ⊓ Inn (PSimple p L)).comap g) =
      Nat.card ↥(P ⊓ Inn (PSimple p L)) * Nat.card g.ker :=
    card_comap_eq g (P ⊓ Inn (PSimple p L)) (by rw [hrange]; exact inf_le_left)
  calc Nat.card ↥B = Nat.card g.range * Nat.card g.ker := by rw [hBcard, hsplit]
    _ = Nat.card ↥P * Nat.card g.ker := by rw [hrange]
    _ ≤ (p * Nat.card ↥(P ⊓ Inn (PSimple p L))) * Nat.card g.ker := Nat.mul_le_mul_right _ h
    _ = p * (Nat.card ↥(P ⊓ Inn (PSimple p L)) * Nat.card g.ker) := by ring
    _ = p * Nat.card ↥((P ⊓ Inn (PSimple p L)).comap g) := by rw [hcomap]
    _ = p * Nat.card ↥(B ⊓ innerModSubgroup p L) := by rw [hOcard]

end CFSG.LocalAnalysis.GLTheoremA
