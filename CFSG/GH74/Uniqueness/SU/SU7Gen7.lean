module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.Assembly.Defs

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Gen

open Subgroup

theorem le_of_forall_hyperplane {G : Type*} [Group G] [Finite G] {F D J : Subgroup G}
    (hF : CFSG.Open.IsElemAbelian 2 F) (hFnt : Nontrivial ↥F)
    (hFD : F ≤ normalizer (D : Set G)) (hDodd : Odd (Nat.card D))
    (hJ : ∀ E : Subgroup G, E ≤ F → (E.subgroupOf F).index = 2 →
      D ⊓ centralizer (E : Set G) ≤ J) : D ≤ J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFcomm := hF.1
  have : IsElementaryAbelian 2 F :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hF.2 x x.2) }
  let _ : MulDistribMulAction F D := Subgroup.conjMulDistribMulActionOfLeNormalizer F D hFD
  have : F.Normalizes D := ⟨hFD⟩
  have hp : ¬ 2 ∣ Nat.card D := fun h => (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr h)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := F) (H := D) hp
  set Jd : Subgroup D := J.comap D.subtype with hJd
  have hle : ⨆ (B : Subgroup F) (_ : B.index = 2), CFSG.fixedPointSubgroup B D ≤ Jd := by
    refine iSup₂_le fun B hB => ?_
    set R : Subgroup G := B.map F.subtype with hR
    have hRF : R ≤ F := Subgroup.map_subtype_le B
    have hRi : (R.subgroupOf F).index = 2 := by
      have hRB : R.subgroupOf F = B :=
        Subgroup.comap_map_eq_self_of_injective F.subtype_injective B
      rw [hRB]
      exact hB
    intro x hx
    refine hJ R hRF hRi ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hyb : b • x = x := hx ⟨b, hb⟩
    have hbx := congrArg Subtype.val hyb
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at hbx
    calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
      _ = (x : G) * (b : G) := by rw [hbx]
  rw [hgen, top_le_iff] at hle
  intro x hx
  have hxC : (⟨x, hx⟩ : D) ∈ Jd := hle ▸ Subgroup.mem_top _
  exact hxC

end CFSG.GH74.Uniqueness.SU.SU7.Gen
