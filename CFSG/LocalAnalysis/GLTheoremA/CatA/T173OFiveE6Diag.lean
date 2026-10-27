module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3Conj
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveSylow
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeToral
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffTwE6Three
open CFSG.StandardType.SmallExc


private theorem exists_conj_le_xHat_of_le_hatGroup {F : Type} [Field F] [Finite F]
    (h3 : 3 ∣ Nat.card F - 1) {E : Subgroup (ModGL Tag.E6 F)} (hE : IsElemAbelian 3 E)
    (hEH : E ≤ hatGroup Tag.E6 F) :
    ∃ c : ↥(hatGroup Tag.E6 F), ∃ E' : Subgroup (ModGL Tag.E6 F),
      E' ≤ xHat Tag.E6 F modelHomE6.range ∧ IsElemAbelian 3 E' ∧
        Nat.card E' = Nat.card E ∧
          ∀ e (he : e ∈ E),
            ((MulAut.conj c).toMonoidHom ⟨e, hEH he⟩ : ModGL Tag.E6 F) ∈ E' := by
  classical
  haveI : Finite ↥(hatGroup Tag.E6 F) := finite_hatGroup
  have hEp : IsPGroup 3 ↥(E.subgroupOf (hatGroup Tag.E6 F)) :=
    (IsElemAbelian.subgroupOf hE _).isPGroup
  obtain ⟨c, hcx⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_xHat (K := F) h3) hEp
  let Ec : Subgroup ↥(hatGroup Tag.E6 F) :=
    (E.subgroupOf (hatGroup Tag.E6 F)).map (MulAut.conj c).toMonoidHom
  let E' : Subgroup (ModGL Tag.E6 F) := Ec.map (hatGroup Tag.E6 F).subtype
  have hE'X : E' ≤ xHat Tag.E6 F modelHomE6.range := by
    rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hcx hp)
  have hE'el : IsElemAbelian 3 E' :=
    (IsElemAbelian.map (IsElemAbelian.subgroupOf hE (hatGroup Tag.E6 F))
      (MulAut.conj c).toMonoidHom).map
      (hatGroup Tag.E6 F).subtype
  have hcardE' : Nat.card E' = Nat.card E := by
    have h1 : Nat.card E' = Nat.card Ec :=
      Subgroup.card_map_of_injective (hatGroup Tag.E6 F).subtype_injective
    have h2 : Nat.card Ec = Nat.card ↥(E.subgroupOf (hatGroup Tag.E6 F)) :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    rw [h1, h2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  refine ⟨c, E', hE'X, hE'el, hcardE', fun e he => ?_⟩
  exact ⟨_, ⟨⟨e, hEH he⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩, rfl⟩

private theorem exists_conj_diag_of_le_xHat_of_elementaryAbelian {F : Type} [Field F] [Finite F]
    (h3 : 3 ∣ Nat.card F - 1) {E' : Subgroup (ModGL Tag.E6 F)}
    (hE'el : IsElemAbelian 3 E') (hE'X : E' ≤ xHat Tag.E6 F modelHomE6.range)
    (hE'5 : 3 ^ 5 ≤ Nat.card E') :
    ∃ g ∈ hatGroup Tag.E6 F, ∀ p ∈ E',
      ∃ b : Fin Tag.E6.rank → Fˣ, g * p * g⁻¹ = rootDiagUnit Tag.E6 b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := F) (p := 3) h3
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  rcases torus_or_cyclic hζo hζ hE'el hE'X hE'5 with htor | ⟨i, hi⟩
  · refine ⟨1, one_mem _, fun p hp => ?_⟩
    obtain ⟨v, hv⟩ := htor p hp
    refine ⟨zetaVec ζ hζ v, ?_⟩
    rw [hv]
    simp
  · obtain ⟨y, hy, hyE⟩ := exists_conj_diag_of_le_xHat hζo hE'el hi
    exact ⟨y, adjointGroup_le_hatGroup hy, fun p hp => hyE p hp⟩

private theorem cube_eq_one_of_conj_eq_rootDiagUnit {F : Type} [Field F]
    {p g : ModGL Tag.E6 F} {b : Fin Tag.E6.rank → Fˣ} (hp3 : p ^ 3 = 1)
    (hb : g * p * g⁻¹ = rootDiagUnit Tag.E6 b) : ∀ i, b i ^ 3 = 1 := by
  have hroot3 : rootDiagUnit Tag.E6 b ^ 3 = 1 := by
    rw [← hb]
    calc (g * p * g⁻¹) ^ 3 = (MulAut.conj g) (p ^ 3) := by
          rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
      _ = 1 := by rw [hp3, map_one]
  have hb3 : b ^ 3 = 1 := by
    apply rootDiagUnit_injective
    rw [← rootDiagUnit_pow, hroot3, rootDiagUnit_one]
  intro i
  simpa using congrFun hb3 i

theorem exists_conj_rootDiag_of_le_hatGroup {F : Type} [Field F] [Finite F]
    (h3 : 3 ∣ Nat.card F - 1) {E : Subgroup (ModGL Tag.E6 F)} (hE : IsElemAbelian 3 E)
    (hEH : E ≤ hatGroup Tag.E6 F) (hc : 3 ^ 5 ≤ Nat.card E) :
    ∃ g ∈ hatGroup Tag.E6 F, ∀ e ∈ E, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
      g * e * g⁻¹ = rootDiagUnit Tag.E6 c := by
  obtain ⟨c, E', hE'X, hE'el, hcardE', hmem⟩ :=
    exists_conj_le_xHat_of_le_hatGroup h3 hE hEH
  have hE'5 : 3 ^ 5 ≤ Nat.card E' := by
    rw [hcardE']
    exact hc
  obtain ⟨g, hgH, hconj⟩ := exists_conj_diag_of_le_xHat_of_elementaryAbelian h3 hE'el hE'X hE'5
  refine ⟨(g : ModGL Tag.E6 F) * (c : ModGL Tag.E6 F), mul_mem hgH c.2, ?_⟩
  intro e he
  set p : ↥(hatGroup Tag.E6 F) := (MulAut.conj c).toMonoidHom ⟨e, hEH he⟩ with hp
  have hp3 : p ^ 3 = 1 := by
    rw [hp]
    have he3 : (⟨e, hEH he⟩ : ↥(hatGroup Tag.E6 F)) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 e he
    rw [← map_pow, he3, map_one]
  have hp3' : (p : ModGL Tag.E6 F) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hp3, Subgroup.coe_one]
  obtain ⟨b, hb⟩ := hconj (p : ModGL Tag.E6 F) (hmem e he)
  have hp_eq : (p : ModGL Tag.E6 F) = (c : ModGL Tag.E6 F) * e * (c : ModGL Tag.E6 F)⁻¹ := by
    rw [hp]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hbdiag : (g : ModGL Tag.E6 F) * ((c : ModGL Tag.E6 F) * e * (c : ModGL Tag.E6 F)⁻¹) *
      (g : ModGL Tag.E6 F)⁻¹ = rootDiagUnit Tag.E6 b := by
    rw [← hp_eq]
    exact hb
  refine ⟨b, cube_eq_one_of_conj_eq_rootDiagUnit hp3' hb, ?_⟩
  calc ((g : ModGL Tag.E6 F) * (c : ModGL Tag.E6 F)) * e *
        ((g : ModGL Tag.E6 F) * (c : ModGL Tag.E6 F))⁻¹
      = (g : ModGL Tag.E6 F) * ((c : ModGL Tag.E6 F) * e * (c : ModGL Tag.E6 F)⁻¹) *
          (g : ModGL Tag.E6 F)⁻¹ := by group
    _ = rootDiagUnit Tag.E6 b := hbdiag

end CFSG.LocalAnalysis.GLTheoremA.T173O
