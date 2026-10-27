module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralExitDefs
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelRecipeID
import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFaithful

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE

private theorem e6exit_entrywiseFrobGL_baseChange
    {K : Type} [Field K] [Finite K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharP Ω 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (y : ModGL Tag.E6 K) :
    entrywiseFrobGL Tag.E6 Ω 2 n (baseChangeGL (algebraMap K Ω) y) =
      baseChangeGL (algebraMap K Ω) y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hcomp : (iterateFrobenius Ω 2 n).comp (algebraMap K Ω) = algebraMap K Ω := by
    refine RingHom.ext fun c => ?_
    change (iterateFrobenius Ω 2 n) (algebraMap K Ω c) = algebraMap K Ω c
    rw [iterateFrobenius_def, ← map_pow]
    congr 1
    rw [← hK]
    simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card c
  rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
    CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]

private theorem e6exit_congr_symm_congr {R C : Type*} [Group R] [Group C]
    (e : R ≃* C) (f : MulAut R) : MulAut.congr e.symm (MulAut.congr e f) = f := by
  ext x
  simp [MulAut.congr, MulEquiv.trans_apply]


theorem e6BigToralExit_of (h : E6LangTorusExit) : E6BigToralExit := by
  intro G _ _ L J A d b n K _ _ hn hK h3 hS θ E hE3 hEcard hEI hEd hEb
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n) (by rw [hK])
  let Ω := AlgebraicClosure K
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let ρ : TableBExc.RecipeGroup Tag.E6 K ≃* adjointGroup Tag.E6 K :=
    TableBExc.recipeEquiv Tag.E6 K
  let θ' : ↥L ⧸ Subgroup.center ↥L ≃* TableBExc.RecipeGroup Tag.E6 K := θ
  let E' : Subgroup (MulAut (adjointGroup Tag.E6 K)) := E.map (MulAut.congr ρ).toMonoidHom
  have hE'el : IsElemAbelian 3 E' := hE3.map _
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.congr ρ).injective
  have hE'range : E' ≤ (TableBExc.E6Three.hatAut Tag.E6 K).range := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (E6ThreeModel.recipeID_iff_hatAut φ).1 (hEI φ hφ)
  have hhatAut_inj : Function.Injective (TableBExc.E6Three.hatAut Tag.E6 K) :=
    NoOffE6Three.hatAut_injective
  let XK : Subgroup ↥(TableBExc.E6Three.hatGroup Tag.E6 K) :=
    E'.comap (TableBExc.E6Three.hatAut Tag.E6 K)
  have hXKel : IsElemAbelian 3 XK := hE'el.comap hhatAut_inj
  have hXKcard : Nat.card XK = Nat.card E' := by
    have hmap : XK.map (TableBExc.E6Three.hatAut Tag.E6 K) = E' :=
      Subgroup.map_comap_eq_self hE'range
    calc Nat.card XK = Nat.card (XK.map (TableBExc.E6Three.hatAut Tag.E6 K)) :=
          (Subgroup.card_map_of_injective hhatAut_inj).symm
      _ = Nat.card E' := by rw [hmap]
  let Xmod : Subgroup (ModGL Tag.E6 K) :=
    XK.map (TableBExc.E6Three.hatGroup Tag.E6 K).subtype
  have hXmodEl : IsElemAbelian 3 Xmod := hXKel.map _
  have hXmodCard : Nat.card Xmod = Nat.card E := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hXKcard, hE'card]
  let AΩ : Subgroup (ModGL Tag.E6 Ω) := Xmod.map (baseChangeGL (algebraMap K Ω))
  have hAel : IsElemAbelian 3 AΩ := hXmodEl.map _
  have hAcard : Nat.card AΩ = Nat.card E := by
    rw [Subgroup.card_map_of_injective (baseChangeGL_injective (algebraMap K Ω)), hXmodCard]
  have hAadj : AΩ ≤ adjointGroup Tag.E6 Ω := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨xK, hxK, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨g, hg, a, hga⟩ := xK.2
    have hsub : ((TableBExc.E6Three.hatGroup Tag.E6 K).subtype xK : ModGL Tag.E6 K) =
        g * rootDiagUnit Tag.E6 a := hga
    rw [hsub, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K Ω) hg)
      (CFSG.RankThree.Classical2.torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup _))
  have hAfixed : ∀ x ∈ AΩ, entrywiseFrobGL Tag.E6 Ω 2 n x = x := by
    rintro _ ⟨y, -, rfl⟩
    exact e6exit_entrywiseFrobGL_baseChange hK y
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h2
    have h1 : 3 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 h3
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    have hsub : 2 ^ n - (2 ^ n - 1) = 1 := by omega
    rw [hsub] at h1
    exact Nat.prime_three.not_dvd_one h1
  obtain ⟨g, hg, hgA⟩ :=
    ExcFramesHalf.bigElemAbelianToralBar_E6_three K h3K AΩ hAadj
      (fun x hx y hy => hAel.comm hx hy)
      (fun x hx => hAel.2 x hx) (by
        change 3 ^ (Tag.E6.rank - 1) ≤ Nat.card AΩ
        rw [hAcard]
        exact hEcard)
  have hpq : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  obtain ⟨w, g0, hg0, hg0F, hg0T⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_lang_torus_of_conj_torus
      (τ := Tag.E6) (L := Ω) (f := n) hn (p := 3) hpq
      (fun x hx => hAel.2 x hx) hAfixed hg hgA
  obtain ⟨φd, hφdE, hφdInd⟩ := hEd
  obtain ⟨φb, hφbE, hφbInd⟩ := hEb
  have hφdI : φd ∈ TableBExc.RecipeID Tag.E6 K := hEI φd hφdE
  have hφbI : φb ∈ TableBExc.RecipeID Tag.E6 K := hEI φb hφbE
  obtain ⟨wd, hwd⟩ := MonoidHom.mem_range.1 ((E6ThreeModel.recipeID_iff_hatAut φd).1 hφdI)
  obtain ⟨wb, hwb⟩ := MonoidHom.mem_range.1 ((E6ThreeModel.recipeID_iff_hatAut φb).1 hφbI)
  have hwdA : baseChangeGL (algebraMap K Ω) (wd : ModGL Tag.E6 K) ∈ AΩ := by
    refine Subgroup.mem_map.2 ⟨(wd : ModGL Tag.E6 K), ?_, rfl⟩
    refine Subgroup.mem_map.2 ⟨wd, ?_, rfl⟩
    exact Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨φd, hφdE, hwd.symm⟩)
  have hwbA : baseChangeGL (algebraMap K Ω) (wb : ModGL Tag.E6 K) ∈ AΩ := by
    refine Subgroup.mem_map.2 ⟨(wb : ModGL Tag.E6 K), ?_, rfl⟩
    refine Subgroup.mem_map.2 ⟨wb, ?_, rfl⟩
    exact Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨φb, hφbE, hwb.symm⟩)
  have hwdeq : MulAut.congr ρ.symm (TableBExc.E6Three.hatAut Tag.E6 K wd) = φd := by
    rw [hwd]
    exact e6exit_congr_symm_congr ρ φd
  have hwbeq : MulAut.congr ρ.symm (TableBExc.E6Three.hatAut Tag.E6 K wb) = φb := by
    rw [hwb]
    exact e6exit_congr_symm_congr ρ φb
  refine h G L J A d b n K hn hK h3 hS θ' wd wb ?_ ?_ w g0 hg0 hg0F ?_
  · rw [hwdeq]
    exact hφdInd
  · rw [hwbeq]
    exact hφbInd
  · intro x hx
    rcases hx with rfl | rfl
    · exact hg0T _ hwdA
    · exact hg0T _ hwbA

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
