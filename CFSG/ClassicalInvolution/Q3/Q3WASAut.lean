module

public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain
public import CFSG.ClassicalInvolution.Q3.Q3PlanFundPSL
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.Q3.M11Branch
public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.Q3.Q3WADict

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.ModelFacts.LinearAut
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups Matrix commutatorElement

section Intrinsic

theorem isClassicalMember3_of_isLongRootSL2 {n : ℕ} (hn : 2 ≤ n)
    {L : Subgroup SL(n, GaloisField 3 1)} {i : SL(n, GaloisField 3 1)}
    (h : IsLongRootSL2 hn L i) :
    IsClassicalMember3 L i ∧ classicalInvolutionOddCore L = ⊥ := by
  have hcl := h.isClassicalSL2 two_ne_zero_gf3
  obtain ⟨e⟩ := hcl.nonempty_mulEquiv
  obtain ⟨ε⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three (F := GaloisField 3 1) card_gf3
  let e' : L ≃* SL(2, ZMod 3) := e.trans ε
  have hO : classicalInvolutionOddCore L = ⊥ := by
    have h1 : (classicalInvolutionOddCore L).map e'.toMonoidHom =
        classicalInvolutionOddCore SL(2, ZMod 3) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e'
    rw [show classicalInvolutionOddCore SL(2, ZMod 3) = ⊥ from componentOddCore_sl2Three] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).mp h1
  refine ⟨⟨hcl.orderOf_eq_two, hcl.mem, ?_, ⟨?_⟩⟩, hO⟩
  · refine isSubnormal_of_normal_subgroupOf hcl.le_centralizer ?_
    rw [Subgroup.normal_subgroupOf_iff hcl.le_centralizer]
    intro l k hl hk
    exact ((Subgroup.mem_normalizer_iff.mp (hcl.centralizer_le_normalizer hk) l).mp hl)
  · exact ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e'

theorem isLongRootSL2_map_aut3 {n : ℕ} (hn : 2 ≤ n)
    (α : SL(n, GaloisField 3 1) ≃* SL(n, GaloisField 3 1))
    {L : Subgroup SL(n, GaloisField 3 1)} {i : SL(n, GaloisField 3 1)}
    (h : IsLongRootSL2 hn L i) : IsLongRootSL2 hn (L.map α.toMonoidHom) (α i) := by
  obtain ⟨hmem, hO⟩ := isClassicalMember3_of_isLongRootSL2 hn h
  have hmem' := IsClassicalMember3.map_mulEquiv α hmem
  have hO' : classicalInvolutionOddCore (L.map α.toMonoidHom) = ⊥ := by
    let e : L ≃* L.map α.toMonoidHom := L.equivMapOfInjective α.toMonoidHom α.injective
    have h1 : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore (L.map α.toMonoidHom) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [← h1, hO, Subgroup.map_bot]
  exact isLongRootSL2_of_isClassicalMember3 hn hmem' hO'

end Intrinsic

section Frame

theorem exists_frame_aut3 {n : ℕ} (hn : 3 ≤ n)
    (α : SL(n, GaloisField 3 1) ≃* SL(n, GaloisField 3 1)) :
    ∃ P : SL(n, GaloisField 3 1), ∀ (a : ℕ) (h : a + 2 ≤ n),
      α (zElt (GaloisField 3 1) (cp n a h)) = P * zElt (GaloisField 3 1) (cp n a h) * P⁻¹ := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  set F := GaloisField 3 1 with hFdef
  have hn2 : 2 ≤ n := by omega
  have hLR : ∀ (a : ℕ) (h : a + 2 ≤ n), IsLongRootSL2 hn2 ((Lc F (cp n a h)).map α.toMonoidHom)
      (α (zElt F (cp n a h))) := fun a h =>
    isLongRootSL2_map_aut3 hn2 α (isLongRootSL2_Lc h2 hn2 (cp n a h))
  let I : ℕ → Matrix (Fin n) (Fin n) F := fun a =>
    if h : a + 2 ≤ n then ((α (zElt F (cp n a h)) : SL(n, F)) : Matrix (Fin n) (Fin n) F) else 1
  have hI : ∀ (a : ℕ) (h : a + 2 ≤ n), I a = ((α (zElt F (cp n a h)) : SL(n, F)) :
      Matrix (Fin n) (Fin n) F) := fun a h => by simp [I, h]
  have hzcomm : ∀ (a b : ℕ) (ha : a + 2 ≤ n) (hb : b + 2 ≤ n),
      zElt F (cp n a ha) * zElt F (cp n b hb) = zElt F (cp n b hb) * zElt F (cp n a ha) := by
    intro a b ha hb
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_zElt, coe_zElt]
    exact zMat_mul_comm _ _
  have hchain : IsInvChain I (n - 1) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      have h := (by omega : a + 2 ≤ n)
      rw [hI a h, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, zElt_mul_self, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    · intro a ha b hb
      have h1 := (by omega : a + 2 ≤ n)
      have h2' := (by omega : b + 2 ≤ n)
      rw [hI a h1, hI b h2', ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul,
        ← map_mul, ← map_mul, hzcomm a b h1 h2']
    · intro a ha
      have h := (by omega : a + 2 ≤ n)
      rw [hI a h]
      exact (hLR a h).finrank_minusSpace h2
    · intro a ha b hb hab
      have h1 := (by omega : a + 2 ≤ n)
      have h2' := (by omega : b + 2 ≤ n)
      rw [hI a h1, hI b h2']
      refine (spaces_of_commutes h2 (by omega : 3 ≤ n) (hLR a h1) (hLR b h2') ?_ ?_).2.2
      · intro e
        exact cp_ne h1 h2' (by omega) (zElt_injective h2 (α.injective e))
      · refine (commutes_map_iff α.toMonoidHom α.injective).mpr ?_
        refine commutes_Lc_of_disjoint h2 ?_
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [cp, pr, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hx hx'
        omega
    · intro a ha
      have h1 := (by omega : a + 2 ≤ n)
      have h2' := (by omega : a + 1 + 2 ≤ n)
      rw [hI a h1, hI (a + 1) h2']
      refine inf_ne_bot_of_not_commutes h2 (hLR a h1) (hLR (a + 1) h2') ?_ ?_
      · show _ * _ = _ * _
        rw [← map_mul, ← map_mul, hzcomm a (a + 1) h1 h2']
      · intro hc
        have := (commutes_map_iff α.toMonoidHom α.injective).mp hc
        exact not_commutes_Lc_overlap h2 (by omega : 3 ≤ n) (i := ⟨a, by omega⟩)
          (j := ⟨a + 1, by omega⟩) (k := ⟨a + 2, by omega⟩) (by simp [Fin.ext_iff])
          (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) this
    · intro a ha
      have h1 := (by omega : a + 2 ≤ n)
      have h2' := (by omega : a + 1 + 2 ≤ n)
      rw [hI a h1, hI (a + 1) h2']
      intro e
      have := Subtype.ext e
      exact cp_ne h1 h2' (by omega) (zElt_injective h2 (α.injective this))
  obtain ⟨-, P, hP, -⟩ := hchain.exists_frame h2 (by omega : 2 ≤ n - 1)
  refine ⟨P, fun a h => ?_⟩
  have hPa := hP a (by omega)
  rw [hI a h, ← coe_zElt_cp h] at hPa
  have hSL : α (zElt F (cp n a h)) * P = P * zElt F (cp n a h) := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact hPa)
  rw [eq_mul_inv_iff_mul_eq, hSL]

end Frame

section Assembly

local notation "𝔽" => GaloisField 3 1

theorem exists_aut_form3 {n : ℕ} (hn : 3 ≤ n)
    (α : SL(n, 𝔽) ≃* SL(n, 𝔽)) :
    ∃ (g : GL (Fin n) 𝔽) (φ : 𝔽 ≃+* 𝔽) (ε : Bool), ∀ x : SL(n, 𝔽),
      ((α x : SL(n, 𝔽)) : Matrix (Fin n) (Fin n) 𝔽) =
        (g : Matrix (Fin n) (Fin n) 𝔽) *
          φ.mapMatrix (if ε then (((x⁻¹ : SL(n, 𝔽)) : Matrix (Fin n) (Fin n) 𝔽))ᵀ
            else (x : Matrix (Fin n) (Fin n) 𝔽)) *
          ((g⁻¹ : GL (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽) := by
  have h2 : (2 : 𝔽) ≠ 0 := two_ne_zero_gf3
  have hn2 : 2 ≤ n := by omega
  obtain ⟨P, hP⟩ := exists_frame_aut3 hn α
  let β : SL(n, 𝔽) ≃* SL(n, 𝔽) := α.trans (MulAut.conj P⁻¹)
  have hβx : ∀ x, β x = P⁻¹ * α x * P := fun x => by
    show P⁻¹ * α x * P⁻¹⁻¹ = P⁻¹ * α x * P
    rw [inv_inv]
  have hch : ∀ (a : ℕ) (h : a + 2 ≤ n),
      β.toMonoidHom (zElt 𝔽 (cp n a h)) = zElt 𝔽 (cp n a h) := by
    intro a h
    show β (zElt 𝔽 (cp n a h)) = _
    rw [hβx, hP a h]
    group
  have hz : ∀ T : Pair n, β.toMonoidHom (zElt 𝔽 T) = zElt 𝔽 T := fixes_zElt hch
  have hL : ∀ T : Pair n, ∀ g ∈ Lc 𝔽 T, β.toMonoidHom g ∈ Lc 𝔽 T := by
    intro T g hg
    have h1 := isLongRootSL2_map_aut3 hn2 β (isLongRootSL2_Lc h2 hn2 T)
    have hzT : β (zElt 𝔽 T) = zElt 𝔽 T := hz T
    rw [hzT] at h1
    have e : (Lc 𝔽 T).map β.toMonoidHom = Lc 𝔽 T := by
      rw [h1.eq_longRootGroup h2, (isLongRootSL2_Lc h2 hn2 T).eq_longRootGroup h2]
    rw [← e]
    exact Subgroup.mem_map_of_mem _ hg
  obtain ⟨g₁, φ, ε, hg₁⟩ := aut_form_of_fixes_signs h2 hn β.toMonoidHom β.injective hz hL
  refine ⟨Matrix.SpecialLinearGroup.toGL P * g₁, φ, ε, fun x => ?_⟩
  have hαx : α x = P * β x * P⁻¹ := by
    rw [hβx]
    group
  have hP1 : (((Matrix.SpecialLinearGroup.toGL P : GL (Fin n) 𝔽)) : Matrix (Fin n) (Fin n) 𝔽) =
      (P : Matrix (Fin n) (Fin n) 𝔽) := rfl
  have hP2 : ((((Matrix.SpecialLinearGroup.toGL P)⁻¹ : GL (Fin n) 𝔽)) :
      Matrix (Fin n) (Fin n) 𝔽) = ((P⁻¹ : SL(n, 𝔽)) : Matrix (Fin n) (Fin n) 𝔽) := rfl
  have e1 := hg₁ x
  rw [MulEquiv.coe_toMonoidHom] at e1
  rw [hαx, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, e1]
  simp only [mul_inv_rev, Units.val_mul, hP1, hP2, Matrix.mul_assoc]

theorem linearAutClassification3 {n : ℕ} (hn : 3 ≤ n) :
    LinearAutClassification (GaloisField 3 1) n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro X _ θ hθ hker σ
  obtain ⟨α, hα⟩ := exists_mulEquiv_lift (K := GaloisField 3 1) (p := 3) (by omega : 1 ≤ n) θ hθ
    hker σ
  obtain ⟨g, φ, ε, h⟩ := exists_aut_form3 hn α
  exact ⟨α.toMonoidHom, g, φ, ε, hα, h⟩

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3W
