module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.TwLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourLang
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Phi4
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


section EntrywiseBaseChange

variable {k k₁ : Type} [Field k] [Field k₁]

@[expose] def scEndFun (ι : k →+* k₁) (d : ℕ) (f : Module.End k (Fin d →₀ k)) :
    Module.End k₁ (Fin d →₀ k₁) :=
  Finsupp.linearCombination k₁ fun a : Fin d =>
    Finsupp.mapRange ι ι.map_zero (f (Finsupp.single a 1))

theorem scEndFun_single (ι : k →+* k₁) (d : ℕ) (f : Module.End k (Fin d →₀ k)) (a : Fin d) :
    scEndFun ι d f (Finsupp.single a 1) =
      Finsupp.mapRange ι ι.map_zero (f (Finsupp.single a 1)) := by
  simp [scEndFun]

theorem mapRange_ι_add (ι : k →+* k₁) {d : ℕ} (v w : Fin d →₀ k) :
    Finsupp.mapRange ι ι.map_zero (v + w) =
      Finsupp.mapRange ι ι.map_zero v + Finsupp.mapRange ι ι.map_zero w := by
  ext a
  simp

theorem mapRange_ι_smul (ι : k →+* k₁) {d : ℕ} (c : k) (v : Fin d →₀ k) :
    Finsupp.mapRange ι ι.map_zero (c • v) = ι c • Finsupp.mapRange ι ι.map_zero v := by
  ext a
  simp

theorem scEndFun_mapRange (ι : k →+* k₁) (d : ℕ) (f : Module.End k (Fin d →₀ k))
    (v : Fin d →₀ k) :
    scEndFun ι d f (Finsupp.mapRange ι ι.map_zero v) =
      Finsupp.mapRange ι ι.map_zero (f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, mapRange_ι_add, hv, hw]
  | single a c =>
    rw [Finsupp.mapRange_single, ← Finsupp.smul_single_one a (ι c), map_smul,
      scEndFun_single, ← Finsupp.smul_single_one a c, map_smul, mapRange_ι_smul]

theorem scEndFun_mul (ι : k →+* k₁) (d : ℕ) (f g : Module.End k (Fin d →₀ k)) :
    scEndFun ι d (f * g) = scEndFun ι d f * scEndFun ι d g := by
  refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
  simp only [Module.End.mul_apply, scEndFun_single, scEndFun_mapRange]

theorem scEndFun_one (ι : k →+* k₁) (d : ℕ) : scEndFun ι d 1 = 1 := by
  refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
  simp [scEndFun_single]

theorem scEndFun_zero (ι : k →+* k₁) (d : ℕ) : scEndFun ι d 0 = 0 := by
  refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
  simp [scEndFun_single]

theorem scEndFun_add (ι : k →+* k₁) (d : ℕ) (f g : Module.End k (Fin d →₀ k)) :
    scEndFun ι d (f + g) = scEndFun ι d f + scEndFun ι d g := by
  refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
  simp only [LinearMap.add_apply, scEndFun_single, mapRange_ι_add]

@[expose] def scEnd (ι : k →+* k₁) (d : ℕ) :
    Module.End k (Fin d →₀ k) →+* Module.End k₁ (Fin d →₀ k₁) where
  toFun := scEndFun ι d
  map_one' := scEndFun_one ι d
  map_mul' := scEndFun_mul ι d
  map_zero' := scEndFun_zero ι d
  map_add' := scEndFun_add ι d

theorem scEnd_apply (ι : k →+* k₁) (d : ℕ) (f : Module.End k (Fin d →₀ k)) :
    scEnd ι d f = scEndFun ι d f :=
  rfl

theorem scEnd_injective (ι : k →+* k₁) (d : ℕ) : Function.Injective (scEnd ι d) := by
  intro f g h
  refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
  have h' : scEndFun ι d f (Finsupp.single a 1) = scEndFun ι d g (Finsupp.single a 1) := by
    rw [← scEnd_apply, ← scEnd_apply, h]
  rw [scEndFun_single, scEndFun_single] at h'
  exact Finsupp.mapRange_injective ι ι.map_zero ι.injective h'

theorem scEnd_smul (ι : k →+* k₁) (d : ℕ) (c : k) (f : Module.End k (Fin d →₀ k)) :
    scEnd ι d (c • f) = ι c • scEnd ι d f := by
  refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
  simp only [scEnd_apply, LinearMap.smul_apply, scEndFun_single, mapRange_ι_smul]

theorem digVec_map (ι : k →+* k₁) (d c : ℕ) :
    Finsupp.mapRange ι ι.map_zero (digVec k d c) = digVec k₁ d c := by
  unfold digVec
  split_ifs with h
  · simp only [mapRange_ι_smul, Finsupp.mapRange_single, map_one, map_pow, map_neg]
  · exact Finsupp.mapRange_zero

theorem scEndFun_toEnd (ι : k →+* k₁) (d M : ℕ) :
    scEndFun ι d (CFSG.LieType.Steinberg.Minuscule.toEnd k d M) =
      CFSG.LieType.Steinberg.Minuscule.toEnd k₁ d M := by
  refine CFSG.LieType.Steinberg.Minuscule.ext_single fun a => ?_
  rw [scEndFun_single, toEnd_single, toEnd_single, digVec_map]

theorem scEnd_rootOp {τ : Tag} (D : MinData τ) (ι : k →+* k₁) (γ : Fin τ.rank → ℤ) :
    scEnd ι D.d (D.rootOp k γ) = D.rootOp k₁ γ := by
  unfold MinData.rootOp
  split_ifs with h
  · exact scEndFun_toEnd ι D.d _
  · exact map_zero _

theorem units_map_xu {τ : Tag} {D : MinData τ} (ι : k →+* k₁) (hV : D.Valid)
    (γ : Fin τ.rank → ℤ) (c : k) :
    Units.map (scEnd ι D.d).toMonoidHom (hV.xu k γ c) = hV.xu k₁ γ (ι c) := by
  refine Units.ext ?_
  change scEnd ι D.d (hV.xu k γ c : Module.End k (Fin D.d →₀ k)) =
    (hV.xu k₁ γ (ι c) : Module.End k₁ (Fin D.d →₀ k₁))
  rw [hV.xu_val, hV.xu_val, map_add, map_one, scEnd_smul, scEnd_rootOp]

theorem minGroup_le_comap {τ : Tag} {D : MinData τ} (ι : k →+* k₁) (hV : D.Valid) :
    hV.minGroup k ≤ (hV.minGroup k₁).comap (Units.map (scEnd ι D.d).toMonoidHom) := by
  rw [MinData.Valid.minGroup, Subgroup.closure_le]
  rintro _ ⟨γ, hγ, c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, units_map_xu]
  exact hV.xu_mem k₁ γ (ι c)

@[expose] def scPhi (ι : k →+* k₁) :
    ↥(e6Data_valid.minGroup k) →* ↥(e6Data_valid.minGroup k₁) :=
  MonoidHom.codRestrict
    ((Units.map (scEnd ι e6Data.d).toMonoidHom).comp (e6Data_valid.minGroup k).subtype)
    (e6Data_valid.minGroup k₁)
    fun g => Subgroup.mem_comap.1 (minGroup_le_comap ι e6Data_valid g.2)

theorem scPhi_injective (ι : k →+* k₁) : Function.Injective (scPhi ι) := by
  intro g h hgh
  refine Subtype.ext (Units.map_injective (scEnd_injective ι e6Data.d) ?_)
  exact congrArg Subtype.val hgh

theorem minGroup_hom_eq_of_gens {τ : Tag} {D : MinData τ} (hV : D.Valid) {H : Type*} [Group H]
    (ψ₁ ψ₂ : ↥(hV.minGroup k) →* H)
    (hgen : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c : k, ψ₁ (hV.xm k γ c) = ψ₂ (hV.xm k γ c)) :
    ψ₁ = ψ₂ := by
  have key : ∀ x : (Module.End k (Fin D.d →₀ k))ˣ,
      x ∈ Subgroup.closure {g | ∃ γ, IsRoot τ γ ∧ ∃ c, g = hV.xu k γ c} →
        ∀ h : x ∈ hV.minGroup k, ψ₁ ⟨x, h⟩ = ψ₂ ⟨x, h⟩ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨γ, hγ, c, rfl⟩ := hx
      intro h
      exact hgen γ hγ c
    | one =>
      intro h
      exact (map_one ψ₁).trans (map_one ψ₂).symm
    | mul x y hx hy ihx ihy =>
      intro h
      have e : (⟨x * y, h⟩ : ↥(hV.minGroup k)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul, map_mul]
      exact congrArg₂ (· * ·) (ihx hx) (ihy hy)
    | inv x hx ih =>
      intro h
      have e : (⟨x⁻¹, h⟩ : ↥(hV.minGroup k)) = (⟨x, hx⟩ : ↥(hV.minGroup k))⁻¹ := rfl
      rw [e, map_inv, map_inv, ih hx]
  refine MonoidHom.ext fun g => ?_
  obtain ⟨x, hx⟩ := g
  exact key x hx hx

theorem baseChangeGL_eltUnit {τ : Tag} (F : RootOperatorFamily τ) (ι : k →+* k₁)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : k) :
    baseChangeGL (τ := τ) ι (F.eltUnit k ⟨α, hα⟩ c) = F.eltUnit k₁ ⟨α, hα⟩ (ι c) := by
  have hk : F.eltUnit k ⟨α, hα⟩ c =
      pinnedX τ k α (((F.pinnedFamilySign α : ℤ) : k) * c) := by
    rw [F.pinnedX_eq_eltUnit k hα, ← mul_assoc, F.pinnedFamilySign_mul_self k α, one_mul]
  rw [hk, baseChangeGL_pinnedX, F.pinnedX_eq_eltUnit k₁ hα, map_mul, map_intCast, ← mul_assoc,
    F.pinnedFamilySign_mul_self k₁ α, one_mul]

theorem yPar_coe_eltUnit {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : k) :
    ((yPar (rootOperatorFamily .E6) e6AdjData_valid γ c : ↥(adjointGroup .E6 k)) :
        ModGL .E6 k) =
      (rootOperatorFamily .E6).eltUnit k ⟨γ, hγ⟩
        ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid γ : k) * c) := by
  rw [yPar, xPar_of_isRoot hγ]
  rfl

theorem e6Isogeny_xm_coe_eltUnit [Finite k] {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (c : k) :
    ((e6Isogeny k (e6Data_valid.xm k γ c) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
      (rootOperatorFamily .E6).eltUnit k ⟨γ, hγ⟩
        ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid γ : k) * c) := by
  rw [e6Isogeny_xm k hγ c]
  exact yPar_coe_eltUnit hγ c

theorem e6_gen_compat [Finite k] [Finite k₁] (ι : k →+* k₁)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : k) :
    ((e6Isogeny k₁ (scPhi ι (e6Data_valid.xm k γ c)) : ↥(adjointGroup .E6 k₁)) :
        ModGL .E6 k₁) =
      baseChangeGL (τ := Tag.E6) ι
        ((e6Isogeny k (e6Data_valid.xm k γ c) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) := by
  have hφ : scPhi ι (e6Data_valid.xm k γ c) = e6Data_valid.xm k₁ γ (ι c) :=
    Subtype.ext (units_map_xu ι e6Data_valid γ c)
  rw [hφ, e6Isogeny_xm_coe_eltUnit hγ (ι c), e6Isogeny_xm_coe_eltUnit hγ c,
    baseChangeGL_eltUnit, map_mul, map_intCast]

end EntrywiseBaseChange

theorem exists_scBaseChange {k k₁ : Type} [Field k] [Finite k] [Field k₁] [Finite k₁]
    (ι : k →+* k₁) :
    ∃ φ : ↥(e6Data_valid.minGroup k) →* ↥(e6Data_valid.minGroup k₁),
      Function.Injective φ ∧
      ∀ g : ↥(e6Data_valid.minGroup k),
        ((e6Isogeny k₁ (φ g) : ↥(adjointGroup Tag.E6 k₁)) : ModGL Tag.E6 k₁) =
          baseChangeGL ι ((e6Isogeny k g : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) := by
  refine ⟨scPhi ι, scPhi_injective ι, fun g => ?_⟩
  let ψ₁ : ↥(e6Data_valid.minGroup k) →* ModGL Tag.E6 k₁ :=
    (adjointGroup Tag.E6 k₁).subtype.comp ((e6Isogeny k₁).comp (scPhi ι))
  let ψ₂ : ↥(e6Data_valid.minGroup k) →* ModGL Tag.E6 k₁ :=
    (baseChangeGL (τ := Tag.E6) ι).comp ((adjointGroup Tag.E6 k).subtype.comp (e6Isogeny k))
  have hψ : ψ₁ = ψ₂ :=
    minGroup_hom_eq_of_gens e6Data_valid ψ₁ ψ₂ fun γ hγ c => e6_gen_compat ι hγ c
  exact congrArg (fun ψ => ψ g) hψ

end CFSG.LieType.SeitzGeneration.ExcWideThree
