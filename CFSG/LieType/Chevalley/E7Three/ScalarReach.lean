module

public import CFSG.LieType.Chevalley.MaxTorusPart
public import CFSG.LieType.Chevalley.E7Three.ModelKernel
public import CFSG.LieType.Chevalley.E7Three.ScalarCube
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.ScalarReach

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.TableBExc.Three
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Chevalley.E7Three.ModelKernel
  CFSG.LieType.Chevalley.E7Three.Cube CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Chevalley.MaxTorusPart

section Scalar

variable {L : Type} [Field L] [CharP L 2]

theorem scalarWord_eq_zetaVec (ζ : Lˣ) (hζ : ζ ^ 3 = 1) :
    (scalarWord ζ : ModGL .E7 L) = rootDiagUnit .E7 (zetaVec ζ hζ scalarVec) := by
  rw [scalarWord_val ζ hζ]
  congr 1
  funext j
  rw [zetaVec_apply]
  change ζ ^ CFSG.LieType.Chevalley.E7Three.Weyl.scalarExp j = ζ ^ (scalarVec j).val
  fin_cases j <;> rfl

theorem scalarWord_mem_of_triAct {ζ : Lˣ} (hζ : ζ ^ 3 = 1) {F : Subgroup (ModGL .E7 L)}
    {x : Fin Tag.E7.rank → ZMod 3} (hx : rootDiagUnit .E7 (zetaVec ζ hζ x) ∈ F)
    {ω : List (Fin Tag.E7.rank)} (hω : triAct ω scalarVec = x) :
    (scalarWord ζ : ModGL .E7 L) ∈ F.map (MulAut.conj
      (canonicalRep (coxeterSystem .E7) L ((coxeterSystem .E7).wordProd ω))⁻¹).toMonoidHom := by
  set n := canonicalRep (coxeterSystem .E7) L ((coxeterSystem .E7).wordProd ω)
  have hconj : n * (scalarWord ζ : ModGL .E7 L) * n⁻¹ = rootDiagUnit .E7 (zetaVec ζ hζ x) := by
    rw [scalarWord_eq_zetaVec ζ hζ, canonicalRep_conj_rootDiagUnit, weylTuple_zetaVec_triAct, hω]
  refine ⟨_, hx, ?_⟩
  change n⁻¹ * rootDiagUnit .E7 (zetaVec ζ hζ x) * n⁻¹⁻¹ = _
  rw [← hconj]
  group

end Scalar

section Weyl

theorem exists_modelWord_of_mem_range {w : WeylGroup .E7} (hw : w ∈ modelHomE7.range) :
    ∃ a b c d : ℕ, a < 3 ∧ b < 3 ∧ c < 3 ∧ d < 3 ∧
      w = (coxeterSystem .E7).wordProd (modelWord a b c d) := by
  obtain ⟨y, rfl⟩ := hw
  refine ⟨(y.left.toAdd 0).val, (y.left.toAdd 1).val, (y.left.toAdd 2).val,
    (Multiplicative.toAdd y.right).val, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _,
    ZMod.val_lt _, ?_⟩
  have h1 : modelHomE7 y = modelHomE7 (SemidirectProduct.inl y.left) *
      cE7 ^ (Multiplicative.toAdd y.right).val := by
    change modelHom isModel_E7 y = modelHom isModel_E7 (SemidirectProduct.inl y.left) * _
    rw [modelHom_inl]
    rfl
  rw [h1, modelHomE7_inl, modelWord, CoxeterSystem.wordProd_append,
    CFSG.StandardType.TableBExc.wordProd_replicate]
  rfl

theorem not_three_dvd_index_modelHomE7 :
    ¬ 3 ∣ modelHomE7.range.index := by
  rw [CFSG.StandardType.NoOffExc.index_eq_of_card card_range_modelHomE7
    CFSG.StandardType.NoOffExc.card_weyl_E7 (show 81 * 35840 = 2903040 by norm_num)
    (by norm_num)]
  norm_num

end Weyl

section Procedure

variable {L : Type} [Field L] [CharP L 2]

theorem exists_conj_card_torus_lt [IsAlgClosed L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3)
    {F : Subgroup (ModGL .E7 L)} [Finite F] (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hexp : ∀ x ∈ F, x ^ 3 = 1) (hFN : ∀ x ∈ F, x ∈ monomialSubgroup .E7 L)
    (hFS : ∀ x ∈ F, ∀ hx : x ∈ monomialSubgroup .E7 L,
      weylQuotientHom .E7 L ⟨x, hx⟩ ∈ modelHomE7.range)
    (hFT : ¬ F ≤ torusGroup .E7 L)
    (hno : ∀ g ∈ adjointGroup .E7 L,
      (scalarWord ζ : ModGL .E7 L) ∉ F.map (MulAut.conj g).toMonoidHom) :
    ∃ g ∈ adjointGroup .E7 L, Nat.card ↥(F ⊓ torusGroup .E7 L) <
      Nat.card ↥(F.map (MulAut.conj g).toMonoidHom ⊓ torusGroup .E7 L) := by
  classical
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζo : orderOf ζ = 3 := hζ.eq_orderOf.symm
  have hL3 : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  obtain ⟨n, hnF, hnT⟩ : ∃ n ∈ F, n ∉ torusGroup .E7 L := by
    by_contra h
    exact hFT fun x hx => by_contra fun hxT => h ⟨x, hx, hxT⟩
  set U := F ⊓ torusGroup .E7 L with hU
  have hchar : ∀ u : U, ∃ x : Fin Tag.E7.rank → ZMod 3,
      (u : ModGL .E7 L) = rootDiagUnit .E7 (zetaVec ζ h3 x) := fun u =>
    exists_zetaVec_of_mem_torusGroup hζo h3 (Subgroup.mem_inf.1 u.2).2
      (hexp _ (Subgroup.mem_inf.1 u.2).1)
  choose e he using hchar
  have hnN := hFN n hnF
  have hn3 := weylQuotientHom_pow_eq_one hnN (hexp n hnF)
  obtain ⟨a', b', c', d', ha', hb', hc', hd', hyw⟩ :=
    exists_modelWord_of_mem_range (hFS n hnF hnN)
  have hfix : ∀ (u : U) v, triPairing (e u)
      ((coxeterSystem .E7).wordProd (modelWord a' b' c' d') • v) = triPairing (e u) v := by
    intro u v
    rw [← hyw]
    refine triPairing_weylQuotientHom_smul hζo h3 hnN ?_ v
    rw [← he u]
    exact hcomm _ (Subgroup.mem_inf.1 u.2).1 n hnF
  have hfree : ∀ (u : U) (ω : List (Fin Tag.E7.rank)), triAct ω scalarVec ≠ e u := by
    intro u ω h
    have hx : rootDiagUnit .E7 (zetaVec ζ h3 (e u)) ∈ F := by
      rw [← he u]
      exact (Subgroup.mem_inf.1 u.2).1
    exact hno _ (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem .E7) L _))
      (scalarWord_mem_of_triAct h3 hx h)
  obtain ⟨R, hR, hR0⟩ := exists_kernel_word ha' hb' hc' hd' (by rw [← hyw]; exact hn3) e hfix
    hfree
  have hwK : weylQuotientHom .E7 L ⟨n, hnN⟩ ∈
      kernelWeylGroup (familyChar fun u => zetaVec ζ h3 (e u)) := by
    rw [hyw, hR]
    exact prod_mem_kernelWeylGroup hζo h3 e R hR0
  exact exists_conj_card_torus_lt_of_mem_kernelWeylGroup
    (monomialToralAt_three_of_block a2BlockToral_E7) hL3 (fun u => zetaVec ζ h3 (e u))
    (fun u hu => ⟨⟨u, hu⟩, (he ⟨u, hu⟩).symm⟩) hnF hnT hnN (hexp n hnF) hwK

theorem exists_conj_scalarWord_mem_of_not_toral [IsAlgClosed L]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E7 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E7 L) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hnt : ¬ ∃ g ∈ adjointGroup .E7 L, ∀ x ∈ E, g * x * g⁻¹ ∈ torusGroup .E7 L) :
    ∃ g ∈ adjointGroup .E7 L, (scalarWord ζ : ModGL .E7 L) ∈ E.map (MulAut.conj g).toMonoidHom := by
  classical
  by_contra hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g₀, hg₀G, hmax⟩ := exists_max_card_inf_torus E
  have := finite_map_conj E g₀
  obtain ⟨c, hcG, hcN, hcS, hcard⟩ := exists_conj_monomial_sylow (ℓ := 2) (p := 3) (by norm_num)
    halg not_three_dvd_index_modelHomE7 (map_conj_le hEG hg₀G) (map_conj_comm hcomm g₀)
    (map_conj_pow_eq_one hexp g₀)
  rw [map_conj_map_conj] at hcN hcS hcard
  have hcg₀ : c * g₀ ∈ adjointGroup .E7 L := mul_mem hcG hg₀G
  have := finite_map_conj E (c * g₀)
  obtain ⟨g, hgG, hlt⟩ := exists_conj_card_torus_lt hζ (map_conj_comm hcomm _)
    (map_conj_pow_eq_one hexp _) hcN hcS
    (fun h => hnt ⟨c * g₀, hcg₀, fun x hx => h ⟨x, hx, rfl⟩⟩)
    (fun g hg h => hno ⟨g * (c * g₀), mul_mem hg hcg₀, by rwa [map_conj_map_conj] at h⟩)
  rw [map_conj_map_conj] at hlt
  have := hmax _ (mul_mem hgG hcg₀)
  omega

theorem exists_conj_cubeE_le_of_not_toral [IsAlgClosed L]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E7 L)} [Finite E]
    (hEG : E ≤ adjointGroup .E7 L) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hnt : ¬ ∃ g ∈ adjointGroup .E7 L, ∀ x ∈ E, g * x * g⁻¹ ∈ torusGroup .E7 L) :
    ∃ g ∈ adjointGroup .E7 L,
      Centralizer.cubeE ζ hζ.pow_eq_one ≤ E.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g₁, hg₁, hs⟩ := exists_conj_scalarWord_mem_of_not_toral halg hζ hEG hcomm hexp hnt
  have := finite_map_conj E g₁
  obtain ⟨g₂, hg₂, hcube⟩ := Centralizer.exists_conj_cubeE_le_of_scalar_mem hζ
    (map_conj_le hEG hg₁) (map_conj_comm hcomm g₁) (map_conj_pow_eq_one hexp g₁) hs
    (fun ⟨g, hg, h⟩ => hnt ⟨g * g₁, mul_mem hg hg₁, fun x hx => by
      rw [show g * g₁ * x * (g * g₁)⁻¹ = g * (g₁ * x * g₁⁻¹) * g⁻¹ by group]
      exact h _ ⟨x, hx, rfl⟩⟩)
  rw [map_conj_map_conj] at hcube
  exact ⟨g₂ * g₁, mul_mem hg₂ hg₁, hcube⟩

end Procedure

end CFSG.LieType.Chevalley.E7Three.ScalarReach
