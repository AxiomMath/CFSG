module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ISign
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ISignComb
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenLeviCentralizer
public import CFSG.Quasithin.H13.NQCatLieCartanG2

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
open CFSG.RankThree.Chevalley.NativeLevi
open scoped Pointwise
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Borel

variable {K : Type} [Field K] [Finite K]


theorem mem_borelGroup_of_stable (g : ↥(adjointGroup Tag.D4 K))
    (hgU : ((posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)).map
      (MulAut.conj g).toMonoidHom = (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)) :
    (g : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := by
  set H : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) with hH
  have hmemH : ∀ y : ↥(adjointGroup Tag.D4 K), y ∈ H ↔ (y : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K :=
    fun y => by rw [hH, Subgroup.mem_subgroupOf]
  have hgH' : H.map (MulAut.conj g)⁻¹.toMonoidHom = H := map_inv_toMonoidHom_of_map_eq hgU
  have hnorm : (g : ModGL Tag.D4 K) ∈
      Subgroup.normalizer (posUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxG : x ∈ adjointGroup Tag.D4 K := posUnipotent_le_adjointGroup hx
      have hmem : (⟨x, hxG⟩ : ↥(adjointGroup Tag.D4 K)) ∈ H := (hmemH _).2 hx
      have h1 : (MulAut.conj g) ⟨x, hxG⟩ ∈ H.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hgU] at h1
      exact (hmemH _).1 h1
    · intro hx
      have hxG' : (g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹ ∈ adjointGroup Tag.D4 K :=
        posUnipotent_le_adjointGroup hx
      have hxG : x ∈ adjointGroup Tag.D4 K := by
        have := mul_mem (mul_mem (inv_mem g.2) hxG') g.2
        simpa [mul_assoc] using this
      have hmem : (⟨(g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹, hxG'⟩ :
          ↥(adjointGroup Tag.D4 K)) ∈ H := (hmemH _).2 hx
      have h1 : (MulAut.conj g)⁻¹ ⟨_, hxG'⟩ ∈ H.map (MulAut.conj g)⁻¹.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hgH'] at h1
      have e : (MulAut.conj g)⁻¹ (⟨(g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹, hxG'⟩ :
          ↥(adjointGroup Tag.D4 K)) = ⟨x, hxG⟩ := by
        apply Subtype.ext
        simp [MulAut.conj_apply, mul_assoc]
      rw [e] at h1
      exact (hmemH _).1 h1
  rw [← CFSG.Quasithin.H13.NQCat.LieCartan.G2.normalizer_posUnipotent_inf_eq
    (K := K) (τ := Tag.D4)]
  exact ⟨hnorm, g.2⟩

theorem signData_of_involution {g : ModGL Tag.D4 K} (hg : BorelScalar g) (hg2 : g * g = 1) :
    SignData hg.s :=
  ⟨fun v hv => borelScalar_sq hg hg2 (by
      obtain ⟨h1, h2, -⟩ := mem_d4RootsFrom.1 hv
      exact ⟨h1, h2⟩),
    fun γ hγ δ hδ hβ => borelScalar_add hg
      (by obtain ⟨h1, h2, -⟩ := mem_d4RootsFrom.1 hγ; exact ⟨h1, h2⟩)
      (by obtain ⟨h1, h2, -⟩ := mem_d4RootsFrom.1 hδ; exact ⟨h1, h2⟩)
      (mem_d4RootsFrom.1 hβ).1⟩

theorem torus_eq_one_of_char_eq_one {h : ModGL Tag.D4 K} (hh : h ∈ torusGroup Tag.D4 K)
    (h1 : ∀ v : D4Vec, IsRoot Tag.D4 v → 0 < height v → torusRootChar h v = 1) : h = 1 := by
  have hst := triangular_borel_structure.{0, 0} Tag.D4 K
  refine Units.ext (rootModule_end_ext (fun j => ?_) (fun α hα => ?_))
  · rw [Units.val_one, Module.End.one_apply]
    exact (hst.2.1 h hh).1 j
  · rw [Units.val_one, Module.End.one_apply, apply_rootVec_of_mem_torusGroup hh hα]
    have : torusRootChar h α = 1 := by
      rcases IsRoot.height_pos_or_neg hα with hp | hn
      · exact h1 α hα hp
      · have hα' : IsRoot Tag.D4 (-α) := IsRoot.neg hα
        have h2 := h1 (-α) hα' (by rw [height_neg]; omega)
        have h3 := torusRootChar_neg hh hα'
        rw [neg_neg] at h3
        rw [h3, h2, inv_one]
    rw [this, one_smul]

theorem eq_one_of_borelScalar_eq_one [CharP K 3] (g : ↥(adjointGroup Tag.D4 K))
    (hgB : (g : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K) (hg2 : g * g = 1)
    (hs : ∀ v ∈ d4RootsFrom 1, (borelScalar_of_mem_borelGroup hgB).s v = 1) : g = 1 := by
  classical
  have hst := triangular_borel_structure.{0, 0} Tag.D4 K
  have hgB' : (g : ModGL Tag.D4 K) ∈
      (SetLike.coe (torusGroup Tag.D4 K) * SetLike.coe (posUnipotent Tag.D4 K) : Set (ModGL Tag.D4 K)) := by
    rw [← hst.2.2.2.2.1]; exact hgB
  obtain ⟨h, hh, u, hu, hgeq0⟩ := hgB'
  have hgeq : (g : ModGL Tag.D4 K) = h * u := hgeq0.symm
  have hhs := borelScalar_of_mem_torusGroup hh
  have hsh : ∀ v : D4Vec, IsRoot Tag.D4 v → 0 < height v → hhs.s v = torusRootChar h v := by
    intro v hv hpos
    rw [borelScalar_s_eq hhs ⟨hv, hpos⟩, conj_pinnedX_of_mem_torusGroup hh hv, mul_one,
      rootCoord_self ⟨hv, hpos⟩]
  have hchar : ∀ v : D4Vec, IsRoot Tag.D4 v → 0 < height v → torusRootChar h v = 1 := by
    intro v hv hpos
    have hv' : v ∈ d4RootsFrom 1 := mem_d4RootsFrom.2 ⟨hv, hpos, hpos⟩
    have e1 := hs v hv'
    rw [borelScalar_s_eq _ ⟨hv, hpos⟩] at e1
    have hxm : pinnedX Tag.D4 K v 1 ∈ heightSeries Tag.D4 K (height v) :=
      pinnedX_mem_heightSeries_height ⟨hv, hpos⟩ 1
    have hym : u * pinnedX Tag.D4 K v 1 * u⁻¹ ∈ heightSeries Tag.D4 K (height v) :=
      (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K _ hu) _).1 hxm
    have e2 : (g : ModGL Tag.D4 K) * pinnedX Tag.D4 K v 1 * (g : ModGL Tag.D4 K)⁻¹ =
        h * (u * pinnedX Tag.D4 K v 1 * u⁻¹) * h⁻¹ := by
      rw [hgeq]; group
    rw [e2, (hhs.spec.2 v ⟨hv, hpos⟩ _ hym), hsh v hv hpos,
      rootCoord_conj ⟨hv, hpos⟩ hu hxm, rootCoord_self ⟨hv, hpos⟩, mul_one] at e1
    exact e1
  have h1 : h = 1 := torus_eq_one_of_char_eq_one hh hchar
  rw [h1, one_mul] at hgeq
  have hgU : g ∈ (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) := by
    rw [Subgroup.mem_subgroupOf, hgeq]; exact hu
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨P₀, hP₀⟩ := (exceptional_ordinary_Sylow_opposition Tag.D4 K 3 w₀ hw₀).1
  have hp : IsPGroup 3 ((posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)) := by
    rw [← hP₀]; exact P₀.isPGroup'
  obtain ⟨k, hk⟩ := hp ⟨g, hgU⟩
  have hord : orderOf (g : ↥(adjointGroup Tag.D4 K)) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [pow_two]; exact hg2)
  have hord2 : orderOf (g : ↥(adjointGroup Tag.D4 K)) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  have : orderOf (g : ↥(adjointGroup Tag.D4 K)) = 1 := by
    have h2 : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    exact Nat.eq_one_of_dvd_coprimes h2 hord hord2
  exact orderOf_eq_one_iff.1 this

end Borel

end CFSG.LocalAnalysis.GLTheoremA
