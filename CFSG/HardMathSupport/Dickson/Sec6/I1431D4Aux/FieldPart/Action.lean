module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.Center

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootDiagUnit)
open scoped Pointwise

set_option linter.unusedSectionVars false

variable (K : Type) [Field K]

@[expose] def UP : Subgroup (adjointGroup Tag.D4 K) :=
  (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)

@[expose] def zElt (c : K) : adjointGroup Tag.D4 K :=
  ⟨pinnedX Tag.D4 K hrD4 c, pinnedX_mem_adjointGroup hrD4 c⟩

@[expose] def ZP : Subgroup (adjointGroup Tag.D4 K) := (UP K).lowerCentralSeries 4

variable {K}

theorem zElt_add (c d : K) : zElt K (c + d) = zElt K c * zElt K d :=
  Subtype.ext (pinnedX_add Tag.D4 K hrD4 c d)

theorem zElt_zero : zElt K 0 = 1 := Subtype.ext (pinnedX_zero Tag.D4 K hrD4)

theorem zElt_injective : Function.Injective (zElt K) := fun c d h =>
  pinnedX_injective Tag.D4 K hrD4 (congrArg Subtype.val h)

theorem mem_UP_iff {u : adjointGroup Tag.D4 K} :
    u ∈ UP K ↔ (u : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K :=
  Subgroup.mem_subgroupOf

theorem map_UP : (UP K).map (adjointGroup Tag.D4 K).subtype = posUnipotent Tag.D4 K := by
  rw [UP, Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.2 posUnipotent_le_adjointGroup

theorem map_ZP : (ZP K).map (adjointGroup Tag.D4 K).subtype = rootSubgroup Tag.D4 K hrD4 := by
  rw [ZP, Subgroup.map_lowerCentralSeries, map_UP, lcs_four_eq]

theorem mem_ZP_iff {x : adjointGroup Tag.D4 K} : x ∈ ZP K ↔ ∃ c, x = zElt K c := by
  have h : x ∈ ZP K ↔ (x : ModGL Tag.D4 K) ∈ rootSubgroup Tag.D4 K hrD4 := by
    rw [← map_ZP]
    exact (Subgroup.mem_map_iff_mem (adjointGroup Tag.D4 K).subtype_injective).symm
  rw [h, mem_rootSubgroup]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

theorem zElt_mem_ZP (c : K) : zElt K c ∈ ZP K := mem_ZP_iff.2 ⟨c, rfl⟩

theorem exists_scalar_of_mem_normalizer {x : adjointGroup Tag.D4 K}
    (hx : x ∈ Subgroup.normalizer ((UP K : Subgroup (adjointGroup Tag.D4 K)) :
      Set (adjointGroup Tag.D4 K))) :
    ∃ μ : Kˣ, ∀ c : K, x * zElt K c * x⁻¹ = zElt K ((μ : K) * c) := by
  have hxN : (x : ModGL Tag.D4 K) ∈ Subgroup.normalizer
      ((posUnipotent Tag.D4 K : Subgroup (ModGL Tag.D4 K)) : Set (ModGL Tag.D4 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hgP : g ∈ adjointGroup Tag.D4 K := posUnipotent_le_adjointGroup hg
      have h1 := (Subgroup.mem_normalizer_iff.1 hx ⟨g, hgP⟩).1 (mem_UP_iff.2 hg)
      exact mem_UP_iff.1 h1
    · intro hg
      have hgP' : (x : ModGL Tag.D4 K) * g * (x : ModGL Tag.D4 K)⁻¹ ∈ adjointGroup Tag.D4 K :=
        posUnipotent_le_adjointGroup hg
      have hgP : g ∈ adjointGroup Tag.D4 K := by
        have := mul_mem (mul_mem (inv_mem x.2) hgP') x.2
        simpa [mul_assoc] using this
      have h1 := (Subgroup.mem_normalizer_iff.1 hx ⟨g, hgP⟩).2 (mem_UP_iff.2 hg)
      exact mem_UP_iff.1 h1
  have hxB : (x : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := by
    have := (borel_self_normalizers Tag.D4 K).1
    rw [← this]
    exact Subgroup.mem_inf.2 ⟨x.2, hxN⟩
  have hBset := ((triangular_borel_structure.{0, 0} Tag.D4 K).2.2.2.2.1)
  have hxm : (x : ModGL Tag.D4 K) ∈ (SetLike.coe (torusGroup Tag.D4 K) *
      SetLike.coe (posUnipotent Tag.D4 K) : Set (ModGL Tag.D4 K)) := by
    rw [← hBset]
    exact hxB
  obtain ⟨t, ht, u, hu, hxtu⟩ := hxm
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  refine ⟨rootChar l hrD4, fun c => ?_⟩
  refine Subtype.ext ?_
  have hz : pinnedX Tag.D4 K hrD4 c ∈ rootSubgroup Tag.D4 K hrD4 :=
    mem_rootSubgroup.2 ⟨c, rfl⟩
  have hcomm : pinnedX Tag.D4 K hrD4 c * u = u * pinnedX Tag.D4 K hrD4 c :=
    commute_of_mem_rootSubgroup_hrD4 K hz hu
  change (x : ModGL Tag.D4 K) * pinnedX Tag.D4 K hrD4 c * (x : ModGL Tag.D4 K)⁻¹ =
    pinnedX Tag.D4 K hrD4 ((rootChar l hrD4 : K) * c)
  rw [← hxtu, hl]
  have h2 : (rootDiagUnit Tag.D4 l * u) * pinnedX Tag.D4 K hrD4 c *
      (rootDiagUnit Tag.D4 l * u)⁻¹ = rootDiagUnit Tag.D4 l * pinnedX Tag.D4 K hrD4 c *
      (rootDiagUnit Tag.D4 l)⁻¹ := by
    have h3 : u * pinnedX Tag.D4 K hrD4 c * u⁻¹ = pinnedX Tag.D4 K hrD4 c := by
      rw [← hcomm, mul_inv_cancel_right]
    calc (rootDiagUnit Tag.D4 l * u) * pinnedX Tag.D4 K hrD4 c * (rootDiagUnit Tag.D4 l * u)⁻¹
        = rootDiagUnit Tag.D4 l * (u * pinnedX Tag.D4 K hrD4 c * u⁻¹) *
          (rootDiagUnit Tag.D4 l)⁻¹ := by group
      _ = _ := by rw [h3]
  rw [h2]
  exact rootDiagUnit_conj_pinnedX l isRoot_hrD4 c

@[expose] def ctr : Fin Tag.D4.rank := ⟨2, by decide⟩

@[expose] def hElt (μ : Kˣ) : adjointGroup Tag.D4 K :=
  ⟨torusElt Tag.D4 K ctr μ, torusElt_mem_adjointGroup ctr μ⟩

theorem hElt_mul_zElt (μ : Kˣ) (c : K) : hElt μ * zElt K c * (hElt μ)⁻¹ = zElt K ((μ : K) * c) := by
  refine Subtype.ext ?_
  change torusElt Tag.D4 K ctr μ * pinnedX Tag.D4 K hrD4 c * (torusElt Tag.D4 K ctr μ)⁻¹ =
    pinnedX Tag.D4 K hrD4 ((μ : K) * c)
  have key : rootChar (fun j : Fin Tag.D4.rank => μ ^ Tag.D4.cartan ctr j) hrD4 = μ := by
    unfold rootChar
    have h4 := Fin.prod_univ_four (fun i : Fin 4 => (μ ^ Tag.D4.cartan ctr i) ^ hrD4 i)
    refine h4.trans ?_
    simp only [← zpow_mul]
    rw [← zpow_add, ← zpow_add, ← zpow_add]
    convert zpow_one μ using 2
    decide
  rw [torusElt_eq_rootDiagUnit, rootDiagUnit_conj_pinnedX _ isRoot_hrD4, key]

theorem hElt_mem_normalizer (μ : Kˣ) : hElt μ ∈ Subgroup.normalizer
    ((UP K : Subgroup (adjointGroup Tag.D4 K)) : Set (adjointGroup Tag.D4 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have key : ∀ (μ : Kˣ) (g : adjointGroup Tag.D4 K), g ∈ UP K → hElt μ * g * (hElt μ)⁻¹ ∈ UP K := by
    intro μ g hg
    rw [mem_UP_iff] at hg ⊢
    have := torusElt_mem_normalizer_posUnipotent (R := K) (τ := Tag.D4) ctr μ
    exact (Subgroup.mem_normalizer_iff.1 this _).1 hg
  refine ⟨key μ g, fun hg => ?_⟩
  have := key μ⁻¹ _ hg
  have hinv : hElt (μ⁻¹ : Kˣ) = (hElt μ : adjointGroup Tag.D4 K)⁻¹ := by
    refine Subtype.ext ?_
    change torusElt Tag.D4 K ctr (μ⁻¹) = (torusElt Tag.D4 K ctr μ)⁻¹
    rw [eq_inv_iff_mul_eq_one, ← torusElt_mul, inv_mul_cancel, torusElt_one]
  rw [hinv, inv_inv] at this
  convert this using 1
  group

end CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart
