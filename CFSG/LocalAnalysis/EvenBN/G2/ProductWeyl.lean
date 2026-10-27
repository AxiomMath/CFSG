module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (diagonalHom)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace ProductWeylAux

section Abstract

variable {Γ : Type*} [Group Γ]

theorem mem_conj_iff_of_mul_self {g : Γ} (hg : g * g = 1) {A : Subgroup Γ} {x : Γ} :
    x ∈ Aᵍ[g] ↔ g * x * g ∈ A := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hgi]
    have : g * (g * y * g) * g = y := by
      calc g * (g * y * g) * g = (g * g) * y * (g * g) := by group
        _ = y := by rw [hg, one_mul, mul_one]
    rwa [this]
  · intro h
    refine ⟨g * x * g, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hgi]
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
      _ = x := by rw [hg, one_mul, mul_one]

theorem conj_le_of_mem {g : Γ} {A K : Subgroup Γ} (hA : A ≤ K) (hg : g ∈ K) : Aᵍ[g] ≤ K := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact mul_mem (mul_mem (inv_mem hg) (hA hy)) hg

theorem conj_eq_of_mem_normalizer {g : Γ} (hg : g * g = 1) {A : Subgroup Γ}
    (hn : g ∈ normalizer (A : Set Γ)) : Aᵍ[g] = A := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  ext x
  rw [mem_conj_iff_of_mul_self hg]
  have := (mem_normalizer_iff.1 hn x).symm
  rwa [hgi] at this

theorem eq_sup_conj_of_generated {S R D' Lv K₁ : Subgroup Γ} {g : Γ} (hS : S = R ⊔ D')
    (hLv : Lv = R ⊔ Rᵍ[g]) (hK : K₁ = D' ⊔ Lv) (hg : g ∈ Lv) (hD : D' ≤ S) :
    K₁ = S ⊔ Sᵍ[g] := by
  have hRS : R ≤ S := hS ▸ le_sup_left
  have hRLv : R ≤ Lv := hLv ▸ le_sup_left
  have hLvK : Lv ≤ K₁ := hK ▸ le_sup_right
  have hSK : S ≤ K₁ := hS ▸ sup_le (hRLv.trans hLvK) (hK ▸ le_sup_left)
  apply le_antisymm
  · rw [hK]
    refine sup_le (hD.trans le_sup_left) ?_
    rw [hLv]
    exact sup_le (hRS.trans le_sup_left)
      ((Subgroup.map_mono hRS : Rᵍ[g] ≤ Sᵍ[g]).trans le_sup_right)
  · exact sup_le hSK (conj_le_of_mem hSK (hLvK hg))

end Abstract

section Reflections

theorem reflect_r_nr : reflect .G2 g2ir g2nr = g2r := List.ofFn_injective (by decide +kernel)

theorem reflect_a_na : reflect .G2 g2ia g2na = g2a := List.ofFn_injective (by decide +kernel)

end Reflections

section Model

variable {K : Type} [Field K]

theorem adjointGroup_le_leviA_sup_leviB :
    adjointGroup .G2 K ≤ Model.leviA K ⊔ Model.leviB K := by
  have hi : ∀ i : Fin Tag.G2.rank, i = g2ia ∨ i = g2ir := fun i => by
    fin_cases i
    exacts [Or.inl rfl, Or.inr rfl]
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hg | hg⟩
  · have hx : g = xUnit .G2 K i c := Units.ext hg
    rw [hx]
    rcases hi i with rfl | rfl
    · exact mem_sup_right (xUnit_mem_g2RankOne _ c)
    · exact mem_sup_left (xUnit_mem_g2RankOne _ c)
  · have hy : g = yUnit .G2 K i c := Units.ext hg
    rw [hy]
    rcases hi i with rfl | rfl
    · exact mem_sup_right (yUnit_mem_g2RankOne _ c)
    · exact mem_sup_left (yUnit_mem_g2RankOne _ c)

end Model

end ProductWeylAux

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

namespace ProductWeylAux

theorem mem_rootGroup_iff (d : G2Data L K) {s : Fin Tag.G2.rank → ℤ} {x : G} :
    x ∈ d.rootGroup s ↔
      ∃ c : K, x = d.emb ⟨pinnedX .G2 K s c, pinnedX_mem_adjointGroup s c⟩ := by
  rw [G2Data.rootGroup, d.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hg
    exact ⟨c, congrArg d.emb (Subtype.ext hc.symm)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, mem_rootSubgroup.2 ⟨c, rfl⟩, rfl⟩

theorem rootGroup_conj_wa (d : G2Data L K) (hK : 4 ≤ Nat.card K)
    {s t : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s) (ht : IsRoot .G2 t)
    (h1 : reflect .G2 g2ir s = t) (h2 : reflect .G2 g2ir t = s) :
    (d.rootGroup s)ᵍ[d.wa] = d.rootGroup t := by
  obtain ⟨-, -, hwa, -, hconj, -⟩ := d.yamada_3_7_G hK
  subst h1
  ext x
  rw [mem_conj_iff_of_mul_self hwa, mem_rootGroup_iff, mem_rootGroup_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hconj hs c, ← hc]
    calc x = (d.wa * d.wa) * x * (d.wa * d.wa) := by rw [hwa, one_mul, mul_one]
      _ = d.wa * (d.wa * x * d.wa) * d.wa := by group
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    have := hconj ht c
    rw [h2] at this
    exact this

theorem rootGroup_conj_wb (d : G2Data L K) (hK : 4 ≤ Nat.card K)
    {s t : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s) (ht : IsRoot .G2 t)
    (h1 : reflect .G2 g2ia s = t) (h2 : reflect .G2 g2ia t = s) :
    (d.rootGroup s)ᵍ[d.wb] = d.rootGroup t := by
  obtain ⟨-, -, -, hwb, -, hconj⟩ := d.yamada_3_7_G hK
  subst h1
  ext x
  rw [mem_conj_iff_of_mul_self hwb, mem_rootGroup_iff, mem_rootGroup_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hconj hs c, ← hc]
    calc x = (d.wb * d.wb) * x * (d.wb * d.wb) := by rw [hwb, one_mul, mul_one]
      _ = d.wb * (d.wb * x * d.wb) * d.wb := by group
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    have := hconj ht c
    rw [h2] at this
    exact this

theorem wa_mem_leviA (d : G2Data L K) : d.wa ∈ d.leviA :=
  d.emb_mem_image (g := ⟨Model.wa K, Model.wa_mem_adjointGroup K⟩)
    (weylElt_mem_g2RankOne g2ir 1)

theorem wb_mem_leviB (d : G2Data L K) : d.wb ∈ d.leviB :=
  d.emb_mem_image (g := ⟨Model.wb K, Model.wb_mem_adjointGroup K⟩)
    (weylElt_mem_g2RankOne g2ia 1)

theorem leviA_eq (d : G2Data L K) : d.leviA = d.rootGroup g2r ⊔ d.rootGroup g2nr := by
  rw [G2Data.leviA, G2Data.rootGroup, G2Data.rootGroup,
    ← d.image_sup (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)]
  congr 1
  rw [Model.leviA, g2RankOne_r_eq, Subgroup.closure_union]
  rfl

theorem leviB_eq (d : G2Data L K) : d.leviB = d.rootGroup g2a ⊔ d.rootGroup g2na := by
  rw [G2Data.leviB, G2Data.rootGroup, G2Data.rootGroup,
    ← d.image_sup (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)]
  congr 1
  rw [Model.leviB, g2RankOne_a_eq, Subgroup.closure_union]
  rfl

theorem S_eq_rootGroup_r_sup_D (d : G2Data L K) : d.S = d.rootGroup g2r ⊔ d.D := by
  obtain ⟨-, -, -, -, -, hM, -, -, hS⟩ := d.yamada_defs
  obtain ⟨-, -, -, -, -, hFD, -, -, -, -⟩ := d.inclusions
  rw [← hS, ← hM]
  exact le_antisymm (sup_le le_sup_right (sup_le le_sup_left (hFD.trans le_sup_right)))
    (sup_le (le_sup_left.trans le_sup_right) le_sup_left)

theorem S_eq_rootGroup_a_sup_M (d : G2Data L K) : d.S = d.rootGroup g2a ⊔ d.M := by
  obtain ⟨-, -, -, -, hD, -, -, -, hS⟩ := d.yamada_defs
  obtain ⟨-, -, -, -, -, -, hFM, -, -, -⟩ := d.inclusions
  rw [← hS, ← hD]
  exact le_antisymm (sup_le (sup_le le_sup_left (hFM.trans le_sup_right)) le_sup_right)
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right)

theorem yamadaK₁_eq_sup_conj (d : G2Data L K) (hK : 4 ≤ Nat.card K) :
    yamadaK₁ d = d.S ⊔ d.Sᵍ[d.wa] := by
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  refine eq_sup_conj_of_generated (S_eq_rootGroup_r_sup_D d) ?_ (yamadaK₁_eq d hK)
    (wa_mem_leviA d) hDS
  rw [leviA_eq d, rootGroup_conj_wa d hK isRoot_g2r isRoot_g2nr reflect_r_r reflect_r_nr]

theorem yamadaK₂_eq_sup_conj (d : G2Data L K) (hK : 4 ≤ Nat.card K) :
    yamadaK₂ d = d.S ⊔ d.Sᵍ[d.wb] := by
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  refine eq_sup_conj_of_generated (S_eq_rootGroup_a_sup_M d) ?_ (yamadaK₂_eq d hK)
    (wb_mem_leviB d) hMS
  rw [leviB_eq d, rootGroup_conj_wb d hK isRoot_g2a isRoot_g2na reflect_a_a reflect_a_na]

theorem yamadaK₁_sup_yamadaK₂ (d : G2Data L K) (hK : 4 ≤ Nat.card K) :
    yamadaK₁ d ⊔ yamadaK₂ d = L := by
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, hSL⟩ := d.inclusions
  have hK₁ : yamadaK₁ d ≤ L := by
    rw [yamadaK₁_eq d hK]
    exact sup_le (hDS.trans hSL) (d.image_le _)
  have hK₂ : yamadaK₂ d ≤ L := by
    rw [yamadaK₂_eq d hK]
    exact sup_le (hMS.trans hSL) (d.image_le _)
  refine le_antisymm (sup_le hK₁ hK₂) ?_
  have hle : d.leviA ⊔ d.leviB ≤ yamadaK₁ d ⊔ yamadaK₂ d := by
    rw [yamadaK₁_eq d hK, yamadaK₂_eq d hK]
    exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)
  calc L = d.image (adjointGroup .G2 K) := d.image_adjointGroup.symm
    _ ≤ d.image (Model.leviA K ⊔ Model.leviB K) := d.image_mono adjointGroup_le_leviA_sup_leviB
    _ = d.leviA ⊔ d.leviB :=
        d.image_sup (Model.leviA_le_adjointGroup K) (Model.leviB_le_adjointGroup K)
    _ ≤ yamadaK₁ d ⊔ yamadaK₂ d := hle

theorem yamadaK₁_le_normalizer_D (d : G2Data L K) (hK : 4 ≤ Nat.card K) :
    yamadaK₁ d ≤ normalizer (d.D : Set G) := by
  rw [yamadaK₁_eq d hK]
  refine sup_le Subgroup.le_normalizer ?_
  calc d.leviA ≤ d.D ⊔ (d.leviA ⊔ d.J₃) := le_sup_of_le_right le_sup_left
    _ = L ⊓ normalizer (d.D : Set G) := (d.yamada_3_13_2_G).2.1.symm
    _ ≤ normalizer (d.D : Set G) := inf_le_right

theorem yamadaK₂_le_normalizer_M (d : G2Data L K) (hK : 4 ≤ Nat.card K) :
    yamadaK₂ d ≤ normalizer (d.M : Set G) := by
  rw [yamadaK₂_eq d hK]
  refine sup_le Subgroup.le_normalizer ?_
  calc d.leviB ≤ d.M ⊔ (d.leviB ⊔ d.J₄) := le_sup_of_le_right le_sup_left
    _ = L ⊓ normalizer (d.M : Set G) := (d.yamada_3_13_3_G).2.2.1.symm
    _ ≤ normalizer (d.M : Set G) := inf_le_right

end ProductWeylAux

namespace G2Data

variable (d : G2Data L K)

theorem weyl_facts (hK : 4 ≤ Nat.card K) :
    (d.wa * d.wa = 1 ∧ d.wb * d.wb = 1 ∧ (d.wa * d.wb) ^ 3 = (d.wb * d.wa) ^ 3) ∧
    ((d.rootGroup g2r)ᵍ[d.wb] = d.rootGroup g2u ∧ (d.rootGroup g2u)ᵍ[d.wb] = d.rootGroup g2r ∧
      (d.rootGroup g2v)ᵍ[d.wb] = d.rootGroup g2v ∧
      (d.rootGroup g2b)ᵍ[d.wb] = d.rootGroup g2c ∧ (d.rootGroup g2c)ᵍ[d.wb] = d.rootGroup g2b ∧
      (d.rootGroup g2a)ᵍ[d.wa] = d.rootGroup g2b ∧ (d.rootGroup g2b)ᵍ[d.wa] = d.rootGroup g2a ∧
      (d.rootGroup g2u)ᵍ[d.wa] = d.rootGroup g2v ∧ (d.rootGroup g2v)ᵍ[d.wa] = d.rootGroup g2u ∧
      (d.rootGroup g2c)ᵍ[d.wa] = d.rootGroup g2c) ∧
    (d.S = d.rootGroup g2r ⊔ d.D ∧ d.S = d.rootGroup g2a ⊔ d.M ∧
      (d.D.subgroupOf (yamadaK₁ d)).Normal ∧ (d.M.subgroupOf (yamadaK₂ d)).Normal ∧
      d.Dᵍ[d.wa] = d.D ∧ d.Mᵍ[d.wb] = d.M) ∧
    (yamadaK₁ d = d.S ⊔ d.Sᵍ[d.wa] ∧ yamadaK₂ d = d.S ⊔ d.Sᵍ[d.wb]) ∧
    yamadaK₁ d ⊔ yamadaK₂ d = L ∧
    (⁅yamadaK₁ d, yamadaK₁ d⁆ = yamadaK₁ d ∧ ⁅yamadaK₂ d, yamadaK₂ d⁆ = yamadaK₂ d) := by
  obtain ⟨-, -, hwa, hwb, -, -⟩ := d.yamada_3_7_G hK
  have hord := (d.yamada_3_8_G).2.2.2.1
  have hD : d.D ≤ yamadaK₁ d := by
    rw [yamadaK₁_eq d hK]
    exact le_sup_left
  have hM : d.M ≤ yamadaK₂ d := by
    rw [yamadaK₂_eq d hK]
    exact le_sup_left
  refine ⟨⟨hwa, hwb, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨ProductWeylAux.S_eq_rootGroup_r_sup_D d, ProductWeylAux.S_eq_rootGroup_a_sup_M d,
      (normal_subgroupOf_iff_le_normalizer hD).2 (ProductWeylAux.yamadaK₁_le_normalizer_D d hK),
      (normal_subgroupOf_iff_le_normalizer hM).2 (ProductWeylAux.yamadaK₂_le_normalizer_M d hK),
      ProductWeylAux.conj_eq_of_mem_normalizer hwa
        (ProductWeylAux.yamadaK₁_le_normalizer_D d hK (by
          rw [yamadaK₁_eq d hK]
          exact mem_sup_right (ProductWeylAux.wa_mem_leviA d))),
      ProductWeylAux.conj_eq_of_mem_normalizer hwb
        (ProductWeylAux.yamadaK₂_le_normalizer_M d hK (by
          rw [yamadaK₂_eq d hK]
          exact mem_sup_right (ProductWeylAux.wb_mem_leviB d)))⟩,
    ⟨ProductWeylAux.yamadaK₁_eq_sup_conj d hK, ProductWeylAux.yamadaK₂_eq_sup_conj d hK⟩,
    ProductWeylAux.yamadaK₁_sup_yamadaK₂ d hK, ?_⟩
  · have h6 : (d.wa * d.wb) ^ 6 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    have hinv : d.wb * d.wa = (d.wa * d.wb)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hwa, inv_eq_of_mul_eq_one_right hwb]
    rw [hinv, inv_pow, eq_inv_iff_mul_eq_one, ← pow_add]
    exact h6
  · exact ProductWeylAux.rootGroup_conj_wb d hK isRoot_g2r isRoot_g2u reflect_a_r reflect_a_u
  · exact ProductWeylAux.rootGroup_conj_wb d hK isRoot_g2u isRoot_g2r reflect_a_u reflect_a_r
  · exact ProductWeylAux.rootGroup_conj_wb d hK isRoot_g2v isRoot_g2v reflect_a_v reflect_a_v
  · exact ProductWeylAux.rootGroup_conj_wb d hK isRoot_g2b isRoot_g2c reflect_a_b reflect_a_c
  · exact ProductWeylAux.rootGroup_conj_wb d hK isRoot_g2c isRoot_g2b reflect_a_c reflect_a_b
  · exact ProductWeylAux.rootGroup_conj_wa d hK isRoot_g2a isRoot_g2b reflect_r_a reflect_r_b
  · exact ProductWeylAux.rootGroup_conj_wa d hK isRoot_g2b isRoot_g2a reflect_r_b reflect_r_a
  · exact ProductWeylAux.rootGroup_conj_wa d hK isRoot_g2u isRoot_g2v reflect_r_u reflect_r_v
  · exact ProductWeylAux.rootGroup_conj_wa d hK isRoot_g2v isRoot_g2u reflect_r_v reflect_r_u
  · exact ProductWeylAux.rootGroup_conj_wa d hK isRoot_g2c isRoot_g2c reflect_r_c reflect_r_c
  · rw [yamadaK₁_eq d hK, yamadaK₂_eq d hK]
    exact ⟨(d.yamada_3_13_4_G hK).2.1, (d.yamada_3_13_4_G hK).2.2.2⟩

end G2Data

end Local

end CFSG.LocalAnalysis.EvenBN.G2
