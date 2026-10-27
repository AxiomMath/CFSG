module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.G2Part1

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem exists_sl2_hom_range_g2RankOne :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) K →* ModGL .G2 K,
      Function.Injective ψ ∧ ψ.range = g2RankOne K g2ir := by
  obtain ⟨φ, hφ, hx, hy⟩ := CFSG.LieType.Steinberg.Adjoint.g2_exists_sl2_hom (K := K) g2ir
  have hx' : ∀ c : K, ((φ (CFSG.LieType.Steinberg.sl2Upper c) : adjointGroup .G2 K) :
      ModGL .G2 K) = xUnit .G2 K g2ir c := fun c => by
    refine Units.ext ?_
    rw [hx c]
    exact CFSG.LieType.Steinberg.Adjoint.endHom_xElt (i := g2ir) (rootOperatorFamily .G2) c
  have hy' : ∀ c : K, ((φ (CFSG.LieType.Steinberg.sl2Lower c) : adjointGroup .G2 K) :
      ModGL .G2 K) = yUnit .G2 K g2ir c := fun c => by
    refine Units.ext ?_
    rw [hy c]
    exact CFSG.LieType.Steinberg.Adjoint.endHom_yElt (i := g2ir) (rootOperatorFamily .G2) c
  refine ⟨(adjointGroup .G2 K).subtype.comp φ, (adjointGroup .G2 K).subtype_injective.comp hφ, ?_⟩
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    obtain ⟨e, a, b, c, rfl⟩ := CFSG.LieType.Steinberg.Adjoint.sl2_eq_prod s
    show ((φ _ : adjointGroup .G2 K) : ModGL .G2 K) ∈ g2RankOne K g2ir
    rw [map_mul, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hx', hy',
      hx', hy']
    exact mul_mem (mul_mem (mul_mem (yUnit_mem_g2RankOne _ _) (xUnit_mem_g2RankOne _ _))
      (yUnit_mem_g2RankOne _ _)) (xUnit_mem_g2RankOne _ _)
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨CFSG.LieType.Steinberg.sl2Upper c, hx' c⟩
    · exact ⟨CFSG.LieType.Steinberg.sl2Lower c, hy' c⟩

theorem nonempty_mulEquiv_g2RankOne :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥(g2RankOne K g2ir)) := by
  obtain ⟨ψ, hψ, hrange⟩ := exists_sl2_hom_range_g2RankOne (K := K)
  exact ⟨(MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)⟩

theorem isQuasisimple_g2RankOne [Finite K] (hK : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple ↥(g2RankOne K g2ir) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_g2RankOne (K := K)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 hK)

theorem isSolvable_g2RankOne_of_card_three [Finite K] (hK : Nat.card K = 3) :
    Group.IsSolvable ↥(g2RankOne K g2ir) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_g2RankOne (K := K)
  haveI := CFSG.GH74.GLS.IVK.GHInv.isSolvable_sl2_of_card_three hK
  exact solvable_of_surjective (f := e.toMonoidHom) e.surjective

private theorem g2RankOne_commute_g2Z {l z : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ir)
    (hz : z ∈ g2Z K) : l * z = z * l := by
  obtain ⟨y, rfl⟩ := (mem_rootSubgroup (τ := .G2) (R := K)).1 hz
  exact (commute_g2RankOne_pinnedX_c hl y).eq

variable (K) in
private def g2ActsSub : Subgroup ↥(g2RankOne K g2ir) where
  carrier := {l | ∀ q ∈ g2Q K, (l : ModGL .G2 K) * q * (l : ModGL .G2 K)⁻¹ * q⁻¹ ∈ g2Z K}
  one_mem' := by
    intro q _
    simp only [Subgroup.coe_one, one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _
  mul_mem' := by
    intro l l' hl hl' q hq
    have hz := hl' q hq
    have hcomm := g2RankOne_commute_g2Z l.2 hz
    have e : ((l * l' : ↥(g2RankOne K g2ir)) : ModGL .G2 K) * q *
        ((l * l' : ↥(g2RankOne K g2ir)) : ModGL .G2 K)⁻¹ * q⁻¹ =
        ((l' : ModGL .G2 K) * q * (l' : ModGL .G2 K)⁻¹ * q⁻¹) *
          ((l : ModGL .G2 K) * q * (l : ModGL .G2 K)⁻¹ * q⁻¹) := by
      calc ((l * l' : ↥(g2RankOne K g2ir)) : ModGL .G2 K) * q *
            ((l * l' : ↥(g2RankOne K g2ir)) : ModGL .G2 K)⁻¹ * q⁻¹
          = (l : ModGL .G2 K) * ((l' : ModGL .G2 K) * q * (l' : ModGL .G2 K)⁻¹ * q⁻¹) *
              (q * (l : ModGL .G2 K)⁻¹ * q⁻¹) := by
            simp only [Subgroup.coe_mul]; group
        _ = ((l' : ModGL .G2 K) * q * (l' : ModGL .G2 K)⁻¹ * q⁻¹) * (l : ModGL .G2 K) *
              (q * (l : ModGL .G2 K)⁻¹ * q⁻¹) := by rw [hcomm]
        _ = ((l' : ModGL .G2 K) * q * (l' : ModGL .G2 K)⁻¹ * q⁻¹) *
              ((l : ModGL .G2 K) * q * (l : ModGL .G2 K)⁻¹ * q⁻¹) := by group
    show ((l * l' : ↥(g2RankOne K g2ir)) : ModGL .G2 K) * q *
        ((l * l' : ↥(g2RankOne K g2ir)) : ModGL .G2 K)⁻¹ * q⁻¹ ∈ g2Z K
    rw [e]
    exact mul_mem hz (hl q hq)
  inv_mem' := by
    intro l hl q hq
    have hq' : (l : ModGL .G2 K)⁻¹ * q * ((l : ModGL .G2 K)⁻¹)⁻¹ ∈ g2Q K :=
      g2RankOne_normalizes_g2Q (inv_mem l.2) hq
    have h1 := hl _ hq'
    have e : ((l⁻¹ : ↥(g2RankOne K g2ir)) : ModGL .G2 K) * q *
        ((l⁻¹ : ↥(g2RankOne K g2ir)) : ModGL .G2 K)⁻¹ * q⁻¹ =
        ((l : ModGL .G2 K) * ((l : ModGL .G2 K)⁻¹ * q * ((l : ModGL .G2 K)⁻¹)⁻¹) *
          (l : ModGL .G2 K)⁻¹ * ((l : ModGL .G2 K)⁻¹ * q * ((l : ModGL .G2 K)⁻¹)⁻¹)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]; group
    show ((l⁻¹ : ↥(g2RankOne K g2ir)) : ModGL .G2 K) * q *
        ((l⁻¹ : ↥(g2RankOne K g2ir)) : ModGL .G2 K)⁻¹ * q⁻¹ ∈ g2Z K
    rw [e]
    exact inv_mem h1

private theorem mem_g2ActsSub {l : ↥(g2RankOne K g2ir)} :
    l ∈ g2ActsSub K ↔
      ∀ q ∈ g2Q K, (l : ModGL .G2 K) * q * (l : ModGL .G2 K)⁻¹ * q⁻¹ ∈ g2Z K :=
  Iff.rfl

private instance g2ActsSub_normal : (g2ActsSub K).Normal where
  conj_mem := by
    intro n hn m q hq
    have hq' : (m : ModGL .G2 K)⁻¹ * q * ((m : ModGL .G2 K)⁻¹)⁻¹ ∈ g2Q K :=
      g2RankOne_normalizes_g2Q (inv_mem m.2) hq
    have h1 := mem_g2ActsSub.1 hn _ hq'
    have hcomm := g2RankOne_commute_g2Z m.2 h1
    have e : ((m * n * m⁻¹ : ↥(g2RankOne K g2ir)) : ModGL .G2 K) * q *
        ((m * n * m⁻¹ : ↥(g2RankOne K g2ir)) : ModGL .G2 K)⁻¹ * q⁻¹ =
        (m : ModGL .G2 K) * ((n : ModGL .G2 K) * ((m : ModGL .G2 K)⁻¹ * q *
          ((m : ModGL .G2 K)⁻¹)⁻¹) * (n : ModGL .G2 K)⁻¹ *
          ((m : ModGL .G2 K)⁻¹ * q * ((m : ModGL .G2 K)⁻¹)⁻¹)⁻¹) * (m : ModGL .G2 K)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    show ((m * n * m⁻¹ : ↥(g2RankOne K g2ir)) : ModGL .G2 K) * q *
        ((m * n * m⁻¹ : ↥(g2RankOne K g2ir)) : ModGL .G2 K)⁻¹ * q⁻¹ ∈ g2Z K
    rw [e, hcomm, mul_inv_cancel_right]
    exact h1

private theorem weylElt_not_mem_g2ActsSub :
    (⟨weylElt .G2 K g2ir 1, weylElt_mem_g2RankOne g2ir 1⟩ : ↥(g2RankOne K g2ir)) ∉
      g2ActsSub K := by
  intro h
  obtain ⟨ε, -, hconj⟩ := weylElt_mul_pinnedX_mul_inv K g2ir isRoot_g2a
  have hq : X g2a 1 ∈ g2Q K :=
    pinnedX_mem_rootSpan (S := {γ | γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c})
      (Or.inl rfl) 1
  have h1 := mem_g2ActsSub.1 h _ hq
  simp only [hconj, reflect_r_a, pinnedX_neg] at h1
  obtain ⟨w, hw⟩ := (mem_rootSubgroup (τ := .G2) (R := K)).1 h1
  have hα : Function.Injective (![g2b, g2a, g2c] : Fin 3 → Fin Tag.G2.rank → ℤ) := by
    unfold g2b g2a g2c
    decide
  have hpos : ∀ i : Fin 3,
      IsRoot .G2 (![g2b, g2a, g2c] i) ∧ 0 < height (![g2b, g2a, g2c] i) := by
    intro i
    fin_cases i
    · exact ⟨isRoot_g2b, by decide⟩
    · exact ⟨isRoot_g2a, by decide⟩
    · exact ⟨isRoot_g2c, by decide⟩
  have hinj := (positive_root_product_injectivity .G2 K ![g2b, g2a, g2c] hα hpos).2
  have e1 : (List.ofFn fun i => X (![g2b, g2a, g2c] i) (![ε * 1, -1, 0] i)).prod =
      X g2b (ε * 1) * X g2a (-1) := by
    simp [List.ofFn_succ, pinnedX_zero]
  have e2 : (List.ofFn fun i => X (![g2b, g2a, g2c] i) (![0, 0, w] i)).prod = X g2c w := by
    simp [List.ofFn_succ, pinnedX_zero]
  have key := @hinj ![ε * 1, -1, 0] ![0, 0, w] (by simp only [e1, e2]; exact hw.symm)
  have h2 := congrFun key 1
  simp at h2

theorem central_of_acts_trivially [Finite K] (hK : 4 ≤ Nat.card K) {l : ModGL .G2 K}
    (hl : l ∈ g2RankOne K g2ir) (h : ∀ q ∈ g2Q K, l * q * l⁻¹ * q⁻¹ ∈ g2Z K) :
    ∀ m ∈ g2RankOne K g2ir, m * l = l * m := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_g2RankOne (K := K) hK)
      (g2ActsSub_normal (K := K)) with htop | hcen
  · exact absurd (htop ▸ Subgroup.mem_top _) weylElt_not_mem_g2ActsSub
  · intro m hm
    have hmem : (⟨l, hl⟩ : ↥(g2RankOne K g2ir)) ∈ g2ActsSub K := mem_g2ActsSub.2 h
    have hc := Subgroup.mem_center_iff.1 (hcen hmem) ⟨m, hm⟩
    exact congrArg Subtype.val hc

end CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux
