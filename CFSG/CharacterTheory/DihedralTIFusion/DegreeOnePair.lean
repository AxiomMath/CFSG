module

public import CFSG.CharacterTheory.DihedralTIFusion.DihedralCharacters
public import CFSG.CharacterTheory.DihedralTIFusion.SelfCentralizingTI
public import CFSG.CharacterTheory.DihedralTIFusion.InductionIsometry
public import CFSG.CharacterTheory.SmallDefect.Basic

public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

open Wreathed TwoRankLowerBound.Helpers BrauerThirdMainTheorem.Helpers

theorem inner_sub_sub_of_irr {K : Type} [Group K] [Fintype K] {a b c : K → ℂ}
    (ha : a ∈ BlocksIrr K) (hb : b ∈ BlocksIrr K) (hc : c ∈ BlocksIrr K)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    BlocksInnerProduct (a - b - c) (a - b - c) = 3 ∧ BlocksInnerProduct (a - b - c) b = -1 := by
  simp only [SmallDefect.blocksInnerProduct_sub_left, SmallDefect.blocksInnerProduct_sub_right,
    SmallDefect.blocksInnerProduct_irr ha ha, SmallDefect.blocksInnerProduct_irr ha hb,
    SmallDefect.blocksInnerProduct_irr ha hc, SmallDefect.blocksInnerProduct_irr hb ha,
    SmallDefect.blocksInnerProduct_irr hb hb, SmallDefect.blocksInnerProduct_irr hb hc,
    SmallDefect.blocksInnerProduct_irr hc ha, SmallDefect.blocksInnerProduct_irr hc hb,
    SmallDefect.blocksInnerProduct_irr hc hc, hab, hac, hbc, Ne.symm hab, Ne.symm hac,
    Ne.symm hbc, ↓reduceIte]
  norm_num

theorem inner_add_one_of {K : Type} [Group K] [Fintype K] {f : K → ℂ}
    (hff : BlocksInnerProduct f f = 3) (hf1 : BlocksInnerProduct f 1 = -1) :
    BlocksInnerProduct (f + 1) (f + 1) = 2 ∧ BlocksInnerProduct (f + 1) 1 = 0 := by
  have h11 : BlocksInnerProduct (1 : K → ℂ) 1 = 1 := by
    rw [SmallDefect.blocksInnerProduct_irr (χ := (1 : K → ℂ)) (ψ := 1) (trivial_mem_irr K)
      (trivial_mem_irr K), ite_eq_left rfl]
  have h1f : BlocksInnerProduct (1 : K → ℂ) f = -1 := by
    rw [SmallDefect.blocksInnerProduct_conj_symm, hf1, map_neg, map_one]
  rw [SmallDefect.blocksInnerProduct_add_left, SmallDefect.blocksInnerProduct_add_left,
    SmallDefect.blocksInnerProduct_add_right, SmallDefect.blocksInnerProduct_add_right, hff,
    hf1, h1f, h11]
  norm_num

theorem norm_two_degree_one_difference {K : Type} [Group K] [Fintype K] {β : K → ℂ}
    (hβ : β ∈ BlocksVChar K) (hββ : BlocksInnerProduct β β = 2)
    (hβ1 : BlocksInnerProduct β 1 = 0) (hdeg : β 1 = 1) :
    ∃ χ ∈ BlocksIrr K \ {1}, ∃ ψ ∈ BlocksIrr K \ {1}, χ ≠ ψ ∧ χ 1 = ψ 1 + 1 ∧ β = χ - ψ := by
  obtain ⟨χ₁, χ₂, e₁, e₂, hne, he₁, he₂, hβeq⟩ := blocksVChar_norm_two_signed_irreducibles hβ hββ
  have hirr1 : (1 : K → ℂ) ∈ BlocksIrr K := trivial_mem_irr K
  have hpair : BlocksInnerProduct β 1 = e₁ * BlocksInnerProduct (χ₁ : K → ℂ) 1 +
      e₂ * BlocksInnerProduct (χ₂ : K → ℂ) 1 := by
    rw [hβeq, SmallDefect.blocksInnerProduct_add_left, SmallDefect.blocksInnerProduct_smul_left,
      SmallDefect.blocksInnerProduct_smul_left]
  rw [SmallDefect.blocksInnerProduct_irr χ₁.2 hirr1, SmallDefect.blocksInnerProduct_irr χ₂.2 hirr1,
    hβ1] at hpair
  have hne' : (χ₁ : K → ℂ) ≠ χ₂ := fun h => hne (Subtype.ext h)
  have h₁ : (χ₁ : K → ℂ) ≠ 1 := by
    intro h
    rw [ite_eq_left h, ite_eq_right (fun h' => hne' (h.trans h'.symm))] at hpair
    rcases he₁ with rfl | rfl <;> norm_num at hpair
  have h₂ : (χ₂ : K → ℂ) ≠ 1 := by
    intro h
    rw [ite_eq_left h, ite_eq_right (fun h' => hne' (h'.trans h.symm))] at hpair
    rcases he₂ with rfl | rfl <;> norm_num at hpair
  obtain ⟨d₁, hd₁, hχ₁1, -⟩ := OddOrderBasics.irreducible_character_degree_divides_order _ χ₁.2
  obtain ⟨d₂, hd₂, hχ₂1, -⟩ := OddOrderBasics.irreducible_character_degree_divides_order _ χ₂.2
  have h1 := congrFun hβeq 1
  rw [hdeg, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hχ₁1,
    hχ₂1] at h1
  have hZ : (1 : ℤ) = e₁ * d₁ + e₂ * d₂ := by exact_mod_cast h1
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · omega
  · refine ⟨χ₁, ⟨χ₁.2, h₁⟩, χ₂, ⟨χ₂.2, h₂⟩, hne', ?_, ?_⟩
    · rw [hχ₁1, hχ₂1]
      have h : (d₁ : ℤ) = d₂ + 1 := by omega
      exact_mod_cast h
    · rw [hβeq]
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      push_cast
      ring
  · refine ⟨χ₂, ⟨χ₂.2, h₂⟩, χ₁, ⟨χ₁.2, h₁⟩, Ne.symm hne', ?_, ?_⟩
    · rw [hχ₁1, hχ₂1]
      have h : (d₂ : ℤ) = d₁ + 1 := by omega
      exact_mod_cast h
    · rw [hβeq]
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      push_cast
      ring
  · omega

theorem dihedral_TI_induction_degree_one_character_pair {G : Type} [Group G] [Fintype G]
    {W : Subgroup G} (hWcyclic : IsCyclic W) (hWodd : Odd (Nat.card W))
    (hWcard : 3 ≤ Nat.card W)
    (hcentralizer : ∀ w ∈ W, w ≠ 1 → Subgroup.centralizer ({w} : Set G) = W) {u : G}
    (hu : orderOf u = 2) (huW : u ∉ W) (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hnormalizer : Subgroup.normalizer (W : Set G) = W ⊔ Subgroup.zpowers u) :
    (∃ χ ∈ BlocksIrr G \ {1}, ∃ ψ ∈ BlocksIrr G \ {1}, χ ≠ ψ ∧ χ 1 = ψ 1 + 1 ∧
      (∀ g ∉ ⋃ a : G, (fun x => a⁻¹ * x * a) '' ((W : Set G) \ {1}), (χ - ψ - 1) g = 0) ∧
      ∃ w ∈ W, (χ - ψ - 1) w ≠ 0) ∧
    ∀ μ ∈ BlocksIrr W \ {1}, ∃ χ ∈ BlocksIrr G \ {1}, ∃ ψ ∈ BlocksIrr G \ {1}, χ ≠ ψ ∧
      χ 1 = ψ 1 + 1 ∧
      (∀ g ∉ ⋃ a : G, (fun x => a⁻¹ * x * a) '' ((W : Set G) \ {1}), (χ - ψ - 1) g = 0) ∧
      (∃ w ∈ W, (χ - ψ - 1) w ≠ 0) ∧
      χ - ψ - 1 = inducedFunction (Subgroup.normalizer (W : Set G))
        (inducedFunction (W.subgroupOf (Subgroup.normalizer (W : Set G)))
            (fun x => μ ⟨x.1.1, x.2⟩) - 1 -
          fun x : Subgroup.normalizer (W : Set G) => if (x : G) ∈ W then 1 else -1) ∧
      (∀ w : W, w ≠ 1 → (χ - ψ - 1) w = μ w + μ w⁻¹ - 2) ∧
      (χ - ψ - 1) 1 = 0 ∧ BlocksInnerProduct (χ - ψ - 1) (χ - ψ - 1) = 3 ∧
      BlocksInnerProduct (χ - ψ - 1) 1 = -1 := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
  have hWne : W ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot W).mp (by omega)
  have hTI := (self_centralizing_subgroup_TI hWne hcentralizer).2.2
  refine (fun hmain => ⟨?first, hmain⟩) ?second
  case first =>
    have : IsMulCommutative W := IsCyclic.isMulCommutative
    have hexists : ∃ μ, μ ∈ BlocksIrr W \ {1} := by
      by_contra hnone
      have hsub : BlocksIrr W ⊆ {1} := fun μ hμ => by
        by_contra h
        exact hnone ⟨μ, hμ, h⟩
      have hle := Nat.card_mono (Set.finite_singleton _) hsub
      have h1 : Nat.card ↥({1} : Set (W → ℂ)) = 1 := Nat.card_unique
      rw [natCard_blocksIrr_of_isMulCommutative W, h1] at hle
      omega
    obtain ⟨μ, hμ⟩ := hexists
    obtain ⟨χ, hχ, ψ, hψ, hχψ, hdeg, hsupp, hnz, -⟩ := hmain μ hμ
    exact ⟨χ, hχ, ψ, hψ, hχψ, hdeg, hsupp, hnz⟩
  intro μ hμ
  obtain ⟨hθirr, hθ1, hθvan, hθval⟩ :=
    dihedral_induced_character hWcyclic hWodd hu2 huW hinvert hnormalizer hμ
  have hε := dihedral_sign_character hu2 huW hinvert hnormalizer
  set D := Subgroup.normalizer (W : Set G) with hD
  set θ := inducedFunction (W.subgroupOf D) (fun x => μ ⟨x.1.1, x.2⟩) with hθ
  set ε : D → ℂ := fun x => if (x : G) ∈ W then 1 else -1 with hεdef
  have hε1 : ε 1 = 1 := by simp [hεdef, W.one_mem]
  have hθε : θ ≠ ε := fun h => by
    have h1 := congrFun h 1
    rw [hθ1, hε1] at h1
    norm_num at h1
  obtain ⟨hφφ, hφ1⟩ := inner_sub_sub_of_irr (b := (1 : D → ℂ)) hθirr.1 (trivial_mem_irr D) hε.1
    hθirr.2 hθε (fun h => hε.2 h.symm)
  set φ : D → ℂ := θ - 1 - ε with hφdef
  have hφvirt : φ ∈ BlocksVChar D :=
    sub_mem (sub_mem (AddSubgroup.subset_closure hθirr.1)
      (AddSubgroup.subset_closure (trivial_mem_irr D))) (AddSubgroup.subset_closure hε.1)
  have hφsupp : ∀ x : D, (x : G) ∉ (W : Set G) \ {1} → φ x = 0 := by
    intro x hx
    by_cases hxW : (x : G) ∈ W
    · have hx1 : x = 1 := Subtype.ext (by_contra fun h => hx ⟨hxW, h⟩)
      subst hx1
      rw [hφdef, Pi.sub_apply, Pi.sub_apply, hθ1, hε1, Pi.one_apply]
      norm_num
    · rw [hφdef, Pi.sub_apply, Pi.sub_apply, hθvan x hxW, Pi.one_apply]
      simp [hεdef, hxW]
  obtain ⟨hαvirt, hαsupp, hαα, hα1⟩ := supported_virtual_induction_data hTI hφvirt hφsupp
  set α := inducedFunction D φ with hαdef
  have hαW : ∀ x : D, (x : G) ∈ (W : Set G) \ {1} → α x = φ x :=
    inducedFunction_eq_of_mem_ti hTI (blocksVChar_isClassFunction hφvirt) hφsupp
  have hαone : α 1 = 0 := by
    rw [hαdef, (OddOrderBasics.induced_class_function_identities D).2.2.1,
      hφsupp 1 (fun h => h.2 rfl), mul_zero]
  have hαα3 : BlocksInnerProduct α α = 3 := hαα.trans hφφ
  have hα1' : BlocksInnerProduct α 1 = -1 := hα1.trans hφ1
  obtain ⟨hββ, hβ1⟩ := inner_add_one_of hαα3 hα1'
  have hβdeg : (α + 1) 1 = 1 := by rw [Pi.add_apply, hαone, Pi.one_apply, zero_add]
  obtain ⟨χ, hχ, ψ, hψ, hχψ, hdeg, hβeq⟩ := norm_two_degree_one_difference
    (add_mem hαvirt (blocksVChar_one G)) hββ hβ1 hβdeg
  have hαeq : χ - ψ - 1 = α := by rw [← hβeq, add_sub_cancel_right]
  refine ⟨χ, hχ, ψ, hψ, hχψ, hdeg, fun g hg => hαeq ▸ hαsupp g hg, ?_, hαeq, ?_,
    hαeq ▸ hαone, hαeq ▸ hαα3, hαeq ▸ hα1'⟩
  · have hφne : φ ≠ 0 := fun h => by
      rw [h, SmallDefect.blocksInnerProduct_zero_left] at hφφ
      norm_num at hφφ
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hφne
    have hxW : (x : G) ∈ (W : Set G) \ {1} := by
      by_contra h
      exact hx (hφsupp x h)
    refine ⟨x, hxW.1, ?_⟩
    rw [hαeq, hαW x hxW]
    exact hx
  · intro w hw1
    have hmem : ((⟨(w : G), Subgroup.le_normalizer w.2⟩ : D) : G) ∈ (W : Set G) \ {1} :=
      ⟨w.2, fun h => hw1 (Subtype.ext h)⟩
    rw [hαeq]
    change α ((⟨(w : G), Subgroup.le_normalizer w.2⟩ : D) : G) = _
    rw [hαW _ hmem, hφdef, Pi.sub_apply, Pi.sub_apply, hθval (w : G) w.2, Pi.one_apply]
    have hεw : ε ⟨(w : G), Subgroup.le_normalizer w.2⟩ = 1 := by simp [hεdef, w.2]
    rw [hεw]
    change μ w + μ w⁻¹ - 1 - 1 = μ w + μ w⁻¹ - 2
    ring

end CFSG.DihedralTIFusion
