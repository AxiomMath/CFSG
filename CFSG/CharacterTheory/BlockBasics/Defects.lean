module

public import CFSG.CharacterTheory.BlockBasics.Bridge
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockDefects
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalBlockDefects
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockResidues
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBlockDefect

public section

open scoped Classical

namespace CFSG.BlockBasics

open CFSG CFSG.BrauerThirdMainTheorem.Helpers

theorem prime_mem_of_charP (p : ℕ) (m : Ideal BlocksAlgInt) [CharP (BlocksAlgInt ⧸ m) p] :
    (p : BlocksAlgInt) ∈ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem mem_localMaxIdeal_iff_of_sub_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {a b : ℂ} (h : a - b ∈ BlocksLocalMaxIdeal m) :
    a ∈ BlocksLocalMaxIdeal m ↔ b ∈ BlocksLocalMaxIdeal m := by
  constructor
  · intro ha
    have hb := localMaxIdeal_sub m hm ha h
    rwa [sub_sub_cancel] at hb
  · intro hb
    have ha := localMaxIdeal_add m hm h hb
    rwa [sub_add_cancel] at ha

theorem blockDefect_iff_of_mem_blockOf (p : ℕ) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {G : Type} [Group G] [Finite G] {χ ψ : G → ℂ} (hχ : χ ∈ BlocksIrr G)
    (hψ : ψ ∈ BlocksBlockOf m G χ) (D : Subgroup G) :
    blockDefect p m χ D ↔ blockDefect p m ψ D := by
  have hres : ∀ C : ConjClasses G,
      BlocksCentralChar χ (classCoefficients C) ∉ BlocksLocalMaxIdeal m ↔
        BlocksCentralChar ψ (classCoefficients C) ∉ BlocksLocalMaxIdeal m := fun C =>
    not_congr (mem_localMaxIdeal_iff_of_sub_mem m hm
      (sameBlock_centralChar_congr m hm G hχ hψ (classCoefficients_central m hm C))).symm
  constructor
  · rintro ⟨⟨C, hC, hCres⟩, huniv⟩
    exact ⟨⟨C, hC, (hres C).mp hCres⟩, fun E hE => huniv E ((hres E).mpr hE)⟩
  · rintro ⟨⟨C, hC, hCres⟩, huniv⟩
    exact ⟨⟨C, hC, (hres C).mpr hCres⟩, fun E hE => huniv E ((hres E).mp hE)⟩

theorem forall_blockDefect_iff (p : ℕ) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {G : Type} [Group G] [Finite G] {B : Set (G → ℂ)} (hB : BlocksIsBlock m G B)
    {χ : G → ℂ} (hχ : χ ∈ B) (D : Subgroup G) :
    (∀ ψ ∈ B, blockDefect p m ψ D) ↔ blockDefect p m χ D := by
  have hBχ := block_eq_blockOf_member m hB hχ
  have hχirr := block_subset_irr m hB hχ
  refine ⟨fun h => h χ hχ, fun h ψ hψ => ?_⟩
  rw [hBχ] at hψ
  exact (blockDefect_iff_of_mem_blockOf p m hm hχirr hψ D).mp h

theorem card_class_product_pairs {G : Type*} [Group G] [Finite G] (C D : ConjClasses G) (z : G) :
    Nat.card {xy : G × G // ConjClasses.mk xy.1 = C ∧ ConjClasses.mk xy.2 = D ∧
      xy.1 * xy.2 = z} = classProductCount C D z := by
  refine Nat.card_congr
    { toFun := fun xy => ⟨xy.1.1, xy.2.1, by
        rw [inv_mul_eq_iff_eq_mul.mpr xy.2.2.2.symm]
        exact xy.2.2.1⟩
      invFun := fun x => ⟨(x.1, x.1⁻¹ * z), x.2.1, x.2.2, mul_inv_cancel_left _ _⟩
      left_inv := fun xy => ?_
      right_inv := fun x => rfl }
  apply Subtype.ext
  ext
  · rfl
  · change xy.1.1⁻¹ * z = xy.1.2
    exact inv_mul_eq_iff_eq_mul.mpr xy.2.2.2.symm

theorem class_product_defect_containment (p : ℕ) (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (C D E : ConjClasses G) (z : G) (hz : ConjClasses.mk z = E)
    (ha : ¬ p ∣ Nat.card {xy : G × G // ConjClasses.mk xy.1 = C ∧ ConjClasses.mk xy.2 = D ∧
      xy.1 * xy.2 = z}) :
    ∀ Q U V : Subgroup G, classDefect p E Q → classDefect p C U → classDefect p D V →
      subgroupSubconjugate Q U ∧ subgroupSubconjugate Q V := by
  intro Q U V hQ hU hV
  rw [card_class_product_pairs] at ha
  subst hz
  exact classProduct_defect_containment p hp C D z ha hQ hU hV

theorem block_defect_existence (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt)
    (hm : m.IsMaximal) [CharP (BlocksAlgInt ⧸ m) p] (G : Type) [Group G] [Finite G]
    (B : Set (G → ℂ)) (hB : BlocksIsBlock m G B) :
    (∃ D : Subgroup G, ∀ χ ∈ B, blockDefect p m χ D) ∧
      ∀ D D' : Subgroup G, (∀ χ ∈ B, blockDefect p m χ D) → (∀ χ ∈ B, blockDefect p m χ D') →
        ∃ g : G, D.map (MulAut.conj g).toMonoidHom = D' := by
  obtain ⟨χ, hχ⟩ := block_nonempty m hB
  have hχirr := block_subset_irr m hB hχ
  have hpm := prime_mem_of_charP p m
  refine ⟨?_, fun D D' hD hD' => ?_⟩
  · obtain ⟨D, hD⟩ := blockDefect_exists p hp m hm hpm G hχirr
    exact ⟨D, (forall_blockDefect_iff p m hm hB hχ D).mpr hD⟩
  · have h1 := hD χ hχ
    have h2 := hD' χ hχ
    obtain ⟨C, hC, hCres⟩ := h1.1
    obtain ⟨C', hC', hC'res⟩ := h2.1
    have hDD' : subgroupSubconjugate D D' := h1.2 C' hC'res D' hC'
    have hD'D : subgroupSubconjugate D' D := h2.2 C hCres D hC
    obtain ⟨g, hg⟩ := hDD'
    refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
    have hcard : Nat.card (D.map (MulAut.conj g).toMonoidHom) = Nat.card D :=
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hcard]
    exact subgroupSubconjugate_card_le hD'D

theorem principal_block_defect (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt)
    [hm : m.IsMaximal] [CharP (BlocksAlgInt ⧸ m) p] (G : Type) [Group G] [Finite G] :
    (∀ D : Subgroup G, (∀ χ ∈ BlocksPrincipalBlock m G, blockDefect p m χ D) ↔
      ∃ P : Sylow p G, (P : Subgroup G) = D) ∧
    ∀ (C : ConjClasses G) (Q : Subgroup G), classDefect p C Q →
      (BlocksCentralChar (fun _ => (1 : ℂ)) (classCoefficients C) ∉ BlocksLocalMaxIdeal m ↔
        ∃ P : Sylow p G, (P : Subgroup G) = Q) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨basis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨l, hl⟩ := exists_label_of_mem_irr basis (trivial_mem_irr G)
  have hl1 : (basis.representation l).character = 1 := hl
  refine ⟨fun D => ?_, fun C Q hQ => ?_⟩
  · rw [forall_blockDefect_iff p m hm (principal_isBlock m G) (trivial_mem_principal m G) D, ← hl,
      ← coefficientBlockDefect_iff basis m p l D]
    exact CFSG.TwoRankLowerBound.Helpers.principal_coefficientBlockDefect_iff_sylow basis m p l
      hl1 D
  · have h := CFSG.TwoRankLowerBound.Helpers.principal_class_residue_ne_zero_iff_sylow basis m p l
      hl1 ((classDefect_iff p C Q).mpr hQ)
    rw [Ne, centralCharacterResidueHom_eq_zero_iff, hl] at h
    have hcoeff :
        (fun g => (CFSG.TwoRankLowerBound.Helpers.centralConjugacyClassSum
          (CFSG.TwoRankLowerBound.Helpers.localizedComplexIntegerRing m) C).val.coeff g) =
          classCoefficients C := by
      funext g
      exact centralConjugacyClassSum_coeff _ C g
    rw [hcoeff] at h
    exact h

theorem normal_p_subgroup_class_vanishing (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt)
    (hm : m.IsMaximal) [CharP (BlocksAlgInt ⧸ m) p] (H : Type) [Group H] [Finite H]
    (P : Subgroup H) [P.Normal] (hP : IsPGroup p P) (B : Set (H → ℂ))
    (hB : BlocksIsBlock m H B) :
    (∀ C : ConjClasses H, (∀ x : H, ConjClasses.mk x = C → x ∉ Subgroup.centralizer (P : Set H)) →
      ∀ χ ∈ B, BlocksCentralChar χ (classCoefficients C) ∈ BlocksLocalMaxIdeal m) ∧
      ∀ D : Subgroup H, (∀ χ ∈ B, blockDefect p m χ D) → P ≤ D := by
  have hpm := prime_mem_of_charP p m
  refine ⟨fun C hC χ hχ => ?_, fun D hD => ?_⟩
  · apply normalPSubgroup_centralChar_vanishes p hp m hm hpm H P hP (block_subset_irr m hB hχ)
      (classCoefficients_central m hm C)
    intro x hx
    simp only [classCoefficients]
    rw [ite_eq_right]
    intro hxC
    exact hC x hxC hx
  · obtain ⟨χ, hχ⟩ := block_nonempty m hB
    exact normalPSubgroup_le_blockDefect p hp m hm hpm H P hP (block_subset_irr m hB hχ) (hD χ hχ)

section Basis

open CFSG.TwoRankLowerBound.Helpers

variable (p : ℕ) [Fact p.Prime] (m : Ideal BlocksAlgInt) [m.IsMaximal]
  [CharP (BlocksAlgInt ⧸ m) p] {G : Type} [Group G] [Fintype G]
  (basis : FiniteIrreducibleCharacterBasis G)

theorem coefficientBlockDefect_existence (l : basis.index) :
    (∃ D : Subgroup G, coefficientBlockDefect basis m p l D) ∧
      ∀ D D' : Subgroup G, coefficientBlockDefect basis m p l D →
        coefficientBlockDefect basis m p l D' →
          ∃ g : G, D.map (MulAut.conj g).toMonoidHom = D' := by
  have hB : BlocksIsBlock m G (BlocksBlockOf m G (basis.representation l).character) :=
    ⟨_, basis_character_mem_irr basis l, rfl⟩
  have hmem := mem_blockOf_self m (basis_character_mem_irr basis l)
  obtain ⟨⟨D, hD⟩, huniq⟩ := block_defect_existence p Fact.out m inferInstance G _ hB
  refine ⟨⟨D, (coefficientBlockDefect_iff basis m p l D).mpr
    ((forall_blockDefect_iff p m inferInstance hB hmem D).mp hD)⟩, fun D D' h h' => ?_⟩
  exact huniq D D'
    ((forall_blockDefect_iff p m inferInstance hB hmem D).mpr
      ((coefficientBlockDefect_iff basis m p l D).mp h))
    ((forall_blockDefect_iff p m inferInstance hB hmem D').mpr
      ((coefficientBlockDefect_iff basis m p l D').mp h'))

theorem normal_p_le_coefficientBlockDefect_of_shared (P : Subgroup G) [P.Normal]
    (hP : IsPGroup p P) (l : basis.index) {D : Subgroup G}
    (hD : coefficientBlockDefect basis m p l D) : P ≤ D := by
  have hB : BlocksIsBlock m G (BlocksBlockOf m G (basis.representation l).character) :=
    ⟨_, basis_character_mem_irr basis l, rfl⟩
  have hmem := mem_blockOf_self m (basis_character_mem_irr basis l)
  exact (normal_p_subgroup_class_vanishing p Fact.out m inferInstance G P hP _ hB).2 D
    ((forall_blockDefect_iff p m inferInstance hB hmem D).mpr
      ((coefficientBlockDefect_iff basis m p l D).mp hD))

theorem principal_coefficientBlockDefect_iff_sylow_of_shared (l : basis.index)
    (hl : (basis.representation l).character = 1) (D : Subgroup G) :
    coefficientBlockDefect basis m p l D ↔ ∃ P : Sylow p G, (P : Subgroup G) = D := by
  rw [coefficientBlockDefect_iff, hl, ← (principal_block_defect p Fact.out m G).1 D]
  exact (forall_blockDefect_iff p m inferInstance (principal_isBlock m G)
    (trivial_mem_principal m G) D).symm

end Basis

end CFSG.BlockBasics
