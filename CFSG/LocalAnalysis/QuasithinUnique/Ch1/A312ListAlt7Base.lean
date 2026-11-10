
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoInputs

@[expose] public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.Seven

open scoped commutatorElement
open Equiv CFSG.QuasithinUnique.Unc25K1.Six CFSG.Assembly.LowTwoRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

def T7 : Subgroup ↥A7s := D7.subgroupOf A7s

theorem card_A7s : Nat.card ↥A7s = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_map_subtype (M : Subgroup ↥A7s) : Nat.card (M.map A7s.subtype) = Nat.card M :=
  Subgroup.card_map_of_injective A7s.subtype_injective

def s5 : Finset (Fin 7) := {0, 1, 2, 3, 6}

def s6 : Finset (Fin 7) := {0, 1, 2, 3, 4, 5}

theorem card_s5 : s5.card = 5 := by decide

theorem card_s6 : s6.card = 6 := by decide

def rng5 : Subgroup ↥A7s := (alternatingGroup.ofSubtype s5).range

def rng6 : Subgroup ↥A7s := (alternatingGroup.ofSubtype s6).range

theorem mem_rng5 (k : ↥A7s) : k ∈ rng5 ↔ k.1 4 = 4 ∧ k.1 5 = 5 := by
  rw [rng5, alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hne
      have := h (Equiv.Perm.mem_support.mpr hne)
      revert this
      decide
    · by_contra hne
      have := h (Equiv.Perm.mem_support.mpr hne)
      revert this
      decide
  · rintro ⟨h4, h5⟩ x hx
    rw [Equiv.Perm.mem_support] at hx
    have hx4 : x ≠ 4 := fun h => hx (by rw [h]; exact h4)
    have hx5 : x ≠ 5 := fun h => hx (by rw [h]; exact h5)
    have key : ∀ y : Fin 7, y ≠ 4 → y ≠ 5 → y ∈ s5 := by decide
    exact key x hx4 hx5

theorem mem_rng6 (k : ↥A7s) : k ∈ rng6 ↔ k.1 6 = 6 := by
  rw [rng6, alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro h
    by_contra hne
    have := h (Equiv.Perm.mem_support.mpr hne)
    revert this
    decide
  · intro h x hx
    rw [Equiv.Perm.mem_support] at hx
    have hx6 : x ≠ 6 := fun h' => hx (by rw [h']; exact h)
    have key : ∀ y : Fin 7, y ≠ 6 → y ∈ s6 := by decide
    exact key x hx6

theorem mem_of_map_eq {M : Subgroup ↥A7s} {i : ℕ} (h : M.map A7s.subtype = Z i) (k : ↥A7s) :
    k ∈ M ↔ k.1 ∈ Z i := by
  rw [← h]
  exact (Subgroup.mem_map_iff_mem A7s.subtype_injective).symm

theorem fix_or_swap {σ : P7} (h4 : σ 4 = 4 ∨ σ 4 = 5) (h5 : σ 5 = 4 ∨ σ 5 = 5) :
    (σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4) := by
  have hne : σ 4 ≠ σ 5 := fun h => absurd (σ.injective h) (by decide)
  rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5
  · exact absurd (h4.trans h5.symm) hne
  · exact Or.inl ⟨h4, h5⟩
  · exact Or.inr ⟨h4, h5⟩
  · exact absurd (h4.trans h5.symm) hne

theorem inv_fix {σ : P7} (h4 : σ 4 = 4) (h5 : σ 5 = 5) : σ⁻¹ 4 = 4 ∧ σ⁻¹ 5 = 5 :=
  ⟨by rw [Equiv.Perm.inv_eq_iff_eq, h4], by rw [Equiv.Perm.inv_eq_iff_eq, h5]⟩

theorem inv_swap {σ : P7} (h4 : σ 4 = 5) (h5 : σ 5 = 4) : σ⁻¹ 4 = 5 ∧ σ⁻¹ 5 = 4 :=
  ⟨by rw [Equiv.Perm.inv_eq_iff_eq, h5], by rw [Equiv.Perm.inv_eq_iff_eq, h4]⟩

noncomputable def rng5Equiv : ↥rng5 ≃* alternatingGroup (Fin 5) :=
  (altRangeEquiv s5).trans (altCongr (finCongr card_s5))

noncomputable def rng6Equiv : ↥rng6 ≃* alternatingGroup (Fin 6) :=
  (altRangeEquiv s6).trans (altCongr (finCongr card_s6))

theorem commutator_eq_top_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : commutator S = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hS
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator S :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact h

theorem perfect_of_equiv_simple {X : Type} [Group X] {H : Subgroup X} {S : Type} [Group S]
    [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (e : ↥H ≃* S) : ⁅H, H⁆ = H := by
  have : Group.IsPerfect S := Group.isPerfect_def.mpr (commutator_eq_top_of_simple hS)
  have : Group.IsPerfect ↥H :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.mp this

theorem nonabelian_of_card_not_prime {S : Type} [Group S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative S := ⟨⟨hcon⟩⟩
  exact h (Group.is_simple_iff_prime_card.mp inferInstance)

theorem alt5_simple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt6_simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt5_nonabelian : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  have := alt5_simple
  refine nonabelian_of_card_not_prime ?_
  have : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [this]
  norm_num

theorem alt6_nonabelian : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  have := alt6_simple
  refine nonabelian_of_card_not_prime ?_
  have : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [this]
  norm_num

theorem isPSL_three_two {G : Type} [Group G] (e : G ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    IsPSL 3 2 1 G :=
  ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2, inferInstance, inferInstance,
    by rw [Nat.card_zmod]; norm_num, ⟨e.trans slThree_equiv_statedProj⟩⟩

theorem lFamily_equiv_of_perfectCore_equiv {X : Type} [Group X] [Finite X] {T B : Subgroup X}
    (hB : B ∈ lFamily T) {S : Type} [Group S] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (e : ↥(perfectCore (B ⊔ T)) ≃* S) : Nonempty (↥B ≃* S) := by
  have hBeq : B = perfectCore (B ⊔ T) :=
    lFamily_eq_perfectCore hB hS e.toMonoidHom e.surjective (by
      have : (e.toMonoidHom).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
      rw [this]
      infer_instance)
  exact ⟨(MulEquiv.subgroupCongr hBeq).trans e⟩

theorem perfectCore_le_commutator {X : Type} [Group X] [Finite X] (M : Subgroup X) :
    perfectCore M ≤ ⁅M, M⁆ :=
  calc perfectCore M = ⁅perfectCore M, perfectCore M⁆ := (perfectCore_perfect M).symm
    _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono (perfectCore_le M) (perfectCore_le M)

theorem case_L3 {B : Subgroup ↥A7s} (hB : B ∈ lFamily T7)
    (eM : ↥(B ⊔ T7) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    A312Case B (⊤ : Subgroup ↥A7s) := by
  have := slThree_isSimple
  have hperfM : ⁅B ⊔ T7, B ⊔ T7⁆ = B ⊔ T7 := perfect_of_equiv_simple slThree_nonabelian eM
  have hpc : perfectCore (B ⊔ T7) = B ⊔ T7 := perfectCore_eq_self_of_perfect hperfM
  obtain ⟨eB⟩ := lFamily_equiv_of_perfectCore_equiv hB slThree_nonabelian
    ((MulEquiv.subgroupCongr hpc).trans eM)
  have hL : IsAlt 7 ↥(⊤ : Subgroup ↥A7s) := ⟨Subgroup.topEquiv⟩
  iterate 4 right
  left
  exact And.intro (Or.inr (isPSL_three_two eB)) (Or.inl hL)

theorem case_A6 {B : Subgroup ↥A7s} (hB : B ∈ lFamily T7)
    (eM : ↥(B ⊔ T7) ≃* alternatingGroup (Fin 6)) : A312Case B (⊤ : Subgroup ↥A7s) := by
  have := alt6_simple
  have hperfM : ⁅B ⊔ T7, B ⊔ T7⁆ = B ⊔ T7 := perfect_of_equiv_simple alt6_nonabelian eM
  have hpc : perfectCore (B ⊔ T7) = B ⊔ T7 := perfectCore_eq_self_of_perfect hperfM
  obtain ⟨eB⟩ := lFamily_equiv_of_perfectCore_equiv hB alt6_nonabelian
    ((MulEquiv.subgroupCongr hpc).trans eM)
  have hL : IsAlt 7 ↥(⊤ : Subgroup ↥A7s) := ⟨Subgroup.topEquiv⟩
  iterate 5 right
  left
  exact Or.inl (And.intro ⟨eB⟩ hL)

end CFSG.QuasithinUnique.Vol2Native.A312L.Seven

namespace CFSG.QuasithinUnique.Vol2Native.A312L

end CFSG.QuasithinUnique.Vol2Native.A312L
