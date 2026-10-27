
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Lattice
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoInputs
public import Certificates.Certificate4083
public import Certificates.Certificate4083Base

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.Seven

open scoped commutatorElement
open Equiv CFSG.QuasithinUnique.Unc25K1.Six CFSG.Assembly.LowTwoRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem z10_iff : ∀ x : P7, Perm.sign x = 1 →
    ((elts (latGens.getD 10 [])).contains (R7.enc x) = true ↔ x 6 = 6) :=
  Certificates.certificate4083.1

theorem z7_iff : ∀ x : P7, Perm.sign x = 1 →
    ((elts (latGens.getD 7 [])).contains (R7.enc x) = true ↔
      (x 4 = 4 ∨ x 4 = 5) ∧ (x 5 = 4 ∨ x 5 = 5)) :=
  Certificates.certificate4083.2.1

theorem mem_Z10 {x : P7} (hx : Perm.sign x = 1) : x ∈ Z 10 ↔ x 6 = 6 := by
  have hG : latGens.getD 10 [] ∈ latGens := by simp [latGens]
  rw [Z, mem_closure_lat hG, ← Std.HashSet.contains_iff_mem]
  exact z10_iff x hx

theorem mem_Z7 {x : P7} (hx : Perm.sign x = 1) :
    x ∈ Z 7 ↔ (x 4 = 4 ∨ x 4 = 5) ∧ (x 5 = 4 ∨ x 5 = 5) := by
  have hG : latGens.getD 7 [] ∈ latGens := by simp [latGens]
  rw [Z, mem_closure_lat hG, ← Std.HashSet.contains_iff_mem]
  exact z7_iff x hx

theorem D7_le_A7s_this : ∀ g ∈ dGens, Perm.sign g = 1 :=
  Certificates.certificate4083.2.2

theorem D7_le_A7s : D7 ≤ A7s := by
  rw [D7, Subgroup.closure_le]
  intro g hg
  have : ∀ g ∈ dGens, Perm.sign g = 1 := D7_le_A7s_this
  exact Equiv.Perm.mem_alternatingGroup.mpr (this g hg)

theorem card_D7 : Nat.card D7 = 8 := by
  have hG : dGens ∈ latGens := by simp [latGens]
  have := card_Z (i := 0) (by norm_num)
  simpa [Z, D7, latGens] using this

theorem isSylowTwoOf_T7 : CFSG.QuasithinUnique.IsSylowTwoOf T7 ⊤ :=
  isSylowTwoOf_top_of_card (a := 3) (m := 315)
    (by rw [T7, Nat.card_congr (Subgroup.subgroupOfEquivOfLe D7_le_A7s).toEquiv, card_D7]
        norm_num)
    (by rw [card_A7s]; norm_num) (by decide)

theorem overgroup_Z {M : Subgroup ↥A7s} (hTM : T7 ≤ M) :
    ∃ i, i < 12 ∧ M.map A7s.subtype = Z i := by
  refine overgroups_A7 ?_ ?_
  · intro x hx
    have hxA : x ∈ A7s := D7_le_A7s hx
    exact ⟨⟨x, hxA⟩, hTM (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · rintro y ⟨k, -, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mp k.2

theorem eq_rng6 {M : Subgroup ↥A7s} (h : M.map A7s.subtype = Z 10) : M = rng6 := by
  ext k
  rw [mem_of_map_eq h, mem_Z10 (Equiv.Perm.mem_alternatingGroup.mp k.2), mem_rng6]

theorem commutator_le_rng5 {M : Subgroup ↥A7s} (h : M.map A7s.subtype = Z 7) :
    ⁅M, M⁆ ≤ rng5 := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hx' := (mem_Z7 (Equiv.Perm.mem_alternatingGroup.mp x.2)).mp ((mem_of_map_eq h x).mp hx)
  have hy' := (mem_Z7 (Equiv.Perm.mem_alternatingGroup.mp y.2)).mp ((mem_of_map_eq h y).mp hy)
  have hxs := fix_or_swap hx'.1 hx'.2
  have hys := fix_or_swap hy'.1 hy'.2
  rw [mem_rng5, commutatorElement_def]
  show (x.1 * y.1 * x.1⁻¹ * y.1⁻¹) 4 = 4 ∧ (x.1 * y.1 * x.1⁻¹ * y.1⁻¹) 5 = 5
  rcases hxs with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hys with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · obtain ⟨c1, c2⟩ := inv_fix a1 a2
    obtain ⟨d1, d2⟩ := inv_fix b1 b2
    simp only [Equiv.Perm.mul_apply, a1, a2, b1, b2, c1, c2, d1, d2, and_self]
  · obtain ⟨c1, c2⟩ := inv_fix a1 a2
    obtain ⟨d1, d2⟩ := inv_swap b1 b2
    simp only [Equiv.Perm.mul_apply, a1, a2, b1, b2, c1, c2, d1, d2, and_self]
  · obtain ⟨c1, c2⟩ := inv_swap a1 a2
    obtain ⟨d1, d2⟩ := inv_fix b1 b2
    simp only [Equiv.Perm.mul_apply, a1, a2, b1, b2, c1, c2, d1, d2, and_self]
  · obtain ⟨c1, c2⟩ := inv_swap a1 a2
    obtain ⟨d1, d2⟩ := inv_swap b1 b2
    simp only [Equiv.Perm.mul_apply, a1, a2, b1, b2, c1, c2, d1, d2, and_self]

theorem alt7_core (hq : CFSG.IsQuasisimple ↥A7s) {B : Subgroup ↥A7s} (hB : B ∈ lFamily T7)
    (hBtop : B ≠ ⊤) : A312Case B (⊤ : Subgroup ↥A7s) := by
  have hB' : B ∈ cComp (B ⊔ T7) := hB
  have hMne : B ⊔ T7 ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hMns : ¬ Group.IsSolvable ↥(B ⊔ T7) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T7))
        (Subgroup.inclusion_injective _))
  obtain ⟨i, hi, hMi⟩ := overgroup_Z (le_sup_right : T7 ≤ B ⊔ T7)
  have hcardM : Nat.card ↥(B ⊔ T7) =
      [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD i 0 := by
    rw [← card_map_subtype, hMi]
    exact card_Z hi
  interval_cases i
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 0) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 2) (by rw [hcardM]; decide)) hMns
  ·
    have := alt5_simple
    have hle : rng5 ≤ B ⊔ T7 := by
      intro k hk
      obtain ⟨h4, h5⟩ := (mem_rng5 k).mp hk
      exact (mem_of_map_eq hMi k).mpr
        ((mem_Z7 (Equiv.Perm.mem_alternatingGroup.mp k.2)).mpr ⟨Or.inl h4, Or.inr h5⟩)
    have hperf5 : ⁅rng5, rng5⁆ = rng5 := perfect_of_equiv_simple alt5_nonabelian rng5Equiv
    have hpc : perfectCore (B ⊔ T7) = rng5 :=
      le_antisymm ((perfectCore_le_commutator (B ⊔ T7)).trans (commutator_le_rng5 hMi))
        (le_perfectCore_of_perfect hle hperf5)
    obtain ⟨eB⟩ := lFamily_equiv_of_perfectCore_equiv hB alt5_nonabelian
      ((MulEquiv.subgroupCongr hpc).trans rng5Equiv)
    have hL : IsAlt 7 ↥(⊤ : Subgroup ↥A7s) := ⟨Subgroup.topEquiv⟩
    iterate 4 right
    left
    exact And.intro (Or.inl ⟨eB⟩) (Or.inl hL)
  ·
    exact case_L3 hB (((B ⊔ T7).equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
      ((MulEquiv.subgroupCongr hMi).trans z8Equiv.symm))
  ·
    exact case_L3 hB (((B ⊔ T7).equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
      ((MulEquiv.subgroupCongr hMi).trans z9Equiv.symm))
  ·
    exact case_A6 hB ((MulEquiv.subgroupCongr (eq_rng6 hMi)).trans rng6Equiv)
  · exfalso
    apply hMne
    apply Subgroup.eq_top_of_card_eq
    rw [hcardM, card_A7s]
    decide

theorem a312For_A7 (hq : CFSG.IsQuasisimple ↥A7s) : A312For ↥A7s :=
  A312For.of_sylow T7 isSylowTwoOf_T7 fun _ hB hBtop => alt7_core hq hB hBtop

end CFSG.QuasithinUnique.Vol2Native.A312L.Seven

namespace CFSG.QuasithinUnique.Vol2Native.A312L

theorem alt7 : FamAlt7 := by
  intro X _ _ hq h
  obtain ⟨e⟩ := h
  have hqY : CFSG.IsQuasisimple ↥Seven.A7s := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  exact A312For.of_mulEquiv e (Seven.a312For_A7 hqY)

end CFSG.QuasithinUnique.Vol2Native.A312L
