module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundBase
import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma119
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Holt.Fixed
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.Walter.Bender1970.S1
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.Bender1970.S3.PGroupFStar
import CFSG.Walter.PSL2Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L J A : Subgroup G} {d b : G}

theorem exists_faithful_image {p : ℕ} {R : Type} [Group R]
    (hS : Setup p L J A d b) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (I : Set (MulAut R))
    (hact : ∀ a ∈ A, ∃ φ ∈ I, LargeEvenInduces θ (conjRel a) φ) :
    ∃ E : Subgroup (MulAut R), IsElemAbelian p E ∧ (E : Set (MulAut R)) ⊆ I ∧
      Nat.card E = Nat.card A ∧
      ∀ a ∈ A, ∃ φ ∈ E, LargeEvenInduces θ (conjRel a) φ := by
  classical
  have hAnorm : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hS.idiag
  let Φ0 : ↥A → MulAut R := fun a => Classical.choose (hact a.1 a.2)
  have hΦ0mem : ∀ a : ↥A, Φ0 a ∈ I := fun a =>
    (Classical.choose_spec (hact a.1 a.2)).1
  have hΦ0ind : ∀ a : ↥A, LargeEvenInduces θ (conjRel (a : G)) (Φ0 a) := fun a =>
    (Classical.choose_spec (hact a.1 a.2)).2
  have hΦ0_one : Φ0 1 = 1 := by
    have h1 : LargeEvenInduces θ (conjRel (1 : G)) (1 : MulAut R) :=
      largeEvenInduces_one (rel := conjRel (1 : G)) fun l l' hl => by
        have hl' : (l' : G) = (l : G) := by simpa [conjRel] using hl
        exact Subtype.ext hl'.symm
    exact largeEvenInduces_unique (hΦ0ind 1) h1 (conjRel_total (Subgroup.one_mem _))
  have hΦ0_mul : ∀ a b : ↥A, Φ0 (a * b) = Φ0 a * Φ0 b := by
    intro a b
    have hab : (a : G) * (b : G) = (b : G) * (a : G) :=
      IsElemAbelian.comm hS.elem a.2 b.2
    have h1 : LargeEvenInduces θ (conjRel ((a : G) * (b : G))) (Φ0 a * Φ0 b) :=
      largeEvenInduces_mul (hAnorm a.2) (hAnorm b.2) hab (hΦ0ind a) (hΦ0ind b)
    exact largeEvenInduces_unique (hΦ0ind (a * b)) h1
      (conjRel_total (hAnorm (Subgroup.mul_mem A a.2 b.2)))
  let Φ : ↥A →* MulAut R := { toFun := Φ0, map_one' := hΦ0_one, map_mul' := hΦ0_mul }
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have hg : (a : G) * (b : G)⁻¹ ∈ A := Subgroup.mul_mem A a.2 (inv_mem b.2)
    have hgN : (a : G) * (b : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) := hAnorm hg
    have hmap : Φ (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hzero : LargeEvenInduces θ (conjRel ((a : G) * (b : G)⁻¹)) (1 : MulAut R) :=
      hmap ▸ hΦ0ind (a * b⁻¹)
    have hcent : (a : G) * (b : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
      centralizes_of_conjRel_center hgN
        (exists_center_of_largeEvenInduces_one hgN hzero)
        (Group.isPerfect_def.mpr hS.qs.1)
    have hinf : (a : G) * (b : G)⁻¹ ∈ A ⊓ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_inf.mpr ⟨hg, hcent⟩
    rw [hS.faithful] at hinf
    have hgone : (a : G) * (b : G)⁻¹ = 1 := Subgroup.mem_bot.mp hinf
    apply Subtype.ext
    calc (a : G) = (a : G) * (b : G)⁻¹ * (b : G) := by group
      _ = 1 * (b : G) := by rw [hgone]
      _ = (b : G) := one_mul _
  have hAbel : IsElemAbelian p Φ.range := by
    have h := (hS.elem.subgroupOf A).map Φ
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h
  refine ⟨Φ.range, hAbel, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    exact hΦ0mem a
  · let e : ↥A → Φ.range := fun a => ⟨Φ a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
    have hinj : Function.Injective e := fun a b h => hΦinj (Subtype.ext_iff.mp h)
    have hsurj : Function.Surjective e := by
      intro y
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp y.2
      exact ⟨a, Subtype.ext ha⟩
    exact (Nat.card_congr (Equiv.ofBijective e ⟨hinj, hsurj⟩)).symm
  · intro a ha
    exact ⟨Φ ⟨a, ha⟩, MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩, hΦ0ind ⟨a, ha⟩⟩

private theorem three_pow_five_le_card_of_not_le (hS : Setup 3 L J A d b)
    (hle : ¬ Nat.card A ≤ 3 ^ 4) : 3 ^ 5 ≤ Nat.card A := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS.elem.isPGroup
  have hk5 : 5 ≤ k := by
    by_contra h
    have hk4 : k ≤ 4 := by omega
    exact hle (hk.symm ▸ Nat.pow_le_pow_right (by norm_num) hk4)
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk5

private theorem e6Bound_true_of (hMt : TwE6Marking) (hXt : TwE6BigToralExit) :
    E6Bound true := by
  intro G _ _ L J A d b hS hcat
  by_contra hle
  have h5 : 3 ^ 5 ≤ Nat.card A := three_pow_five_le_card_of_not_le hS hle
  obtain ⟨n, K, hK, hKfin, hn, h3, hcardK, _, θ, hact⟩ :=
    hMt G L J A d b hS (by simpa using hcat)
  letI := hK
  letI := hKfin
  obtain ⟨E, hE, hEI, hcardE, hind⟩ :=
    exists_faithful_image hS θ (TwE6Delta.RecipeI K n) hact
  have hE5 : 3 ^ 5 ≤ Nat.card E := by rw [hcardE]; exact h5
  exact hS.nonID (hXt G L J A d b n K hn hcardK h3 hS θ E hE hE5 hEI
    (hind d hS.d_mem) (hind b hS.b_mem))

private theorem e6Bound_false_of (hMu : E6Marking) (hXu : E6BigToralExit) :
    E6Bound false := by
  intro G _ _ L J A d b hS hcat
  by_contra hle
  have h5 : 3 ^ 5 ≤ Nat.card A := three_pow_five_le_card_of_not_le hS hle
  obtain ⟨n, K, hK, hKfin, hn, h3, hcardK, θ, hact⟩ :=
    hMu G L J A d b hS (by simpa using hcat)
  letI := hK
  letI := hKfin
  obtain ⟨E, hE, hEI, hcardE, hind⟩ :=
    exists_faithful_image hS θ
      (LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenChevH (LargeEvenCartanE 6) K false)) hact
  have hE5 : 3 ^ 5 ≤ Nat.card E := by rw [hcardE]; exact h5
  exact hS.nonID (hXu G L J A d b n K hn hcardK h3 hS θ E hE hE5 hEI
    (hind d hS.d_mem) (hind b hS.b_mem))

theorem e6Bound_of (hMt : TwE6Marking) (hXt : TwE6BigToralExit) (hMu : E6Marking)
    (hXu : E6BigToralExit) (tw : Bool) : E6Bound tw := by
  cases tw
  · exact e6Bound_false_of hMu hXu
  · exact e6Bound_true_of hMt hXt

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
