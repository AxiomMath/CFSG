module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.A6FrameCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4Levi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.E6.StdF4RadicalRoots
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.KD4L.TauCert
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open scoped Matrix MatrixGroups

namespace E6FourFine

private def iform (x : Fin Tag.E6.rank → ℤ) (j : Fin Tag.E6.rank) : ℤ :=
  ∑ i, Tag.E6.cartan j i * x i

private abbrev esingle (p : Fin Tag.E6.rank) : Fin Tag.E6.rank → ℤ := Pi.single p 1

private abbrev E (x : Fin Tag.E6.rank → ℤ) : Prop :=
  ∀ j ∈ d4Nodes Tag.E6, 2 ∣ iform x j

private lemma iform_single (i j : Fin Tag.E6.rank) :
    iform (esingle j) i = Tag.E6.cartan i j := by
  simp only [iform, esingle]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · intro h
    exact absurd (Finset.mem_univ j) h

private lemma iform_add (x y : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    iform (x + y) i = iform x i + iform y i := by
  simp only [iform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma iform_smul (c : ℤ) (x : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    iform (c • x) i = c * iform x i := by
  simp only [iform, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun l _ => by ring)

private lemma iform_sub (x y : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    iform (x - y) i = iform x i - iform y i := by
  simp only [iform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma iform_reflect (j : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    iform (reflect Tag.E6 j x) i = iform x i - iform x j * Tag.E6.cartan i j := by
  have h : reflect Tag.E6 j x = x - (iform x j) • (esingle j) := rfl
  rw [h, iform_sub, iform_smul, iform_single]

private lemma E_reflect {j : Fin Tag.E6.rank} (hj : j ∈ d4Nodes Tag.E6)
    {x : Fin Tag.E6.rank → ℤ} (hx : E x) : E (reflect Tag.E6 j x) := by
  intro i hi
  rw [iform_reflect]
  exact dvd_sub (hx i hi) (dvd_mul_of_dvd_left (hx j hj) (Tag.E6.cartan i j))

private lemma E_smul_of_mem (u : WeylGroup Tag.E6)
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)) :
    ∀ x, (E x ↔ E (u • x)) ∧ (E x → ∀ k, 2 ∣ (u • x - x) k) := by
  refine Subgroup.closure_induction
    (p := fun w _ => ∀ x, (E x ↔ E (w • x)) ∧ (E x → ∀ k, 2 ∣ (w • x - x) k))
    ?_ ?_ ?_ ?_ hu
  · rintro w ⟨j, hj, rfl⟩ x
    constructor
    · constructor
      · intro hx
        simpa only [simple_smul] using E_reflect hj hx
      · intro hx
        have h := E_reflect hj (x := simple Tag.E6 j • x) hx
        have h2 : simple Tag.E6 j • (simple Tag.E6 j • x) = x := by
          rw [← mul_smul, CoxeterSystem.simple_mul_simple_self (coxeterSystem Tag.E6) j,
            one_smul]
        rwa [← simple_smul, h2] at h
    · intro hx k
      have hk : (simple Tag.E6 j • x - x) k
          = -(iform x j * (esingle j) k) := by
        simp only [simple_smul, reflect, iform, esingle, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hk]
      exact dvd_neg.mpr (dvd_mul_of_dvd_left (hx j hj) _)
  · intro x
    constructor
    · simp
    · intro _ k
      simp
  · intro u v hu hv ihu ihv x
    rw [mul_smul]
    constructor
    · constructor
      · intro hx
        exact (ihu (v • x)).1.mp ((ihv x).1.mp hx)
      · intro hx
        exact (ihv x).1.mpr ((ihu (v • x)).1.mpr hx)
    · intro hx k
      have h1 : 2 ∣ (u • (v • x) - v • x) k := (ihu (v • x)).2 ((ihv x).1.mp hx) k
      have h2 : 2 ∣ (v • x - x) k := (ihv x).2 hx k
      have hsum : (u • (v • x) - x) k = (u • (v • x) - v • x) k + (v • x - x) k := by
        simp only [Pi.sub_apply]; ring
      rw [hsum]
      exact dvd_add h1 h2
  · intro u hu ihu x
    have hux : u • (u⁻¹ • x) = x := smul_inv_smul u x
    constructor
    · constructor
      · intro hx
        have h := (ihu (u⁻¹ • x)).1
        rw [hux] at h
        exact h.mpr hx
      · intro hx
        have h := (ihu (u⁻¹ • x)).1
        rw [hux] at h
        exact h.mp hx
    · intro hx k
      have hx' : E (u⁻¹ • x) := by
        have h := (ihu (u⁻¹ • x)).1
        rw [hux] at h
        exact h.mpr hx
      have hd : 2 ∣ (x - u⁻¹ • x) k := by
        have h := (ihu (u⁻¹ • x)).2 hx' k
        rwa [hux] at h
      have : (u⁻¹ • x - x) k = -((x - u⁻¹ • x) k) := by
        simp only [Pi.sub_apply]; ring
      rw [this]
      exact dvd_neg.mpr hd

private lemma single_mem_parabolicRoots {J : Set (Fin Tag.E6.rank)} {i : Fin Tag.E6.rank}
    (hi : i ∈ J) : esingle i ∈ parabolicRoots Tag.E6 J :=
  ⟨isRoot_single Tag.E6 i,
    fun j hj => Pi.single_eq_of_ne (fun h => hj (by rw [h]; exact hi)) 1⟩

private lemma eq_one_or_two_or_four {p : Fin Tag.E6.rank}
    (hp : p.val ∈ ({1, 2, 4} : Set ℕ)) : p = 1 ∨ p = 2 ∨ p = 4 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h | h | h
  · left; ext; exact h
  · right; left; ext; exact h
  · right; right; ext; exact h

private lemma cartan_pair_even (p q j : Fin Tag.E6.rank)
    (hp : p.val ∈ ({1, 2, 4} : Set ℕ)) (hq : q.val ∈ ({1, 2, 4} : Set ℕ))
    (hj : j ∈ d4Nodes Tag.E6) :
    2 ∣ Tag.E6.cartan j p + Tag.E6.cartan j q := by
  rcases eq_one_or_two_or_four hp with rfl | rfl | rfl <;>
    rcases eq_one_or_two_or_four hq with rfl | rfl | rfl <;>
    fin_cases j <;> simp_all [d4Nodes] <;> decide

private lemma E_single_add_single {p q : Fin Tag.E6.rank}
    (hp : p.val ∈ ({1, 2, 4} : Set ℕ)) (hq : q.val ∈ ({1, 2, 4} : Set ℕ)) :
    E (esingle p + esingle q) := by
  intro j hj
  rw [iform_add, iform_single, iform_single]
  exact cartan_pair_even p q j hp hq hj

theorem not_involution_of_leaf_threeCycle {a b c : Fin Tag.E6.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val ∈ ({1, 2, 4} : Set ℕ))
    (hb : b.val ∈ ({1, 2, 4} : Set ℕ)) (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    {u w' : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w' • α = u • permLattice (List.formPerm [a, b, c]) α)
    (hsq : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), w' • w' • α = α) : False := by
  have ha' : a ∈ d4Nodes Tag.E6 := by
    simp only [d4Nodes, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    omega
  have hb' : b ∈ d4Nodes Tag.E6 := by
    simp only [d4Nodes, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hb ⊢
    omega
  have hc' : c ∈ d4Nodes Tag.E6 := by
    simp only [d4Nodes, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
    omega
  have hroot_a : esingle a ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) :=
    single_mem_parabolicRoots ha'
  have hroot_b : esingle b ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) :=
    single_mem_parabolicRoots hb'
  have hroot_c : esingle c ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) :=
    single_mem_parabolicRoots hc'
  have hπa : List.formPerm [a, b, c] a = b := by
    rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (a := b) (b := c) (x := a) hab hac, Equiv.swap_apply_left]
  have hπb : List.formPerm [a, b, c] b = c := by
    rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (a := a) (b := b) (x := c) (Ne.symm hac) (Ne.symm hbc)]
  have hπc : List.formPerm [a, b, c] c = a := by
    rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_right]
  have hwa : w' • esingle a = u • esingle b := by
    have h := hact (esingle a) hroot_a
    rw [permLattice_single, hπa] at h
    exact h
  have hwb : w' • esingle b = u • esingle c := by
    have h := hact (esingle b) hroot_b
    rw [permLattice_single, hπb] at h
    exact h
  have hwc : w' • esingle c = u • esingle a := by
    have h := hact (esingle c) hroot_c
    rw [permLattice_single, hπc] at h
    exact h
  have hsa : w' • (u • esingle b) = esingle a := by
    have h := hsq (esingle a) hroot_a
    rw [hwa] at h
    exact h
  have hsb : w' • (u • esingle c) = esingle b := by
    have h := hsq (esingle b) hroot_b
    rw [hwb] at h
    exact h
  have hsc : w' • (u • esingle a) = esingle c := by
    have h := hsq (esingle c) hroot_c
    rw [hwc] at h
    exact h
  have step1 := E_smul_of_mem u hu
  have hE1 : E (esingle b + esingle c) := E_single_add_single hb hc
  have hdiv1 := (step1 (esingle b + esingle c)).2 hE1
  let t1 : Fin Tag.E6.rank → ℤ :=
    fun k => (u • (esingle b + esingle c) - (esingle b + esingle c)) k / 2
  have ht1 : u • (esingle b + esingle c) - (esingle b + esingle c) = (2 : ℤ) • t1 := by
    ext k
    simp only [t1, Pi.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdiv1 k)).symm
  have hE2 : E (esingle c + esingle a) := E_single_add_single hc ha
  have hdiv2 := (step1 (esingle c + esingle a)).2 hE2
  let t2 : Fin Tag.E6.rank → ℤ :=
    fun k => (u • (esingle c + esingle a) - (esingle c + esingle a)) k / 2
  have ht2 : u • (esingle c + esingle a) - (esingle c + esingle a) = (2 : ℤ) • t2 := by
    ext k
    simp only [t2, Pi.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdiv2 k)).symm
  have hy1 : u • esingle b + u • esingle c
      = (esingle b + esingle c) + (2 : ℤ) • t1 := by
    rw [← smul_add, ← ht1]
    abel
  have hy2 : u • esingle c + u • esingle a
      = (esingle c + esingle a) + (2 : ℤ) • t2 := by
    rw [← smul_add, ← ht2]
    abel
  have hL : w' • (u • esingle b + u • esingle c) = esingle a + esingle b := by
    rw [smul_add, hsa, hsb]
  have hR : w' • ((esingle b + esingle c) + (2 : ℤ) • t1)
      = (esingle c + esingle a) + (2 : ℤ) • (t2 + w' • t1) := by
    rw [smul_add, smul_add, hwb, hwc, smul_comm, hy2, smul_add]
    abel
  have hmain : esingle a + esingle b
      = (esingle c + esingle a) + (2 : ℤ) • (t2 + w' • t1) := by
    calc esingle a + esingle b
        = w' • (u • esingle b + u • esingle c) := hL.symm
      _ = w' • ((esingle b + esingle c) + (2 : ℤ) • t1) := by rw [hy1]
      _ = (esingle c + esingle a) + (2 : ℤ) • (t2 + w' • t1) := hR
  have hca : (esingle a) c = 0 := Pi.single_eq_of_ne (Ne.symm hac) 1
  have hcb : (esingle b) c = 0 := Pi.single_eq_of_ne (Ne.symm hbc) 1
  have hcc : (esingle c) c = 1 := Pi.single_eq_same c 1
  have hval := congrFun hmain c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hca, hcb, hcc] at hval
  omega

end E6FourFine

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

end
