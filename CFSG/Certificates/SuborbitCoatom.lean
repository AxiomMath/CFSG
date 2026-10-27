module

public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Atoms

public section

namespace CFSG.Certificates

open scoped Pointwise

theorem isCoatom_stabilizer_of_suborbits {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (x : X) (H : Subgroup G) (hH : H ≤ MulAction.stabilizer G x) {k : ℕ}
    (B : Fin (k + 1) → Set X) (hB0 : B 0 = {x})
    (hBorb : ∀ c, B c ⊆ MulAction.orbit G x)
    (hcover : ∀ y ∈ MulAction.orbit G x, ∃ c, y ∈ B c)
    (hdisj : ∀ c d, c ≠ d → Disjoint (B c) (B d))
    (htrans : ∀ c, ∀ y ∈ B c, ∀ z ∈ B c, ∃ h ∈ H, h • y = z)
    (hprim : ∀ T : Finset (Fin (k + 1)), 0 ∈ T →
      (∑ c ∈ T, (B c).ncard) ∣ ∑ c, (B c).ncard → T = {0} ∨ T = Finset.univ)
    (hnt : ∃ c, c ≠ 0 ∧ (B c).Nonempty) :
    IsCoatom (MulAction.stabilizer G x) := by
  classical
  have hXfin : (MulAction.orbit G x).Finite := Set.finite_range _
  have hBfin : ∀ c, (B c).Finite := fun c => hXfin.subset (hBorb c)
  have hunion : ∀ T : Finset (Fin (k + 1)),
      (⋃ c ∈ T, B c).ncard = ∑ c ∈ T, (B c).ncard := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
      have hfinU : (⋃ c ∈ T, B c).Finite :=
        hXfin.subset (Set.iUnion₂_subset fun c _ => hBorb c)
      have hd : Disjoint (B a) (⋃ c ∈ T, B c) := by
        rw [Set.disjoint_iUnion₂_right]
        intro c hc
        exact hdisj a c (fun h => ha (h ▸ hc))
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha, Set.ncard_union_eq hd (hBfin a) hfinU,
        ih]
  have horbit : MulAction.orbit G x = ⋃ c ∈ (Finset.univ : Finset (Fin (k + 1))), B c := by
    ext y
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    exact ⟨hcover y, fun ⟨c, hc⟩ => hBorb c hc⟩
  have hcardG : (MulAction.orbit G x).ncard = ∑ c, (B c).ncard := by
    rw [horbit, hunion]
  refine ⟨fun htop => ?_, fun L hKL => ?_⟩
  ·
    obtain ⟨c, hc0, y, hy⟩ := hnt
    obtain ⟨g, rfl⟩ := hBorb c hy
    have hg : g ∈ MulAction.stabilizer G x := htop ▸ Subgroup.mem_top g
    rw [MulAction.mem_stabilizer_iff] at hg
    have hx0 : x ∈ B 0 := by rw [hB0]; rfl
    have hy' : g • x ∈ B c := hy
    rw [hg] at hy'
    exact Set.disjoint_left.1 (hdisj c 0 hc0) hy' hx0
  set K := MulAction.stabilizer G x
  set OL : Set X := (fun g : G => g • x) '' (L : Set G) with hOL
  have hOLorb : OL ⊆ MulAction.orbit G x := by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩
  set T : Finset (Fin (k + 1)) := Finset.univ.filter fun c => (B c ∩ OL).Nonempty with hT
  have hOLT : OL = ⋃ c ∈ T, B c := by
    ext y
    simp only [Set.mem_iUnion, hT, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := hcover y (hOLorb hy)
      exact ⟨c, ⟨y, hc, hy⟩, hc⟩
    · rintro ⟨c, ⟨w, hwc, hwL⟩, hyc⟩
      obtain ⟨h, hh, rfl⟩ := htrans c w hwc y hyc
      obtain ⟨l, hl, rfl⟩ := hwL
      refine ⟨h * l, L.mul_mem (hKL.le (hH hh)) hl, ?_⟩
      simp only [mul_smul]
  have hcardL : OL.ncard = ∑ c ∈ T, (B c).ncard := by rw [hOLT, hunion]
  have hstabL : (K.subgroupOf L).index = OL.ncard := by
    have h := MulAction.index_stabilizer (G := ↥L) (x := x)
    have e1 : MulAction.stabilizer (↥L) x = K.subgroupOf L := by
      ext g
      simp [K, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    have e2 : MulAction.orbit (↥L) x = OL := by
      ext y
      simp only [MulAction.mem_orbit_iff, hOL, Set.mem_image, SetLike.mem_coe, Subtype.exists,
        Subgroup.mk_smul, exists_prop]
    rw [← e1, ← e2, h]
  have hindexG : K.index = (MulAction.orbit G x).ncard := MulAction.index_stabilizer G x
  have hmul := Subgroup.relIndex_mul_index hKL.le
  rw [Subgroup.relIndex] at hmul
  have hdvd : (∑ c ∈ T, (B c).ncard) ∣ ∑ c, (B c).ncard := by
    rw [← hcardL, ← hstabL, ← hcardG, ← hindexG, ← hmul]
    exact Dvd.intro _ rfl
  have h0T : (0 : Fin (k + 1)) ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨x, by rw [hB0]; rfl, 1, L.one_mem, one_smul _ _⟩
  rcases hprim T h0T hdvd with hT0 | hTU
  ·
    exfalso
    have h1 : OL.ncard = 1 := by
      rw [hcardL, hT0, Finset.sum_singleton, hB0, Set.ncard_singleton]
    rw [← hstabL, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
    exact (lt_irrefl _ (lt_of_lt_of_le hKL h1))
  ·
    have h1 : (K.subgroupOf L).index = K.index := by
      rw [hstabL, hcardL, hTU, hindexG, hcardG]
    have hpos : 0 < (K.subgroupOf L).index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rw [← h1] at hmul
    have hL1 : L.index = 1 := by
      have := Nat.eq_of_mul_eq_mul_left hpos (hmul.trans (mul_one _).symm)
      exact this
    exact Subgroup.index_eq_one.1 hL1

end CFSG.Certificates
