module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
open CFSG.EvenSporadicStandard.HNRecog.TwoHSData

section Iso

variable {H H' : Type} [Group H] [Group H']

private theorem isConj_map_iff {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (x y : G) :
    IsConj (e x) (e y) ↔ IsConj x y :=
  ⟨isConj_of_map_mulEquiv e, isConj_map_mulEquiv e⟩

private theorem map_ne_iff {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (x y : G) :
    e x ≠ e y ↔ x ≠ y := by
  simp only [ne_eq, e.injective.eq_iff]

private theorem mem_tab4Base_map (e : H ≃* H') (a b y x : H) :
    e x ∈ tab4Base (e a) (e b) (e y) ↔ x ∈ tab4Base a b y := by
  simp only [tab4Base, Set.mem_setOf_eq, ← map_mul, isConj_map_iff, map_ne_iff]

private theorem mem_tab6Base_map (e : H ≃* H') (a z y x : H) :
    e x ∈ tab6Base (e a) (e z) (e y) ↔ x ∈ tab6Base a z y := by
  simp only [tab6Base, Set.mem_setOf_eq, ← map_mul, isConj_map_iff, map_ne_iff]

theorem HIsA_map (e : H ≃* H') (a z b x : H) : HIsA (e a) (e z) (e b) (e x) ↔ HIsA a z b x := by
  unfold HIsA
  rw [← map_mul]
  exact or_congr (isConj_map_iff e a x)
    (or_congr (isConj_map_iff e (a * z) x) (isConj_map_iff e b x))

theorem HIsB_map (e : H ≃* H') (z z₁ x : H) : HIsB (e z) (e z₁) (e x) ↔ HIsB z z₁ x := by
  unfold HIsB
  exact or_congr (isConj_map_iff e z x) (isConj_map_iff e z₁ x)

private theorem HIsA_map' (e : H ≃* H') (a z b y x : H) :
    HIsA (e a) (e z) (e b) (e y * e x) ↔ HIsA a z b (y * x) := by
  rw [← map_mul]
  exact HIsA_map e a z b (y * x)

private theorem HIsB_map' (e : H ≃* H') (z z₁ y x : H) :
    HIsB (e z) (e z₁) (e y * e x) ↔ HIsB z z₁ (y * x) := by
  rw [← map_mul]
  exact HIsB_map e z z₁ (y * x)

private theorem pow_eq_map (e : H ≃* H') (a y x : H) (n : ℕ) :
    (e y * e x) ^ n = e a ↔ (y * x) ^ n = a := by
  rw [← map_mul, ← map_pow, e.injective.eq_iff]

private theorem HIsA_pow_map (e : H ≃* H') (a z b y x : H) (n : ℕ) :
    HIsA (e a) (e z) (e b) ((e y * e x) ^ n) ↔ HIsA a z b ((y * x) ^ n) := by
  rw [← map_mul, ← map_pow]
  exact HIsA_map e a z b ((y * x) ^ n)

private theorem HIsB_pow_map (e : H ≃* H') (z z₁ y x : H) (n : ℕ) :
    HIsB (e z) (e z₁) ((e y * e x) ^ n) ↔ HIsB z z₁ ((y * x) ^ n) := by
  rw [← map_mul, ← map_pow]
  exact HIsB_map e z z₁ ((y * x) ^ n)

private theorem orderOf_mul_map (e : H ≃* H') (y x : H) :
    orderOf (e y * e x) = orderOf (y * x) := by
  rw [← map_mul, MulEquiv.orderOf_eq]

private theorem isShapeFiveC_Gx_map (e : H ≃* H') (x : H) :
    IsShapeCentralizerFiveC ↥(Gx (e x)) ↔ IsShapeCentralizerFiveC ↥(Gx x) :=
  ⟨fun h => IsShapeCentralizerFiveC.of_mulEquiv (centralizerMulEquiv e x).symm h,
   fun h => IsShapeCentralizerFiveC.of_mulEquiv (centralizerMulEquiv e x) h⟩

private theorem isShapeFiveB_Gx_map (e : H ≃* H') (x : H) :
    IsShapeCentralizerFiveB ↥(Gx (e x)) ↔ IsShapeCentralizerFiveB ↥(Gx x) :=
  ⟨fun h => IsShapeCentralizerFiveB.of_mulEquiv (centralizerMulEquiv e x).symm h,
   fun h => IsShapeCentralizerFiveB.of_mulEquiv (centralizerMulEquiv e x) h⟩

private theorem isShapeFiveC_Gx_mul_map (e : H ≃* H') (y x : H) :
    IsShapeCentralizerFiveC ↥(Gx (e y * e x)) ↔ IsShapeCentralizerFiveC ↥(Gx (y * x)) := by
  rw [← map_mul]
  exact isShapeFiveC_Gx_map e (y * x)

private theorem isShapeFiveB_Gx_mul_map (e : H ≃* H') (y x : H) :
    IsShapeCentralizerFiveB ↥(Gx (e y * e x)) ↔ IsShapeCentralizerFiveB ↥(Gx (y * x)) := by
  rw [← map_mul]
  exact isShapeFiveB_Gx_map e (y * x)

private theorem mem_Gx_map (e : H ≃* H') (z x : H) : e x ∈ Gx (e z) ↔ x ∈ Gx z := by
  rw [mem_Gx, mem_Gx, ← map_mul, ← map_mul, e.injective.eq_iff]

private theorem HIsA_map_mul3 (e : H ≃* H') (a z b x : H) :
    HIsA (e a) (e z) (e b) (e a * e z * e x) ↔ HIsA a z b (a * z * x) := by
  rw [← map_mul, ← map_mul]
  exact HIsA_map e a z b (a * z * x)

private theorem HIsB_map_mul3 (e : H ≃* H') (a z z₁ x : H) :
    HIsB (e z) (e z₁) (e a * e z * e x) ↔ HIsB z z₁ (a * z * x) := by
  rw [← map_mul, ← map_mul]
  exact HIsB_map e z z₁ (a * z * x)

theorem nonempty_mulEquiv_inf_Gx_map (e : H ≃* H') (y c : H) :
    Nonempty (↥(Gx y ⊓ Gx c) ≃* ↥(Gx (e y) ⊓ Gx (e c))) := by
  refine ⟨(mapSubgroupMulEquiv e (Gx y ⊓ Gx c)).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [Subgroup.map_inf_eq (Gx y) (Gx c) e.toMonoidHom e.injective,
    map_centralizer_singleton e y, map_centralizer_singleton e c]

theorem natCard_Gx_map (e : H ≃* H') (y : H) : Nat.card ↥(Gx (e y)) = Nat.card ↥(Gx y) :=
  (Nat.card_congr (centralizerMulEquiv e y).toEquiv).symm

theorem mem_tab4Set_map (e : H ≃* H') (a z b z₁ y x : H) (i : Fin 6) :
    e x ∈ tab4Set (e a) (e z) (e b) (e z₁) (e y) i ↔ x ∈ tab4Set a z b z₁ y i := by
  fin_cases i <;>
    simp [tab4Set, mem_tab4Base_map, HIsA_map', HIsB_map', HIsA_map, HIsB_map, HIsA_pow_map,
      HIsB_pow_map, pow_eq_map, orderOf_mul_map]

theorem mem_tab6Set_map (e : H ≃* H') (a z b z₁ y x : H) (i : Fin 8) :
    e x ∈ tab6Set (e a) (e z) (e b) (e z₁) (e y) i ↔ x ∈ tab6Set a z b z₁ y i := by
  fin_cases i <;>
    simp [tab6Set, mem_tab6Base_map, HIsA_map', HIsB_map', HIsA_map, HIsB_map, HIsA_pow_map,
      HIsB_pow_map, orderOf_mul_map, isShapeFiveC_Gx_mul_map, isShapeFiveB_Gx_mul_map]

theorem mem_tabXSet_map (e : H ≃* H') (a z b z₁ x : H) (i : Fin 2) :
    e x ∈ tabXSet (e a) (e z) (e b) (e z₁) i ↔ x ∈ tabXSet a z b z₁ i := by
  fin_cases i <;>
    simp [- isConj_iff, tabXSet, isConj_map_iff, mem_Gx_map, HIsA_map_mul3, HIsB_map_mul3]

end Iso

section Class

variable {H : Type} [Group H]

private theorem conj_eq_iff (g x y : H) : g * x * g⁻¹ = g * y * g⁻¹ ↔ x = y :=
  (conj_injective (x := g)).eq_iff

private theorem conj_ne_iff (g x y : H) : g * x * g⁻¹ ≠ g * y * g⁻¹ ↔ x ≠ y := by
  simp only [ne_eq, conj_eq_iff]

private theorem isConj_self_conj (g x : H) : IsConj x (g * x * g⁻¹) :=
  isConj_iff.2 ⟨g, rfl⟩

private theorem isConj_congr_right_conj (g b x : H) :
    IsConj b (g * x * g⁻¹) ↔ IsConj b x :=
  ⟨fun h => h.trans (isConj_self_conj g x).symm, fun h => h.trans (isConj_self_conj g x)⟩

private theorem isConj_congr_left {b b' : H} (hb : IsConj b b') (c : H) :
    IsConj b' c ↔ IsConj b c :=
  ⟨fun h => hb.trans h, fun h => (isConj_comm.mp hb).trans h⟩

private theorem conj_center {a : H} (ha : a ∈ Subgroup.center H) (g : H) :
    g * a * g⁻¹ = a := by
  rw [Subgroup.mem_center_iff.mp ha g]
  simp

private theorem conj_mul_center {a : H} (ha : a ∈ Subgroup.center H) (y g : H) :
    g * (a * y) * g⁻¹ = a * (g * y * g⁻¹) := by
  rw [← conj_mul, conj_center ha g]

private theorem isConj_mul_center {a : H} (ha : a ∈ Subgroup.center H) {z z' : H}
    (hz : IsConj z z') : IsConj (a * z) (a * z') := by
  rw [isConj_iff] at hz ⊢
  obtain ⟨g, hg⟩ := hz
  refine ⟨g, ?_⟩
  rw [← conj_mul, conj_center ha g, hg]

private theorem mem_tab4Base_conj {a : H} (ha : a ∈ Subgroup.center H) (b y x g : H) :
    g * x * g⁻¹ ∈ tab4Base a b (g * y * g⁻¹) ↔ x ∈ tab4Base a b y := by
  simp only [tab4Base, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(isConj_congr_right_conj g b x).mp h1, (conj_ne_iff g x y).mp h2, ?_⟩
    rw [← conj_mul_center ha y g] at h3
    exact (conj_ne_iff g x (a * y)).mp h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(isConj_congr_right_conj g b x).mpr h1, (conj_ne_iff g x y).mpr h2, ?_⟩
    rw [← conj_mul_center ha y g]
    exact (conj_ne_iff g x (a * y)).mpr h3

private theorem mem_tab6Base_conj (a z y x g : H) :
    g * x * g⁻¹ ∈ tab6Base a z (g * y * g⁻¹) ↔ x ∈ tab6Base a z y := by
  simp only [tab6Base, Set.mem_setOf_eq]
  exact and_congr (isConj_congr_right_conj g (a * z) x) (conj_ne_iff g x y)

private theorem HIsA_conj (a z b y x g : H) :
    HIsA a z b (g * (y * x) * g⁻¹) ↔ HIsA a z b (y * x) := by
  unfold HIsA
  rw [isConj_congr_right_conj g a (y * x), isConj_congr_right_conj g (a * z) (y * x),
    isConj_congr_right_conj g b (y * x)]

private theorem HIsB_conj (z z₁ y x g : H) :
    HIsB z z₁ (g * (y * x) * g⁻¹) ↔ HIsB z z₁ (y * x) := by
  unfold HIsB
  rw [isConj_congr_right_conj g z (y * x), isConj_congr_right_conj g z₁ (y * x)]

private theorem HIsA_conj_pow (a z b y x g : H) (n : ℕ) :
    HIsA a z b (g * (y * x) ^ n * g⁻¹) ↔ HIsA a z b ((y * x) ^ n) := by
  unfold HIsA
  rw [isConj_congr_right_conj g a ((y * x) ^ n),
    isConj_congr_right_conj g (a * z) ((y * x) ^ n),
    isConj_congr_right_conj g b ((y * x) ^ n)]

private theorem HIsB_conj_pow (z z₁ y x g : H) (n : ℕ) :
    HIsB z z₁ (g * (y * x) ^ n * g⁻¹) ↔ HIsB z z₁ ((y * x) ^ n) := by
  unfold HIsB
  rw [isConj_congr_right_conj g z ((y * x) ^ n),
    isConj_congr_right_conj g z₁ ((y * x) ^ n)]

private theorem conj_pow_mul_eq {a : H} (ha : a ∈ Subgroup.center H) (y x g : H) (n : ℕ) :
    g * (y * x) ^ n * g⁻¹ = a ↔ (y * x) ^ n = a := by
  constructor
  · intro h
    have h' : g * (y * x) ^ n * g⁻¹ = g * a * g⁻¹ := by rw [h, conj_center ha g]
    exact (conj_eq_iff g ((y * x) ^ n) a).mp h'
  · intro h
    rw [h, conj_center ha g]

private theorem orderOf_conj_mul (y x g : H) :
    orderOf (g * (y * x) * g⁻¹) = orderOf (y * x) := by
  rw [← MulAut.conj_apply g (y * x)]
  exact MulEquiv.orderOf_eq (MulAut.conj g) (y * x)

private theorem isShapeFiveC_Gx_conj (y x g : H) :
    IsShapeCentralizerFiveC ↥(Gx (g * y * g⁻¹ * (g * x * g⁻¹))) ↔
      IsShapeCentralizerFiveC ↥(Gx (y * x)) := by
  rw [conj_mul, ← MulAut.conj_apply g (y * x)]
  exact isShapeFiveC_Gx_map (MulAut.conj g) (y * x)

private theorem isShapeFiveB_Gx_conj (y x g : H) :
    IsShapeCentralizerFiveB ↥(Gx (g * y * g⁻¹ * (g * x * g⁻¹))) ↔
      IsShapeCentralizerFiveB ↥(Gx (y * x)) := by
  rw [conj_mul, ← MulAut.conj_apply g (y * x)]
  exact isShapeFiveB_Gx_map (MulAut.conj g) (y * x)

theorem HIsA_congr {a z z' b b' : H} (ha : a ∈ Subgroup.center H) (hz : IsConj z z')
    (hb : IsConj b b') (x : H) : HIsA a z' b' x ↔ HIsA a z b x := by
  unfold HIsA
  refine or_congr Iff.rfl (or_congr ?_ (isConj_congr_left hb x))
  exact ⟨fun h => (isConj_mul_center ha hz).trans h,
    fun h => (isConj_mul_center ha hz).symm.trans h⟩

theorem HIsB_congr {z z' z₁ z₁' : H} (hz : IsConj z z') (hz₁ : IsConj z₁ z₁') (x : H) :
    HIsB z' z₁' x ↔ HIsB z z₁ x := by
  unfold HIsB
  exact or_congr (isConj_congr_left hz x) (isConj_congr_left hz₁ x)

private theorem isConj_congr_eq {p q : H} (h : IsConj p q) : IsConj q = IsConj p := by
  funext c
  exact propext ⟨fun hc => h.trans hc, fun hc => (isConj_comm.mp h).trans hc⟩

private theorem HIsA_congr_eq {a z z' b b' : H} (ha : a ∈ Subgroup.center H) (hz : IsConj z z')
    (hb : IsConj b b') : HIsA a z' b' = HIsA a z b := by
  funext x
  exact propext (HIsA_congr ha hz hb x)

private theorem HIsB_congr_eq {z z' z₁ z₁' : H} (hz : IsConj z z') (hz₁ : IsConj z₁ z₁') :
    HIsB z' z₁' = HIsB z z₁ := by
  funext x
  exact propext (HIsB_congr hz hz₁ x)

theorem tab4Set_congr {a z z' b b' z₁ z₁' : H} (ha : a ∈ Subgroup.center H) (hz : IsConj z z')
    (hb : IsConj b b') (hz₁ : IsConj z₁ z₁') (y : H) :
    tab4Set a z' b' z₁' y = tab4Set a z b z₁ y := by
  funext i
  ext c
  fin_cases i <;>
    simp [- isConj_iff, tab4Set, tab4Base, isConj_congr_eq hb, HIsA_congr_eq ha hz hb,
      HIsB_congr_eq hz hz₁]

theorem tab6Set_congr {a z z' b b' z₁ z₁' : H} (ha : a ∈ Subgroup.center H) (hz : IsConj z z')
    (hb : IsConj b b') (hz₁ : IsConj z₁ z₁') (y : H) :
    tab6Set a z' b' z₁' y = tab6Set a z b z₁ y := by
  funext i
  ext c
  fin_cases i <;>
    simp [- isConj_iff, tab6Set, tab6Base, isConj_congr_eq (isConj_mul_center ha hz),
      HIsA_congr_eq ha hz hb, HIsB_congr_eq hz hz₁]

theorem tabXSet_congr {a z b b' z₁ z₁' : H} (ha : a ∈ Subgroup.center H) (hb : IsConj b b')
    (hz₁ : IsConj z₁ z₁') : tabXSet a z b' z₁' = tabXSet a z b z₁ := by
  funext i
  ext c
  fin_cases i <;>
    simp [- isConj_iff, tabXSet, isConj_congr_eq hb, HIsA_congr_eq ha (IsConj.refl z) hb,
      HIsB_congr_eq (IsConj.refl z) hz₁]

theorem mem_tab4Set_conj {a : H} (ha : a ∈ Subgroup.center H) (z b z₁ y x g : H) (i : Fin 6) :
    g * x * g⁻¹ ∈ tab4Set a z b z₁ (g * y * g⁻¹) i ↔ x ∈ tab4Set a z b z₁ y i := by
  fin_cases i <;>
    simp [tab4Set, mem_tab4Base_conj ha b y x g, HIsA_conj, HIsB_conj, HIsB_conj_pow,
      conj_pow_mul_eq ha y x g, orderOf_conj_mul]

theorem mem_tab6Set_conj {a : H} (ha : a ∈ Subgroup.center H) (z b z₁ y x g : H) (i : Fin 8) :
    g * x * g⁻¹ ∈ tab6Set a z b z₁ (g * y * g⁻¹) i ↔ x ∈ tab6Set a z b z₁ y i := by
  fin_cases i <;>
    simp [tab6Set, mem_tab6Base_conj, HIsA_conj, HIsB_conj, HIsA_conj_pow, HIsB_conj_pow,
      orderOf_conj_mul, isShapeFiveC_Gx_conj, isShapeFiveB_Gx_conj]

end Class

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
