module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviHeis
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSylow
import CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo

public section

namespace CFSG.AGLEmbedding

open CFSG.Fischer.Classification
open scoped commutatorElement

variable {K : Type*} [Group K]

structure EndNodeSUThree (L T U : Subgroup K) (x y : K) : Prop where
  cubeRel : CubeRel x y
  ne_comm : x * y ≠ y * x
  x_mem : x ∈ L
  y_mem : y ∈ L
  le_normalizer : L ≤ Subgroup.normalizer (Subgroup.closure ({x, y} : Set K) : Set K)
  card : Nat.card L = 216
  pow_three_of_commute : ∀ g ∈ L, g * x = x * g → g * y = y * g → g ^ 3 = 1
  eq_one_of_mem_center : ∀ z ∈ Subgroup.center K, z ∈ L → z = 1
  torus_pow : ∀ t ∈ T, t ^ 3 = 1
  torus_le_normalizer : T ≤ Subgroup.normalizer (L : Set K)
  torus_le_normalizer_unip : T ≤ Subgroup.normalizer (U : Set K)
  le_normalizer_unip : L ≤ Subgroup.normalizer (U : Set K)
  isPGroup_unip : IsPGroup 2 U
  exists_comm : ∃ d ∈ T, ∃ q ∈ L, (q * d * q⁻¹ * d⁻¹) ^ 3 ≠ 1

namespace EndNodeSUThree

variable [Finite K] {L T U : Subgroup K} {x y : K} (h : EndNodeSUThree L T U x y)
include h

omit [Finite K] in
theorem closure_le_rankOne : Subgroup.closure ({x, y} : Set K) ≤ L := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact h.x_mem
  · exact h.y_mem

theorem card_closure_heisR : Nat.card (Subgroup.closure ({x, y} : Set K)) = 27 :=
  CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo.card_closure_eq_of_cubeRel h.cubeRel
    h.ne_comm

theorem isPGroup_closure_heis : IsPGroup 3 (Subgroup.closure ({x, y} : Set K)) :=
  IsPGroup.of_card (n := 3) (by rw [h.card_closure_heisR]; norm_num)

theorem le_closure_of_isPGroup {V : Subgroup K} (hVL : V ≤ L) (hV : IsPGroup 3 V) :
    V ≤ Subgroup.closure ({x, y} : Set K) :=
  le_of_isPGroup_three_of_normal h.closure_le_rankOne h.le_normalizer h.isPGroup_closure_heis
    (m := 8) (by norm_num) (by rw [h.card, h.card_closure_heisR]) hVL hV

theorem pow_three_of_pow_eq_one {w : K} (hwL : w ∈ L) {e : ℕ} (hw : w ^ 3 ^ e = 1) :
    w ^ 3 = 1 := by
  have h3 : IsPGroup 3 (Subgroup.zpowers w) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨e, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]
  have hle := h.le_closure_of_isPGroup ((Subgroup.zpowers_le).2 hwL) h3
  exact h.cubeRel.pow_three_eq_one (hle (Subgroup.mem_zpowers w))

theorem conj_mem_closure_of_mem_normalizer {t : K} (ht : t ∈ Subgroup.normalizer (L : Set K))
    {r : K} (hr : r ∈ Subgroup.closure ({x, y} : Set K)) :
    t * r * t⁻¹ ∈ Subgroup.closure ({x, y} : Set K) := by
  set V := (Subgroup.closure ({x, y} : Set K)).map (MulAut.conj t).toMonoidHom
  have hVL : V ≤ L := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 ht s).1 (h.closure_le_rankOne hs)
  exact h.le_closure_of_isPGroup hVL (h.isPGroup_closure_heis.map _) ⟨r, hr, rfl⟩

theorem mem_normalizer_closure_of_mem_normalizer {t : K}
    (ht : t ∈ Subgroup.normalizer (L : Set K)) :
    t ∈ Subgroup.normalizer (Subgroup.closure ({x, y} : Set K) : Set K) :=
  Subgroup.mem_normalizer_fintype fun _ hr => h.conj_mem_closure_of_mem_normalizer ht hr

omit [Finite K] in
theorem eq_one_of_mem_of_le_normalizer {M : Subgroup K}
    (hM : L ≤ Subgroup.normalizer (M : Set K)) (hM3 : ∀ m ∈ M, m ∈ L → m ^ 3 = 1 → m = 1)
    {m : K} (hm : m ∈ M) (hmL : m ∈ L) : m = 1 := by
  have hcomm : ∀ r ∈ Subgroup.closure ({x, y} : Set K), m * r = r * m := by
    intro r hr
    have hrL := h.closure_le_rankOne hr
    have hcM : m * r * m⁻¹ * r⁻¹ ∈ M := by
      have h1 : r * m⁻¹ * r⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1 (hM hrL) _).1 (inv_mem hm)
      have h2 := mul_mem hm h1
      rwa [← mul_assoc, ← mul_assoc] at h2
    have hcR : m * r * m⁻¹ * r⁻¹ ∈ Subgroup.closure ({x, y} : Set K) :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 (h.le_normalizer hmL) r).1 hr) (inv_mem hr)
    have hc1 := hM3 _ hcM (h.closure_le_rankOne hcR) (h.cubeRel.pow_three_eq_one hcR)
    calc m * r = m * r * m⁻¹ * r⁻¹ * (r * m) := by group
      _ = r * m := by rw [hc1, one_mul]
  exact hM3 m hm hmL (h.pow_three_of_commute m hmL
    (hcomm x (Subgroup.subset_closure (Set.mem_insert x {y})))
    (hcomm y (Subgroup.subset_closure (Set.mem_insert_of_mem x rfl))))

omit [Finite K] in
theorem pow_three_mem_unip {g : K} (hg : g ∈ U ⊔ Subgroup.closure ({x, y} : Set K)) :
    g ^ 3 ∈ U := by
  have hRU := h.closure_le_rankOne.trans h.le_normalizer_unip
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left U _ hRU] at hg
  obtain ⟨u, hu, r, hr, rfl⟩ := hg
  have e : (u * r) ^ 3 = u * (r * u * r⁻¹) * ((r * r) * u * (r * r)⁻¹) * r ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [e, h.cubeRel.pow_three_eq_one hr, mul_one]
  have h1 : r * u * r⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hRU hr) u).1 hu
  have h2 : (r * r) * u * (r * r)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.1 (hRU (mul_mem hr hr)) u).1 hu
  exact mul_mem (mul_mem hu h1) h2

section Center

variable {Z : Subgroup K} (hZ : Z ≤ Subgroup.center K) (hZ3 : ∀ c ∈ Z, c ^ 3 = 1)
include hZ

omit [Finite K] h in
theorem exists_mul_of_mem_sup_center {g : K} (hg : g ∈ T ⊔ Z) :
    ∃ t ∈ T, ∃ c ∈ Z, g = t * c := by
  have : Z.Normal := ⟨fun c hc g => by
    rw [Subgroup.mem_center_iff.1 (hZ hc) g, mul_inv_cancel_right]
    exact hc⟩
  rw [← SetLike.mem_coe, Subgroup.mul_normal T Z] at hg
  obtain ⟨t, ht, c, hc, rfl⟩ := hg
  exact ⟨t, ht, c, hc, rfl⟩

omit [Finite K] in
include hZ3 in
theorem torus_sup_pow {g : K} (hg : g ∈ T ⊔ Z) : g ^ 3 = 1 := by
  obtain ⟨t, ht, c, hc, rfl⟩ := exists_mul_of_mem_sup_center hZ hg
  have hcomm : Commute t c := Subgroup.mem_center_iff.1 (hZ hc) t
  rw [hcomm.mul_pow, h.torus_pow t ht, hZ3 c hc, one_mul]

omit [Finite K] in
theorem torus_sup_le_normalizer : T ⊔ Z ≤ Subgroup.normalizer (L : Set K) :=
  sup_le h.torus_le_normalizer (hZ.trans (Subgroup.center_le_normalizer _))

include hZ3 in
theorem card_sup_rankOne :
    Nat.card ↥((T ⊔ Z) ⊔ L) = 8 * Nat.card ↥((T ⊔ Z) ⊔ Subgroup.closure ({x, y} : Set K)) := by
  have hTL := h.torus_sup_le_normalizer hZ
  have hTR : T ⊔ Z ≤ Subgroup.normalizer (Subgroup.closure ({x, y} : Set K) : Set K) :=
    fun t ht => h.mem_normalizer_closure_of_mem_normalizer (hTL ht)
  rw [card_sup_eq_mul_index _ _ hTL, card_sup_eq_mul_index _ _ hTR, h.card, h.card_closure_heisR]
  have hP : IsPGroup 3 ↥((T ⊔ Z) ⊓ L) := fun g =>
    ⟨1, Subtype.ext (by simpa using h.torus_sup_pow hZ hZ3 g.2.1)⟩
  have hle := h.le_closure_of_isPGroup inf_le_right hP
  have he : L.subgroupOf (T ⊔ Z) = (Subgroup.closure ({x, y} : Set K)).subgroupOf (T ⊔ Z) := by
    ext ⟨t, ht⟩
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun htL => hle ⟨ht, htL⟩, fun htR => h.closure_le_rankOne htR⟩
  rw [he]
  ring

include hZ3 in
theorem pow_three_mem_zpowers_commutator {g : K}
    (hg : g ∈ (T ⊔ Z) ⊔ Subgroup.closure ({x, y} : Set K)) : g ^ 3 ∈ Subgroup.zpowers ⁅x, y⁆ := by
  have hTL := h.torus_sup_le_normalizer hZ
  have hTR : T ⊔ Z ≤ Subgroup.normalizer (Subgroup.closure ({x, y} : Set K) : Set K) :=
    fun t ht => h.mem_normalizer_closure_of_mem_normalizer (hTL ht)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTR] at hg
  obtain ⟨t, ht, r, hr, rfl⟩ := hg
  exact pow_three_mem_zpowers_of_cubeRel h.cubeRel h.ne_comm (h.torus_sup_pow hZ hZ3 ht)
    (fun s hs => h.conj_mem_closure_of_mem_normalizer (hTL ht) hs) hr

end Center

end EndNodeSUThree

end CFSG.AGLEmbedding
