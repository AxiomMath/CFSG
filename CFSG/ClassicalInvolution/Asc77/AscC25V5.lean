module

public import CFSG.ClassicalInvolution.Asc77.AscC25Y4
public import CFSG.ClassicalInvolution.Asc77.AscT7U6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Conj

variable {G : Type} [Group G] [Finite G] {R V : Subgroup G} {z : G}

theorem exists_conj_az (hR : IsQuatSub R) (hz : IsUniqueInvolution R z) (hV2 : IsPGroup 2 V)
    (hRV : R ≤ V) (hVR : ∀ y ∈ V, conjSub y R = R) {a : G} (haV : a ∈ V)
    (hFa : IsFAut R a) (ha2 : a * a ∈ Subgroup.zpowers z) :
    ∃ r ∈ R, r⁻¹ * a * r = a * z := by
  obtain ⟨x, y, n, c, hinv⟩ := T7F2.exists_coord hR hz hV2 hVR
  have s : T7F2.Out.Setting R V x y n := ⟨c, hRV, hVR, hinv⟩
  obtain ⟨hn2, hax, -⟩ := T7U.coord_of_isFAut hR hz s haV hFa ha2
  have hzx : z = x ^ (2 ^ n) := T7U.z_eq_pow_of_coord c hz
  have hz2 : z * z = 1 := hz.sq
  have hzR : z ∈ R := hz.mem
  have hzc : ∀ g : G, conjSub g R = R → g * z * g⁻¹ = z := by
    intro g hg
    have h1 : g * z * g⁻¹ ∈ R := by
      have := conj_mem_conjSub (n := g) hzR
      rwa [hg] at this
    have h2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
      calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    rcases hz.unique _ h1 h2 with h | h
    · exfalso
      apply hz.ne_one
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact h
  have haz : a * z * a⁻¹ = z := hzc a (hVR a haV)
  have hpow : x ^ ((1 : ℤ) + 2 ^ n) = x * z := by
    rw [zpow_add, zpow_one]
    congr 1
    rw [show ((2 : ℤ) ^ n) = ((2 ^ n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← hzx]
  rw [hpow] at hax
  refine ⟨x, c.ha, ?_⟩
  have h1 : a * x = x * z * a := by
    calc a * x = (a * x * a⁻¹) * a := by group
      _ = x * z * a := by rw [hax]
  have h2 : z * a = a * z := by
    calc z * a = (a * z * a⁻¹) * a := by rw [haz]
      _ = a * z := by group
  calc x⁻¹ * a * x = x⁻¹ * (a * x) := by group
    _ = x⁻¹ * (x * z * a) := by rw [h1]
    _ = z * a := by group
    _ = a * z := h2

end Conj

section ZStar

variable {G : Type} [Group G] [Finite G]

theorem mem_zStarOf_iff' (H : Subgroup G) {x : G} :
    x ∈ zStarOf H ↔ x ∈ H ∧ ∀ y ∈ H, x⁻¹ * y⁻¹ * x * y ∈ oddCoreOf H := by
  unfold zStarOf
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, fun y hy => ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff] at hh
    have h1 := hh (QuotientGroup.mk (⟨y, hy⟩ : ↥H))
    rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥H) (⟨y, hy⟩ : ↥H), ← map_mul,
      ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp [mul_assoc]⟩
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥H) y, ← map_mul, ← map_mul,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp (hc (y : G) y.2)
    have hwv' : (w : G) = x⁻¹ * (y : G)⁻¹ * x * y := hwv
    have : (y * (⟨x, hx⟩ : ↥H))⁻¹ * ((⟨x, hx⟩ : ↥H) * y) = w := by
      apply Subtype.ext
      rw [hwv']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]
    rw [this]
    exact hw

theorem conj_mem_zStarOf_conjSub' (H : Subgroup G) (c : G) {x : G} (hx : x ∈ zStarOf H) :
    c * x * c⁻¹ ∈ zStarOf (conjSub c H) := by
  rw [mem_zStarOf_iff'] at hx ⊢
  obtain ⟨hxH, hxc⟩ := hx
  refine ⟨mem_conjSub_iff.mpr (by simpa [mul_assoc] using hxH), fun y hy => ?_⟩
  have hy' : c⁻¹ * y * c ∈ H := mem_conjSub_iff.mp hy
  have h1 := hxc (c⁻¹ * y * c) hy'
  have h2 : oddCoreOf (conjSub c H) = conjSub c (oddCoreOf H) :=
    Thompson.oddCoreOf_conjSub_eq c H
  rw [h2]
  refine mem_conjSub_iff.mpr ?_
  have e : c⁻¹ * ((c * x * c⁻¹)⁻¹ * y⁻¹ * (c * x * c⁻¹) * y) * c =
      x⁻¹ * (c⁻¹ * y * c)⁻¹ * x * (c⁻¹ * y * c) := by group
  rw [e]
  exact h1

theorem centralizer_conj' (c a : G) :
    Subgroup.centralizer ({c * a * c⁻¹} : Set G) =
      conjSub c (Subgroup.centralizer ({a} : Set G)) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, mem_conjSub_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c⁻¹ * x * c * a = c⁻¹ * (x * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * x) * c := by rw [h]
      _ = a * (c⁻¹ * x * c) := by group
  · intro h
    calc x * (c * a * c⁻¹) = c * ((c⁻¹ * x * c) * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
      _ = (c * a * c⁻¹) * x := by group

theorem zStar_conj_iff {z a c : G} (hcz : c * z * c⁻¹ = z) :
    z ∈ zStarOf (Subgroup.centralizer ({c * a * c⁻¹} : Set G)) ↔
      z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  constructor
  · intro h
    have h1 := conj_mem_zStarOf_conjSub' (Subgroup.centralizer ({c * a * c⁻¹} : Set G)) c⁻¹ h
    have hcz' : c⁻¹ * z * c⁻¹⁻¹ = z := by
      calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ := by rw [hcz]
        _ = z := by group
    rw [hcz', centralizer_conj' c a, ← conjSub_mul] at h1
    simpa using h1
  · intro h
    have h1 := conj_mem_zStarOf_conjSub' (Subgroup.centralizer ({a} : Set G)) c h
    rw [hcz, ← centralizer_conj' c a] at h1
    exact h1

end ZStar

section Four

variable {G : Type} [Group G]

theorem fourGroup {a z : G} (ha2 : a * a = 1) (hz2 : z * z = 1) (haz : a * z = z * a)
    (ha1 : a ≠ 1) (hz1 : z ≠ 1) (haz' : a ≠ z) :
    IsElemAbelian2 (Subgroup.closure ({a, z} : Set G)) 2 ∧
      ∀ b ∈ Subgroup.closure ({a, z} : Set G), b = 1 ∨ b = a ∨ b = z ∨ b = a * z := by
  classical
  have hmem : ∀ b ∈ Subgroup.closure ({a, z} : Set G), b = 1 ∨ b = a ∨ b = z ∨ b = a * z :=
    fun b hb => C25Y.mem_closure_pair ha2 hz2 haz hb
  refine ⟨⟨?_, ?_⟩, hmem⟩
  · have hset : ((Subgroup.closure ({a, z} : Set G) : Subgroup G) : Set G) =
        (({1, a, z, a * z} : Finset G) : Set G) := by
      ext b
      constructor
      · intro hb
        rcases hmem b hb with rfl | rfl | rfl | rfl <;> simp
      · intro hb
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hb
        have ha : a ∈ Subgroup.closure ({a, z} : Set G) := Subgroup.subset_closure (by simp)
        have hz : z ∈ Subgroup.closure ({a, z} : Set G) := Subgroup.subset_closure (by simp)
        rcases hb with rfl | rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact ha
        · exact hz
        · exact Subgroup.mul_mem _ ha hz
    have h1 : Nat.card ↥(Subgroup.closure ({a, z} : Set G)) =
        Set.ncard ((Subgroup.closure ({a, z} : Set G) : Subgroup G) : Set G) :=
      Nat.card_coe_set_eq _
    rw [h1, hset, Set.ncard_coe_finset]
    have n1 : (1 : G) ∉ ({a, z, a * z} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => ha1 h.symm, fun h => hz1 h.symm, fun h => ?_⟩
      apply haz'
      have : a * z = 1 := h.symm
      calc a = a * (z * z) := by rw [hz2, mul_one]
        _ = (a * z) * z := by rw [mul_assoc]
        _ = z := by rw [this, one_mul]
    have n2 : a ∉ ({z, a * z} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨haz', fun h => hz1 ?_⟩
      have : a * z = a * 1 := by rw [mul_one]; exact h.symm
      exact mul_left_cancel this
    have n3 : z ∉ ({a * z} : Finset G) := by
      simp only [Finset.mem_singleton]
      intro h
      apply ha1
      have : 1 * z = a * z := by rw [one_mul]; exact h
      exact (mul_right_cancel this).symm
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_singleton]
    norm_num
  · intro b hb
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rcases hmem b hb with rfl | rfl | rfl | rfl
    · simp
    · exact ha2
    · exact hz2
    · calc a * z * (a * z) = a * (z * a) * z := by group
        _ = a * (a * z) * z := by rw [haz]
        _ = (a * a) * (z * z) := by group
        _ = 1 := by rw [ha2, hz2, one_mul]

end Four

section Pure

variable {G : Type} [Group G]

theorem case_pure {a t' v z : G} (ha2 : a * a = 1) (hz2 : z * z = 1)
    (hzt : z * t' = t' * z) (hzv : z * v = v * z) (hv2 : v * v = z)
    (hav : a * v = v * a) {q : G} (hq : q = v ∨ q = v * z) (h : a * t' * a = q * t' * v) :
    z * t' = (v⁻¹ * a) * t' * (v⁻¹ * a)⁻¹ ∨
      ((v⁻¹ * a) * t' * (v⁻¹ * a)⁻¹ = t' ∧ (v⁻¹ * a) * (v⁻¹ * a) = z) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hkey : (v⁻¹ * a) * t' * (v⁻¹ * a)⁻¹ = v⁻¹ * (q * t' * v) * v := by
    calc (v⁻¹ * a) * t' * (v⁻¹ * a)⁻¹ = v⁻¹ * (a * t' * a⁻¹) * v := by group
      _ = v⁻¹ * (a * t' * a) * v := by rw [hai]
      _ = v⁻¹ * (q * t' * v) * v := by rw [h]
  rcases hq with rfl | rfl
  · left
    rw [hkey]
    calc z * t' = t' * z := hzt
      _ = t' * (q * q) := by rw [hv2]
      _ = q⁻¹ * (q * t' * q) * q := by group
  · right
    refine ⟨?_, ?_⟩
    · rw [hkey]
      calc v⁻¹ * (v * z * t' * v) * v = z * t' * (v * v) := by
            calc v⁻¹ * (v * z * t' * v) * v = (z * t') * (v * v) := by group
              _ = z * t' * (v * v) := rfl
        _ = z * t' * z := by rw [hv2]
        _ = t' * (z * z) := by rw [hzt]; group
        _ = t' := by rw [hz2, mul_one]
    · have hvi : a * v⁻¹ = v⁻¹ * a := by
        calc a * v⁻¹ = v⁻¹ * (v * a) * v⁻¹ := by group
          _ = v⁻¹ * (a * v) * v⁻¹ := by rw [hav]
          _ = v⁻¹ * a := by group
      calc (v⁻¹ * a) * (v⁻¹ * a) = v⁻¹ * (a * v⁻¹) * a := by group
        _ = v⁻¹ * (v⁻¹ * a) * a := by rw [hvi]
        _ = (v * v)⁻¹ * (a * a) := by group
        _ = z := by rw [hv2, ha2, mul_one]; exact inv_eq_of_mul_eq_one_right hz2

end Pure

end CFSG.ClassicalInvolution.Asc77.C25V
