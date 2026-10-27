module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6SylowProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6KleinModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup A6Model

private theorem le_pRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p) {H E : Subgroup G}
    {k : ℕ} (hE : E ≤ H) (hEa : IsElemAbelian p E) (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p H := CFSG.SectionRank.le_pRank hp hE hEa hk

private theorem klein_identities {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : x * (x * y) = y ∧ y * x = x * y ∧ y * (x * y) = x ∧
      x * y * x = y ∧ x * y * y = x ∧ x * y * (x * y) = 1 := by
  have e4 : x * y * x = y := by rw [mul_assoc, ← hxy, ← mul_assoc, hx, one_mul]
  exact ⟨by rw [← mul_assoc, hx, one_mul], hxy.symm,
    by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one], e4, by rw [mul_assoc, hy, mul_one],
    by rw [← mul_assoc, e4, hy]⟩

private def klein {G : Type*} [Group G] (x y : G) (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : Subgroup G where
  carrier := {1, x, y, x * y}
  mul_mem' := by
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := klein_identities hx hy hxy
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
      simp [hx, hy, e1, e2, e3, e4, e5, e6]
  one_mem' := by simp
  inv_mem' := by
    obtain ⟨-, e2, -⟩ := klein_identities hx hy hxy
    have ix : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have iy : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with ha | ha | ha | ha <;> rw [ha] <;> simp [ix, iy, mul_inv_rev, e2]

private theorem mem_klein {G : Type*} [Group G] {x y : G} {hx : x * x = 1} {hy : y * y = 1}
    {hxy : x * y = y * x} {g : G} :
    g ∈ klein x y hx hy hxy ↔ g = 1 ∨ g = x ∨ g = y ∨ g = x * y := Iff.rfl

private theorem klein_isPGroup {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : IsPGroup 2 (klein x y hx hy hxy) := by
  obtain ⟨-, -, -, -, -, e6⟩ := klein_identities hx hy hxy
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨g, hg⟩ := g
  rcases mem_klein.mp hg with h | h | h | h <;> subst h <;> simp [pow_two, hx, hy, e6]

private theorem klein_normalizer {G : Type} [Group G] {x y u : G} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y = y * x) (hux : u * x * u⁻¹ = y) (huy : u * y * u⁻¹ = x * y) :
    u ∈ normalizer ((klein x y hx hy hxy : Subgroup G) : Set G) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := klein_identities hx hy hxy
  have huxy : u * (x * y) * u⁻¹ = x := by
    calc u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by group
      _ = x := by rw [hux, huy, e3]
  have hix : u⁻¹ * x * u = x * y := by
    calc u⁻¹ * x * u = u⁻¹ * (u * (x * y) * u⁻¹) * u := by rw [huxy]
      _ = x * y := by group
  have hiy : u⁻¹ * y * u = x := by
    calc u⁻¹ * y * u = u⁻¹ * (u * x * u⁻¹) * u := by rw [hux]
      _ = x := by group
  have hixy : u⁻¹ * (x * y) * u = y := by
    calc u⁻¹ * (x * y) * u = (u⁻¹ * x * u) * (u⁻¹ * y * u) := by group
      _ = y := by rw [hix, hiy, e4]
  refine mem_normalizer_of_conj (fun t ht => ?_) (fun t ht => ?_)
  · rcases mem_klein.mp ht with h | h | h | h <;> subst h <;> simp only [mem_klein]
    · simp
    · exact Or.inr (Or.inr (Or.inl hux))
    · exact Or.inr (Or.inr (Or.inr huy))
    · exact Or.inr (Or.inl huxy)
  · rcases mem_klein.mp ht with h | h | h | h <;> subst h <;> simp only [mem_klein]
    · simp
    · exact Or.inr (Or.inr (Or.inr hix))
    · exact Or.inr (Or.inl hiy)
    · exact Or.inr (Or.inr (Or.inl hixy))

private theorem top_le_of_klein {K : Type} [Group K] [Finite K] {T : Subgroup K}
    (hrank : 1 ≤ CFSG.Open.pRank 3 T)
    (hmax : ∀ Y : Subgroup K, normalizer (T : Set K) ≤ Y → Y = normalizer (T : Set K) ∨ Y = ⊤)
    {u x y : K} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hux : u * x * u⁻¹ = y) (huy : u * y * u⁻¹ = x * y) (hxN : x ∉ normalizer (T : Set K)) :
    ⊤ ≤ rankThreeGamma 1 3 T ⊔
      sSup {V : Subgroup K | IsPGroup 2 V ∧ u ∈ normalizer (V : Set K)} := by
  have hV : (klein x y hx hy hxy : Subgroup K) ∈
      {V : Subgroup K | IsPGroup 2 V ∧ u ∈ normalizer (V : Set K)} :=
    ⟨klein_isPGroup hx hy hxy, klein_normalizer hx hy hxy hux huy⟩
  have hxV : x ∈ (klein x y hx hy hxy : Subgroup K) := mem_klein.mpr (Or.inr (Or.inl rfl))
  have hN : normalizer (T : Set K) ≤ rankThreeGamma 1 3 T :=
    le_sSup ⟨T, le_rfl, hrank, rfl⟩
  rcases hmax _ (hN.trans le_sup_left) with h | h
  · exact absurd (h ▸ Subgroup.mem_sup_right (le_sSup hV hxV)) hxN
  · exact h.ge

theorem a6TwoSignalizer_proved : KFactA6TwoSignalizer := by
  intro K _ _ hK T u huT hu3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hel, hcard, hmax⟩ := a6SylowData_proved K hK T
  obtain ⟨Φ, hΦ⟩ := exists_equiv_of_sylow hK T
  have hrank : 1 ≤ CFSG.Open.pRank 3 (T : Subgroup K) :=
    (show 1 ≤ 2 by norm_num).trans (le_pRank (by norm_num) le_rfl hel hcard)
  have hu' : u ∈ uHom.range.map Φ.toMonoidHom := hΦ ▸ huT
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hu'
  obtain ⟨a, rfl⟩ := mem_range_iff.mp hz
  have ha : a ≠ 0 := by
    rintro rfl
    have h1 : Φ.toMonoidHom (ut 0) = 1 := by rw [ut_zero, map_one]
    rw [h1, orderOf_one] at hu3
    exact absurd hu3 (by norm_num)
  obtain ⟨x, y, hx, hy, hxy, hux, huy, hxN⟩ := klein_model a ha
  refine top_le_of_klein (x := Φ x) (y := Φ y) hrank hmax ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, hx, map_one]
  · rw [← map_mul, hy, map_one]
  · rw [← map_mul, ← map_mul, hxy]
  · change Φ (ut a) * Φ x * (Φ (ut a))⁻¹ = Φ y
    rw [← map_inv, ← map_mul, ← map_mul, hux]
  · change Φ (ut a) * Φ y * (Φ (ut a))⁻¹ = Φ x * Φ y
    rw [← map_inv, ← map_mul, ← map_mul, huy, map_mul]
  · intro hn
    apply hxN
    rw [hΦ, ← Subgroup.map_equiv_normalizer_eq] at hn
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hn
    rwa [← Φ.injective hwx]

end CFSG.LocalAnalysis.RankThreeTheoremC
