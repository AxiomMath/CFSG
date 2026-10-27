module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Words
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G]

@[expose] noncomputable def e1M0 (Z : Subgroup G) [Z.Normal] (z : G) : Subgroup (G ⧸ Z) :=
  (Subgroup.centralizer {z}).map (QuotientGroup.mk' Z)

section Sigma

variable {Z : Subgroup G} [Z.Normal] {e z : G}

theorem e1M0_le_centralizer : e1M0 Z z ≤ Subgroup.centralizer {(z : G ⧸ Z)} := by
  intro s hs
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hs
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hg]

variable (he : e ∈ Subgroup.center G) (hZ : ∀ g, g ∈ Z ↔ g = 1 ∨ g = e)
include he hZ

omit [Z.Normal] he in
theorem mul_self_of_mem_iff : e * e = 1 := by
  rcases (hZ _).mp (Z.mul_mem ((hZ e).mpr (Or.inr rfl)) ((hZ e).mpr (Or.inr rfl))) with h | h
  · exact h
  · rw [mul_eq_left.mp h, mul_one]

omit hZ in
theorem mul_conj_centralElt (g w : G) : g * e * w * (g * e)⁻¹ = g * w * g⁻¹ := by
  rw [show g * e * w * (g * e)⁻¹ = g * (e * w) * e⁻¹ * g⁻¹ by group,
    ← Subgroup.mem_center_iff.mp he w, show g * (w * e) * e⁻¹ * g⁻¹ = g * w * g⁻¹ by group]

omit he in
theorem conj_eq_or_of_mk_mem_centralizer {g : G}
    (hg : (g : G ⧸ Z) ∈ Subgroup.centralizer {(z : G ⧸ Z)}) :
    g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * e := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have h : (z : G ⧸ Z) = ((g * z * g⁻¹ : G) : G ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hg,
      mul_inv_cancel_right]
  rcases (hZ _).mp (QuotientGroup.eq.mp h) with h1 | h1
  · exact Or.inl (inv_mul_eq_one.mp h1).symm
  · exact Or.inr (by rw [← h1]; group)

theorem mk_mem_e1M0_iff {g : G} : (g : G ⧸ Z) ∈ e1M0 Z z ↔ g * z * g⁻¹ = z := by
  constructor
  · intro hg
    obtain ⟨h, hh, hhg⟩ := Subgroup.mem_map.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hh
    have hc : h⁻¹ * g ∈ Z := QuotientGroup.eq.mp hhg
    have hhz : h * z * h⁻¹ = z := by rw [hh, mul_inv_cancel_right]
    rcases (hZ _).mp hc with h1 | h1
    · rw [← inv_mul_eq_one.mp h1]
      exact hhz
    · rw [show g = h * e by rw [← h1]; group, mul_conj_centralElt he]
      exact hhz
  · intro hg
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hg]

theorem conj_eq_mul_of_not_mem_e1M0 {g : G}
    (hg : (g : G ⧸ Z) ∈ Subgroup.centralizer {(z : G ⧸ Z)}) (hg' : (g : G ⧸ Z) ∉ e1M0 Z z) :
    g * z * g⁻¹ = z * e :=
  (conj_eq_or_of_mk_mem_centralizer hZ hg).resolve_left fun h =>
    hg' ((mk_mem_e1M0_iff he hZ).mpr h)

theorem mul_mem_e1M0_of_not_mem {s t : G ⧸ Z}
    (hs : s ∈ Subgroup.centralizer {(z : G ⧸ Z)}) (ht : t ∈ Subgroup.centralizer {(z : G ⧸ Z)})
    (hs' : s ∉ e1M0 Z z) (ht' : t ∉ e1M0 Z z) : s * t ∈ e1M0 Z z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective t
  rw [← QuotientGroup.mk_mul, mk_mem_e1M0_iff he hZ]
  have h1 := conj_eq_mul_of_not_mem_e1M0 he hZ hs hs'
  have h2 := conj_eq_mul_of_not_mem_e1M0 he hZ ht ht'
  calc g * h * z * (g * h)⁻¹ = g * (h * z * h⁻¹) * g⁻¹ := by group
    _ = g * z * g⁻¹ * e := by
        rw [h2, show g * (z * e) * g⁻¹ = g * z * (e * g⁻¹) by group,
          ← Subgroup.mem_center_iff.mp he g⁻¹, ← mul_assoc]
    _ = z := by rw [h1, mul_assoc, mul_self_of_mem_iff hZ, mul_one]

theorem mem_e1M0_of_pow_eq_one {s : G ⧸ Z} (hs : s ∈ Subgroup.centralizer {(z : G ⧸ Z)})
    {k : ℕ} (hk : Odd k) (hsk : s ^ k = 1) : s ∈ e1M0 Z z := by
  by_contra hs'
  obtain ⟨j, rfl⟩ := hk
  have h2 : (s * s) ^ j ∈ e1M0 Z z :=
    (e1M0 Z z).pow_mem (mul_mem_e1M0_of_not_mem he hZ hs hs hs' hs') j
  refine hs' ?_
  have hs1 : s = ((s * s) ^ j)⁻¹ * s ^ (2 * j + 1) := by
    rw [pow_succ, pow_mul, pow_two]
    group
  rw [hs1, hsk, mul_one]
  exact (e1M0 Z z).inv_mem h2

theorem relIndex_e1M0_of_le {A : Subgroup (G ⧸ Z)}
    (hA : A ≤ Subgroup.centralizer {(z : G ⧸ Z)}) {a : G ⧸ Z} (ha : a ∈ A)
    (ha' : a ∉ e1M0 Z z) : (e1M0 Z z).relIndex A = 2 := by
  refine Subgroup.relIndex_eq_two_iff.mpr ⟨a, ha, fun b hb => ?_⟩
  by_cases hbM : b ∈ e1M0 Z z
  · refine Or.inr ⟨hbM, fun h => ha' ?_⟩
    rw [show a = b⁻¹ * (b * a) by group]
    exact (e1M0 Z z).mul_mem ((e1M0 Z z).inv_mem hbM) h
  · exact Or.inl ⟨mul_mem_e1M0_of_not_mem he hZ (hA hb) (hA ha) hbM ha', hbM⟩

end Sigma

open scoped Classical in
@[expose] noncomputable def e1Sigma (Z : Subgroup G) [Z.Normal] (z : G) {e : G}
    (he : e ∈ Subgroup.center G) (hZ : ∀ g, g ∈ Z ↔ g = 1 ∨ g = e) :
    Subgroup.centralizer {(z : G ⧸ Z)} →* ℤˣ where
  toFun s := if (s : G ⧸ Z) ∈ e1M0 Z z then 1 else -1
  map_one' := by simp [(e1M0 Z z).one_mem]
  map_mul' s t := by
    by_cases hs : (s : G ⧸ Z) ∈ e1M0 Z z <;> by_cases ht : (t : G ⧸ Z) ∈ e1M0 Z z
    · simp [hs, ht, (e1M0 Z z).mul_mem hs ht]
    · have hst : (s : G ⧸ Z) * t ∉ e1M0 Z z := fun h =>
        ht (by simpa using (e1M0 Z z).mul_mem ((e1M0 Z z).inv_mem hs) h)
      simp [hs, ht, hst]
    · have hst : (s : G ⧸ Z) * t ∉ e1M0 Z z := fun h =>
        hs (by simpa using (e1M0 Z z).mul_mem h ((e1M0 Z z).inv_mem ht))
      simp [hs, ht, hst]
    · simp [hs, ht, mul_mem_e1M0_of_not_mem he hZ s.2 t.2 hs ht]

section SigmaLemmas

variable {Z : Subgroup G} [Z.Normal] {e z : G} (he : e ∈ Subgroup.center G)
  (hZ : ∀ g, g ∈ Z ↔ g = 1 ∨ g = e)

open scoped Classical in
theorem e1Sigma_apply (s : Subgroup.centralizer {(z : G ⧸ Z)}) :
    e1Sigma Z z he hZ s = if (s : G ⧸ Z) ∈ e1M0 Z z then 1 else -1 :=
  rfl

theorem e1Sigma_eq_one_iff (s : Subgroup.centralizer {(z : G ⧸ Z)}) :
    e1Sigma Z z he hZ s = 1 ↔ (s : G ⧸ Z) ∈ e1M0 Z z := by
  rw [e1Sigma_apply]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

theorem ker_e1Sigma :
    (e1Sigma Z z he hZ).ker = (e1M0 Z z).subgroupOf (Subgroup.centralizer {(z : G ⧸ Z)}) := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, e1Sigma_eq_one_iff]

include he hZ in
theorem normal_e1M0 :
    ((e1M0 Z z).subgroupOf (Subgroup.centralizer {(z : G ⧸ Z)})).Normal := by
  rw [← ker_e1Sigma he hZ]
  exact (e1Sigma Z z he hZ).normal_ker

end SigmaLemmas

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
