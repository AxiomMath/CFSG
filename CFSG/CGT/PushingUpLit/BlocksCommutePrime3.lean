module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjSub (g : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub_iff {g : G} {X : Subgroup G} {z : G} : z ∈ conjSub g X ↔ g⁻¹ * z * g ∈ X := by
  unfold conjSub
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_conjSub {g : G} {X : Subgroup G} {z : G} (hz : z ∈ X) :
    g * z * g⁻¹ ∈ conjSub g X := by
  rw [mem_conjSub_iff]
  simpa [mul_assoc] using hz

theorem conjSub_one (X : Subgroup G) : conjSub 1 X = X := by
  ext z
  rw [mem_conjSub_iff]
  simp

theorem mem_normalizer_of_conjSub_eq {g₁ g₂ : G} {X : Subgroup G}
    (h : conjSub g₁ X = conjSub g₂ X) : g₂⁻¹ * g₁ ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have e1 : ∀ z, z ∈ X → g₁ * z * g₁⁻¹ ∈ conjSub g₂ X := fun z hz => h ▸ conj_mem_conjSub hz
  have e2 : ∀ z, z ∈ X → g₂ * z * g₂⁻¹ ∈ conjSub g₁ X := fun z hz => h.symm ▸ conj_mem_conjSub hz
  constructor
  · intro hz
    have := e1 z hz
    rw [mem_conjSub_iff] at this
    simpa [mul_assoc] using this
  · intro hz
    have := e2 _ hz
    rw [mem_conjSub_iff] at this
    simpa [mul_assoc] using this

theorem mem_of_pow_mem_prime {y : G} {p : ℕ} (hp : p.Prime) (hyo : orderOf y = p) {m : ℕ}
    (hm : 0 < m) (hmp : m < p) {S : Subgroup G} (h : y ^ m ∈ S) : y ∈ S := by
  have hcop : Nat.Coprime m (orderOf y) := by
    rw [hyo]
    exact (hp.coprime_iff_not_dvd.2 fun hd => absurd (Nat.le_of_dvd hm hd) (not_le.2 hmp)).symm
  exact (Subgroup.zpowers_le.2 h) (CFSG.Quasithin.A4.mem_zpowers_pow_of_coprime hcop)

theorem conjSub_pow_ne {X : Subgroup G} {y : G} {p : ℕ} (hp : p.Prime) (hyo : orderOf y = p)
    (hyn : y ∉ Subgroup.normalizer (X : Set G)) {i j : ℕ} (hij : i % p ≠ j % p) :
    conjSub (y ^ i) X ≠ conjSub (y ^ j) X := by
  intro h
  have hmem := mem_normalizer_of_conjSub_eq h
  have hi : y ^ i = y ^ (i % p) := by rw [← hyo, pow_mod_orderOf]
  have hj : y ^ j = y ^ (j % p) := by rw [← hyo, pow_mod_orderOf]
  rw [hi, hj] at hmem
  have hip : i % p < p := Nat.mod_lt _ hp.pos
  have hjp : j % p < p := Nat.mod_lt _ hp.pos
  have key : ∀ a b : ℕ, a < b → b < p → (y ^ b)⁻¹ * y ^ a ∈ Subgroup.normalizer (X : Set G) →
      y ∈ Subgroup.normalizer (X : Set G) := by
    intro a b hab hbp hmem
    obtain ⟨m, hm, hm0⟩ : ∃ m, b = a + m ∧ 0 < m := ⟨b - a, by omega, by omega⟩
    subst hm
    have e : (y ^ (a + m))⁻¹ * y ^ a = (y ^ m)⁻¹ := by
      rw [pow_add]
      group
    rw [e] at hmem
    exact mem_of_pow_mem_prime hp hyo hm0 (by omega) (inv_mem_iff.1 hmem)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hyn (key _ _ hlt hjp hmem)
  · refine hyn (key _ _ hgt hip ?_)
    have := inv_mem hmem
    simpa using this

theorem orbit_commute {X Y : Subgroup G} {p : ℕ} (hp : p.Prime) {y : G} (hy : y ∈ Y)
    (hyo : orderOf y = p) (hyn : y ∉ Subgroup.normalizer (X : Set G))
    (hcomm : ∀ g₁ ∈ Y, ∀ g₂ ∈ Y, conjSub g₁ X ≠ conjSub g₂ X →
      ⁅conjSub g₁ X, conjSub g₂ X⁆ = ⊥) {i j : ℕ} (hij : i % p ≠ j % p) :
    ∀ a ∈ conjSub (y ^ i) X, ∀ b ∈ conjSub (y ^ j) X, a * b = b * a := by
  have h := hcomm (y ^ i) (pow_mem hy i) (y ^ j) (pow_mem hy j) (conjSub_pow_ne hp hyo hyn hij)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.1 (h ha) b hb).symm

end CFSG.CGT.PushingUpLit
