module

public import CFSG.GH74.GLS.Stage4.T2NegRU3Basic
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk41RConj

public section

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.Ivk41R CFSG.Assembly.LowTwoRank
  CFSG.RankThree.Classical Matrix

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk41RU3

theorem natCard_centralizer_singleton_congr {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    (z : G) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card (Subgroup.centralizer ({φ z} : Set G')) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨φ x, ?_⟩
      invFun := fun y => ⟨φ.symm y, ?_⟩
      left_inv := fun x => Subtype.ext (φ.symm_apply_apply _)
      right_inv := fun y => Subtype.ext (φ.apply_symm_apply _) }
  · have := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, this]
  · have := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact this

theorem exists_conj_to_base {G : Type*} [Group G] [Finite G] {p n m : ℕ} [Fact p.Prime] {t : G}
    (hC : Nat.card (Subgroup.centralizer ({t} : Set G)) = p ^ n * m) (hm : ¬ p ∣ m)
    {X₀ : Subgroup G} (hX₀t : X₀ ≤ Subgroup.centralizer ({t} : Set G))
    (hX₀c : Nat.card X₀ = p ^ n) {z : G} (hz : ∃ a : G, a * t * a⁻¹ = z) {X : Subgroup G}
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G)) (hXc : Nat.card X = p ^ n) :
    ∃ g : G, g * z * g⁻¹ = t ∧ X.map (MulAut.conj g).toMonoidHom = X₀ := by
  obtain ⟨a, rfl⟩ := hz
  have hX₁C : X.map (MulAut.conj a⁻¹).toMonoidHom ≤ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxz := Subgroup.mem_centralizer_singleton_iff.mp (hXz hx)
    show a⁻¹ * x * a⁻¹⁻¹ * t = t * (a⁻¹ * x * a⁻¹⁻¹)
    calc a⁻¹ * x * a⁻¹⁻¹ * t = a⁻¹ * (x * (a * t * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * t * a⁻¹) * x) * a := by rw [hxz]
      _ = t * (a⁻¹ * x * a⁻¹⁻¹) := by group
  have hX₁c : Nat.card (X.map (MulAut.conj a⁻¹).toMonoidHom) = p ^ n := by
    rw [Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective]
    exact hXc
  obtain ⟨k, hkC, hk⟩ := exists_conj_subgroup_of_le (Subgroup.centralizer ({t} : Set G)) hC hm
    hX₁C hX₀t hX₁c hX₀c
  have hkt : k * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp hkC
  refine ⟨k * a⁻¹, ?_, ?_⟩
  · calc k * a⁻¹ * (a * t * a⁻¹) * (k * a⁻¹)⁻¹ = k * t * k⁻¹ := by group
      _ = t := by rw [hkt]; group
  · have : (MulAut.conj (k * a⁻¹)).toMonoidHom =
        (MulAut.conj k).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, ← Subgroup.map_map]
    exact hk

theorem natCard_GU2Stated {q : ℕ} {F : Type} [Field F] [Finite F] (hq : Nat.card F = q ^ 2)
    (hq1 : 1 ≤ q) : Nat.card (GU2Stated q F) = q * ((q + 1) * (q ^ 2 - 1)) := by
  have := Fintype.ofFinite F
  have hF : Fintype.card F = q ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hq
  have hGU : GU2Stated q F = CFSG.Quasithin.StatedGU 2 q F := rfl
  have h := CFSG.GroupTheory.WeirSylow.natCard_statedGU_cast hF (n := 2) (by norm_num)
  rw [hGU]
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have : ((Nat.card (CFSG.Quasithin.StatedGU 2 q F) : ℕ) : ℤ) =
      ((q * ((q + 1) * (q ^ 2 - 1)) : ℕ) : ℤ) := by
    rw [h]
    push_cast [Nat.cast_sub hq2]
    simp [show Finset.Icc 1 2 = {1, 2} from by decide]
    ring
  exact_mod_cast this

theorem range_blkU_eq {p n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p n F) (hp2 : p ≠ 2) :
    (Lemma41aU3.blkU h).range =
      Subgroup.centralizer ({unitaryInvT h} : Set ↥(StatedSU 3 (p ^ n) F)) := by
  ext y
  constructor
  · rintro ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Lemma41aU3.blkU_commute h A
  · intro hy
    exact Lemma41aU3.mem_range_blkU_of_commute h hp2 (Subgroup.mem_centralizer_singleton_iff.mp hy)

theorem card_centralizer_unitaryInvT {p n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p n F)
    (hp2 : p ≠ 2) :
    ∃ m : ℕ, Nat.card (Subgroup.centralizer ({unitaryInvT h} : Set ↥(StatedSU 3 (p ^ n) F))) =
      p ^ n * m ∧ ¬ p ∣ m := by
  have := h.finite
  have hq1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ h.prime.pos
  have hF : Nat.card F = (p ^ n) ^ 2 := by rw [h.card, pow_mul']
  refine ⟨(p ^ n + 1) * ((p ^ n) ^ 2 - 1), ?_, ?_⟩
  · rw [← range_blkU_eq h hp2]
    exact (Nat.card_range_of_injective (Lemma41aU3.blkU_injective h)).trans
      (natCard_GU2Stated hF hq1)
  · have hpq : p ∣ p ^ n := dvd_pow_self p (by have := h.one_le; omega)
    intro hdvd
    rcases (Nat.Prime.dvd_mul h.prime).1 hdvd with h1 | h1
    · have : p ∣ 1 := (Nat.dvd_add_right hpq).mp h1
      exact h.prime.one_lt.ne' (Nat.dvd_one.mp this)
    · exact not_dvd_pow_sub_one h.prime hpq hq1 (j := 2) (by norm_num) h1

theorem rconjU3 {p n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p n K) :
    p ≠ 2 → ∀ (z : hypSU h 1 1) (X : Subgroup (hypSU h 1 1)), orderOf z = 2 →
      X ≤ Subgroup.centralizer ({z} : Set (hypSU h 1 1)) → Nat.card X = p ^ n →
        ∃ g : hypSU h 1 1, g * z * g⁻¹ = tzU h ∧ X.map (MulAut.conj g).toMonoidHom = X0U h := by
  intro hp2 z X hz hXz hXc
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite (hypSU h 1 1) := finite_hypSU h
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let φ : hypSU h 1 1 ≃* unitarySU p n K 3 := hypTransport h hR
  obtain ⟨m, hCm, hpm⟩ := card_centralizer_unitaryInvT h hp2
  have hφz : orderOf (φ z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  have hφtz : orderOf (φ (tzU h)) = 2 := by rw [MulEquiv.orderOf_eq]; exact orderOf_tzU hp2 h
  have hc1 := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 hφz)
  have hc2 := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 hφtz)
  obtain ⟨c₁, hc₁⟩ := hc1
  obtain ⟨c₂, hc₂⟩ := hc2
  have hconj : ∃ a : hypSU h 1 1, a * tzU h * a⁻¹ = z := by
    refine ⟨φ.symm (c₁ * c₂⁻¹), ?_⟩
    apply φ.injective
    rw [map_mul, map_mul, map_inv, φ.apply_symm_apply, ← hc₂, ← hc₁]
    group
  have hC : Nat.card (Subgroup.centralizer ({tzU h} : Set (hypSU h 1 1))) = p ^ n * m := by
    rw [natCard_centralizer_singleton_congr φ (tzU h), ← hc₂, ← hCm,
      natCard_centralizer_singleton_congr (MulAut.conj c₂) (unitaryInvT h), MulAut.conj_apply]
  obtain ⟨g, hg1, hg2⟩ := exists_conj_to_base hC hpm X0U_le_centralizer_tz (card_X0U h) hconj hXz hXc
  exact ⟨g, hg1, hg2⟩

end CFSG.GH74.GLS.IVK.Proofs2.Ivk41RU3
