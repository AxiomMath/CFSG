module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockResidues
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ClassCoefficients
public import CFSG.CharacterTheory.Blocks.VirtualCharacterRing

public section

namespace CFSG.PSL2Table

open CFSG CFSG.BrauerThirdMainTheorem.Helpers

variable (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)

section Arithmetic

include hm

theorem odd_not_mem (h2 : (2 : BlocksAlgInt) ∈ m) {n : ℤ} (hn : Odd n) :
    (n : BlocksAlgInt) ∉ m := by
  intro h
  obtain ⟨k, rfl⟩ := hn
  have h1 : ((2 * k + 1 : ℤ) : BlocksAlgInt) - 2 * (k : BlocksAlgInt) = 1 := by
    push_cast
    ring
  exact one_not_mem m hm (h1 ▸ m.sub_mem h (m.mul_mem_right _ h2))

theorem intCast_mem_localRing (n : ℤ) : (n : ℂ) ∈ BlocksLocalRing m := by
  simpa using localRing_of_algInt m hm (n : BlocksAlgInt)

theorem inv_odd_mem_localRing (h2 : (2 : BlocksAlgInt) ∈ m) {n : ℤ} (hn : Odd n) :
    ((n : ℂ))⁻¹ ∈ BlocksLocalRing m :=
  ⟨1, n, odd_not_mem m hm h2 hn, by simp⟩

theorem integral_mem_localRing {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ BlocksLocalRing m :=
  localRing_of_algInt m hm ⟨x, (mem_integralClosure_iff ℤ ℂ).mpr hx⟩

theorem two_mem_localMaxIdeal (h2 : (2 : BlocksAlgInt) ∈ m) : (2 : ℂ) ∈ BlocksLocalMaxIdeal m := by
  have h := localMaxIdeal_of_mem m hm h2
  have h2' : ((2 : BlocksAlgInt) : ℂ) = 2 := Complex.ext rfl rfl
  rwa [h2'] at h

theorem mem_localMaxIdeal_of_eq_two_mul (h2 : (2 : BlocksAlgInt) ∈ m) {x y : ℂ}
    (hy : y ∈ BlocksLocalRing m) (hxy : x = 2 * y) : x ∈ BlocksLocalMaxIdeal m := by
  rw [hxy]
  exact localMaxIdeal_mul_localRing m hm (two_mem_localMaxIdeal m hm h2) hy

theorem div_odd_mem_localRing (h2 : (2 : BlocksAlgInt) ∈ m) {a : ℂ} (ha : a ∈ BlocksLocalRing m)
    {n : ℤ} (hn : Odd n) : a / n ∈ BlocksLocalRing m := by
  rw [div_eq_mul_inv]
  exact localRing_mul m hm ha (inv_odd_mem_localRing m hm h2 hn)

theorem natCast_mem_localRing (n : ℕ) : (n : ℂ) ∈ BlocksLocalRing m := by
  simpa using intCast_mem_localRing m hm n

theorem intCast_div_sub_one_mem (h2 : (2 : BlocksAlgInt) ∈ m) {a b : ℤ} (ha : Odd a)
    (hb : Odd b) : (a : ℂ) / b - 1 ∈ BlocksLocalMaxIdeal m := by
  obtain ⟨c, hc⟩ := ha.sub_odd hb
  have hb0 : (b : ℂ) ≠ 0 := by
    have : b ≠ 0 := by
      rintro rfl
      exact Int.not_even_iff_odd.mpr hb ⟨0, rfl⟩
    exact_mod_cast this
  refine mem_localMaxIdeal_of_eq_two_mul m hm h2
    (div_odd_mem_localRing m hm h2 (intCast_mem_localRing m hm c) hb) ?_
  have hc' : (a : ℂ) - b = c + c := by exact_mod_cast hc
  field_simp
  linear_combination hc'

end Arithmetic

theorem admissible_of_finset {G : Type} [Group G] [Fintype G] {A : Finset (G → ℂ)}
    (hA : ∀ χ ∈ A, χ ∈ BlocksIrr G)
    (hcoeff : ∀ g : G, (∑ χ ∈ A, χ 1 * χ g) / (Nat.card G : ℂ) ∈ BlocksLocalRing m) :
    BlocksAdmissible m G (A : Set (G → ℂ)) := by
  refine ⟨fun χ hχ => hA χ hχ, fun g => ?_⟩
  unfold BlocksIdempotentCoeff
  rw [finsum_mem_coe_finset]
  convert hcoeff g⁻¹ using 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  ring

theorem blockOf_subset_of_admissible' {G : Type} [Group G] {A : Set (G → ℂ)}
    (hA : BlocksAdmissible m G A) {χ : G → ℂ} (hχ : χ ∈ A) : BlocksBlockOf m G χ ⊆ A :=
  fun _ hψ => (hψ.2 A hA).mp hχ

open scoped Classical in
theorem sum_eq_sum_conjClasses {G : Type} [Group G] [Fintype G] (F : G → ℂ)
    (hF : ∀ g h : G, F (h * g * h⁻¹) = F g) :
    ∑ g, F g = ∑ c : ConjClasses G, (Nat.card c.carrier : ℂ) * F c.exists_rep.choose := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := ConjClasses.mk) (f := F)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hrep : ConjClasses.mk c.exists_rep.choose = c := c.exists_rep.choose_spec
  have hconst : ∀ g ∈ Finset.univ.filter (fun g : G => ConjClasses.mk g = c),
      F g = F c.exists_rep.choose := by
    intro g hg
    rw [Finset.mem_filter] at hg
    have hconj : IsConj g c.exists_rep.choose := by
      rw [← ConjClasses.mk_eq_mk_iff_isConj, hg.2, hrep]
    obtain ⟨h, hh⟩ := isConj_iff.mp hconj
    rw [← hh, hF]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun g : G => ConjClasses.mk g = c)).card =
      Nat.card c.carrier := by
    rw [Nat.card_eq_card_toFinset]
    congr 1
    ext g
    simp [ConjClasses.mem_carrier_iff_mk_eq]
  rw [hcard]

theorem mem_blockOf_of_pointwise (hm : m.IsMaximal) {G : Type} [Group G] [Fintype G]
    {χ ψ : G → ℂ}
    (hχ : χ ∈ BlocksIrr G) (hψ : ψ ∈ BlocksIrr G)
    (h : ∀ g : G, (Nat.card (ConjClasses.mk g).carrier : ℂ) * (ψ g / ψ 1 - χ g / χ 1) ∈
      BlocksLocalMaxIdeal m) :
    ψ ∈ BlocksBlockOf m G χ := by
  apply mem_blockOf_of_centralChar_congr m hm G hχ hψ
  intro z hz
  have hχc := blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)
  have hψc := blocksVChar_isClassFunction (AddSubgroup.subset_closure hψ)
  have hdiff : BlocksCentralChar ψ z - BlocksCentralChar χ z =
      ∑ g, z g * (ψ g / ψ 1 - χ g / χ 1) := by
    unfold BlocksCentralChar
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_div, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    ring
  rw [hdiff, sum_eq_sum_conjClasses _ (fun g k => by rw [hz.2 g k, hψc g k, hχc g k])]
  apply localMaxIdeal_sum m hm
  intro c _
  have hrep : ConjClasses.mk c.exists_rep.choose = c := c.exists_rep.choose_spec
  have hterm := h c.exists_rep.choose
  rw [hrep] at hterm
  have : (Nat.card c.carrier : ℂ) * (z c.exists_rep.choose *
      (ψ c.exists_rep.choose / ψ 1 - χ c.exists_rep.choose / χ 1)) =
      ((Nat.card c.carrier : ℂ) *
        (ψ c.exists_rep.choose / ψ 1 - χ c.exists_rep.choose / χ 1)) * z c.exists_rep.choose := by
    ring
  rw [this]
  exact localMaxIdeal_mul_localRing m hm hterm (hz.1 _)

theorem card_carrier_mul_card_centralizer {G : Type} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier * Nat.card (Subgroup.centralizer {g}) = Nat.card G := by
  rw [← ConjAct.orbit_eq_carrier_conjClasses, Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

theorem card_carrier_conj {G : Type} [Group G] (g h : G) :
    Nat.card (ConjClasses.mk (h * g * h⁻¹)).carrier = Nat.card (ConjClasses.mk g).carrier := by
  rw [ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h, rfl⟩).symm]

theorem card_carrier_one {G : Type} [Group G] : Nat.card (ConjClasses.mk (1 : G)).carrier = 1 := by
  have : (ConjClasses.mk (1 : G)).carrier = {1} := by
    ext x
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left,
      Set.mem_singleton_iff]
  rw [this, Nat.card_unique]

theorem even_card_carrier {G : Type} [Group G] [Finite G] (hG : 4 ∣ Nat.card G) {g : G}
    (hC : ¬ 4 ∣ Nat.card (Subgroup.centralizer {g})) :
    Even (Nat.card (ConjClasses.mk g).carrier) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  apply hC
  have hcop : Nat.Coprime 4 (Nat.card (ConjClasses.mk g).carrier) := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    norm_num at this
    exact this
  rw [← card_carrier_mul_card_centralizer g] at hG
  exact hcop.dvd_of_dvd_mul_left hG

open scoped Classical in
theorem card_filter_mk_eq {G : Type} [Group G] [Fintype G] (c : ConjClasses G) :
    (Finset.univ.filter (fun g : G => ConjClasses.mk g = c)).card = Nat.card c.carrier := by
  rw [Nat.card_eq_card_toFinset]
  congr 1
  ext g
  simp [ConjClasses.mem_carrier_iff_mk_eq]

open scoped Classical in
theorem centralChar_classCoefficients {G : Type} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : BlocksIsClassFunction χ) (g : G) :
    BlocksCentralChar χ (classCoefficients (ConjClasses.mk g)) =
      (Nat.card (ConjClasses.mk g).carrier : ℂ) * χ g / χ 1 := by
  unfold BlocksCentralChar
  rw [finsum_eq_sum_of_fintype]
  congr 1
  have hterm : ∀ h : G, classCoefficients (ConjClasses.mk g) h * χ h =
      if ConjClasses.mk h = ConjClasses.mk g then χ g else 0 := by
    intro h
    unfold classCoefficients
    split_ifs with hh
    · obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hh.symm)
      rw [one_mul, ← hc, hχ]
    · rw [zero_mul]
  rw [Finset.sum_congr rfl (fun h _ => hterm h), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, card_filter_mk_eq]

theorem card_carrier_mul_div_mem_localRing (hm : m.IsMaximal) {G : Type} [Group G] [Fintype G]
    {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (g : G) :
    (Nat.card (ConjClasses.mk g).carrier : ℂ) * χ g / χ 1 ∈ BlocksLocalRing m := by
  rw [← centralChar_classCoefficients
    (blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ))]
  exact centralChar_localRing m hm hχ (classCoefficients_central m hm _)

theorem blockOf_eq_singleton (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) {G : Type}
    [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {N : ℤ} (hN : Odd N)
    (hG : (Nat.card G : ℂ) = χ 1 * N) : BlocksBlockOf m G χ = {χ} := by
  classical
  have hadm : BlocksAdmissible m G (({χ} : Finset (G → ℂ)) : Set (G → ℂ)) := by
    refine admissible_of_finset m (fun θ hθ => by rw [Finset.mem_singleton.mp hθ]; exact hχ)
      (fun g => ?_)
    rw [Finset.sum_singleton, hG, mul_div_mul_left _ _ (irr_degree_ne_zero hχ)]
    exact div_odd_mem_localRing m hm h2 (integral_mem_localRing m hm (irr_integral hχ g)) hN
  rw [Finset.coe_singleton] at hadm
  apply Set.Subset.antisymm (blockOf_subset_of_admissible' m hadm rfl)
  rw [Set.singleton_subset_iff]
  exact mem_blockOf_self m hχ

theorem mem_blockOf_of_eq_or_eq_neg (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m)
    {G : Type} [Group G] [Fintype G] {χ ψ : G → ℂ} (hχ : χ ∈ BlocksIrr G)
    (hψ : ψ ∈ BlocksIrr G) (h1 : ψ 1 = χ 1) (h : ∀ g, ψ g = χ g ∨ ψ g = -χ g) :
    ψ ∈ BlocksBlockOf m G χ := by
  apply mem_blockOf_of_pointwise m hm hχ hψ
  intro g
  rw [h1]
  rcases h g with hg | hg
  · rw [hg, sub_self, mul_zero]
    exact localMaxIdeal_zero m hm
  · refine mem_localMaxIdeal_of_eq_two_mul m hm h2
      (localRing_neg m (card_carrier_mul_div_mem_localRing m hm hχ g)) ?_
    rw [hg]
    ring

theorem blockOf_eq_pair (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) {G : Type} [Group G]
    [Fintype G] {χ ψ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (hψ : ψ ∈ BlocksIrr G) (hne : χ ≠ ψ)
    (h1 : ψ 1 = χ 1) (h : ∀ g, ψ g = χ g ∨ ψ g = -χ g) {N : ℤ} (hN : Odd N)
    (hG : (Nat.card G : ℂ) = 2 * χ 1 * N) : BlocksBlockOf m G χ = {χ, ψ} := by
  classical
  have hadm : BlocksAdmissible m G (({χ, ψ} : Finset (G → ℂ)) : Set (G → ℂ)) := by
    refine admissible_of_finset m (fun θ hθ => ?_) (fun g => ?_)
    · rcases Finset.mem_insert.mp hθ with rfl | hθ
      · exact hχ
      · rw [Finset.mem_singleton.mp hθ]
        exact hψ
    · rw [Finset.sum_pair hne, h1]
      have hχ0 := irr_degree_ne_zero hχ
      rcases h g with hg | hg
      · rw [hg, hG]
        have : (χ 1 * χ g + χ 1 * χ g) / (2 * χ 1 * N) = χ g / N := by
          field_simp
          ring
        rw [this]
        exact div_odd_mem_localRing m hm h2 (integral_mem_localRing m hm (irr_integral hχ g)) hN
      · rw [hg, mul_neg, add_neg_cancel, zero_div]
        exact localRing_zero m hm
  rw [Finset.coe_pair] at hadm
  apply Set.Subset.antisymm (blockOf_subset_of_admissible' m hadm (Set.mem_insert _ _))
  rw [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨mem_blockOf_self m hχ, mem_blockOf_of_eq_or_eq_neg m hm h2 hχ hψ h1 h⟩

theorem mem_principalBlock_of_odd (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m)
    {G : Type} [Group G] [Fintype G] {ψ : G → ℂ} (hψ : ψ ∈ BlocksIrr G)
    (h : ∀ g, Even (Nat.card (ConjClasses.mk g).carrier) ∨ ∃ a : ℤ, Odd a ∧ ψ g = a) :
    ψ ∈ BlocksPrincipalBlock m G := by
  obtain ⟨b, hb, hb1⟩ : ∃ b : ℤ, Odd b ∧ ψ 1 = b := by
    rcases h 1 with h1 | h1
    · rw [card_carrier_one] at h1
      exact absurd h1 Nat.not_even_one
    · exact h1
  apply mem_blockOf_of_pointwise m hm (trivial_mem_irr G) hψ
  intro g
  simp only [div_one]
  rcases h g with ⟨k, hk⟩ | ⟨a, ha, hga⟩
  · refine mem_localMaxIdeal_of_eq_two_mul m hm h2 (y := (k : ℂ) * (ψ g / ψ 1 - 1)) ?_ ?_
    · refine localRing_mul m hm (natCast_mem_localRing m hm k)
        (localRing_sub m hm ?_ (localRing_one m hm))
      rw [hb1]
      exact div_odd_mem_localRing m hm h2 (integral_mem_localRing m hm (irr_integral hψ g)) hb
    · rw [hk]
      push_cast
      ring
  · rw [hga, hb1, mul_comm]
    exact localMaxIdeal_mul_localRing m hm (intCast_div_sub_one_mem m hm h2 ha hb)
      (natCast_mem_localRing m hm _)

end CFSG.PSL2Table
