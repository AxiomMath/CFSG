module

public import CFSG.CharacterTheory.Wreathed.OddKernelFixedSpaceCharacter
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityMultiplicities

public noncomputable section

namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

variable {G : Type} [Group G]

@[expose] def squareRootSection (y : G) : Set G :=
  {g | ∃ (h : ℤ) (v : G), Odd h ∧ Odd (orderOf v) ∧
    v ∈ Subgroup.centralizer ({y} : Set G) ∧ IsConj (y ^ h * v) g}

theorem commute_of_commute_odd_power {y v : G} {a : ℕ} (hy : y ^ 2 ^ a = 1)
    {h : ℤ} (hh : Odd h) (hv : Commute v (y ^ h)) : Commute v y := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (CFSG.Wreathed.mem_zpowers_zpow_of_odd hy hh)
  rw [← hk]
  exact hv.zpow_right k

theorem mem_squareRootSection_iff_primary_conjugate {y : G} {a : ℕ}
    (hy : orderOf y = 2 ^ a) {g u w : G} {e : ℕ}
    (huw : Commute u w) (hproduct : u * w = g)
    (hu : orderOf u ∣ 2 ^ e) (hw : Odd (orderOf w)) :
    g ∈ squareRootSection y ↔ ∃ h : ℤ, Odd h ∧ IsConj u (y ^ h) := by
  have hy2 : y ^ 2 ^ a = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  constructor
  · rintro ⟨h, v, hh, hv, hcentral, hconj⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    let v' := MulAut.conj c v
    let y' := MulAut.conj c (y ^ h)
    have hyh : orderOf (y ^ h) ∣ 2 ^ a := by
      rw [← hy]
      exact orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers y h)
    have hy' : orderOf y' ∣ 2 ^ a := by
      dsimp only [y']
      rw [MulEquiv.orderOf_eq]
      exact hyh
    have hv' : Nat.Coprime 2 (orderOf v') := by
      dsimp only [v']
      rw [MulEquiv.orderOf_eq]
      exact Nat.coprime_two_left.mpr hv
    have hcv : Commute v y := Subgroup.mem_centralizer_singleton_iff.mp hcentral
    have hcomm : Commute y' v' := (hcv.symm.zpow_left h).map (MulAut.conj c)
    have hprod : y' * v' = g := by
      rw [← map_mul]
      exact hc
    have huniq := CFSG.LyonsUnitaryFour.primary_factorization_unique hu
      (Nat.coprime_two_left.mpr hw) huw hy' hv' hcomm (hproduct.trans hprod.symm)
    refine ⟨h, hh, IsConj.symm ?_⟩
    exact isConj_iff.mpr ⟨c, huniq.1.symm⟩
  · rintro ⟨h, hh, hconj⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    let v := MulAut.conj c w
    have hv : Odd (orderOf v) := by
      dsimp only [v]
      rw [MulEquiv.orderOf_eq]
      exact hw
    have hvh : Commute v (y ^ h) := by
      rw [← hc]
      exact huw.symm.map (MulAut.conj c)
    have hvy := commute_of_commute_odd_power hy2 hh hvh
    refine ⟨h, v, hh, hv, Subgroup.mem_centralizer_singleton_iff.mpr hvy,
      IsConj.symm ?_⟩
    apply isConj_iff.mpr
    refine ⟨c, ?_⟩
    rw [← hproduct]
    change MulAut.conj c (u * w) = y ^ h * v
    rw [map_mul]
    exact congrArg (fun z => z * v) hc

theorem squareRootSection_primary_characterization [Finite G] {y g : G} {a : ℕ}
    (hy : orderOf y = 2 ^ a) :
    g ∈ squareRootSection y ↔
      ∃ u w : G, ∃ e : ℕ, Commute u w ∧ u * w = g ∧
        orderOf u ∣ 2 ^ e ∧ Odd (orderOf w) ∧ ∃ h : ℤ, Odd h ∧ IsConj u (y ^ h) := by
  constructor
  · intro hg
    obtain ⟨u, w, e, -, -, huw, hproduct, hu, hw⟩ :=
      finite_prime_primary_factorization g 2 Nat.prime_two
    have hwodd := Nat.coprime_two_left.mp hw
    exact ⟨u, w, e, huw, hproduct, hu, hwodd,
      (mem_squareRootSection_iff_primary_conjugate hy huw hproduct hu hwodd).mp hg⟩
  · rintro ⟨u, w, e, huw, hproduct, hu, hw, hh⟩
    exact (mem_squareRootSection_iff_primary_conjugate hy huw hproduct hu hw).mpr hh

theorem not_isConj_odd_power_of_not_mem_section {y g : G} {a : ℕ}
    (hy : orderOf y = 2 ^ a) (hg : g ∉ squareRootSection y)
    {u w : G} {e : ℕ} (huw : Commute u w) (hproduct : u * w = g)
    (hu : orderOf u ∣ 2 ^ e) (hw : Odd (orderOf w)) {h : ℤ} (hh : Odd h) :
    ¬ IsConj u (y ^ h) := by
  intro hconj
  exact hg ((mem_squareRootSection_iff_primary_conjugate hy huw hproduct hu hw).mpr
    ⟨h, hh, hconj⟩)

theorem classFunction_section_value_iff {y : G} {f : G → ℂ}
    (hf : BlocksIsClassFunction f) {c : ℂ} :
    (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({y} : Set G) → f (y ^ h * v) = c) ↔
      ∀ g ∈ squareRootSection y, f g = c := by
  constructor
  · intro hvalue g hg
    obtain ⟨h, v, hh, hv, hcentral, hconj⟩ := hg
    obtain ⟨a, ha⟩ := isConj_iff.mp hconj
    rw [← ha, hf, hvalue h v hh hv hcentral]
  · intro hvalue h v hh hv hcentral
    exact hvalue _ ⟨h, v, hh, hv, hcentral, IsConj.refl _⟩

omit [Group G] in
theorem integral_average_columns_support {ι κ : Type*}
    (I : Finset ι) (K : Finset κ) (χ : ι → G → ℂ) (u : κ → G)
    (c : ι → ℤ) (scale : ℂ) (T : G → ℂ)
    (hT : ∀ g, T g = ∑ i ∈ I, (c i : ℂ) * χ i g)
    (hc : ∀ i ∈ I, (c i : ℂ) = scale * ∑ k ∈ K, χ i (u k))
    (U : Set G)
    (hoff : ∀ g ∉ U, ∀ k ∈ K,
      ∑ i ∈ I, χ i (u k) * starRingEnd ℂ (χ i g) = 0) :
    ∀ g ∉ U, T g = 0 := by
  intro g hg
  have hweighted : ∑ i ∈ I, (c i : ℂ) * starRingEnd ℂ (χ i g) = 0 := by
    calc
      (∑ i ∈ I, (c i : ℂ) * starRingEnd ℂ (χ i g)) =
          scale * ∑ k ∈ K, ∑ i ∈ I, χ i (u k) * starRingEnd ℂ (χ i g) := by
        calc
          (∑ i ∈ I, (c i : ℂ) * starRingEnd ℂ (χ i g)) =
              ∑ i ∈ I, (scale * ∑ k ∈ K, χ i (u k)) * starRingEnd ℂ (χ i g) := by
            exact Finset.sum_congr rfl fun i hi => congrArg
              (fun z => z * starRingEnd ℂ (χ i g)) (hc i hi)
          _ = scale * ∑ i ∈ I, ∑ k ∈ K,
              χ i (u k) * starRingEnd ℂ (χ i g) := by
            simp only [mul_assoc, Finset.sum_mul, Finset.mul_sum]
          _ = scale * ∑ k ∈ K, ∑ i ∈ I,
              χ i (u k) * starRingEnd ℂ (χ i g) := by rw [Finset.sum_comm]
      _ = 0 := by simp only [Finset.sum_congr rfl fun k hk => hoff g hg k hk,
          Finset.sum_const_zero, mul_zero]
  have hconj := congrArg (starRingEnd ℂ) hweighted
  simpa only [map_sum, map_mul, map_intCast, Complex.conj_conj, map_zero, ← hT g] using hconj

theorem character_eq_of_square_root_sections [Fintype G]
    (y : G) (A B D : BlocksIrr G) {q Q : ℕ} (ε : ℤ)
    (hq : 5 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (hQ : (Q : ℤ) = (q : ℤ) ^ 2 + ε * q + 1)
    (hA : (A : G → ℂ) 1 = (q ^ 3 : ℕ))
    (hB : (B : G → ℂ) 1 = (Q : ℂ))
    (hD : (D : G → ℂ) 1 = (q * Q : ℕ))
    (hsupport : ∀ g ∉ squareRootSection y, signedTest ε A B D g = 0)
    (hsectionB : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({y} : Set G) → (B : G → ℂ) (y ^ h * v) = -1)
    (θ : FiniteComplexRepresentation.{0, 0} G)
    (hdegree : Module.finrank ℂ θ.vector ≤ Q)
    (hsectionθ : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({y} : Set G) → θ.character (y ^ h * v) = -1) :
    θ.character = (B : G → ℂ) ∧ Module.finrank ℂ θ.vector = Q := by
  have hclassB : BlocksIsClassFunction (B : G → ℂ) := by
    obtain ⟨ρ, _, _, _, data, _, hdata⟩ := B.property
    rw [← hdata]
    exact fun x a => Representation.char_conj data x a
  have hclassθ : BlocksIsClassFunction θ.character :=
    fun x a => Representation.char_conj θ.representation x a
  have hBunion := (classFunction_section_value_iff hclassB).mp hsectionB
  have hθunion := (classFunction_section_value_iff hclassθ).mp hsectionθ
  exact character_eq_of_square_root_degrees_and_support A B D ε hq hε hQ hA hB hD
    (squareRootSection y) hsupport θ hdegree (fun g hg => (hθunion g hg).trans (hBunion g hg).symm)

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
