module

public import CFSG.ClassicalInvolution.AschTight.S1911P3d
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Model

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19M

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.BorelTits

theorem odd_natCard_center_of_pow_three {G : Type*} [Group G] [Finite G]
    (h : ∀ z ∈ Subgroup.center G, z ^ 3 = 1) : Odd (Nat.card (Subgroup.center G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.center G) := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg : g ^ 3 = 1 := Subtype.ext (by simpa using h g g.2)
    have h3 : orderOf g ∣ 3 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hg
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h3
    exact ⟨i, hi⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact Odd.pow (by decide)

theorem center_pow_three_sl (F : Type) [Field F] :
    ∀ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F), z ^ 3 = 1 := by
  intro z hz
  obtain ⟨r, hr, hz'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hz', ← map_pow, hr, map_one]
  rfl

theorem pow_ne_two_of_ne_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ^ f ≠ 2 := by
  intro h
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp at h
  · have h3 : 3 ≤ p := by have := hp.two_le; omega
    have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega

theorem center_pow_three_su {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    ∀ z ∈ Subgroup.center (Unitary.SU (unitaryInvolution F p f) 3), z ^ 3 = 1 := by
  intro z hz
  set e := Unitary.equivStatedSU hF 3 with he
  have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := fun h =>
    pow_ne_two_of_ne_two (Fact.out : p.Prime) hp2 (congrArg Prod.snd h)
  have hz' : e z ∈ Subgroup.center (StatedSU 3 (p ^ f) F) := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨z, hz, rfl⟩
  rw [(Unitary.isQuasisimple_statedSU_of_card hF le_rfl hnq).2] at hz'
  obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.mp hz'
  have hdet := Unitary.det_eq_one_of_mem_statedSU (e z).2
  rw [← hu] at hdet
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
      using hdet
  have h3 : e z ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hu, ← map_pow, hu3, map_one, Subgroup.coe_one]
  apply e.injective
  rw [map_pow, h3, map_one]

theorem factM3 : S1911.FactM3 := by
  intro p e hp hp2 t k ht hadm
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : Finite (modelUniv .PSL 3 p e hp).K := ModelFacts.finite_modelUniv hp2 hp trivial hadm
    exact odd_natCard_center_of_pow_three (center_pow_three_sl (GaloisField p e))
  · have : Finite (modelUniv .PSU 3 p e hp).K := ModelFacts.finite_modelUniv hp2 hp trivial hadm
    have hF := card_galoisField_two_mul p e he
    have h : modelUniv .PSU 3 p e hp =
        ⟨Unitary.SU (unitaryInvolution (GaloisField p (2 * e)) p e) 3,
          Unitary.rootDatum hF 3⟩ := by
      simp only [modelUniv, lieUniversal, he, ↓reduceDIte]
    have key : ∀ (U : LieUniversal) (_ : modelUniv .PSU 3 p e hp = U),
        (∀ z ∈ Subgroup.center U.K, z ^ 3 = 1) →
          ∀ z ∈ Subgroup.center (modelUniv .PSU 3 p e hp).K, z ^ 3 = 1 := by
      intro U hU h3
      subst hU
      exact h3
    exact odd_natCard_center_of_pow_three (key _ h (center_pow_three_su hF hp2))
  · rw [RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inl rfl) 0 he, Subgroup.card_bot]
    exact odd_one
  · rw [RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0 he, Subgroup.card_bot]
    exact odd_one

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19M
