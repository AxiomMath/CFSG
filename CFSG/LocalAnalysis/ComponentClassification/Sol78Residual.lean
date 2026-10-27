module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.GH74.GLS

variable {X : Type} [Group X]

@[expose] def twoElements (Y : Subgroup X) : Set X :=
  {x | x ∈ Y ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}

theorem oPrimeResidualOf_eq_closure (Y : Subgroup X) :
    oPrimeResidualOf 2 Y = closure (twoElements Y) := by
  unfold oPrimeResidualOf oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩

theorem oPrimeResidualOf_le (Y : Subgroup X) : oPrimeResidualOf 2 Y ≤ Y :=
  map_subtype_le _

theorem le_oPrimeResidualOf [Finite X] {J Y : Subgroup X} (hJY : J ≤ Y)
    (hJ : CatalogueBPrimeJoin.primeResidual 2 J = ⊤) : J ≤ oPrimeResidualOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro j hj
  have hjT : (⟨j, hj⟩ : J) ∈ CatalogueBPrimeJoin.primeResidual 2 J := by
    rw [hJ]; exact mem_top _
  rw [CatalogueBPrimeJoin.primeResidual_eq_closure] at hjT
  rw [oPrimeResidualOf_eq_closure]
  have hmap : (closure {x : J | ∃ k : ℕ, orderOf x = 2 ^ k}).map J.subtype ≤
      closure (twoElements Y) := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
    refine subset_closure ⟨hJY x.2, k, ?_⟩
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, ← hk, pow_orderOf_eq_one, Subgroup.coe_one]
  exact hmap ⟨⟨j, hj⟩, hjT, rfl⟩

theorem mem_normalizer_oPrimeResidualOf {Y : Subgroup X} {g : X}
    (hg : g ∈ normalizer (Y : Set X)) :
    g ∈ normalizer ((oPrimeResidualOf 2 Y : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq, oPrimeResidualOf_eq_closure]
  rw [MonoidHom.map_closure]
  congr 1
  have hY := mem_normalizer_iff.mp hg
  have hY' := mem_normalizer_iff.mp (inv_mem hg)
  ext x
  constructor
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    refine ⟨(hY y).mp hy, k, ?_⟩
    change (g * y * g⁻¹) ^ (2 ^ k) = 1
    rw [conj_pow, hk]
    group
  · rintro ⟨hx, k, hk⟩
    refine ⟨g⁻¹ * x * g, ⟨?_, k, ?_⟩, ?_⟩
    · have := (hY' x).mp hx
      simpa using this
    · rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, conj_pow, hk]
      group
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem primeResidual_oPrimeResidualOf [Finite X] (Y : Subgroup X) :
    CatalogueBPrimeJoin.primeResidual 2 ↥(oPrimeResidualOf 2 Y) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := oPrimeResidualOf 2 Y with hR
  have hRc : R = closure (twoElements Y) := oPrimeResidualOf_eq_closure Y
  rw [eq_top_iff]
  have hgen : closure (((↑) : R → X) ⁻¹' twoElements Y) = ⊤ := by
    have h := Subgroup.closure_closure_coe_preimage (k := twoElements Y)
    rw [← hRc] at h
    exact h
  rw [← hgen, closure_le]
  rintro r ⟨-, k, hk⟩
  refine CatalogueBPrimeJoin.pSubgroup_le_residual 2 (zpowers r) ?_ (mem_zpowers r)
  apply IsPGroup.of_card (n := (orderOf r).factorization 2)
  rw [Nat.card_zpowers]
  have hdvd : orderOf r ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hj, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

end CFSG.ComponentClassification.Sol78
