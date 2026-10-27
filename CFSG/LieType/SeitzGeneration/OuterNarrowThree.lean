module

public import CFSG.LieType.SeitzGeneration.OutdiagScope
public import CFSG.LieType.SeitzGeneration.UnitaryScope
public import CFSG.LieType.SeitzGeneration.OuterModel
import CFSG.LieType.SeitzGeneration.OuterHeisFixedUnitary
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.UnitaryPlaneStatements
import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_cube_root_of_dvd {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_card_sub_one Nat.prime_three h3
  exact ⟨ζ, hζ.pow_eq_one, hζ.ne_one (by norm_num)⟩

variable {K : Type} [Field K] [Finite K]

theorem le_linearAutGroup_of_narrowScope {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (h3 : 3 ∣ Nat.card K - 1)
    {E : Subgroup (MulAut (projectiveSL 3 K))} (hE : IsElemAbelian 3 E) (hs : NarrowScope 3 E) :
    E ≤ linearAutGroup 3 K := by
  classical
  intro a haE
  by_contra haD
  have hp : Nat.Prime 3 := Nat.prime_three
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hpℓ : 3 ≠ ℓ := by
    rintro rfl
    have h1 : 3 ∣ Nat.card K := by rw [hK]; exact dvd_pow_self 3 (by omega)
    have h2 : 3 ∣ 1 := by
      have := Nat.dvd_sub h1 h3
      rwa [Nat.sub_sub_self Nat.card_pos] at this
    omega
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := K) (le_refl 3)
  have ha3 : a ^ 3 = 1 := hE.2 a haE
  have ha1 : a ≠ 1 := fun h => haD (h ▸ one_mem _)
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have haS : a ∈ semilinearAutGroup 3 K :=
    CFSG.RankThree.PartOne.KCLinCommOdd.mem_semilinearAutGroup_of_pow_eq_one (le_refl 3)
      (by norm_num) hp (j := 1) (by simpa using ha3)
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf (le_refl 3) hK
  obtain ⟨-, σ, hσ, ⟨h, -, hha⟩, -⟩ := hdesc 3 hp hpℓ a haS haD haord
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_dvd h3
  obtain ⟨s, t, hst, hs1, hs3, ht3, ht, hfs, hft⟩ :=
    exists_heis_pair_linear hω3 hω1 (ringAut_apply_eq_of_pow_three hσ3 hω3 hω1)
  have hcongr : MulAut.congr h⁻¹ a = fieldAut 3 K σ := by
    change h⁻¹ * a * h = _
    rw [hha]
    group
  refine NarrowScope.false_of_fixed_e9 hp hinj (hs.map_congr h⁻¹) ⟨a, haE, hcongr⟩
    (by rw [← map_pow, hσ3, map_one]) ?_ hst hs1 hs3 ht3 ht hfs hft
  intro x hx
  refine haD ?_
  have : a = MulAut.conj (h x) := by
    rw [← mulAut_mul_conj_mul_inv, ← hx, ← hha]
  rw [this]
  exact conj_mem_linearAutGroup _

end Linear

section Unitary

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem le_primeFormD_of_narrowScope (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    (hq : ℓ ^ f ≠ 2) {E : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hE : IsElemAbelian 3 E) (hs : NarrowScope 3 E) : E ≤ primeFormD h (idGram K 3) := by
  classical
  intro a haE
  by_contra haD
  have hfin := h.finite
  have hp : Nat.Prime 3 := Nat.prime_three
  have hne : ¬(3 = 3 ∧ ℓ ^ f = 2) := fun hh => hq hh.2
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hpℓ : 3 ≠ ℓ := by
    rintro rfl
    have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
    have h2 : 3 ∣ 1 := (Nat.dvd_add_right h1).mp hq3
    omega
  have : IsSimpleGroup (primeFormP h (idGram K 3)) :=
    CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h le_rfl hne
  have hnab : ∃ x y : primeFormP h (idGram K 3), x * y ≠ y * x := by
    have := CFSG.RankThree.Classical.not_commute_primeFormP_one h le_rfl hne
    push Not at this
    exact this
  have hinj := CFSG.RankThree.PartOne.CTP.conj_injective_of_simple hnab
  have ha3 : a ^ 3 = 1 := hE.2 a haE
  have ha1 : a ≠ 1 := fun h1 => haD (h1 ▸ one_mem _)
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  set σ := primeFormFieldFactor h hC le_rfl hne a with hσdef
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply haD
    rw [← ker_primeFormFieldFactor h hC le_rfl hne]
    exact h1
  have hσ3 : σ ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h le_rfl hne hp
      (by norm_num) hpℓ a haord σ rfl hσord
  obtain ⟨r, hr⟩ : ∃ r, ℓ ^ f = r + 1 :=
    ⟨ℓ ^ f - 1, by have := Nat.one_le_pow f ℓ h.prime.pos; omega⟩
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [h.card, pow_mul', hr, Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = r * (r + 2) + 1 by ring)]
    exact Dvd.dvd.mul_left (by rw [hr] at hq3; omega) r
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_dvd h3K
  have hσω : σ ω = ω := ringAut_apply_eq_of_pow_three hσ3 hω3 hω1
  have hωb : h.bar ω * ω = 1 := by
    obtain ⟨m, hm⟩ := hq3
    rw [h.bar_apply, ← pow_succ, hm, pow_mul, hω3, one_pow]
  obtain ⟨s, t, hst, hs1, hs3, ht3, ht, hfs, hft⟩ := exists_heis_pair_unitary h hω3 hω1 hωb hσω
  set c := primeFormConjHom h (idGram K 3) M with hc
  have hcD : c ∈ primeFormD h (idGram K 3) := ⟨M, rfl⟩
  have hfa : MulAut.congr c⁻¹ a = primeFormFieldHom h hC σ := by
    change c⁻¹ * a * c = _
    exact hM
  refine NarrowScope.false_of_fixed_e9 hp hinj (hs.map_congr c⁻¹) ⟨a, haE, hfa⟩
    (by rw [← map_pow, hσ3, map_one]) ?_ hst hs1 hs3 ht3 ht hfs hft
  intro x hx
  apply haD
  have hax : a = c * MulAut.conj x * c⁻¹ := by
    rw [← hx, ← hM]
    group
  rw [hax]
  exact mul_mem (mul_mem hcD (inner_le_primeFormD h ⟨x, rfl⟩)) (inv_mem hcD)

end Unitary

section Pieces

theorem primePower_card_four {q : TauCeti.PrimePower} (h : q.card = 4) :
    q.p = 2 ∧ q.exponent = 2 := by
  have hp2 : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, h] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
      (q.prime_p.dvd_of_dvd_pow (show q.p ∣ 2 ^ 2 by simpa using h1))
  refine ⟨hp2, ?_⟩
  have h2 : 2 ^ q.exponent = 2 ^ 2 := by
    have h3 := h
    rw [TauCeti.PrimePower.card_def, hp2] at h3
    rw [h3]
    norm_num
  exact Nat.pow_right_injective (le_refl 2) h2

theorem seitzOuter_A2_three (hOH : OuterHeisCore) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ IsLinearIndex d.1 ∧
      (p = 3 ∧ ∃ q, d.1 = .A 2 q ∧ 3 ∣ q.card - 1) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨-, hs, -, rfl, q, hd, hq3⟩
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hKcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have h3K : 3 ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by
    rw [hKcard, ← TauCeti.PrimePower.card_def]
    exact hq3
  have h4 : q.card ≠ 4 := fun h4 =>
    hex (Or.inl ⟨rfl, Or.inr (Or.inl ⟨q, (primePower_card_four h4).1,
      (primePower_card_four h4).2, rfl⟩)⟩)
  exact planeGen_outer_A2_linear hOH hv hq3 h4 hE hc
    (le_linearAutGroup_of_narrowScope q.prime_p q.exponent_pos hKcard h3K
      (isElemAbelian_map_congr (linearModel hv) hE) (hs.map_congr (linearModel hv)))

theorem seitzOuter_twistedA2_three (hUH : UnitaryHeisCore) (hUOH : UnitaryOuterHeisCore) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ IsUnitaryIndex' d.1 ∧
      (p = 3 ∧ ∃ q, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨-, hs, -, rfl, q, hd, hq3⟩
  subst hd
  obtain ⟨-, -, -, hne, F, _, hU, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
        (MulEquiv.refl (Cat ⟨.twistedA 2 q, hv⟩)))
  have hq3' : 3 ∣ q.p ^ q.exponent + 1 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq3
  have hq2 : q.p ^ q.exponent ≠ 2 := fun h2 => hne ⟨rfl, h2⟩
  exact planeGen_of_unitaryDiagAut_equiv hUH hUOH hU hq3' hq2 θ hE hc
    (le_primeFormD_of_narrowScope hU hq3' hq2 (isElemAbelian_map_congr θ hE) (hs.map_congr θ))

end Pieces

end CFSG.LieType.SeitzGeneration
