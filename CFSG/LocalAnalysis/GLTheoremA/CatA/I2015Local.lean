module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem le_primeCore_of_le_ker {H : Type} [Group H] [Finite H] {p : ℕ}
    (hodd : Odd (Nat.card (Subgroup.center (ppQuot p H))))
    {S : Subgroup H} (hS : IsPGroup 2 S) (hk : S ≤ (piOf p H).ker) :
    S ≤ GLAPPrimeCore p H := by
  intro s hs
  have hcen : (QuotientGroup.mk s : ppQuot p H) ∈ Subgroup.center (ppQuot p H) := by
    have h1 : piOf p H s = 1 := (MonoidHom.mem_ker).1 (hk hs)
    exact (QuotientGroup.eq_one_iff (QuotientGroup.mk s : ppQuot p H)).1 h1
  obtain ⟨k, hk2⟩ := hS ⟨s, hs⟩
  have hs1 : s ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk2
    simpa using this
  let q : Subgroup.center (ppQuot p H) := ⟨QuotientGroup.mk s, hcen⟩
  have hq : q ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← QuotientGroup.mk_pow, hs1, QuotientGroup.mk_one]
  have hord1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hq
  have hord2 : orderOf q ∣ Nat.card (Subgroup.center (ppQuot p H)) := orderOf_dvd_natCard q
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Subgroup.center (ppQuot p H))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hone : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  have hq1 : q = 1 := orderOf_eq_one_iff.1 hone
  have hmk : (QuotientGroup.mk s : ppQuot p H) = 1 := congrArg Subtype.val hq1
  exact (QuotientGroup.eq_one_iff s).1 hmk

theorem local_reduction {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hodd : I2015OddCentreFact) (_hlie : I2015LieModelFact) (hpar : I2015NoParabolicFact)
    {δ : MulAut H} (hδ : δ ^ p = 1) (hperf : commutator (ppQuot p H) = ⊤)
    (hchev : IsChevSimple 2 (psimpleOf p H)) (hfield : FieldAutOn p H δ)
    {I I₀ S : Subgroup H} (hI : GLAPComponent p (fixSub δ) I) (hI0 : I₀ ≤ I)
    (hcov : I₀ ⊔ GLAPPrimeCoreOf p I = I) (hS : IsPGroup 2 S)
    (hN : I₀ ≤ Subgroup.normalizer (S : Set H)) :
    S ≤ GLAPPrimeCore p H := by
  classical
  by_cases hk : S ≤ (piOf p H).ker
  · exact le_primeCore_of_le_ker (hodd H p δ hp hp2 hδ hperf hchev hfield) hS hk
  exfalso
  set U : Subgroup (psimpleOf p H) := S.map (piOf p H) with hUdef
  have hU : U ≠ ⊥ := by
    intro hbot
    apply hk
    intro s hs
    have hmem : piOf p H s ∈ U := Subgroup.mem_map_of_mem _ hs
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (MonoidHom.mem_ker).2 hmem
  have hU2 : IsPGroup 2 U := by
    intro u
    obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.1 u.2
    obtain ⟨k, hk2⟩ := hS ⟨s, hs⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hs1 : s ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk2
      simpa using this
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hsu, ← map_pow, hs1, map_one]
  have hconj : ∀ x ∈ Subgroup.normalizer (S : Set H), ∀ u ∈ U,
      piOf p H x * u * (piOf p H x)⁻¹ ∈ U := by
    intro x hx u hu
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hu
    have hxs : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hx s).1 hs
    have : piOf p H x * piOf p H s * (piOf p H x)⁻¹ = piOf p H (x * s * x⁻¹) := by
      simp only [map_mul, map_inv]
    rw [this]
    exact Subgroup.mem_map_of_mem _ hxs
  have hNUx : ∀ x ∈ Subgroup.normalizer (S : Set H), piOf p H x ∈ Subgroup.normalizer (U : Set (psimpleOf p H)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconj x hx h hh
    · intro hh
      have hx' : x⁻¹ ∈ Subgroup.normalizer (S : Set H) := Subgroup.inv_mem _ hx
      have := hconj x⁻¹ hx' _ hh
      simpa [map_inv, mul_assoc] using this
  have hmap : I₀.map (piOf p H) ≤ Subgroup.normalizer (U : Set (psimpleOf p H)) := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    exact hNUx x (hN hx)
  exact hpar H p δ I I₀ hp hp2 hδ hperf hchev hfield hI hI0 hcov U hU hU2 hmap

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
