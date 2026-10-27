module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Strings
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Digits

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section Bound


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem dvd_of_forall_pow_eq {n : ℕ} (hK : Nat.card K = 2 ^ n) {b b' : ℕ} (hb : b ≤ b')
    (h : ∀ z : Kˣ, (algebraMap K k (z : K)) ^ b = (algebraMap K k (z : K)) ^ b') :
    (2 ^ n - 1) ∣ b' - b := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf γ = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, hK]
  have hinj : Function.Injective (Units.map (algebraMap K k).toMonoidHom) :=
    Units.map_injective (algebraMap K k).injective
  have hmod : orderOf (Units.map (algebraMap K k).toMonoidHom γ) = 2 ^ n - 1 :=
    (orderOf_injective _ hinj γ).trans hord
  have h2 : (Units.map (algebraMap K k).toMonoidHom γ) ^ b =
      (Units.map (algebraMap K k).toMonoidHom γ) ^ b' := by
    refine Units.ext ?_
    simpa using h γ
  rw [pow_eq_pow_iff_modEq, hmod] at h2
  exact (Nat.modEq_iff_dvd' hb).1 h2

theorem string_nonempty {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k (adjointGroup τ K) V}
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} (hs : s ∉ J) {J' : Finset ℕ}
    (hχ : ∀ z : Kˣ, χ (dC τ K s z) = (algebraMap K k (z : K)) ^ (∑ i ∈ J', 2 ^ i))
    (hJ0 : J' = ∅ → ∀ g, ρ (rankOne τ K s g) y = y) : J'.Nonempty := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases J'.eq_empty_or_nonempty with h0 | h0
  · exfalso
    apply hs
    have hfix := hJ0 h0
    rw [ht.2.2.2 s]
    refine ⟨fun z => ?_, ?_⟩
    · rw [hχ z, h0]; simp
    · letI : Fintype K := Fintype.ofFinite K
      rw [heckeT_chevDatum]
      have hn' : ∀ c : K, ρ (xC τ K s c * nC τ K s) y = y := by
        intro c
        rw [← rankOne_u s c, ← rankOne_w s, ← map_mul]
        exact hfix _
      simp only [hn']
      rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      have : (2 ^ n : ℕ) • y = ((2 ^ n : ℕ) : k) • y := (Nat.cast_smul_eq_nsmul k _ y).symm
      rw [this]
      have h0' : ((2 ^ n : ℕ) : k) = 0 := by
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
        rw [pow_succ]; push_cast; rw [CharTwo.two_eq_zero, mul_zero]
      rw [h0', zero_smul]
  · exact h0

theorem periodic_dvd {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {χ : adjointGroup τ K → k} {s : Fin τ.rank} {J' : Finset ℕ} {g : ℕ}
    (hχ : ∀ z : Kˣ, χ (dC τ K s z) = (algebraMap K k (z : K)) ^ (∑ i ∈ J', 2 ^ i))
    (hper : ∀ z : Kˣ, χ (dC τ K s z) ^ (2 ^ g) = χ (dC τ K s z)) :
    (2 ^ n - 1) ∣ (2 ^ g - 1) * ∑ i ∈ J', 2 ^ i := by
  set b := ∑ i ∈ J', 2 ^ i with hb
  have h1 : ∀ z : Kˣ, (algebraMap K k (z : K)) ^ (b * 2 ^ g) = (algebraMap K k (z : K)) ^ b := by
    intro z
    have := hper z
    rw [hχ z, ← pow_mul] at this
    exact this
  have hle : b ≤ b * 2 ^ g := Nat.le_mul_of_pos_right _ (by positivity)
  have h2 := dvd_of_forall_pow_eq hK hle (fun z => (h1 z).symm)
  have : b * 2 ^ g - b = (2 ^ g - 1) * b := by
    rw [Nat.sub_one_mul, mul_comm]
  rwa [this] at h2

theorem two_pow_le_finrank_orbitSpan {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} (hs : s ∉ J) {g : ℕ} (hg : 1 ≤ g)
    (hgn : g ∣ n) (hper : ∀ z : Kˣ, χ (dC τ K s z) ^ (2 ^ g) = χ (dC τ K s z)) :
    2 ^ (n / g) ≤ Module.finrank k (orbitSpan (ρ.comp (rankOne τ K s)) y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J', hJ', hχ, hdim, hJ0, -⟩ := string_of_highest (hw := hw) hK hρ ht s
  have hne : J'.Nonempty := string_nonempty hn hK ht hs hχ hJ0
  have hper' := periodic_dvd hK hχ hper
  have hcard := card_ge_of_periodic hg hgn hJ' hne hper'
  calc 2 ^ (n / g) ≤ 2 ^ J'.card := Nat.pow_le_pow_right (by norm_num) hcard
    _ = Module.finrank k (orbitSpan (ρ.comp (rankOne τ K s)) y) := hdim.symm

theorem two_pow_le_finrank_of_periodic [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} (hs : s ∉ J) {g : ℕ} (hg : 1 ≤ g)
    (hgn : g ∣ n) (hper : ∀ z : Kˣ, χ (dC τ K s z) ^ (2 ^ g) = χ (dC τ K s z)) :
    2 ^ (n / g) ≤ Module.finrank k V :=
  (two_pow_le_finrank_orbitSpan hn hK hρ ht hs hg hgn hper).trans (Submodule.finrank_le _)

end Bound

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
