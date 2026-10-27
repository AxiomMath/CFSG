module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.StrWts
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Strings

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
open scoped MatrixGroups


variable {K : Type} [Field K] [Finite K] [CharP K 2]
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

theorem string_nonempty {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {s : N6} (hs : s ∉ J) {J' : Finset ℕ}
    (hχ : ∀ z : Kˣ, χ (e6Data_valid.hm K s z) = (algebraMap K k (z : K)) ^ (∑ i ∈ J', 2 ^ i))
    (hJ0 : J' = ∅ → ∀ g, ρ (rankOne6 K s g) y = y) : J'.Nonempty := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases J'.eq_empty_or_nonempty with h0 | h0
  · exfalso
    apply hs
    have hfix := hJ0 h0
    refine (ht.2.2.2 s).2 ⟨fun z => ?_, ?_⟩
    · show χ (e6Data_valid.hm K s z) = 1
      rw [hχ z, h0]; simp
    · letI : Fintype K := Fintype.ofFinite K
      refine ((e6CoverRankOne K).heckeT_datum ρ s y).trans ?_
      have hn' : ∀ c : K, ρ ((e6CoverRankOne K).x s c * (e6CoverData K).nhat s) y = y := by
        intro c
        show ρ (e6Data_valid.xm K (Pi.single s 1) c * (e6CoverData K).nhat s) y = y
        rw [nhat_e6, ← rankOne6_u s c, ← rankOne6_w s, ← map_mul]
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
    {χ : ↥(e6Data_valid.minGroup K) → k} {s : N6} {J' : Finset ℕ} {g : ℕ}
    (hχ : ∀ z : Kˣ, χ (e6Data_valid.hm K s z) = (algebraMap K k (z : K)) ^ (∑ i ∈ J', 2 ^ i))
    (hper : ∀ z : Kˣ, χ (e6Data_valid.hm K s z) ^ (2 ^ g) = χ (e6Data_valid.hm K s z)) :
    (2 ^ n - 1) ∣ (2 ^ g - 1) * ∑ i ∈ J', 2 ^ i := by
  set b := ∑ i ∈ J', 2 ^ i with hb
  have h1 : ∀ z : Kˣ, (algebraMap K k (z : K)) ^ (b * 2 ^ g) = (algebraMap K k (z : K)) ^ b := by
    intro z
    have := hper z
    rw [hχ z, ← pow_mul] at this
    exact this
  have hle : b ≤ b * 2 ^ g := Nat.le_mul_of_pos_right _ (by positivity)
  have h2 := dvd_of_forall_pow_eq (k := k) hK hle (fun z => (h1 z).symm)
  have : b * 2 ^ g - b = (2 ^ g - 1) * b := by
    rw [Nat.sub_one_mul, mul_comm]
  rwa [this] at h2

theorem two_pow_le_finrank_orbitSpan {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {s : N6} (hs : s ∉ J) {g : ℕ} (hg : 1 ≤ g)
    (hgn : g ∣ n) (hper : ∀ z : Kˣ, χ (e6Data_valid.hm K s z) ^ (2 ^ g) = χ (e6Data_valid.hm K s z)) :
    2 ^ (n / g) ≤ Module.finrank k (orbitSpan (ρ.comp (rankOne6 K s)) y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J', hJ', hχ, hdim, hJ0, -⟩ := string_of_highest hK hρ ht s
  have hne : J'.Nonempty := string_nonempty hn hK ht hs hχ hJ0
  have hper' := periodic_dvd hK hχ hper
  have hcard := card_ge_of_periodic hg hgn hJ' hne hper'
  calc 2 ^ (n / g) ≤ 2 ^ J'.card := Nat.pow_le_pow_right (by norm_num) hcard
    _ = Module.finrank k (orbitSpan (ρ.comp (rankOne6 K s)) y) := hdim.symm

@[expose] def alphaF (s : N6) : N6 → ℤ := fun i => Tag.cartan .E6 i s

@[expose] def omegaF (s : N6) : N6 → ℤ := Pi.single s 1

theorem string_wt_vec {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {s : N6} (hJ : ∀ s', s' ≠ s → s' ∈ J) :
    ∃ J' : Finset ℕ, (∀ i ∈ J', i < n) ∧
      (∀ z : Kˣ, χ (e6Data_valid.hm K s z) = (algebraMap K k (z : K)) ^ (∑ i ∈ J', 2 ^ i)) ∧
      (J' = ∅ → ∀ g, ρ (rankOne6 K s g) y = y) ∧
      Module.finrank k (orbitSpan (ρ.comp (rankOne6 K s)) y) = 2 ^ J'.card ∧
      ∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (rankOne6 K s)) y, e ≠ 0 ∧
        e ∈ wt ρ (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) • omegaF s - (2 : ℤ) ^ b • alphaF s) := by
  obtain ⟨J', hJ', hε, hdim, hJ0, hwt⟩ := string_of_highest hK hρ ht s
  refine ⟨J', hJ', hε, hJ0, hdim, fun b hb => ?_⟩
  obtain ⟨e, he, he0, hed⟩ := hwt b hb
  refine ⟨e, he, he0, ?_⟩
  set a : ℤ := ((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) with ha
  have hy : ∀ i t, ρ (e6Data_valid.hm K i t) y = kp (k := k) K t (a * (if i = s then 1 else 0)) • y := by
    intro i t
    have h1 := ht.2.2.1 _ (e6_hm_mem_H i t)
    rw [h1]
    congr 1
    by_cases hi : i = s
    · subst hi
      rw [hε t]
      simp only [↓reduceIte, mul_one]
      unfold kp
      rw [ha, zpow_natCast]
    · have hiJ := hJ i hi
      have h3 := ((ht.2.2.2 i).1 hiJ).1 t
      have h3' : χ (e6Data_valid.hm K i t) = 1 := h3
      rw [h3']
      simp [kp, hi]
  have hes : ∀ z : Kˣ, ρ (e6Data_valid.hm K s z) e =
      kp (k := k) K z (a * (if s = s then 1 else 0) - 2 * (2 : ℤ) ^ b) • e := by
    intro z
    rw [hed z]
    simp only [↓reduceIte, mul_one]
    congr 2
    ring
  intro i t
  have := weight_shift ρ s (fun i => a * (if i = s then 1 else 0)) hy ((2 : ℤ) ^ b) he hes i t
  rw [this]
  congr 1
  simp only [omegaF, alphaF, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  ring_nf

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
