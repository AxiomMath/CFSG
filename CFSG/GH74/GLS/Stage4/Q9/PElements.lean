module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open MulAction

section FixCount

variable {G : Type*} [Group G]

@[expose] noncomputable def cosetFixCount (P : Subgroup G) (g : G) : ℕ :=
  Nat.card (fixedBy (G ⧸ P) g)

theorem exists_conj_mem_of_cosetFixCount_ne_zero [Finite G] {P : Subgroup G} {g : G}
    (h : cosetFixCount P g ≠ 0) : ∃ x : G, x⁻¹ * g * x ∈ P := by
  have hne : Nonempty (fixedBy (G ⧸ P) g) :=
    (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero h)).1
  obtain ⟨⟨q, hq⟩⟩ := hne
  induction q using QuotientGroup.induction_on with
  | H x =>
    refine ⟨x, ?_⟩
    have hq' : ((g * x : G) : G ⧸ P) = (x : G ⧸ P) := hq
    rw [QuotientGroup.eq] at hq'
    have := P.inv_mem hq'
    simpa [mul_assoc] using this

theorem pow_eq_one_of_cosetFixCount_ne_zero [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {g : G} (h : cosetFixCount (P : Subgroup G) g ≠ 0) :
    g ^ (p ^ (Nat.card G).factorization p) = 1 := by
  obtain ⟨x, hx⟩ := exists_conj_mem_of_cosetFixCount_ne_zero h
  have h1 : (x⁻¹ * g * x) ^ (p ^ (Nat.card G).factorization p) = 1 := by
    have hdvd := Subgroup.orderOf_dvd_natCard (P : Subgroup G) hx
    rw [P.card_eq_multiplicity] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.1 hdvd
  have h2 : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
  calc g ^ (p ^ (Nat.card G).factorization p)
      = (x * (x⁻¹ * g * x) * x⁻¹) ^ (p ^ (Nat.card G).factorization p) := by rw [← h2]
    _ = x * (x⁻¹ * g * x) ^ (p ^ (Nat.card G).factorization p) * x⁻¹ := conj_pow
    _ = 1 := by rw [h1]; group

theorem not_dvd_cosetFixCount_of_pow_eq_one [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {g : G} (hg : g ^ (p ^ (Nat.card G).factorization p) = 1) :
    ¬ p ∣ cosetFixCount (P : Subgroup G) g := by
  have hH : IsPGroup p (Subgroup.zpowers g) := by
    rintro ⟨h, hh⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    refine ⟨(Nat.card G).factorization p, Subtype.ext ?_⟩
    change (g ^ k) ^ (p ^ (Nat.card G).factorization p) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have hmod := hH.card_modEq_card_fixedPoints (G ⧸ (P : Subgroup G))
  have hfix : fixedPoints (Subgroup.zpowers g) (G ⧸ (P : Subgroup G)) =
      fixedBy (G ⧸ (P : Subgroup G)) g := by
    ext x
    constructor
    · intro hx
      exact hx ⟨g, Subgroup.mem_zpowers g⟩
    · intro hx h
      have hle : Subgroup.zpowers g ≤ stabilizer G x :=
        Subgroup.zpowers_le.2 (mem_stabilizer_iff.2 hx)
      exact mem_stabilizer_iff.1 (hle h.2)
  have hmod' : Nat.card (G ⧸ (P : Subgroup G)) ≡ cosetFixCount (P : Subgroup G) g [MOD p] := by
    unfold cosetFixCount
    rw [hfix] at hmod
    exact hmod
  intro hdvd
  exact P.not_dvd_index ((hmod'.dvd_iff dvd_rfl).2 hdvd)

open scoped Classical in
theorem cosetFixCount_pow_modEq [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) (g : G) :
    cosetFixCount (P : Subgroup G) g ^ Nat.totient (p ^ (Nat.card G).factorization p) ≡
      (if g ^ (p ^ (Nat.card G).factorization p) = 1 then 1 else 0)
        [MOD p ^ (Nat.card G).factorization p] := by
  split_ifs with hg
  · apply Nat.ModEq.pow_totient
    exact Nat.Coprime.pow_right _
      ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (not_dvd_cosetFixCount_of_pow_eq_one P hg)).symm
  · have h0 : cosetFixCount (P : Subgroup G) g = 0 := by
      by_contra h
      exact hg (pow_eq_one_of_cosetFixCount_ne_zero P h)
    rw [h0, zero_pow (Nat.totient_pos.2 (pow_pos hp.out.pos _)).ne']

@[expose] def fixedByPiEquiv {X : Type*} [MulAction G X] (ι : Type*) (g : G) :
    fixedBy (ι → X) g ≃ (ι → fixedBy X g) where
  toFun f i := ⟨f.1 i, congrFun f.2 i⟩
  invFun f := ⟨fun i => (f i).1, funext fun i => (f i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_dvd_sum_cosetFixCount_pow [Fintype G] (P : Subgroup G) (k : ℕ) :
    Nat.card G ∣ ∑ g : G, cosetFixCount P g ^ k := by
  classical
  have : ∀ g : G, Fintype (fixedBy (Fin k → G ⧸ P) g) := fun g => Fintype.ofFinite _
  have : Fintype (orbitRel.Quotient G (Fin k → G ⧸ P)) := Fintype.ofFinite _
  have hburn := sum_card_fixedBy_eq_card_orbits_mul_card_group G (Fin k → G ⧸ P)
  have hterm : ∀ g : G, Fintype.card (fixedBy (Fin k → G ⧸ P) g) = cosetFixCount P g ^ k := by
    intro g
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (fixedByPiEquiv (Fin k) g), Nat.card_fun,
      Nat.card_fin]
    rfl
  simp_rw [hterm] at hburn
  rw [hburn, Nat.card_eq_fintype_card]
  exact Dvd.intro_left _ rfl

end FixCount

theorem pow_card_factorization_eq_one_iff {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (g : G) :
    g ^ (p ^ (Nat.card G).factorization p) = 1 ↔ ∃ k : ℕ, g ^ (p ^ k) = 1 := by
  refine ⟨fun h => ⟨_, h⟩, ?_⟩
  rintro ⟨k, hk⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hk)
  have hjG : p ^ j ∣ Nat.card G := hj ▸ orderOf_dvd_natCard g
  have hjle : j ≤ (Nat.card G).factorization p :=
    (hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hjG
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ pow_dvd_pow p hjle)

theorem pow_card_factorization_eq_one_iff_orderOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (g : G) :
    g ^ (p ^ (Nat.card G).factorization p) = 1 ↔ ∃ k : ℕ, orderOf g = p ^ k := by
  rw [pow_card_factorization_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hk)
    exact ⟨j, hj⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, orderOf_dvd_iff_pow_eq_one.1 hk.dvd⟩

theorem card_pElements_dvd (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    p ^ (Nat.card G).factorization p ∣
      Nat.card {g : G // g ^ (p ^ (Nat.card G).factorization p) = 1} := by
  classical
  have := Fintype.ofFinite G
  let P : Sylow p G := default
  have hsum := card_dvd_sum_cosetFixCount_pow (P : Subgroup G)
    (Nat.totient (p ^ (Nat.card G).factorization p))
  have hdvd : p ^ (Nat.card G).factorization p ∣
      ∑ g : G, cosetFixCount (P : Subgroup G) g ^
        Nat.totient (p ^ (Nat.card G).factorization p) :=
    (Nat.ordProj_dvd _ _).trans hsum
  have hcard : Nat.card {g : G // g ^ (p ^ (Nat.card G).factorization p) = 1} =
      ∑ g : G, (if g ^ (p ^ (Nat.card G).factorization p) = 1 then 1 else 0) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [hcard]
  apply Nat.dvd_of_mod_eq_zero
  rw [Finset.sum_nat_mod]
  have hcongr : ∀ g ∈ (Finset.univ : Finset G),
      (if g ^ (p ^ (Nat.card G).factorization p) = 1 then 1 else 0) %
          p ^ (Nat.card G).factorization p =
        cosetFixCount (P : Subgroup G) g ^ Nat.totient (p ^ (Nat.card G).factorization p) %
          p ^ (Nat.card G).factorization p :=
    fun g _ => (cosetFixCount_pow_modEq P g).symm
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_nat_mod]
  exact Nat.mod_eq_zero_of_dvd hdvd

theorem card_pElements_dvd_orderOf (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    p ^ (Nat.card G).factorization p ∣ Nat.card {g : G // ∃ k : ℕ, orderOf g = p ^ k} := by
  rw [← Nat.card_congr (Equiv.subtypeEquivRight fun g =>
    pow_card_factorization_eq_one_iff_orderOf (p := p) g)]
  exact card_pElements_dvd G p

end CFSG.GH74.GLS.Stage4.Q9
