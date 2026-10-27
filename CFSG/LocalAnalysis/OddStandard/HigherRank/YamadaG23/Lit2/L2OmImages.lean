module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Transfer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Symp

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem l2_om_images {E H S Ω : Type} [Group E] [Finite E] [Group H] [Group S] [Group Ω]
    (α : E →* H) (hα : Function.Surjective α) (ρ : H →* S) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = center H) (hH2 : IsPGroup 2 ↥(center H)) {A : Subgroup S}
    (hE : IsE 4 ↥A) (hP : L2Pauli ρ A) {ζ : E} (hζk : ζ ∈ (ρ.comp α).ker)
    (hζ4 : orderOf ζ = 4) (hζg : ∀ u ∈ (ρ.comp α).ker, ∃ k : ℕ, u = ζ ^ k)
    (hcen : ∀ u ∈ (ρ.comp α).ker, ∀ x : E, u * x = x * u)
    (π : Ω →* S) (hπ2 : ∀ u ∈ π.ker, u * u = 1) (hπcen : ∀ u ∈ π.ker, ∀ w : Ω, u * w = w * u)
    (θ : E →* Ω) (hθ : π.comp θ = ρ.comp α) :
    ∃ y : Fin 4 → Ω, (∀ i, y i * y i = 1) ∧ (∀ i j, y i * y j = y j * y i) ∧
      ∀ d : Ω, (∀ i, y i * d = d * y i) → ∀ a ∈ A, a * π d = π d * a := by
  let m : E := ζ ^ 2
  have hm1 : m ≠ 1 := by
    intro h
    have hdvd : orderOf ζ ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact h
    rw [hζ4] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    omega
  have hm2 : m * m = 1 := by
    dsimp only [m]
    rw [← pow_two, ← pow_mul, show (2 : ℕ) * 2 = 4 from rfl, ← hζ4, pow_orderOf_eq_one]
  have hm2sq : m ^ 2 = 1 := by rw [pow_two]; exact hm2
  have hmk : m ∈ (ρ.comp α).ker := by
    dsimp only [m]
    exact pow_mem hζk 2
  have hmcen : ∀ x : E, m * x = x * m := fun x => hcen m hmk x
  have hker_sq : ∀ u ∈ (ρ.comp α).ker, u * u = 1 ∨ u * u = m := by
    intro u hu
    obtain ⟨k, hk⟩ := hζg u hu
    rw [hk]
    have h : ζ ^ k * ζ ^ k = m ^ k := by
      rw [← pow_two, ← pow_mul, mul_comm k 2, pow_mul]
    rw [h]
    rcases Nat.even_or_odd k with hk_even | hk_odd
    · left
      obtain ⟨s, hs⟩ := even_iff_exists_two_mul.mp hk_even
      rw [hs, pow_mul, hm2sq, one_pow]
    · right
      obtain ⟨s, hs⟩ := odd_iff_exists_bit1.mp hk_odd
      rw [hs, pow_succ, pow_mul, hm2sq, one_pow, one_mul]
  have hker_odd : ∀ u ∈ (ρ.comp α).ker, Odd (orderOf u) → u = 1 := by
    intro u hu ho
    obtain ⟨j, hj⟩ := hζg u hu
    have h4 : u ^ 4 = 1 := by
      rw [hj, ← pow_mul, mul_comm j 4, pow_mul, ← hζ4, pow_orderOf_eq_one, one_pow]
    have hdvd : orderOf u ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr h4
    have h4' : orderOf u ∣ 2 * 2 := by simpa using hdvd
    have hc : Nat.Coprime (orderOf u) 2 := ho.coprime_two_right
    have h2 : orderOf u ∣ 2 := (hc.dvd_mul_left (m := 2) (n := 2)).mp h4'
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2eq
    · exact orderOf_eq_one_iff.mp h1
    · rw [h2eq] at ho
      exact absurd ho (by decide)
  have hmu : ∀ u ∈ (ρ.comp α).ker, u * u = 1 → u = 1 ∨ u = m := by
    intro u hu huu
    obtain ⟨k, hk⟩ := hζg u hu
    rw [hk] at huu ⊢
    have hpow : ζ ^ (2 * k) = 1 := by
      rw [mul_comm 2 k, pow_mul, pow_two]
      exact huu
    have hdvd : orderOf ζ ∣ 2 * k := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rw [hζ4] at hdvd
    obtain ⟨t, ht⟩ := hdvd
    have hk2 : k = 2 * t := by omega
    rw [hk2, pow_mul]
    change m ^ t = 1 ∨ m ^ t = m
    rcases Nat.even_or_odd t with ht_even | ht_odd
    · left
      obtain ⟨s, hs⟩ := even_iff_exists_two_mul.mp ht_even
      rw [hs, pow_mul, hm2sq, one_pow]
    · right
      obtain ⟨s, hs⟩ := odd_iff_exists_bit1.mp ht_odd
      rw [hs, pow_succ, pow_mul, hm2sq, one_pow, one_mul]
  obtain ⟨hP1, hP2, hP3⟩ :=
    l2_pauli_transfer α hα ρ hρk hH2 hE hP hm1 hm2 hmk hmu hcen
  have hμs : Function.Surjective (ρ.comp α) := hρs.comp hα
  obtain ⟨a₁, b₁, a₂, b₂, ha₁, hb₁, ha₂, hb₂, -, -, -, -, -, -, hgen⟩ :=
    l2_symp_basis (ρ.comp α) hμs hE hmcen hm1 hm2 hcen hP1 hP2
  have hsq_lift : ∀ a : E, (ρ.comp α) a ∈ A → a * a = 1 ∨ a * a = m := by
    intro a ha
    obtain ⟨x, hx, k, hk, hko, hksq⟩ := hP3 ((ρ.comp α) a) ha
    have hk1 : k = 1 := hker_odd k hk hko
    have hx_sq : x * x = 1 ∨ x * x = m := by
      rcases hksq with h | h
      · left; rw [h, hk1]
      · right; rw [h, hk1, mul_one]
    have hmem : a * x⁻¹ ∈ (ρ.comp α).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx]
      simp
    have hc_sq : (a * x⁻¹) * (a * x⁻¹) = 1 ∨ (a * x⁻¹) * (a * x⁻¹) = m :=
      hker_sq _ hmem
    have hcx : (a * x⁻¹) * x = x * (a * x⁻¹) := hcen _ hmem x
    have hcxa : (a * x⁻¹) * x = a := by group
    have haa : a * a = ((a * x⁻¹) * (a * x⁻¹)) * (x * x) := by
      calc a * a = ((a * x⁻¹) * x) * ((a * x⁻¹) * x) := by rw [hcxa]
        _ = ((a * x⁻¹) * (a * x⁻¹)) * (x * x) := by
              have h2 := (show Commute (a * x⁻¹) x from hcx).mul_pow 2
              simpa only [pow_two] using h2
    rcases hc_sq with hc | hc <;> rcases hx_sq with hx1 | hx1
    · exact Or.inl (by rw [haa, hc, hx1, one_mul])
    · exact Or.inr (by rw [haa, hc, hx1, one_mul])
    · exact Or.inr (by rw [haa, hc, hx1, mul_one])
    · exact Or.inl (by rw [haa, hc, hx1, hm2])
  have hθζker : θ ζ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    exact (DFunLike.congr_fun hθ ζ).trans (MonoidHom.mem_ker.mp hζk)
  have hθm : θ m = 1 := by
    dsimp only [m]
    rw [pow_two, map_mul]
    exact hπ2 (θ ζ) hθζker
  have hsq_θ : ∀ a : E, (ρ.comp α) a ∈ A → θ a * θ a = 1 := by
    intro a ha
    rcases hsq_lift a ha with h | h
    · rw [← map_mul, h, map_one]
    · rw [← map_mul, h, hθm]
  let lift : Fin 4 → E := ![a₁, b₁, a₂, b₂]
  have hmemlift : ∀ i, (ρ.comp α) (lift i) ∈ A := by
    intro i
    fin_cases i
    · simpa [lift] using ha₁
    · simpa [lift] using hb₁
    · simpa [lift] using ha₂
    · simpa [lift] using hb₂
  refine ⟨fun i => θ (lift i), ?_, ?_, ?_⟩
  · intro i
    exact hsq_θ (lift i) (hmemlift i)
  · intro i j
    have hc := hP1 (lift i) (lift j) (hmemlift i) (hmemlift j)
    have h : ⁅θ (lift i), θ (lift j)⁆ = 1 := by
      rw [← map_commutatorElement]
      rcases hc with h | h
      · rw [h, map_one]
      · rw [h, hθm]
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  · intro d hd a ha
    obtain ⟨x, hx⟩ := hμs a
    have hxgen : x ∈ Subgroup.closure (({a₁, b₁, a₂, b₂} : Set E) ∪ ((ρ.comp α).ker : Set E)) := by
      apply hgen
      rw [hx]
      exact ha
    have hylift : ∀ i, (ρ.comp α) (lift i) * π d = π d * (ρ.comp α) (lift i) := by
      intro i
      have hdi : θ (lift i) * d = d * θ (lift i) := hd i
      have hθl : π (θ (lift i)) = (ρ.comp α) (lift i) := by
        have h := DFunLike.congr_fun hθ (lift i)
        simpa [MonoidHom.comp_apply] using h
      calc (ρ.comp α) (lift i) * π d
          = π (θ (lift i)) * π d := by rw [← hθl]
        _ = π (θ (lift i) * d) := by rw [← map_mul]
        _ = π (d * θ (lift i)) := by rw [hdi]
        _ = π d * π (θ (lift i)) := by rw [map_mul]
        _ = π d * (ρ.comp α) (lift i) := by rw [hθl]
    have hcomm_gen : ∀ z ∈ ({a₁, b₁, a₂, b₂} : Set E),
        (ρ.comp α) z * π d = π d * (ρ.comp α) z := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [lift] using hylift 0
      · simpa [lift] using hylift 1
      · simpa [lift] using hylift 2
      · simpa [lift] using hylift 3
    have hle : Subgroup.closure (({a₁, b₁, a₂, b₂} : Set E) ∪ ((ρ.comp α).ker : Set E)) ≤
        (Subgroup.centralizer ({π d} : Set S)).comap (ρ.comp α) := by
      rw [Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rcases hz with hz | hz
      · exact (hcomm_gen z hz).symm
      · rw [MonoidHom.mem_ker.mp hz]
        simp
    have hmem : (ρ.comp α) x ∈ Subgroup.centralizer ({π d} : Set S) := by
      have := hle hxgen
      rwa [Subgroup.mem_comap] at this
    have hres := (Subgroup.mem_centralizer_iff.mp hmem) (π d) (Set.mem_singleton (π d))
    rw [hx] at hres
    exact hres.symm

end CFSG.OddStandard.HigherRank.YamadaG23
