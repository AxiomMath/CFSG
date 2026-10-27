module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCG
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveN
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixGenBase
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem exists_pow_prime_pow_eq_map {G P : Type*} [Group G] [Finite G] [Group P] {p : ℕ}
    (hp : p.Prime) (f : G →* P) (x : G) (hfx : orderOf (f x) = p) :
    ∃ k : ℕ, (∃ a : ℕ, orderOf (x ^ k) = p ^ a) ∧ f (x ^ k) = f x := by
  obtain ⟨a, m, hmp, hxm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  have hcop : Nat.Coprime m p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hmp)
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨m * j, ?_, ?_⟩
  · have h1 : (x ^ (m * j)) ^ p ^ a = 1 := by
      rw [← pow_mul, show m * j * p ^ a = p ^ a * m * j by ring, pow_mul, ← hxm,
        pow_orderOf_eq_one, one_pow]
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨b, hb⟩
  · rw [map_pow, ← pow_mod_orderOf, hfx, hj, pow_one]

theorem exists_five_pair_of_card_support_le_four {w : Perm (Fin 9)} (hw2 : w * w = 1)
    (hw4 : w.support.card ≤ 4) :
    ∃ π₁ π₂ : Perm (Fin 9), π₁ ∈ alternatingGroup (Fin 9) ∧ π₂ ∈ alternatingGroup (Fin 9) ∧
      π₁ * w = w * π₁ ∧ π₂ * w = w * π₂ ∧ orderOf π₁ = 5 ∧ orderOf π₂ = 5 ∧
      π₁ * π₂ ≠ 1 ∧ π₁ * π₂ * (π₁ * π₂) = 1 := by
  classical
  set c₁ : Perm (Fin 9) := SixGen.permOf [(0, 1), (1, 2), (2, 3), (3, 4)] with hc₁def
  set c₂ : Perm (Fin 9) := SixGen.permOf [(0, 1), (1, 2), (2, 4), (4, 3)] with hc₂def
  have hc₁5 : orderOf c₁ = 5 := orderOf_eq_prime (by decide) (by decide)
  have hc₂5 : orderOf c₂ = 5 := orderOf_eq_prime (by decide) (by decide)
  have hc₁A : c₁ ∈ alternatingGroup (Fin 9) := by rw [Perm.mem_alternatingGroup]; decide
  have hc₂A : c₂ ∈ alternatingGroup (Fin 9) := by rw [Perm.mem_alternatingGroup]; decide
  have hc₁₂1 : c₁ * c₂ ≠ 1 := by decide
  have hc₁₂2 : c₁ * c₂ * (c₁ * c₂) = 1 := by decide
  have hstd : ∀ w₀ : Perm (Fin 9), w₀ = 1 ∨ w₀ = SixGen.permOf [(5, 6)] ∨
      w₀ = SixGen.permOf [(5, 6), (7, 8)] →
      c₁ * w₀ = w₀ * c₁ ∧ c₂ * w₀ = w₀ * c₂ := by
    rintro w₀ (rfl | rfl | rfl) <;> exact ⟨by decide, by decide⟩
  have hev : 2 ∣ w.support.card :=
    two_dvd_card_support_of_pow_two_pow (k := 1) (by rw [pow_one, sq]; exact hw2)
  obtain ⟨w₀, hw₀, π, hπ⟩ : ∃ w₀ : Perm (Fin 9), (w₀ = 1 ∨ w₀ = SixGen.permOf [(5, 6)] ∨
      w₀ = SixGen.permOf [(5, 6), (7, 8)]) ∧ ∃ π : Perm (Fin 9), π * w₀ * π⁻¹ = w := by
    rcases (by omega : w.support.card = 0 ∨ w.support.card = 2 ∨ w.support.card = 4) with
      h0 | h2 | h4
    · refine ⟨1, Or.inl rfl, 1, ?_⟩
      rw [Finset.card_eq_zero, Perm.support_eq_empty_iff] at h0
      rw [h0]; group
    · have hct : w.cycleType = (SixGen.permOf [(5, 6)]).cycleType := by
        rw [SixGen.cycleType_of_mul_self (k := 1) hw2 (by norm_num) h2,
          SixGen.cycleType_of_mul_self (k := 1) (by decide) (by norm_num) (by decide)]
      obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct.symm)
      exact ⟨_, Or.inr (Or.inl rfl), π, hπ⟩
    · have hct : w.cycleType = (SixGen.permOf [(5, 6), (7, 8)]).cycleType := by
        rw [SixGen.cycleType_of_mul_self (k := 2) hw2 (by norm_num) h4,
          SixGen.cycleType_of_mul_self (k := 2) (by decide) (by norm_num) (by decide)]
      obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct.symm)
      exact ⟨_, Or.inr (Or.inr rfl), π, hπ⟩
  obtain ⟨h₁, h₂⟩ := hstd w₀ hw₀
  have hconj_ord : ∀ c : Perm (Fin 9), orderOf (π * c * π⁻¹) = orderOf c := fun c => by
    have := orderOf_injective (MulAut.conj π).toMonoidHom (MulAut.conj π).injective c
    simpa using this
  refine ⟨π * c₁ * π⁻¹, π * c₂ * π⁻¹, (alternatingGroup.normal (α := Fin 9)).conj_mem _ hc₁A π,
    (alternatingGroup.normal (α := Fin 9)).conj_mem _ hc₂A π, ?_, ?_, by rw [hconj_ord, hc₁5],
    by rw [hconj_ord, hc₂5], ?_, ?_⟩
  · rw [← hπ]
    calc π * c₁ * π⁻¹ * (π * w₀ * π⁻¹) = π * (c₁ * w₀) * π⁻¹ := by group
      _ = π * (w₀ * c₁) * π⁻¹ := by rw [h₁]
      _ = π * w₀ * π⁻¹ * (π * c₁ * π⁻¹) := by group
  · rw [← hπ]
    calc π * c₂ * π⁻¹ * (π * w₀ * π⁻¹) = π * (c₂ * w₀) * π⁻¹ := by group
      _ = π * (w₀ * c₂) * π⁻¹ := by rw [h₂]
      _ = π * w₀ * π⁻¹ * (π * c₂ * π⁻¹) := by group
  · intro h
    apply hc₁₂1
    have h' : π * (c₁ * c₂) * π⁻¹ = 1 := by
      rw [← h]; group
    have := congrArg (fun z => π⁻¹ * z * π) h'
    simpa [mul_assoc] using this
  · calc π * c₁ * π⁻¹ * (π * c₂ * π⁻¹) * (π * c₁ * π⁻¹ * (π * c₂ * π⁻¹)) =
        π * (c₁ * c₂ * (c₁ * c₂)) * π⁻¹ := by group
      _ = 1 := by rw [hc₁₂2]; group

namespace Sig36

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem five_le_card_support_of_centralizer_le (S : Sig36 X t J 9 e E D)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M H : Subgroup X} (hJM : J ≤ M)
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ)
    (hHN : H ≤ normalizer (M : Set X)) {N : Subgroup X}
    (hNK : N ≤ H ⊓ UnbalancedLayer.coreActionKernel M)
    (hNodd : ∀ k ∈ H ⊓ UnbalancedLayer.coreActionKernel M, k ∈ N ↔ Odd (orderOf k))
    {s g : X} (hgs : g⁻¹ * t * g = s) (hsH : s ∈ H)
    (hs2 : ρ ⟨s, hHN hsH⟩ * ρ ⟨s, hHN hsH⟩ = 1) (hs8 : (ρ ⟨s, hHN hsH⟩).support.card = 8)
    {r : X} (hr2 : r * r = 1) (hrs : r * s = s * r) (hCr : centralizer ({r} : Set X) ≤ H)
    (hrN : g * r * g⁻¹ ∈ normalizer (M : Set X)) :
    5 ≤ (ρ ⟨g * r * g⁻¹, hrN⟩).support.card := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_contra h5
  push Not at h5
  generalize hr'def : g * r * g⁻¹ = r' at hrN h5
  have hts : t = g * s * g⁻¹ := by rw [← hgs]; group
  have hr't : r' * t = t * r' := by
    rw [hts, ← hr'def]
    calc g * r * g⁻¹ * (g * s * g⁻¹) = g * (r * s) * g⁻¹ := by group
      _ = g * (s * r) * g⁻¹ := by rw [hrs]
      _ = g * s * g⁻¹ * (g * r * g⁻¹) := by group
  have hr'2 : r' * r' = 1 := by
    rw [← hr'def]
    calc g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hr'J : r' ∈ normalizer (J : Set X) :=
    S.centralizer_le_normalizer hT13 hML hSch (mem_centralizer_singleton_iff.mpr hr't)
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) e
  have hsupp := card_support_rho_eq_rhoJ (by norm_num) hJM hsup hρ hρJ hr'J hrN
  obtain ⟨w, hwdef⟩ : ∃ w, ρJ ⟨r', hr'J⟩ = w := ⟨_, rfl⟩
  have hw2 : w * w = 1 := by
    rw [← hwdef, ← map_mul]
    have h1 : (⟨r', hr'J⟩ : ↥(normalizer (J : Set X))) * ⟨r', hr'J⟩ = 1 := Subtype.ext hr'2
    rw [h1, map_one]
  have hw4 : w.support.card ≤ 4 := by rw [← hwdef, ← hsupp]; omega
  obtain ⟨π₁, π₂, hπ₁A, hπ₂A, hπ₁w, hπ₂w, hπ₁5, hπ₂5, h12, h122⟩ :=
    exists_five_pair_of_card_support_le_four hw2 hw4
  set B := zpowers r' with hBdef
  have hBN : B ≤ normalizer (J : Set X) := zpowers_le.mpr hr'J
  have hB2 : IsPGroup 2 B := isPGroup_zpowers_of_mul_self hr'2
  have hcommB : ∀ π : Perm (Fin 9), π * w = w * π →
      ∀ (y : X) (hy : y ∈ B), π * ρJ ⟨y, hBN hy⟩ = ρJ ⟨y, hBN hy⟩ * π := by
    intro π hπ y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have h1 : (⟨r' ^ k, hBN hy⟩ : ↥(normalizer (J : Set X))) = ⟨r', hr'J⟩ ^ k :=
      Subtype.ext (by simp)
    rw [h1, map_zpow, hwdef]
    exact ((Commute.zpow_right (show Commute π w from hπ) k)).eq
  let fJ : ↥J →* Perm (Fin 9) := ρJ.comp (Subgroup.inclusion le_normalizer)
  have hlift : ∀ π : Perm (Fin 9), π ∈ alternatingGroup (Fin 9) → π * w = w * π →
      orderOf π = 5 → ∃ x : X, ∃ hxJ : x ∈ J, x ∈ centralizer (B : Set X) ∧
        (∃ a : ℕ, orderOf x = 5 ^ a) ∧ ρJ ⟨x, le_normalizer hxJ⟩ = π := by
    intro π hπA hπw hπ5
    obtain ⟨x₁, hx₁B, hx₁e⟩ := hρJ.exists_lift_of_isPGroup hBN hB2 (b := ⟨π, hπA⟩)
      (hcommB π hπw)
    have hfx₁ : fJ x₁ = π := by
      change ρJ ⟨x₁, le_normalizer x₁.2⟩ = π
      rw [hρJ.apply_of_mem (by norm_num) x₁, hx₁e]
    obtain ⟨k, ⟨a, hxa⟩, hxk⟩ :=
      exists_pow_prime_pow_eq_map (p := 5) (by norm_num) fJ x₁ (by rw [hfx₁, hπ5])
    refine ⟨((x₁ ^ k : ↥J) : X), (x₁ ^ k).2, ?_, ⟨a, by rw [Subgroup.orderOf_coe, hxa]⟩, ?_⟩
    · rw [Subgroup.coe_pow]
      exact pow_mem hx₁B k
    · change fJ (x₁ ^ k) = π
      rw [hxk, hfx₁]
  obtain ⟨x₁, hx₁J, hx₁B, hx₁a, hx₁ρ⟩ := hlift π₁ hπ₁A hπ₁w hπ₁5
  obtain ⟨x₂, hx₂J, hx₂B, hx₂a, hx₂ρ⟩ := hlift π₂ hπ₂A hπ₂w hπ₂5
  set σ := ρ ⟨s, hHN hsH⟩ with hσdef
  have hcardC : Nat.card (centralizer ({σ} : Set (Perm (Fin 9)))) = 384 := by
    rw [Perm.nat_card_centralizer, SixGen.cycleType_of_mul_self (k := 4) hs2 (by norm_num) hs8]
    simp
    decide
  have hconjord : ∀ y : X, orderOf (g⁻¹ * y * g) = orderOf y := fun y => by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y
    simpa using this
  have hdown : ∀ x : X, x ∈ J → x ∈ centralizer (B : Set X) → (∃ a : ℕ, orderOf x = 5 ^ a) →
      g⁻¹ * x * g ∈ N := by
    rintro x hxJ hxB ⟨a, hxa⟩
    have hxr' : x * r' = r' * x :=
      (mem_centralizer_iff.mp hxB r' (mem_zpowers r')).symm
    have hxr : g⁻¹ * x * g ∈ centralizer ({r} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have hr : r = g⁻¹ * r' * g := by rw [← hr'def]; group
      rw [hr]
      calc g⁻¹ * x * g * (g⁻¹ * r' * g) = g⁻¹ * (x * r') * g := by group
        _ = g⁻¹ * (r' * x) * g := by rw [hxr']
        _ = g⁻¹ * r' * g * (g⁻¹ * x * g) := by group
    have hxH := hCr hxr
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (S.pair.1.2.1 hxJ)
    have hxs : g⁻¹ * x * g * s = s * (g⁻¹ * x * g) := by
      rw [← hgs]
      calc g⁻¹ * x * g * (g⁻¹ * t * g) = g⁻¹ * (x * t) * g := by group
        _ = g⁻¹ * (t * x) * g := by rw [hxt]
        _ = g⁻¹ * t * g * (g⁻¹ * x * g) := by group
    have hord : orderOf (g⁻¹ * x * g) = 5 ^ a := by rw [hconjord, hxa]
    have hρ1 : ρ ⟨g⁻¹ * x * g, hHN hxH⟩ = 1 := by
      set y := ρ ⟨g⁻¹ * x * g, hHN hxH⟩ with hydef
      have hyC : y ∈ centralizer ({σ} : Set (Perm (Fin 9))) := by
        rw [mem_centralizer_singleton_iff, hydef, hσdef, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hxs
      have h1 : orderOf y ∣ 5 ^ a := by
        rw [← hord]
        exact (orderOf_map_dvd ρ _).trans (by rw [Subgroup.orderOf_mk])
      have h2 : orderOf y ∣ 384 := by
        rw [← hcardC]
        have := Subgroup.orderOf_dvd_natCard (centralizer ({σ} : Set (Perm (Fin 9)))) hyC
        exact this
      have h3 : Nat.Coprime (5 ^ a) 384 := Nat.Coprime.pow_left a (by norm_num)
      exact orderOf_eq_one_iff.mp
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h3) h2)
    refine (hNodd _ ⟨hxH, hρ.mem_coreActionKernel _ hρ1⟩).mpr ?_
    rw [hord]
    exact Odd.pow (by decide)
  have hy := N.mul_mem (hdown x₁ hx₁J hx₁B hx₁a) (hdown x₂ hx₂J hx₂B hx₂a)
  have hyK := hNK hy
  have hodd := (hNodd _ hyK).mp hy
  rw [show g⁻¹ * x₁ * g * (g⁻¹ * x₂ * g) = g⁻¹ * (x₁ * x₂) * g by group, hconjord] at hodd
  have hx12J : x₁ * x₂ ∈ J := J.mul_mem hx₁J hx₂J
  have hρ12 : ρJ ⟨x₁ * x₂, le_normalizer hx12J⟩ = π₁ * π₂ := by
    have h1 : (⟨x₁ * x₂, le_normalizer hx12J⟩ : ↥(normalizer (J : Set X))) =
        ⟨x₁, le_normalizer hx₁J⟩ * ⟨x₂, le_normalizer hx₂J⟩ := rfl
    rw [h1, map_mul, hx₁ρ, hx₂ρ]
  have hord2 : orderOf (π₁ * π₂) = 2 := orderOf_eq_prime (by rw [sq]; exact h122) h12
  have hdvd : orderOf (π₁ * π₂) ∣ orderOf (x₁ * x₂) := by
    rw [← hρ12]
    exact (orderOf_map_dvd ρJ _).trans (by rw [Subgroup.orderOf_mk])
  rw [hord2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end Sig36

end CFSG.ComponentClassification.SolMax
