module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Core
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtExact

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem exists_langSetup_of_inner_untw_of_prime {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀K : ¬ p₀ ∣ Nat.card K) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ Nat.card K)
    (hmon : MonomialToralAt τ p)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤)
    (β : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹) (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p₀) (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have hqK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L ℓ (f : ℕ) c = c ^ Nat.card K := fun c => by
    rw [hqK]
    exact iterateFrobenius_def ℓ (f : ℕ) c
  have hFix : ∀ y : ModGL τ K,
      entrywiseFrobGL τ L ℓ (f : ℕ) (baseChangeGL ι₁ y) = baseChangeGL ι₁ y := by
    intro y
    have hcomp : (iterateFrobenius L ℓ (f : ℕ)).comp ι₁ = ι₁ := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ f) (ι₁ c) = ι₁ c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hf]
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hℓp : ℓ ≠ p := by
    intro h
    apply hpK
    rw [hqK, h]
    exact dvd_pow_self p (by omega)
  have hpq : Nat.Coprime p (ℓ ^ (f : ℕ)) := (Nat.Prime.coprime_iff_not_dvd hp).2 (hqK ▸ hpK)
  set u : ModGL τ L := baseChangeGL ι₁ h with hu
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon hℓp
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) hhL hup
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_untw (f : ℕ) hf1 hpq hup (hFix h) hconj
  set ι₀ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι₁).comp (adjointGroup τ K).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hd : LangDescent D 7 ι₀ := by
    rcases hτ with h' | h' | h' | h' | h'
    · exact langDescent_exact (Or.inl h') hFr D hΦ hperf
    · exact langDescent_exact (Or.inr h') hFr D hΦ hperf
    · exact langDescent_untw 3 (Or.inl ⟨h', rfl⟩) hFr D hΦ Nat.prime_seven (by norm_num) hperf
    · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h', rfl⟩)) hFr D hΦ Nat.prime_seven
        (by norm_num) hperf
    · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h', rfl⟩)) hFr D hΦ Nat.prime_seven
        (by norm_num) hperf
  have hβ' : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (β c : ModGL τ K) = baseChangeGL ι₁ h *
      baseChangeGL ι₁ (c : ModGL τ K) * (baseChangeGL ι₁ h)⁻¹
    rw [hβ c, map_mul, map_mul, map_inv]
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq, ← hqK]
    exact hq₀
  have hℓp₀ : ℓ ≠ p₀ := by
    intro h
    apply hp₀K
    rw [hqK, h]
    exact dvd_pow_self p₀ (by omega)
  obtain ⟨S, a, ι, rfl, hT, hap, h1, hinj, hrange, hconjι⟩ :=
    exists_langSetup_of_toral_datum_of_prime hℓ hf1 D hDq hp₀ hℓp₀.symm hq' hd.finite_model ι₀
      hι₀inj hd.Γ_eq β hβ' hmem hup hu1
  exact ⟨S, a, ι, hDq.trans hqK.symm, ⟨iterateFrobenius L ℓ (f : ℕ), hFr, hΦ⟩, hT, hap, h1,
    hinj, hrange, hconjι⟩

theorem exists_langSetup_of_inner_untw {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (hq : 5 ≤ p ∨ 4 ≤ Nat.card K) (hmon : MonomialToralAt τ p)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤)
    (β : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹) (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) p) (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ :=
  exists_langSetup_of_inner_untw_of_prime hτ hp hpK hp hpK hq hmon hperf β h hhL hβ hp1 hh1

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
