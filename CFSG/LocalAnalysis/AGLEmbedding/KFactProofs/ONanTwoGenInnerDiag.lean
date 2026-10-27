module

public import CFSG.Assembly.LowTwoRankDefs
import CFSG.RankThree.CentralCover.SteinbergBNLinearSplitPrime

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)

theorem dvd_card_of_psl_diag {T : Type} [Group T] [Finite T] {p n ℓ f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hmod : StatedClassicalModel T .PSL n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f - 1) : p ∣ Nat.card T := by
  classical
  obtain ⟨⟨hℓ, hf, hn2, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd (by omega) hpn)
  have := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hchar : CharP k ℓ := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hk])
  have hpk : p ∣ Fintype.card k - 1 := by rwa [← Nat.card_eq_fintype_card, hk]
  let ψ : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm
  let φ : (⊤ : Subgroup T) →* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    ψ.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom
  have hφs : Function.Surjective φ := ψ.surjective.comp Subgroup.topEquiv.surjective
  have hker : φ.ker ≤ Subgroup.center (⊤ : Subgroup T) := by
    intro x hx
    have hx' : φ x = 1 := hx
    have : x = 1 := (ψ.injective.comp Subgroup.topEquiv.injective) (by simpa [φ] using hx')
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨u, -, hu, V, hV, hVab, hVcard, -⟩ :=
    CFSG.RankThree.CentralCover.linear_split_prime_central_cover_two_local_rank (⊤ : Subgroup T)
      hℓ hp (by omega) hpk (by omega) φ hφs hker
  have hr : 1 ≤ (if ℓ = 2 then n - 2 - (if p ∣ n then 1 else 0) else
      n - 1 - (if p ∣ n then 1 else 0)) := by
    simp only [hpn, ↓reduceIte]
    split_ifs <;> omega
  have h1 : p ∣ Nat.card V := by
    rw [hVcard]
    exact dvd_pow_self p (by omega)
  exact h1.trans (Subgroup.card_subgroup_dvd_card V)

theorem dvd_card_of_psu_diag {T : Type} [Group T] [Finite T] {p n ℓ f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hmod : StatedClassicalModel T .PSU n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f + 1) : p ∣ Nat.card T := by
  classical
  obtain ⟨⟨hℓ, hf, hn3, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd (by omega) hpn)
  have hU : UnitaryFieldData ℓ f k := ⟨hℓ, hf, by rw [hk, ← pow_mul, mul_comm]⟩
  let ψ : T ≃* unitaryPSU hU n := e.trans (unitaryPSUEquiv hU (by omega)).symm
  let φ : (⊤ : Subgroup T) →* unitaryPSU hU n := ψ.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom
  have hφs : Function.Surjective φ := ψ.surjective.comp Subgroup.topEquiv.surjective
  have hker : φ.ker ≤ Subgroup.center (⊤ : Subgroup T) := by
    intro x hx
    have hx' : φ x = 1 := hx
    have : x = 1 := (ψ.injective.comp Subgroup.topEquiv.injective) (by simpa [φ] using hx')
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨u, -, hu, V, hV, hVab, hVcard⟩ :=
    CFSG.RankThree.Classical2.unitary_split_prime_central_cover_two_local_rank (⊤ : Subgroup T)
      hU hp (by omega) hpq (by omega) φ hφs hker
  have hr : 1 ≤ (if ℓ = 2 then n - 2 - (if p ∣ n then 1 else 0) else
      n - 1 - (if p ∣ n then 1 else 0)) := by
    simp only [hpn, ↓reduceIte]
    split_ifs <;> omega
  have h1 : p ∣ Nat.card V := by
    have hVc : Nat.card V = p ^ (if ℓ = 2 then n - 2 - (if p ∣ n then 1 else 0) else
        n - 1 - (if p ∣ n then 1 else 0)) := hVcard
    rw [hVc]
    exact dvd_pow_self p (by omega)
  exact h1.trans (Subgroup.card_subgroup_dvd_card V)

theorem not_dvd_gcd_psl_of_not_dvd_card {T : Type} [Group T] [Finite T] {p n ℓ f : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hmod : StatedClassicalModel T .PSL n ℓ f)
    (hT : ¬ p ∣ Nat.card T) : ¬ p ∣ Nat.gcd n (ℓ ^ f - 1) := fun h =>
  hT (dvd_card_of_psl_diag hp hp5 hmod (h.trans (Nat.gcd_dvd_left _ _))
    (h.trans (Nat.gcd_dvd_right _ _)))

theorem not_dvd_gcd_psu_of_not_dvd_card {T : Type} [Group T] [Finite T] {p n ℓ f : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hmod : StatedClassicalModel T .PSU n ℓ f)
    (hT : ¬ p ∣ Nat.card T) : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := fun h =>
  hT (dvd_card_of_psu_diag hp hp5 hmod (h.trans (Nat.gcd_dvd_left _ _))
    (h.trans (Nat.gcd_dvd_right _ _)))

end CFSG.AGLEmbedding.TwoGenInner
