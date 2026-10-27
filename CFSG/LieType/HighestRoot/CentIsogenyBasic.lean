module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LieType.HighestRoot

variable {G C : Type*} [Group G] [Group C] {p : ℕ} [hp : Fact p.Prime]

theorem mem_of_mul_mem_center {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G)
    (hpZ : ¬ p ∣ Nat.card Z) {H : Subgroup G} {j c : G} (hj : j ∈ H) (hc : c ∈ Z) {n : ℕ}
    (hn : (j * c) ^ (p ^ n) = 1) : j * c ∈ H := by
  have hcomm : Commute j c := (Subgroup.mem_center_iff.1 (hZ hc) j)
  rw [hcomm.mul_pow] at hn
  have hcp : c ^ (p ^ n) ∈ H := by
    rw [eq_inv_of_mul_eq_one_right hn]
    exact inv_mem (pow_mem hj _)
  have hcop : (p ^ n).Coprime (orderOf c) := by
    refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun h => hpZ ?_)
    exact h.trans (Subgroup.orderOf_dvd_natCard Z hc)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hcH : c ∈ H := by
    rw [← hm]
    exact pow_mem hcp m
  exact mul_mem hj hcH

variable (θ : G →* C)

theorem mem_of_map_mem (hker : θ.ker ≤ Subgroup.center G) (hpk : ¬ p ∣ Nat.card θ.ker)
    {H : Subgroup G} {y : G} (hy : θ y ∈ H.map θ) {n : ℕ} (hn : y ^ (p ^ n) = 1) : y ∈ H := by
  obtain ⟨j, hj, hjy⟩ := hy
  have hc : j⁻¹ * y ∈ θ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hjy, inv_mul_cancel]
  have e : y = j * (j⁻¹ * y) := by group
  rw [e] at hn ⊢
  exact mem_of_mul_mem_center hker hpk hj hc hn

theorem le_of_map_le_of_isPGroup (hker : θ.ker ≤ Subgroup.center G) (hpk : ¬ p ∣ Nat.card θ.ker)
    {P H : Subgroup G} (hP : IsPGroup p P) (hPH : P.map θ ≤ H.map θ) : P ≤ H := by
  intro y hy
  obtain ⟨n, hn⟩ := hP ⟨y, hy⟩
  exact mem_of_map_mem θ hker hpk (hPH ⟨y, hy, rfl⟩) (n := n)
    (by simpa using congrArg Subtype.val hn)

theorem le_centralizer_of_map_commute (hker : θ.ker ≤ Subgroup.center G)
    (hpk : ¬ p ∣ Nat.card θ.ker) {P : Subgroup G} (hP : IsPGroup p P) {z : G}
    (hz : ∀ x ∈ P, θ x * θ z = θ z * θ x) : P ≤ Subgroup.centralizer ({z} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  have hxn : x ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
  set c := z * x * z⁻¹ * x⁻¹ with hc_def
  have hc : c ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hc_def, map_mul, map_mul, map_mul, map_inv, map_inv, ← hz x hx]
    group
  have hcx : z * x * z⁻¹ = c * x := by rw [hc_def]; group
  have hcomm : Commute c x := (Subgroup.mem_center_iff.1 (hker hc) x).symm
  have hcn : c ^ (p ^ n) = 1 := by
    have h1 : (z * x * z⁻¹) ^ (p ^ n) = 1 := by rw [conj_pow, hxn]; group
    rwa [hcx, hcomm.mul_pow, hxn, mul_one] at h1
  have hcop : (p ^ n).Coprime (Nat.card θ.ker) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpk)
  have h1 : orderOf c ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcn) (Subgroup.orderOf_dvd_natCard _ hc)
  have hc1 : c = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  calc x * z = (z * x * z⁻¹ * x⁻¹)⁻¹ * (z * x) := by group
    _ = z * x := by rw [← hc_def, hc1, inv_one, one_mul]

theorem centralizer_le_normalizer_of_map (hker : θ.ker ≤ Subgroup.center G)
    (hpk : ¬ p ∣ Nat.card θ.ker) {A B : Subgroup G} (hA : IsPGroup p A) (hB : IsPGroup p B)
    {z : G} (hCZ : Subgroup.centralizer ({θ z} : Set C) ≤
      Subgroup.normalizer (((A ⊔ B).map θ : Subgroup C) : Set C)) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ h ∈ A ⊔ B, g * h * g⁻¹ ∈ A ⊔ B := by
    intro g hg
    have hθg : θ g ∈ Subgroup.normalizer (((A ⊔ B).map θ : Subgroup C) : Set C) := by
      refine hCZ (Subgroup.mem_centralizer_singleton_iff.2 ?_)
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hg]
    have hconj : ∀ P : Subgroup G, P ≤ A ⊔ B → IsPGroup p P →
        P.map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
      intro P hPle hP
      refine le_of_map_le_of_isPGroup θ hker hpk (hP.map _) ?_
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have h := (Subgroup.mem_normalizer_iff.1 hθg (θ x)).1 ⟨x, hPle hx, rfl⟩
      simpa [map_mul, map_inv] using h
    have hle : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
      rw [Subgroup.map_sup]
      exact sup_le (hconj A le_sup_left hA) (hconj B le_sup_right hB)
    intro h hh
    exact hle ⟨h, hh, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have h' := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using h'

end CFSG.LieType.HighestRoot
