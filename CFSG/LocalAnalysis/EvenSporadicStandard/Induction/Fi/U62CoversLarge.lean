module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.SylowChar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.YS14
open scoped Pointwise

@[expose] def IsLargeInvAt {T : Type*} [Group T] (n : ℕ) (x : T) : Prop :=
  x * x = 1 ∧ x ≠ 1 ∧ 2 ^ n ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set T))

@[expose] def largeCentralizer (n : ℕ) (T : Type*) [Group T] : Subgroup T :=
  Subgroup.centralizer {x : T | IsLargeInvAt n x}

theorem mulEquiv_isLargeInvAt_iff {A B : Type*} [Group A] [Group B] (n : ℕ) (e : A ≃* B)
    (a : A) : IsLargeInvAt n a ↔ IsLargeInvAt n (e a) := by
  have hsq : a * a = 1 ↔ e a * e a = 1 := by
    rw [← map_mul, e.map_eq_one_iff]
  have hne : a ≠ 1 ↔ e a ≠ 1 := by
    rw [Ne, Ne, e.map_eq_one_iff]
  have hc : Nat.card ↥(Subgroup.centralizer ({a} : Set A)) =
      Nat.card ↥(Subgroup.centralizer ({e a} : Set B)) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv e.toEquiv (fun x => ?_)
    show x ∈ Subgroup.centralizer ({a} : Set A) ↔ e x ∈ Subgroup.centralizer ({e a} : Set B)
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := congrArg e h
      rwa [map_mul, map_mul] at h'
    · intro h
      apply e.injective
      rw [map_mul, map_mul]
      exact h
  unfold IsLargeInvAt
  rw [hsq, hne, hc]

theorem largeCentralizer_char {T : Type*} [Group T] (n : ℕ) (ψ : T ≃* T) {u : T}
    (hu : u ∈ largeCentralizer n T) : ψ u ∈ largeCentralizer n T := by
  rw [largeCentralizer, Subgroup.mem_centralizer_iff] at hu ⊢
  intro x hx
  have hx' : IsLargeInvAt n (ψ.symm x) := (mulEquiv_isLargeInvAt_iff n ψ.symm x).1 hx
  have h := hu (ψ.symm x) hx'
  have h' := congrArg ψ h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'

theorem involutionFixesElem_of_sylow_char {K : Type*} [Group K] [Finite K] {T : Type*} [Group T]
    (E : Subgroup T) (hchar : ∀ ψ : T ≃* T, ∀ u ∈ E, ψ u ∈ E)
    (hiso : ∀ S : Sylow 2 K, Nonempty (↥(S : Subgroup K) ≃* T))
    (hsq : ∀ u ∈ E, u * u = 1) (hcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u)
    {k i : ℕ} (hcard : 2 ^ k ≤ Nat.card ↥E) (hi : 2 * i ≤ k + 1) :
    InvolutionFixesElem K (2 ^ i) := by
  classical
  intro α _ hαα
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSα⟩ := exists_sylow_two_fixed α hαα
  obtain ⟨φ⟩ := hiso S
  have hSsub : α • (S : Subgroup K) = (S : Subgroup K) := by
    rw [← Sylow.pointwise_smul_def, hSα]
  have hαS : ∀ x ∈ (S : Subgroup K), α x ∈ (S : Subgroup K) := by
    intro x hx
    have h := Subgroup.smul_mem_pointwise_smul x α (S : Subgroup K) hx
    rw [hSsub, MulAut.smul_def] at h
    exact h
  let ι : T →* K := (S : Subgroup K).subtype.comp φ.symm.toMonoidHom
  have hι : Function.Injective ι :=
    (Subgroup.subtype_injective (S : Subgroup K)).comp φ.symm.injective
  let ψ : T ≃* T := φ.symm.trans ((invAutRestrict hαα (S : Subgroup K) hαS).trans φ)
  have hψ : ∀ t : T, α (ι t) = ι (ψ t) := by
    intro t
    show α ((φ.symm t : ↥(S : Subgroup K)) : K) = ((φ.symm (ψ t) : ↥(S : Subgroup K)) : K)
    have : φ.symm (ψ t) = invAutRestrict hαα (S : Subgroup K) hαS (φ.symm t) := by
      simp only [ψ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [this]
    rfl
  let EK : Subgroup K := E.map ι
  have hEα : ∀ a ∈ EK, α a ∈ EK := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨ψ u, hchar ψ u hu, (hψ u).symm⟩
  have hαE : α • EK = EK := by
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MulAut.smul_def]
      exact hEα y hy
    · intro hx
      exact ⟨α x, hEα x hx, by rw [MulAut.smul_def, mulAut_apply_apply_of_mul_eq_one hαα]⟩
  have hE2 : ∀ a ∈ EK, a * a = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, hsq u hu, map_one]
  have hEc : ∀ a ∈ EK, ∀ b ∈ EK, a * b = b * a := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, hcomm u hu v hv]
  have hcardEK : Nat.card ↥EK = Nat.card ↥E := Subgroup.card_map_of_injective hι
  obtain ⟨C, hCα, hC2, hCc, hle⟩ := card_fixedSubgroup_ge α hαα EK hE2 hEc hαE
  have hCp : IsPGroup 2 ↥C := by
    rw [IsPGroup.iff_orderOf]
    intro g
    by_cases hg : g = 1
    · exact ⟨0, by simp [hg]⟩
    · refine ⟨1, ?_⟩
      have h2 : g ^ 2 = 1 := by
        rw [pow_two]
        exact Subtype.ext (hC2 g.1 g.2)
      rw [orderOf_eq_prime h2 hg]
      norm_num
  obtain ⟨n, hn⟩ := hCp.exists_card_eq
  rw [hn, hcardEK] at hle
  have hk : 2 ^ k ≤ 2 ^ n * 2 ^ n := le_trans hcard hle
  refine ⟨C, hCα, hC2, hCc, ?_⟩
  rw [hn]
  have hkn : k ≤ 2 * n := by
    by_contra h
    push Not at h
    have : 2 ^ n * 2 ^ n < 2 ^ k := by
      rw [← pow_add]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem involutionFixesElem_of_sylow_largeCentralizer {K : Type*} [Group K] [Finite K]
    {T : Type*} [Group T] (n : ℕ) (hiso : ∀ S : Sylow 2 K, Nonempty (↥(S : Subgroup K) ≃* T))
    (hsq : ∀ u ∈ largeCentralizer n T, u * u = 1)
    (hcomm : ∀ u ∈ largeCentralizer n T, ∀ v ∈ largeCentralizer n T, u * v = v * u)
    {k i : ℕ} (hcard : 2 ^ k ≤ Nat.card ↥(largeCentralizer n T)) (hi : 2 * i ≤ k + 1) :
    InvolutionFixesElem K (2 ^ i) :=
  involutionFixesElem_of_sylow_char (largeCentralizer n T)
    (fun ψ _ hu => largeCentralizer_char n ψ hu) hiso hsq hcomm hcard hi

end CFSG.EvenSporadicStandard.Induction.Fi
