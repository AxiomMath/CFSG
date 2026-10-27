module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Gen
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthPivot
import CFSG.ClassicalGroups.Orthogonal.Represents
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Basic

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace SPN

set_option linter.unusedSectionVars false

open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth QuadraticMap
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (elementaryGroup_le_of_subgroup')
open scoped commutatorElement

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem two_ne_zero_of_odd {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  intro h2
  have hchar : ringChar F = 2 := by
    have hdvd : ringChar F ∣ 2 := (ringChar.spec F 2).mp (by exact_mod_cast h2)
    have hp2 : (ringChar F).Prime := by
      obtain ⟨n, hn⟩ := FiniteField.card F (ringChar F)
      exact hn.1
    exact (Nat.prime_dvd_prime_iff_eq hp2 Nat.prime_two).mp hdvd
  have heven := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card] at heven
  have := Nat.odd_iff.mp hodd
  omega

section Far

variable [FiniteDimensional F V] [Finite F]

theorem eichler_mem_far (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F)) {U N M : Submodule F V}
    (hUN : ∀ x ∈ U, ∀ y ∈ N, polar Q x y = 0) (hUM : ∀ x ∈ U, ∀ y ∈ M, polar Q x y = 0)
    (hNM : ∀ x ∈ N, ∀ y ∈ M, polar Q x y = 0) (hN : PolarNondegOn Q N)
    (hM : PolarNondegOn Q M) (hN0 : N ≠ ⊥) (hM0 : M ≠ ⊥)
    (hdim : 2 ≤ Module.finrank F N ∨ 2 ≤ Module.finrank F M) {H : Subgroup (V ≃ₗ[F] V)}
    (hH₁ : elemOn Q (U ⊔ N) ≤ H) (hH₂ : elemOn Q (N ⊔ M) ≤ H) {e : V} (heU : e ∈ U) {m : V}
    (hm : m ∈ M) : eichler Q e m ∈ H := by
  classical
  have hMN : ∀ x ∈ M, ∀ y ∈ N, polar Q x y = 0 := fun x hx y hy => by
    rw [polar_comm]; exact hNM y hy x hx
  have hUNM : ∀ x ∈ U, ∀ y ∈ N ⊔ M, polar Q x y = 0 := fun x hx y hy => by
    obtain ⟨n, hn, m', hm', rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_right, hUN x hx n hn, hUM x hx m' hm', add_zero]
  set G := eichlerParamSet Q H e with hG
  have hmemG : ∀ w, w ∈ G ↔ polar Q e w = 0 ∧ eichler Q e w ∈ H := fun w => mem_eichlerParamSet
  have heUN : e ∈ U ⊔ N := Submodule.mem_sup_left heU
  have hNG : ∀ n ∈ N, n ∈ G := fun n hn =>
    (hmemG n).mpr ⟨hUN e heU n hn, hH₁ (eichler_mem_elemOn heUN (Submodule.mem_sup_right hn))⟩
  obtain ⟨a, haN, b, hbM, hQa, hQb, hab⟩ : ∃ a ∈ N, ∃ b ∈ M, Q a ≠ 0 ∧ Q b ≠ 0 ∧
      Q a + Q b = 0 := by
    rcases hdim with hN2 | hM2
    · obtain ⟨b, hbM, hQb⟩ := hM.exists_map_ne_zero hM0
      obtain ⟨a, haN, hQa⟩ := hN.exists_map_eq h2 hN2 (-Q b)
      exact ⟨a, haN, b, hbM, by rw [hQa]; exact neg_ne_zero.mpr hQb, hQb, by rw [hQa]; ring⟩
    · obtain ⟨a, haN, hQa⟩ := hN.exists_map_ne_zero hN0
      obtain ⟨b, hbM, hQb⟩ := hM.exists_map_eq h2 hM2 (-Q a)
      exact ⟨a, haN, b, hbM, hQa, by rw [hQb]; exact neg_ne_zero.mpr hQa, by rw [hQb]; ring⟩
  have hab0 : polar Q a b = 0 := hNM a haN b hbM
  have hba0 : polar Q b a = 0 := by rw [polar_comm, hab0]
  have huNM : a + b ∈ N ⊔ M := Submodule.add_mem_sup haN hbM
  have hu : Q (a + b) = 0 := by
    rw [QuadraticMap.map_add Q a b, hab0, add_zero, hab]
  set β : F := polar Q a (a + b) with hβdef
  have hβ : β = polar Q a a := by rw [hβdef, polar_add_right, hab0, add_zero]
  have hβ0 : β ≠ 0 := by
    rw [hβ, QuadraticMap.polar_self, two_nsmul, ← two_mul]
    exact mul_ne_zero h2 hQa
  have key : ∀ z ∈ N ⊔ M, polar Q (a + b) z = 0 →
      β • z - (polar Q a z + Q z * β) • (a + b) ∈ G := by
    intro z hz huz
    have hea : polar Q e a = 0 := hUN e heU a haN
    have heu : polar Q e (a + b) = 0 := hUNM e heU _ huNM
    have hez : polar Q e z = 0 := hUNM e heU z hz
    have hcomm := commutator_eichler_eichler (Q := Q) hu huz hea heu hez
    have hg : eichler Q (a + b) z ∈ H := hH₂ (eichler_mem_elemOn huNM hz)
    have hg' : eichler Q e a ∈ H := ((hmemG a).mp (hNG a haN)).2
    have hmem : ⁅eichler Q (a + b) z, eichler Q e a⁆ ∈ H := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')
    rw [hcomm] at hmem
    refine (hmemG _).mpr ⟨?_, ?_⟩
    · rw [polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hez, heu]
      ring
    · convert hmem using 3
  have hF3a : ∀ z ∈ M, polar Q b z = 0 → β • z - (Q z * β) • b ∈ G := by
    intro z hz hbz
    have hz' : z ∈ N ⊔ M := Submodule.mem_sup_right hz
    have haz : polar Q a z = 0 := hNM a haN z hz
    have huz : polar Q (a + b) z = 0 := by rw [polar_add_left, haz, hbz, add_zero]
    have h := key z hz' huz
    rw [haz, zero_add] at h
    have hNa : (Q z * β) • a ∈ G := hNG _ (N.smul_mem _ haN)
    have := G.add_mem h hNa
    have e : β • z - (Q z * β) • (a + b) + (Q z * β) • a = β • z - (Q z * β) • b := by module
    rwa [e] at this
  have hF3b : ∀ z ∈ N, polar Q a z = 0 → (-(Q z * β)) • b ∈ G := by
    intro z hz haz
    have hz' : z ∈ N ⊔ M := Submodule.mem_sup_left hz
    have hbz : polar Q b z = 0 := hMN b hbM z hz
    have huz : polar Q (a + b) z = 0 := by rw [polar_add_left, haz, hbz, add_zero]
    have h := key z hz' huz
    rw [haz, zero_add] at h
    have hNa : (Q z * β) • a - β • z ∈ G :=
      G.sub_mem (hNG _ (N.smul_mem _ haN)) (hNG _ (N.smul_mem _ hz))
    have := G.add_mem h hNa
    have e : β • z - (Q z * β) • (a + b) + ((Q z * β) • a - β • z) = (-(Q z * β)) • b := by
      module
    rwa [e] at this
  obtain ⟨κ, hκ0, hκ⟩ : ∃ κ : F, κ ≠ 0 ∧ ∀ t : F, (κ * (t * t)) • b ∈ G := by
    by_cases hM2 : 2 ≤ Module.finrank F M
    · obtain ⟨z₀, hz₀M, hbz₀, hQz₀⟩ := hM.exists_polar_eq_zero_map_ne_zero h2 hM2 hbM hQb
      refine ⟨-2 * (Q z₀ * β), mul_ne_zero (neg_ne_zero.mpr h2) (mul_ne_zero hQz₀ hβ0),
        fun t => ?_⟩
      have h1 := hF3a (t • z₀) (M.smul_mem _ hz₀M)
        (by rw [polar_smul_right_eq, hbz₀, mul_zero])
      have h1' := hF3a ((-t) • z₀) (M.smul_mem _ hz₀M)
        (by rw [polar_smul_right_eq, hbz₀, mul_zero])
      rw [map_smul_eq_sq] at h1 h1'
      have := G.add_mem h1 h1'
      have e : β • t • z₀ - (t ^ 2 * Q z₀ * β) • b + (β • (-t) • z₀ - ((-t) ^ 2 * Q z₀ * β) • b) =
          (-2 * (Q z₀ * β) * (t * t)) • b := by module
      rwa [e] at this
    · have hN2 : 2 ≤ Module.finrank F N := hdim.resolve_right hM2
      obtain ⟨z₀, hz₀N, haz₀, hQz₀⟩ := hN.exists_polar_eq_zero_map_ne_zero h2 hN2 haN hQa
      refine ⟨-(Q z₀ * β), neg_ne_zero.mpr (mul_ne_zero hQz₀ hβ0), fun t => ?_⟩
      have h1 := hF3b (t • z₀) (N.smul_mem _ hz₀N)
        (by rw [polar_smul_right_eq, haz₀, mul_zero])
      rw [map_smul_eq_sq] at h1
      have e : (-(t ^ 2 * Q z₀ * β)) • b = (-(Q z₀ * β) * (t * t)) • b := by module
      rwa [e] at h1
  have hc : ∀ c : F, c • b ∈ G := by
    intro c
    obtain ⟨s, r, hsr⟩ := exists_add_sq_eq hodd (c₁ := (1 : F)) (c₂ := 1) one_ne_zero one_ne_zero
      (c / κ)
    have hsr' : s * s + r * r = c / κ := by simpa using hsr
    have hc' : c = κ * (s * s) + κ * (r * r) := by
      have : c = κ * (s * s + r * r) := by rw [hsr']; field_simp
      rw [this]
      ring
    rw [hc', add_smul]
    exact G.add_mem (hκ s) (hκ r)
  have hbb : polar Q b b ≠ 0 := by
    rw [QuadraticMap.polar_self, two_nsmul, ← two_mul]
    exact mul_ne_zero h2 hQb
  have hmG : m ∈ G := by
    set k : F := polar Q b m / polar Q b b with hk
    set m' : V := m - k • b with hm'
    have hm'M : m' ∈ M := M.sub_mem hm (M.smul_mem _ hbM)
    have hbm' : polar Q b m' = 0 := by
      rw [hm', polar_sub_right, polar_smul_right_eq, hk]
      field_simp
      ring
    have hz := hF3a (β⁻¹ • m') (M.smul_mem _ hm'M) (by rw [polar_smul_right_eq, hbm', mul_zero])
    rw [map_smul_eq_sq] at hz
    have hm'G : m' ∈ G := by
      have := G.add_mem hz (hc (β⁻¹ ^ 2 * Q m' * β))
      have e : β • β⁻¹ • m' - (β⁻¹ ^ 2 * Q m' * β) • b + (β⁻¹ ^ 2 * Q m' * β) • b = m' := by
        rw [smul_smul, mul_inv_cancel₀ hβ0, one_smul]; abel
      rwa [e] at this
    have : m = k • b + m' := by rw [hm']; abel
    rw [this]
    exact G.add_mem (hc k) hm'G
  exact ((hmemG m).mp hmG).2

end Far

section Overlap

variable [FiniteDimensional F V] [Finite F]

theorem elementaryGroup_le_of_overlap (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) {U N M : Submodule F V} (hU : PolarNondegOn Q U)
    (h3 : 3 ≤ Module.finrank F U) (hUN : ∀ x ∈ U, ∀ y ∈ N, polar Q x y = 0)
    (hUM : ∀ x ∈ U, ∀ y ∈ M, polar Q x y = 0) (hNM : ∀ x ∈ N, ∀ y ∈ M, polar Q x y = 0)
    (hN : PolarNondegOn Q N) (hM : PolarNondegOn Q M) (hN0 : N ≠ ⊥) (hM0 : M ≠ ⊥)
    (hdim : 2 ≤ Module.finrank F N ∨ 2 ≤ Module.finrank F M) (htop : U ⊔ N ⊔ M = ⊤)
    {H : Subgroup (V ≃ₗ[F] V)} (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hH₁ : elemOn Q (U ⊔ N) ≤ H) (hH₂ : elemOn Q (N ⊔ M) ≤ H) : elementaryGroup Q ≤ H := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd hodd
  obtain ⟨P, he, hf⟩ := CFSG.ClassicalInvolution.Asc77.exists_hypPair_le hodd hU h3
  have hUle : U ≤ U ⊔ N := le_sup_left
  have hNle : N ≤ U ⊔ N := le_sup_right
  have hU' : ∀ w, polar Q P.e w = 0 → eichler Q P.e w ∈ H := by
    intro w hw
    have hwtop : w ∈ U ⊔ N ⊔ M := by rw [htop]; trivial
    obtain ⟨x, hx, w₃, hw₃, rfl⟩ := Submodule.mem_sup.mp hwtop
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hx
    have h1 : polar Q P.e w₁ = 0 := by
      rw [polar_add_right, polar_add_right, hUN _ he w₂ hw₂, hUM _ he w₃ hw₃, add_zero,
        add_zero] at hw
      exact hw
    have h2' : polar Q P.e w₂ = 0 := hUN _ he w₂ hw₂
    have h3' : polar Q P.e w₃ = 0 := hUM _ he w₃ hw₃
    rw [← eichler_mul (by rw [polar_add_right, h1, h2', add_zero]) h3',
      ← eichler_mul h1 h2']
    refine mul_mem (mul_mem ?_ ?_) ?_
    · exact hH₁ (eichler_mem_elemOn (hUle he) (hUle hw₁))
    · exact hH₁ (eichler_mem_elemOn (hUle he) (hNle hw₂))
    · exact eichler_mem_far h2 hodd hUN hUM hNM hN hM hN0 hM0 hdim hH₁ hH₂ he hw₃
  have hX : PolarNondegOn Q (U ⊓ P.perp) := PolarNondegOn.inf_perp hU P he hf
  have hdim' := CFSG.ClassicalInvolution.Asc77.finrank_inf_perp_hypPair hQ P he hf
  have hne : U ⊓ P.perp ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hdim'
    omega
  obtain ⟨a, haX, hca⟩ := hX.exists_map_ne_zero hne
  have haU : a ∈ U := haX.1
  have haP : a ∈ P.perp := haX.2
  set s : F := (Q a)⁻¹ with hs_def
  have hs : Q a * s * 1 = 1 := by rw [hs_def, mul_inv_cancel₀ hca, mul_one]
  have hweyl : (eichler Q P.e (s • a) * eichler Q P.f ((1 : F) • a) * eichler Q P.e (s • a)) P.e =
      (-((1 : F) ^ 2 * Q a)) • P.f := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eichler_e_apply_e, eichler_f_apply_e P haP,
      map_sub, map_add, map_smul, map_smul, eichler_e_apply_e, eichler_e_apply_a P haP,
      eichler_e_apply_f P haP]
    match_scalars
    · linear_combination (Q a * s * 1 - 1) * hs
    · linear_combination (-1) * hs
    · ring
  have hwmem : eichler Q P.e (s • a) * eichler Q P.f ((1 : F) • a) * eichler Q P.e (s • a) ∈ H := by
    refine hH₁ (mul_mem (mul_mem ?_ ?_) ?_)
    · exact eichler_mem_elemOn (hUle he) (hUle (U.smul_mem _ haU))
    · exact eichler_mem_elemOn (hUle hf) (hUle (U.smul_mem _ haU))
    · exact eichler_mem_elemOn (hUle he) (hUle (U.smul_mem _ haU))
  refine elementaryGroup_le_of_subgroup' H hQ hHO hU' ⟨_, hwmem, -((1 : F) ^ 2 * Q a), ?_, hweyl⟩
  rw [neg_ne_zero]
  exact mul_ne_zero (by norm_num) hca

end Overlap

end SPN

end CFSG.ClassicalInvolution.Asc77
