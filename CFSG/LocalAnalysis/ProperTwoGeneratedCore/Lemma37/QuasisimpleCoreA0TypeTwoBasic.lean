module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0Quat

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}
  {N : Subgroup J} {M : ℕ}

namespace A0Config

variable (φ : a0Kernel Q B N ≃* QuaternionGroup M) [NeZero M] (hc : A0Config Q B z u N)

include hc in
theorem conj_kerGen_eq (h3 : 3 ≤ M)
    (hII : ∃ k ∈ a0Kernel Q B N, z * k * z⁻¹ ≠ u * k * u⁻¹) :
    z * kerGen φ * z⁻¹ = centralElt J * kerGen φ := by
  have h := hc.setting
  have hz := hc.fourGen
  refine (hc.conj_eq_of_mem_a0Kernel (kerGen_mem φ)).resolve_left fun hza => ?_
  obtain ⟨k₀, hk₀, hne⟩ := hII
  obtain ⟨t, htQ, ht, htV⟩ := hz.exists_involution_not_mem_fourGroup h
  have hztK := hc.mul_mem_a0Kernel htQ ht htV
  have hzpow : ∀ i : ℕ, z * kerGen φ ^ i * z⁻¹ = kerGen φ ^ i := fun i => by
    rw [← conj_pow, hza]
  by_cases hk₀a : ∃ k : ℕ, k₀ = kerGen φ ^ k
  · obtain ⟨k, rfl⟩ := hk₀a
    apply hne
    rw [hzpow, ← hc.pow_comm_self φ h3 k, mul_inv_cancel_right]
  · obtain ⟨i, hi⟩ := hc.exists_pow_mul_of_not_pow φ hk₀ hztK hk₀a
      (hc.not_pow_of_conj_self φ h3 (hc.conj_self_eq_of_mul htQ ht htV)) h3
    apply hne
    rw [hc.conj_of_not_pow φ h3 hk₀ hk₀a, hi]
    calc z * (kerGen φ ^ i * (z * t)) * z⁻¹ = (z * kerGen φ ^ i * z⁻¹) * (z * (z * t) * z⁻¹) := by
          group
      _ = centralElt J * (kerGen φ ^ i * (z * t)) := by
          rw [hzpow, hc.conj_mul_eq_central_mul htQ ht htV, h.mul_central_left]

include hc in
theorem mul_conj_kerGen_ne (h3 : 3 ≤ M)
    (hII : ∃ k ∈ a0Kernel Q B N, z * k * z⁻¹ ≠ u * k * u⁻¹) {k : J}
    (hk : k ∈ a0Kernel Q B N) : z * k * kerGen φ * (z * k)⁻¹ ≠ kerGen φ := by
  have h := hc.setting
  have hza := hc.conj_kerGen_eq φ h3 hII
  intro heq
  rcases hc.mem_cases φ hk with ⟨i, rfl⟩ | ⟨-, hinv⟩
  · have hci : kerGen φ ^ i * kerGen φ = kerGen φ * kerGen φ ^ i :=
      (Commute.self_pow (kerGen φ) i).eq.symm
    rw [show z * kerGen φ ^ i * kerGen φ * (z * kerGen φ ^ i)⁻¹ =
        z * (kerGen φ ^ i * kerGen φ) * (kerGen φ ^ i)⁻¹ * z⁻¹ by group, hci,
      show z * (kerGen φ * kerGen φ ^ i) * (kerGen φ ^ i)⁻¹ * z⁻¹ = z * kerGen φ * z⁻¹ by group,
      hza] at heq
    exact h.centralElt_ne_one (mul_eq_right.mp heq)
  · rw [show z * k * kerGen φ * (z * k)⁻¹ = z * (k * kerGen φ * k⁻¹) * z⁻¹ by group, hinv,
      show z * (kerGen φ)⁻¹ * z⁻¹ = (z * kerGen φ * z⁻¹)⁻¹ by group, hza, mul_inv_rev,
      inv_eq_of_mul_eq_one_right h.centralElt_mul_self] at heq
    have h2 : kerGen φ * kerGen φ = centralElt J := by
      nth_rewrite 2 [← heq]
      group
    apply kerGen_pow_four_ne_one φ h3
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two, h2, h.centralElt_mul_self]

include hc φ in
theorem eq_of_centralizes (h3 : 3 ≤ M)
    (hII : ∃ k ∈ a0Kernel Q B N, z * k * z⁻¹ ≠ u * k * u⁻¹) {w : J}
    (hwQ : w ∈ (Q : Subgroup J)) (hwK : ∀ k ∈ a0Kernel Q B N, w * k = k * w) :
    w = 1 ∨ w = centralElt J := by
  have h := hc.setting
  have hz := hc.fourGen
  have hB : ∀ v ∈ (Q : Subgroup J), (∀ k ∈ a0Kernel Q B N, v * k = k * v) →
      (v ∈ a0Kernel Q B N ∨ z * v ∈ a0Kernel Q B N) → v = 1 ∨ v = centralElt J := by
    intro v hvQ hvK hv
    rcases hv with hv | hv
    · obtain ⟨i, rfl⟩ := hc.exists_pow_of_comm φ h3 hv (hvK u hc.self_mem_a0Kernel)
      obtain ⟨t, htQ, ht, htV⟩ := hz.exists_involution_not_mem_fourGroup h
      have hztK := hc.mul_mem_a0Kernel htQ ht htV
      rcases hc.mem_cases φ hztK with hk | ⟨-, hinv⟩
      · exact absurd hk (hc.not_pow_of_conj_self φ h3 (hc.conj_self_eq_of_mul htQ ht htV))
      have h1 : z * t * kerGen φ ^ i * (z * t)⁻¹ = kerGen φ ^ i := by
        rw [← hvK _ hztK, mul_inv_cancel_right]
      rw [← conj_pow, hinv, inv_pow] at h1
      refine hc.pow_eq_of_sq_eq_one φ i ?_
      rw [two_mul, pow_add]
      calc kerGen φ ^ i * kerGen φ ^ i = kerGen φ ^ i * (kerGen φ ^ i)⁻¹⁻¹ := by rw [inv_inv]
        _ = 1 := by rw [h1, mul_inv_cancel]
    · exfalso
      apply hc.mul_conj_kerGen_ne φ h3 hII hv
      rw [show z * (z * v) = v by rw [← mul_assoc, hz.mul_self, one_mul],
        hvK _ (kerGen_mem φ), mul_inv_cancel_right]
  have hC : ∀ v ∈ (Q : Subgroup J), (∀ k ∈ a0Kernel Q B N, v * k = k * v) →
      (v * v = 1 ∨ v * v = centralElt J) → v = 1 ∨ v = centralElt J := by
    intro v hvQ hvK hvv
    rcases hvv with hvv | hvv
    · exact hB v hvQ hvK (hc.mem_a0Kernel_or_mul_mem hvQ hvv)
    · have hvu : v * u * (v * u) = 1 := by
        rw [show v * u * (v * u) = v * (u * v) * u by group, ← hvK u hc.self_mem_a0Kernel,
          show v * (v * u) * u = (v * v) * (u * u) by group, hvv, hc.sq, h.centralElt_mul_self]
      refine hB v hvQ hvK ?_
      rcases hc.mem_a0Kernel_or_mul_mem ((Q : Subgroup J).mul_mem hvQ hc.mem) hvu with h1 | h1
      · left
        have h2 := (a0Kernel Q B N).mul_mem h1 ((a0Kernel Q B N).inv_mem hc.self_mem_a0Kernel)
        rwa [mul_inv_cancel_right] at h2
      · right
        have h2 := (a0Kernel Q B N).mul_mem h1 ((a0Kernel Q B N).inv_mem hc.self_mem_a0Kernel)
        rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at h2
  have hind : ∀ k : ℕ, ∀ v ∈ (Q : Subgroup J), (∀ k ∈ a0Kernel Q B N, v * k = k * v) →
      v ^ 2 ^ k = 1 → v = 1 ∨ v = centralElt J := by
    intro k
    induction k with
    | zero => intro v _ _ hv; left; simpa using hv
    | succ k ih =>
      intro v hvQ hvK hv
      have hvv : v * v ∈ (Q : Subgroup J) := (Q : Subgroup J).mul_mem hvQ hvQ
      have hvvK : ∀ k ∈ a0Kernel Q B N, v * v * k = k * (v * v) := fun k hk => by
        rw [mul_assoc, hvK k hk, ← mul_assoc, hvK k hk, mul_assoc]
      have h1 := ih (v * v) hvv hvvK (by rw [← pow_two, ← pow_mul, ← pow_succ']; exact hv)
      exact hC v hvQ hvK h1
  obtain ⟨k, hk⟩ := Q.isPGroup' ⟨w, hwQ⟩
  exact hind k w hwQ hwK (by simpa using congrArg Subtype.val hk)

include hc in
theorem eq_of_mem_of_comm (h3 : 3 ≤ M) {b : J} (hb : b ∈ a0Kernel Q B N)
    (hba : ¬ ∃ k : ℕ, b = kerGen φ ^ k) {r : J} (hr : r ∈ a0Kernel Q B N)
    (hrb : r * b = b * r) (hru : r * u = u * r) : r = 1 ∨ r = centralElt J := by
  obtain ⟨k, rfl⟩ := hc.exists_pow_of_comm φ h3 hr hru
  refine hc.pow_eq_of_sq_eq_one φ k ?_
  have h1 := hc.conj_pow_of_not_pow φ hb hba k
  rw [← hrb, mul_inv_cancel_right] at h1
  rw [two_mul, pow_add]
  calc kerGen φ ^ k * kerGen φ ^ k = kerGen φ ^ k * (kerGen φ ^ k)⁻¹⁻¹ := by rw [inv_inv]
    _ = 1 := by rw [← h1, mul_inv_cancel]

include hc in
theorem exists_mul_comm (h3 : 3 ≤ M) {b : J} (hb : b ∈ a0Kernel Q B N)
    (hba : ¬ ∃ k : ℕ, b = kerGen φ ^ k) (hbz : z * b = b * z)
    (hza : z * kerGen φ * z⁻¹ = centralElt J * kerGen φ) {s : J} (hs : s ∈ (Q : Subgroup J)) :
    ∃ k ∈ a0Kernel Q B N, k * s * b = b * (k * s) ∧ k * s * u = u * (k * s) := by
  have h := hc.setting
  have hz := hc.fourGen
  set b' := s * b * s⁻¹ with hb'
  have hb'K : b' ∈ a0Kernel Q B N := hc.conj_mem_a0Kernel hs hb
  have hb'a : ¬ ∃ k : ℕ, b' = kerGen φ ^ k := by
    rintro ⟨k, hk⟩
    obtain ⟨i, hi⟩ := hc.exists_conj_kerGen_eq_pow φ h3 ((Q : Subgroup J).inv_mem hs)
    apply hba
    refine ⟨i * k, ?_⟩
    calc b = s⁻¹ * b' * s⁻¹⁻¹ := by rw [hb']; group
      _ = (s⁻¹ * kerGen φ * s⁻¹⁻¹) ^ k := by rw [hk, conj_pow]
      _ = kerGen φ ^ (i * k) := by rw [hi, pow_mul]
  have hb'z : z * b' * z⁻¹ = b' := by
    have hzs : s⁻¹ * z * s = z ∨ s⁻¹ * z * s = centralElt J * z := by
      have := hz.conj_eq h ((Q : Subgroup J).inv_mem hs)
      simpa using this
    have hzb : (s⁻¹ * z * s) * b * (s⁻¹ * z * s)⁻¹ = b := by
      rcases hzs with h1 | h1 <;> rw [h1]
      · rw [hbz, mul_inv_cancel_right]
      · rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.centralElt_mul_self,
          show centralElt J * z * b * (z⁻¹ * centralElt J) =
            centralElt J * (z * b * z⁻¹) * centralElt J by group, hbz, mul_inv_cancel_right,
          ← (h.commute_centralElt b).eq, mul_assoc, h.centralElt_mul_self, mul_one]
    calc z * b' * z⁻¹ = s * ((s⁻¹ * z * s) * b * (s⁻¹ * z * s)⁻¹) * s⁻¹ := by rw [hb']; group
      _ = b' := by rw [hzb, hb']
  obtain ⟨l, hl⟩ := hc.exists_pow_mul_of_not_pow φ hb'K hb hb'a hba h3
  have hl2 : Even l := by
    have h1 : z * b' * z⁻¹ = centralElt J ^ l * b' := by
      rw [hl, show z * (kerGen φ ^ l * b) * z⁻¹ = (z * kerGen φ * z⁻¹) ^ l * (z * b * z⁻¹) by
        rw [conj_pow]; group, hza, hbz, mul_inv_cancel_right,
        (h.commute_centralElt (kerGen φ)).symm.mul_pow, mul_assoc]
    rw [hb'z] at h1
    have h2 : centralElt J ^ l = 1 := mul_eq_right.mp h1.symm
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨m, rfl⟩ := hodd
    rw [pow_succ, pow_mul, pow_two, h.centralElt_mul_self, one_pow, one_mul] at h2
    exact h.centralElt_ne_one h2
  obtain ⟨m, rfl⟩ := hl2
  set s₁ := (kerGen φ ^ m)⁻¹ * s with hs₁
  have hs₁Q : s₁ ∈ (Q : Subgroup J) :=
    (Q : Subgroup J).mul_mem ((Q : Subgroup J).inv_mem ((Q : Subgroup J).pow_mem
      (kerGen_mem φ).1 m)) hs
  have hs₁b : s₁ * b = b * s₁ := by
    have h1 := hc.conj_pow_of_not_pow φ hb hba m
    have h2 : s₁ * b * s₁⁻¹ = b := by
      calc s₁ * b * s₁⁻¹ = (kerGen φ ^ m)⁻¹ * b' * kerGen φ ^ m := by rw [hs₁, hb']; group
        _ = (kerGen φ ^ m)⁻¹ * (kerGen φ ^ (m + m) * b) * kerGen φ ^ m := by rw [hl]
        _ = kerGen φ ^ m * (b * kerGen φ ^ m * b⁻¹) * b := by rw [pow_add]; group
        _ = b := by rw [h1]; group
    calc s₁ * b = s₁ * b * s₁⁻¹ * s₁ := by group
      _ = b * s₁ := by rw [h2]
  have hamK : (kerGen φ ^ m)⁻¹ ∈ a0Kernel Q B N :=
    (a0Kernel Q B N).inv_mem ((a0Kernel Q B N).pow_mem (kerGen_mem φ) m)
  rcases h.conj_eq_of_mem_quasiNormalizer hc.sq (hc.mem_quasiNormalizer hs₁Q) with h1 | h1
  · refine ⟨(kerGen φ ^ m)⁻¹, hamK, by rw [← hs₁]; exact hs₁b, ?_⟩
    rw [← hs₁]
    calc s₁ * u = s₁ * u * s₁⁻¹ * s₁ := by group
      _ = u * s₁ := by rw [h1]
  · refine ⟨b * (kerGen φ ^ m)⁻¹, (a0Kernel Q B N).mul_mem hb hamK, ?_, ?_⟩
    · rw [mul_assoc b, ← hs₁, mul_assoc, hs₁b]
    · rw [mul_assoc b, ← hs₁]
      have h2 := hc.conj_self_of_not_pow φ h3 hb hba
      have h3' : b * s₁ * u * (b * s₁)⁻¹ = u := by
        calc b * s₁ * u * (b * s₁)⁻¹ = b * (s₁ * u * s₁⁻¹) * b⁻¹ := by group
          _ = centralElt J * (b * u * b⁻¹) := by rw [h1, h.mul_central_left]; group
          _ = u := by rw [h2, ← mul_assoc, h.centralElt_mul_self, one_mul]
      calc b * s₁ * u = b * s₁ * u * (b * s₁)⁻¹ * (b * s₁) := by group
        _ = u * (b * s₁) := by rw [h3']

include hc in
theorem comm_mod (h3 : 3 ≤ M) (hII : ∃ k ∈ a0Kernel Q B N, z * k * z⁻¹ ≠ u * k * u⁻¹)
    {b : J} (hb : b ∈ a0Kernel Q B N) (hba : ¬ ∃ k : ℕ, b = kerGen φ ^ k) {r r' : J}
    (hrQ : r ∈ (Q : Subgroup J)) (hr'Q : r' ∈ (Q : Subgroup J)) (hrb : r * b = b * r)
    (hr'b : r' * b = b * r') :
    r⁻¹ * r'⁻¹ * r * r' = 1 ∨ r⁻¹ * r'⁻¹ * r * r' = centralElt J := by
  obtain ⟨i, hi⟩ := hc.exists_conj_kerGen_eq_pow φ h3 hrQ
  obtain ⟨i', hi'⟩ := hc.exists_conj_kerGen_eq_pow φ h3 hr'Q
  have h1 : (r * r') * kerGen φ * (r * r')⁻¹ = (r' * r) * kerGen φ * (r' * r)⁻¹ := by
    calc (r * r') * kerGen φ * (r * r')⁻¹ = r * (r' * kerGen φ * r'⁻¹) * r⁻¹ := by group
      _ = (r * kerGen φ * r⁻¹) ^ i' := by rw [hi', conj_pow]
      _ = kerGen φ ^ (i * i') := by rw [hi, ← pow_mul]
      _ = (r' * kerGen φ * r'⁻¹) ^ i := by rw [hi', ← pow_mul, mul_comm]
      _ = (r' * r) * kerGen φ * (r' * r)⁻¹ := by rw [conj_pow, ← hi]; group
  set c := r⁻¹ * r'⁻¹ * r * r' with hcdef
  have hca : c * kerGen φ = kerGen φ * c := by
    have h2 : c * kerGen φ * c⁻¹ = kerGen φ := by
      calc c * kerGen φ * c⁻¹ = (r' * r)⁻¹ * ((r * r') * kerGen φ * (r * r')⁻¹) * (r' * r) := by
            rw [hcdef]; group
        _ = kerGen φ := by rw [h1]; group
    calc c * kerGen φ = c * kerGen φ * c⁻¹ * c := by group
      _ = kerGen φ * c := by rw [h2]
  have hcb : c * b = b * c := by
    have hr : Commute r b := hrb
    have hr' : Commute r' b := hr'b
    have : Commute c b := by
      rw [hcdef]
      exact ((hr.inv_left.mul_left hr'.inv_left).mul_left hr).mul_left hr'
    exact this
  have hcQ : c ∈ (Q : Subgroup J) := by
    rw [hcdef]
    exact (Q : Subgroup J).mul_mem ((Q : Subgroup J).mul_mem ((Q : Subgroup J).mul_mem
      ((Q : Subgroup J).inv_mem hrQ) ((Q : Subgroup J).inv_mem hr'Q)) hrQ) hr'Q
  exact hc.eq_of_centralizes φ h3 hII hcQ (hc.centralizes_of_comm φ h3 hb hba hca hcb)

end A0Config

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
