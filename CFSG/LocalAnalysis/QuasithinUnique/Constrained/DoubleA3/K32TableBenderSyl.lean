module

public import CFSG.Goldschmidt.Steps.GoldTypeBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAut

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.BenderExt (benderData_of_isBenderGroup)
open CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt (mem_sylowCenter_of_sq_eq_one
  mem_center_of_conj_eq_one)
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem k32_conj_injective (hX : fusionIsBenderGroup K) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgc : g ∈ Subgroup.center K := mem_center_of_conj_eq_one hg
  have hs : IsSimpleGroup K := (benderData_of_isBenderGroup hX).simple
  have hcenter : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · exfalso
      obtain ⟨q, k, -, hB⟩ := (benderData_of_isBenderGroup hX).borel
      obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 K))
      apply (hB Q).1.1
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro t
      have hx : x ∈ Subgroup.center K := by rw [h]; exact Subgroup.mem_top x
      rw [← (Subgroup.mem_center_iff.mp hx t), mul_inv_cancel_right]
  rw [hcenter] at hgc
  exact Subgroup.mem_bot.mp hgc

theorem k32_exists_sylow
    (hX : fusionIsBenderGroup K) {S : Subgroup (MulAut K)}
    (hS : IsSylowTwoOf S (innAut K)) :
    ∃ Q : Sylow 2 K, (Q : Subgroup K).map (MulAut.conj : K →* MulAut K) = S := by
  have hinj := k32_conj_injective hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (S.comap (MulAut.conj : K →* MulAut K)) :=
    hS.2.1.comap_of_injective _ hinj
  have hidx : ¬ 2 ∣ (S.comap (MulAut.conj : K →* MulAut K)).index := by
    rw [Subgroup.index_comap]
    exact hS.2.2
  refine ⟨hp.toSylow hidx, ?_⟩
  show (S.comap (MulAut.conj : K →* MulAut K)).map (MulAut.conj : K →* MulAut K) = S
  exact Subgroup.map_comap_eq_self hS.1

omit [Finite K] in
theorem k32_conj_conj (γ : MulAut K) (t : K) :
    γ * MulAut.conj t * γ⁻¹ = MulAut.conj (γ t) := by
  ext x
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem k32_bender_sq_central
    (hX : fusionIsBenderGroup K) {q k : ℕ} (hB : fusionBenderBorel K q k)
    (hq : 2 ≤ q) {S : Subgroup (MulAut K)} (hS : IsSylowTwoOf S (innAut K)) {s : MulAut K}
    (hs : s ∈ S) (hs2 : s * s = 1) : ∀ s' ∈ S, s * s' = s' * s := by
  obtain ⟨Q, hQ⟩ := k32_exists_sylow hX hS
  have hinj := k32_conj_injective hX
  rw [← hQ] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  intro s' hs'
  rw [← hQ] at hs'
  obtain ⟨t', ht', rfl⟩ := hs'
  have ht2 : t ^ 2 = 1 := by
    apply hinj
    rw [map_pow, pow_two, hs2, map_one]
  have hz := mem_sylowCenter_of_sq_eq_one hB hq Q ht ht2
  have hc : t' * t = t * t' := (mem_sylowCenter.mp hz).2 t' ht'
  show MulAut.conj t * MulAut.conj t' = MulAut.conj t' * MulAut.conj t
  rw [← map_mul, ← map_mul, hc]

theorem k32_bender_ti
    (hX : fusionIsBenderGroup K) {q k : ℕ} (hB : fusionBenderBorel K q k)
    {S : Subgroup (MulAut K)} (hS : IsSylowTwoOf S (innAut K)) (γ : MulAut K) {v : MulAut K}
    (hvS : v ∈ S) (hv1 : v ≠ 1) (hγv : γ * v * γ⁻¹ ∈ S) : ∀ s ∈ S, γ * s * γ⁻¹ ∈ S := by
  obtain ⟨Q, hQ⟩ := k32_exists_sylow hX hS
  have hinj := k32_conj_injective hX
  rw [← hQ] at hvS
  obtain ⟨t₀, ht₀, rfl⟩ := hvS
  have ht01 : t₀ ≠ 1 := fun h => hv1 (by rw [h, map_one])
  rw [k32_conj_conj, ← hQ] at hγv
  have hγt₀ : γ t₀ ∈ (Q : Subgroup K) := by
    obtain ⟨u, hu, hu'⟩ := hγv
    rw [← hinj hu']
    exact hu
  have hsm : (γ • Q : Sylow 2 K) = Q := by
    by_contra hne
    apply ht01
    have h1 : γ t₀ ∈ ((γ • Q : Sylow 2 K) : Subgroup K) := by
      rw [Omega.mem_smul_iff]
      have e : γ⁻¹ (γ t₀) = t₀ := by simp
      rw [e]
      exact ht₀
    have h0 := Omega.eq_one_of_mem_of_mem (hB Q).1 hne hγt₀ h1
    exact γ.injective (by rw [h0, map_one])
  intro s hs
  rw [← hQ] at hs ⊢
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨γ t, ?_, (k32_conj_conj γ t).symm⟩
  have h2 : γ t ∈ ((γ • Q : Sylow 2 K) : Subgroup K) := by
    rw [Omega.mem_smul_iff]
    have e : γ⁻¹ (γ t) = t := by simp
    rw [e]
    exact ht
  rw [hsm] at h2
  exact h2

omit [Finite K] in
theorem k32_commutator_conj_mem {P : Subgroup K} {d : K} (hd : ∀ x ∈ P, d * x * d⁻¹ ∈ P)
    {w : K} (hw : w ∈ ⁅P, P⁆) : d * w * d⁻¹ ∈ ⁅P, P⁆ := by
  rw [Subgroup.commutator_def] at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨d * a * d⁻¹, hd a ha, d * b * d⁻¹, hd b hb, ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have := Subgroup.mul_mem _ hx hy
    convert this using 1
    group
  | inv x _ hx =>
    have := Subgroup.inv_mem _ hx
    convert this using 1
    group

theorem k32_center_le_commutator_of_bender
    (hX : fusionIsBenderGroup K) {q k : ℕ}
    (hB : fusionBenderBorel K q k) (Q : Sylow 2 K)
    (hnab : ∃ a ∈ (Q : Subgroup K), ∃ b ∈ (Q : Subgroup K), a * b ≠ b * a) :
    sylowCenter (Q : Subgroup K) ≤ ⁅(Q : Subgroup K), (Q : Subgroup K)⁆ := by
  obtain ⟨hSE, hZ2, -, -⟩ := benderBorel_sylowCenter hB Q
  have hcomm := CFSG.Goldschmidt.GoldType.commutator_le_sylowCenter_of_bender hX Q
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  set x := ⁅a, b⁆ with hx
  have hxQ : x ∈ ⁅(Q : Subgroup K), (Q : Subgroup K)⁆ := Subgroup.commutator_mem_commutator ha hb
  have hx1 : x ≠ 1 := by
    intro h
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp h)
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]; exact Subgroup.one_mem _
  obtain ⟨n, hn, hnz⟩ := normalizer_transitive_center hSE hZ2 (hcomm hxQ) hz hx1 hz1
  have hn' : n⁻¹ ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) :=
    (Subgroup.normalizer _).inv_mem hn
  have := k32_commutator_conj_mem (P := (Q : Subgroup K)) (d := n⁻¹)
    (fun y hy => (Subgroup.mem_normalizer_iff.mp hn' y).mp hy) hxQ
  rw [← hnz]
  simpa using this

theorem k32_bender_center_le_commutator
    (hX : fusionIsBenderGroup K) {q k : ℕ}
    (hB : fusionBenderBorel K q k) {S : Subgroup (MulAut K)} (hS : IsSylowTwoOf S (innAut K))
    (hnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) :
    ∀ z ∈ S, (∀ s ∈ S, z * s = s * z) → z ∈ ⁅S, S⁆ := by
  obtain ⟨Q, hQ⟩ := k32_exists_sylow hX hS
  have hinj := k32_conj_injective hX
  have hnabQ : ∃ a ∈ (Q : Subgroup K), ∃ b ∈ (Q : Subgroup K), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    rw [← hQ] at ha hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    refine ⟨a₀, ha₀, b₀, hb₀, fun h => hab ?_⟩
    show MulAut.conj a₀ * MulAut.conj b₀ = MulAut.conj b₀ * MulAut.conj a₀
    rw [← map_mul, ← map_mul, h]
  have hQcomm := k32_center_le_commutator_of_bender hX hB Q hnabQ
  intro z hz hzc
  rw [← hQ] at hz
  obtain ⟨t₀, ht₀, rfl⟩ := hz
  have ht₀c : t₀ ∈ sylowCenter (Q : Subgroup K) := by
    refine mem_sylowCenter.mpr ⟨ht₀, fun t' ht' => ?_⟩
    apply hinj
    rw [map_mul, map_mul]
    exact (hzc (MulAut.conj t') (by rw [← hQ]; exact ⟨t', ht', rfl⟩)).symm
  rw [← hQ, ← Subgroup.map_commutator]
  exact ⟨t₀, hQcomm ht₀c, rfl⟩

theorem k32_nonabelian_of_borel {q k : ℕ} (hB : fusionBenderBorel K q k) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (Q : Sylow 2 K) :
    ∃ a ∈ (Q : Subgroup K), ∃ b ∈ (Q : Subgroup K), a * b ≠ b * a := by
  obtain ⟨-, -, hZcard, hQcard⟩ := benderBorel_sylowCenter hB Q
  by_contra hcon
  push Not at hcon
  have hle : (Q : Subgroup K) ≤ sylowCenter (Q : Subgroup K) := fun a ha =>
    mem_sylowCenter.mpr ⟨ha, fun t ht => (hcon t ht a ha)⟩
  have := Subgroup.card_le_of_le hle
  rw [hZcard, hQcard] at this
  have h1 : q ^ 2 ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
  nlinarith

theorem k32_bender_nonabelian
    (hX : fusionIsBenderGroup K) {q k : ℕ} (hB : fusionBenderBorel K q k)
    (hq : 2 ≤ q) (hk : 2 ≤ k) {S : Subgroup (MulAut K)} (hS : IsSylowTwoOf S (innAut K)) :
    ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a := by
  obtain ⟨Q, hQ⟩ := k32_exists_sylow hX hS
  obtain ⟨a, ha, b, hb, hab⟩ := k32_nonabelian_of_borel hB hq hk Q
  refine ⟨MulAut.conj a, ?_, MulAut.conj b, ?_, fun h => hab ?_⟩
  · rw [← hQ]; exact ⟨a, ha, rfl⟩
  · rw [← hQ]; exact ⟨b, hb, rfl⟩
  · apply k32_conj_injective hX
    rw [map_mul, map_mul]
    exact h

end CFSG.QuasithinUnique.DoubleA3
