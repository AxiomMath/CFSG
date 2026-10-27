module

public import CFSG.RankThree.PartOne.CTP.FusionSound

public section

namespace CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7

open CFSG.RankThree.PartOne.CTP.Fus

@[expose] def FusionDatum {G : Type*} [Group G] (p : ℕ) (E : Subgroup G) (Γ : Set G) : Prop :=
  IsPGroup p E ∧ E ≠ ⊥ ∧ Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ, ∃ e ∈ E, e ≠ 1 ∧ g * e * g⁻¹ ∈ E

theorem fusionGenerationOf_iff {G : Type*} [Group G] {p : ℕ} :
    FusionGenerationOf G p ↔ ∃ (E : Subgroup G) (Γ : Set G), FusionDatum p E Γ :=
  Iff.rfl

section Datum

variable {G : Type*} [Group G] {p : ℕ} {E : Subgroup G} {Γ : Set G}

theorem FusionDatum.of_le (h : FusionDatum p E Γ) {E' : Subgroup G} (hle : E ≤ E')
    (hE' : IsPGroup p E') : FusionDatum p E' Γ := by
  obtain ⟨-, hne, hΓ, hfus⟩ := h
  refine ⟨hE', ?_, hΓ, fun g hg => ?_⟩
  · rintro rfl
    exact hne (le_bot_iff.mp hle)
  · obtain ⟨e, he, he1, hge⟩ := hfus g hg
    exact ⟨e, hle he, he1, hle hge⟩

theorem FusionDatum.conj (h : FusionDatum p E Γ) (k : G) :
    FusionDatum p (E.map (MulAut.conj k).toMonoidHom) ((fun g => k * g * k⁻¹) '' Γ) := by
  obtain ⟨hp, hne, hΓ, hfus⟩ := h
  refine ⟨hp.map _, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj k).injective]
    exact hne
  · have h1 : (Subgroup.closure Γ).map (MulAut.conj k).toMonoidHom =
        Subgroup.closure ((fun g => k * g * k⁻¹) '' Γ) := by
      rw [MonoidHom.map_closure]
      rfl
    rw [← h1, hΓ, Subgroup.map_top_of_surjective _ (MulAut.conj k).surjective]
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨e, he, he1, hge⟩ := hfus g hg
    refine ⟨k * e * k⁻¹, ⟨e, he, rfl⟩, ?_, ⟨g * e * g⁻¹, hge, ?_⟩⟩
    · intro h1
      apply he1
      have : k * e * k⁻¹ = k * 1 * k⁻¹ := by rw [h1]; group
      simpa using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem exists_datum_sylow [Finite G] [Fact p.Prime] (h : FusionGenerationOf G p)
    (P : Sylow p G) : ∃ Γ : Set G, FusionDatum p (P : Subgroup G) Γ := by
  obtain ⟨E, Γ, hd⟩ := fusionGenerationOf_iff.mp h
  obtain ⟨Q, hQ⟩ := hd.1.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨_, (hd.of_le hQ Q.isPGroup').conj g |>.of_le ?_ P.isPGroup'⟩
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  exact le_rfl

theorem fusionGenerationOf_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    (h : FusionGenerationOf X p) : FusionGenerationOf Y p := by
  obtain ⟨E, Γ, hEp, hE1, hΓ, hfus⟩ := h
  refine ⟨E.map e.toMonoidHom, e.toMonoidHom '' Γ, hEp.map _, ?_, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
  · rw [← MonoidHom.map_closure, hΓ, Subgroup.map_top_of_surjective _ e.surjective]
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha, ha1, hga⟩ := hfus g hg
    refine ⟨e a, ⟨a, ha, rfl⟩, ?_, ⟨g * a * g⁻¹, hga, by simp⟩⟩
    rwa [Ne, map_eq_one_iff _ e.injective]

end Datum

section CentralQuotient

variable {K X : Type*} [Group K] [Group X]

theorem mem_of_map_mem_of_central {p : ℕ} (π : K →* X) (hcen : π.ker ≤ Subgroup.center K)
    (hker : ∀ k ∈ π.ker, ∀ n : ℕ, k ^ (p ^ n) = 1 → k = 1) {P : Subgroup K} (hP : IsPGroup p P)
    {x : K} (hx : ∃ n : ℕ, x ^ (p ^ n) = 1) (hxP : π x ∈ P.map π) : x ∈ P := by
  obtain ⟨y, hyP, hy⟩ := Subgroup.mem_map.mp hxP
  obtain ⟨n, hn⟩ := hx
  set k : K := y⁻¹ * x with hk
  have hkker : k ∈ π.ker := by
    rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hy, inv_mul_cancel]
  have hkc : Commute y k := by
    have := Subgroup.mem_center_iff.mp (hcen hkker) y
    exact this
  have hxk : x = y * k := by rw [hk]; group
  obtain ⟨m, hm⟩ : ∃ m : ℕ, y ^ (p ^ m) = 1 := by
    obtain ⟨m, hm⟩ := hP ⟨y, hyP⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hkpow : k ^ (p ^ (n + m)) = 1 := by
    have h1 : x ^ (p ^ (n + m)) = 1 := by
      rw [pow_add, pow_mul, hn, one_pow]
    have h2 : y ^ (p ^ (n + m)) = 1 := by
      rw [add_comm, pow_add, pow_mul, hm, one_pow]
    rw [hxk, hkc.mul_pow, h2, one_mul] at h1
    exact h1
  have := hker k hkker _ hkpow
  rw [hxk, this, mul_one]
  exact hyP

theorem fusionGenerationOf_of_central_quotient [Finite K] {p : ℕ} [Fact p.Prime] (π : K →* X)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center K)
    (hker : ∀ k ∈ π.ker, ∀ n : ℕ, k ^ (p ^ n) = 1 → k = 1)
    (h : FusionGenerationOf X p) : FusionGenerationOf K p := by
  have : Finite X := Finite.of_surjective π hπ
  obtain ⟨Q⟩ : Nonempty (Sylow p X) := inferInstance
  obtain ⟨Γ, hΓ⟩ := exists_datum_sylow h Q
  obtain ⟨P, hPQ⟩ := Sylow.mapSurjective_surjective hπ p Q
  have hPQ' : (P : Subgroup K).map π = Q := by
    have := congrArg (fun S : Sylow p X => (S : Subgroup X)) hPQ
    simpa using this
  obtain ⟨hQp, hQ1, hΓtop, hfus⟩ := hΓ
  have hP1 : (P : Subgroup K) ≠ ⊥ := by
    intro hP
    apply hQ1
    rw [← hPQ', hP, Subgroup.map_bot]
  refine fusionGenerationOf_iff.mpr ⟨P, π ⁻¹' Γ ∪ (π.ker : Set K), P.isPGroup', hP1, ?_, ?_⟩
  · refine eq_top_iff.mpr fun x _ => ?_
    have hπx : π x ∈ Subgroup.closure Γ := by rw [hΓtop]; trivial
    have key : ∀ z ∈ Subgroup.closure Γ, ∃ w ∈ Subgroup.closure (π ⁻¹' Γ ∪ (π.ker : Set K)),
        π w = z := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨w, rfl⟩ := hπ z
        exact ⟨w, Subgroup.subset_closure (Or.inl hz), rfl⟩
      | one => exact ⟨1, one_mem _, map_one π⟩
      | mul a b _ _ ha hb =>
        obtain ⟨a', ha', rfl⟩ := ha
        obtain ⟨b', hb', rfl⟩ := hb
        exact ⟨a' * b', mul_mem ha' hb', map_mul π a' b'⟩
      | inv a _ ha =>
        obtain ⟨a', ha', rfl⟩ := ha
        exact ⟨a'⁻¹, inv_mem ha', map_inv π a'⟩
    obtain ⟨x', hx', hxx'⟩ := key _ hπx
    have hk : x'⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel]
    have hkC : x'⁻¹ * x ∈ Subgroup.closure (π ⁻¹' Γ ∪ (π.ker : Set K)) :=
      Subgroup.subset_closure (Or.inr hk)
    simpa using mul_mem hx' hkC
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨e, he, he1, hge⟩ := hfus (π g) hg
      rw [← hPQ'] at he hge
      obtain ⟨e', he'P, rfl⟩ := Subgroup.mem_map.mp he
      refine ⟨e', he'P, ?_, ?_⟩
      · rintro rfl
        exact he1 (map_one π)
      · refine mem_of_map_mem_of_central π hcen hker P.isPGroup' ?_ (by simpa using hge)
        obtain ⟨n, hn⟩ := P.isPGroup' ⟨e', he'P⟩
        refine ⟨n, ?_⟩
        have h1 : e' ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
        have h2 : (g * e' * g⁻¹) ^ (p ^ n) = g * e' ^ (p ^ n) * g⁻¹ := by simp
        rw [h2, h1]
        group
    · obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
      refine ⟨e, e.2, fun h => he1 (Subtype.ext (by simpa using h)), ?_⟩
      have hc := Subgroup.mem_center_iff.mp (hcen hg) (e : K)
      have : g * (e : K) * g⁻¹ = e := by
        rw [← hc]
        group
      rw [this]
      exact e.2

end CentralQuotient

end CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7
