module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem isSylowTwoIn_of_card {T M : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T) {k : ℕ}
    (hM : Nat.card M = Nat.card T * k) (hk : ¬ 2 ∣ k) : IsSylowTwoIn T M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := T)).1 hT
  have hk0 : k ≠ 0 := fun h => hk (h ▸ dvd_zero 2)
  have hcard : Nat.card (T.subgroupOf M) = 2 ^ (Nat.card M).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv, hM, ha,
      Nat.factorization_mul (by positivity) hk0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hk, add_zero]
  exact ⟨hTM, Sylow.ofCard _ hcard, Sylow.coe_ofCard _ _⟩

theorem exists_mul_mem_normalizer {T M : Subgroup G} (hT : IsSylowTwoIn T M) {g : G}
    (hg : g ∈ normalizer (M : Set G)) : ∃ m ∈ M, m * g ∈ normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTM, P₀, hP₀⟩ := hT
  set T₂ := T.map (MulAut.conj g).toMonoidHom with hT₂
  have hT₂M : T₂ ≤ M := by
    rintro _ ⟨t, ht, rfl⟩
    exact (mem_normalizer_iff.mp hg t).mp (hTM ht)
  have hcardT₂ : Nat.card T₂ = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcard : Nat.card (T₂.subgroupOf M) = 2 ^ (Nat.card M).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hT₂M).toEquiv, hcardT₂,
      ← Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv, ← hP₀]
    exact Sylow.card_eq_multiplicity P₀
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (Sylow.ofCard _ hcard) P₀
  have key : ∀ y : M, (y : G) ∈ T ↔ ((m : G) * g)⁻¹ * y * ((m : G) * g) ∈ T := by
    intro y
    have h1 : y ∈ (P₀ : Subgroup M) ↔ y ∈ ((m • Sylow.ofCard _ hcard : Sylow 2 M) :
        Subgroup M) := by rw [hm]
    rw [hP₀, mem_subgroupOf, Sylow.coe_subgroup_smul, Sylow.coe_ofCard,
      Subgroup.mem_smul_pointwise_iff_exists] at h1
    rw [h1]
    constructor
    · rintro ⟨b, hb, hby⟩
      have hval : (m : G) * b * (m : G)⁻¹ = y := by
        have := congrArg Subtype.val hby
        simpa [MulAut.smul_def, MulAut.conj_apply] using this
      rw [mem_subgroupOf, hT₂] at hb
      obtain ⟨t, ht, htb⟩ := hb
      have e : ((m : G) * g)⁻¹ * y * ((m : G) * g) = t := by
        rw [← hval, ← htb]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact ht
    · intro hy
      refine ⟨⟨(m : G)⁻¹ * y * m, M.mul_mem (M.mul_mem (M.inv_mem m.2) y.2) m.2⟩, ?_, ?_⟩
      · rw [mem_subgroupOf, hT₂]
        refine ⟨((m : G) * g)⁻¹ * y * ((m : G) * g), hy, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · apply Subtype.ext
        simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        group
  have hmg : (m : G) * g ∈ normalizer (M : Set G) := mul_mem (le_normalizer m.2) hg
  refine ⟨m, m.2, mem_normalizer_iff''.mpr fun h => ⟨fun hh => (key ⟨h, hTM hh⟩).1 hh,
    fun hh => ?_⟩⟩
  have hhM : h ∈ M := by
    have := (mem_normalizer_iff''.mp hmg h).mpr (hTM hh)
    exact this
  exact (key ⟨h, hhM⟩).2 hh

end CFSG.ComponentClassification.GrSLit.L34Facts
