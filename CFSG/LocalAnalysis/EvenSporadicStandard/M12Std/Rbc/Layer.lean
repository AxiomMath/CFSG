module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Concat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.PGroups
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompAt
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

variable {G : Type} [Group G] [Finite G]

theorem le_layerIn_centralizer_of_lemma15 (h15 : FS79Lemma15At G)
    (hKp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hO : CFSG.oddCore G = ⊥)
    {T₀ T₁ K : Subgroup G} (hT₀ : IsPGroup 2 T₀) (hle : T₁ ≤ T₀)
    (hK : IsCompIn K (centralizer (T₀ : Set G))) :
    K ≤ layerIn (centralizer (T₁ : Set G)) := by
  have h1 := (h15 hKp T₀ hT₀).1 T₁ hle
  rw [(h15 hKp T₀ hT₀).2 hO, (h15 hKp T₁ (hT₀.to_le hle)).2 hO] at h1
  exact (Junction.le_layerIn_of_isCompIn hK).trans h1

private theorem exists_tLinks_to_inLF_aux (h15 : FS79Lemma15At G)
    (hKp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hO : CFSG.oddCore G = ⊥) (n : ℕ) :
    ∀ {T₀ K : Subgroup G}, Nat.card T₀ = n → IsPGroup 2 T₀ → T₀ ≠ ⊥ →
      IsCompIn K (centralizer (T₀ : Set G)) →
      ∃ a L T s, TLinks G a L T s ∧ L 0 = K ∧ InLF (L a) ∧ ∀ i ≤ a, T i ≠ ⊥ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T₀ K hn hT₀ hT₀1 hK
    obtain ⟨T₁, u, -, hT₁le, huT₀, huT₁, hu2, hconj, hcover⟩ :=
      Junction.exists_index_two hT₀ bot_le hT₀1.symm
    have hT₁ : IsPGroup 2 T₁ := hT₀.to_le hT₁le
    have hu : u ∈ normalizer (T₁ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hconj u huT₀ x hx, fun hx => ?_⟩
      have := hconj u⁻¹ (T₀.inv_mem huT₀) _ hx
      simpa [mul_assoc] using this
    have hsup : T₁ ⊔ zpowers u = T₀ := by
      refine le_antisymm (sup_le hT₁le (zpowers_le.2 huT₀)) fun g hg => ?_
      rcases hcover g hg with h | h
      · exact Subgroup.mem_sup_left h
      · have hg' : g = u * (u⁻¹ * g) := by group
        rw [hg']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers u))
          (Subgroup.mem_sup_left h)
    have hKc : IsCompIn K (centralizer ((T₁ ⊔ zpowers u : Subgroup G) : Set G)) := by
      rw [hsup]
      exact hK
    have hlt : T₁ < T₀ := lt_of_le_of_ne hT₁le fun h => huT₁ (h ▸ huT₀)
    have hcard : Nat.card T₁ < n := by
      rw [← hn]
      exact Subgroup.card_lt_of_lt hlt
    by_cases hT₁1 : T₁ = ⊥
    ·
      subst hT₁1
      rw [bot_sup_eq] at hsup
      have hsq : u ^ 2 = 1 := Subgroup.mem_bot.1 hu2
      have hne : u ≠ 1 := fun h => huT₁ (by rw [h]; exact Subgroup.one_mem _)
      refine ⟨0, fun _ => K, fun _ => T₀, fun _ => 1, TLinks.singleton hT₀ hK, rfl, ?_,
        fun _ _ => hT₀1⟩
      refine ⟨u, orderOf_eq_prime hsq hne, ?_⟩
      rw [← centralizer_zpowers_eq, hsup]
      exact hK
    · have hKL : K ≤ layerIn (centralizer (T₁ : Set G)) :=
        le_layerIn_centralizer_of_lemma15 h15 hKp hO hT₀ hT₁le hK
      have hT₁' : T₁ ⊔ zpowers u ≠ ⊥ := fun h => hT₁1 (le_bot_iff.1 (h ▸ le_sup_left))
      rcases pumpUp_trichotomy hu hu2 hKc hKL with hKT | ⟨M, hM, -, hlink, hle, hcl⟩
      ·
        exact ih (Nat.card T₁) hcard (T₀ := T₁) (K := K) rfl hT₁ hT₁1 hKT
      ·
        obtain ⟨a, L, T, s, hl, h0, hin, hT⟩ :=
          ih (Nat.card T₁) hcard (T₀ := T₁) (K := M) rfl hT₁ hT₁1 hM
        have hjoin : L 0 = seq2 K M 1 := by simp [seq2, h0]
        refine ⟨1 + a, concat 1 (seq2 K M) L, concat 1 (seq2 (T₁ ⊔ zpowers u) T₁) T,
          concat 1 (seq2 1 u) s,
          (tLinks_single hT₁ hu hu2 hKc hM hlink hle hcl).append hl hjoin, ?_, ?_, ?_⟩
        · rw [concat_of_le (Nat.zero_le 1)]
          simp
        · rw [concat_add hjoin]
          exact hin
        · exact forall_le_concat (P := fun x => x ≠ ⊥) (seq2_ne_bot hT₁' hT₁1) hT

theorem exists_tLinks_to_inLF (h15 : FS79Lemma15At G)
    (hKp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hO : CFSG.oddCore G = ⊥)
    {T₀ K : Subgroup G} (hT₀ : IsPGroup 2 T₀) (hT₀1 : T₀ ≠ ⊥)
    (hK : IsCompIn K (centralizer (T₀ : Set G))) :
    ∃ a L T s, TLinks G a L T s ∧ L 0 = K ∧ InLF (L a) ∧ ∀ i ≤ a, T i ≠ ⊥ :=
  exists_tLinks_to_inLF_aux h15 hKp hO (Nat.card T₀) rfl hT₀ hT₀1 hK

end CFSG.EvenSporadicStandard.M12Std.Rbc
