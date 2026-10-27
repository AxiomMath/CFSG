module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Native
public import CFSG.LieType.SeitzGeneration.ExcHigh.Generic

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

section Embedding

theorem planeCl_eq_top_of_embedded_high {r : ℕ} {F M : Type*} [Group F] [Group M]
    (hF : ∀ E₃ : Subgroup F, (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
      ¬ NormalizesRIn r E₃ → planeCl E₃ = ⊤)
    {E₀ : Subgroup M} (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 2)
    (hn : ¬ NormalizesRIn r E₀) (g : M) (ι : F →* M) (E₃ : Subgroup F)
    (hι : Function.Injective ι) (hE₃ : E₃.map ι = E₀.map (MulAut.conj g).toMonoidHom)
    {e : F} (he : e ∈ E₃) (he1 : e ≠ 1)
    (hgen : Subgroup.closure
      ((ι.range : Set M) ∪ (Subgroup.centralizer ({ι e} : Set M) : Set M)) = ⊤) :
    planeCl E₀ = ⊤ := by
  have hE₃c : Nat.card E₃ = 3 ^ 2 := by
    have h1 : Nat.card (E₃.map ι) = Nat.card E₃ := Subgroup.card_map_of_injective hι
    have h2 : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = Nat.card E₀ :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [← h1, hE₃, h2, hcard]
  have hE₃p : ∀ x ∈ E₃, x ^ 3 = 1 := by
    intro x hx
    have hmem : ι x ∈ E₀.map (MulAut.conj g).toMonoidHom := hE₃ ▸ Subgroup.mem_map_of_mem ι hx
    obtain ⟨y, hy, hyx⟩ := hmem
    apply hι
    rw [map_pow, map_one, ← hyx, ← map_pow, hexp y hy, map_one]
  have hnF : ¬ NormalizesRIn r E₃ := by
    rintro ⟨R₃, hR1, hRp, hRn⟩
    apply hn
    set R₆ : Subgroup M := R₃.map ι with hR₆
    have hR₆1 : R₆ ≠ ⊥ := fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective R₃ hι).mp h)
    have hR₆p : IsPGroup r R₆ :=
      hRp.of_surjective (ι.subgroupMap R₃) (ι.subgroupMap_surjective R₃)
    have hnorm₆ : E₃.map ι ≤ Subgroup.normalizer (R₆ : Set M) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_conj_eq_iff_mem_normalizer]
      have hxn := (map_conj_eq_iff_mem_normalizer R₃ x).2 (hRn hx)
      have hcomp : (MulAut.conj (ι x)).toMonoidHom.comp ι = ι.comp (MulAut.conj x).toMonoidHom := by
        ext z
        simp [MulAut.conj_apply]
      rw [hR₆, Subgroup.map_map, hcomp, ← Subgroup.map_map, hxn]
    refine ⟨R₆.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
    · exact fun h =>
        hR₆1 ((Subgroup.map_eq_bot_iff_of_injective R₆ (MulAut.conj g⁻¹).injective).mp h)
    · exact hR₆p.of_surjective ((MulAut.conj g⁻¹).toMonoidHom.subgroupMap R₆)
        ((MulAut.conj g⁻¹).toMonoidHom.subgroupMap_surjective R₆)
    · intro y hy
      rw [mem_normalizer_map_conj_iff, inv_inv]
      exact hnorm₆ (hE₃ ▸ Subgroup.mem_map_of_mem _ hy)
  have h3 : planeCl E₃ = ⊤ := hF E₃ hE₃p hE₃c hnF
  have h4 : planeCl (E₃.map ι) = ⊤ := planeCl_eq_top_of_embedding ι hι h3 he he1 hgen
  rw [hE₃] at h4
  exact CFSG.LieType.SeitzGeneration.ExcHigh.closure_centralizers_eq_top_of_map_conj_eq_top g E₀ h4

end Embedding

section TwistedF4


theorem twE6ThreeNative_of_F4 {ε : ℕ} (hF : F4ThreeNative ε) (hE : TwE6HighInF4 ε) :
    TwE6ThreeNative ε := by
  intro q K _ _ σ hK hσ hq E₀ hexp hcard hn
  obtain ⟨k, _, _, g, ι, E₃, hk, hr, hι, hE₃, e, he, he1, hgen⟩ :=
    hE q K σ hK hσ hq E₀ hexp hcard hn
  refine planeCl_eq_top_of_embedded_high (r := ringChar K)
    (fun E₃ h1 h2 h3 => hF k (by rw [hk]; exact hq) E₃ h1 h2
      (by rw [NormalizesRNative, hr]; exact h3))
    hexp hcard hn g ι E₃ hι hE₃ he he1 hgen

end TwistedF4

section E6

theorem e6ThreeNative_of_F4 {ε : ℕ} (hF : F4ThreeNative ε) (hE : E6HighInF4 ε) :
    E6ThreeNative ε := by
  intro K _ _ hres E₀ hexp hcard hn
  obtain ⟨g, ι, E₃, hι, hE₃, e, he, he1, hgen⟩ := hE K hres E₀ hexp hcard hn
  exact planeCl_eq_top_of_embedded_high (r := ringChar K) (fun E₃ h1 h2 h3 => hF K hres E₃ h1 h2 h3)
    hexp hcard hn g ι E₃ hι hE₃ he he1 hgen

end E6

end CFSG.LieType.SeitzGeneration.ExcHighThree
