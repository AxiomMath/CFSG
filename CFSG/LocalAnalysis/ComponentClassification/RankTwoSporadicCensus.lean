module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCore
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open

variable {W U : Type*} [Group W] [Group U]

section Transport

variable (ι : W →* U) (hι : Function.Injective ι)
include hι

theorem map_centralizer_singleton (t : W) :
    (centralizer ({t} : Set W)).map ι = ι.range ⊓ centralizer ({ι t} : Set U) := by
  ext y
  simp only [mem_map, mem_inf, MonoidHom.mem_range, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, by rw [← map_mul, ← map_mul, hx]⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, hι ?_, rfl⟩
    rw [map_mul, map_mul, hx]

theorem map_inf_centralizer (X : Subgroup W) (t : W) :
    (X ⊓ centralizer ({t} : Set W)).map ι = X.map ι ⊓ centralizer ({ι t} : Set U) := by
  rw [map_inf_eq _ _ _ hι, map_centralizer_singleton ι hι]
  rw [← inf_assoc, inf_eq_left.mpr (map_le_range ι X)]

theorem map_centDer (X : Subgroup W) (t : W) :
    (centDer X t).map ι = centDer (X.map ι) (ι t) := by
  rw [centDer, centDer, map_commutator, map_inf_centralizer ι hι]

theorem map_gammaE (X E : Subgroup W) :
    (gammaE X E).map ι = gammaE (X.map ι) (E.map ι) := by
  rw [gammaE, gammaE, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ht => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ht1 => ?_
    rw [map_centDer ι hι]
    exact le_iSup₂_of_le (ι t) ⟨t, ht, rfl⟩
      (le_iSup_of_le (fun h => ht1 (hι (h.trans (map_one ι).symm))) le_rfl)
  · refine iSup₂_le fun u hu => iSup_le fun hu1 => ?_
    obtain ⟨t, ht, rfl⟩ := hu
    rw [← map_centDer ι hι]
    refine le_iSup_of_le t ?_
    rw [Subgroup.map_iSup]
    refine le_iSup_of_le ht ?_
    rw [Subgroup.map_iSup]
    exact le_iSup_of_le (fun h => hu1 (by rw [h, map_one])) le_rfl

theorem map_nE (X E : Subgroup W) : (nE X E).map ι = nE (X.map ι) (E.map ι) := by
  rw [nE, nE, map_commutator, map_gammaE ι hι]

theorem card_map_inf (X E : Subgroup W) :
    Nat.card ↥(E.map ι ⊓ X.map ι) = Nat.card ↥(E ⊓ X) := by
  rw [← map_inf_eq _ _ _ hι, card_map_of_injective hι]

theorem yWitness_map_iff (X E : Subgroup W) :
    YWitness (X.map ι) (E.map ι) ↔ YWitness X E := by
  unfold YWitness
  rw [← map_nE ι hι, card_map_inf ι hι]
  constructor
  · rintro (⟨_, ⟨w, hw, rfl⟩, h4⟩ | ⟨P, hP, hP2, hcard⟩)
    · exact Or.inl ⟨w, hw, by rwa [orderOf_injective ι hι] at h4⟩
    · refine Or.inr ⟨P.comap ι, fun x hx => ?_, ?_, ?_⟩
      · obtain ⟨y, hy, he⟩ := hP hx
        rw [← hι he]
        exact hy
      · exact hP2.comap_of_injective ι hι
      · have hle : P ≤ ι.range := hP.trans (map_le_range ι _)
        have hc : Nat.card (P.comap ι) = Nat.card P := by
          rw [← card_map_of_injective hι, map_comap_eq_self hle]
        rwa [hc]
  · rintro (⟨w, hw, h4⟩ | ⟨P, hP, hP2, hcard⟩)
    · exact Or.inl ⟨ι w, ⟨w, hw, rfl⟩, by rwa [orderOf_injective ι hι]⟩
    · exact Or.inr ⟨P.map ι, map_mono hP, hP2.map ι, by rwa [card_map_of_injective hι]⟩

theorem pWitness_map_iff (X E : Subgroup W) :
    PWitness (X.map ι) (E.map ι) ↔ PWitness X E := by
  unfold PWitness
  rw [← map_gammaE ι hι]
  constructor
  · rintro ⟨P', hP'Γ, hP'perf, hEP', x', hx'P, hx'2, hP'gen⟩
    have hle : P' ≤ ι.range := hP'Γ.trans (map_le_range ι _)
    set P := P'.comap ι with hPdef
    have hPmap : P.map ι = P' := map_comap_eq_self hle
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ P, ι x = x' := by
      obtain ⟨x, rfl⟩ := hle hx'P
      exact ⟨x, hx'P, rfl⟩
    refine ⟨P, ?_, ?_, ?_, x, hx, ?_, ?_⟩
    · rw [← map_le_map_iff_of_injective hι, hPmap]
      exact hP'Γ
    · apply map_injective hι
      rw [map_commutator, hPmap, hP'perf]
    · intro hEP
      apply hEP'
      rintro _ ⟨e, he, rfl⟩
      rw [mem_centralizer_iff]
      intro y hy
      rw [← hPmap] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (hEP he) p hp]
    · have := hx'2.comap_of_injective ι hι
      rwa [← MonoidHom.map_zpowers, comap_map_eq_self_of_injective hι] at this
    · rw [← map_le_map_iff_of_injective hι, hPmap, MonoidHom.map_closure]
      refine hP'gen.trans (closure_mono ?_)
      rintro _ ⟨p', hp', rfl⟩
      rw [← hPmap] at hp'
      obtain ⟨p, hp, rfl⟩ := hp'
      exact ⟨p * x ^ 2 * p⁻¹, ⟨p, hp, rfl⟩, by simp⟩
  · rintro ⟨P, hPΓ, hPperf, hEP, x, hx, hx2, hPgen⟩
    refine ⟨P.map ι, map_mono hPΓ, by rw [← map_commutator, hPperf], ?_, ι x, ⟨x, hx, rfl⟩,
      ?_, ?_⟩
    · intro hEP'
      apply hEP
      intro e he
      rw [mem_centralizer_iff]
      intro p hp
      have := mem_centralizer_iff.mp (hEP' ⟨e, he, rfl⟩) (ι p) ⟨p, hp, rfl⟩
      rw [← map_mul, ← map_mul] at this
      exact hι this
    · rw [← MonoidHom.map_zpowers]
      exact hx2.map ι
    · refine (map_mono hPgen).trans ?_
      rw [MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨ι p, ⟨p, hp, rfl⟩, by simp⟩

end Transport

section Mono

theorem gammaE_mono (X : Subgroup W) {E₀ E : Subgroup W} (h : E₀ ≤ E) :
    gammaE X E₀ ≤ gammaE X E :=
  iSup₂_le fun t ht => iSup_le fun ht1 => le_iSup₂_of_le t (h ht) (le_iSup_of_le ht1 le_rfl)

theorem nE_mono (X : Subgroup W) {E₀ E : Subgroup W} (h : E₀ ≤ E) : nE X E₀ ≤ nE X E :=
  commutator_mono h (gammaE_mono X h)

theorem yWitness_of_le_of_orderOf {X E₀ E : Subgroup W} (h : E₀ ≤ E)
    (hw : ∃ w ∈ nE X E₀, 4 ∣ orderOf w) : YWitness X E := by
  obtain ⟨w, hw, h4⟩ := hw
  exact Or.inl ⟨w, nE_mono X h hw, h4⟩

theorem pWitness_of_le {X E₀ E : Subgroup W} (h : E₀ ≤ E) (hP : PWitness X E₀) :
    PWitness X E := by
  obtain ⟨P, hPΓ, hPperf, hEP, x, hx, hx2, hPgen⟩ := hP
  exact ⟨P, hPΓ.trans (gammaE_mono X h), hPperf, fun hle => hEP (h.trans hle), x, hx, hx2, hPgen⟩

end Mono

section Sylow

variable [Finite W]

omit [Finite W] in
theorem map_conj_eq_of_normal {X : Subgroup W} (hX : X.Normal) (w : W) :
    X.map (MulAut.conj w).toMonoidHom = X :=
  (mem_normalizer_iff_map_conj_eq).mp (normalizer_eq_top_iff.mpr hX ▸ mem_top w)

omit [Finite W] in
theorem isPGroup_of_isElemAbelian {E : Subgroup W} (hE : IsElemAbelian 2 E) : IsPGroup 2 E :=
  CFSG.Open.IsElemAbelian.isPGroup hE

omit [Finite W] in
theorem isElemAbelian_map {E : Subgroup W} (hE : IsElemAbelian 2 E) (f : W →* U) :
    IsElemAbelian 2 (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem yCensus_of_le_sylow {X S : Subgroup W} (hX : X.Normal)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤)
    {Exc : Subgroup W → Prop}
    (hExc : ∀ (E : Subgroup W) (w : W), Exc (E.map (MulAut.conj w).toMonoidHom) → Exc E)
    (h : ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E → ¬ Exc E → YWitness X E) :
    YCensus X Exc := by
  intro E hE hE4 hExcE
  obtain ⟨m, -, hm⟩ := exists_conj_le_of_isSylowOf hS (isPGroup_of_isElemAbelian hE) le_top
  set σ := MulAut.conj m⁻¹
  have hle : E.map σ.toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [σ, MulAut.conj_apply] using hm x hx
  have hw := h _ hle (isElemAbelian_map hE _)
    (by rwa [card_map_of_injective σ.injective])
    (fun hc => hExcE (hExc E m⁻¹ hc))
  rwa [← map_conj_eq_of_normal hX m⁻¹, yWitness_map_iff σ.toMonoidHom σ.injective] at hw

theorem yCensus17_of_le_sylow {X S : Subgroup W} (hX : X.Normal)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {Exc : Subgroup W → Prop}
    (hExc : ∀ (E : Subgroup W) (w : W), Exc (E.map (MulAut.conj w).toMonoidHom) → Exc E)
    (h : ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E → ¬ Exc E →
      YWitness X E ∨ PWitness X E) :
    YCensus17 X Exc := by
  intro E hE hE4 hExcE
  obtain ⟨m, -, hm⟩ := exists_conj_le_of_isSylowOf hS (isPGroup_of_isElemAbelian hE) le_top
  set σ := MulAut.conj m⁻¹
  have hle : E.map σ.toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [σ, MulAut.conj_apply] using hm x hx
  have hw := h _ hle (isElemAbelian_map hE _)
    (by rwa [card_map_of_injective σ.injective])
    (fun hc => hExcE (hExc E m⁻¹ hc))
  rwa [← map_conj_eq_of_normal hX m⁻¹, yWitness_map_iff σ.toMonoidHom σ.injective,
    pWitness_map_iff σ.toMonoidHom σ.injective] at hw

end Sylow

end CFSG.ComponentClassification.RankTwoSporadic
