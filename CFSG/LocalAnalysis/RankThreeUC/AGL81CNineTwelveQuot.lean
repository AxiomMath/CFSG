module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

private theorem relPPrimeCore_eq_map' {p : ℕ} (hp : p.Prime) (C : Subgroup G) :
    CFSG.Open.relPPrimeCore p C = (primeComplementCore (G := ↥C) p).map C.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNC, hNn, hNc⟩ := hN
    have h1 : N.subgroupOf C ≤ primeComplementCore (G := ↥C) p := by
      refine le_sSup ⟨hNn, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
      exact hNc
    calc N = (N.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hNC).symm
      _ ≤ _ := Subgroup.map_mono h1
  · refine le_sSup ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · show (Subgroup.comap C.subtype
          ((primeComplementCore (G := ↥C) p).map C.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      infer_instance
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card

private lemma range_comp_inclusion_mk'_eq_starImg {p : ℕ} {H A : Subgroup G} (hAH : A ≤ H) :
    ((QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp
        (Subgroup.inclusion hAH)).range = starImg p H A := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

private lemma ker_comp_inclusion_mk'_eq_relPPrimeCore_subgroupOf {p : ℕ} (hp : p.Prime)
    {H A : Subgroup G} (hAH : A ≤ H) :
    ((QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp
        (Subgroup.inclusion hAH)).ker
      = (CFSG.Open.relPPrimeCore p H).subgroupOf A := by
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let ι : ↥A →* ↥H := Subgroup.inclusion hAH
  let ρ : ↥A →* ↥H ⧸ O := (QuotientGroup.mk' O).comp ι
  have hO : O.map H.subtype = CFSG.Open.relPPrimeCore p H :=
    (relPPrimeCore_eq_map' hp H).symm
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hO]
  constructor
  · intro ha
    have h1 : ι a ∈ O := (QuotientGroup.eq_one_iff (ι a)).mp ha
    exact Subgroup.mem_map_of_mem H.subtype h1
  · intro ha
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha
    have hia : ι a = b := Subtype.ext (by
      show ((ι a : ↥H) : G) = (b : G)
      exact hba.symm)
    have : ι a ∈ O := by rwa [← hia] at hb
    exact (QuotientGroup.eq_one_iff (ι a)).mpr this

private lemma index_relPPrimeCore_subgroupOf_eq_card_starImg {p : ℕ} (hp : p.Prime)
    {H A : Subgroup G} (hAH : A ≤ H) :
    ((CFSG.Open.relPPrimeCore p H).subgroupOf A).index = Nat.card (starImg p H A) := by
  rw [← ker_comp_inclusion_mk'_eq_relPPrimeCore_subgroupOf hp hAH, Subgroup.index_ker,
    range_comp_inclusion_mk'_eq_starImg hAH]

theorem exists_normal_index_eq_of_forall {p : ℕ} (hp : p.Prime) {H A : Subgroup G}
    (hAH : A ≤ H) {B : Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)}
    (hAB : starImg p H A = B) {W : Type} [Group W] (φ : ↥A →* W)
    (hφ : ∀ a : ↥A, (a : G) ∈ CFSG.Open.relPPrimeCore p H → φ a = 1) :
    ∃ N : Subgroup ↥B, N.Normal ∧ N.index = Nat.card φ.range := by
  subst hAB
  let f : ↥A →* ↥H ⧸ primeComplementCore (G := ↥H) p :=
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp (Subgroup.inclusion hAH)
  have hfrange : f.range = starImg p H A := range_comp_inclusion_mk'_eq_starImg hAH
  have hfker : f.ker = (CFSG.Open.relPPrimeCore p H).subgroupOf A :=
    ker_comp_inclusion_mk'_eq_relPPrimeCore_subgroupOf hp hAH
  let ρ' : ↥A →* ↥(starImg p H A) := f.codRestrict (starImg p H A) (fun a => hfrange ▸ ⟨a, rfl⟩)
  have hρ'surj : Function.Surjective ρ' := by
    intro y
    have hy : (y : ↥H ⧸ primeComplementCore (G := ↥H) p) ∈ f.range :=
      hfrange.symm ▸ y.2
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hy
    exact ⟨a, Subtype.ext (by simpa [ρ'] using ha)⟩
  have hle : ρ'.ker ≤ φ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    have ha' : a ∈ f.ker := by simpa [ρ'] using ha
    rw [hfker] at ha'
    exact hφ a (Subgroup.mem_subgroupOf.mp ha')
  let g : ↥(starImg p H A) →* W := (ρ'.liftOfSurjective hρ'surj) ⟨φ, hle⟩
  have hgcomp : g.comp ρ' = φ := by
    have hsymm := Equiv.symm_apply_apply (ρ'.liftOfSurjective hρ'surj) ⟨φ, hle⟩
    simpa [g] using congrArg Subtype.val hsymm
  have hgrange : g.range = φ.range := by
    have h1 : (g.comp ρ').range = φ.range := by rw [hgcomp]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hρ'surj, Subgroup.map_top] at h1
    exact h1
  exact ⟨g.ker, MonoidHom.normal_ker g, by rw [Subgroup.index_ker, hgrange]⟩

theorem card_range_dvd_card_map_mul_card_starImg {p : ℕ} (hp : p.Prime) {H A : Subgroup G}
    (hAH : A ≤ H) {W : Type} [Group W] (φ : ↥A →* W) :
    Nat.card φ.range ∣
      Nat.card (((CFSG.Open.relPPrimeCore p H).subgroupOf A).map φ) *
        Nat.card (starImg p H A) := by
  let J : Subgroup ↥A := (CFSG.Open.relPPrimeCore p H).subgroupOf A
  let ψ : ↥A →* ↥φ.range := φ.rangeRestrict
  have hJ : J.index = Nat.card (starImg p H A) :=
    index_relPPrimeCore_subgroupOf_eq_card_starImg hp hAH
  have hcard2 : Nat.card (J.map ψ) = Nat.card (J.map φ) := by
    have h1 : J.map φ = (J.map ψ).map φ.range.subtype := by
      rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
    rw [h1, Subgroup.card_map_of_injective φ.range.subtype_injective]
  have hcard3 : Nat.card φ.range = Nat.card (J.map ψ) * (J.map ψ).index :=
    (Subgroup.card_mul_index (H := J.map ψ)).symm
  have hdvd : (J.map ψ).index ∣ Nat.card (starImg p H A) := by
    rw [← hJ]
    exact Subgroup.index_map_dvd (H := J) (MonoidHom.rangeRestrict_surjective φ)
  obtain ⟨d, hd⟩ := hdvd
  rw [hcard3, hcard2]
  exact ⟨d, by rw [hd]; ring⟩

theorem not_dvd_card_map_of_isSylowOf {q : ℕ} [Fact q.Prime] {N R A : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf q R N) (hAR : A ≤ normalizer (R : Set G))
    {W : Type} [Group W] (φ : ↥A →* W) (hφ : ∀ a : ↥A, (a : G) ∈ R → φ a = 1) :
    ¬ q ∣ Nat.card ((N.subgroupOf A).map φ) := by
  let J : Subgroup ↥A := N.subgroupOf A
  let ψ : ↥J →* W := φ.comp J.subtype
  have hψrange : ψ.range = J.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨S, hS⟩ := hR
  have hRq : IsPGroup q R := hS ▸ S.isPGroup'.map N.subtype
  have hRN : R ≤ N := by
    intro x hx
    rw [← hS] at hx
    obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact s.2
  let T : Sylow q ↥J := Classical.choice (inferInstance : Nonempty (Sylow q ↥J))
  let T₀ : Subgroup G := ((T : Subgroup ↥J).map J.subtype).map A.subtype
  have hT0q : IsPGroup q T₀ := (T.isPGroup'.map J.subtype).map A.subtype
  have hT0A : T₀ ≤ A := Subgroup.map_subtype_le _
  have hT0N : T₀ ≤ N := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_subgroupOf.mp t.2
  have hT0norm : T₀ ≤ normalizer (R : Set G) := hT0A.trans hAR
  have hsupq : IsPGroup q (T₀ ⊔ R : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hT0q hRq hT0norm
  have hsupN : T₀ ⊔ R ≤ N := sup_le hT0N hRN
  have hQ : IsPGroup q ((T₀ ⊔ R).subgroupOf N) := hsupq.comap_subtype (K := N)
  have hle : (S : Subgroup ↥N) ≤ (T₀ ⊔ R).subgroupOf N := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := N.subtype) N.subtype_injective]
    rw [hS, Subgroup.map_subgroupOf_eq_of_le hsupN]
    exact le_sup_right
  have hEq : (T₀ ⊔ R).subgroupOf N = S := S.is_maximal' hQ hle
  have hsup_eq_R : T₀ ⊔ R = R := by
    have h1 : ((T₀ ⊔ R).subgroupOf N).map N.subtype = T₀ ⊔ R := by
      rw [Subgroup.map_subgroupOf_eq_of_le hsupN]
    calc T₀ ⊔ R = ((T₀ ⊔ R).subgroupOf N).map N.subtype := h1.symm
      _ = (S : Subgroup ↥N).map N.subtype := by rw [hEq]
      _ = R := hS
  have hT0leR : T₀ ≤ R := sup_eq_right.mp hsup_eq_R
  have hTleker : (T : Subgroup ↥J) ≤ ψ.ker := by
    intro t ht
    rw [MonoidHom.mem_ker]
    have h1 : ((J.subtype t : ↥A) : G) ∈ T₀ :=
      Subgroup.mem_map_of_mem A.subtype (Subgroup.mem_map_of_mem J.subtype ht)
    exact hφ (J.subtype t) (hT0leR h1)
  have hkerindex : ψ.ker.index ∣ (T : Subgroup ↥J).index := Subgroup.index_dvd_of_le hTleker
  have hcard : Nat.card ψ.range = ψ.ker.index := (Subgroup.index_ker ψ).symm
  have hnotdvd : ¬ q ∣ (T : Subgroup ↥J).index := Sylow.not_dvd_index T
  intro hq
  apply hnotdvd
  rw [← hψrange, hcard] at hq
  exact hq.trans hkerindex

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
