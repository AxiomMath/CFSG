module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovals
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneUnique
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovals
public import Certificates.Certificate2028
public import Certificates.Certificate2037
public import Certificates.Certificate2038
public import Certificates.Certificate2040

public section

namespace CFSG.ComponentClassification.WittDesign

open CFSG.Monster.B.Classical.Plane

@[expose] def modelBlocks (𝒞 : List (Finset (Fin 21))) : Finset (Finset (Option (Fin 21))) :=
  (Finset.univ.image fun a => insert none ((projLine a).map Function.Embedding.some)) ∪
    𝒞.toFinset.image fun X => X.map Function.Embedding.some

theorem card_modelBlocks_le (𝒞 : List (Finset (Fin 21))) (h𝒞 : 𝒞.length = 56) :
    (modelBlocks 𝒞).card ≤ 77 := by
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := (Finset.card_image_le (s := (Finset.univ : Finset (Fin 21)))
    (f := fun a => insert none ((projLine a).map Function.Embedding.some)))
  have h2 := (Finset.card_image_le (s := 𝒞.toFinset)
    (f := fun X : Finset (Fin 21) => X.map Function.Embedding.some))
  have h3 := List.toFinset_card_le 𝒞
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem delta_cube : ∀ x, deltaPerm (deltaPerm (deltaPerm x)) = x :=
  Certificates.certificate2040

@[expose] def deltaOpt : Equiv.Perm (Option (Fin 21)) := Equiv.optionCongr deltaPerm

theorem map_deltaOpt_mem {i : Fin 3} {C : Finset (Option (Fin 21))}
    (hC : C ∈ modelBlocks (hyperClass i)) :
    C.map deltaOpt.toEmbedding ∈ modelBlocks (hyperClass (i + 1)) := by
  rcases Finset.mem_union.1 hC with h | h
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨b, hb⟩ := (mem_lineAut.1 deltaPerm_mem_lineAut) a
    refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨b, Finset.mem_univ _, ?_⟩)
    rw [← hb, Finset.map_insert, Finset.map_map, Finset.map_map]
    rfl
  · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 h
    refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨X.map deltaPerm.toEmbedding,
      List.mem_toFinset.2 (map_delta_class i (List.mem_toFinset.1 hX)), ?_⟩)
    rw [Finset.map_map, Finset.map_map]
    rfl

theorem map_deltaOpt_three (C : Finset (Option (Fin 21))) :
    ((C.map deltaOpt.toEmbedding).map deltaOpt.toEmbedding).map deltaOpt.toEmbedding = C := by
  ext y
  simp only [Finset.mem_map_equiv]
  have h : ∀ z : Option (Fin 21), deltaOpt (deltaOpt (deltaOpt z)) = z := by
    rintro (_ | z)
    · rfl
    · simp [deltaOpt, delta_cube]
  have h' : deltaOpt.symm (deltaOpt.symm (deltaOpt.symm y)) = y := by
    rw [← h (deltaOpt.symm (deltaOpt.symm (deltaOpt.symm y)))]
    simp
  rw [h']

theorem map_deltaOpt_mem_iff (i : Fin 3) (C : Finset (Option (Fin 21))) :
    C ∈ modelBlocks (hyperClass i) ↔
      C.map deltaOpt.toEmbedding ∈ modelBlocks (hyperClass (i + 1)) := by
  refine ⟨map_deltaOpt_mem, fun h => ?_⟩
  have h3 := map_deltaOpt_mem (map_deltaOpt_mem h)
  rwa [map_deltaOpt_three, show i + 1 + 1 + 1 = i by fin_cases i <;> rfl] at h3

theorem exists_iso_model_class (i j : Fin 3) : ∃ d : Equiv.Perm (Option (Fin 21)),
    ∀ C, C ∈ modelBlocks (hyperClass i) ↔ C.map d.toEmbedding ∈ modelBlocks (hyperClass j) := by
  have step : ∀ (i : Fin 3) (d : Equiv.Perm (Option (Fin 21))),
      (∀ C, C ∈ modelBlocks (hyperClass i) ↔ C.map d.toEmbedding ∈ modelBlocks (hyperClass j)) →
      ∃ d' : Equiv.Perm (Option (Fin 21)), ∀ C, C ∈ modelBlocks (hyperClass (i + 1)) ↔
        C.map d'.toEmbedding ∈ modelBlocks (hyperClass j) := by
    intro i d hd
    refine ⟨d * deltaOpt⁻¹, fun C => ?_⟩
    rw [map_perm_mul', ← hd]
    have := map_deltaOpt_mem_iff i (C.map deltaOpt⁻¹.toEmbedding)
    rw [← map_perm_mul', mul_inv_cancel,
      show (1 : Equiv.Perm (Option (Fin 21))).toEmbedding = Function.Embedding.refl _ from rfl,
      Finset.map_refl] at this
    exact this.symm
  have h0 : ∃ d : Equiv.Perm (Option (Fin 21)), ∀ C, C ∈ modelBlocks (hyperClass j) ↔
      C.map d.toEmbedding ∈ modelBlocks (hyperClass j) :=
    ⟨1, fun C => by
      rw [show (1 : Equiv.Perm (Option (Fin 21))).toEmbedding = Function.Embedding.refl _ from rfl,
        Finset.map_refl]⟩
  obtain ⟨d₁, hd₁⟩ := h0
  obtain ⟨d₂, hd₂⟩ := step j d₁ hd₁
  obtain ⟨d₃, hd₃⟩ := step (j + 1) d₂ hd₂
  have hi : i = j ∨ i = j + 1 ∨ i = j + 1 + 1 := by
    fin_cases i <;> fin_cases j <;> simp
  rcases hi with rfl | rfl | rfl
  · exact ⟨d₁, hd₁⟩
  · exact ⟨d₂, hd₂⟩
  · exact ⟨d₃, hd₃⟩

section Model

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] in
theorem subtype_inter (B B' : Finset Ω) (p : Ω → Prop) [DecidablePred p] :
    B.subtype p ∩ B'.subtype p = (B ∩ B').subtype p := by
  ext x
  simp

omit [Fintype Ω] in
theorem card_subtype_ne_of_not_mem {B : Finset Ω} {a : Ω} (ha : a ∉ B) :
    (B.subtype (· ≠ a)).card = B.card := by
  rw [Finset.card_subtype, Finset.filter_true_of_mem]
  intro x hx e
  exact ha (e ▸ hx)

theorem exists_iso_model {𝓑 : Finset (Finset Ω)} (h : IsSteinerTriple 𝓑) :
    ∃ (i : Fin 3) (e : Ω ≃ Option (Fin 21)),
      ∀ B, B ∈ 𝓑 ↔ B.map e.toEmbedding ∈ modelBlocks (hyperClass i) := by
  obtain ⟨p⟩ : Nonempty Ω := by
    rw [← Fintype.card_pos_iff, h.card_points]
    norm_num
  obtain ⟨ι, hι⟩ := steinerPlane_iso_projLine (h.derived p)
  set e : Ω ≃ Option (Fin 21) := ((Equiv.optionCongr ι.symm).trans (Equiv.optionSubtypeNe p)).symm
  have he_none : e.symm none = p := rfl
  have he_some : ∀ z, e.symm (some z) = (ι.symm z : Ω) := fun z => rfl
  set arc : Finset Ω → Finset (Fin 21) := fun B => (B.subtype (· ≠ p)).map ι.toEmbedding
    with harc_def
  have hmap : ∀ B : Finset Ω, B.map e.toEmbedding =
      if p ∈ B then insert none ((arc B).map Function.Embedding.some)
      else (arc B).map Function.Embedding.some := by
    intro B
    ext y
    rw [Finset.mem_map_equiv]
    rcases y with _ | z
    · rw [he_none]
      split_ifs with hp
      · simp [hp]
      · simp [hp]
    · rw [he_some]
      have : (ι.symm z : Ω) ∈ B ↔ z ∈ arc B := by
        simp only [arc, Finset.mem_map_equiv, mem_subtype_ne]
      split_ifs <;> simp [this]
  have hline : ∀ B ∈ 𝓑, p ∈ B → ∃ a, arc B = projLine a := by
    intro B hB hp
    have : arc B ∈ Finset.univ.image projLine := by
      rw [← hι]
      exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hB, hp⟩))
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 this
    exact ⟨a, ha.symm⟩
  have hlines : ∀ a, ∃ B ∈ 𝓑, p ∈ B ∧ arc B = projLine a := by
    intro a
    have : projLine a ∈ (derivedLines 𝓑 p).image fun L => L.map ι.toEmbedding := by
      rw [hι]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨L, hL, hLa⟩ := Finset.mem_image.1 this
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hL
    exact ⟨B, (Finset.mem_filter.1 hB).1, (Finset.mem_filter.1 hB).2, hLa⟩
  have harc_card : ∀ B ∈ 𝓑, p ∉ B → (arc B).card = 6 := by
    intro B hB hp
    simp only [harc_def]
    rw [Finset.card_map, card_subtype_ne_of_not_mem hp, h.card_block hB]
  have harc_inter : ∀ B B' : Finset Ω, (arc B ∩ arc B').card ≤ (B ∩ B').card := by
    intro B B'
    simp only [harc_def]
    rw [← Finset.map_inter, Finset.card_map, subtype_inter, Finset.card_subtype]
    exact Finset.card_filter_le _ _
  have harc_inter_eq : ∀ B B' : Finset Ω, p ∉ B → (arc B ∩ arc B').card = (B ∩ B').card := by
    intro B B' hp
    simp only [harc_def]
    rw [← Finset.map_inter, Finset.card_map, subtype_inter,
      card_subtype_ne_of_not_mem (fun h' => hp (Finset.mem_inter.1 h').1)]
  have hsix : ∀ B ∈ 𝓑, p ∉ B → IsSixArc (arc B) := by
    intro B hB hp
    refine ⟨harc_card B hB hp, fun a => ?_⟩
    obtain ⟨B', hB', hpB', hB'a⟩ := hlines a
    rw [← hB'a]
    have hne : B ≠ B' := fun e => hp (e ▸ hpB')
    exact (harc_inter B B').trans (h.card_inter_le hB hB' hne)
  have harc_inj : Set.InjOn arc {B | p ∉ B} := by
    intro B hB B' hB' e
    have e' : B.subtype (· ≠ p) = B'.subtype (· ≠ p) := Finset.map_injective _ e
    ext x
    by_cases hx : x = p
    · subst hx
      exact ⟨fun h => absurd h hB, fun h => absurd h hB'⟩
    · have := congrArg (fun L : Finset {x : Ω // x ≠ p} => (⟨x, hx⟩ : {x : Ω // x ≠ p}) ∈ L) e'
      simpa only [mem_subtype_ne, eq_iff_iff] using this
  set 𝓗 := (𝓑.filter (p ∉ ·)).image arc
  have h𝓗card : 𝓗.card = 56 := by
    show ((𝓑.filter (p ∉ ·)).image arc).card = 56
    rw [Finset.card_image_of_injOn, h.card_blocks_not_mem p]
    intro B hB B' hB' e
    exact harc_inj (Finset.mem_filter.1 hB).2 (Finset.mem_filter.1 hB').2 e
  obtain ⟨B₀, hB₀⟩ : (𝓑.filter (p ∉ ·)).Nonempty := by
    rw [← Finset.card_pos, h.card_blocks_not_mem p]
    norm_num
  rw [Finset.mem_filter] at hB₀
  obtain ⟨i, hi⟩ := mem_hyperClasses (hsix B₀ hB₀.1 hB₀.2)
  have hsub : 𝓗 ⊆ (hyperClass i).toFinset := by
    intro X hX
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hX
    rw [Finset.mem_filter] at hB
    rw [List.mem_toFinset]
    by_cases e : B = B₀
    · rw [e]
      exact hi
    obtain ⟨k, hk⟩ := mem_hyperClasses (hsix B hB.1 hB.2)
    by_cases hki : k = i
    · exact hki ▸ hk
    exfalso
    have hodd := card_inter_odd hki hk hi
    rw [harc_inter_eq B B₀ hB.2] at hodd
    rcases h.card_inter hB.1 hB₀.1 e with h0 | h2 <;> omega
  have h𝓗eq : 𝓗 = (hyperClass i).toFinset := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [h𝓗card, List.toFinset_card_of_nodup (nodup_hyperClass i), length_hyperClass]
  refine ⟨i, e, ?_⟩
  have himg : 𝓑.image (fun B => B.map e.toEmbedding) ⊆ modelBlocks (hyperClass i) := by
    intro C hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hC
    rw [hmap B]
    split_ifs with hp
    · obtain ⟨a, ha⟩ := hline B hB hp
      rw [ha]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
    · refine Finset.mem_union_right _ (Finset.mem_image_of_mem _ ?_)
      rw [← h𝓗eq]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hB, hp⟩)
  have heq : 𝓑.image (fun B => B.map e.toEmbedding) = modelBlocks (hyperClass i) := by
    refine Finset.eq_of_subset_of_card_le himg ?_
    rw [Finset.card_image_of_injective _ (Finset.map_injective _), h.card_blocks]
    exact card_modelBlocks_le _ (length_hyperClass i)
  intro B
  rw [← heq]
  constructor
  · exact fun hB => Finset.mem_image_of_mem _ hB
  · intro hB
    obtain ⟨B', hB', e'⟩ := Finset.mem_image.1 hB
    rwa [← Finset.map_injective _ e']

end Model

theorem steinerTriple_iso {Ω : Type*} {Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] {𝓑 : Finset (Finset Ω)} {𝓑' : Finset (Finset Ω')} (h : IsSteinerTriple 𝓑)
    (h' : IsSteinerTriple 𝓑') :
    ∃ e : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝓑 ↔ B.map e.toEmbedding ∈ 𝓑' := by
  obtain ⟨i, e₁, he₁⟩ := exists_iso_model h
  obtain ⟨j, e₂, he₂⟩ := exists_iso_model h'
  obtain ⟨d, hd⟩ := exists_iso_model_class i j
  refine ⟨e₁.trans (d.trans e₂.symm), fun B => ?_⟩
  have e : (B.map e₁.toEmbedding).map d.toEmbedding =
      (B.map (e₁.trans (d.trans e₂.symm)).toEmbedding).map e₂.toEmbedding := by
    rw [Finset.map_map, Finset.map_map]
    congr 1
    ext x
    simp
  rw [he₁, hd, he₂, e]

end CFSG.ComponentClassification.WittDesign
