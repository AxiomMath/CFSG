module

public import CFSG.Goldschmidt75.Descent
public import CFSG.Goldschmidt75.Quotient

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped Pointwise

universe u

section Rel

variable {G : Type*} [Group G]

@[expose] def BaRel (S : Subgroup G) (U V : Set G) : Prop :=
  ∃ n ∈ normalizer (S : Set G), rconj n ((S : Set G) * U) = (S : Set G) * V

theorem rconj_mul_subgroup {S : Subgroup G} {n : G} (hn : n ∈ normalizer (S : Set G))
    (U : Set G) : rconj n ((S : Set G) * U) = (S : Set G) * rconj n U := by
  rw [rconj_mul_set, rconj_eq_of_mem_normalizer hn]

theorem baRel_equivalence (S : Subgroup G) : Equivalence (BaRel S) where
  refl U := ⟨1, (normalizer _).one_mem, by rw [rconj_one]⟩
  symm := by
    rintro U V ⟨n, hn, h⟩
    refine ⟨n⁻¹, (normalizer _).inv_mem hn, ?_⟩
    rw [← h, rconj_inv_rconj]
  trans := by
    rintro U V W ⟨n, hn, h⟩ ⟨m, hm, h'⟩
    refine ⟨n * m, (normalizer _).mul_mem hn hm, ?_⟩
    rw [rconj_mul, h, h']

theorem subgroup_mul_of_le {S S₁ : Subgroup G} (h : S₁ ≤ S) :
    (S : Set G) * (S₁ : Set G) = S := by
  apply le_antisymm
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact S.mul_mem ha (h hb)
  · intro x hx
    exact ⟨x, hx, 1, S₁.one_mem, mul_one x⟩

theorem mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ normalizer (A : Set G))
    (hB : x ∈ normalizer (B : Set G)) : x ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro y
  simp only [mem_inf]
  rw [hA y, hB y]

theorem image_subtype_preimage {L : Subgroup G} {U : Set G} (hU : U ⊆ L) :
    (Subtype.val : L → G) '' ((Subtype.val : L → G) ⁻¹' U) = U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hU hx⟩, hx, rfl⟩

end Rel

@[expose] def BaFor (p : ℕ) (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow p G) (S : Subgroup G), S ≤ P → fusionStronglyClosed (S : Set G) P →
    ∀ U : Set G, U ⊆ P → ∀ g : G, rconj g U ⊆ P → BaRel S U (rconj g U)

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem baRel_of_quotient (P : Sylow p G) {S S₀ : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) (hS₀S : S₀ ≤ S) [S₀.Normal]
    (hQ : BaFor p (G ⧸ S₀)) {U : Set G} (hU : U ⊆ P) (h : G) (hUh : rconj h U ⊆ P) :
    BaRel S U (rconj h U) := by
  set π := QuotientGroup.mk' S₀
  have hS' := stronglyClosed_map S₀ P hSP hS
  have hSP' : S.map π ≤ (sylowMap S₀ P : Subgroup (G ⧸ S₀)) := by
    rw [coe_sylowMap]; exact map_mono hSP
  have hU' : π '' U ⊆ (sylowMap S₀ P : Subgroup (G ⧸ S₀)) := by
    rw [coe_sylowMap]; rintro _ ⟨u, hu, rfl⟩; exact ⟨u, hU hu, rfl⟩
  have hUh' : rconj (π h) (π '' U) ⊆ (sylowMap S₀ P : Subgroup (G ⧸ S₀)) := by
    rw [← image_rconj, coe_sylowMap]; rintro _ ⟨u, hu, rfl⟩; exact ⟨u, hUh hu, rfl⟩
  obtain ⟨nb, hnb, heq⟩ := hQ (sylowMap S₀ P) (S.map π) hSP' hS' (π '' U) hU' (π h) hUh'
  rw [normalizer_map S₀ P hSP hS] at hnb
  obtain ⟨n, hn, rfl⟩ := hnb
  refine ⟨n, hn, eq_of_image_eq S₀ ?_ ?_ ?_⟩
  · rw [rconj_mul_subgroup hn]; exact mul_normal_eq S₀ hS₀S _
  · exact mul_normal_eq S₀ hS₀S _
  · rw [image_rconj, Set.image_mul, Set.image_mul, image_rconj, ← Subgroup.coe_map]
    exact heq

theorem baRel_of_subgroup (P : Sylow p G) {S S₀ : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) (hfn : FullyNormalized p P S₀)
    (hL : BaFor p (normalizer (S₀ : Set G)))
    (hlarger : Respects (BaRel S) P (S ⊓ normalizer (S₀ : Set G))) {h : G}
    (hh : h ∈ normalizer (S₀ : Set G)) {U : Set G}
    (hU : U ⊆ ((P ⊓ normalizer (S₀ : Set G) : Subgroup G) : Set G)) (hUh : rconj h U ⊆ P) :
    BaRel S U (rconj h U) := by
  set L := normalizer (S₀ : Set G)
  set S₁ := S ⊓ L
  have hcard : Nat.card (((P : Subgroup G) ⊓ L).subgroupOf L) =
      p ^ (Nat.card L).factorization p :=
    (Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv).trans hfn
  set PL : Sylow p L := Sylow.ofCard _ hcard
  have hPL : ∀ x : L, x ∈ (PL : Subgroup L) ↔ (x : G) ∈ (P : Subgroup G) ⊓ L := fun x =>
    Iff.rfl
  set SL := S₁.subgroupOf L
  have hSLP : SL ≤ PL := fun x hx => (hPL x).2 ⟨hSP hx.1, x.2⟩
  have hSL : fusionStronglyClosed (SL : Set L) PL := by
    intro a ha l hl
    have hl' := ((hPL _).1 hl).1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hl'
    have h1 : (l : G)⁻¹ * a * l ∈ S := hS _ ha.1 _ hl'
    exact ⟨by simpa using h1, (l⁻¹ * a * l).2⟩
  set UL := (Subtype.val : L → G) ⁻¹' U
  have hUL : UL ⊆ PL := fun x hx => (hPL x).2 (hU hx)
  set hl : L := ⟨h, hh⟩
  have hULU : ∀ V : Set G, V ⊆ L → L.subtype '' ((Subtype.val : L → G) ⁻¹' V) = V :=
    fun V hV => image_subtype_preimage hV
  have hrc : rconj hl UL = (Subtype.val : L → G) ⁻¹' (rconj h U) := by
    ext x
    simp only [mem_rconj, Set.mem_preimage, UL, hl, Subgroup.coe_mul, Subgroup.coe_inv]
  have hULh : rconj hl UL ⊆ PL := by
    rw [hrc]; intro x hx; exact (hPL x).2 ⟨hUh hx, x.2⟩
  obtain ⟨m, hm, heq⟩ := hL PL SL hSLP hSL UL hUL hl hULh
  have hmG : (m : G) ∈ normalizer (S₁ : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf inf_le_right hm
  have hSLG : L.subtype '' (SL : Set L) = S₁ := by
    rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have heqG : rconj (m : G) ((S₁ : Set G) * U) = (S₁ : Set G) * rconj h U := by
    have := congrArg (fun X => L.subtype '' X) heq
    simp only [image_rconj, Set.image_mul, hSLG] at this
    rwa [hULU U fun x hx => (hU hx).2] at this
  have hU1 : (S₁ : Set G) * U ⊆ ((P ⊓ normalizer (S₁ : Set G) : Subgroup G) : Set G) := by
    rintro _ ⟨s, hs, u, hu, rfl⟩
    have hsN : s ∈ (P : Subgroup G) ⊓ normalizer (S₁ : Set G) :=
      ⟨hSP hs.1, Subgroup.le_normalizer hs⟩
    have huN : u ∈ (P : Subgroup G) ⊓ normalizer (S₁ : Set G) :=
      ⟨(hU hu).1, mem_normalizer_inf (sylow_le_normalizer P hSP hS (hU hu).1)
        (Subgroup.le_normalizer (hU hu).2)⟩
    exact Subgroup.mul_mem _ hsN huN
  have hU1h : rconj (m : G) ((S₁ : Set G) * U) ⊆ P := by
    rw [heqG]
    rintro _ ⟨s, hs, u, hu, rfl⟩
    exact P.mul_mem (hSP hs.1) (hUh hu)
  obtain ⟨n, hn, hn'⟩ := hlarger (m : G) hmG _ hU1 hU1h
  refine ⟨n, hn, ?_⟩
  rw [heqG, ← mul_assoc, ← mul_assoc, subgroup_mul_of_le inf_le_left] at hn'
  exact hn'

theorem baFor_of_lt (IH : ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G →
    BaFor p H) : BaFor p G := by
  intro P S hSP hS U hU g hg
  by_cases hS1 : S = ⊥
  · subst hS1
    have hn : g ∈ normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [normalizer_eq_top_iff.mpr inferInstance]; exact mem_top g
    exact ⟨g, hn, rconj_mul_subgroup hn U⟩
  refine descent P hSP hS hS1 (baRel_equivalence S) ?_ U hU g hg
  intro S₀ hS₀ hS₀1 hfn hlarger h hh V hV hVh
  by_cases hS₀S : S₀ = S
  · subst hS₀S
    exact ⟨h, hh, rconj_mul_subgroup hh V⟩
  have hlt : S₀ < S := lt_of_le_of_ne hS₀ hS₀S
  by_cases hN : normalizer (S₀ : Set G) = ⊤
  · have : S₀.Normal := normalizer_eq_top_iff.mp hN
    have hcard : Nat.card (G ⧸ S₀) < Nat.card G := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup S₀
      have h2 : 1 < Nat.card S₀ := (Subgroup.one_lt_card_iff_ne_bot S₀).mpr hS₀1
      have h3 : 0 < Nat.card (G ⧸ S₀) := Nat.card_pos
      rw [h1]
      nlinarith
    exact baRel_of_quotient P hSP hS hS₀ (IH _ hcard) (fun x hx => (hV hx).1) h hVh
  · have hcard : Nat.card (normalizer (S₀ : Set G)) < Nat.card G := by
      rw [← Subgroup.card_top (G := G)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hN)
    have hS₁ : Nat.card S₀ < Nat.card ↥(S ⊓ normalizer (S₀ : Set G)) :=
      Subgroup.card_lt_of_lt (lt_inf_normalizer (P.isPGroup'.to_le hSP) hlt)
    exact baRel_of_subgroup P hSP hS hfn (IH _ hcard) (hlarger _ inf_le_left hS₁) hh hV hVh

theorem baFor (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [Finite G] : BaFor p G := by
  suffices key : ∀ n, ∀ (H : Type u) [Group H] [Finite H], Nat.card H = n → BaFor p H from
    key _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ hn
  exact baFor_of_lt fun K _ _ hK => ih _ (hn ▸ hK) K rfl

theorem image_conj_eq_rconj {H : Type*} [Group H] (g : H) (U : Set H) :
    (fun x => g⁻¹ * x * g) '' U = rconj g U := by
  ext x
  rw [mem_rconj]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [mul_assoc] using hu
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by group⟩

theorem theoremB_a (P : Sylow p G) {S : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) {U₁ U₂ : Set G} (hU₁ : U₁ ⊆ P) (hU₂ : U₂ ⊆ P)
    {g : G} (hg : (fun x => g⁻¹ * x * g) '' U₁ = U₂) :
    ∃ n ∈ normalizer (S : Set G),
      (fun x => n⁻¹ * x * n) '' ((S : Set G) * U₁) = (S : Set G) * U₂ := by
  rw [image_conj_eq_rconj] at hg
  subst hg
  obtain ⟨n, hn, h⟩ := baFor p G P S hSP hS U₁ hU₁ g hU₂
  exact ⟨n, hn, by rw [image_conj_eq_rconj]; exact h⟩

end CFSG.Goldschmidt75
