module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockTransferBar

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Subgroup Pointwise CFSG.Open CFSG.QuasithinUnique
open CFSG.AGLEmbedding (Asc81bHyp barM)

variable {G : Type} [Group G]

theorem conj_mem_barM_of_normalizes {X S L : Subgroup G} (hSX : S ≤ X)
    (hSL : S ≤ normalizer (L : Set G)) {s l : ↥X ⧸ CFSG.pCore 2 ↥X} (hs : s ∈ barM X S)
    (hl : l ∈ barM X L) : s * l * s⁻¹ ∈ barM X L := by
  obtain ⟨x, hxX, hxS, rfl⟩ := mem_barM_iff.1 hs
  obtain ⟨y, hyX, hyL, rfl⟩ := mem_barM_iff.1 hl
  refine mem_barM_iff.2 ⟨x * y * x⁻¹, X.mul_mem (X.mul_mem hxX hyX) (X.inv_mem hxX),
    (mem_normalizer_iff.1 (hSL hxS) y).1 hyL, ?_⟩
  rfl

theorem blockTransfer_iso [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hSL : S ≤ normalizer (L : Set G)) (T : Subgroup ↥(barM X L))
    (hnorm : ∀ s ∈ barM X S, ∀ l l' : ↥(barM X L),
      (l' : ↥X ⧸ CFSG.pCore 2 ↥X) = s * l * s⁻¹ → l ∈ T → l' ∈ T)
    (hsolv : Group.IsSolvable ↥T)
    (hodd : ¬ 2 ∣ (((barM X (S ⊓ L)).subgroupOf (barM X L)).subgroupOf T).index)
    (hT3 : ∀ R : Subgroup ↥(barM X L), R ≤ T → (∀ b ∈ T, ∀ r ∈ R, b * r * b⁻¹ ∈ R) →
      (∀ r ∈ R, ∃ m : ℕ, r ^ (3 ^ m) = 1) → R = ⊥)
    (hLB : SolvableSylowNormalizer X S) :
    ∀ t ∈ T, (t : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ barM X (normalizer (S : Set G) ⊓ L) := by
  have hSX : S ≤ X := hA.twoRadical.1
  set Bb : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) := T.map (barM X L).subtype with hBb
  have hBL : Bb ≤ barM X L := by
    rintro _ ⟨t, -, rfl⟩; exact t.2
  have hmemBb : ∀ x, x ∈ Bb ↔ ∃ t ∈ T, (t : ↥X ⧸ CFSG.pCore 2 ↥X) = x := by
    intro x; simp [hBb]
  have hBn : ∀ s ∈ barM X S, ∀ b ∈ Bb, s * b * s⁻¹ ∈ Bb := by
    intro s hs b hb
    obtain ⟨t, ht, rfl⟩ := (hmemBb b).1 hb
    have hm := conj_mem_barM_of_normalizes hSX hSL hs t.2
    exact (hmemBb _).2 ⟨⟨_, hm⟩, hnorm s hs t ⟨_, hm⟩ rfl ht, rfl⟩
  let e : ↥T ≃* ↥Bb := Subgroup.equivMapOfInjective T (barM X L).subtype (Subgroup.subtype_injective _)
  have hsolv' : Group.IsSolvable ↥Bb :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hodd' : ¬ 2 ∣ ((barM X (S ⊓ L)).subgroupOf Bb).index := by
    have hc : (((barM X (S ⊓ L)).subgroupOf Bb).comap e.toMonoidHom) =
        ((barM X (S ⊓ L)).subgroupOf (barM X L)).subgroupOf T := by
      ext t
      have h1 : ((e t : ↥Bb) : ↥X ⧸ CFSG.pCore 2 ↥X) = ((t : ↥(barM X L)) : ↥X ⧸ CFSG.pCore 2 ↥X) :=
        rfl
      simp only [mem_comap, mem_subgroupOf, MulEquiv.coe_toMonoidHom, h1]
    rw [← index_comap_of_surjective ((barM X (S ⊓ L)).subgroupOf Bb) (f := e.toMonoidHom)
      (by exact e.surjective), hc]
    exact hodd
  have hT3' : ∀ R : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X), R ≤ Bb →
      (∀ b ∈ Bb, ∀ r ∈ R, b * r * b⁻¹ ∈ R) → (∀ r ∈ R, ∃ m : ℕ, r ^ (3 ^ m) = 1) → R = ⊥ := by
    intro R hRB hRn hR3
    have hR' : R.comap (barM X L).subtype = ⊥ := by
      refine hT3 _ ?_ ?_ ?_
      · intro l hl
        obtain ⟨t, ht, htl⟩ := (hmemBb _).1 (hRB hl)
        have : t = l := Subtype.ext htl
        rwa [← this]
      · intro b hb r hr
        have := hRn b ((hmemBb _).2 ⟨b, hb, rfl⟩) r hr
        exact this
      · intro r hr
        obtain ⟨m, hm⟩ := hR3 r hr
        exact ⟨m, Subtype.ext (by simpa using hm)⟩
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (hmemBb x).1 (hRB hx)
    have : t ∈ R.comap (barM X L).subtype := hx
    rw [hR'] at this
    have ht1 : t = 1 := (mem_bot.1 this)
    rw [ht1]; simp
  have hres := blockTransfer_bar hA hSL hBL hBn hsolv' hodd' hT3' hLB
  intro t ht
  exact hres ((hmemBb _).2 ⟨t, ht, rfl⟩)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
