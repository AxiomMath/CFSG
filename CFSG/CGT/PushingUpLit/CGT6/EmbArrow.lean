module

public import CFSG.CGT.PushingUpLit.CGT6.SixFiveArrow
public import CFSG.CGT.PushingUpLit.CGT6.Props

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped Pointwise Nat

theorem ArrowNat.le {G : Type} [Group G] {Y X : Subgroup G} (h : ArrowNat Y X) : Y ≤ X := by
  rcases h with rfl | ⟨-, -, -, -, -, -, -, -, h, -⟩
  · exact le_rfl
  · exact h

theorem ArrowNat.trans {G : Type} [Group G] [Finite G] {X Y Z : Subgroup G}
    (htop : X ≠ Y → Y ≠ Z →
      IsSimpleGroup (↥Y ⧸ pCore 2 ↥Y) ∧ ∃ a b : ↥Y ⧸ pCore 2 ↥Y, a * b ≠ b * a)
    (h1 : ArrowNat X Y) (h2 : ArrowNat Y Z) : ArrowNat X Z := by
  classical
  by_cases hXY : X = Y
  · rw [hXY]
    exact h2
  by_cases hYZ : Y = Z
  · rw [← hYZ]
    exact h1
  obtain ⟨hsimple, hnab⟩ := htop hXY hYZ
  rcases h1 with h1 | ⟨a, b, φY, F₁, ⟨ψX⟩, hnatY, hF₁, hU₁, hXY', himg₁⟩
  · exact absurd h1 hXY
  rcases h2 with h2 | ⟨a', c, φZ, F₂, ⟨ψY⟩, hnatZ, hF₂, hU₂, hYZ', himg₂⟩
  · exact absurd h2 hYZ
  have hm5 : 5 ≤ 2 * a + 1 := five_le_of_isSimple φY hsimple hnab
  have hmm' : 2 * a + 1 = 2 * c + 1 :=
    alt_card_inj hm5 ((Nat.card_congr φY.toEquiv).symm.trans (Nat.card_congr ψY.toEquiv))
  have hac : a = c := by omega
  subst hac
  have hm : 2 * a + 1 = 5 ∨ 7 ≤ 2 * a + 1 := by omega
  let ΦY : ↥Y →* alternatingGroup (Fin (2 * a + 1)) :=
    φY.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥Y))
  let ΦZ : ↥Z →* alternatingGroup (Fin (2 * a' + 1)) :=
    φZ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥Z))
  have hΦY : Function.Surjective ΦY := φY.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerY : ΦY.ker = pCore 2 ↥Y := by
    ext y
    simp only [MonoidHom.mem_ker, ΦY, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      EmbeddingLike.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hkerZ : ΦZ.ker = pCore 2 ↥Z := by
    ext y
    simp only [MonoidHom.mem_ker, ΦZ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      EmbeddingLike.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let f : ↥Y →* alternatingGroup (Fin (2 * a' + 1)) := ΦZ.comp (Subgroup.inclusion hYZ')
  have hkerf : f.ker ≤ pCore 2 ↥Y := ker_comp_inclusion_le_pCore hYZ' ΦZ hkerZ.le
  have himg₁' : (X.subgroupOf Y).map ΦY = altStabilizer (2 * a + 1) F₁ := by
    rw [← himg₁, Subgroup.map_map]
  have himg₂' : (Y.subgroupOf Z).map ΦZ = altStabilizer (2 * a' + 1) F₂ := by
    rw [← himg₂, Subgroup.map_map]
  have hrangef : f.range = altStabilizer (2 * a' + 1) F₂ := by
    rw [← himg₂', MonoidHom.range_comp, Subgroup.inclusion_range]
  have hmk : 2 * a + 1 ≤ 2 * a' + 1 := by
    by_contra hk
    have hk' : 2 * a' + 1 < 2 * a + 1 := not_le.mp hk
    have hF₂0 : F₂.card = 0 := by omega
    have hF₂e : F₂ = ∅ := Finset.card_eq_zero.mp hF₂0
    have htop : f.range = ⊤ := by
      rw [hrangef, hF₂e]
      ext σ
      simp [mem_altStabilizer']
    have hfs : Function.Surjective f := MonoidHom.range_eq_top.mp htop
    have h3 := card_quot_pCore_le f hfs hkerf
    rw [Nat.card_congr φY.toEquiv] at h3
    have h4 := alt_card_le hm5 h3
    omega
  have hnm : 2 * b + 1 ≤ 2 * a + 1 := by
    by_contra hn
    have hn' : 2 * a + 1 < 2 * b + 1 := not_le.mp hn
    have hF₁0 : F₁.card = 0 := by omega
    have hF₁e : F₁ = ∅ := Finset.card_eq_zero.mp hF₁0
    let g : ↥X →* alternatingGroup (Fin (2 * a + 1)) := ΦY.comp (Subgroup.inclusion hXY')
    have hrg : g.range = ⊤ := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range, himg₁', hF₁e]
      ext σ
      simp [mem_altStabilizer']
    have hgs : Function.Surjective g := MonoidHom.range_eq_top.mp hrg
    have hkerg : g.ker ≤ pCore 2 ↥X := ker_comp_inclusion_le_pCore hXY' ΦY hkerY.le
    have h3 := card_quot_pCore_le g hgs hkerg
    rw [Nat.card_congr ψX.toEquiv] at h3
    have h4 := alt_card_le (by omega : 5 ≤ 2 * b + 1) h3
    omega
  have hcompl : F₂ᶜ.card = 2 * a + 1 := by
    rw [Finset.card_compl, Fintype.card_fin, hF₂]
    omega
  have hkerfeq : f.ker = pCore 2 ↥Y := by
    refine le_antisymm hkerf ?_
    have hidxf : f.ker.index = Nat.card ↥(altStabilizer (2 * a' + 1) F₂) := by
      rw [Subgroup.index_ker, hrangef]
    have hidxY : (pCore 2 ↥Y).index = Nat.card ↥(alternatingGroup (Fin (2 * a + 1))) := by
      rw [← hkerY, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hΦY]
      exact Subgroup.card_top
    have hidx : f.ker.index = (pCore 2 ↥Y).index := by
      rw [hidxf, hidxY, natCard_altStabilizer hcompl]
    have hc1 := Subgroup.index_mul_card (H := f.ker)
    have hc2 := Subgroup.index_mul_card (H := pCore 2 ↥Y)
    have hpos : 0 < (pCore 2 ↥Y).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hidx] at hc1
    have hcard : Nat.card ↥(pCore 2 ↥Y) ≤ Nat.card ↥f.ker :=
      (Nat.mul_left_cancel hpos (hc2.trans hc1.symm)).le
    exact fun x hx => by
      have := Subgroup.eq_of_le_of_card_ge hkerf hcard
      rw [this]
      exact hx
  have hker_le : ΦY.ker ≤ f.ker := by rw [hkerY, hkerfeq]
  let θ₀ : alternatingGroup (Fin (2 * a + 1)) →* alternatingGroup (Fin (2 * a' + 1)) :=
    ΦY.liftOfSurjective hΦY ⟨f, hker_le⟩
  have hθ₀ : ∀ y, θ₀ (ΦY y) = f y := fun y =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨f, hker_le⟩ y
  have hθ₀inj : Function.Injective θ₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨y, rfl⟩ := hΦY x
    rw [hθ₀] at hx
    have hy : y ∈ f.ker := hx
    rw [hkerfeq, ← hkerY] at hy
    exact hy
  have hθ₀range : θ₀.range = altStabilizer (2 * a' + 1) F₂ := by
    rw [← hrangef]
    ext x
    constructor
    · rintro ⟨x', rfl⟩
      obtain ⟨y, rfl⟩ := hΦY x'
      exact ⟨y, (hθ₀ y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨ΦY y, hθ₀ y⟩
  obtain ⟨τ, hτinj, hτF, hτ⟩ := altStab_map_of_range_eq hm hcompl hθ₀inj hθ₀range
  have hdisj : Disjoint F₂ (F₁.image τ) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx'
    exact hτF i hx
  refine Or.inr ⟨a', b, φZ, F₂ ∪ F₁.image τ, ⟨ψX⟩, hnatZ, ?_, hU₁.trans hU₂,
    hXY'.trans hYZ', ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hτinj, hF₂, hF₁]
    omega
  · have hXZ : (X.subgroupOf Y).map (Subgroup.inclusion hYZ') = X.subgroupOf Z := by
      ext z
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hz
        exact ⟨⟨z.1, hXY' hz⟩, hz, rfl⟩
    have hfθ : f = θ₀.comp ΦY := MonoidHom.ext fun y => (hθ₀ y).symm
    rw [Subgroup.map_map, ← hXZ, Subgroup.map_map]
    have : (ΦZ.comp (Subgroup.inclusion hYZ')) = f := rfl
    show (X.subgroupOf Y).map (ΦZ.comp (Subgroup.inclusion hYZ')) = _
    rw [this, hfθ, ← Subgroup.map_map, himg₁', hτ]

theorem ArrowNat.trans_of_inClassX {G : Type} [Group G] [Finite G] {X Y Z : Subgroup G}
    (hX : InClassX ↥X) (hY : InClassX ↥Y) (h1 : ArrowNat X Y) (h2 : ArrowNat Y Z) :
    ArrowNat X Z :=
  ArrowNat.trans (fun hXY _ => arrow_top_simple hX hY h1.le hXY h1.arrow) h1 h2

end CFSG.CGT.PushingUpLit.CGT6
