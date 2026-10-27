module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinCase

open Subgroup CFSG.LocalAnalysis.EvenBN.LinearThree

theorem linrq_of_map {H G : Type*} [Group H] [Group G] {φ : H →* G} (hφ : Function.Injective φ)
    {V V₁ V₂ : Subgroup H} {q : ℕ} (hR : Radicals (V.map φ) (V₁.map φ) (V₂.map φ) q) :
    Radicals V V₁ V₂ q := by
  have hcardmap : ∀ W : Subgroup H, Nat.card (W.map φ) = Nat.card W := fun W =>
    Subgroup.card_map_of_injective hφ
  have hle : ∀ {X Y : Subgroup H}, X.map φ ≤ Y.map φ → X ≤ Y := fun h =>
    (Subgroup.map_le_map_iff_of_injective hφ).1 h
  have hnorm : ∀ {W : Subgroup H}, W ≤ V → ((W.map φ).subgroupOf (V.map φ)).Normal →
      (W.subgroupOf V).Normal := fun {W} hWV hW =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWV).2 fun v hv =>
      (mem_normalizer_map_iff hφ v W).1
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono (f := φ) hWV)).1 hW
          (Subgroup.mem_map_of_mem φ hv))
  exact
    { le₁ := hle hR.le₁
      le₂ := hle hR.le₂
      normal₁ := hnorm (hle hR.le₁) hR.normal₁
      normal₂ := hnorm (hle hR.le₂) hR.normal₂
      elem₁ := by
        have h := isElemAbelian_comap hφ hR.elem₁
        rwa [Subgroup.comap_map_eq_self_of_injective hφ] at h
      elem₂ := by
        have h := isElemAbelian_comap hφ hR.elem₂
        rwa [Subgroup.comap_map_eq_self_of_injective hφ] at h
      card₁ := (hcardmap V₁).symm.trans hR.card₁
      card₂ := (hcardmap V₂).symm.trans hR.card₂
      card := (hcardmap V).symm.trans hR.card
      inf_eq := by
        apply Subgroup.map_injective hφ
        rw [map_inf_centralizer hφ V, ← hR.inf_eq, Subgroup.map_inf V₁ V₂ φ hφ]
      sup_eq := by
        apply Subgroup.map_injective hφ
        rw [Subgroup.map_sup, hR.sup_eq]
      card_center := by
        rw [← hcardmap, map_inf_centralizer hφ V]
        exact hR.card_center
      le_of_elem := by
        intro E hE hEl
        rcases hR.le_of_elem (E.map φ) (Subgroup.map_mono hE) (isElemAbelian_map φ hEl) with h | h
        · exact Or.inl (hle h)
        · exact Or.inr (hle h)
      eq_of_card := by
        intro E hE hEl hc
        rcases hR.eq_of_card (E.map φ) (Subgroup.map_mono hE) (isElemAbelian_map φ hEl)
          ((hcardmap E).trans hc) with h | h
        · exact Or.inl (Subgroup.map_injective hφ h)
        · exact Or.inr (Subgroup.map_injective hφ h)
      le_of_sq := by
        intro x hx hx2
        have hφx : φ x ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
        rcases hR.le_of_sq (φ x) (Subgroup.mem_map_of_mem φ hx) hφx with h | h
        · exact Or.inl ((Subgroup.mem_map_iff_mem hφ).1 h)
        · exact Or.inr ((Subgroup.mem_map_iff_mem hφ).1 h) }

theorem radicals_quotient {G : Type*} [Group G] {S E R : Subgroup G} (hES : E ≤ S) (hRS : R ≤ S)
    [hEn : (E.subgroupOf S).Normal] (hsup : E ⊔ R = S) (hinf : E ⊓ R = ⊥) {R₁ R₂ : Subgroup G}
    {q : ℕ} (hR : CFSG.LocalAnalysis.EvenBN.LinearThree.Radicals R R₁ R₂ q) :
    CFSG.LocalAnalysis.EvenBN.LinearThree.Radicals (⊤ : Subgroup (↥S ⧸ E.subgroupOf S))
      ((R₁.subgroupOf S).map (QuotientGroup.mk' (E.subgroupOf S)))
      ((R₂.subgroupOf S).map (QuotientGroup.mk' (E.subgroupOf S))) q := by
  have hSN : S ≤ normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hES).1 hEn
  have hRN : R ≤ normalizer (E : Set G) := fun r hr => hSN (hRS hr)
  have hdecomp : ∀ s ∈ S, ∃ r ∈ R, ∃ e ∈ E, r * e = s := by
    intro s hs
    have hs' : s ∈ ((R ⊔ E : Subgroup G) : Set G) := by
      rw [sup_comm, hsup]
      exact hs
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R E hRN] at hs'
    obtain ⟨r, hr, e, he, hre⟩ := Set.mem_mul.1 hs'
    exact ⟨r, hr, e, he, hre⟩
  set π : ↥S →* ↥S ⧸ E.subgroupOf S := QuotientGroup.mk' (E.subgroupOf S) with hπ
  set ι : ↥R →* ↥S ⧸ E.subgroupOf S := π.comp (Subgroup.inclusion hRS) with hι
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (Subgroup.inclusion hRS x : ↥S) ∈ E.subgroupOf S :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hRS x)).1 hx
    have hxE : (x : G) ∈ E ⊓ R := ⟨Subgroup.mem_subgroupOf.1 hx', x.2⟩
    rw [hinf, Subgroup.mem_bot] at hxE
    exact Subtype.ext hxE
  have hsurj : Function.Surjective ι := by
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf S) y
    obtain ⟨r, hr, e, he, hre⟩ := hdecomp s.1 s.2
    refine ⟨⟨r, hr⟩, ?_⟩
    show QuotientGroup.mk' (E.subgroupOf S) (Subgroup.inclusion hRS ⟨r, hr⟩) =
      QuotientGroup.mk' (E.subgroupOf S) s
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    show (r : G)⁻¹ * (s : G) ∈ E
    rw [← hre, inv_mul_cancel_left]
    exact he
  have hmapinc : ∀ W : Subgroup G, W ≤ R →
      (W.subgroupOf R).map (Subgroup.inclusion hRS) = W.subgroupOf S := by
    intro W hW
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_subgroupOf]
      exact hx
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      exact ⟨⟨y, hW hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  have e_top : (⊤ : Subgroup ↥R).map ι = ⊤ := Subgroup.map_top_of_surjective ι hsurj
  have e₁ : (R₁.subgroupOf R).map ι =
      (R₁.subgroupOf S).map (QuotientGroup.mk' (E.subgroupOf S)) := by
    rw [← hmapinc R₁ hR.le₁, Subgroup.map_map]
  have e₂ : (R₂.subgroupOf R).map ι =
      (R₂.subgroupOf S).map (QuotientGroup.mk' (E.subgroupOf S)) := by
    rw [← hmapinc R₂ hR.le₂, Subgroup.map_map]
  have hR_sub : Radicals ((⊤ : Subgroup ↥R).map R.subtype) ((R₁.subgroupOf R).map R.subtype)
      ((R₂.subgroupOf R).map R.subtype) q := by
    have h1 : (⊤ : Subgroup ↥R).map R.subtype = R := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h2 : (R₁.subgroupOf R).map R.subtype = R₁ := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hR.le₁]
    have h3 : (R₂.subgroupOf R).map R.subtype = R₂ := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hR.le₂]
    rw [h1, h2, h3]
    exact hR
  have hR_top := linrq_of_map R.subtype_injective hR_sub
  have hfin := Radicals.map hinj hR_top
  rw [e_top, e₁, e₂] at hfin
  exact hfin

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
