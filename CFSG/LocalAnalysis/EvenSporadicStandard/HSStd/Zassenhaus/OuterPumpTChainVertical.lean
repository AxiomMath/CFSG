module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTType
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainVertical

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.HSStd

@[expose] def VertT (Q Q' : Type) [Group Q] [Group Q'] : Prop :=
  (Nonempty (Q ≃* alternatingGroup (Fin 8)) →
      (∃ m : ℕ, 5 ≤ m ∧ Nonempty (Q' ≃* alternatingGroup (Fin (2 * m)))) ∨ IsSporadic Q' .HS ∨
        LieModel Q' .PSL 4 2 2 ∨ IsSporadic Q' .McL) ∧
    (∀ j : ℕ, 5 ≤ j → Nonempty (Q ≃* alternatingGroup (Fin (2 * j))) →
      (∃ m : ℕ, j < m ∧ Nonempty (Q' ≃* alternatingGroup (Fin (2 * m)))) ∨
        (j = 5 ∧ IsSporadic Q' .HN)) ∧
    (IsSporadic Q .HS → IsSporadic Q' .HN) ∧ ¬ IsSporadic Q .McL ∧ ¬ IsSporadic Q .HN ∧
    (∀ i : ℕ, 1 ≤ i → LieModel Q .PSL 4 2 (2 ^ i) → LieModel Q' .PSL 4 2 (2 ^ (i + 1)))

theorem VertT.left_congr {Q Q₀ Q' : Type} [Group Q] [Group Q₀] [Group Q'] (e : Q ≃* Q₀)
    (h : VertT Q₀ Q') : VertT Q Q' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun ⟨f⟩ => h1 ⟨e.symm.trans f⟩, fun j hj ⟨f⟩ => h2 j hj ⟨e.symm.trans f⟩,
    fun ⟨f⟩ => h3 ⟨e.symm.trans f⟩, fun ⟨f⟩ => h4 ⟨e.symm.trans f⟩, fun ⟨f⟩ => h5 ⟨e.symm.trans f⟩,
    fun i hi hL => h6 i hi (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hL)⟩

variable {G : Type} [Group G]

theorem vertical_tableT [Finite G] (ctx : PumpCtx G) (hT : KGPumpTableT) {K L : Subgroup G}
    {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hK : IsCompIn K (centralizer ({s} : Set G))) (hL : IsCompIn L (centralizer ({t} : Set G)))
    (hLs : L.map (MulAut.conj s).toMonoidHom = L) (hKL : K ≤ L) (hne : K ≠ L) :
    VertT (↥K ⧸ center ↥K) (↥L ⧸ center ↥L) := by
  have hs2 : s * s = 1 := mul_self_eq_one_of_orderOf_eq_two hs
  have hLcl : ∀ x ∈ L, s * x * s⁻¹ ∈ L := fun x hx => by
    rw [← hLs]
    exact ⟨x, hx, rfl⟩
  set σ := conjAutL L s hs2 hLcl with hσdef
  have hσ : ∀ x, σ (σ x) = x := conjAutL_sq L hs2 hLcl
  set ι : ↥K →* ↥L := Subgroup.inclusion hKL with hι
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective hKL
  have hKq := hK.isQuasisimple
  have hLq := hL.isQuasisimple
  have hmemι : ∀ x : ↥L, x ∈ ι.range ↔ (x : G) ∈ K := by
    intro x
    constructor
    · rintro ⟨k, rfl⟩
      exact k.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hfix : ι.range ≤ autCentralizer σ := by
    intro x hx
    have hxK : (x : G) ∈ K := (hmemι x).1 hx
    have hc : (x : G) ∈ centralizer ({s} : Set G) := hK.le hxK
    have hc' := mem_centralizer_singleton_iff.1 hc
    show σ x = x
    apply Subtype.ext
    show s * (x : G) * s⁻¹ = x
    rw [← hc']
    group
  have hsub : (ι.range.subgroupOf (autCentralizer σ)).IsSubnormal := by
    let f : ↥(autCentralizer σ) →* ↥(centralizer ({s} : Set G)) :=
      MonoidHom.codRestrict (L.subtype.comp (autCentralizer σ).subtype) _ (fun x => by
        have hxK : ((x : ↥L) : G) ∈ L := x.1.2
        have hfx : σ (x : ↥L) = x := x.2
        have := congrArg Subtype.val hfx
        refine mem_centralizer_singleton_iff.2 ?_
        have h2 : s * ((x : ↥L) : G) * s⁻¹ = ((x : ↥L) : G) := this
        calc ((x : ↥L) : G) * s = (s * ((x : ↥L) : G) * s⁻¹) * s := by rw [h2]
          _ = s * ((x : ↥L) : G) := by group)
    have h1 := hK.2.2.comap f
    convert h1 using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact hmemι _
  have hτ : quotAut σ ≠ 1 := by
    intro h1
    apply hne
    have htop := range_eq_top_of_quotAut_eq_one hLq hKq σ ι hιinj hsub h1
    refine le_antisymm hKL fun x hx => ?_
    have : (⟨x, hx⟩ : ↥L) ∈ ι.range := htop ▸ mem_top _
    exact (hmemι _).1 this
  set φ : ↥K →* ↥L ⧸ center ↥L := (QuotientGroup.mk' (center ↥L)).comp ι with hφ
  have hker : φ.ker ≤ center ↥K := by
    intro k hk
    have hk' : ι k ∈ center ↥L := by
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hk
      exact hk
    rw [mem_center_iff]
    intro k'
    apply hιinj
    rw [map_mul, map_mul]
    exact mem_center_iff.1 hk' (ι k')
  have hNq := isQuasisimple_range_of_ker_le_center hKq φ hker
  obtain ⟨e⟩ := nonempty_quotient_center_equiv_range hKq φ hker
  have hcat : Catalog (↥L ⧸ center ↥L) := ctx.catalog_center_quotient ht hL
  have hsimple : IsSimpleGroup (↥L ⧸ center ↥L) := hLq.2.1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hT (↥L ⧸ center ↥L) hcat hsimple (quotAut σ) (quotAut_sq hσ)
    hτ φ.range (range_le_autCentralizer_quotAut σ ι hfix) hNq
    (isSubnormal_range_quotAut σ ι hfix hsub)
    (isPGroup_center_range hKq φ hker (ctx.isPGroup_center hs hK))
  refine VertT.left_congr e ⟨fun h => ?_, h2, fun h => (h3 h).1, h4, h5, h6⟩
  rcases h1 h with h | h | h | ⟨h, -⟩
  exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]

theorem ltF_stepT [Finite G] (ctx : PumpCtx G) (hT : KGPumpTableT) {K L : Subgroup G}
    (h : LtF K L) :
    Nonempty (↥K ⧸ center ↥K ≃* ↥L ⧸ center ↥L) ∨
      (K ≠ L ∧ VertT (↥K ⧸ center ↥K) (↥L ⧸ center ↥L)) := by
  obtain ⟨s, t, hs, ht, hst, hK, hL, hKL⟩ := h
  by_cases hLe : L.map (MulAut.conj s).toMonoidHom = L
  · by_cases hKL' : K = L
    · subst hKL'
      exact Or.inl ⟨MulEquiv.refl _⟩
    · exact Or.inr ⟨hKL', vertical_tableT ctx hT hs ht hK hL hLe (le_of_conj_eq hLe hKL) hKL'⟩
  · obtain ⟨e⟩ := nonempty_quotient_center_equiv_of_ltF_ne hs hst hK hL hKL hLe
    exact Or.inl ⟨e.symm⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
