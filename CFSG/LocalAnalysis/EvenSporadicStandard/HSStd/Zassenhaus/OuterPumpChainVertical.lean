module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainAut

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.HSStd

variable {G : Type} [Group G]

@[expose] def conjAutL (L : Subgroup G) (s : G) (hs2 : s * s = 1)
    (hL : ∀ x ∈ L, s * x * s⁻¹ ∈ L) : MulAut ↥L where
  toFun x := ⟨s * x * s⁻¹, hL x x.2⟩
  invFun x := ⟨s * x * s⁻¹, hL x x.2⟩
  left_inv x := Subtype.ext (by
    show s * (s * (x : G) * s⁻¹) * s⁻¹ = x
    have h : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hs2, inv_one]
    calc s * (s * (x : G) * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
      _ = x := by rw [hs2, h]; group)
  right_inv x := Subtype.ext (by
    show s * (s * (x : G) * s⁻¹) * s⁻¹ = x
    have h : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hs2, inv_one]
    calc s * (s * (x : G) * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
      _ = x := by rw [hs2, h]; group)
  map_mul' x y := Subtype.ext (by
    show s * ((x : G) * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹)
    group)

theorem conjAutL_sq (L : Subgroup G) {s : G} (hs2 : s * s = 1) (hL : ∀ x ∈ L, s * x * s⁻¹ ∈ L)
    (x : ↥L) : conjAutL L s hs2 hL (conjAutL L s hs2 hL x) = x :=
  (conjAutL L s hs2 hL).left_inv x

theorem vertical_table [Finite G] (ctx : PumpCtx G) (hTab : KGPumpTable) {K L : Subgroup G}
    {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hK : IsCompIn K (centralizer ({s} : Set G))) (hL : IsCompIn L (centralizer ({t} : Set G)))
    (hLs : L.map (MulAut.conj s).toMonoidHom = L) (hKL : K ≤ L)
    (hpump : PumpType (↥K ⧸ center ↥K)) :
    K = L ∨ (PumpType (↥L ⧸ center ↥L) ∧
      ¬ Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 8)) ∧
      (IsSporadic (↥L ⧸ center ↥L) .HS →
        Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8)))) := by
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
  by_cases hKL' : K = L
  · exact Or.inl hKL'
  refine Or.inr ?_
  have hτ : quotAut σ ≠ 1 := by
    intro h1
    apply hKL'
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
  obtain ⟨hP, hA8, hHS⟩ := hTab (↥L ⧸ center ↥L) hcat hsimple (quotAut σ) (quotAut_sq hσ) hτ φ.range
    (range_le_autCentralizer_quotAut σ ι hfix) hNq (isSubnormal_range_quotAut σ ι hfix hsub)
    (isPGroup_center_range hKq φ hker (ctx.isPGroup_center hs hK)) (PumpType.congr e hpump)
  exact ⟨hP, hA8, fun h => by
    obtain ⟨f⟩ := hHS h
    exact ⟨e.trans f⟩⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
