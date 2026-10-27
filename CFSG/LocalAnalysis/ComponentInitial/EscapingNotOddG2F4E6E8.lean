module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlockOrdinaryRootObstruction
public import CFSG.LieType.AlgebraicGroups.RationalInnerDiagonal
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem map_inf_centralizer_singleton_of_injective {G H : Type*} [Group G] [Group H]
    {f : G →* H} (hf : Function.Injective f) (A : Subgroup G) (x : G) :
    (A ⊓ centralizer ({x} : Set G)).map f = A.map f ⊓ centralizer ({f x} : Set H) := by
  rw [Subgroup.map_inf_eq _ _ _ hf, map_centralizer_singleton_of_injective hf, ← inf_assoc,
    inf_eq_left.2 (map_le_range f A)]

theorem commuting_block_G2_F4_E6_E8_ringChar_dvd_card {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) (τ : Tag)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (k : Type) [Field k] [Finite k]
    (hk : ringChar k ≠ 2) (e : L ⧸ center L ≃* adjointGroup τ k) :
    ringChar k ∣ Nat.card J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨-, -, -, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₂, hK₂, hne⟩ := hΔ.exists_ne J
  have hK₂L : K₂ ≤ L := (le_blockGroup hK₂).trans hML
  have hK₂even : Even (Nat.card K₂) := by
    obtain ⟨g, hg⟩ := hK₂.1
    rw [hg, card_conjSub]
    exact heven
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := K₂) 2 (even_iff_two_dvd.1 hK₂even)
  have ht : orderOf (⟨(t₀ : G), hK₂L t₀.2⟩ : L) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, ht₀]
  obtain ⟨hu2, hcomp⟩ := hloc J mem_block_self K₂ hK₂ (Ne.symm hne) ⟨t₀, hK₂L t₀.2⟩ t₀.2 ht
  set u := QuotientGroup.mk' (center L) (⟨(t₀ : G), hK₂L t₀.2⟩ : L) with hu
  have h1 : CFSG.Assembly.IsComponentOf ((centerQuotientImage L J).map e.toMonoidHom)
      (centralizer ({e u} : Set (adjointGroup τ k))) := by
    have := (isComponentOf_map_iff (f := e.toMonoidHom) e.injective).2 hcomp
    rwa [map_centralizer_singleton_of_injective (f := e.toMonoidHom) e.injective,
      MonoidHom.range_eq_top.2 e.surjective, top_inf_eq] at this
  set x : ModGL τ k := ((e u : adjointGroup τ k) : ModGL τ k) with hx
  have h2 : CFSG.Assembly.IsComponentOf
      (((centerQuotientImage L J).map e.toMonoidHom).map (adjointGroup τ k).subtype)
      (adjointGroup τ k ⊓ centralizer ({x} : Set (ModGL τ k))) := by
    have := (isComponentOf_map_iff (adjointGroup τ k).subtype_injective).2 h1
    rwa [map_subtype_centralizer_singleton] at this
  set ι := baseChangeGL (τ := τ) (algebraMap k (AlgebraicClosure k)) with hι
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  have h3 : CFSG.Assembly.IsComponentOf
      ((((centerQuotientImage L J).map e.toMonoidHom).map (adjointGroup τ k).subtype).map ι)
      ((adjointGroup τ k).map ι ⊓ centralizer ({ι x} : Set (ModGL τ (AlgebraicClosure k)))) := by
    have := (isComponentOf_map_iff hιinj).2 h2
    rwa [map_inf_centralizer_singleton_of_injective hιinj] at this
  set r := ringChar k with hr_def
  have : CharP k r := ringChar.charP k
  obtain ⟨n, hr, hcard⟩ := FiniteField.card k r
  have : Fact r.Prime := ⟨hr⟩
  have : CharP (AlgebraicClosure k) r :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective r
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure k) r n c = c ^ Nat.card k := fun c => by
    rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hkodd : Odd (Nat.card k) := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact (hr.odd_of_ne_two hk).pow
  have hx₀ := (exceptional_Lang_Frobenius_fixed_derived_root_group τ k hkodd (AlgebraicClosure k)
    _ hFr).2.1 ⟨x, (e u).2, rfl⟩
  have hx2 : x ^ 2 = 1 := by
    have hu' : u ^ 2 = 1 := by rw [← hu2, pow_orderOf_eq_one]
    have he' : (e u) ^ 2 = 1 := by rw [← map_pow, hu', map_one]
    rw [hx, ← Subgroup.coe_pow, he', Subgroup.coe_one]
  have hx₀2 : (ι x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
  obtain ⟨h, -, a, ha, -, -, hCh, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components τ k (AlgebraicClosure k) hτ
      hkodd _ hFr hx₀ hx₀2
  have h4 : CFSG.Assembly.IsComponentOf
      (((((centerQuotientImage L J).map e.toMonoidHom).map (adjointGroup τ k).subtype).map ι).map
        (MulAut.conj h).toMonoidHom)
      ((adjointGroup τ k).map ι ⊓ centralizer {rootDiagUnit τ a}) := by
    have := (isComponentOf_map_iff (f := (MulAut.conj h).toMonoidHom)
      (MulAut.conj h).injective).2 h3
    rwa [hCh] at this
  set b : Fin τ.rank → kˣ := fun i => if a i = 1 then 1 else -1 with hb_def
  have hb : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
    by_cases h1 : a i = 1 <;> simp [hb_def, h1]
  have hab : (fun i => Units.map (algebraMap k (AlgebraicClosure k)).toMonoidHom (b i)) = a := by
    funext i
    by_cases h1 : a i = 1
    · simp [hb_def, h1]
    · have h2 : a i = -1 := (ha i).resolve_left h1
      rw [h2]
      simp only [hb_def, h1, ↓reduceIte]
      exact Units.ext (by simp)
  have hXK : (toralCentralizer τ k b).map ι =
      (adjointGroup τ k).map ι ⊓ centralizer {rootDiagUnit τ a} := by
    have := map_baseChangeGL_toralCentralizer (algebraMap k (AlgebraicClosure k)) b
    rwa [hab] at this
  set B₅ := ((((centerQuotientImage L J).map e.toMonoidHom).map (adjointGroup τ k).subtype).map
    ι).map (MulAut.conj h).toMonoidHom with hB₅
  have hB₅ι : B₅ ≤ ι.range := h4.1.trans (hXK ▸ map_le_range ι _)
  have h5 : CFSG.Assembly.IsComponentOf (B₅.comap ι) (toralCentralizer τ k b) := by
    rw [← isComponentOf_map_iff hιinj, map_comap_eq_self hB₅ι, hXK]
    exact h4
  obtain ⟨-, -, -, -, hdvd⟩ := odd_toral_ordinary_component_root_factor_and_prime_divisor r hr hk k
    τ b hb (maskChar (signTupleBits b)) (rootCharKernel_eq_kernelRoots hk hb).symm _ h5
  have hcard5 : Nat.card (B₅.comap ι) = Nat.card (centerQuotientImage L J) := by
    rw [← card_map_of_injective hιinj, map_comap_eq_self hB₅ι, hB₅,
      card_map_of_injective (MulAut.conj h).injective, card_map_of_injective hιinj,
      card_map_of_injective (adjointGroup τ k).subtype_injective,
      card_map_of_injective (f := e.toMonoidHom) e.injective]
  rw [hcard5] at hdvd
  have hJL : Nat.card (J.subgroupOf L) = Nat.card J :=
    Nat.card_congr (subgroupOfEquivOfLe ((le_blockGroup mem_block_self).trans hML)).toEquiv
  exact hdvd.trans (hJL ▸ card_map_dvd _ _)

theorem commuting_block_odd_G2_F4_E6_E8_overgroup_exclusion {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ∀ (τ : Tag) (k : Type) [Field k] [Finite k], (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) →
      ringChar k ≠ 2 → ¬ Nonempty (L ⧸ center L ≃* adjointGroup τ k) := by
  intro τ k _ _ hτ hk ⟨e⟩
  have : CharP k (ringChar k) := ringChar.charP k
  have hr : (ringChar k).Prime := CharP.char_is_prime k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hr⟩
  exact commuting_block_ordinary_root_quotient_prime_divisor_obstruction hq heven hV hJ hΔ hL
    hML hLH (ringChar k) (hr.odd_of_ne_two hk) k τ ⟨e⟩
    (commuting_block_G2_F4_E6_E8_ringChar_dvd_card hq heven hJ hΔ hL hML hLH τ hτ k hk e)

end CFSG.LocalAnalysis.ComponentInitial
