module

public import CFSG.LargeExtraspecial.S8CorC
public import CFSG.LargeExtraspecial.S8CorBStatement

public section

namespace CFSG.LargeExtraspecial.S8

open Subgroup

universe u

section Transfer

variable {Y X : Type*} [Group Y] [Group X]

theorem image_conjCent (e : Y ≃* X) (t : Y) : e '' conjCent t = conjCent (e t) := by
  ext σ
  constructor
  · rintro ⟨τ, ⟨hc, hconj⟩, rfl⟩
    exact ⟨by rw [← map_mul, hc, map_mul], (e : Y →* X).map_isConj hconj⟩
  · rintro ⟨hc, hconj⟩
    refine ⟨e.symm σ, ⟨e.injective ?_, ?_⟩, e.apply_symm_apply σ⟩
    · rw [map_mul, map_mul, e.apply_symm_apply]
      exact hc
    · have := (e.symm : X →* Y).map_isConj hconj
      rwa [MonoidHom.coe_ofClass, e.symm_apply_apply] at this

theorem map_closure_conjCent (e : Y ≃* X) (t : Y) :
    (closure (conjCent t)).map (e : Y →* X) = closure (conjCent (e t)) := by
  rw [MonoidHom.map_closure]
  exact congrArg Subgroup.closure (image_conjCent e t)

theorem isSimpleGroup_quotient_center_map (e : Y ≃* X) (U : Subgroup Y)
    [IsSimpleGroup (↥U ⧸ center ↥U)] :
    IsSimpleGroup (↥(U.map (e : Y →* X)) ⧸ center ↥(U.map (e : Y →* X))) :=
  (QuotientGroup.congr (center U) (center ↥(U.map (e : Y →* X))) (e.subgroupMap U)
    (map_center_eq _)).symm.isSimpleGroup

theorem exists_derivedSeries_le_map (e : Y ≃* X) {U : Subgroup Y}
    (h : ∃ k, derivedSeries Y k ≤ U ⊔ centralizer (U : Set Y)) :
    ∃ k, derivedSeries X k ≤ U.map (e : Y →* X) ⊔ centralizer (U.map (e : Y →* X) : Set X) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [← map_derivedSeries_eq (f := (e : Y →* X)) e.surjective k]
  refine (map_mono hk).trans ?_
  rw [Subgroup.map_sup]
  refine sup_le_sup_left ?_ _
  intro z hz
  obtain ⟨c, hc, rfl⟩ := mem_map.mp hz
  rw [mem_centralizer_iff] at hc ⊢
  intro w hw
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hw
  rw [← map_mul, ← map_mul, hc x hx]

theorem sect_map [Finite Y] (e : Y ≃* X) {U : Subgroup Y}
    (hsect : ∀ t ∈ U, orderOf t = 2 → (∃ u ∈ U, u * t ≠ t * u) →
      ∀ R N : Subgroup Y, N ≤ R → R ≤ U ⊓ centralizer ({t} : Set Y) →
        ∀ (_ : (N.subgroupOf R).Normal), IsSimpleGroup (↥R ⧸ N.subgroupOf R) →
          ∃ P : Sylow 2 (↥R ⧸ N.subgroupOf R),
            ∀ x ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)),
              ∀ y ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)), x * y = y * x) :
    ∀ t ∈ U.map (e : Y →* X), orderOf t = 2 → (∃ u ∈ U.map (e : Y →* X), u * t ≠ t * u) →
      ∀ R N : Subgroup X, N ≤ R → R ≤ U.map (e : Y →* X) ⊓ centralizer ({t} : Set X) →
        ∀ (_ : (N.subgroupOf R).Normal), IsSimpleGroup (↥R ⧸ N.subgroupOf R) →
          ∃ P : Sylow 2 (↥R ⧸ N.subgroupOf R),
            ∀ x ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)),
              ∀ y ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)), x * y = y * x := by
  intro t ht hto hnc R N hNR hR hNn hs
  have hmemU : ∀ {x : X}, x ∈ U.map (e : Y →* X) → e.symm x ∈ U := fun hx =>
    (mem_map_equiv (f := e) (K := U)).mp hx
  set R' : Subgroup Y := R.map (e.symm : X →* Y) with hR'
  set N' : Subgroup Y := N.map (e.symm : X →* Y) with hN'
  set eR : R' ≃* R := (e.symm.subgroupMap R).symm with heR
  have he : (N'.subgroupOf R').map eR.toMonoidHom = N.subgroupOf R := by
    ext x
    rw [mem_map_equiv, mem_subgroupOf, mem_subgroupOf]
    change e.symm (x : X) ∈ N.map e.symm.toMonoidHom ↔ (x : X) ∈ N
    rw [mem_map_equiv, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  have hcomap : N'.subgroupOf R' = (N.subgroupOf R).comap eR.toMonoidHom := by
    rw [← he, comap_map_eq_self_of_injective eR.injective]
  have hN'n : (N'.subgroupOf R').Normal := by
    rw [hcomap]
    exact hNn.comap _
  set eQ : (↥R' ⧸ N'.subgroupOf R') ≃* (↥R ⧸ N.subgroupOf R) :=
    QuotientGroup.congr (N'.subgroupOf R') (N.subgroupOf R) eR he with heQ
  have hs' : IsSimpleGroup (↥R' ⧸ N'.subgroupOf R') := eQ.isSimpleGroup
  have hR'U : R' ≤ U ⊓ centralizer ({e.symm t} : Set Y) := by
    rintro _ ⟨r, hr, rfl⟩
    have hrU : r ∈ U.map (e : Y →* X) := (hR hr).1
    have hrc : r ∈ centralizer ({t} : Set X) := (hR hr).2
    refine ⟨hmemU hrU, ?_⟩
    rw [mem_centralizer_singleton_iff] at hrc
    show _ ∈ centralizer ({e.symm t} : Set Y)
    rw [mem_centralizer_singleton_iff]
    change e.symm r * e.symm t = e.symm t * e.symm r
    rw [← map_mul, ← map_mul, hrc]
  obtain ⟨u, hu, hut⟩ := hnc
  obtain ⟨P', hP'⟩ := hsect (e.symm t) (hmemU ht) (by rw [MulEquiv.orderOf_eq]; exact hto)
    ⟨e.symm u, hmemU hu, fun h => hut (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
    R' N' (map_mono hNR) hR'U hN'n hs'
  refine ⟨P'.mapSurjective (f := eQ.toMonoidHom) eQ.surjective, fun x hx y hy => ?_⟩
  have hx1 : x ∈ (P' : Subgroup (↥R' ⧸ N'.subgroupOf R')).map eQ.toMonoidHom := hx
  have hy1 : y ∈ (P' : Subgroup (↥R' ⧸ N'.subgroupOf R')).map eQ.toMonoidHom := hy
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx1
  obtain ⟨b, hb, rfl⟩ := mem_map.mp hy1
  rw [← map_mul, ← map_mul, hP' a ha b hb]

end Transfer

section Perfect

variable {Y : Type} [Group Y] [Finite Y]

theorem commutator_normalClosure_eq_of_isConj_mul {t : Y} (ht : orderOf t = 2)
    (h2 : ∀ τ : Y, τ * t = t * τ → IsConj t τ → τ ≠ t → IsConj t (t * τ))
    (hsimp : IsSimpleGroup
      (↥(normalClosure ({t} : Set Y)) ⧸ center ↥(normalClosure ({t} : Set Y)))) :
    ⁅normalClosure ({t} : Set Y), normalClosure ({t} : Set Y)⁆ =
      normalClosure ({t} : Set Y) := by
  set U := normalClosure ({t} : Set Y) with hU
  have hUn : U.Normal := normalClosure_normal
  have htU : t ∈ U := subset_normalClosure (Set.mem_singleton t)
  have htt : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hDn : (⁅U, U⁆).Normal := Subgroup.commutator_normal U U
  refine le_antisymm (commutator_le_left U U) ?_
  suffices htD : t ∈ ⁅U, U⁆ from normalClosure_le_normal (Set.singleton_subset_iff.mpr htD)
  by_contra htD
  set π := QuotientGroup.mk' (center ↥U) with hπ
  set t' : U := ⟨t, htU⟩ with ht'
  have hUnc : ¬ ∀ a b : U, a * b = b * a := by
    intro hc
    have htop : center ↥U = ⊤ := eq_top_iff.mpr fun a _ => mem_center_iff.mpr fun b => hc b a
    have : Subsingleton (↥U ⧸ center ↥U) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_subsingleton _) this
  have hLnc : center (↥U ⧸ center ↥U) ≠ ⊤ := by
    intro htop
    have : IsMulCommutative (↥U ⧸ center ↥U) :=
      ⟨⟨fun a b => mem_center_iff.mp (htop ▸ mem_top b) a⟩⟩
    have hp := (Group.is_simple_iff_prime_card (α := ↥U ⧸ center ↥U)).mp hsimp
    have : Fact (Nat.card (↥U ⧸ center ↥U)).Prime := ⟨hp⟩
    have : IsCyclic (↥U ⧸ center ↥U) := isCyclic_of_prime_card rfl
    exact hUnc fun a b => (π.isMulCommutative_of_isCyclic_of_ker_le_center (by
      rw [hπ, QuotientGroup.ker_mk'])).is_comm.comm a b
  have htZ : π t' ≠ 1 := by
    intro h1
    have hZ : t' ∈ center ↥U := by
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    apply hUnc
    have hC : U ≤ centralizer (U : Set Y) :=
      normalClosure_le_normal (Set.singleton_subset_iff.mpr (mem_centralizer_iff.mpr
        fun u hu => congrArg Subtype.val (mem_center_iff.mp hZ ⟨u, hu⟩)))
    exact fun a b => Subtype.ext (mem_centralizer_iff.mp (hC b.2) a a.2)
  obtain ⟨y, hyU, hyc, hyne⟩ : ∃ y ∈ U, (y * t * y⁻¹) * t = t * (y * t * y⁻¹) ∧
      y * t * y⁻¹ ≠ t := by
    by_contra hiso
    push Not at hiso
    have : Fintype U := Fintype.ofFinite _
    obtain ⟨K, hK, hKodd, hKt⟩ := CFSG.ZStar.glauberman_zStar U t'
      (fun h => ht1 (congrArg Subtype.val h)) (Subtype.ext htt)
      (fun g hg => Subtype.ext (hiso g g.2 (congrArg Subtype.val hg)))
    rcases (hK.map π (QuotientGroup.mk'_surjective _)).eq_bot_or_eq_top with hbot | htop
    ·
      have hcen : π t' ∈ center (↥U ⧸ center ↥U) := by
        refine mem_center_iff.mpr fun q => ?_
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center ↥U) q
        have h1 : π (g * t' * g⁻¹ * t'⁻¹) = 1 := by
          rw [← mem_bot, ← hbot]
          exact mem_map_of_mem π (hKt g)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
          mul_inv_eq_iff_eq_mul] at h1
        exact h1
      rcases (inferInstance : (center (↥U ⧸ center ↥U)).Normal).eq_bot_or_eq_top with h | h
      · rw [h] at hcen
        exact htZ (mem_bot.mp hcen)
      · exact hLnc h
    ·
      have hmem : π t' ∈ K.map π := by
        rw [htop]
        exact mem_top _
      obtain ⟨k, hk, hkt⟩ := hmem
      have hodd : Odd (orderOf (π t')) :=
        Odd.of_dvd_nat hKodd ((hkt ▸ orderOf_map_dvd π k).trans (K.orderOf_dvd_natCard hk))
      have htt' : t' * t' = 1 := Subtype.ext htt
      have h2t : orderOf (π t') ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_two, ← map_mul, htt', map_one])
      rcases (Nat.dvd_prime Nat.prime_two).mp h2t with h | h
      · exact htZ (orderOf_eq_one_iff.mp h)
      · rw [h] at hodd
        exact absurd hodd (by decide)
  have hmem : t * (y * t * y⁻¹) ∈ ⁅U, U⁆ := by
    have h := commutator_mem_commutator htU hyU
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right htt] at h
    rwa [show t * (y * t * y⁻¹) = t * y * t * y⁻¹ by group]
  obtain ⟨c, hc⟩ := isConj_iff.mp (h2 (y * t * y⁻¹) hyc (isConj_iff.mpr ⟨y, rfl⟩) hyne)
  apply htD
  have h := hDn.conj_mem _ hmem c⁻¹
  rwa [← hc, show c⁻¹ * (c * t * c⁻¹) * c⁻¹⁻¹ = t by group] at h

end Perfect

theorem corB_trichotomy (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    {X : Type u} [Group X] [Finite X] {t : X} (ht : orderOf t = 2)
    (h1p : IsPGroup 2 (closure (conjCent t)))
    (h1c : ⁅⁅closure (conjCent t), closure (conjCent t)⁆, closure (conjCent t)⁆ = ⊥)
    (h2 : ∀ τ : X, τ * t = t * τ → IsConj t τ → τ ≠ t → IsConj t (t * τ)) :
    (∃ K : Subgroup X, K.Normal ∧ Odd (Nat.card K) ∧ normalClosure {t} = K ⊔ zpowers t) ∨
    (∀ x ∈ normalClosure ({t} : Set X), ∀ y ∈ normalClosure ({t} : Set X),
      x * y = y * x ∧ x * x = 1) ∨
    (IsSimpleGroup (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X))) ∧
      (∃ k, derivedSeries X k ≤
        normalClosure ({t} : Set X) ⊔ centralizer (normalClosure ({t} : Set X) : Set X)) ∧
      ∀ t₁ ∈ normalClosure ({t} : Set X), orderOf t₁ = 2 →
        (∃ u ∈ normalClosure ({t} : Set X), u * t₁ ≠ t₁ * u) →
        ∀ R N : Subgroup X, N ≤ R → R ≤ normalClosure ({t} : Set X) ⊓ centralizer ({t₁} : Set X) →
          ∀ (_ : (N.subgroupOf R).Normal), IsSimpleGroup (↥R ⧸ N.subgroupOf R) →
            ∃ P : Sylow 2 (↥R ⧸ N.subgroupOf R),
              ∀ x ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)),
                ∀ y ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)), x * y = y * x) := by
  set e : Shrink.{0} X ≃* X := Shrink.mulEquiv with he
  set t' : Shrink.{0} X := e.symm t with ht'
  have het : e t' = t := e.apply_symm_apply t
  have hW : (closure (conjCent t')).map (e : Shrink.{0} X →* X) = closure (conjCent t) := by
    rw [map_closure_conjCent, het]
  have ho' : orderOf t' = 2 := by rw [ht', MulEquiv.orderOf_eq]; exact ht
  have h1p' : IsPGroup 2 (closure (conjCent t')) := by
    have := h1p.comap_of_injective (e : Shrink.{0} X →* X) e.injective
    rwa [← hW, comap_map_eq_self_of_injective e.injective] at this
  have h1c' : ⁅⁅closure (conjCent t'), closure (conjCent t')⁆, closure (conjCent t')⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective (f := (e : Shrink.{0} X →* X)) _ e.injective).mp
    rw [map_commutator, map_commutator, hW]
    exact h1c
  have h2' : ∀ τ, τ * t' = t' * τ → IsConj t' τ → τ ≠ t' → IsConj t' (t' * τ) := by
    intro τ hτ hc hne
    have h := h2 (e τ) (by rw [← het, ← map_mul, hτ, map_mul])
      (by rw [← het]; exact (e : Shrink.{0} X →* X).map_isConj hc)
      (fun h => hne (e.injective (h.trans het.symm)))
    have := (e.symm : X →* Shrink.{0} X).map_isConj h
    rwa [MonoidHom.coe_ofClass, map_mul, e.symm_apply_apply] at this
  have hU : (normalClosure ({t'} : Set (Shrink.{0} X))).map (e : Shrink.{0} X →* X) =
      normalClosure ({t} : Set X) := by
    rw [map_normalClosure _ _ e.surjective, Set.image_singleton, MonoidHom.coe_ofClass, het]
  rcases hCorB (Shrink.{0} X) t' ho' h1p' h1c' h2' with ⟨K', hK'U, hK'n, hK'odd, hUK'⟩ | hab |
    hlist
  ·
    left
    have ht't' : t' * t' = 1 := by rw [← pow_two, ← ho']; exact pow_orderOf_eq_one t'
    have ht'1 : t' ≠ 1 := fun h => by
      rw [h, orderOf_one] at ho'
      exact absurd ho' (by norm_num)
    have hK'N := normal_of_sup_zpowers normalClosure_normal hK'U hK'n hK'odd ht't' ht'1 hUK'
    refine ⟨K'.map (e : Shrink.{0} X →* X), hK'N.map _ e.surjective, ?_, ?_⟩
    · rw [card_map_of_injective e.injective]
      exact hK'odd
    · rw [← hU, hUK', Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.coe_ofClass, het]
  ·
    right; left
    rw [← hU]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨hxy, hxx⟩ := hab x hx y hy
    exact ⟨by rw [← map_mul, ← map_mul, hxy], by rw [← map_mul, hxx, map_one]⟩
  ·
    right; right
    obtain ⟨hsimp, hder, hsect⟩ := hFacts (Shrink.{0} X) _ normalClosure_normal hlist
    have hk := hder (commutator_normalClosure_eq_of_isConj_mul ho' h2' hsimp)
    rw [← hU]
    exact ⟨isSimpleGroup_quotient_center_map e _, exists_derivedSeries_le_map e hk,
      sect_map e hsect⟩

end CFSG.LargeExtraspecial.S8
