module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR8
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.LocalAnalysis.SeitzReduction.Inheritance
import CFSG.Quasithin.SteinbergCFIndexThreeComponentTools

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def NeighbourOvergroupSLm {Y : Type} [Group Y] (s : Y) (D : Subgroup Y) (m f : ℕ) :
    Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          SLmOvergroup Kc (Kc.normalizerMonoidHom ⟨s, hsN⟩) m f) ∨
      (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧ Nonempty (Kc ≃* D)))

theorem lieModel_quotient_center_congr {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : LieModel (A ⧸ center A) t n p f) : LieModel (B ⧸ center B) t n p f :=
  LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr (center A) (center B) e (map_center_eq e)) h

theorem lieModel_quotient_center_map_oddCore {G : Type} [Group G] {H D : Subgroup G}
    (hDH : D ≤ H) (hDq : CFSG.IsQuasisimple D) {m f : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f)
    (hne : (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≠ ⊥) :
    LieModel (((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) ⧸
      center ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)))) .PSL m 2 f := by
  have hD₁ : CFSG.IsQuasisimple (D.subgroupOf H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDH).symm hDq
  have hnt : ∃ k, (QuotientGroup.mk' (oddCore H)).subgroupMap (D.subgroupOf H) k ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    rw [eq_bot_iff]
    rintro _ ⟨d, hd, rfl⟩
    exact (mem_bot).mpr (congrArg Subtype.val (h ⟨d, hd⟩))
  obtain ⟨e₂⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hD₁
    ((QuotientGroup.mk' (oddCore H)).subgroupMap (D.subgroupOf H))
    ((QuotientGroup.mk' (oddCore H)).subgroupMap_surjective _)
    (LieType.CurtisTits.ker_le_center_of_isQuasisimple hD₁ hnt)
  exact LieType.CurtisTits.lieModel_of_mulEquiv e₂
    (lieModel_quotient_center_congr (subgroupOfEquivOfLe hDH).symm hDm)

theorem isComponent_fixedSubgroup_of_le_of_quotient {Y : Type} [Group Y] {s : Y}
    {Kc D : Subgroup Y} (hsN : s ∈ normalizer (Kc : Set Y)) (hDK : D ≤ Kc)
    (hDs : D ≤ centralizer ({s} : Set Y))
    (hDcomp : IsComponent (D.subgroupOf (Kc ⊓ centralizer ({s} : Set Y)))) {m f : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) :
    IsComponent
        ((D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) ∧
      LieModel
        (((D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) ⧸
          center ((D.subgroupOf Kc).subgroupOf
            (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)))) .PSL m 2 f ∧
      ((D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))).map
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)).subtype = D.subgroupOf Kc := by
  have hDfix : D.subgroupOf Kc ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
    rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  exact ⟨F4Pilot.isComponent_subgroupOf_subgroupOf
      (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp,
    lieModel_quotient_center_congr (F4Pilot.subgroupOfSubgroupOfEquiv hDK hDfix).symm hDm,
    by rw [subgroupOf_map_subtype, inf_eq_left.mpr hDfix]⟩

section Swap

variable {Y : Type*} [Group Y]

private theorem eq_one_or_eq_of_mem_zpowers [Finite Y] {s y : Y} (hs : orderOf s = 2)
    (hy : y ∈ zpowers s) : y = 1 ∨ y = s := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hy)
  rw [← pow_mod_orderOf, hs]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h]
  · exact Or.inl (pow_zero s)
  · exact Or.inr (pow_one s)

theorem mem_normalizer_sup_map_conj {s : Y} (hs2 : s ^ 2 = 1) (H : Subgroup Y) :
    s ∈ normalizer ((H ⊔ H.map (MulAut.conj s).toMonoidHom : Subgroup Y) : Set Y) := by
  refine mem_normalizer_iff_map_conj_eq.2 ?_
  change (H ⊔ H.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s).toMonoidHom = _
  rw [Subgroup.map_sup, CentralizerComponents.map_conj_map_conj hs2, sup_comm]

theorem center_eq_bot_and_nonempty_mulEquiv_of_swap [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {s : Y} (hs : orderOf s = 2) {Kc D : Subgroup Y} (hKc : IsComponent Kc)
    (hne : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥)
    (hdiag : (D : Set Y) = {g | ∃ k ∈ Kc, k * (s * k * s⁻¹) = g})
    (hDs : D ≤ centralizer ({s} : Set Y))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2) :
    center Kc = ⊥ ∧ Nonempty (Kc ≃* D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hKK' : ∀ k ∈ Kc, ∀ k' ∈ Kc.map (MulAut.conj s).toMonoidHom, k * k' = k' * k :=
    fun k hk k' hk' =>
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm hk) k' hk').symm
  have hconj : ∀ k ∈ Kc, s * k * s⁻¹ ∈ Kc.map (MulAut.conj s).toMonoidHom :=
    fun k hk => ⟨k, hk, by simp⟩
  have hsK : s ∉ Kc := fun h => hne (mem_normalizer_iff_map_conj_eq.1 (le_normalizer h))
  set Zc : Subgroup Y := (center Kc).map Kc.subtype
  have hZcK : Zc ≤ Kc := map_subtype_le _
  have hZcp : IsPGroup 2 Zc :=
    (CFSG.Quasithin.SteinbergCF.isPGroup_center_of_isComponent hO hKc).map _
  have hZcD : Zc ≤ centralizer (D : Set Y) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro d hd
    have hd' : d ∈ {g | ∃ k ∈ Kc, k * (s * k * s⁻¹) = g} := hdiag ▸ hd
    obtain ⟨k, hk, rfl⟩ := hd'
    have h1 : k * (z : Y) = (z : Y) * k := congrArg Subtype.val (mem_center_iff.mp hz ⟨k, hk⟩)
    have h2 : (s * k * s⁻¹) * (z : Y) = (z : Y) * (s * k * s⁻¹) :=
      (hKK' z z.2 _ (hconj k hk)).symm
    change k * (s * k * s⁻¹) * (z : Y) = (z : Y) * (k * (s * k * s⁻¹))
    calc k * (s * k * s⁻¹) * (z : Y) = k * ((s * k * s⁻¹) * (z : Y)) := mul_assoc _ _ _
      _ = k * ((z : Y) * (s * k * s⁻¹)) := by rw [h2]
      _ = (k * (z : Y)) * (s * k * s⁻¹) := (mul_assoc _ _ _).symm
      _ = ((z : Y) * k) * (s * k * s⁻¹) := by rw [h1]
      _ = (z : Y) * (k * (s * k * s⁻¹)) := mul_assoc _ _ _
  have hZc'D : Zc.map (MulAut.conj s).toMonoidHom ≤ centralizer (D : Set Y) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_iff]
    intro d hd
    have hwd : d * w = w * d := mem_centralizer_iff.mp (hZcD hw) d hd
    have hds : d * s = s * d := mem_centralizer_singleton_iff.mp (hDs hd)
    have hd' : s * d * s⁻¹ = d := by rw [← hds, mul_inv_cancel_right]
    change d * (s * w * s⁻¹) = (s * w * s⁻¹) * d
    calc d * (s * w * s⁻¹) = (s * d * s⁻¹) * (s * w * s⁻¹) := by rw [hd']
      _ = s * (d * w) * s⁻¹ := by group
      _ = s * (w * d) * s⁻¹ := by rw [hwd]
      _ = (s * w * s⁻¹) * (s * d * s⁻¹) := by group
      _ = (s * w * s⁻¹) * d := by rw [hd']
  have hsD : s ∈ centralizer (D : Set Y) :=
    mem_centralizer_iff.mpr fun d hd => mem_centralizer_singleton_iff.mp (hDs hd)
  have hZZ'p : IsPGroup 2 (Zc ⊔ Zc.map (MulAut.conj s).toMonoidHom : Subgroup Y) :=
    hZcp.to_sup_of_normal_right' (hZcp.map _)
      ((hZcK.trans ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (centralizer_le (map_mono hZcK)))).trans (centralizer_le_normalizer _))
  have hzp : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  have hUp : IsPGroup 2 ((Zc ⊔ Zc.map (MulAut.conj s).toMonoidHom) ⊔ zpowers s : Subgroup Y) :=
    hZZ'p.to_sup_of_normal_left' hzp
      ((zpowers_le (G := Y)).mpr (mem_normalizer_sup_map_conj hs2 Zc))
  have hUD : (Zc ⊔ Zc.map (MulAut.conj s).toMonoidHom) ⊔ zpowers s ≤
      centralizer (D : Set Y) :=
    sup_le (sup_le hZcD hZc'D) ((zpowers_le (G := Y)).mpr hsD)
  have hUeq : zpowers s = (Zc ⊔ Zc.map (MulAut.conj s).toMonoidHom) ⊔ zpowers s :=
    eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, hs]; exact hsyl _ hUp hUD)
  have hZ : center Kc = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzs : (z : Y) ∈ zpowers s := hUeq ▸ mem_sup_left (mem_sup_left ⟨z, hz, rfl⟩)
    rcases eq_one_or_eq_of_mem_zpowers hs hzs with h | h
    · exact (mem_bot).mpr (Subtype.ext h)
    · exact absurd (h ▸ z.2) hsK
  refine ⟨hZ, ?_⟩
  let ψ : Kc →* Y :=
    { toFun := fun k => (k : Y) * (s * k * s⁻¹)
      map_one' := by simp
      map_mul' := fun x y => by
        have hxy : (y : Y) * (s * x * s⁻¹) = (s * x * s⁻¹) * y := hKK' y y.2 _ (hconj x x.2)
        change ((x * y : Kc) : Y) * (s * ((x * y : Kc) : Y) * s⁻¹) =
          (x : Y) * (s * x * s⁻¹) * ((y : Y) * (s * y * s⁻¹))
        rw [Subgroup.coe_mul]
        calc (x : Y) * y * (s * (x * y) * s⁻¹) = x * (y * (s * x * s⁻¹)) * (s * y * s⁻¹) := by
              group
          _ = x * ((s * x * s⁻¹) * y) * (s * y * s⁻¹) := by rw [hxy]
          _ = x * (s * x * s⁻¹) * (y * (s * y * s⁻¹)) := by group }
  have hrange : ψ.range = D := by
    apply SetLike.coe_injective
    rw [hdiag, MonoidHom.coe_range]
    ext g
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk1 : (k : Y) * (s * k * s⁻¹) = 1 := hk
    have hk' : (k : Y) ∈ Kc.map (MulAut.conj s).toMonoidHom := by
      rw [eq_inv_of_mul_eq_one_left hk1]
      exact inv_mem (hconj k k.2)
    have hkZ : k ∈ center Kc := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hKK' g g.2 k hk')
    rw [hZ] at hkZ
    exact (mem_bot).mp hkZ
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

end Swap

theorem neighbour_overgroup_slm_center_of_pPrimeCore_eq_bot {m f : ℕ} (hm : 3 ≤ m)
    (hmf : 5 ≤ m ∨ 2 ≤ f) (hcat : SLmCatalogueClausesAt m) {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) : NeighbourOvergroupSLm s D m f := by
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
  have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
  obtain ⟨-, Kc, hKc, -, hDKK, -, -, hfix, hswap⟩ :=
    exists_isComponent_orbit_of_isComponent_centralizer hO hs2 hDs hDc
  refine ⟨Kc, hKc, hDKK, ?_⟩
  by_cases hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc
  · left
    obtain ⟨hDK, hDcomp⟩ := hfix hKt
    have hDne : D ≠ Kc := by
      rintro rfl
      exact hnn (F4Pilot.normal_of_isComponent_of_standard hKc hstd)
    have hsN : s ∈ normalizer (Kc : Set Y) := mem_normalizer_iff_map_conj_eq.2 hKt
    have hKs : ¬ Kc ≤ centralizer ({s} : Set Y) := by
      intro hKs
      rw [inf_eq_left.mpr hKs] at hDcomp
      exact hDne (F4Pilot.eq_of_isComponent_subgroupOf hKc.1 hDK hDcomp)
    have hτ2 := F4Pilot.orderOf_normalizerMonoidHom_eq_two Kc hsN hs2 hKs
    obtain ⟨hD'c, hD'm, hD'map⟩ :=
      isComponent_fixedSubgroup_of_le_of_quotient hsN hDK hDs hDcomp hDm
    have hcatK := hsec Kc hKc
    have hsK : s ∉ Kc := fun hsK =>
      E6Pilot.not_slmSmall hmf (slm_inner_small_of_clauses hcat hKc.1 hcatK _ hτ2 hm _
        hD'c hD'm (F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsK)
        (E6Pilot.fixedCentralizerTwoSmall_of_card_le_two _ hDK hsyl _ hD'map))
    exact ⟨hKt, lt_of_le_of_ne hDK hDne, hsK, hsN, slm_overgroup_catalogue hcat
      hKc.1 hcatK _ hτ2 hm _ hD'c hD'm
      (F4Pilot.fixedCentralizerTwoFree_of_card_le_two hsN hs hsK hDs hDK hsyl _ hD'map)⟩
  · right
    obtain ⟨hcomm, -, hdiag, -⟩ := hswap hKt
    exact ⟨hKt, hcomm,
      center_eq_bot_and_nonempty_mulEquiv_of_swap hO hs hKc hKt hcomm hdiag hDs hsyl⟩

theorem neighbour_overgroup_slm_center {m f : ℕ} (hm : 3 ≤ m) (hmf : 5 ≤ m ∨ 2 ≤ f)
    (hcat : SLmCatalogueClausesAt m) {G : Type} [Group G] [Finite G]
    (hKP : CFSG.Assembly.KProper Catalog G) {X : Subgroup G}
    (hXG : centralizer (X : Set G) ≠ ⊤) {t : G} (htX : t ∈ centralizer (X : Set G))
    (ht : orderOf t = 2) {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G))
    (hDq : CFSG.IsQuasisimple D) (hDm : LieModel (D ⧸ center D) .PSL m 2 f)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f := by
  have hsec : ∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc → Catalog (Kc ⧸ center Kc) :=
    fun Kc hKc => F4Pilot.catalog_center_quotient_of_kProper hKP hXG hKc.1
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  exact neighbour_overgroup_slm_center_of_pPrimeCore_eq_bot hm hmf hcat
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hsec (orderOf_mk_oddCore ht') hcomp hsyl
    hstd hnn
    (lieModel_quotient_center_map_oddCore hDX hDq hDm (ne_bot_of_isQuasisimple hcomp.2.2))

theorem NeighbourOvergroupSLm.exact {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {s : Y} {D : Subgroup Y} {m f : ℕ} (hmf : 5 ≤ m ∨ 2 ≤ f)
    (h : NeighbourOvergroupSLm s D m f) :
    ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
      ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
          (∃ hsN : s ∈ normalizer (Kc : Set Y),
            Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL m 2 (2 * f)) ∨
        (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧
            Nonempty (Kc ≃* D))) := by
  obtain ⟨Kc, hKc, hDKK, ⟨hKt, hDK, hsK, hsN, hov⟩ | hswap⟩ := h
  · obtain ⟨hZ, hmodel⟩ := E6Pilot.lieModel_of_slmOvergroup_of_pPrimeCore_eq_bot hO hKc hov hmf
    exact ⟨Kc, hKc, hDKK, .inl ⟨hKt, hDK, hsK, ⟨hsN, hov.1⟩, hZ, hmodel⟩⟩
  · exact ⟨Kc, hKc, hDKK, .inr hswap⟩

end CFSG.SeitzReduction.LinearPilot
