module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalPerfectLifts
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.Dihedral.DisconnectedInvolutionGraph.NormalSylowIntersection

public noncomputable section
namespace CFSG.Wreathed.PrimewisePerfectLift
open scoped Classical Pointwise commutatorElement
universe u v

theorem perfectResidual_eq_native {G : Type u} [Group G] :
    CFSG.perfectResidual G = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual G := rfl

theorem perfectResidual_isPerfect {G : Type u} [Group G] [Finite G] :
    Group.IsPerfect (CFSG.perfectResidual G) := by
  rw [perfectResidual_eq_native]
  exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect

theorem perfectResidual_characteristic {G : Type u} [Group G] :
    (CFSG.perfectResidual G).Characteristic := by
  rw [perfectResidual_eq_native]
  exact CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic

theorem perfectResidual_surjects {G : Type u} {H : Type v}
    [Group G] [Finite G] [Group H] [Group.IsPerfect H]
    (f : G →* H) (hf : Function.Surjective f) :
    (CFSG.perfectResidual G).map f = ⊤ := by
  rw [perfectResidual_eq_native]
  exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image f hf

theorem eq_top_of_one_Sylow_per_prime {G : Type u} [Group G] [Finite G]
    (D : Subgroup G)
    (hD : ∀ p : ℕ, p.Prime → p ∣ Nat.card G →
      ∃ P : Sylow p G, (P : Subgroup G) ≤ D) : D = ⊤ := by
  apply Subgroup.index_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hd
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := hD p hp (hd.trans D.index_dvd_card)
  exact P.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hP))

theorem kernel_conjugation_centralizer_image {G : Type u} {H : Type v}
    [Group G] [Group H] (f : G →* H) {r : G} (hr : f r = 1)
    (A : Subgroup G) (M : Subgroup H) :
    ((Subgroup.centralizer ((A.map (MulAut.conj r).toMonoidHom) : Set G)) ⊓
      M.comap f).map f = (Subgroup.centralizer (A : Set G) ⊓ M.comap f).map f := by
  have hcent : (Subgroup.centralizer (A : Set G)).map (MulAut.conj r).toMonoidHom =
      Subgroup.centralizer ((A.map (MulAut.conj r).toMonoidHom) : Set G) := by
    apply le_antisymm
    · exact Subgroup.map_centralizer_le_centralizer_image _ _
    · intro g hg
      refine Subgroup.mem_map.mpr ⟨(MulAut.conj r).symm g, ?_,
        (MulAut.conj r).apply_symm_apply g⟩
      intro a ha
      apply (MulAut.conj r).injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using
        hg ((MulAut.conj r) a) (Subgroup.mem_map_of_mem _ ha)
  have hV : (M.comap f).map (MulAut.conj r).toMonoidHom = M.comap f := by
    ext g
    rw [Subgroup.mem_map_equiv]
    change f ((MulAut.conj r).symm g) ∈ M ↔ f g ∈ M
    simp only [MulAut.conj_symm_apply, map_mul, map_inv, hr, inv_one, one_mul, mul_one]
  calc
    _ = ((Subgroup.centralizer (A : Set G) ⊓ M.comap f).map
        (MulAut.conj r).toMonoidHom).map f := by
      rw [Subgroup.map_inf _ _ (MulAut.conj r).toMonoidHom (MulAut.conj r).injective,
        hcent, hV]
    _ = _ := by
      rw [Subgroup.map_map]
      congr 1
      ext a
      simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        MulAut.conj_apply, map_mul, map_inv, hr, one_mul, inv_one, mul_one]

theorem coverage_for_every_prime_Sylow {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) [R.Normal] {ell : ℕ} (hell : ell.Prime)
    (M : Subgroup (G ⧸ R))
    (hcov : ∃ P : Sylow ell R,
      (Subgroup.centralizer (((P : Subgroup R).map R.subtype) : Set G) ⊓
        M.comap (QuotientGroup.mk' R)).map (QuotientGroup.mk' R) = M)
    (Q : Sylow ell R) :
    (Subgroup.centralizer (((Q : Subgroup R).map R.subtype) : Set G) ⊓
      M.comap (QuotientGroup.mk' R)).map (QuotientGroup.mk' R) = M := by
  let : Fact ell.Prime := ⟨hell⟩
  obtain ⟨P, hP⟩ := hcov
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R P Q
  have hconj : ((r • P : Sylow ell R) : Subgroup R) =
      (P : Subgroup R).map (MulAut.conj r).toMonoidHom := rfl
  have hmap : (Q : Subgroup R).map R.subtype =
      ((P : Subgroup R).map R.subtype).map (MulAut.conj (r : G)).toMonoidHom := by
    rw [← hr, hconj, Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmap, kernel_conjugation_centralizer_image (QuotientGroup.mk' R)
    ((QuotientGroup.eq_one_iff (r : G)).mpr r.property)]
  exact hP

theorem two_subgroup_le_kernel_of_odd_image {G : Type u} {H : Type v}
    [Group G] [Group H] (T : Subgroup G) (hT : IsPGroup 2 T)
    (f : G →* H) (hodd : Odd (Nat.card (T.map f))) : T ≤ f.ker := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : T.map f = ⊥ := by
    apply (Subgroup.eq_bot_iff_card _).mpr
    exact (hT.map f).card_eq_or_dvd.resolve_right hodd.not_two_dvd_nat
  exact (Subgroup.map_eq_bot_iff _).mp hbot


theorem actual_Sylow_intersection_centralizes_invariant_prime_Sylow
    {G : Type u} [Group G] (R : Subgroup G) [R.Normal]
    (hR : Odd (Nat.card R)) (S : Sylow 2 G) {ell : ℕ}
    (P : Sylow ell R)
    (hSP : (S : Subgroup G) ≤ Subgroup.normalizer
      (((P : Subgroup R).map R.subtype) : Set G))
    (M : Subgroup (G ⧸ R))
    (hcov : (Subgroup.centralizer (((P : Subgroup R).map R.subtype) : Set G) ⊓
      M.comap (QuotientGroup.mk' R)).map (QuotientGroup.mk' R) = M) :
    (S : Subgroup G) ⊓ M.comap (QuotientGroup.mk' R) ≤
      Subgroup.centralizer (((P : Subgroup R).map R.subtype) : Set G) := by
  let A := (P : Subgroup R).map R.subtype
  let B := Subgroup.normalizer (A : Set G)
  let C := Subgroup.centralizer (A : Set G)
  let D := C.subgroupOf B
  let T := ((S : Subgroup G) ⊓ M.comap (QuotientGroup.mk' R)).subgroupOf B
  let Rb := R.subgroupOf B
  let : D.Normal := inferInstance
  let f := QuotientGroup.mk' D
  have hTodd : IsPGroup 2 T := S.isPGroup'.to_inf_left.comap_subtype
  have hRbodd : Odd (Nat.card Rb) := by
    have hcard : Nat.card Rb = Nat.card (R ⊓ B : Subgroup G) := by
      rw [← Subgroup.card_map_of_injective B.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
    rw [hcard]
    exact hR.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have himage : T.map f ≤ Rb.map f := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hz
    have htM : QuotientGroup.mk' R (t : G) ∈ M := ht.2
    rw [← hcov] at htM
    obtain ⟨c, hc, hct⟩ := Subgroup.mem_map.mp htM
    have hcB : c ∈ B := Subgroup.centralizer_le_normalizer (A : Set G) hc.1
    let cb : B := ⟨c, hcB⟩
    have hdc : cb ∈ D := hc.1
    let rb : B := cb⁻¹ * t
    have hrb : rb ∈ Rb := by
      change c⁻¹ * (t : G) ∈ R
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' R) (c⁻¹ * (t : G)) = 1
      rw [map_mul, map_inv, hct, inv_mul_cancel]
    refine Subgroup.mem_map.mpr ⟨rb, hrb, ?_⟩
    have hcone : f cb = 1 := (QuotientGroup.eq_one_iff cb).mpr hdc
    simp only [rb, map_mul, map_inv, hcone, inv_one, one_mul]
  have himageodd : Odd (Nat.card (T.map f)) :=
    (hRbodd.of_dvd_nat (Rb.card_map_dvd f)).of_dvd_nat (Subgroup.card_dvd_of_le himage)
  have hTker : T ≤ f.ker := two_subgroup_le_kernel_of_odd_image T hTodd f himageodd
  intro t ht
  have htB : t ∈ B := hSP ht.1
  have htT : (⟨t, htB⟩ : B) ∈ T := ht
  have := hTker htT
  rw [QuotientGroup.ker_mk'] at this
  exact this


theorem primewise_coverage_Sylow_intersection_centralizes_kernel
    {G : Type u} [Group G] [Finite G] (R : Subgroup G) [R.Normal]
    (hR : Odd (Nat.card R)) (S : Sylow 2 G) (M : Subgroup (G ⧸ R))
    (hcov : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card R →
      ∃ P : Sylow ell R,
        (Subgroup.centralizer (((P : Subgroup R).map R.subtype) : Set G) ⊓
          M.comap (QuotientGroup.mk' R)).map (QuotientGroup.mk' R) = M) :
    (S : Subgroup G) ⊓ M.comap (QuotientGroup.mk' R) ≤
      Subgroup.centralizer (R : Set G) := by
  let T := (S : Subgroup G) ⊓ M.comap (QuotientGroup.mk' R)
  let D := (Subgroup.centralizer (T : Set G)).subgroupOf R
  have hD : D = ⊤ := by
    apply eq_top_of_one_Sylow_per_prime
    intro ell hell hdiv
    obtain ⟨P, hSP⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow
      2 ell Nat.prime_two hell (S : Subgroup G) R S.isPGroup'
      Subgroup.le_normalizer_of_normal hR.coprime_two_left
    refine ⟨P, ?_⟩
    have hTP := actual_Sylow_intersection_centralizes_invariant_prime_Sylow
      R hR S P hSP M (coverage_for_every_prime_Sylow R hell M (hcov ell hell hdiv) P)
    have hPT : (P : Subgroup R).map R.subtype ≤ Subgroup.centralizer (T : Set G) :=
      Subgroup.le_centralizer_iff.mp hTP
    intro p hp
    exact hPT (Subgroup.mem_map_of_mem R.subtype hp)
  intro t ht r hr
  have hrD : (⟨r, hr⟩ : R) ∈ D := hD ▸ Subgroup.mem_top _
  exact (hrD t ht).symm

theorem normal_Sylow_overgroup_eq_top_of_even_simple_central_quotient
    {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]
    [IsSimpleGroup (G ⧸ Subgroup.center G)]
    (heven : Even (Nat.card (G ⧸ Subgroup.center G)))
    (D : Subgroup G) [D.Normal] (S : Sylow 2 G) (hSD : (S : Subgroup G) ≤ D) :
    D = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := QuotientGroup.mk' (Subgroup.center G)
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center G))
  let image := D.map f
  let : image.Normal := (inferInstance : D.Normal).map f (QuotientGroup.mk'_surjective _)
  have hP : (P : Subgroup (G ⧸ Subgroup.center G)) ≤ image := Subgroup.map_mono hSD
  have himage : image = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal image with h | h
    · exact False.elim ((P.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven))
        (eq_bot_iff.mpr (hP.trans_eq h)))
    · exact h
  have hjoin : D ⊔ Subgroup.center G = ⊤ := by
    have := congrArg (Subgroup.comap f) himage
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at this
    exact this
  have hderived : ⁅D, D⁆ = ⊤ := by
    rw [← CFSG.RankThreeCoreUniqueness.Helpers.commutator_central_join_eq D
      (Subgroup.center G) le_rfl, hjoin]
    exact Group.IsPerfect.commutator_eq_top
  apply top_le_iff.mp
  rw [← hderived]
  exact D.commutator_le_self


theorem primewise_coverage_kernel_centralizer_image
    {G : Type u} [Group G] [Finite G] (R : Subgroup G) [R.Normal]
    (hR : Odd (Nat.card R)) (M : Subgroup (G ⧸ R)) [M.Normal] [Group.IsPerfect M]
    [IsSimpleGroup (M ⧸ Subgroup.center M)]
    (heven : Even (Nat.card (M ⧸ Subgroup.center M)))
    (hcov : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card R →
      ∃ P : Sylow ell R,
        (Subgroup.centralizer (((P : Subgroup R).map R.subtype) : Set G) ⊓
          M.comap (QuotientGroup.mk' R)).map (QuotientGroup.mk' R) = M) :
    (M.comap (QuotientGroup.mk' R) ⊓ Subgroup.centralizer (R : Set G)).map
      (QuotientGroup.mk' R) = M := by
  let pi := QuotientGroup.mk' R
  let Y := M.comap pi
  let H0 := Y ⊓ Subgroup.centralizer (R : Set G)
  let restriction : Y →* M := (pi.domRestrict Y).codRestrict M fun y => y.property
  have hsurj : Function.Surjective restriction := by
    intro m
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective R m.val
    have hy : g ∈ Y := by change pi g ∈ M; rw [hg]; exact m.property
    exact ⟨⟨g, hy⟩, Subtype.ext hg⟩
  let S : Sylow 2 G := Sylow.nonempty.some
  obtain ⟨T, hT⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection
    2 Y S
  let P := T.mapSurjective hsurj
  let D := (H0.map pi).subgroupOf M
  let : D.Normal := inferInstance
  have hTD : (P : Subgroup M) ≤ D := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hp
    have htS : (t : G) ∈ (S : Subgroup G) := by
      rw [hT] at ht
      exact ht
    have hcentral := primewise_coverage_Sylow_intersection_centralizes_kernel
      R hR S M hcov (show (t : G) ∈ (S : Subgroup G) ⊓ Y from ⟨htS, t.property⟩)
    exact Subgroup.mem_map.mpr ⟨(t : G), ⟨t.property, hcentral⟩, rfl⟩
  have hD : D = ⊤ := normal_Sylow_overgroup_eq_top_of_even_simple_central_quotient
    heven D P hTD
  apply le_antisymm
  · exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le _ _)
  · intro m hm
    have hd : (⟨m, hm⟩ : M) ∈ D := hD ▸ Subgroup.mem_top _
    exact hd

@[expose] def actualResidual {G : Type u} [Group G] (H0 : Subgroup G) : Subgroup G :=
  (CFSG.perfectResidual H0).map H0.subtype

theorem actualResidual_properties {G : Type u} [Group G] [Finite G]
    (H0 : Subgroup G) [H0.Normal] :
    Group.IsPerfect (actualResidual H0) ∧ (actualResidual H0).Normal ∧
      actualResidual H0 ≤ H0 := by
  let : Group.IsPerfect (CFSG.perfectResidual H0) := perfectResidual_isPerfect
  let : (CFSG.perfectResidual H0).Characteristic := perfectResidual_characteristic
  exact ⟨Group.IsPerfect.map H0.subtype, ConjAct.normal_of_characteristic_of_normal,
    Subgroup.map_subtype_le _⟩

theorem actualResidual_image {G : Type u} {H : Type v} [Group G] [Finite G] [Group H]
    (f : G →* H) (H0 : Subgroup G) (M : Subgroup H) [Group.IsPerfect M]
    (himage : H0.map f = M) : (actualResidual H0).map f = M := by
  let g : H0 →* M := (f.domRestrict H0).codRestrict M fun h => by
    rw [← himage]
    exact Subgroup.mem_map_of_mem f h.property
  have hg : Function.Surjective g := by
    intro m
    have hm : m.val ∈ H0.map f := himage ▸ m.property
    obtain ⟨h, hh, hhm⟩ := Subgroup.mem_map.mp hm
    exact ⟨⟨h, hh⟩, Subtype.ext hhm⟩
  have hr := congrArg (Subgroup.map M.subtype) (perfectResidual_surjects g hg)
  rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_map] at hr
  change (CFSG.perfectResidual H0).map (f.comp H0.subtype) = M at hr
  rw [actualResidual, Subgroup.map_map]
  exact hr

theorem original_quotient_preimage_factorization {G : Type u} [Group G]
    (R : Subgroup G) [R.Normal] (M : Subgroup (G ⧸ R)) (J : Subgroup G)
    (himage : J.map (QuotientGroup.mk' R) = M) :
    J ⊔ R = M.comap (QuotientGroup.mk' R) := by
  rw [← himage, Subgroup.comap_map_eq, QuotientGroup.ker_mk']


theorem kernel_centralizer_lift_center_product {G : Type u} [Group G]
    (R J Y : Subgroup G) [R.Normal]
    (hproduct : J ⊔ R = Y) (hJR : J ≤ Subgroup.centralizer (R : Set G)) :
    Y ⊓ Subgroup.centralizer (R : Set G) =
      J ⊔ (Subgroup.center R).map R.subtype := by
  let Z := (Subgroup.center R).map R.subtype
  have hZC : Z ≤ Subgroup.centralizer (R : Set G) := by
    rintro z ⟨c, hc, rfl⟩ r hr
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc (⟨r, hr⟩ : R))
  apply le_antisymm
  · intro h hh
    have hy : h ∈ J ⊔ R := hproduct ▸ hh.1
    obtain ⟨j, hj, r, hr, hprod⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have hrC : r ∈ Subgroup.centralizer (R : Set G) := by
      have := (Subgroup.centralizer (R : Set G)).mul_mem
        ((Subgroup.centralizer (R : Set G)).inv_mem (hJR hj)) hh.2
      rwa [← hprod, inv_mul_cancel_left] at this
    have hrZ : r ∈ Z := by
      refine Subgroup.mem_map.mpr ⟨⟨r, hr⟩, ?_, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro a
      exact Subtype.ext (hrC a.val a.property)
    rw [← hprod]
    exact Subgroup.mul_mem_sup hj hrZ
  · apply sup_le
    · exact le_inf (le_sup_left.trans_eq hproduct) hJR
    · exact le_inf ((Subgroup.map_subtype_le _).trans
        (le_sup_right.trans_eq hproduct)) hZC

theorem kernel_center_central_in_centralizer {G : Type u} [Group G]
    (R Y : Subgroup G) :
    (((Subgroup.center R).map R.subtype).subgroupOf
      (Y ⊓ Subgroup.centralizer (R : Set G))) ≤
        Subgroup.center (↥(Y ⊓ Subgroup.centralizer (R : Set G))) := by
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Subgroup.mem_map.mp hz
  apply Subgroup.mem_center_iff.mpr
  intro h
  apply Subtype.ext
  change (h : G) * (z : G) = (z : G) * (h : G)
  change r.val = z.val at hrz
  rw [← hrz]
  exact (h.property.2 r.val r.property).symm

theorem kernel_centralizer_derived_eq_lift {G : Type u} [Group G]
    (R J Y : Subgroup G) [R.Normal] [Group.IsPerfect J]
    (hproduct : J ⊔ R = Y) (hJR : J ≤ Subgroup.centralizer (R : Set G)) :
    ⁅Y ⊓ Subgroup.centralizer (R : Set G),
      Y ⊓ Subgroup.centralizer (R : Set G)⁆ = J := by
  let H0 := Y ⊓ Subgroup.centralizer (R : Set G)
  let Z := (Subgroup.center R).map R.subtype
  let Ji := J.subgroupOf H0
  let Zi := Z.subgroupOf H0
  have hJH : J ≤ H0 := le_inf (le_sup_left.trans_eq hproduct) hJR
  have hZH : Z ≤ H0 := by
    rw [show H0 = J ⊔ Z from kernel_centralizer_lift_center_product R J Y hproduct hJR]
    exact le_sup_right
  have hfactor : Ji ⊔ Zi = ⊤ := by
    change J.subgroupOf H0 ⊔ Z.subgroupOf H0 = ⊤
    rw [← Subgroup.subgroupOf_sup hJH hZH,
      ← kernel_centralizer_lift_center_product R J Y hproduct hJR]
    exact Subgroup.subgroupOf_self _
  have hZcentral : Zi ≤ Subgroup.center H0 :=
    kernel_center_central_in_centralizer R Y
  have hderived := congrArg (Subgroup.map H0.subtype)
    (CFSG.RankThreeCoreUniqueness.Helpers.commutator_central_join_eq Ji Zi hZcentral)
  rw [hfactor] at hderived
  have hJmap : Ji.map H0.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJH
  have htopmap : (⊤ : Subgroup H0).map H0.subtype = H0 := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hleft : Subgroup.map H0.subtype (⁅(⊤ : Subgroup H0), (⊤ : Subgroup H0)⁆) = ⁅H0, H0⁆ := by
    rw [Subgroup.map_commutator, htopmap]
  have hright : Subgroup.map H0.subtype (⁅Ji, Ji⁆) = J := by
    rw [Subgroup.map_commutator, hJmap]
    exact Subgroup.commutator_eq_self
  rw [hleft, hright] at hderived
  exact hderived


theorem unique_perfect_centralizing_lift {G : Type u} [Group G]
    (R : Subgroup G) [R.Normal] (M : Subgroup (G ⧸ R)) (J J1 : Subgroup G)
    [Group.IsPerfect J] [Group.IsPerfect J1]
    (hJimage : J.map (QuotientGroup.mk' R) = M)
    (hJ1image : J1.map (QuotientGroup.mk' R) = M)
    (hJR : J ≤ Subgroup.centralizer (R : Set G))
    (hJ1R : J1 ≤ Subgroup.centralizer (R : Set G)) : J1 = J := by
  let Y := M.comap (QuotientGroup.mk' R)
  have hpJ := original_quotient_preimage_factorization R M J hJimage
  have hpJ1 := original_quotient_preimage_factorization R M J1 hJ1image
  rw [← kernel_centralizer_derived_eq_lift R J1 Y hpJ1 hJ1R,
    kernel_centralizer_derived_eq_lift R J Y hpJ hJR]

theorem centralizing_kernel_centers {G : Type u} [Group G]
    (R J : Subgroup G) (hJR : J ≤ Subgroup.centralizer (R : Set G)) :
    ((J ⊓ R).subgroupOf J) ≤ Subgroup.center J ∧
      ((J ⊓ R).subgroupOf R) ≤ Subgroup.center R := by
  constructor
  · intro e he
    apply Subgroup.mem_center_iff.mpr
    intro j
    exact Subtype.ext (hJR j.property e.val he.2).symm
  · intro e he
    apply Subgroup.mem_center_iff.mpr
    intro r
    exact Subtype.ext (hJR he.1 r.val r.property)

instance originalIntersectionKernel_normal {G : Type u} [Group G]
    (R J : Subgroup G) [R.Normal] : ((J ⊓ R).subgroupOf J).Normal := by
  have h : (J ⊓ R).subgroupOf J = R.subgroupOf J := by
    ext j
    change (j.val ∈ J ∧ j.val ∈ R) ↔ j.val ∈ R
    exact and_iff_right j.property
  rw [h]
  infer_instance

theorem original_central_extension {G : Type u} [Group G]
    (R : Subgroup G) [R.Normal] (J : Subgroup G) (M : Subgroup (G ⧸ R))
    (himage : J.map (QuotientGroup.mk' R) = M) :
    ∃ e : J ⧸ ((J ⊓ R).subgroupOf J) ≃* M,
      ∀ j : J, e (QuotientGroup.mk j) =
        ⟨QuotientGroup.mk' R j.val, by
          rw [← himage]
          exact Subgroup.mem_map_of_mem _ j.property⟩ := by
  let f : J →* M := ((QuotientGroup.mk' R).domRestrict J).codRestrict M fun j => by
    rw [← himage]
    exact Subgroup.mem_map_of_mem _ j.property
  have hf : Function.Surjective f := by
    intro m
    have hm : m.val ∈ J.map (QuotientGroup.mk' R) := himage ▸ m.property
    obtain ⟨j, hj, hjm⟩ := Subgroup.mem_map.mp hm
    exact ⟨⟨j, hj⟩, Subtype.ext hjm⟩
  have hker : ((J ⊓ R).subgroupOf J) = f.ker := by
    ext j
    change (j.val ∈ J ∧ j.val ∈ R) ↔ f j = 1
    rw [show f j = 1 ↔ QuotientGroup.mk' R j.val = 1 from
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩,
      show (QuotientGroup.mk' R) j.val = 1 ↔ j.val ∈ R from
        QuotientGroup.eq_one_iff j.val]
    exact and_iff_right j.property
  let e := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨e, ?_⟩
  intro j
  rfl


theorem primewise_Sylow_centralizer_coverage_gives_canonical_perfect_lift
    {G : Type u} [Group G] [Finite G] (R : Subgroup G) [R.Normal]
    (hR : Odd (Nat.card R)) (M : Subgroup (G ⧸ R)) [M.Normal]
    (hM : CFSG.IsQuasisimple M)
    (heven : Even (Nat.card (M ⧸ Subgroup.center M)))
    (hcov : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card R →
      ∃ P : Sylow ell R,
        (Subgroup.centralizer (((P : Subgroup R).map R.subtype) : Set G) ⊓
          M.comap (QuotientGroup.mk' R)).map (QuotientGroup.mk' R) = M) :
    let pi := QuotientGroup.mk' R
    let Y := M.comap pi
    let H0 := Y ⊓ Subgroup.centralizer (R : Set G)
    let J := (CFSG.perfectResidual H0).map H0.subtype
    let E := J ⊓ R
    Group.IsPerfect J ∧ J.Normal ∧ J ≤ Y ∧ J.map pi = M ∧
      J ≤ Subgroup.centralizer (R : Set G) ∧ ⁅J, R⁆ = ⊥ ∧
      J ⊔ R = Y ∧ (Y : Set G) = (J : Set G) * (R : Set G) ∧
      Odd (Nat.card E) ∧ E.subgroupOf J ≤ Subgroup.center J ∧
      E.subgroupOf R ≤ Subgroup.center R ∧
      H0 = J ⊔ (Subgroup.center R).map R.subtype ∧
      (H0 : Set G) = (J : Set G) * (((Subgroup.center R).map R.subtype) : Set G) ∧
      ⁅H0, H0⁆ = J ∧
      (∀ J1 : Subgroup G, Group.IsPerfect J1 → J1 ≤ Y →
        J1.map pi = M → J1 ≤ Subgroup.centralizer (R : Set G) → J1 = J) ∧
      ∃ e : J ⧸ E.subgroupOf J ≃* M,
        ∀ j : J, (e (QuotientGroup.mk j) : G ⧸ R) = pi j.val := by
  dsimp only
  let pi := QuotientGroup.mk' R
  let Y := M.comap pi
  let H0 := Y ⊓ Subgroup.centralizer (R : Set G)
  let J := actualResidual H0
  let : Group.IsPerfect M := hM.1
  let : IsSimpleGroup (M ⧸ Subgroup.center M) := hM.2.1
  have hHimage : H0.map pi = M :=
    primewise_coverage_kernel_centralizer_image R hR M heven hcov
  obtain ⟨hJperfect, hJnormal, hJH⟩ := actualResidual_properties H0
  let : Group.IsPerfect J := hJperfect
  let : J.Normal := hJnormal
  have hJimage : J.map pi = M := actualResidual_image pi H0 M hHimage
  have hJY : J ≤ Y := hJH.trans inf_le_left
  have hJR : J ≤ Subgroup.centralizer (R : Set G) := hJH.trans inf_le_right
  have hproduct : J ⊔ R = Y := original_quotient_preimage_factorization R M J hJimage
  have hcenters := centralizing_kernel_centers R J hJR
  have hcenterproduct : H0 = J ⊔ (Subgroup.center R).map R.subtype :=
    kernel_centralizer_lift_center_product R J Y hproduct hJR
  have hcenterNormal : ((Subgroup.center R).map R.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  let : ((Subgroup.center R).map R.subtype).Normal := hcenterNormal
  have hsetproduct : (Y : Set G) = (J : Set G) * (R : Set G) := by
    rw [← hproduct]
    exact Subgroup.mul_normal J R
  have hsetcenterproduct : (H0 : Set G) =
      (J : Set G) * (((Subgroup.center R).map R.subtype) : Set G) := by
    rw [hcenterproduct]
    exact Subgroup.mul_normal J ((Subgroup.center R).map R.subtype)
  refine ⟨hJperfect, hJnormal, hJY, hJimage, hJR,
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJR, hproduct,
    hsetproduct, hR.of_dvd_nat
      (Subgroup.card_dvd_of_le (show J ⊓ R ≤ R from inf_le_right)),
    hcenters.1, hcenters.2, hcenterproduct,
    hsetcenterproduct,
    kernel_centralizer_derived_eq_lift R J Y hproduct hJR, ?_, ?_⟩
  · intro J1 hJ1perfect _hJ1Y hJ1image hJ1R
    let : Group.IsPerfect J1 := hJ1perfect
    exact unique_perfect_centralizing_lift R M J J1 hJimage hJ1image hJR hJ1R
  · obtain ⟨e, he⟩ := original_central_extension R J M hJimage
    exact ⟨e, fun j => congrArg Subtype.val (he j)⟩

theorem trivial_kernel_primewise_coverage {G : Type u} [Group G]
    (R : Subgroup G) [R.Normal] (hR : R = ⊥) (M : Subgroup (G ⧸ R)) :
    ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card R →
      ∃ P : Sylow ell R,
        (Subgroup.centralizer (((P : Subgroup R).map R.subtype) : Set G) ⊓
          M.comap (QuotientGroup.mk' R)).map (QuotientGroup.mk' R) = M := by
  intro ell hell hdiv
  rw [hR, Subgroup.card_bot] at hdiv
  exact False.elim (hell.not_dvd_one hdiv)

end CFSG.Wreathed.PrimewisePerfectLift
