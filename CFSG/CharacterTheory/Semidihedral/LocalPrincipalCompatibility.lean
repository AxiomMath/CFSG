module

public import CFSG.CharacterTheory.Semidihedral.SameParameterRegularity
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeQOddRestriction

public section

namespace CFSG.Semidihedral.LocalPrincipalCompatibility

noncomputable section

open scoped Pointwise
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.SameParameterRegularity
open CFSG.Semidihedral.Principal
open CFSG.Open
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.TwoRankLowerBound.Helpers
open CFSG.GorensteinWalter

@[expose] def centralizerInclusion {G : Type*} [Group G]
    (U : Subgroup G) (t : U) : C t →* C (t : G) :=
  (U.comap (C (t : G)).subtype).subtype.comp
    (subgroupCentralizerEquiv U t).toMonoidHom

theorem centralizerInclusion_coe {G : Type*} [Group G]
    (U : Subgroup G) (t : U) (b : C t) :
    (centralizerInclusion U t b : G) = ((b : U) : G) := rfl

theorem centralizerInclusion_involution {G : Type*} [Group G]
    (U : Subgroup G) (t : U) :
    centralizerInclusion U t (tInC t) = tInC (t : G) := rfl

theorem centralizerInclusion_injective {G : Type*} [Group G]
    (U : Subgroup G) (t : U) : Function.Injective (centralizerInclusion U t) :=
  (U.comap (C (t : G)).subtype).subtype_injective.comp
    (subgroupCentralizerEquiv U t).injective

theorem centralizerInclusion_range {G : Type*} [Group G]
    (U : Subgroup G) (t : U) :
    (centralizerInclusion U t).range = U.comap (C (t : G)).subtype := by
  rw [centralizerInclusion, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (subgroupCentralizerEquiv U t).surjective,
    Subgroup.map_top, Subgroup.range_subtype]

theorem centralizerInclusion_Z {G : Type*} [Group G]
    (U : Subgroup G) (t : U) :
    (Z t).map (centralizerInclusion U t) = Z (t : G) := by
  rw [Z, MonoidHom.map_zpowers, centralizerInclusion_involution]

theorem full_kernel_intersection {G : Type*} [Group G]
    (U : Subgroup G) (t : U)
    (hcore : (N t).map (centralizerInclusion U t) =
      (U.comap (C (t : G)).subtype) ⊓ N (t : G)) :
    (NZ (t : G)).comap (centralizerInclusion U t) = NZ t := by
  let i := centralizerInclusion U t
  have hR : (N (t : G)).comap i = N t := by
    apply Subgroup.map_injective (f := i) (centralizerInclusion_injective U t)
    rw [Subgroup.map_comap_eq, centralizerInclusion_range]
    exact hcore.symm
  apply le_antisymm
  · intro b hb
    change i b ∈ N (t : G) ⊔ Z (t : G) at hb
    obtain ⟨c, hc, z, hz, hcz⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    obtain ⟨a, ha, hia⟩ := Subgroup.mem_map.mp
      ((centralizerInclusion_Z U t).symm ▸ hz)
    have hba : b * a⁻¹ ∈ N t := by
      rw [← hR]
      change i (b * a⁻¹) ∈ N (t : G)
      rw [map_mul, map_inv, hia, ← hcz, mul_inv_cancel_right]
      exact hc
    have heq : (b * a⁻¹) * a = b := by group
    exact heq ▸ (NZ t).mul_mem ((le_sup_left : N t ≤ NZ t) hba) ((le_sup_right : Z t ≤ NZ t) ha)
  · apply sup_le
    · rw [← hR]
      exact Subgroup.comap_mono le_sup_left
    · intro z hz
      change i z ∈ N (t : G) ⊔ Z (t : G)
      apply (le_sup_right : Z (t : G) ≤ NZ (t : G))
      rw [← centralizerInclusion_Z U t]
      exact Subgroup.mem_map_of_mem i hz

@[expose] def reducedInclusion {G : Type*} [Group G]
    (U : Subgroup G) (t : U)
    (hkernel : (NZ (t : G)).comap (centralizerInclusion U t) = NZ t) :
    Gamma t →* Gamma (t : G) :=
  QuotientGroup.lift (NZ t) ((kappa (t : G)).comp (centralizerInclusion U t))
    (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hkernel])

theorem reducedInclusion_kappa {G : Type*} [Group G]
    (U : Subgroup G) (t : U)
    (hkernel : (NZ (t : G)).comap (centralizerInclusion U t) = NZ t) (b : C t) :
    reducedInclusion U t hkernel (kappa t b) = kappa (t : G) (centralizerInclusion U t b) :=
  rfl

theorem reducedInclusion_injective {G : Type*} [Group G]
    (U : Subgroup G) (t : U)
    (hkernel : (NZ (t : G)).comap (centralizerInclusion U t) = NZ t) :
    Function.Injective (reducedInclusion U t hkernel) := by
  unfold reducedInclusion
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact hkernel.symm

theorem reducedInclusion_range {G : Type*} [Group G]
    (U : Subgroup G) (t : U)
    (hkernel : (NZ (t : G)).comap (centralizerInclusion U t) = NZ t) :
    (reducedInclusion U t hkernel).range =
      (U.comap (C (t : G)).subtype).map (kappa (t : G)) := by
  have hcomp : (reducedInclusion U t hkernel).comp (kappa t) =
      (kappa (t : G)).comp (centralizerInclusion U t) := rfl
  have hr := congrArg MonoidHom.range hcomp
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
    Subgroup.map_top, MonoidHom.range_comp, centralizerInclusion_range] at hr
  exact hr

theorem simple_normal_subgroups_equal {X : Type*} [Group X]
    (L M : Subgroup X) [L.Normal] [M.Normal] [IsSimpleGroup L] [IsSimpleGroup M]
    (hcentral : Subgroup.centralizer (L : Set X) = ⊥) : M = L := by
  have hnontrivial : L ⊓ M ≠ ⊥ := by
    intro hbot
    have hdisjoint : Disjoint L M := disjoint_iff.mpr hbot
    have hM : M ≤ Subgroup.centralizer (L : Set X) := by
      intro m hm
      apply Subgroup.mem_centralizer_iff.mpr
      intro l hl
      exact (Subgroup.commute_of_normal_of_disjoint L M inferInstance inferInstance
        hdisjoint l m hl hm).eq
    have hMbot : M = ⊥ := le_antisymm (hcentral ▸ hM) bot_le
    exact (Subgroup.isSimpleGroup_iff.mp (inferInstance : IsSimpleGroup M)).1 hMbot
  have hL : L ⊓ M = L := by
    rcases (Subgroup.isSimpleGroup_iff.mp (inferInstance : IsSimpleGroup L)).2
      (L ⊓ M) inf_le_left inferInstance with h | h
    · exact False.elim (hnontrivial h)
    · exact h
  have hM : L ⊓ M = M := by
    rcases (Subgroup.isSimpleGroup_iff.mp (inferInstance : IsSimpleGroup M)).2
      (L ⊓ M) inf_le_right inferInstance with h | h
    · exact False.elim (hnontrivial h)
    · exact h
  exact hM.symm.trans hL

theorem normal_image_in_range {X Y : Type*} [Group X] [Group Y]
    (j : X →* Y) (M : Subgroup X) [M.Normal] : (M.map j).subgroupOf j.range |>.Normal := by
  let M' := M.map j.rangeRestrict
  have hM' : M'.Normal := Subgroup.Normal.map inferInstance _ j.rangeRestrict_surjective
  have hmap : M'.map j.range.subtype = M.map j := by
    rw [Subgroup.map_map]
    rfl
  have heq : (M.map j).subgroupOf j.range = M' := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective j.range.subtype_injective M'
  exact heq.symm ▸ hM'

theorem actual_layer_image {X Y : Type*} [Group X] [Group Y]
    (j : X →* Y) (hinj : Function.Injective j)
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    [IsSimpleGroup (CFSG.generalizedFitting Y)]
    (hcover : CFSG.generalizedFitting Y ≤ j.range)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) = ⊥) :
    (CFSG.generalizedFitting X).map j = CFSG.generalizedFitting Y := by
  let L := CFSG.generalizedFitting Y
  let M := (CFSG.generalizedFitting X).map j
  let E := j.range
  have hMle : M ≤ E := Subgroup.map_le_range _ _
  let eM := (CFSG.generalizedFitting X).equivMapOfInjective j hinj
  let : IsSimpleGroup M := eM.symm.isSimpleGroup
  let : IsSimpleGroup (M.subgroupOf E) := (Subgroup.subgroupOfEquivOfLe hMle).isSimpleGroup
  let : IsSimpleGroup (L.subgroupOf E) := (Subgroup.subgroupOfEquivOfLe hcover).isSimpleGroup
  let : (M.subgroupOf E).Normal := normal_image_in_range j _
  have hC : Subgroup.centralizer (L.subgroupOf E : Set E) = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    have hxc : (x : Y) ∈ Subgroup.centralizer (L : Set Y) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro l hl
      have h := Subgroup.mem_centralizer_iff.mp hx (⟨l, hcover hl⟩ : E) hl
      exact congrArg Subtype.val h
    rw [hcentral, Subgroup.mem_bot] at hxc
    exact Subtype.ext hxc
  have heq : M.subgroupOf E = L.subgroupOf E :=
    simple_normal_subgroups_equal _ _ hC
  have h := congrArg (Subgroup.map E.subtype) heq
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hMle, inf_eq_left.mpr hcover] at h
  exact h

theorem reducedInclusion_covers_layer {G : Type*} [Group G]
    (U : Subgroup G) (t : U)
    (hkernel : (NZ (t : G)).comap (centralizerInclusion U t) = NZ t)
    (hcover : (CFSG.generalizedFitting (Gamma (t : G))).comap (barKappa (t : G)) ≤
      (U.comap (C (t : G)).subtype).map (nu (t : G))) :
    CFSG.generalizedFitting (Gamma (t : G)) ≤ (reducedInclusion U t hkernel).range := by
  rw [reducedInclusion_range]
  have hmap := Subgroup.map_mono (f := barKappa (t : G)) hcover
  rw [Subgroup.map_comap_eq_self_of_surjective (barKappa_surjective _),
    Subgroup.map_map, barKappa_comp_nu] at hmap
  exact hmap

theorem odd_order_closure_map_le {X Y : Type*} [Group X] [Group Y] (j : X →* Y) :
    (Subgroup.closure {x : X | Odd (orderOf x)}).map j ≤
      Subgroup.closure {y : Y | Odd (orderOf y)} := by
  rw [MonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro y ⟨x, hx, rfl⟩
  exact Subgroup.subset_closure (hx.of_dvd_nat (orderOf_map_dvd j x))

theorem centralizerInclusion_K_le {G : Type*} [Group G] (U : Subgroup G) (t : U) :
    (K t).map (centralizerInclusion U t) ≤ K (t : G) := by
  rw [K_eq_odd_order_closure, K_eq_odd_order_closure]
  exact odd_order_closure_map_le _

theorem index_two_odd_index_comap {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (j : X →* Y) (A : Subgroup X) (D : Subgroup Y) [D.Normal]
    (hA : A.index = 2) (hD : D.index = 2) (hodd : Odd j.range.index)
    (hAD : A.map j ≤ D) : D.comap j = A := by
  have hle : A ≤ D.comap j := Subgroup.map_le_iff_le_comap.mp hAD
  have hdiv : (D.comap j).index ∣ 2 := by
    rw [Subgroup.index_comap, ← hD]
    exact Subgroup.relIndex_dvd_index_of_normal (H := D) (K := j.range)
  have hne : (D.comap j).index ≠ 1 := by
    intro h1
    have hrange : j.range ≤ D := by
      have htop := Subgroup.index_eq_one.mp h1
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      exact (show x ∈ D.comap j from htop ▸ Subgroup.mem_top x)
    have hdvd : 2 ∣ j.range.index := hD ▸ Subgroup.index_dvd_of_le hrange
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hindex : (D.comap j).index = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left hne
  have heq : A = D.comap j := Subgroup.eq_of_index_dvd_index hle (by rw [hA, hindex])
  exact heq.symm

@[expose] def layerEquiv {X Y : Type*} [Group X] [Group Y]
    (j : X →* Y) (hinj : Function.Injective j) (M : Subgroup X) (L : Subgroup Y)
    (himage : M.map j = L) : M ≃* L :=
  (M.equivMapOfInjective j hinj).trans (MulEquiv.subgroupCongr himage)

theorem layerEquiv_coe {X Y : Type*} [Group X] [Group Y]
    (j : X →* Y) (hinj : Function.Injective j) (M : Subgroup X) (L : Subgroup Y)
    (himage : M.map j = L) (x : M) :
    (layerEquiv j hinj M L himage x : Y) = j x := rfl

theorem layerEquiv_conjNormal {X Y : Type*} [Group X] [Group Y]
    (j : X →* Y) (hinj : Function.Injective j) (M : Subgroup X) (L : Subgroup Y)
    [M.Normal] [L.Normal] (himage : M.map j = L) (x : X) (a : M) :
    layerEquiv j hinj M L himage (MulAut.conjNormal (H := M) x a) =
      MulAut.conjNormal (H := L) (j x) (layerEquiv j hinj M L himage a) := by
  apply Subtype.ext
  simp only [layerEquiv_coe, MulAut.conjNormal_apply, map_mul, map_inv]

theorem sylow_map_bijective {M L : Type*} [Group M] [Group L] [Finite M]
    (p : ℕ) [Fact p.Prime] (e : M ≃* L) :
    Function.Bijective (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective :
      Sylow p M → Sylow p L) := by
  refine ⟨?_, Sylow.mapSurjective_surjective e.surjective p⟩
  intro P Q hPQ
  apply Sylow.ext
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  exact congrArg Sylow.toSubgroup hPQ

set_option backward.isDefEq.respectTransparency false in
theorem sylow_map_conjNormal {X Y : Type*} [Group X] [Group Y] [Finite X]
    (p : ℕ) [Fact p.Prime] (j : X →* Y) (hinj : Function.Injective j)
    (M : Subgroup X) (L : Subgroup Y) [M.Normal] [L.Normal]
    (himage : M.map j = L) (x : X) (P : Sylow p M) :
    Sylow.mapSurjective (f := (layerEquiv j hinj M L himage).toMonoidHom)
      (show Function.Surjective (layerEquiv j hinj M L himage).toMonoidHom from
        (layerEquiv j hinj M L himage).surjective) (MulAut.conjNormal (H := M) x • P) =
    MulAut.conjNormal (H := L) (j x) •
      Sylow.mapSurjective (f := (layerEquiv j hinj M L himage).toMonoidHom)
        (show Function.Surjective (layerEquiv j hinj M L himage).toMonoidHom from
          (layerEquiv j hinj M L himage).surjective) P := by
  apply Sylow.ext
  rw [Sylow.coe_mapSurjective, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def,
    Sylow.pointwise_smul_def, Sylow.coe_mapSurjective, Subgroup.pointwise_smul_def,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  exact congrArg Subtype.val (layerEquiv_conjNormal j hinj M L himage x a)

theorem sylow_fixed_card_inclusion {X Y : Type*} [Group X] [Group Y] [Finite X]
    (p : ℕ) [Fact p.Prime] (j : X →* Y) (hinj : Function.Injective j)
    (M : Subgroup X) (L : Subgroup Y) [M.Normal] [L.Normal]
    (himage : M.map j = L) (x : X) :
    Nat.card {P : Sylow p M // MulAut.conjNormal (H := M) x • P = P} =
      Nat.card {P : Sylow p L // MulAut.conjNormal (H := L) (j x) • P = P} := by
  let e := layerEquiv j hinj M L himage
  let beta : Sylow p M → Sylow p L :=
    Sylow.mapSurjective (f := e.toMonoidHom)
      (show Function.Surjective e.toMonoidHom from e.surjective)
  have hbeta : Function.Bijective (beta : Sylow p M → Sylow p L) := sylow_map_bijective p e
  apply Nat.card_congr
  apply (Equiv.ofBijective beta hbeta).subtypeEquiv
  intro P
  change MulAut.conjNormal (H := M) x • P = P ↔
    MulAut.conjNormal (H := L) (j x) • beta P = beta P
  rw [← sylow_map_conjNormal p j hinj M L himage x P]
  change MulAut.conjNormal (H := M) x • P = P ↔
    beta (MulAut.conjNormal (H := M) x • P) = beta P
  exact ⟨fun h => congrArg beta h, fun h => hbeta.injective h⟩

@[expose] def residualSign {G : Type*} [Group G] (t : G) (c : C t) : ℂ :=
  by classical exact if c ∈ K t then 1 else -1

@[expose] def intrinsicPhi {G : Type*} [Group G] (p : ℕ) (t : G) (c : C t) : ℂ :=
  (Nat.card {P : Sylow p (CFSG.generalizedFitting (Gamma t)) //
    ((P : Subgroup (CFSG.generalizedFitting (Gamma t))).map
      (CFSG.generalizedFitting (Gamma t)).subtype).map
        (MulAut.conj (kappa t c)).toMonoidHom =
      (P : Subgroup (CFSG.generalizedFitting (Gamma t))).map
        (CFSG.generalizedFitting (Gamma t)).subtype} : ℂ) - 1

theorem intrinsicPhi_eq_conjNormal {G : Type*} [Group G] (p : ℕ) (t : G) (c : C t) :
    intrinsicPhi p t c =
      (Nat.card {P : Sylow p (CFSG.generalizedFitting (Gamma t)) //
        MulAut.conjNormal (H := CFSG.generalizedFitting (Gamma t)) (kappa t c) • P = P} :
          ℂ) - 1 := by
  unfold intrinsicPhi
  congr 2
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P =>
    (conjNormal_smul_eq_iff_map_conj_eq _ _ P).symm)

theorem intrinsicPhi_restriction {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (U : Subgroup G) (t : U)
    (j : Gamma t →* Gamma (t : G)) (hinj : Function.Injective j)
    (hrep : ∀ b : C t, j (kappa t b) = kappa (t : G) (centralizerInclusion U t b))
    (himage : (CFSG.generalizedFitting (Gamma t)).map j =
      CFSG.generalizedFitting (Gamma (t : G))) (b : C t) :
    intrinsicPhi p (t : G) (centralizerInclusion U t b) = intrinsicPhi p t b := by
  rw [intrinsicPhi_eq_conjNormal, intrinsicPhi_eq_conjNormal, ← hrep]
  rw [sylow_fixed_card_inclusion p j hinj _ _ himage]

theorem residualSign_restriction {G : Type*} [Group G] (U : Subgroup G) (t : U)
    (hK : (K (t : G)).comap (centralizerInclusion U t) = K t) (b : C t) :
    residualSign (t : G) (centralizerInclusion U t b) = residualSign t b := by
  classical
  have hmem : centralizerInclusion U t b ∈ K (t : G) ↔ b ∈ K t := by
    change b ∈ (K (t : G)).comap (centralizerInclusion U t) ↔ b ∈ K t
    rw [hK]
  simp only [residualSign, hmem]

theorem localDelta_eq_residualSign {G : Type*} [Group G] {t : G} {n p f : ℕ}
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F)
    (data : ActualMatrixData t n p f F A rho) (hNZK : NZ t ≤ K t)
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (c : C t) :
    localDelta F rho c = residualSign t c := by
  classical
  have hF : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hpodd, hf, data.field_card⟩
  have hiff := localDelta_eq_one_iff F A rho data.faithful data.full_image
    data.residual_image hNZK hF c
  by_cases hc : c ∈ K t
  · rw [residualSign, ite_eq_left hc]
    exact hiff.mpr hc
  · rw [residualSign, ite_eq_right hc]
    exact localDelta_eq_neg_one_of_not_mem F rho c (fun h => hc (hiff.mp h))

theorem localPhi_eq_intrinsicPhi {G : Type*} [Group G] [Finite G] {t : G} {n p f : ℕ}
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F)
    (data : ActualMatrixData t n p f F A rho) (hp : p.Prime) (c : C t) :
    localPhi F rho c = intrinsicPhi p t c := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, data.field_card])
  let L := CFSG.generalizedFitting (Gamma t)
  let psi : Gamma t →* Equiv.Perm (Omega F) :=
    (coordinateE F).subtype.comp rho
  have hinj : Function.Injective (psi.comp L.subtype) :=
    ((coordinateE F).subtype_injective.comp
      data.faithful).comp L.subtype_injective
  have hrange : L.map psi =
      coordinateG F := by
    have hGE := (coordinateG_le_D F).trans
      (coordinateD_le_E F)
    rw [← Subgroup.map_map, data.layer_image, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hGE]
  obtain ⟨-, -, -, hcount⟩ := exists_equivariant_point_sylow_bijection p F L psi hinj hrange
  have hcard : Nat.card {x : Omega F //
      psi (kappa t c) x = x} =
    Nat.card {P : Sylow p L // MulAut.conjNormal (H := L) (kappa t c) • P = P} := by
    have h := hcount (kappa t c)
    omega
  rw [intrinsicPhi_eq_conjNormal]
  unfold localPhi
  exact congrArg (fun k : ℕ => (k : ℂ) - 1) hcard

theorem K_index_two {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (e : SemidihedralGroup n ≃* S)
    (hG : ∀ V : Subgroup G, V.index ≠ 2) (t : G) (ht : orderOf t = 2) :
    (K t).index = 2 := by
  obtain ⟨S', e', hcenter⟩ :=
    CFSG.Semidihedral.InvolutionFusion.exists_centered_semidihedral_sylow n hn S e hG t ht
  have hcenter' : CFSG.Semidihedral.CentralizerResidual.centeredInvolution n S' e' = t :=
    hcenter
  subst t
  exact CFSG.Semidihedral.CentralizerResidual.oddResidual_index n hn S' e' hG

theorem centralizer_K_intersection {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) (t : U) (hKG : (K (t : G)).index = 2) (hKU : (K t).index = 2)
    (hodd : Odd (U.comap (C (t : G)).subtype).index) :
    (K (t : G)).comap (centralizerInclusion U t) = K t ∧
      (K t).map (centralizerInclusion U t) =
        (U.comap (C (t : G)).subtype) ⊓ K (t : G) := by
  have hpre := index_two_odd_index_comap (centralizerInclusion U t) (K t) (K (t : G))
    hKU hKG (by rw [centralizerInclusion_range]; exact hodd) (centralizerInclusion_K_le U t)
  refine ⟨hpre, ?_⟩
  rw [← hpre, Subgroup.map_comap_eq, centralizerInclusion_range, inf_comm]

structure ExplicitPrincipalCharacters {G : Type*} [Group G] (p q : ℕ) (t : G)
    [Fintype (C t)] (basis : FiniteIrreducibleCharacterBasis (C t))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) : Prop where
  distinct : ([1, residualSign t, intrinsicPhi p t,
    residualSign t * intrinsicPhi p t] : List (C t → ℂ)).Nodup
  characters : ∀ (chi : C t → ℂ) (degree : ℕ),
    (chi, degree) ∈ [(1, 1), (residualSign t, 1), (intrinsicPhi p t, q),
      (residualSign t * intrinsicPhi p t, q)] →
    ∃ label : basis.index, (basis.representation label).character = chi ∧
      (basis.representation label).IsIrreducible ∧
      label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      (∀ c, ∃ z : ℤ, chi c = z) ∧
      Module.finrank ℂ (basis.representation label).vector = degree ∧ chi 1 = degree

theorem explicit_principal_characters_of_actual_data {G : Type*} [Group G] [Finite G]
    (t : G) (n p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F) (data : ActualMatrixData t n p f F A rho)
    (hNZK : NZ t ≤ K t) [Fintype (C t)]
    (basis : FiniteIrreducibleCharacterBasis (C t))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (characters : ActualCharacterData F rho (p ^ f) basis ideal principal) :
    ExplicitPrincipalCharacters p (p ^ f) t basis ideal principal := by
  obtain ⟨ld, lp, ldp, hd, hphi, hdp, hnodup, hP, hdeg1, hdegd, hdegp, hdegdp, -⟩ :=
    characters.characters
  have hdelta : (basis.representation ld).character = residualSign t := by
    funext c
    exact (hd c).trans (localDelta_eq_residualSign F A rho data hNZK hp hpodd hf c)
  have haug : (basis.representation lp).character = intrinsicPhi p t := by
    funext c
    exact (hphi c).trans (localPhi_eq_intrinsicPhi F A rho data hp c)
  have hprod : (basis.representation ldp).character = residualSign t * intrinsicPhi p t := by
    funext c
    rw [hdp, localDelta_eq_residualSign F A rho data hNZK hp hpodd hf,
      localPhi_eq_intrinsicPhi F A rho data hp]
    rfl
  refine ⟨?_, ?_⟩
  · have h := hnodup.map basis.distinct
    simpa only [List.map_cons, List.map_nil, hprincipal, hdelta, haug, hprod] using h
  · have hcert : ∀ (label : basis.index) (chi : C t → ℂ) (degree : ℕ),
        label ∈ [principal, ld, lp, ldp] →
        (basis.representation label).character = chi →
        Module.finrank ℂ (basis.representation label).vector = degree →
        ∃ label : basis.index, (basis.representation label).character = chi ∧
          (basis.representation label).IsIrreducible ∧
          label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
          (∀ c, ∃ z : ℤ, chi c = z) ∧
          Module.finrank ℂ (basis.representation label).vector = degree ∧ chi 1 = degree := by
      intro label chi degree hmem heq hdegree
      obtain ⟨hirr, hblock, hint⟩ := hP label hmem
      refine ⟨label, heq, hirr, hblock, ?_, hdegree, ?_⟩
      · simpa only [heq] using hint
      · rw [← heq, FiniteComplexRepresentation.character, Representation.char_one, hdegree]
    intro chi degree hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h
    · cases h
      exact hcert principal 1 1 (by simp) hprincipal hdeg1
    · cases h
      exact hcert ld (residualSign t) 1 (by simp) hdelta hdegd
    · cases h
      exact hcert lp (intrinsicPhi p t) (p ^ f) (by simp) haug hdegp
    · cases h
      exact hcert ldp (residualSign t * intrinsicPhi p t) (p ^ f) (by simp) hprod hdegdp

open scoped Classical in
structure SameParameterLocalPrincipalCompatibility {G : Type*} [Group G] [Fintype G]
    (U : Subgroup G) (t : U) (n m p f : ℕ)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] : Prop where
  core_intersection : (N t).map (centralizerInclusion U t) =
    (U.comap (C (t : G)).subtype) ⊓ N (t : G)
  kernel_intersection : (NZ (t : G)).comap (centralizerInclusion U t) = NZ t
  full_cover : (CFSG.generalizedFitting (Gamma (t : G))).comap (barKappa (t : G)) ≤
    (U.comap (C (t : G)).subtype).map (nu (t : G))
  odd_quotient_embedding : ∃ iota : H t →* H (t : G), Function.Injective iota ∧
    (∀ b : C t, iota (nu t b) = nu (t : G) (centralizerInclusion U t b)) ∧
    iota.range = (U.comap (C (t : G)).subtype).map (nu (t : G))
  full_cover_field : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
    Nonempty (((CFSG.generalizedFitting (Gamma (t : G))).comap (barKappa (t : G))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F)
  parameters : n = m
  ambient_index : Odd U.index
  centralizer_index : Odd (U.comap (C (t : G)).subtype).index
  reduced_quotient_embedding : ∃ j : Gamma t →* Gamma (t : G), Function.Injective j ∧
    (∀ b : C t, j (kappa t b) = kappa (t : G) (centralizerInclusion U t b)) ∧
    j.range = (U.comap (C (t : G)).subtype).map (kappa (t : G)) ∧
    (CFSG.generalizedFitting (Gamma t)).map j = CFSG.generalizedFitting (Gamma (t : G))
  residual_intersection : (K t).map (centralizerInclusion U t) =
    (U.comap (C (t : G)).subtype) ⊓ K (t : G)
  residual_preimage : (K (t : G)).comap (centralizerInclusion U t) = K t
  ambient_characters : ∀ (basis : FiniteIrreducibleCharacterBasis (C (t : G)))
    (principal : basis.index), (basis.representation principal).character = 1 →
    ExplicitPrincipalCharacters p (p ^ f) (t : G) basis ideal principal
  subgroup_characters : ∀ (basis : FiniteIrreducibleCharacterBasis (C t))
    (principal : basis.index), (basis.representation principal).character = 1 →
    ExplicitPrincipalCharacters p (p ^ f) t basis ideal principal
  ambient_characters_exist : ∃ (basis : FiniteIrreducibleCharacterBasis (C (t : G)))
    (principal : basis.index), (basis.representation principal).character = 1 ∧
    ExplicitPrincipalCharacters p (p ^ f) (t : G) basis ideal principal
  subgroup_characters_exist : ∃ (basis : FiniteIrreducibleCharacterBasis (C t))
    (principal : basis.index), (basis.representation principal).character = 1 ∧
    ExplicitPrincipalCharacters p (p ^ f) t basis ideal principal
  restrictions : ∀ b : C t,
    residualSign (t : G) (centralizerInclusion U t b) = residualSign t b ∧
    intrinsicPhi p (t : G) (centralizerInclusion U t b) = intrinsicPhi p t b ∧
    residualSign (t : G) (centralizerInclusion U t b) *
      intrinsicPhi p (t : G) (centralizerInclusion U t b) =
        residualSign t b * intrinsicPhi p t b
  ambient_realizations : ∀ (F : Type) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (rho : Gamma (t : G) →* coordinateE F),
    ActualMatrixData (t : G) n p f F A rho → ∀ c : C (t : G),
      localDelta F rho c = residualSign (t : G) c ∧
      localPhi F rho c = intrinsicPhi p (t : G) c ∧
      localDelta F rho c * localPhi F rho c = residualSign (t : G) c * intrinsicPhi p (t : G) c
  subgroup_realizations : ∀ (F : Type) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (rho : Gamma t →* coordinateE F),
    ActualMatrixData t m p f F A rho → ∀ b : C t,
      localDelta F rho b = residualSign t b ∧ localPhi F rho b = intrinsicPhi p t b ∧
      localDelta F rho b * localPhi F rho b = residualSign t b * intrinsicPhi p t b
  every_realization_restriction : ∀ (F : Type) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (rho : Gamma (t : G) →* coordinateE F),
    ActualMatrixData (t : G) n p f F A rho →
    ∀ (F' : Type) [Field F'] [Finite F'] (A' : Subgroup (F' ≃+* F'))
      (rho' : Gamma t →* coordinateE F'), ActualMatrixData t m p f F' A' rho' →
      ∀ b : C t,
        localDelta F rho (centralizerInclusion U t b) = localDelta F' rho' b ∧
        localPhi F rho (centralizerInclusion U t b) = localPhi F' rho' b ∧
        localDelta F rho (centralizerInclusion U t b) *
          localPhi F rho (centralizerInclusion U t b) = localDelta F' rho' b * localPhi F' rho' b

open scoped Classical in
theorem same_parameter_local_principal_character_restriction {G : Type}
    [Group G] [Fintype G] (U : Subgroup G) (t : U) (ht : orderOf t = 2)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (S : Sylow 2 G) (eS : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (eSU : SemidihedralGroup m ≃* SU)
    (hG : ∀ V : Subgroup G, V.index ≠ 2)
    (hU : ∀ V : Subgroup U, V.index ≠ 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hnonabU : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : G)) : Set (Gamma (t : G))) = ⊥)
    (hcentralU : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma (t : G))), ¬ IsCyclic V)
    (hncU : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic V)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : G))) .PSL 2 p f)
    (hmodelU : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    SameParameterLocalPrincipalCompatibility U t n m p f ideal := by
  obtain ⟨hcore, hcover, hiota, hfield, hnm, hoddU, hoddB⟩ :=
    same_parameter_subgroup_centralizer_odd_core_intersection U t ht n m hn hm S eS SU eSU
      hG hU hnonab hnonabU hcentral hcentralU hnc hncU p f hp hpodd hf hq hmodel hmodelU
  have hkernel := full_kernel_intersection U t hcore
  let j := reducedInclusion U t hkernel
  have hinj : Function.Injective j := reducedInclusion_injective U t hkernel
  have hrep : ∀ b : C t, j (kappa t b) = kappa (t : G) (centralizerInclusion U t b) :=
    reducedInclusion_kappa U t hkernel
  have hlayer : (CFSG.generalizedFitting (Gamma t)).map j =
      CFSG.generalizedFitting (Gamma (t : G)) :=
    actual_layer_image j hinj (reducedInclusion_covers_layer U t hkernel hcover) hcentral
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  obtain ⟨hKpre, hKmap⟩ := centralizer_K_intersection U t
    (K_index_two n hn S eS hG (t : G) htG) (K_index_two m hm SU eSU hU t ht) hoddB
  obtain ⟨hNZKG, -⟩ := actual_quotient_inputs n hn S eS hG (t : G) htG
  obtain ⟨hNZKU, -⟩ := actual_quotient_inputs m hm SU eSU hU t ht
  obtain ⟨F, fieldF, finiteF, A, rho, data, hcharacters⟩ :=
    actual_simple_layer_involution_centralizer_local_package n hn S eS hG (t : G) htG
      hnonab hcentral hnc p f hp hpodd hf hmodel
  let : Field F := fieldF
  let : Finite F := finiteF
  obtain ⟨FU, fieldFU, finiteFU, AU, rhoU, dataU, hcharactersU⟩ :=
    actual_simple_layer_involution_centralizer_local_package m hm SU eSU hU t ht
      hnonabU hcentralU hncU p f hp hpodd hf hmodelU
  let : Field FU := fieldFU
  let : Finite FU := finiteFU
  have hCG : ∀ (basis : FiniteIrreducibleCharacterBasis (C (t : G)))
      (principal : basis.index), (basis.representation principal).character = 1 →
      ExplicitPrincipalCharacters p (p ^ f) (t : G) basis ideal principal := by
    intro basis principal hprincipal
    exact explicit_principal_characters_of_actual_data (t : G) n p f hp hpodd hf
      F A rho data hNZKG basis ideal principal hprincipal
        (hcharacters basis ideal inferInstance inferInstance principal hprincipal)
  have hCU : ∀ (basis : FiniteIrreducibleCharacterBasis (C t))
      (principal : basis.index), (basis.representation principal).character = 1 →
      ExplicitPrincipalCharacters p (p ^ f) t basis ideal principal := by
    intro basis principal hprincipal
    exact explicit_principal_characters_of_actual_data t m p f hp hpodd hf
      FU AU rhoU dataU hNZKU basis ideal principal hprincipal
        (hcharactersU basis ideal inferInstance inferInstance principal hprincipal)
  let : Fact p.Prime := ⟨hp⟩
  have hrestr : ∀ b : C t,
      residualSign (t : G) (centralizerInclusion U t b) = residualSign t b ∧
      intrinsicPhi p (t : G) (centralizerInclusion U t b) = intrinsicPhi p t b ∧
      residualSign (t : G) (centralizerInclusion U t b) *
        intrinsicPhi p (t : G) (centralizerInclusion U t b) =
          residualSign t b * intrinsicPhi p t b := by
    intro b
    have hd := residualSign_restriction U t hKpre b
    have hphi := intrinsicPhi_restriction p U t j hinj hrep hlayer b
    exact ⟨hd, hphi, by rw [hd, hphi]⟩
  refine
    { core_intersection := hcore
      kernel_intersection := hkernel
      full_cover := hcover
      odd_quotient_embedding := hiota
      full_cover_field := hfield
      parameters := hnm
      ambient_index := hoddU
      centralizer_index := hoddB
      reduced_quotient_embedding :=
        ⟨j, hinj, hrep, reducedInclusion_range U t hkernel, hlayer⟩
      residual_intersection := hKmap
      residual_preimage := hKpre
      ambient_characters := hCG
      subgroup_characters := hCU
      ambient_characters_exist := ?_
      subgroup_characters_exist := ?_
      restrictions := hrestr
      ambient_realizations := ?_
      subgroup_realizations := ?_
      every_realization_restriction := ?_ }
  · obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := C (t : G))
    obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basis
    exact ⟨basis, principal, hprincipal, hCG basis principal hprincipal⟩
  · obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
    obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basis
    exact ⟨basis, principal, hprincipal, hCU basis principal hprincipal⟩
  · intro F' _ _ A' rho' data' c
    have hd := localDelta_eq_residualSign F' A' rho' data' hNZKG hp hpodd hf c
    have hphi := localPhi_eq_intrinsicPhi F' A' rho' data' hp c
    exact ⟨hd, hphi, by rw [hd, hphi]⟩
  · intro F' _ _ A' rho' data' b
    have hd := localDelta_eq_residualSign F' A' rho' data' hNZKU hp hpodd hf b
    have hphi := localPhi_eq_intrinsicPhi F' A' rho' data' hp b
    exact ⟨hd, hphi, by rw [hd, hphi]⟩
  · intro F' _ _ A' rho' data' FU' _ _ AU' rhoU' dataU' b
    obtain ⟨hd, hphi, -⟩ := hrestr b
    rw [localDelta_eq_residualSign F' A' rho' data' hNZKG hp hpodd hf,
      localPhi_eq_intrinsicPhi F' A' rho' data' hp,
      localDelta_eq_residualSign FU' AU' rhoU' dataU' hNZKU hp hpodd hf,
      localPhi_eq_intrinsicPhi FU' AU' rhoU' dataU' hp, hd, hphi]
    exact ⟨rfl, rfl, rfl⟩

end

end CFSG.Semidihedral.LocalPrincipalCompatibility
