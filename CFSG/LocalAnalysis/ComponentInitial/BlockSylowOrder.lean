module

public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl
public import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorFactor

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification OuterAutomorphisms
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def normalizerConjHom (J : Subgroup G) : normalizer (J : Set G) →* MulAut J where
  toFun g := conjAut J g.2
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp [coe_conjAut])
  map_mul' g h := MulEquiv.ext fun x => Subtype.ext (by simp [coe_conjAut, mul_assoc])

theorem coe_normalizerConjHom_apply (J : Subgroup G) (g : normalizer (J : Set G)) (x : J) :
    ((normalizerConjHom J g x : J) : G) = g * x * (g : G)⁻¹ := rfl

theorem ker_normalizerConjHom (J : Subgroup G) :
    (normalizerConjHom J).ker = (centralizer (J : Set G)).subgroupOf (normalizer (J : Set G)) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizer_iff]
  constructor
  · intro h x hx
    have h1 := congrArg (fun σ : MulAut J => ((σ ⟨x, hx⟩ : J) : G)) h
    simp only [coe_normalizerConjHom_apply, MulAut.one_apply] at h1
    calc x * g = (g : G) * x * (g : G)⁻¹ * g := by rw [h1]
      _ = g * x := by group
  · intro h
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [coe_normalizerConjHom_apply, MulAut.one_apply, ← h x x.2, mul_inv_cancel_right]

theorem ker_centerQuotient_comp_normalizerConjHom (J : Subgroup G) [Group.IsPerfect J] :
    ((PerfectAutomorphisms.centerQuotientHom J).comp (normalizerConjHom J)).ker =
      (centralizer (J : Set G)).subgroupOf (normalizer (J : Set G)) := by
  rw [← ker_normalizerConjHom]
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro h
    exact PerfectAutomorphisms.centerQuotientHom_injective J (h.trans (map_one _).symm)
  · intro h
    rw [h, map_one]

theorem inner_le_range_centerQuotient_comp (J : Subgroup G) :
    OuterAutomorphisms.inner (J ⧸ center J) ≤
      ((PerfectAutomorphisms.centerQuotientHom J).comp (normalizerConjHom J)).range := by
  rintro _ ⟨τ, rfl⟩
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center J) τ
  refine ⟨⟨j, le_normalizer j.2⟩, ?_⟩
  rw [MonoidHom.comp_apply, ← centerQuotient_conj]
  congr 1

theorem card_dvd_card_mul_card_outer {T : Type*} [Group T] [Finite T] (hT : center T = ⊥)
    {A : Subgroup (MulAut T)} (hA : OuterAutomorphisms.inner T ≤ A) :
    Nat.card A ∣ Nat.card T * Nat.card (Outer T) := by
  set f := (QuotientGroup.mk' (OuterAutomorphisms.inner T)).comp A.subtype with hf
  have hker : f.ker.map A.subtype = OuterAutomorphisms.inner T := by
    ext σ
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hτ)
    · intro hσ
      exact ⟨⟨σ, hA hσ⟩, MonoidHom.mem_ker.2 ((QuotientGroup.eq_one_iff _).2 hσ), rfl⟩
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hgc : g ∈ center T := mem_center_iff.2 fun y => by
      have := congrArg (fun σ : MulAut T => σ y) (MonoidHom.mem_ker.1 hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = g * y * g⁻¹ * g := by rw [this]
        _ = g * y := by group
    rw [hT] at hgc
    exact hgc
  have hinner : Nat.card (OuterAutomorphisms.inner T) = Nat.card T := by
    rw [OuterAutomorphisms.inner, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    ← Subgroup.card_map_of_injective A.subtype_injective, hker, hinner] at h1
  rw [h1, mul_comm]
  exact Nat.mul_dvd_mul_left _ (Subgroup.card_subgroup_dvd_card f.range)

variable [Finite G]

theorem ordProj_card_normalizer_le {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) :
    ordProj[2] (Nat.card (normalizer (J : Set G))) ≤
      ordProj[2] (Nat.card (centralizer (J : Set G))) * ordProj[2] (Nat.card (J ⧸ center J)) *
        ordProj[2] (Nat.card (Outer (J ⧸ center J))) := by
  have hJn := (AssemblyBPredicates.isQuasisimple_iff_native J).1 hq
  have : Group.IsPerfect J := hJn.1
  set ψ := (PerfectAutomorphisms.centerQuotientHom J).comp (normalizerConjHom J) with hψ
  have hCN : centralizer (J : Set G) ≤ normalizer (J : Set G) := centralizer_le_normalizer _
  have hcard : Nat.card (normalizer (J : Set G)) =
      Nat.card ψ.range * Nat.card (centralizer (J : Set G)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv,
      ker_centerQuotient_comp_normalizerConjHom,
      Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv] at h1
    exact h1
  have hdvd := card_dvd_card_mul_card_outer (Group.IsPerfect.center_quotient_center_eq_bot (G := J))
    (inner_le_range_centerQuotient_comp J)
  have hpos1 : Nat.card ψ.range ≠ 0 := Nat.card_pos.ne'
  have hpos2 : Nat.card (centralizer (J : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hpos3 : Nat.card (J ⧸ center J) ≠ 0 := Nat.card_pos.ne'
  have hpos4 : Nat.card (Outer (J ⧸ center J)) ≠ 0 := Nat.card_pos.ne'
  rw [hcard, Nat.ordProj_mul 2 hpos1 hpos2, mul_comm (ordProj[2] _), mul_assoc]
  refine Nat.mul_le_mul_left _ ?_
  rw [← Nat.ordProj_mul 2 hpos3 hpos4]
  exact Nat.le_of_dvd (Nat.ordProj_pos _ _)
    (Nat.ordProj_dvd_ordProj_of_dvd (Nat.mul_ne_zero hpos3 hpos4) hdvd 2)

theorem card_normalizer_blockGroup {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) :
    Nat.card (normalizer (blockGroup J : Set G)) =
      (block J).ncard * Nat.card (normalizer (J : Set G)) := by
  classical
  set H := normalizer (blockGroup J : Set G) with hHdef
  set N := (normalizer (J : Set G)).subgroupOf H with hNdef
  have hNH : normalizer (J : Set G) ≤ H := normalizer_le_normalizer_blockGroup hJ heven
    mem_block_self
  have hconj_eq : ∀ g₁ g₂ : G, conjSub g₁ J = conjSub g₂ J ↔ g₁⁻¹ * g₂ ∈ normalizer (J : Set G) := by
    intro g₁ g₂
    constructor
    · intro h
      have h1 : conjSub (g₁⁻¹ * g₂) J = J := by
        rw [conjSub_mul, ← h, conjSub_inv_conjSub]
      have h2 : conjSub (g₁⁻¹ * g₂)⁻¹ J = J := by
        calc conjSub (g₁⁻¹ * g₂)⁻¹ J = conjSub (g₁⁻¹ * g₂)⁻¹ (conjSub (g₁⁻¹ * g₂) J) := by
              rw [h1]
          _ = J := conjSub_inv_conjSub _ J
      exact mem_normalizer_of_conjSub_le (le_of_eq h1) (le_of_eq h2)
    · intro h
      have h1 := conjSub_eq_of_mem_normalizer h
      calc conjSub g₁ J = conjSub g₁ (conjSub (g₁⁻¹ * g₂) J) := by rw [h1]
        _ = conjSub g₂ J := by rw [← conjSub_mul, mul_inv_cancel_left]
  have hmemΔ : ∀ h : H, conjSub (h : G) J ∈ block J := fun h =>
    ((mem_normalizer_blockGroup_iff hq hJ heven h).1 h.2 J).1 mem_block_self
  let f : H ⧸ N → block J := Quotient.lift (fun h : H => ⟨conjSub (h : G) J, hmemΔ h⟩)
    (fun a b hab => by
      have h1 : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
      rw [hNdef, Subgroup.mem_subgroupOf] at h1
      exact Subtype.ext ((hconj_eq a b).2 (by simpa using h1)))
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      have h1 : conjSub (a : G) J = conjSub (b : G) J := congrArg Subtype.val hxy
      refine QuotientGroup.eq.2 ?_
      rw [hNdef, Subgroup.mem_subgroupOf]
      simpa using (hconj_eq a b).1 h1
    · rintro ⟨K, hK⟩
      obtain ⟨g, rfl⟩ := hK.1
      have hg : g ∈ H := mem_normalizer_blockGroup hJ heven mem_block_self hK
      exact ⟨QuotientGroup.mk ⟨g, hg⟩, rfl⟩
  have hidx : N.index = (block J).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr (Equiv.ofBijective f hf)]
    rfl
  rw [← Subgroup.card_mul_index N, hidx, mul_comm]
  congr 1
  exact Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv

omit [Finite G] in
theorem card_center_conjSub (g : G) (J : Subgroup G) :
    Nat.card (center (conjSub g J)) = Nat.card (center J) ∧
      Nat.card (conjSub g J ⧸ center (conjSub g J)) = Nat.card (J ⧸ center J) := by
  let e : J ≃* conjSub g J := J.equivMapOfInjective _ (MulAut.conj g).injective
  have hc := center_map_equiv e
  refine ⟨?_, ?_⟩
  · rw [← hc, Subgroup.card_map_of_injective e.injective]
  · exact (Nat.card_congr (QuotientGroup.congr _ _ e hc).toEquiv).symm

omit [Finite G] in
theorem ordProj_card_eq_center_mul [Finite G] (K : Subgroup G) :
    ordProj[2] (Nat.card K) =
      ordProj[2] (Nat.card (center K)) * ordProj[2] (Nat.card (K ⧸ center K)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center K), mul_comm,
    Nat.ordProj_mul 2 Nat.card_pos.ne' Nat.card_pos.ne']

theorem ordProj_card_centralizer_ge {J : Subgroup G} (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hn : 2 ≤ (block J).ncard) :
    ordProj[2] (Nat.card (center J)) * ordProj[2] (Nat.card (J ⧸ center J)) ^ ((block J).ncard - 1)
      ≤ ordProj[2] (Nat.card (centralizer (J : Set G))) := by
  classical
  set z := ordProj[2] (Nat.card (center J)) with hz
  set a := ordProj[2] (Nat.card (J ⧸ center J)) with ha
  have : Finite (Subgroup G) := Finite.of_injective (fun K : Subgroup G => (K : Set G))
    SetLike.coe_injective
  have hfin : (block J).Finite := Set.toFinite _
  have hzpos : 0 < z := Nat.ordProj_pos _ _
  have hKcard : ∀ K ∈ block J, ordProj[2] (Nat.card K) = z * a ∧
      Nat.card (center K) = Nat.card (center J) := by
    intro K hK
    obtain ⟨g, rfl⟩ := hK.1
    obtain ⟨h1, h2⟩ := card_center_conjSub g J
    refine ⟨?_, h1⟩
    rw [ordProj_card_eq_center_mul, h1, h2]
  have hcomm : ∀ K₁ ∈ block J, ∀ K₂ ∈ block J, K₁ ≠ K₂ → K₁ ≤ centralizer (K₂ : Set G) :=
    fun K₁ hK₁ K₂ hK₂ hne => commutator_eq_bot_iff_le_centralizer.1
      ((commRel_of_mem_block hJ heven hK₁ hK₂).resolve_left hne)
  obtain ⟨K₀, hK₀, hK₀J⟩ : ∃ K₀ ∈ block J, K₀ ≠ J := by
    by_contra h
    push Not at h
    have hsub : block J ⊆ {J} := fun K hK => h K hK
    have := Set.ncard_le_ncard hsub (Set.finite_singleton J)
    rw [Set.ncard_singleton] at this
    omega
  have claim : ∀ F : Finset (Subgroup G), (∀ K ∈ F, K ∈ block J ∧ K ≠ J ∧ K ≠ K₀) →
      z * a ^ (F.card + 1) ≤ ordProj[2] (Nat.card ↥(K₀ ⊔ sSup (F : Set (Subgroup G)))) ∧
        K₀ ⊔ sSup (F : Set (Subgroup G)) ≤ centralizer (J : Set G) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.coe_empty, sSup_empty, sup_bot_eq, Finset.card_empty, zero_add, pow_one,
        (hKcard K₀ hK₀).1]
      exact ⟨le_rfl, hcomm K₀ hK₀ J mem_block_self hK₀J⟩
    | @insert K F hKF ih =>
      intro hF
      obtain ⟨hKΔ, hKJ, hKK₀⟩ := hF K (Finset.mem_insert_self K F)
      obtain ⟨ih1, ih2⟩ := ih fun K' hK' => hF K' (Finset.mem_insert_of_mem hK')
      set P := K₀ ⊔ sSup (F : Set (Subgroup G)) with hPdef
      have hP' : K₀ ⊔ sSup ((insert K F : Finset (Subgroup G)) : Set (Subgroup G)) = P ⊔ K := by
        rw [Finset.coe_insert, sSup_insert, sup_comm K, ← sup_assoc]
      rw [hP', Finset.card_insert_of_notMem hKF]
      have hPK : P ≤ centralizer (K : Set G) := by
        refine sup_le (hcomm K₀ hK₀ K hKΔ (Ne.symm hKK₀)) (sSup_le fun K' hK' => ?_)
        have hK'F : K' ∈ F := hK'
        refine hcomm K' (hF K' (Finset.mem_insert_of_mem hK'F)).1 K hKΔ ?_
        rintro rfl
        exact hKF hK'F
      have hcommPK : ∀ x ∈ P, ∀ y ∈ K, x * y = y * x := fun x hx y hy =>
        (mem_centralizer_iff.1 (hPK hx) y hy).symm
      have hcard := card_sup_mul_card_inf_of_commute hcommPK
      have hcard2 : ordProj[2] (Nat.card ↥(P ⊔ K) * Nat.card ↥(P ⊓ K)) =
          ordProj[2] (Nat.card P * Nat.card K) := by rw [hcard]
      rw [Nat.ordProj_mul 2 Nat.card_pos.ne' Nat.card_pos.ne',
        Nat.ordProj_mul 2 Nat.card_pos.ne' Nat.card_pos.ne', (hKcard K hKΔ).1] at hcard2
      have hinf : Nat.card ↥(P ⊓ K) ∣ Nat.card (center J) := by
        rw [← (hKcard K hKΔ).2, ← Subgroup.card_map_of_injective K.subtype_injective]
        refine Subgroup.card_dvd_of_le fun x hx => ?_
        obtain ⟨hxP, hxK⟩ := mem_inf.1 hx
        refine ⟨⟨x, hxK⟩, mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
        exact mem_centralizer_iff.1 (hPK hxP) y y.2
      have hinf2 : ordProj[2] (Nat.card ↥(P ⊓ K)) ≤ z :=
        Nat.le_of_dvd hzpos (Nat.ordProj_dvd_ordProj_of_dvd Nat.card_pos.ne' hinf 2)
      refine ⟨?_, sup_le ih2 (hcomm K hKΔ J mem_block_self hKJ)⟩
      have h3 : z * (z * a ^ (F.card + 1 + 1)) ≤
          ordProj[2] (Nat.card ↥(P ⊔ K)) * ordProj[2] (Nat.card ↥(P ⊓ K)) :=
        calc z * (z * a ^ (F.card + 1 + 1)) = (z * a ^ (F.card + 1)) * (z * a) := by ring
          _ ≤ ordProj[2] (Nat.card P) * (z * a) := Nat.mul_le_mul_right _ ih1
          _ = _ := hcard2.symm
      have h4 : ordProj[2] (Nat.card ↥(P ⊔ K)) * ordProj[2] (Nat.card ↥(P ⊓ K)) ≤
          ordProj[2] (Nat.card ↥(P ⊔ K)) * z := Nat.mul_le_mul_left _ hinf2
      have h5 := h3.trans h4
      rw [mul_comm (ordProj[2] _) z] at h5
      exact Nat.le_of_mul_le_mul_left h5 hzpos
  set F := (hfin.toFinset.erase J).erase K₀ with hFdef
  have hFmem : ∀ K ∈ F, K ∈ block J ∧ K ≠ J ∧ K ≠ K₀ := by
    intro K hK
    rw [hFdef, Finset.mem_erase, Finset.mem_erase, Set.Finite.mem_toFinset] at hK
    exact ⟨hK.2.2, hK.2.1, hK.1⟩
  have hFcard : F.card + 1 = (block J).ncard - 1 := by
    have h1 : K₀ ∈ hfin.toFinset.erase J :=
      Finset.mem_erase.2 ⟨hK₀J, hfin.mem_toFinset.2 hK₀⟩
    rw [hFdef, Finset.card_erase_of_mem h1, Finset.card_erase_of_mem
      (hfin.mem_toFinset.2 mem_block_self), ← Set.ncard_eq_toFinset_card _ hfin]
    omega
  obtain ⟨h1, h2⟩ := claim F hFmem
  rw [hFcard] at h1
  exact h1.trans (Nat.le_of_dvd (Nat.ordProj_pos _ _)
    (Nat.ordProj_dvd_ordProj_of_dvd Nat.card_pos.ne' (Subgroup.card_dvd_of_le h2) 2))

omit [Finite G] in
theorem conjSub_eq_mulAut_smul (g : G) (K : Subgroup G) : conjSub g K = MulAut.conj g • K := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  rfl

omit [Finite G] in
theorem map_subtype_conjSub (H : Subgroup G) (h : H) (S : Subgroup H) :
    (conjSub h S).map H.subtype = conjSub (h : G) (S.map H.subtype) := by
  rw [conjSub, conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1

abbrev SylowControlled (H : Subgroup G) : Prop :=
  ∀ S : Sylow 2 H, (∃ P : Sylow 2 G, (P : Subgroup G) = (S : Subgroup H).map H.subtype) ∧
    normalizer (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) ≤ H

theorem sylowControlled_of_sq_gt {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J)
    (heven : Even (Nat.card J)) (hCeven : Even (Nat.card (centralizer (J : Set G))))
    (hJ : IsUniversalComponent J)
    (hc : ordProj[2] (Nat.card (normalizer (blockGroup J : Set G))) <
      ordProj[2] (Nat.card (centralizer (J : Set G))) ^ 2) :
    SylowControlled (normalizer (blockGroup J : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (blockGroup J : Set G) with hHdef
  set C := centralizer (J : Set G) with hCdef
  have hCH : C ≤ H := (centralizer_le_normalizer _).trans
    (normalizer_le_normalizer_blockGroup hJ heven mem_block_self)
  obtain ⟨Q⟩ : Nonempty (Sylow 2 C) := inferInstance
  set QG := (Q : Subgroup C).map C.subtype with hQGdef
  have hQcard : Nat.card QG = ordProj[2] (Nat.card C) := by
    rw [hQGdef, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
  have hQ2 : IsPGroup 2 QG := Q.isPGroup'.map _
  have hQC : QG ≤ C := Subgroup.map_subtype_le _
  have hQH : QG ≤ H := hQC.trans hCH
  obtain ⟨S₀, hS₀⟩ := (hQ2.comap_of_injective H.subtype H.subtype_injective).exists_le_sylow
  set S₀G := (S₀ : Subgroup H).map H.subtype with hS₀Gdef
  have hQS₀ : QG ≤ S₀G := fun x hx =>
    ⟨⟨x, hQH hx⟩, hS₀ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hS₀card : Nat.card S₀G = ordProj[2] (Nat.card H) := by
    rw [hS₀Gdef, Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity]
  have hS₀2 : IsPGroup 2 S₀G := S₀.isPGroup'.map _
  have hS₀H : S₀G ≤ H := Subgroup.map_subtype_le _
  have hnorm₀ : normalizer (S₀G : Set G) ≤ H := by
    intro g hg
    by_contra hgH
    have hodd := (commuting_block_two_subgroup_normalizer_control hq heven hCeven hJ).2.1 g hgH
    set Qg := CFSG.conjugate QG g with hQgdef
    have hQgS : Qg ≤ S₀G := by
      rintro _ ⟨q, hq', rfl⟩
      have := (mem_normalizer_iff.1 (inv_mem hg) q).1 (hQS₀ hq')
      simpa using this
    have hQgcard : Nat.card Qg = Nat.card QG :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    let f : QG × Qg → S₀G := fun p => ⟨p.1 * p.2, mul_mem (hQS₀ p.1.2) (hQgS p.2.2)⟩
    have hcard : Nat.card S₀G < Nat.card (QG × Qg) := by
      rw [Nat.card_prod, hQgcard, hQcard, hS₀card, ← sq]
      exact hc
    have hninj : ¬ Function.Injective f := fun hf =>
      absurd (Nat.card_le_card_of_injective f hf) (not_le.2 hcard)
    rw [Function.Injective] at hninj
    push Not at hninj
    obtain ⟨p, p', heq, hne⟩ := hninj
    have heq' : (p.1 : G) * p.2 = p'.1 * p'.2 := congrArg Subtype.val heq
    set w := (p'.1 : G)⁻¹ * p.1 with hwdef
    have hw2 : w = p'.2 * (p.2 : G)⁻¹ := by
      rw [hwdef, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq', mul_inv_cancel_right]
    have hwQ : w ∈ QG := mul_mem (inv_mem p'.1.2) p.1.2
    have hwQg : w ∈ Qg := by rw [hw2]; exact mul_mem p'.2.2 (inv_mem p.2.2)
    have hw1 : w ≠ 1 := by
      intro h
      apply hne
      have h1 : (p.1 : G) = p'.1 := by
        rw [hwdef, inv_mul_eq_one] at h
        exact h.symm
      have h2 : (p.2 : G) = p'.2 := by
        rw [hw2, mul_inv_eq_one] at h
        exact h.symm
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    have hwC : w ∈ C ⊓ CFSG.conjugate C g := mem_inf.2 ⟨hQC hwQ, map_mono hQC hwQg⟩
    obtain ⟨k, hk⟩ := hQ2 ⟨w, hwQ⟩
    have hwk : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hwk)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hw1 (orderOf_eq_one_iff.1 (by rw [hm, pow_zero]))
    have h2dvd : 2 ∣ Nat.card ↥(C ⊓ CFSG.conjugate C g) := by
      have := orderOf_dvd_natCard (⟨w, hwC⟩ : ↥(C ⊓ CFSG.conjugate C g))
      rw [Subgroup.orderOf_mk, hm] at this
      exact (dvd_pow_self 2 hm0).trans this
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2dvd)
  obtain ⟨P, hP⟩ := hS₀2.exists_le_sylow
  have hS₀P : S₀G = P := by
    by_contra hne
    have hlt : S₀G.subgroupOf P < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => hne (le_antisymm hP fun x hx => ?_)
      have : (⟨x, hx⟩ : P) ∈ S₀G.subgroupOf P := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    have : Group.IsNilpotent P := P.isPGroup'.isNilpotent
    obtain ⟨p, hpN, hpS⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hpG : (p : G) ∈ normalizer (S₀G : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      have key : ∀ y : P, (y : G) ∈ S₀G ↔ ((p * y * p⁻¹ : P) : G) ∈ S₀G := fun y => by
        have h1 := (mem_normalizer_iff.1 hpN) y
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h1
        exact h1
      constructor
      · intro hx
        exact (key ⟨x, hP hx⟩).1 hx
      · intro hx
        have hxP : x ∈ (P : Subgroup G) := by
          have h1 := (P : Subgroup G).mul_mem
            ((P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem p.2) (hP hx)) p.2
          simpa [mul_assoc] using h1
        exact (key ⟨x, hxP⟩).2 hx
    have hY2 : IsPGroup 2 (((P : Subgroup G) ⊓ normalizer (S₀G : Set G)).subgroupOf H) :=
      (P.isPGroup'.to_le inf_le_left).comap_of_injective H.subtype H.subtype_injective
    have hS₀Y : (S₀ : Subgroup H) ≤ ((P : Subgroup G) ⊓ normalizer (S₀G : Set G)).subgroupOf H :=
      fun s hs => Subgroup.mem_subgroupOf.2 (mem_inf.2 ⟨hP ⟨s, hs, rfl⟩, le_normalizer ⟨s, hs, rfl⟩⟩)
    have hYeq := S₀.is_maximal' hY2 hS₀Y
    have hpY : (⟨p, hnorm₀ hpG⟩ : H) ∈
        ((P : Subgroup G) ⊓ normalizer (S₀G : Set G)).subgroupOf H :=
      Subgroup.mem_subgroupOf.2 (mem_inf.2 ⟨p.2, hpG⟩)
    rw [hYeq] at hpY
    exact hpS (Subgroup.mem_subgroupOf.2 ⟨_, hpY, rfl⟩)
  intro S
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq H S₀ S
  have hSG : ((h • S₀ : Sylow 2 H) : Subgroup H).map H.subtype = conjSub (h : G) S₀G := by
    rw [Sylow.coe_subgroup_smul, ← conjSub_eq_mulAut_smul, map_subtype_conjSub]
  rw [hSG]
  refine ⟨⟨(h : G) • P, ?_⟩, ?_⟩
  · rw [Sylow.coe_subgroup_smul, ← conjSub_eq_mulAut_smul, ← hS₀P]
  · rw [show conjSub (h : G) S₀G = S₀G.map (MulAut.conj (h : G)).toMonoidHom from rfl,
      ← map_equiv_normalizer_eq]
    calc (normalizer (S₀G : Set G)).map (MulAut.conj (h : G)).toMonoidHom ≤ conjSub (h : G) H :=
          map_mono hnorm₀
      _ = H := conjSub_eq_of_mem_normalizer (le_normalizer h.2)

theorem ordProj_two_le_four_pow {n : ℕ} (hn : 3 ≤ n) : ordProj[2] n ≤ 4 ^ (n - 3) := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn4
  · rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  · have hle : n ≤ 4 ^ (n - 3) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      rw [show k + 4 - 3 = k + 1 by omega]
      induction k with
      | zero => norm_num
      | succ k ih =>
        rw [pow_succ]
        have := ih (by omega) (by omega)
        omega
    exact (Nat.ordProj_le 2 (by omega)).trans hle

theorem commuting_block_Sylow_order_criterion {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hCeven : Even (Nat.card (centralizer (J : Set G)))) (hJ : IsUniversalComponent J)
    (hn : 2 ≤ (block J).ncard) :
    let H := normalizer (blockGroup J : Set G)
    let n := (block J).ncard
    let c := ordProj[2] (Nat.card (centralizer (J : Set G)))
    let a := ordProj[2] (Nat.card (J ⧸ center J))
    let z := ordProj[2] (Nat.card (center J))
    let o := ordProj[2] (Nat.card (Outer (J ⧸ center J)))
    (∀ g ∈ H, ∀ K ∈ block J, CFSG.conjugate K g ∈ block J) ∧
      (∀ K₁ ∈ block J, ∀ K₂ ∈ block J, ∃ g ∈ H, CFSG.conjugate K₁ g = K₂) ∧
      ordProj[2] (Nat.card H) ≤ ordProj[2] n * c * a * o ∧
      z * a ^ (n - 1) ≤ c ∧
      (ordProj[2] (Nat.card H) < c ^ 2 → SylowControlled H) ∧
      (ordProj[2] n * a * o < c → SylowControlled H) ∧
      (ordProj[2] n * o < z * a ^ (n - 2) → SylowControlled H) ∧
      (3 ≤ n → 4 ≤ a → o < a → SylowControlled H) := by
  intro H n c a z o
  have hconj : ∀ (K : Subgroup G) (g : G), CFSG.conjugate K g = conjSub g⁻¹ K := fun _ _ => rfl
  have hpres : ∀ g ∈ H, ∀ K ∈ block J, CFSG.conjugate K g ∈ block J := fun g hg K hK => by
    rw [hconj]
    exact ((mem_normalizer_blockGroup_iff hq hJ heven g⁻¹).1 (inv_mem hg) K).1 hK
  have htrans : ∀ K₁ ∈ block J, ∀ K₂ ∈ block J, ∃ g ∈ H, CFSG.conjugate K₁ g = K₂ := by
    intro K₁ hK₁ K₂ hK₂
    obtain ⟨g₁, rfl⟩ := hK₁.1
    obtain ⟨g₂, rfl⟩ := hK₂.1
    have hg₁ : g₁ ∈ H := mem_normalizer_blockGroup hJ heven mem_block_self hK₁
    have hg₂ : g₂ ∈ H := mem_normalizer_blockGroup hJ heven mem_block_self hK₂
    refine ⟨g₁ * g₂⁻¹, mul_mem hg₁ (inv_mem hg₂), ?_⟩
    rw [hconj, ← conjSub_mul, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  have hn0 : n ≠ 0 := by omega
  have hHle : ordProj[2] (Nat.card H) ≤ ordProj[2] n * c * a * o := by
    have h1 := card_normalizer_blockGroup hq hJ heven
    have h2 := ordProj_card_normalizer_le hq
    change Nat.card H = n * Nat.card (normalizer (J : Set G)) at h1
    rw [h1, Nat.ordProj_mul 2 hn0 Nat.card_pos.ne', mul_assoc, mul_assoc]
    rw [mul_assoc] at h2
    exact Nat.mul_le_mul_left _ h2
  have hcge : z * a ^ (n - 1) ≤ c := ordProj_card_centralizer_ge heven hJ hn
  have hsq : ordProj[2] (Nat.card H) < c ^ 2 → SylowControlled H :=
    sylowControlled_of_sq_gt hq heven hCeven hJ
  have hcpos : 0 < c := Nat.ordProj_pos _ _
  have hapos : 0 < a := Nat.ordProj_pos _ _
  have hzpos : 0 < z := Nat.ordProj_pos _ _
  have hn2pos : 0 < ordProj[2] n := Nat.ordProj_pos _ _
  have h5a : ordProj[2] n * a * o < c → SylowControlled H := fun h => hsq (by
    calc ordProj[2] (Nat.card H) ≤ ordProj[2] n * c * a * o := hHle
      _ = c * (ordProj[2] n * a * o) := by ring
      _ < c * c := Nat.mul_lt_mul_of_pos_left h hcpos
      _ = c ^ 2 := (sq c).symm)
  have h5b : ordProj[2] n * o < z * a ^ (n - 2) → SylowControlled H := fun h => h5a (by
    have hpow : a ^ (n - 1) = a ^ (n - 2) * a := by
      rw [← pow_succ]
      congr 1
      omega
    calc ordProj[2] n * a * o = ordProj[2] n * o * a := by ring
      _ < z * a ^ (n - 2) * a := Nat.mul_lt_mul_of_pos_right h hapos
      _ = z * a ^ (n - 1) := by rw [hpow, mul_assoc]
      _ ≤ c := hcge)
  refine ⟨hpres, htrans, hHle, hcge, hsq, h5a, h5b, fun hn3 ha4 hoa => h5b ?_⟩
  have hpow : a ^ (n - 2) = a * a ^ (n - 3) := by
    rw [← pow_succ']
    congr 1
    omega
  have h4 : ordProj[2] n ≤ a ^ (n - 3) :=
    (ordProj_two_le_four_pow hn3).trans (Nat.pow_le_pow_left ha4 _)
  calc ordProj[2] n * o < ordProj[2] n * a := Nat.mul_lt_mul_of_pos_left hoa hn2pos
    _ ≤ a ^ (n - 3) * a := Nat.mul_le_mul_right _ h4
    _ = a ^ (n - 2) := by rw [hpow, mul_comm]
    _ ≤ z * a ^ (n - 2) := Nat.le_mul_of_pos_left _ hzpos

end CFSG.LocalAnalysis.ComponentInitial
