module

public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents
import CFSG.LocalAnalysis.AGLEmbedding.OneLieBender

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Abstract

variable {Y : Type*} [Group Y]

private theorem eq_bot_of_commutator_eq_of_isSolvable {J : Subgroup Y} (hJ : ⁅J, J⁆ = J)
    (hs : Group.IsSolvable J) : J = ⊥ := by
  have : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJ
  obtain ⟨n, hn⟩ := hs.solvable
  rw [Group.IsPerfect.derivedSeries_eq_top] at hn
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : J) ∈ (⊤ : Subgroup J) := Subgroup.mem_top _
  rw [hn, Subgroup.mem_bot] at h1
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)

theorem le_centralizer_of_perfect_of_isCyclic {O J : Subgroup Y} [O.Normal] (hO : IsCyclic O)
    (hJ : ⁅J, J⁆ = J) : J ≤ Subgroup.centralizer (O : Set Y) := by
  rw [← hJ, Subgroup.commutator_le]
  intro a _ b _
  have hcomm : ∀ f g : MulAut O, f * g = g * f := by
    intro f g
    apply (IsCyclic.mulAutMulEquiv (G := O)).injective
    rw [map_mul, map_mul, mul_comm]
  have h1 : MulAut.conjNormal (H := O) ⁅a, b⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      hcomm (MulAut.conjNormal a) (MulAut.conjNormal b)]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  have h2 := congrArg (fun f : MulAut O => ((f ⟨o, ho⟩ : O) : Y)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc o * ⁅a, b⁆ = ⁅a, b⁆ * o * ⁅a, b⁆⁻¹ * ⁅a, b⁆ := by rw [h2]
    _ = ⁅a, b⁆ * o := by group

end Abstract

section Reduced

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.eq_bot_of_le_centralizer_of_perfect
    (h : ReducedNongeneration p Y Rb Y₀) {K : Subgroup Y} [K.Normal] (hK : IsComponentOf K ⊤)
    (hKY₀ : ¬ K ≤ Y₀) (hI : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) {J : Subgroup Y}
    (hJC : J ≤ Subgroup.centralizer (K : Set Y)) (hJ : ⁅J, J⁆ = J) : J = ⊥ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer (K : Set Y)
  have hcomp : ∀ L : Subgroup C, ¬ IsComponentOf L ⊤ := by
    intro L hL
    have hL' := ComponentClassification.LocalComponents.of_subnormal_subgroup C
      (ComponentClassification.Components.chain_of_mathlib_subnormal
        (inferInstance : C.Normal).isSubnormal) L hL
    have hLK := hI _ hL'
    have hKC : K ≤ C := hLK ▸ Subgroup.map_subtype_le L
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
    apply hab
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKC b.2) a a.2)
  have hB := centralizer_pCore_le_pCore_of_forall (p := p) hcomp
    fun q hq hqp => h.pCore_eq_bot_of_ne C hq hqp
  have hOp : IsPGroup p (CFSG.pCore p C) := CFSG.pCore_isPGroup
  have hOc : IsCyclic (CFSG.pCore p C) := by
    have := h.isCyclic_of_le_centralizer hK hKY₀ (hOp.map C.subtype)
      (Subgroup.map_subtype_le (CFSG.pCore p C))
    exact isCyclic_of_surjective ((CFSG.pCore p C).equivMapOfInjective C.subtype
      C.subtype_injective).symm.toMonoidHom (MulEquiv.surjective _)
  set J' : Subgroup C := J.subgroupOf C
  have hJ' : ⁅J', J'⁆ = J' := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJC, hJ]
  have hJO : J' ≤ CFSG.pCore p C :=
    (le_centralizer_of_perfect_of_isCyclic hOc hJ').trans hB
  have hJ'p : IsPGroup p J' := hOp.to_le hJO
  have : Group.IsNilpotent J' := hJ'p.isNilpotent
  have : Group.IsSolvable J' := inferInstance
  have hJ'b := eq_bot_of_commutator_eq_of_isSolvable hJ' this
  rw [← Subgroup.map_subgroupOf_eq_of_le hJC]
  change J'.map C.subtype = ⊥
  rw [hJ'b, Subgroup.map_bot]

end Reduced

section OneLie

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.coprime_card_of_perfect (hK : KFactOneLie) (hΓ : KFactOneLieBorelSolvable)
    (hd : D1OneLieData p P M H R Rbar K)
    (hI : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    {U : Subgroup G} (hU : U ≤ H ⊓ M) (hUp : ⁅U, U⁆ = U) : p.Coprime (Nat.card U) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set X₀ := ((H ⊓ M).subgroupOf H).map π
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  obtain ⟨hsimple, hnonab⟩ := hd.isSimpleGroup
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hd.center).trans QuotientGroup.quotientBot).symm
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hd.cfg.catalog.isCatalogGroup_center_quotient hd.comp)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hd.comp.2.1
      Subgroup.IsSubnormal.top)
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hc => hd.noncyclic (by
    rw [← hT]
    exact isCyclic_of_surjective _ (K.subtype.subgroupMap_surjective (T : Subgroup K)))
  have hne := hd.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT
  have hF := hK K hsimple hnonab hcat p hp hd.cfg.red.ne_two T hTnc hne hd.big
  have hs := hΓ K hsimple hnonab hcat p hp hd.cfg.red.ne_two T hTnc hne hd.big
  have hΓX : (GLBCore p 1 (T : Subgroup K)).map K.subtype ≤ X₀ :=
    glbCore_map_le_of_normalizer_le hp hT hN
  have hcomap : X₀.comap K.subtype = GLBCore p 1 (T : Subgroup K) := by
    rcases (hF.uPrime T hne).1 (X₀.comap K.subtype) (Subgroup.map_le_iff_le_comap.mp hΓX) with
      h | h
    · exact h
    · exact absurd (fun k hk => (Subgroup.mem_comap.mp (h.ge (Subgroup.mem_top ⟨k, hk⟩)) :)) hKX₀
  have hKX : K ⊓ X₀ = (GLBCore p 1 (T : Subgroup K)).map K.subtype := by
    rw [← hcomap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  have hKXs : Group.IsSolvable (K ⊓ X₀ : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hKX]
    exact Group.isSolvable_of_surjective (f := ((GLBCore p 1 (T : Subgroup K)).equivMapOfInjective
      K.subtype K.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  set Ub := (U.subgroupOf H).map π
  have hUH : U ≤ H := hU.trans inf_le_left
  have hUb : ⁅Ub, Ub⁆ = Ub := by
    have h1 : ⁅U.subgroupOf H, U.subgroupOf H⁆ = U.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUH, hUp]
    rw [← Subgroup.map_commutator, h1]
  have hUbX : Ub ≤ X₀ := Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.mpr
    (hU (Subgroup.mem_subgroupOf.mp hu))
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  have hUbKC : Ub ≤ K ⊔ C :=
    le_sup_centralizer_of_isPerfect (Subgroup.isPerfect_iff.mpr hUb) hF.outer_solvable
  have hCX : C ≤ X₀ := hd.cfg.red.centralizer_le_of_rankOne hd.noncyclic hzR hzK hzp hzc
  have hCn : C.Normal := Subgroup.normal_centralizer
  set φ := QuotientGroup.mk' C
  have hφ : Ub.map φ ≤ (K ⊓ X₀).map φ := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨k, hk, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hUbKC hu)
    have hkX : k ∈ X₀ := by
      have := X₀.mul_mem (hUbX hu) (X₀.inv_mem (hCX hc))
      simpa using this
    refine ⟨k, ⟨hk, hkX⟩, ?_⟩
    have hc1 : φ c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    change φ k = φ (k * c)
    rw [map_mul, hc1, mul_one]
  have hsolφ : Group.IsSolvable ((K ⊓ X₀).map φ) :=
    Group.isSolvable_of_surjective (φ.subgroupMap_surjective (K ⊓ X₀))
  have hsolU : Group.IsSolvable (Ub.map φ) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hφ)
  have hUbφ : Ub.map φ = ⊥ := eq_bot_of_commutator_eq_of_isSolvable
    (by rw [← Subgroup.map_commutator, hUb]) hsolU
  have hUbC : Ub ≤ C := by
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hUbφ
  have hUb1 : Ub = ⊥ := hd.cfg.red.eq_bot_of_le_centralizer_of_perfect hd.comp hKX₀ hI hUbC hUb
  have hUN : U ≤ GLBPrimeCore p H := by
    intro u hu
    have h1 : π ⟨u, hUH hu⟩ ∈ Ub := ⟨⟨u, hUH hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hUb1, Subgroup.mem_bot] at h1
    exact (mk'_primeComplementCore_eq_one_iff p _).mp h1
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hUN) (glbPrimeCore_coprime p H)

end OneLie

end CFSG.AGLEmbedding
