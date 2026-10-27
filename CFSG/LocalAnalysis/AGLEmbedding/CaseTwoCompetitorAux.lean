module

import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefsAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.LocalAnalysis.ComponentInitial.PerfectNormalizerLayer
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

section Perfect

variable {Y : Type*} [Group Y]

theorem le_centralizer_of_isPerfect_of_isCyclic {A C : Subgroup Y} [C.Normal]
    (hA : Group.IsPerfect A) (hC : IsCyclic C) : A ≤ Subgroup.centralizer (C : Set Y) := by
  have hcomm : IsMulCommutative (MulAut C) :=
    ⟨⟨fun a b => (IsCyclic.mulAutMulEquiv C).injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  let f : A →* MulAut C := (MulAut.conjNormal (H := C)).comp A.subtype
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  intro a ha
  have h1 : f ⟨a, ha⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨f ⟨a, ha⟩, ⟨_, rfl⟩⟩ : f.range) 1)
  rw [← ker_conjNormal_eq_centralizer]
  exact h1

end Perfect

@[expose] def KFactCaseTwoInvOn (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ K : Subgroup Y, IsComponentOf K ⊤ → Subgroup.center K = ⊥ → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → ∀ p : ℕ, (p = 3 ∨ p = 5) →
      ∀ T : Sylow p K, ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup K) ≤ 2 →
      ∀ (A : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup p L →
        ∀ f : A →* L, ¬ Function.Surjective f

theorem KFactCaseTwoInvIn.on {G : Type} [Group G] [Finite G] (h : KFactCaseTwoInvIn G)
    {H : Subgroup G} {N : Subgroup H} [N.Normal] : KFactCaseTwoInvOn (H ⧸ N) :=
  fun K hK hZ hs hn hc p hp T hT hΓ hr A L _ hL f =>
    h H N K hK.2.2 hZ hs hn hc p hp T hT hΓ hr A L hL f

section Reduced

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.conj_mem_normalizer_component (h : ReducedNongeneration p Y Rb Y₀)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) {x : Y} (hx : x ∈ (Rb : Subgroup Y)) (c : Y) :
    c * x * c⁻¹ ∈ Subgroup.normalizer (L : Set Y) :=
  Subgroup.normalCore_le _ ((Subgroup.normalCore_normal _).conj_mem x
    (h.sylow_le_normalCore_normalizer_component hL hx) c)

theorem ReducedNongeneration.le_layer_of_isPerfect (h : ReducedNongeneration p Y Rb Y₀)
    (hX : CatalogSimpleSections Y) (hSch : KFactCatalogSchreier) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) {A : Subgroup Y} (hA : Group.IsPerfect A)
    (hN : ∀ L : Subgroup Y, IsComponentOf L ⊤ → A ≤ Subgroup.normalizer (L : Set Y)) :
    A ≤ CFSG.layer Y := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : CFSG.fittingSubgroup Y = CFSG.pCore p Y := CFSG.Fitting_eq_pcore Y p h.core_eq_bot
  have : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  refine CFSG.LocalAnalysis.ComponentInitial.unique_perfect_component_normalizer_enters_layer hA
    ?_ (fun L hL => hN L ((CFSG.isComponent_iff_open L).mp hL)) fun L hL => ?_
  · rw [hF]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_of_isPerfect_of_isCyclic hA (h.isCyclic_pCore_of_component hK))
  · have hL' := (CFSG.isComponent_iff_open L).mp hL
    have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL'.2.2.2
    exact hSch _ inferInstance
      (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hL'.2.2)
      (hX.isCatalogGroup_center_quotient hL')

theorem ReducedNongeneration.pRank_top_le_two_of_mem_centralizer
    (h : ReducedNongeneration p Y Rb Y₀) (h3 : Open.pRank p (Rb : Subgroup Y) ≤ 3)
    {K : Subgroup Y} {T : Sylow p K} (hT : (T : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K)
    {z : Y} (hzR : z ∈ (Rb : Subgroup Y)) (hzK : z ∉ K) (hzp : orderOf z = p)
    (hzc : z ∈ Subgroup.centralizer (K : Set Y)) :
    Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have e1 := (CFSG.SectionRank.pRank_sylow T).1
  have e2 := pRank_map_of_injective p hp K.subtype K.subtype_injective (T : Subgroup K)
  rw [hT] at e2
  obtain ⟨E, hE, hEel, hEcard⟩ := pRank_attained p hp ((Rb : Subgroup Y) ⊓ K)
  have h4 := succ_le_pRank_of_isElemAbelian_of_mem_centralizer hp hEel hEcard
    (hzp ▸ pow_orderOf_eq_one z) (fun hzE => hzK (hE hzE).2)
    (Subgroup.centralizer_le (hE.trans inf_le_right) hzc) (hE.trans inf_le_left) hzR
  omega

theorem ReducedNongeneration.false_of_surjective_of_rankOne_at
    (h : ReducedNongeneration p Y Rb Y₀) (hX : CatalogSimpleSections Y)
    (hInv : KFactCaseTwoInvOn Y)
    (hSch : KFactCatalogSchreier)
    (h3 : Open.pRank p (Rb : Subgroup Y) ≤ 3) {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y))
    (hz : ∃ z ∈ (Rb : Subgroup Y), z ∉ K ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (K : Set Y))
    {L : Type} [Group L] (hL : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a)
    (hiso : IsCaseTwoGroup p L) {Jt : Subgroup Y} (φ : Jt →* L) (hφ : Function.Surjective φ)
    (hY₀ : (Y₀.subgroupOf Jt).map φ ≠ ⊤) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
  have hKn : K.Normal := h.normal_of_rankOne hK hnc
  have hZ := h.center_eq_bot_of_rankOne hK hnc hzR hzK hzp hzc
  obtain ⟨hNU, hKY₀⟩ := h.rankOne_principle hK hnc hzR hzK hzp hzc
  obtain ⟨hKs, hKnab, hKcat⟩ := hX.isSimpleGroup_of_center_eq_bot hK hZ
  have hout : Group.IsSolvable (Outer K) := hSch K hKs hKnab hKcat
  let θ : Jt →* MulAut K := (MulAut.conjNormal (H := K)).comp Jt.subtype
  have hθφ : θ.ker ≤ φ.ker := by
    have : (θ.ker.map φ).Normal := (MonoidHom.normal_ker θ).map φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (θ.ker.map φ) with hbot | htop
    · exact (Subgroup.map_eq_bot_iff _).mp hbot
    · refine absurd (eq_top_iff.mpr (htop.symm.le.trans (Subgroup.map_mono fun j hj => ?_))) hY₀
      have hjC : (j : Y) ∈ Subgroup.centralizer (K : Set Y) := by
        rw [← ker_conjNormal_eq_centralizer]
        exact hj
      exact h.centralizer_le_of_rankOne hnc hzR hzK hzp hzc hjC
  obtain ⟨φ₁, hφ₁, hφ₁s, -⟩ := exists_surjective_comp_eq θ.rangeRestrict
    θ.rangeRestrict_surjective φ hφ (by rw [MonoidHom.ker_rangeRestrict]; exact hθφ)
  have hIn : (((inner K).subgroupOf θ.range).map φ₁).Normal :=
    (Subgroup.normal_subgroupOf).map φ₁ hφ₁s
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((inner K).subgroupOf θ.range).map φ₁) with
    hbot | htop
  ·
    let ψ : θ.range →* Outer K := (QuotientGroup.mk' (inner K)).comp θ.range.subtype
    have hψ : ψ.ker ≤ φ₁.ker := by
      intro b hb
      have hbI : (b : MulAut K) ∈ inner K := (QuotientGroup.eq_one_iff _).mp hb
      exact (Subgroup.map_eq_bot_iff _).mp hbot hbI
    obtain ⟨φ₂, -, hφ₂s, -⟩ := exists_surjective_comp_eq ψ.rangeRestrict
      ψ.rangeRestrict_surjective φ₁ hφ₁s (by rw [MonoidHom.ker_rangeRestrict]; exact hψ)
    have : Group.IsSolvable L := Group.isSolvable_of_surjective hφ₂s
    obtain ⟨a, b, hab⟩ := hLnab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)
  let A : Subgroup K := θ.range.comap (MulAut.conj : K →* MulAut K)
  let ι : A →* θ.range :=
    MonoidHom.codRestrict ((MulAut.conj : K →* MulAut K).comp A.subtype) θ.range fun a => a.2
  have hsurj : Function.Surjective (φ₁.comp ι) := by
    intro l
    obtain ⟨b, ⟨k, hk⟩, hbl⟩ : l ∈ ((inner K).subgroupOf θ.range).map φ₁ :=
      htop ▸ Subgroup.mem_top l
    refine ⟨⟨k, show MulAut.conj k ∈ θ.range from hk ▸ b.2⟩, ?_⟩
    rw [← hbl, MonoidHom.comp_apply]
    exact congrArg φ₁ (Subtype.ext hk)
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hp35 : p = 3 ∨ p = 5 := by
    obtain ⟨d, hd | hd, -⟩ := hiso
    · exact Or.inl hd.1
    · exact Or.inr hd.1
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hc => hnc (by
    rw [← hT]
    exact isCyclic_of_surjective _ ((T : Subgroup K).equivMapOfInjective K.subtype
      K.subtype_injective).surjective)
  exact hInv K hK hZ hKs hKnab hKcat p hp35 T hTnc (h.glbCore_ne_top_of_rankOne hNU hKY₀ hT)
    (h.pRank_top_le_two_of_mem_centralizer h3 hT hzR hzK hzp hzc) A L hiso (φ₁.comp ι) hsurj

end Reduced

section Competitor

open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem exists_competitor_surj_of (hp : p.Prime) {Y : Subgroup G}
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hLJ : L ≤ ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    {H' : Subgroup G} (hcore : GLBPrimeCore p H' ≤ M) (hJH' : nclIn H Y ≤ H') :
    ∃ (Jt : Subgroup (H' ⧸ primeComplementCore (G := H') p)) (φ : Jt →* L),
      Function.Surjective φ ∧
        ((((H' ⊓ M).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p))
          ).subgroupOf Jt).map φ ≠ ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set π' := QuotientGroup.mk' (primeComplementCore (G := H') p)
  set J := nclIn H Y
  have hJH : J ≤ H := nclIn_le_self _ _
  set J₁ : Subgroup G := J ⊓ (L.comap π).map H.subtype
  let θ₀ : J₁.subgroupOf H' →* H :=
    MonoidHom.codRestrict (H'.subtype.comp (J₁.subgroupOf H').subtype) H fun a => hJH a.2.1
  have hθ₀L : ∀ a, π (θ₀ a) ∈ L := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hx, hxa⟩ := ha.2
    have hθ : θ₀ ⟨a, ha⟩ = x := Subtype.ext hxa.symm
    rw [hθ]
    exact hx
  let ψ : J₁.subgroupOf H' →* L := (π.comp θ₀).codRestrict L hθ₀L
  have hψs : Function.Surjective ψ := by
    intro l
    obtain ⟨j, hj, hjl⟩ := hLJ l.2
    exact ⟨⟨⟨j, hJH' hj⟩, hj, j, show π j ∈ L from hjl ▸ l.2, rfl⟩, Subtype.ext hjl⟩
  set ρ := π'.subgroupMap (J₁.subgroupOf H')
  have hker : ρ.ker ≤ ψ.ker := by
    intro a ha
    have ha' : ((a : H') : G) ∈ GLBPrimeCore p H' := by
      rw [← mk'_primeComplementCore_eq_one_iff]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    have hN := inf_glbPrimeCore_le_glbPrimeCore p hJH' ⟨a.2.1, ha'⟩
    rw [glbPrimeCore_nclIn] at hN
    rw [MonoidHom.mem_ker, ← OneMemClass.coe_eq_one, MonoidHom.codRestrict_apply]
    exact (mk'_primeComplementCore_eq_one_iff p (θ₀ a)).mpr hN.2
  obtain ⟨φ, hφρ, hφs, -⟩ :=
    exists_surjective_comp_eq ρ (π'.subgroupMap_surjective _) ψ hψs hker
  refine ⟨(J₁.subgroupOf H').map π', φ, hφs, ?_⟩
  intro htop
  refine hLX₀ fun l hl => ?_
  obtain ⟨j, hj, hjl⟩ : (⟨l, hl⟩ : L) ∈ ((((H' ⊓ M).subgroupOf H').map π').subgroupOf
      ((J₁.subgroupOf H').map π')).map φ := htop ▸ Subgroup.mem_top _
  obtain ⟨a, rfl⟩ := π'.subgroupMap_surjective _ j
  obtain ⟨m, hm, hma⟩ := hj
  have hmN : (((m⁻¹ * a : H') : H') : G) ∈ GLBPrimeCore p H' := by
    rw [← mk'_primeComplementCore_eq_one_iff, map_mul, map_inv, hma]
    exact inv_mul_cancel _
  have haM : ((a : H') : G) ∈ M := by
    have e : ((a : H') : G) = (m : G) * ((m⁻¹ * a : H') : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [e]
    exact M.mul_mem hm.2 (hcore hmN)
  rw [hφρ] at hjl
  exact ⟨θ₀ a, ⟨(θ₀ a).2, haM⟩, congrArg Subtype.val hjl⟩

theorem D1CaseTwoDataAt.false_of_rankOne_competitor_of (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoDataAt p P M H R Rbar)
    {Y : Subgroup G} {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤) (hLX₀ : ¬ L ≤ d1X0 p M H)
    (hLJ : L ≤ ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    {H' : Subgroup G} {Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p)}
    (hcfg' : D1ComponentConfigU p P M H' R Rbar') (hJH' : nclIn H Y ≤ H')
    {K' : Subgroup (H' ⧸ primeComplementCore (G := H') p)} (hK' : IsComponentOf K' ⊤)
    (hnc' : ¬ IsCyclic ((Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) ⊓ K' :
      Subgroup (H' ⧸ primeComplementCore (G := H') p)))
    (hz' : ∃ z ∈ (Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)), z ∉ K' ∧
      orderOf z = p ∧ z ∈ Subgroup.centralizer (K' : Set (H' ⧸ primeComplementCore (G := H') p))) :
    False := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hiso := hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
      hd.cfg.catalog)
    hS hd.cyclic hd.rank hL hLX₀
  obtain ⟨hLs, hLnab, -⟩ :=
    hd.cfg.red.isSimpleGroup_of_isCyclic hd.cfg.catalog hL (hd.cyclic L hL)
  have h3' : Open.pRank p (Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) ≤ 3 := by
    have e := hd.rank
    rw [hd.cfg.rbar, pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
      Subgroup.map_subgroupOf_eq_of_le hd.cfg.ext.le_H] at e
    rw [hcfg'.rbar, pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
      Subgroup.map_subgroupOf_eq_of_le hcfg'.ext.le_H, e]
  obtain ⟨Jt, φ, hφs, hY₀⟩ := exists_competitor_surj_of hp hLX₀ hLJ hcfg'.ext.primeCore_le hJH'
  exact hcfg'.red.false_of_surjective_of_rankOne_at hcfg'.catalog hInv.on hSch h3' hK' hnc' hz' hLs
    hLnab hiso φ hφs hY₀

end Competitor

end CFSG.AGLEmbedding
