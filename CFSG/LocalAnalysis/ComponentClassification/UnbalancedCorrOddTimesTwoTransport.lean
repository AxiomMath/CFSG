module

public import CFSG.LocalAnalysis.ComponentClassification.ProperSectionBKGroup
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup

theorem closure_odd_orderOf_eq_top_of_isPerfect {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : closure {x : X | Odd (orderOf x)} = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := closure {x : X | Odd (orderOf x)} with hNdef
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      show Odd (orderOf (g * x * g⁻¹))
      have := (MulAut.conj g).orderOf_eq x
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hx
    | one => simp
    | mul x y _ _ ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact N.mul_mem ihx ihy
    | inv x _ ih =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact N.inv_mem ih
  have h2 : IsPGroup 2 (X ⧸ N) :=
    CFSG.Glauberman.isPGroup_quotient_of_pPrime_order_elements_mem N fun x hx =>
      Subgroup.subset_closure (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hx))
  rcases subsingleton_or_nontrivial (X ⧸ N) with h | h
  · exact eq_top_iff.mpr fun x _ => (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  · exact absurd h2.isNilpotent (Group.IsPerfect.not_isNilpotent _)

theorem not_isPGroup_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hQ : IsQuasisimple Q) : ¬ IsPGroup p Q := fun h => by
  have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isNilpotent Q h.isNilpotent

theorem inf_eq_bot_of_isPGroup_two {G : Type*} [Group G] [Finite G] {P O : Subgroup G}
    (hP : IsPGroup 2 P) (hO : Nat.Coprime 2 (Nat.card O)) : P ⊓ O = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  exact disjoint_iff.mp (disjoint_of_coprime_natCard (by rw [hn]; exact Nat.Coprime.pow_left n hO))

theorem le_pPrimeCore_of_isSubnormal {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (hN : N.IsSubnormal) (hcop : Nat.Coprime 2 (Nat.card N)) : N ≤ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htop : pPrimeCore 2 N = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, by rwa [card_top]⟩)
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val ≠ 2} hN
  rw [← pPrimeCore_eq_piCore, ← pPrimeCore_eq_piCore, htop, ← MonoidHom.range_eq_map,
    range_subtype] at h
  exact inf_eq_left.mp h.symm

theorem card_ker_subgroupMap_dvd {G G' : Type*} [Group G] [Group G'] [Finite G] (f : G →* G')
    (S : Subgroup G) : Nat.card (f.subgroupMap S).ker ∣ Nat.card f.ker := by
  let g : (f.subgroupMap S).ker →* f.ker :=
    { toFun := fun x => ⟨((x : S) : G), (MonoidHom.mem_ker).mpr
        (congrArg Subtype.val ((MonoidHom.mem_ker).mp x.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine card_dvd_of_injective g fun x y h => ?_
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

theorem kGroup_odd_times_two_normalizer_component_transport_of_inputs
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    {H : Type} [Group H] [Finite H]
    (hK : SectionRank.IsKGroupCat H) (B : Subgroup H) [B.Normal] (hB : IsPGroup 2 B)
    {Q : Type*} [Group Q] (θ : H →* Q) (hθ : Function.Surjective θ)
    (hθN : θ.ker = pPrimeCore 2 H ⊔ B) (A : Subgroup H) (hA : IsPGroup 2 A) (hA1 : A ≠ ⊥)
    (hBA : B ≤ A) (M : Subgroup H) (hMA : M ≤ normalizer (A : Set H))
    (hM : IsPComponent 2 (M.subgroupOf (normalizer (A : Set H)))) :
    ⁅pPrimeCore 2 H, B⁆ = ⊥ ∧ pPrimeCore 2 H ⊓ B = ⊥ ∧
      (∃ e : ↥(pPrimeCore 2 H) × ↥B ≃* ↥(pPrimeCore 2 H ⊔ B),
        ∀ (r : ↥(pPrimeCore 2 H)) (b : ↥B), (e (r, b) : H) = r * b) ∧
      ⁅M, A⁆ = ⊥ ∧
      (normalizer (A : Set H)).map θ = normalizer ((A.map θ : Subgroup Q) : Set Q) ∧
      M.map θ ≠ ⊥ ∧ M.map θ ≤ normalizer ((A.map θ : Subgroup Q) : Set Q) ∧
      IsComponent ((M.map θ).subgroupOf (normalizer ((A.map θ : Subgroup Q) : Set Q))) ∧
      (pPrimeCore 2 ↥M).map (θ.subgroupMap M) ≤ center ↥(M.map θ) ∧
      CFSG.Open.fusionZStar ↥M = (center ↥(M.map θ)).comap (θ.subgroupMap M) ∧
      (∃ e : ↥M ⧸ CFSG.Open.fusionZStar ↥M ≃* ↥(M.map θ) ⧸ center ↥(M.map θ),
        ∀ m : ↥M, e (m : ↥M ⧸ CFSG.Open.fusionZStar ↥M) =
          ((θ.subgroupMap M m : ↥(M.map θ)) : ↥(M.map θ) ⧸ center ↥(M.map θ))) ∧
      (2 ≤ pRank 2 ↥M → 2 ≤ pRank 2 ↥(M.map θ)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective θ hθ
  set R := pPrimeCore 2 H with hRdef
  set K := normalizer (A : Set H) with hKdef
  obtain ⟨Kc, hKc, hLsub, hLmap, -⟩ := id hM
  have hRcop : Nat.Coprime 2 (Nat.card R) := pPrimeCore_coprime_card
  have hRB : R ⊓ B = ⊥ := by rw [inf_comm]; exact inf_eq_bot_of_isPGroup_two hB hRcop
  have hRBc : ⁅R, B⁆ = ⊥ := le_bot_iff.mp (hRB ▸ commutator_le_inf R B)
  have hprod : ∃ e : ↥R × ↥B ≃* ↥(R ⊔ B), ∀ (r : ↥R) (b : ↥B), (e (r, b) : H) = r * b := by
    have hc : ∀ (r : ↥R) (b : ↥B), Commute (R.subtype r) (B.subtype b) := by
      intro r b
      have h := commutator_mem_commutator r.2 b.2
      rw [hRBc, mem_bot] at h
      exact commutatorElement_eq_one_iff_mul_comm.mp h
    let f := MonoidHom.noncommCoprod R.subtype B.subtype hc
    have hf : ∀ x, f x ∈ R ⊔ B := fun x =>
      mul_mem (mem_sup_left x.1.2) (mem_sup_right x.2.2)
    let f' := f.codRestrict (R ⊔ B) hf
    have hbij : Function.Bijective f' := by
      refine ⟨fun x y hxy => ?_, fun ⟨z, hz⟩ => ?_⟩
      · have h1 : (x.1 : H) * x.2 = y.1 * y.2 := congrArg Subtype.val hxy
        have hmem : (y.1 : H)⁻¹ * x.1 ∈ R ⊓ B := by
          refine ⟨R.mul_mem (R.inv_mem y.1.2) x.1.2, ?_⟩
          have : (y.1 : H)⁻¹ * x.1 = y.2 * (x.2 : H)⁻¹ := by
            calc (y.1 : H)⁻¹ * x.1 = (y.1 : H)⁻¹ * (x.1 * x.2) * (x.2 : H)⁻¹ := by group
              _ = (y.1 : H)⁻¹ * (y.1 * y.2) * (x.2 : H)⁻¹ := by rw [h1]
              _ = y.2 * (x.2 : H)⁻¹ := by group
          rw [this]
          exact B.mul_mem y.2.2 (B.inv_mem x.2.2)
        rw [hRB, mem_bot, inv_mul_eq_one] at hmem
        have h2 : (x.2 : H) = y.2 := by
          rw [← hmem] at h1
          exact mul_left_cancel h1
        exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext h2)
      · rw [← SetLike.mem_coe, normal_mul] at hz
        obtain ⟨r, hr, b, hb, rfl⟩ := Set.mem_mul.mp hz
        exact ⟨(⟨r, hr⟩, ⟨b, hb⟩), rfl⟩
    exact ⟨MulEquiv.ofBijective f' hbij, fun r b => rfl⟩
  have hAK : A ≤ K := le_normalizer
  have hA'2 : IsPGroup 2 (A.subgroupOf K) := hA.comap_of_injective K.subtype K.subtype_injective
  have hA'n : (A.subgroupOf K).Normal := normal_in_normalizer
  have hĀn : ((A.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K))).Normal :=
    hA'n.map _ (QuotientGroup.mk'_surjective _)
  have hĀs : Group.IsSolvable ↥((A.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K))) := by
    have : Group.IsNilpotent ↥((A.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K))) :=
      (hA'2.map _).isNilpotent
    infer_instance
  have hcK := (CFSG.LocalCores.component_solvable_centralizer hĀs hĀn.isSubnormal).1 Kc hKc
  rw [← hLmap, ← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hcK
  have hLA : ⁅M.subgroupOf K, A.subgroupOf K⁆ = ⊥ := by
    have h := le_inf (commutator_le_right (M.subgroupOf K) (A.subgroupOf K)) hcK
    rwa [inf_eq_bot_of_isPGroup_two hA'2 pPrimeCore_coprime_card, le_bot_iff] at h
  have hML : (M.subgroupOf K).map K.subtype = M := by
    rw [subgroupOf_map_subtype, inf_of_le_left hMA]
  have hAL : (A.subgroupOf K).map K.subtype = A := by
    rw [subgroupOf_map_subtype, inf_of_le_left hAK]
  have hMAc : ⁅M, A⁆ = ⊥ := by rw [← hML, ← hAL, ← map_commutator, hLA, Subgroup.map_bot]
  set π := QuotientGroup.mk' R with hπdef
  have hNπ : (R ⊔ B).map π = B.map π := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hnorm : K.map θ = normalizer ((A.map θ : Subgroup Q) : Set Q) := by
    refine le_antisymm (le_normalizer_map θ) fun y hy => ?_
    obtain ⟨h, rfl⟩ := hθ y
    have hc : (A.map θ).comap θ = A ⊔ R := by
      rw [comap_map_eq, hθN, sup_comm R B, ← sup_assoc, sup_eq_left.mpr hBA]
    have h1 : h ∈ normalizer ((A ⊔ R : Subgroup H) : Set H) := by
      rw [← hc, ← comap_normalizer_eq_of_surjective _ hθ]
      exact hy
    have h2 := le_normalizer_map π (mem_map_of_mem π h1)
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      ← CFSG.GroupTheory.normal_coprime_quotient_normalizer 2 R
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hRcop) A hA] at h2
    obtain ⟨k, hk, hkh⟩ := h2
    refine ⟨k, hk, ?_⟩
    have hkR : k⁻¹ * h ∈ R := QuotientGroup.eq.mp hkh
    have h3 : θ (k⁻¹ * h) = 1 := by
      rw [← MonoidHom.mem_ker, hθN]
      exact mem_sup_left hkR
    rw [map_mul, map_inv, inv_mul_eq_one] at h3
    exact h3
  have hP : IsQuasisimple ↥(M.map π) := by
    obtain ⟨-, -, hloc⟩ := ProperSectionB.kGroupBConclusion_of_inputs hS hU hheld hK
    obtain ⟨-, -, hcomp⟩ := hloc A hA1 hA
    have hc := (hcomp (M.subgroupOf K) hM).1
    rw [subgroupOf_map_subtype, inf_of_le_left hMA] at hc
    have hR₀ : CFSG.Assembly.oddCore H = R := by
      show sSup _ = sSup _
      congr 1
      ext J
      simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]
    have key : ∀ (R' : Subgroup H) [R'.Normal], R' = R →
        CFSG.Assembly.IsQuasisimple ↥(M.map (QuotientGroup.mk' R')) →
          IsQuasisimple ↥(M.map π) := by
      intro R' _ hR' hq
      subst hR'
      exact (AssemblyBPredicates.isQuasisimple_iff_native _).mp hq
    exact key _ hR₀ hc.2.2
  have hRθ : R ≤ θ.ker := hθN ▸ le_sup_left
  set φ : H ⧸ R →* Q := QuotientGroup.lift R θ hRθ with hφdef
  have hψmem : ∀ x : ↥(M.map π), φ.comp (M.map π).subtype x ∈ M.map θ := by
    rintro ⟨_, m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  set ψ : ↥(M.map π) →* ↥(M.map θ) := (φ.comp (M.map π).subtype).codRestrict (M.map θ) hψmem
    with hψdef
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨_, m, hm, rfl⟩
    exact ⟨π.subgroupMap M ⟨m, hm⟩, rfl⟩
  have hMθ : M.map θ ≠ ⊥ := by
    intro hbot
    have hMN : M ≤ R ⊔ B := by rw [← hθN]; exact (Subgroup.map_eq_bot_iff M).mp hbot
    exact not_isPGroup_of_isQuasisimple hP ((hB.map π).to_le ((map_mono hMN).trans hNπ.le))
  have hψker : ψ.ker ≤ center ↥(M.map π) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hP ψ.normal_ker with h | h
    · refine absurd (eq_bot_iff.mpr fun y hy => ?_) hMθ
      obtain ⟨x, hx⟩ := hψsurj ⟨y, hy⟩
      have h1 : ψ x = 1 := MonoidHom.mem_ker.mp (h ▸ mem_top x)
      rw [h1] at hx
      exact mem_bot.mpr (congrArg Subtype.val hx).symm
    · exact h
  have hU : IsQuasisimple ↥(M.map θ) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hP ψ hψsurj hψker
  set W := normalizer ((A.map θ : Subgroup Q) : Set Q) with hWdef
  have hMW : M.map θ ≤ W := hnorm ▸ map_mono hMA
  have hθKmem : ∀ k : ↥K, θ.comp K.subtype k ∈ W := fun k => hnorm ▸ mem_map_of_mem θ k.2
  set θK : ↥K →* ↥W := (θ.comp K.subtype).codRestrict W hθKmem with hθKdef
  have hθKsurj : Function.Surjective θK := by
    rintro ⟨y, hy⟩
    rw [← hnorm] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact ⟨⟨k, hk⟩, rfl⟩
  have hLW : (M.subgroupOf K).map θK = (M.map θ).subgroupOf W := by
    ext ⟨y, hy⟩
    rw [mem_map, mem_subgroupOf]
    constructor
    · rintro ⟨k, hk, hky⟩
      exact ⟨(k : H), hk, congrArg Subtype.val hky⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hMA hm⟩, hm, rfl⟩
  have hcomp : IsComponent ((M.map θ).subgroupOf W) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMW).symm hU,
      hLW ▸ hLsub.map hθKsurj⟩
  set O := pPrimeCore 2 ↥M with hOdef
  set π' := π.subgroupMap M with hπ'def
  have hπ'surj : Function.Surjective π' := π.subgroupMap_surjective M
  have hπ'ker : π'.ker ≤ O := by
    refine le_sSup ⟨π'.normal_ker, ?_⟩
    have h := card_ker_subgroupMap_dvd π M
    rw [QuotientGroup.ker_mk'] at h
    exact Nat.Coprime.coprime_dvd_right h hRcop
  have hOn : (O.map π').Normal := Subgroup.Normal.map inferInstance π' hπ'surj
  have hOc : O.map π' ≤ center ↥(M.map π) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hP hOn with h | h
    · exfalso
      have hOtop : O = ⊤ := by
        refine eq_top_iff.mpr fun m _ => ?_
        have hm : π' m ∈ O.map π' := by rw [h]; exact mem_top _
        obtain ⟨o, ho, hom⟩ := hm
        have hk : o⁻¹ * m ∈ π'.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hom, inv_mul_cancel]
        simpa using O.mul_mem ho (hπ'ker hk)
      have hMcop : Nat.Coprime 2 (Nat.card ↥M) := by
        have h1 : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card
        rwa [hOtop, card_top] at h1
      have hLcop : Nat.Coprime 2 (Nat.card ↥(M.subgroupOf K)) := by
        rwa [Nat.card_congr (subgroupOfEquivOfLe hMA).toEquiv]
      have hKbot : Kc = ⊥ := by
        rw [← hLmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        exact le_pPrimeCore_of_isSubnormal hLsub hLcop
      exact (nontrivial_iff_ne_bot Kc).mp (CFSG.LocalCores.isQuasisimple_nontrivial hKc.1) hKbot
    · exact h
  have hfo : CFSG.Open.fusionOddCore ↥M = O := by
    show sSup _ = sSup _
    congr 1
    ext J
    simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]
  have hzstar : ∀ m : ↥M,
      m ∈ CFSG.Open.fusionZStar ↥M ↔ ∀ x : ↥M, (x * m)⁻¹ * (m * x) ∈ O := by
    intro m
    rw [← hfo]
    show QuotientGroup.mk' _ m ∈ center _ ↔ _
    rw [mem_center_iff]
    constructor
    · intro h x
      have h1 := h (QuotientGroup.mk' _ x)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h1
      exact QuotientGroup.eq.mp h1
    · intro h y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
      exact QuotientGroup.eq.mpr (h x)
  have hZπ : CFSG.Open.fusionZStar ↥M = (center ↥(M.map π)).comap π' := by
    ext m
    rw [hzstar, mem_comap]
    constructor
    · intro h
      have hcz := CFSG.LocalCores.comap_center_eq_of_perfect hP.1 (QuotientGroup.mk' (O.map π'))
        (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hOc)
      rw [← hcz, mem_comap, mem_center_iff]
      intro z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ z
      obtain ⟨x, rfl⟩ := hπ'surj w
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
      refine QuotientGroup.eq.mpr ?_
      have h1 := mem_map_of_mem π' (h x)
      rwa [map_mul, map_inv, map_mul, map_mul] at h1
    · intro h x
      apply hπ'ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mem_center_iff.mp h (π' x),
        inv_mul_cancel]
  have hθψ : θ.subgroupMap M = ψ.comp π' := MonoidHom.ext fun m => rfl
  have hZθ : CFSG.Open.fusionZStar ↥M = (center ↥(M.map θ)).comap (θ.subgroupMap M) := by
    rw [hZπ, hθψ, ← comap_comap,
      CFSG.LocalCores.comap_center_eq_of_perfect hP.1 ψ hψsurj hψker]
  have hOZ : O ≤ CFSG.Open.fusionZStar ↥M := fun o ho => (hzstar o).mpr fun x => by
    have h1 : (x * o)⁻¹ * (o * x) = o⁻¹ * (x⁻¹ * o * x⁻¹⁻¹) := by group
    rw [h1]
    exact O.mul_mem (O.inv_mem ho) ((inferInstance : O.Normal).conj_mem o ho x⁻¹)
  have hOθ : O.map (θ.subgroupMap M) ≤ center ↥(M.map θ) :=
    map_le_iff_le_comap.mpr (hZθ ▸ hOZ)
  have hiso : ∃ e : ↥M ⧸ CFSG.Open.fusionZStar ↥M ≃* ↥(M.map θ) ⧸ center ↥(M.map θ),
      ∀ m : ↥M, e (m : ↥M ⧸ CFSG.Open.fusionZStar ↥M) =
        ((θ.subgroupMap M m : ↥(M.map θ)) : ↥(M.map θ) ⧸ center ↥(M.map θ)) := by
    let F : ↥M →* ↥(M.map θ) ⧸ center ↥(M.map θ) :=
      (QuotientGroup.mk' _).comp (θ.subgroupMap M)
    have hF : Function.Surjective F :=
      (QuotientGroup.mk'_surjective _).comp (θ.subgroupMap_surjective M)
    have hFker : CFSG.Open.fusionZStar ↥M = F.ker := by
      rw [hZθ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hFker).trans
      (QuotientGroup.quotientKerEquivOfSurjective F hF), fun m => rfl⟩
  have hrank : 2 ≤ pRank 2 ↥M → 2 ≤ pRank 2 ↥(M.map θ) := by
    intro hM2
    by_contra hlt
    have hU1 : pRank 2 ↥(M.map θ) ≤ 1 := by omega
    obtain ⟨-, -, -, hsyl⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.quasisimple_rank_one_unique_central_involution hU hU1
    obtain ⟨r, hr3, ⟨e⟩⟩ := hsyl (Classical.arbitrary _)
    have : Group.IsPerfect ↥(M.map π) := hP.1
    have h2ker : IsPGroup 2 ψ.ker := by
      rintro ⟨⟨y, hy⟩, hx⟩
      have hyB : y ∈ B.map π := by
        obtain ⟨m, hm, rfl⟩ := hy
        rw [← hNπ]
        refine mem_map_of_mem π ?_
        rw [← hθN, MonoidHom.mem_ker]
        exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      obtain ⟨k, hk⟩ := (hB.map π) ⟨y, hyB⟩
      have hk' := congrArg Subtype.val hk
      exact ⟨k, Subtype.ext (Subtype.ext hk')⟩
    have hker := CFSG.LieType.CentralExt.ker_eq_bot_of_sylow_quaternion
      closure_odd_orderOf_eq_top_of_isPerfect ψ hψsurj hψker h2ker _ hr3 e
    have hbij : Function.Bijective ψ := ⟨(MonoidHom.ker_eq_bot_iff ψ).mp hker, hψsurj⟩
    have hPU : pRank 2 ↥(M.map π) = pRank 2 ↥(M.map θ) := by
      rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
      exact SectionRank.pRank_top_eq_of_mulEquiv one_lt_two (MulEquiv.ofBijective ψ hbij)
    have hMP : pRank 2 ↥M = pRank 2 ↥(M.map π) := by
      have hnd : ¬ 2 ∣ Nat.card π'.ker := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (Nat.Coprime.coprime_dvd_right (card_ker_subgroupMap_dvd π M)
          (by rwa [QuotientGroup.ker_mk']))
      rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top,
        ← SectionRank.pRank_quotient_eq π'.ker hnd]
      exact SectionRank.pRank_top_eq_of_mulEquiv one_lt_two
        (QuotientGroup.quotientKerEquivOfSurjective π' hπ'surj)
    omega
  exact ⟨hRBc, hRB, hprod, hMAc, hnorm, hMθ, hMW, hcomp, hOθ, hZθ, hiso, hrank⟩

end CFSG.ComponentClassification.UnbalancedCorr
