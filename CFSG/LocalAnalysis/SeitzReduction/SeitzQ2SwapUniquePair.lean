module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2SwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUniqueType

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (inducedAut inducedAut_mul_self inducedAut_ne_one
  card_fixedSubgroup_inducedAut_dvd card_perfectCore_fixedSubgroup_inducedAut
  map_perfectCore_fixedSubgroup_le_centralizer factorization_two_le_of_odd_ker
  card_dvd_card_range_of_ker_le quotientCenterEquivOfSurjective)

@[expose] def SwapPairExclusion (P : Type*) [Group P] : Prop :=
  ∀ θ θ' : MulAut P, θ * θ = 1 → θ ≠ 1 → θ' * θ' = 1 → θ' ≠ 1 →
    (Nat.card (fixedSubgroup θ)).factorization 2 + (Nat.card (fixedSubgroup θ')).factorization 2 ≤
      (2 * Nat.card (MulAut P)).factorization 2 →
    Nat.card (perfectCore (fixedSubgroup θ)) * Nat.card (perfectCore (fixedSubgroup θ')) ∣
      Nat.card P → False

section Core

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {P : Type} [Group P] [Finite P]

theorem exists_pair_of_factorNormal_of_mulEquiv (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A B : Subgroup G} (hqA : CFSG.Open.IsQuasisimple A) (hqB : CFSG.Open.IsQuasisimple B)
    (hAB : B ≤ centralizer (A : Set G)) (hodd : Odd (Nat.card (A ⊓ B : Subgroup G)))
    (ψA : A ⧸ center A ≃* P) (ψB : B ⧸ center B ≃* P)
    (htA : t ∈ normalizer (A : Set G)) (htB : t ∈ normalizer (B : Set G))
    (hnA : t ∉ centralizer (A : Set G)) (hnB : t ∉ centralizer (B : Set G)) :
    ∃ θ θ' : MulAut P, θ * θ = 1 ∧ θ ≠ 1 ∧ θ' * θ' = 1 ∧ θ' ≠ 1 ∧
      (Nat.card (fixedSubgroup θ)).factorization 2 +
          (Nat.card (fixedSubgroup θ')).factorization 2 ≤
        (2 * Nat.card (MulAut P)).factorization 2 ∧
      Nat.card (perfectCore (fixedSubgroup θ)) * Nat.card (perfectCore (fixedSubgroup θ')) ∣
        Nat.card P := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have : Group.IsPerfect A := ⟨hqA.1⟩
  have : Group.IsPerfect B := ⟨hqB.1⟩
  refine ⟨inducedAut A ψA htA, inducedAut B ψB htB, inducedAut_mul_self ψA htA ht,
    inducedAut_ne_one ψA htA hnA, inducedAut_mul_self ψB htB ht, inducedAut_ne_one ψB htB hnB,
    ?_, ?_⟩
  ·
    set CA := A ⊓ centralizer ({t} : Set G) with hCA
    set CB := B ⊓ centralizer ({t} : Set G) with hCB
    have hcomm : ∀ (x : CA) (y : CB), Commute (CA.subtype x) (CB.subtype y) := fun x y =>
      mem_centralizer_iff.1 (hAB y.2.1) x x.2.1
    set μ := MonoidHom.noncommCoprod CA.subtype CB.subtype hcomm with hμ
    have hrange : μ.range ≤ centralizer ({t} : Set G) := by
      rintro _ ⟨p, rfl⟩
      rw [hμ, MonoidHom.noncommCoprod_apply]
      exact mul_mem p.1.2.2 p.2.2.2
    have hrel : ∀ p : μ.ker, ((p : CA × CB).1 : G) = ((p : CA × CB).2 : G)⁻¹ := by
      intro p
      have h0 := (MonoidHom.noncommCoprod_apply CA.subtype CB.subtype hcomm
        (p : CA × CB)).symm.trans (MonoidHom.mem_ker.1 p.2)
      exact eq_inv_of_mul_eq_one_left h0
    have hmem : ∀ p : μ.ker, ((p : CA × CB).1 : G) ∈ A ⊓ B := fun p =>
      mem_inf.2 ⟨(p : CA × CB).1.2.1, by rw [hrel p]; exact inv_mem (p : CA × CB).2.2.1⟩
    let ι : μ.ker →* (A ⊓ B : Subgroup G) :=
      { toFun := fun p => ⟨_, hmem p⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro p q hpq
      have h1 : ((p : CA × CB).1 : G) = ((q : CA × CB).1 : G) :=
        congrArg (fun z : (A ⊓ B : Subgroup G) => (z : G)) hpq
      have h2 : ((p : CA × CB).2 : G) = ((q : CA × CB).2 : G) := by
        have hp := hrel p
        have hq := hrel q
        rw [h1] at hp
        exact inv_injective (hp.symm.trans hq)
      exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
    have hkerodd : Odd (Nat.card μ.ker) := Odd.of_dvd_nat hodd (card_dvd_of_injective ι hι)
    have h1 := factorization_two_le_of_odd_ker μ hrange hkerodd
    have hCt := F4Pilot.card_centralizer_dvd_two_mul_card_mulAut e ht
      (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC
        ht) hKt
    have h2 := LinearPilot.factorization_two_le_of_dvd hCt
      (mul_ne_zero two_ne_zero Nat.card_pos.ne')
    have hdA := LinearPilot.factorization_two_le_of_dvd (card_fixedSubgroup_inducedAut_dvd ψA htA)
      Nat.card_pos.ne'
    have hdB := LinearPilot.factorization_two_le_of_dvd (card_fixedSubgroup_inducedAut_dvd ψB htB)
      Nat.card_pos.ne'
    rw [Nat.card_prod, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply] at h1
    rw [← hCA] at hdA
    rw [← hCB] at hdB
    omega
  ·
    set PA := perfectCore (fixedSubgroup (A.normalizerMonoidHom ⟨t, htA⟩)) with hPA
    set PB := perfectCore (fixedSubgroup (B.normalizerMonoidHom ⟨t, htB⟩)) with hPB
    have hcomm : ∀ (x : PA) (y : PB),
        Commute ((A.subtype.comp PA.subtype) x) ((B.subtype.comp PB.subtype) y) := fun x y =>
      mem_centralizer_iff.1 (hAB (y : B).2) _ (x : A).2
    set μ := MonoidHom.noncommCoprod (A.subtype.comp PA.subtype) (B.subtype.comp PB.subtype)
      hcomm with hμ
    set ν := MonoidHom.prodMap ((QuotientGroup.mk' (center A)).comp PA.subtype)
      ((QuotientGroup.mk' (center B)).comp PB.subtype) with hν
    have hker : μ.ker ≤ ν.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      intro p hp
      rw [MonoidHom.mem_ker, hμ, MonoidHom.noncommCoprod_apply] at hp
      have hx : (((p.1 : PA) : A) : G) = (((p.2 : PB) : B) : G)⁻¹ := eq_inv_of_mul_eq_one_left hp
      have hy : (((p.2 : PB) : B) : G) = (((p.1 : PA) : A) : G)⁻¹ := eq_inv_of_mul_eq_one_right hp
      have hxZ : ((p.1 : PA) : A) ∈ center A := by
        rw [mem_center_iff]
        intro a
        apply Subtype.ext
        have hxB : (((p.1 : PA) : A) : G) ∈ B := by rw [hx]; exact inv_mem ((p.2 : PB) : B).2
        exact mem_centralizer_iff.1 (hAB hxB) a a.2
      have hyZ : ((p.2 : PB) : B) ∈ center B := by
        rw [mem_center_iff]
        intro b
        apply Subtype.ext
        have hyA : (((p.2 : PB) : B) : G) ∈ A := by rw [hy]; exact inv_mem ((p.1 : PA) : A).2
        exact (mem_centralizer_iff.1 (hAB b.2) _ hyA).symm
      rw [MonoidHom.mem_ker]
      refine Prod.ext ?_ ?_
      · change QuotientGroup.mk' (center A) ((p.1 : PA) : A) = 1
        exact (QuotientGroup.eq_one_iff _).2 hxZ
      · change QuotientGroup.mk' (center B) ((p.2 : PB) : B) = 1
        exact (QuotientGroup.eq_one_iff _).2 hyZ
    have hdvd := card_dvd_card_range_of_ker_le μ ν.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ν) hker
    have hνr : Nat.card ν.range = Nat.card (PA.map (QuotientGroup.mk' (center A))) *
        Nat.card (PB.map (QuotientGroup.mk' (center B))) := by
      rw [hν, MonoidHom.range_prodMap, MonoidHom.range_comp, MonoidHom.range_comp, range_subtype,
        range_subtype, ← Nat.card_prod]
      exact Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv
    have hpA : Group.IsPerfect PA :=
      Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfectCore_perfect _)
    have hpB : Group.IsPerfect PB :=
      Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfectCore_perfect _)
    have htop : ⁅(⊤ : Subgroup (PA × PB)), (⊤ : Subgroup (PA × PB))⁆ =
        (⊤ : Subgroup (PA × PB)) := by
      rw [← Subgroup.top_prod_top, Subgroup.commutator_prod_prod, ← _root_.commutator_def,
        ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top,
        Group.IsPerfect.commutator_eq_top]
    have hperf : ⁅μ.range, μ.range⁆ = μ.range := by
      rw [MonoidHom.range_eq_map, ← map_commutator, htop]
    have hμt : μ.range ≤ centralizer ({t} : Set G) := by
      rintro _ ⟨p, rfl⟩
      rw [hμ, MonoidHom.noncommCoprod_apply]
      exact mul_mem (map_perfectCore_fixedSubgroup_le_centralizer htA ⟨_, p.1.2, rfl⟩)
        (map_perfectCore_fixedSubgroup_le_centralizer htB ⟨_, p.2.2, rfl⟩)
    have hμL : μ.range ≤ L :=
      CFSG.SeitzReduction.std_perfect_le hset.standardSetting hOut htC ht hperf hμt
    have hLdvd : Nat.card μ.range ∣ Nat.card P := by
      rw [← Nat.card_congr e.toEquiv]
      exact Subgroup.card_dvd_of_le hμL
    rw [card_perfectCore_fixedSubgroup_inducedAut, card_perfectCore_fixedSubgroup_inducedAut,
      ← hPA, ← hPB, ← hνr]
    exact hdvd.trans hLdvd

end Core

section Exclusion

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {P : Type} [Group P] [Finite P]

theorem factorNormal_of_swapPairExclusion (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P) (hP : SwapPairExclusion P) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ A : Subgroup G, CFSG.Open.IsQuasisimple A → Odd (Nat.card (center A)) →
      (∃ φ : A →* L, Function.Surjective φ ∧ φ.ker ≤ center A) →
      ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G) →
        t ∈ normalizer (A : Set G) →
        t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
        t ∉ centralizer (A : Set G) →
        t ∉ centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) → False := by
  intro A hq hoddZ hφ g hAB htA htB hnA hnB
  obtain ⟨φ, hφs, hφk⟩ := hφ
  have hZL := hset.center_eq_bot
  set B := A.map (MulAut.conj g).toMonoidHom with hB
  have hqB : CFSG.Open.IsQuasisimple B := LinearPilot.isQuasisimple_map_conj hq g
  set σ : B ≃* A := (A.equivMapOfInjective _ (MulAut.conj g).injective).symm with hσ
  have hφBs : Function.Surjective (φ.comp σ.toMonoidHom) := hφs.comp σ.surjective
  have hφBk : (φ.comp σ.toMonoidHom).ker ≤ center B := by
    intro z hz
    have hz' : σ z ∈ center A := hφk hz
    rw [mem_center_iff] at hz' ⊢
    intro w
    apply σ.injective
    rw [map_mul, map_mul]
    exact hz' (σ w)
  set ψA := (quotientCenterEquivOfSurjective φ hφs hφk hZL).trans e with hψA
  set ψB := (quotientCenterEquivOfSurjective (φ.comp σ.toMonoidHom) hφBs hφBk hZL).trans e
    with hψB
  have hodd : Odd (Nat.card (A ⊓ B : Subgroup G)) := by
    have hle : (A ⊓ B).subgroupOf A ≤ center A := by
      intro x hx
      rw [mem_subgroupOf] at hx
      rw [mem_center_iff]
      intro a
      apply Subtype.ext
      exact mem_centralizer_iff.1 (hAB (mem_inf.1 hx).2) a a.2
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv]
    exact Odd.of_dvd_nat hoddZ (Subgroup.card_dvd_of_le hle)
  obtain ⟨θ, θ', h1, h2, h3, h4, h5, h6⟩ := exists_pair_of_factorNormal_of_mulEquiv hset hOut e ht
    hKt hq hqB hAB hodd ψA ψB htA htB hnA hnB
  exact hP θ θ' h1 h2 h3 h4 h5 h6

theorem unique_of_swapFactors_of_neighbours_of_swapPairExclusion (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P) (hP : SwapPairExclusion P) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    {κ : Type*} (X D : κ → Subgroup G) (hXL : ∀ k, X k ≤ L)
    (hDX : ∀ k, D k ≤ centralizer (X k : Set G)) (hDperf : ∀ k, ⁅D k, D k⁆ = D k)
    (hgen : ⨆ k, D k = L)
    (hE : ∀ k, F4Pilot.centralizerPerfectCore (X k) ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) :
    ∀ g : G, g⁻¹ * t * g ∈
        normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
  unique_of_swapFactors_of_neighbours_of_factorNormal hset hOut ht hKt
    (factorNormal_of_swapPairExclusion hset hOut e hP ht hKt) hq h₁₂ hδ hsurj X D hXL hDX hDperf
    hgen hE

theorem false_of_coherent_swapParam_of_swapPairExclusion (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P) (hP : SwapPairExclusion P) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {ι κ : Type*} {D : ι → Subgroup G} (Ψ : ∀ a, SwapParam t (D a)) (O : κ → Subgroup G)
    (ν : κ → ι) (hOν : ∀ k, O k ≤ D (ν k)) (hOperf : ∀ k, ⁅O k, O k⁆ = O k)
    (hpair : ∀ k l, ∃ a, O k ≤ D a ∧ O l ≤ D a ∧ AgreeOn (Ψ (ν k)) (Ψ a) (O k) ∧
      AgreeOn (Ψ (ν l)) (Ψ a) (O l))
    (hgen : ⨆ k, O k = L) (X : κ → Subgroup G) (hXL : ∀ k, X k ≤ L)
    (hOX : ∀ k, O k ≤ centralizer (X k : Set G))
    (hM : ∀ k, F4Pilot.centralizerPerfectCore (X k) =
      (((O k).subgroupOf (D (ν k))).prod ((O k).subgroupOf (D (ν k)))).map (Ψ (ν k)).Ψ) :
    False :=
  false_of_coherent_swapParam_of_overlaps hset hOut ht hKt
    (factorNormal_of_swapPairExclusion hset hOut e hP ht hKt) Ψ O ν hOν hOperf hpair hgen X hXL
    hOX hM

end Exclusion

end CFSG.SeitzReduction.SeitzQ2
