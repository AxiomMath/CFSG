module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.AGLEmbedding

namespace ToralCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem le_normalizer_of_conj_inv_mem {G : Type*} [Group G] {S T : Subgroup G}
    (h : ∀ x ∈ S, ∀ t ∈ T, x * t * x⁻¹ ∈ T) : S ≤ Subgroup.normalizer (T : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨h x hx t, fun ht => ?_⟩
  simpa [mul_assoc] using h x⁻¹ (S.inv_mem hx) _ ht

theorem comap_normalizer_map_eq {G P : Type*} [Group G] [Group P] [Finite G] {φ : G →* P}
    (hker : φ.ker ≤ Subgroup.center G) (hodd : Odd (Nat.card φ.ker)) {T : Subgroup G}
    (hT : IsPGroup 2 T) :
    (Subgroup.normalizer ((T.map φ : Subgroup P) : Set P)).comap φ =
      Subgroup.normalizer (T : Set G) := by
  refine le_antisymm (le_normalizer_of_conj_inv_mem fun x hx t ht => ?_)
    (Subgroup.map_le_iff_le_comap.mp (Subgroup.le_normalizer_map φ))
  have hx' := (Subgroup.mem_normalizer_iff.mp hx (φ t)).mp ⟨t, ht, rfl⟩
  rw [← map_mul, ← map_inv, ← map_mul] at hx'
  obtain ⟨t', ht', hφ⟩ := hx'
  set z := t'⁻¹ * (x * t * x⁻¹) with hz
  have hzk : z ∈ φ.ker := by rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hφ, inv_mul_cancel]
  have hzc := hker hzk
  have hw : x * t * x⁻¹ = t' * z := by rw [hz, mul_inv_cancel_left]
  obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
  obtain ⟨b, hb⟩ := hT ⟨t', ht'⟩
  have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have htb : t' ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hzm : z ^ 2 ^ (a + b) = 1 := by
    have h1 : (x * t * x⁻¹) ^ 2 ^ (a + b) = 1 := by
      rw [conj_pow, pow_add, pow_mul, hta, one_pow, mul_one, mul_inv_cancel]
    have h2 : t' ^ 2 ^ (a + b) = 1 := by
      rw [pow_add, mul_comm, pow_mul, htb, one_pow]
    rw [hw, (show Commute t' z from Subgroup.mem_center_iff.mp hzc t').mul_pow, h2,
      one_mul] at h1
    exact h1
  have hord : orderOf (⟨z, hzk⟩ : φ.ker) = 1 := by
    refine Nat.Coprime.eq_one_of_dvd ?_ (orderOf_dvd_natCard _)
    refine Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one (Subtype.ext hzm : _)) ?_
    exact (Nat.Coprime.pow_left _ (Nat.coprime_comm.mp (Odd.coprime_two_right hodd)))
  have hz1 : z = 1 := by
    rw [← Subgroup.orderOf_coe, orderOf_eq_one_iff] at hord
    exact hord
  rw [hw, hz1, mul_one]
  exact ht'

theorem not_two_dvd_index_map_of_surjective {G P : Type*} [Group G] [Group P] {φ : G →* P}
    (hφ : Function.Surjective φ) {T : Subgroup G} (hT : ¬ 2 ∣ T.index) :
    ¬ 2 ∣ (T.map φ).index := by
  rw [← Subgroup.index_comap_of_surjective _ hφ, Subgroup.comap_map_eq]
  exact fun h => hT (h.trans (Subgroup.index_dvd_of_le le_sup_left))

theorem flagStabilizer_eq_upperTriangular {K : Type*} [Field K] {n : ℕ} {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hall : ∀ i, 1 ≤ i → i < n → i ∈ I) :
    flagStabilizer n K I = upperTriangular n K := by
  obtain ⟨hB, -⟩ := borel_overgroups (upperTriangular n K) le_rfl
  have hcuts : borelOvergroupCuts (upperTriangular n K) = I := by
    ext i
    constructor
    · rintro ⟨hi, hin, -⟩
      exact hall i hi hin
    · intro hiI
      obtain ⟨hi, hin⟩ := hI i hiI
      refine ⟨hi, hin, fun hmem => reflection_notMem_stabilizer (K := K) hi hin ?_⟩
      exact mem_flagStabilizer.mp (upperTriangular_le_flagStabilizer {i} hmem) i rfl
  rw [← hcuts]
  exact hB.symm

theorem proj_conj_mem_map_iff {K : Type*} [Field K] {n : ℕ} (I : Set ℕ)
    (g y : SpecialLinearGroup (Fin n) K) :
    proj n K (g * y * g⁻¹) ∈ ((flagStabilizer n K I).map (proj n K)).map
        (MulAut.conj (proj n K g)).toMonoidHom ↔ y ∈ flagStabilizer n K I := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, map_mul, map_mul, map_inv]
  rw [show (proj n K g)⁻¹ * (proj n K g * proj n K y * (proj n K g)⁻¹) * proj n K g =
    proj n K y by group]
  constructor
  · rintro ⟨q, hq, hqy⟩
    have hs : q⁻¹ * y ∈ scalars n K := proj_eq_proj_iff.mp hqy
    simpa using Subgroup.mul_mem _ hq (scalars_le_flagStabilizer n K I hs)
  · exact fun hy => ⟨y, hy, rfl⟩

theorem map_perfectJoin_comap_eq {G H : Type*} [Group G] [Group H] (σ : G →* H)
    (hker : σ.ker ≤ Subgroup.center G) {J : Subgroup H} (hJ : J ≤ σ.range) :
    (ParabPrime.perfectJoin (J.comap σ)).map σ = ParabPrime.perfectJoin J := by
  refine le_antisymm (ParabPrime.le_perfectJoin ?_ ?_) ?_
  · exact Subgroup.map_le_iff_le_comap.mpr (ParabPrime.perfectJoin_le _)
  · rw [← Subgroup.map_commutator, ParabPrime.perfectJoin_perfect]
  · obtain ⟨W, hW, hWle, hWmap⟩ := ParabPrime.exists_perfect_map_eq σ hker
      (ParabPrime.perfectJoin_perfect J) ((ParabPrime.perfectJoin_le J).trans hJ)
    rw [← hWmap]
    refine Subgroup.map_mono (ParabPrime.le_perfectJoin (fun x hx => ?_) hW)
    exact ParabPrime.perfectJoin_le J (hWle hx)

end ToralCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique
  CFSG.GH74.Generic ToralCensus in
theorem exists_comap_eq_flagStabilizer {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K)
    {ρ : SpecialLinearGroup (Fin n) K →* ↥L} (hρs : Function.Surjective ρ)
    (hρ : ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g) (hJ : IsParabolicTwo L J) :
    ∃ (σ : SpecialLinearGroup (Fin n) K →* ↥L)
      (e' : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K) (I : Set ℕ),
      Function.Surjective σ ∧ (∀ g, e' (QuotientGroup.mk (σ g)) = proj n K g) ∧
      (∀ i ∈ I, 1 ≤ i ∧ i < n) ∧ (J.subgroupOf L).comap σ = flagStabilizer n K I ∧
      (J ≠ L → I.Nonempty) ∧
      ((∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
        ∃ i, 1 ≤ i ∧ i < n ∧ i ∉ I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJL, T, ⟨hTL, hT2, hTi⟩, hTJ⟩ := hJ
  set φ := centralQuotientMap e with hφdef
  have hφs := centralQuotientMap_surjective e
  have hφker := centralQuotientMap_ker e
  set T' := T.subgroupOf L with hT'
  set J' := J.subgroupOf L with hJ'
  have hT'2 : IsPGroup 2 T' := hT2.comap_of_injective L.subtype L.subtype_injective
  have hNT : Subgroup.normalizer (T' : Set ↥L) =
      (Subgroup.normalizer (T : Set Y)).comap L.subtype :=
    (Subgroup.comap_normalizer_eq_of_le_range (by rwa [Subgroup.range_subtype])).symm
  have hNJ : Subgroup.normalizer (T' : Set ↥L) ≤ J' := fun x hx => by
    rw [hNT] at hx
    exact hTJ ⟨x.2, hx⟩
  have hZJ : φ.ker ≤ J' := hφker ▸ (Subgroup.center_le_normalizer _).trans hNJ
  have hJcomap : (J'.map φ).comap φ = J' := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hZJ]
  have hNcomap := comap_normalizer_map_eq hφker.le (hφker ▸ hodd) hT'2
  set S := (hT'2.map φ).toSylow (not_two_dvd_index_map_of_surjective hφs hTi) with hS
  have hScoe : (S : Subgroup (projectiveSL n K)) = T'.map φ := IsPGroup.toSylow_coe _ _
  have hNS : Subgroup.normalizer ((S : Subgroup (projectiveSL n K)) : Set (projectiveSL n K)) ≤
      J'.map φ := by
    intro y hy
    obtain ⟨x, rfl⟩ := hφs y
    rw [hScoe] at hy
    have hx : x ∈ (Subgroup.normalizer ((T'.map φ : Subgroup _) : Set _)).comap φ := hy
    rw [hNcomap] at hx
    exact ⟨x, hNJ hx, rfl⟩
  obtain ⟨gb, I, hI, hNB, hJI⟩ := LinearThreeKit.exists_eq_map_conj_flagStabilizer 2 hn S _ hNS
  obtain ⟨g, rfl⟩ := proj_surjective n K gb
  have hσφ : ∀ y, φ (ρ (MulAut.conj g y)) = proj n K (g * y * g⁻¹) := fun y => by
    rw [hφdef, centralQuotientMap_apply, hρ, MulAut.conj_apply]
  have hcomap : J'.comap (ρ.comp (MulAut.conj g).toMonoidHom) = flagStabilizer n K I := by
    ext y
    rw [Subgroup.mem_comap, ← hJcomap, Subgroup.mem_comap, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, hσφ, hJI, proj_conj_mem_map_iff]
  refine ⟨ρ.comp (MulAut.conj g).toMonoidHom, e.trans (MulAut.conj (proj n K g)⁻¹), I,
    hρs.comp (MulAut.conj g).surjective, fun y => ?_, hI, hcomap, ?_, ?_⟩
  · have h := hσφ y
    rw [hφdef, centralQuotientMap_apply] at h
    change (MulAut.conj (proj n K g)⁻¹) (e (QuotientGroup.mk (ρ (MulAut.conj g y)))) = _
    rw [h, MulAut.conj_apply, map_mul, map_mul, map_inv]
    group
  · intro hne
    by_contra hI0
    rw [Set.not_nonempty_iff_eq_empty] at hI0
    refine hne (le_antisymm hJL fun l hl => ?_)
    obtain ⟨y, hy⟩ := (hρs.comp (MulAut.conj g).surjective) ⟨l, hl⟩
    have hmem : y ∈ J'.comap (ρ.comp (MulAut.conj g).toMonoidHom) := by
      rw [hcomap, hI0, flagStabilizer_empty]
      exact Subgroup.mem_top y
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hmem
    rw [Function.comp_apply] at hy
    rw [hy] at hmem
    exact hmem
  · intro hnb
    by_contra hall
    push Not at hall
    have hQB := flagStabilizer_eq_upperTriangular (K := K) hI hall
    rw [hQB] at hJI
    have hJN : J'.map φ = Subgroup.normalizer ((S : Subgroup (projectiveSL n K)) :
        Set (projectiveSL n K)) := by
      rw [hJI, hNB]
      rfl
    refine hnb T ⟨hTL, hT2, hTi⟩ (le_antisymm (fun y hy => ⟨hJL hy, ?_⟩) hTJ)
    have hy' : (⟨y, hJL hy⟩ : ↥L) ∈ J' := hy
    rw [← hJcomap, hJN, hScoe, hNcomap, hNT] at hy'
    exact hy'

end CFSG.AGLEmbedding
