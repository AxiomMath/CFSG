module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroLift
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneLiePerfect
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroChar

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.pow_eq_one_of_d1LiftX_decomp (hExp : KFactSmallSylowExp)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i) : ∀ r ∈ R, r ^ p = 1 := by
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzp1 : z ^ p = 1 := by rw [← hz.2.1]; exact pow_orderOf_eq_one z
  intro r hr
  obtain ⟨t, ht, i, rfl⟩ := hdec r hr
  have hc : Commute t (z ^ i) := Commute.pow_right
    (show Commute t z from Subgroup.mem_centralizer_singleton_iff.mp
      (hRC (d1LiftX_le p H R K ht))) i
  rw [hc.mul_pow, hd.pow_eq_one_of_mem_d1LiftX hExp ht, ← pow_mul, mul_comm, pow_mul, hzp1,
    one_pow, one_mul]

theorem D1OneSmallData.fusion_count (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hexpR : ∀ r ∈ R, r ^ p = 1) :
    p ∣ (fusionSet R z ∩ (d1LiftX p H R K : Set G)).ncard + (p - 1) *
      (1 + ({t | t ∈ d1LiftX p H R K ∧ z * t ∈ fusionSet R z} \ {1}).ncard) ∧
    D1InvSubset p H R K z (fusionSet R z ∩ (d1LiftX p H R K : Set G)) ∧
    D1InvSubset p H R K z ({t | t ∈ d1LiftX p H R K ∧ z * t ∈ fusionSet R z} \ {1}) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set T := d1LiftX p H R K with hT
  have hTR : T ≤ R := d1LiftX_le p H R K
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzR : z ∈ R := hz.1
  have hzp : orderOf z = p := hz.2.1
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzp; exact hp.one_lt.ne hzp
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  obtain ⟨hzT, -⟩ := hd.d1LiftX_facts hz
  obtain ⟨x, hxP, hxN, hxR, -⟩ := hd.exists_moving_elt hz hB0
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
  have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpdvd : p ∣ (fusionSet R z).ncard := p_dvd_ncard_fusionSet hzp hxN hxk hxR
    (fun y hy hyz hyk => hd.mem_of_mem_normalizer_of_commute hB0 hy hyz hyk)
  have hcount := ncard_fusionSet_eq hp hTR hzR hzT hzp hRz hexpR hdec
  set O' : Set G := {t | t ∈ T ∧ z * t ∈ fusionSet R z} with hO'
  have h1O' : (1 : G) ∈ O' := ⟨T.one_mem, by rw [mul_one]; exact self_mem_fusionSet hz1⟩
  have hO'card : O'.ncard = 1 + (O' \ {1}).ncard := by
    rw [add_comm]
    exact (Set.ncard_sdiff_singleton_add_one h1O').symm
  refine ⟨?_, ?_, ?_⟩
  · rw [← hO'card, ← hcount]
    exact hpdvd
  · exact ⟨fun w hw => ⟨hw.2, hw.1.1⟩, fun n hn hnz hnT w hw =>
      ⟨conj_mem_fusionSet hn hw.1, hnT w hw.2⟩⟩
  · refine ⟨fun t ht => ⟨ht.1.1, ht.2⟩, fun n hn hnz hnT t ht => ⟨⟨hnT t ht.1.1, ?_⟩, ?_⟩⟩
    · have h1 : z * (n * t * n⁻¹) = n * (z * t) * n⁻¹ := by
        calc z * (n * t * n⁻¹) = (n * z * n⁻¹) * (n * t * n⁻¹) := by rw [hnz]
          _ = n * (z * t) * n⁻¹ := by group
      rw [h1]
      exact conj_mem_fusionSet hn ht.1.2
    · intro h
      apply ht.2
      rw [Set.mem_singleton_iff] at h ⊢
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group

omit [Finite G] in
theorem mem_fusionSet_of_not_mem_of_mul {R T : Subgroup G} {z : G} (hTR : T ≤ R) (hzR : z ∈ R)
    (hRz : ∀ r ∈ R, r * z = z * r) (hexpR : ∀ r ∈ R, r ^ 3 = 1)
    (hdec : ∀ r ∈ R, ∃ t ∈ T, ∃ i : ℕ, r = t * z ^ i)
    (hzt : ∀ t ∈ T, z * t ∈ fusionSet R z) :
    ∀ r ∈ R, r ∉ T → r ∈ fusionSet R z := by
  have hz3 : z ^ 3 = 1 := hexpR z hzR
  intro r hr hrT
  obtain ⟨t, ht, i, rfl⟩ := hdec r hr
  have hct : Commute t z := hRz t (hTR ht)
  have hzi : z ^ i = z ^ (i % 3) := by
    conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hz3, one_pow, mul_one]
  have hi3 : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [hzi] at hrT ⊢
  interval_cases h : i % 3
  · exact absurd (by simpa using ht) hrT
  · rw [pow_one, hct.eq]
    exact hzt t ht
  · have hsq : (t * z ^ 2) ^ 2 = z * t ^ 2 := by
      have hc2 : Commute t (z ^ 2) := hct.pow_right 2
      rw [hc2.mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hz3, one_mul,
        pow_one, ← hct.pow_left 2 |>.eq]
    have hmem : z * t ^ 2 ∈ fusionSet R z := hzt _ (Subgroup.pow_mem _ ht 2)
    have hr4 : ((t * z ^ 2) ^ 2) ^ 2 = t * z ^ 2 := by
      have h3 : (t * z ^ 2) ^ 3 = 1 := hexpR _ (R.mul_mem (hTR ht) (R.pow_mem hzR 2))
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    rw [← hr4, hsq]
    refine pow_mem_fusionSet hmem ?_
    rw [← hsq, hr4]
    intro h1
    exact hrT (h1 ▸ Subgroup.one_mem _)

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem D1OneSmallData.coprime_card_of_perfect_of_eq (hd : D1OneSmallData p P M H R Rbar K)
    (hI : D1SmallIa p H K) {T₁ : Sylow p K}
    (hY : (d1X0 p M H).subgroupOf K = GLBCore p 1 (T₁ : Subgroup K))
    (hout : Group.IsSolvable (Outer K))
    (hs : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)))
    {U : Subgroup G} (hU : U ≤ H ⊓ M) (hUp : ⁅U, U⁆ = U) : p.Coprime (Nat.card U) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set X₀ := ((H ⊓ M).subgroupOf H).map π
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨-, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hcomap : X₀.comap K.subtype = GLBCore p 1 (T₁ : Subgroup K) := hY
  have hKX : K ⊓ X₀ = (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype := by
    rw [← hcomap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  have hKXs : Group.IsSolvable (K ⊓ X₀ : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hKX]
    exact Group.isSolvable_of_surjective (f := ((GLBCore p 1 (T₁ : Subgroup K)).equivMapOfInjective
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
    le_sup_centralizer_of_isPerfect (Subgroup.isPerfect_iff.mpr hUb) hout
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
  have hUbφ : Ub.map φ = ⊥ := by
    by_contra hne'
    have : Nontrivial (Ub.map φ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne'
    have : Group.IsPerfect (Ub.map φ) :=
      Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hUb])
    exact Group.IsPerfect.not_isSolvable _ hsolU
  have hUbC : Ub ≤ C := by
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hUbφ
  have hUb1 : Ub = ⊥ := hd.cfg.red.eq_bot_of_le_centralizer_of_perfect hd.comp hKX₀ hI hUbC hUb
  have hUN : U ≤ GLBPrimeCore p H := by
    intro u hu
    have h1 : π ⟨u, hUH hu⟩ ∈ Ub := ⟨⟨u, hUH hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hUb1, Subgroup.mem_bot] at h1
    exact (mk'_primeComplementCore_eq_one_iff p _).mp h1
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hUN) (glbPrimeCore_coprime p H)

end CFSG.AGLEmbedding
