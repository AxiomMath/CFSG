module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

theorem card_comap_mk' {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (V : Subgroup (H ⧸ N)) :
    Nat.card (V.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card V := by
  have hNV : N ≤ V.comap (QuotientGroup.mk' N) := by
    intro n hn
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have h1 := relIndex_mul_card N (V.comap (QuotientGroup.mk' N))
  rw [inf_eq_left.mpr hNV] at h1
  have h2 : N.relIndex (V.comap (QuotientGroup.mk' N)) = Nat.card V := by
    have h := relIndex_comap (H := (⊥ : Subgroup (H ⧸ N))) (QuotientGroup.mk' N)
      (V.comap (QuotientGroup.mk' N))
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk', map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N), relIndex_bot_left] at h
    exact h
  rw [← h1, h2, mul_comm]

theorem pPrimeCore_quotient_assemblyOddCore_eq_bot (H : Type*) [Group H] [Finite H] :
    CFSG.pPrimeCore 2 (H ⧸ CFSG.Assembly.oddCore H) = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro V hV hcop
  set N := CFSG.Assembly.oddCore H
  have hodd : Odd (Nat.card (V.comap (QuotientGroup.mk' N))) := by
    rw [card_comap_mk']
    exact (odd_card_assemblyOddCore H).mul (Nat.coprime_two_left.mp hcop)
  have hle : V.comap (QuotientGroup.mk' N) ≤ N := le_assemblyOddCore (hV.comap _) hodd
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N v
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hle hv

variable {G : Type} [Group G]

theorem oUpperTwoPrime_le (X : Subgroup G) : oUpperTwoPrime X ≤ X :=
  (closure_le _).mpr fun _ hx => hx.1

theorem mem_oUpperTwoPrime {X : Subgroup G} {x : G} (hx : x ∈ X) {n : ℕ}
    (hn : x ^ 2 ^ n = 1) : x ∈ oUpperTwoPrime X :=
  subset_closure ⟨hx, n, hn⟩

theorem map_conj_oUpperTwoPrime_le {X : Subgroup G} {w : G}
    (hw : w ∈ normalizer (X : Set G)) :
    (oUpperTwoPrime X).map (MulAut.conj w).toMonoidHom ≤ oUpperTwoPrime X := by
  rw [oUpperTwoPrime, MonoidHom.map_closure]
  refine closure_mono ?_
  rintro _ ⟨x, ⟨hx, n, hn⟩, rfl⟩
  refine ⟨(mem_normalizer_iff.mp hw x).mp hx, n, ?_⟩
  simp [MulAut.conj_apply, conj_pow, hn]

theorem normalizer_le_normalizer_oUpperTwoPrime [Finite G] (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (oUpperTwoPrime X : Set G) := fun _ hw =>
  mem_normalizer_of_map_conj_le (map_conj_oUpperTwoPrime_le hw)

theorem twoPrimeLayerIn_le (K : Subgroup G) : twoPrimeLayerIn K ≤ K :=
  map_subtype_le _

theorem oddCoreIn_le_twoPrimeLayerIn (K : Subgroup G) : oddCoreIn K ≤ twoPrimeLayerIn K := by
  refine map_mono fun x hx => ?_
  rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

theorem twoPrimeLayerIn_eq_oddCoreIn_iff (K : Subgroup G) :
    twoPrimeLayerIn K = oddCoreIn K ↔ CFSG.layer (K ⧸ CFSG.Assembly.oddCore K) = ⊥ := by
  have hker : (⊥ : Subgroup (K ⧸ CFSG.Assembly.oddCore K)).comap
      (QuotientGroup.mk' (CFSG.Assembly.oddCore K)) = CFSG.Assembly.oddCore K := by
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
  rw [twoPrimeLayerIn, oddCoreIn, (map_injective K.subtype_injective).eq_iff]
  constructor
  · intro h
    apply comap_injective (QuotientGroup.mk'_surjective (CFSG.Assembly.oddCore K))
    rw [h, hker]
  · intro h
    rw [h, hker]

theorem card_twoPrimeLayerIn (K : Subgroup G) :
    Nat.card (twoPrimeLayerIn K) = Nat.card (CFSG.Assembly.oddCore K) *
      Nat.card (CFSG.layer (K ⧸ CFSG.Assembly.oddCore K)) := by
  rw [twoPrimeLayerIn, card_map_of_injective K.subtype_injective, card_comap_mk']

theorem le_normalizer_twoPrimeLayerIn (K : Subgroup G) :
    K ≤ normalizer (twoPrimeLayerIn K : Set G) := by
  have : (CFSG.layer (K ⧸ CFSG.Assembly.oddCore K)).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := K ⧸ CFSG.Assembly.oddCore K)
    infer_instance
  have : ((CFSG.layer (K ⧸ CFSG.Assembly.oddCore K)).comap
      (QuotientGroup.mk' (CFSG.Assembly.oddCore K))).Normal :=
    Subgroup.Normal.comap inferInstance _
  exact le_normalizer_map_subtype_of_normal K _

variable [Finite G]

theorem exists_sylow_map {K R : Subgroup G} (hR : IsSylowOf 2 R K) :
    ∃ S : Sylow 2 (K ⧸ CFSG.Assembly.oddCore K), (S : Subgroup (K ⧸ CFSG.Assembly.oddCore K)) =
      (R.subgroupOf K).map (QuotientGroup.mk' (CFSG.Assembly.oddCore K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hR.exists_sylow_eq_subgroupOf
  exact ⟨Q.mapSurjective (QuotientGroup.mk'_surjective _), by rw [Sylow.coe_mapSurjective, hQ]⟩

omit [Finite G] in
theorem mem_sup_of_mk_mem {K R : Subgroup G} {k : G} (hk : k ∈ K)
    (h : QuotientGroup.mk' (CFSG.Assembly.oddCore K) ⟨k, hk⟩ ∈
      (R.subgroupOf K).map (QuotientGroup.mk' (CFSG.Assembly.oddCore K))) :
    k ∈ oddCoreIn K ⊔ R := by
  obtain ⟨r, hr, hrk⟩ := h
  have hmem : r⁻¹ * ⟨k, hk⟩ ∈ CFSG.Assembly.oddCore K := QuotientGroup.eq.mp hrk
  have hk' : k = (r : G) * ((r⁻¹ * ⟨k, hk⟩ : K) : G) := by simp
  rw [hk']
  exact mul_mem (mem_sup_right (mem_subgroupOf.mp hr)) (mem_sup_left ⟨_, hmem, rfl⟩)

theorem twoElements_le_of_layer_eq_bot {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRe : IsElemAbelian 2 R) (hL : CFSG.layer (K ⧸ CFSG.Assembly.oddCore K) = ⊥) :
    ∀ k ∈ K, ∀ n : ℕ, k ^ 2 ^ n = 1 → k ∈ oddCoreIn K ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Assembly.oddCore K with hN
  obtain ⟨S, hS⟩ := exists_sylow_map hR
  have hchar : centralizer (CFSG.pCore 2 (K ⧸ N) : Set (K ⧸ N)) ≤ CFSG.pCore 2 (K ⧸ N) :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ 2
      (pPrimeCore_quotient_assemblyOddCore_eq_bot K) hL
  have : (CFSG.pCore 2 (K ⧸ N)).Normal := CFSG.pCore_normal (p := 2)
  have hPS : CFSG.pCore 2 (K ⧸ N) ≤ S := (CFSG.pCore_isPGroup (p := 2)).le_sylow_of_normal S
  have hScomm : ∀ x ∈ (S : Subgroup (K ⧸ N)), ∀ y ∈ (S : Subgroup (K ⧸ N)), x * y = y * x := by
    rw [hS]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have h := congrArg Subtype.val (hRe.1.is_comm.comm ⟨a, mem_subgroupOf.mp ha⟩
      ⟨b, mem_subgroupOf.mp hb⟩)
    simp only [coe_mul] at h
    exact Subtype.ext (by simpa using h)
  have hSP : (S : Subgroup (K ⧸ N)) ≤ CFSG.pCore 2 (K ⧸ N) := by
    refine le_trans (fun x hx => ?_) hchar
    rw [mem_centralizer_iff]
    intro y hy
    exact hScomm y (hPS hy) x hx
  have hSn : (S : Subgroup (K ⧸ N)).Normal := by
    rw [le_antisymm hSP hPS]
    infer_instance
  intro k hk n hkn
  apply mem_sup_of_mk_mem hk
  rw [← hS]
  have hz := isPGroup_zpowers_of_pow_eq_one
    (x := QuotientGroup.mk' N (⟨k, hk⟩ : K)) (n := n) (by
      rw [← map_pow]
      have : (⟨k, hk⟩ : K) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hkn)
      rw [this, map_one])
  have heq := S.is_maximal' (hz.to_sup_of_normal_right S.isPGroup') le_sup_right
  rw [← heq]
  exact mem_sup_left (mem_zpowers _)

theorem twoElements_le_of_sq_mem {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hsq : ∀ k ∈ oUpperTwoPrime K, k ^ 2 ∈ oddCoreIn K) :
    ∀ k ∈ K, ∀ n : ℕ, k ^ 2 ^ n = 1 → k ∈ oddCoreIn K ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Assembly.oddCore K with hN
  obtain ⟨S, hS⟩ := exists_sylow_map hR
  set M := ((oUpperTwoPrime K).subgroupOf K).map (QuotientGroup.mk' N) with hM
  have hMn : M.Normal := by
    have : ((oUpperTwoPrime K).subgroupOf K).Normal :=
      (normal_subgroupOf_iff_le_normalizer (oUpperTwoPrime_le K)).mpr
        ((le_normalizer).trans (normalizer_le_normalizer_oUpperTwoPrime K))
    exact this.map _ (QuotientGroup.mk'_surjective N)
  have hMp : IsPGroup 2 M := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hk2 : k ^ 2 ∈ N := by
      obtain ⟨y, hy, hyk⟩ := hsq _ hk
      have : y = k ^ 2 := Subtype.ext (by simpa using hyk)
      exact this ▸ hy
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk2
  have hMS := hMp.le_sylow_of_normal S
  intro k hk n hkn
  apply mem_sup_of_mk_mem hk
  rw [← hS]
  exact hMS ⟨⟨k, hk⟩, mem_oUpperTwoPrime hk hkn, rfl⟩

theorem false_of_pRank_twoPrimeLayerIn_eq_one {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRe : IsElemAbelian 2 R) (hne : twoPrimeLayerIn K ≠ oddCoreIn K)
    (h1 : Open.pRank 2 (twoPrimeLayerIn K) = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := CFSG.layer (K ⧸ CFSG.Assembly.oddCore K) with hL
  have hL1 : L ≠ ⊥ := fun h => hne ((twoPrimeLayerIn_eq_oddCoreIn_iff K).mpr h)
  have : Nontrivial L := (nontrivial_iff_ne_bot L).mpr hL1
  have : Group.IsPerfect L := CFSG.LocalCores.layer_isPerfect
  have h4L : 2 ^ 2 ∣ Nat.card L := by simpa using four_dvd_card_of_isPerfect (Q := L)
  have h4 : 2 ^ 2 ∣ Nat.card (twoPrimeLayerIn K) := by
    rw [card_twoPrimeLayerIn]
    exact h4L.mul_left _
  have hP : IsSylowOf 2 (R ⊓ twoPrimeLayerIn K) (twoPrimeLayerIn K) :=
    hR.inf_of_le_normalizer (twoPrimeLayerIn_le K) (le_normalizer_twoPrimeLayerIn K)
  have h4P := pow_dvd_card_of_isSylowOf hP h4
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP.isPGroup
  rw [hm] at h4P
  have hm2 : 2 ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h4P
  have hle := CFSG.SectionRank.le_pRank one_lt_two inf_le_right (IsElemAbelian.mono hRe inf_le_left)
    hm
  omega

end CFSG.ComponentClassification.AS76b
