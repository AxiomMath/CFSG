module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUHelp
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUGamma
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUOdd

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem card_map_of_isSylowTwoOf {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) {L T : Subgroup X} (hT : IsSylowTwoOf T L) (hLc : Nat.card (L.map f) = 20160) :
    Nat.card (T.map f) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := f.subgroupMap L with hψ
  set T' := T.subgroupOf L with hT'
  have hT'p : IsPGroup 2 T' := hT.2.1.comap_subtype
  let S₀ : Sylow 2 L := hT'p.toSylow hT.2.2
  let S₁ : Sylow 2 (L.map f) := S₀.mapSurjective (f.subgroupMap_surjective L)
  have hS₁ : Nat.card S₁ = 64 := by
    rw [Sylow.card_eq_multiplicity, hLc]
    have hf : Nat.factorization 20160 2 = 6 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [hf]
    norm_num
  have hS₁eq : ((S₁ : Subgroup (L.map f))).map (L.map f).subtype = T.map f := by
    change ((T'.map ψ)).map (L.map f).subtype = T.map f
    rw [Subgroup.map_map]
    have hc : (L.map f).subtype.comp ψ = f.comp L.subtype := by ext; rfl
    rw [hc, ← Subgroup.map_map, hT', Subgroup.map_subgroupOf_eq_of_le hT.1]
  rw [← hS₁eq, Subgroup.card_map_of_injective (L.map f).subtype_injective]
  exact hS₁

theorem exists_ne_comm_of_isQuasisimple {Q : Type*} [Group Q] (hQ : Open.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ :=
    ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.card_dvd_seventytwo (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData 3 P M H R Rbar K) (hL : IsLinThreeFour K)
    {Y : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hYX : Y ≤ d1X0 3 M H) (hYK : Y ≤ K) :
    Nat.card Y ∣ 72 := by
  obtain ⟨T₁, -, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE (Or.inl ⟨rfl, hL⟩)
  have h1 : Y.subgroupOf K ≤ CFSG.Open.GLBCore 3 1 (T₁ : Subgroup K) := by
    rw [← hY]
    exact Subgroup.comap_mono hYX
  have h2 := (Subgroup.card_dvd_of_le h1).trans (card_glbCore_dvd_of_isLinThreeFour hL T₁)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv] at h2

structure L34BlockFacts (M H L : Subgroup G) (K : Subgroup (H ⧸ primeComplementCore (G := H) 3))
    (φ : (↥H ⧸ CFSG.pCore 2 ↥H) →* (↥H ⧸ primeComplementCore (G := H) 3)) : Prop where
  map_eq : (barM H L).map φ = K
  card_map : Nat.card ((barM H L).map φ) = 20160
  ker_le : (φ.comp (barM H L).subtype).ker ≤ Subgroup.center (barM H L)
  le_ker : Subgroup.center (barM H L) ≤ (φ.comp (barM H L).subtype).ker
  quasisimple : Open.IsQuasisimple (barM H L)
  map_J : ((barM H (Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) ⊓ L)).map φ) ≤
    d1X0 3 M H ⊓ K
  J_le : barM H (Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) ⊓ L) ≤ barM H L
  ker_coprime : ∀ y, φ y = 1 → Nat.Coprime 3 (orderOf y)

theorem l34BlockFacts_of_map_eq {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    {L : Subgroup G}
    (hmap : (barM H L).map (twoPrimeMap H Nat.prime_three (by norm_num)) = K)
    (hcenter : Subgroup.center K = ⊥) (hcard : Nat.card K = 20160)
    (hNH : H ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M)
    (hLw : IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L)
    (hLW : ¬ barM H L ≤
      (primeComplementCore (G := H) 3).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :
    L34BlockFacts M H L K (twoPrimeMap H Nat.prime_three (by norm_num)) := by
  set φ := twoPrimeMap H Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2) with hφ
  have hLc : IsComponentOf (barM H L) ⊤ := hLw.component
  have hker : ¬ barM H L ≤ φ.ker := fun h =>
    hLW fun x hx => mem_map_of_twoPrimeMap_eq_one Nat.prime_three (by norm_num) (h hx)
  have hcard' : Nat.card ((barM H L).map φ) = 20160 := by rw [hmap]; exact hcard
  refine ⟨hmap, hcard', ker_restrict_le_center_of_isQuasisimple φ hLc.2.2 hker, ?_, hLc.2.2, ?_,
    ?_, ?_⟩
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hxK : φ x ∈ K := hmap ▸ Subgroup.mem_map_of_mem φ x.2
    have hc : (⟨φ x, hxK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨k, hk⟩
      rw [← hmap] at hk
      obtain ⟨y, hy, rfl⟩ := hk
      apply Subtype.ext
      have h1 : y * (x : ↥H ⧸ CFSG.pCore 2 ↥H) = x * y := by
        have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)
        simpa using this
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul, h1]
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  · rintro _ ⟨j, ⟨x, hx, rfl⟩, rfl⟩
    have hxG := Subgroup.mem_subgroupOf.mp hx
    refine ⟨?_, ?_⟩
    · refine ⟨x, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      exact hNH ▸ ⟨x.2, hxG.1⟩
    · rw [← hmap]
      exact ⟨_, ⟨x, Subgroup.mem_subgroupOf.mpr hxG.2, rfl⟩, rfl⟩
  · exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mp hx).2
  · intro y hy
    have hyW := mem_map_of_twoPrimeMap_eq_one Nat.prime_three (by norm_num) hy
    have hcop : Nat.Coprime 3 (Nat.card ((primeComplementCore (G := H) 3).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) :=
      (primeComplementCore_coprime 3).coprime_dvd_right (Subgroup.card_map_dvd _ _)
    have hord : orderOf y ∣ Nat.card ((primeComplementCore (G := H) 3).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) := by
      have := orderOf_dvd_natCard (⟨y, hyW⟩ : (primeComplementCore (G := H) 3).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
      rwa [Subgroup.orderOf_mk] at this
    exact hcop.coprime_dvd_right hord

theorem l34BlockFacts_of_unique {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (huniq : ∀ L' : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L' ⊤ → L' = K)
    (hcenter : Subgroup.center K = ⊥) (hcard : Nat.card K = 20160)
    (hNH : H ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M) {L : Subgroup G}
    (hLw : IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L)
    (hLW : ¬ barM H L ≤
      (primeComplementCore (G := H) 3).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :
    L34BlockFacts M H L K (twoPrimeMap H Nat.prime_three (by norm_num)) := by
  have hker : ¬ barM H L ≤ (twoPrimeMap H Nat.prime_three (by norm_num)).ker := fun h =>
    hLW fun x hx => mem_map_of_twoPrimeMap_eq_one Nat.prime_three (by norm_num) (h hx)
  exact l34BlockFacts_of_map_eq (huniq _ (isComponentOf_map_top_of_surj _
    (twoPrimeMap_surjective Nat.prime_three (by norm_num)) hLw.component hker)) hcenter hcard hNH
    hLw hLW

theorem D1OneSmallData.l34BlockFacts (hUE : KFactUPrimeExc) (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData 3 P M H R Rbar K) (hI : D1SmallIa 3 H K) (hL : IsLinThreeFour K)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) {L : Subgroup G}
    (hLw : IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L)
    (hLW : ¬ barM H L ≤
      (primeComplementCore (G := H) 3).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :
    L34BlockFacts M H L K (twoPrimeMap H Nat.prime_three (by norm_num)) :=
  l34BlockFacts_of_unique hI hd.center ((hO K).2.1 hL) (hd.inf_normalizer_twoCore_inf hUE rfl hL hS)
    hLw hLW

end CFSG.AGLEmbedding
