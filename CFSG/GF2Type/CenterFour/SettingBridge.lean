module

public import CFSG.GF2Type.CenterFour.Setting
public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions
import CFSG.GF2Type.CenterFour.BridgeLinear
import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGGF2CenterFourNonemptyFusion

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem mem_pCore_of_central {M : Subgroup G} {z : G} (hzM : z ∈ M) (hz : orderOf z = 2)
    (hcent : ∀ m ∈ M, m * z = z * m) : (⟨z, hzM⟩ : M) ∈ CFSG.pCore 2 M := by
  set x : M := ⟨z, hzM⟩ with hx
  have hxc : ∀ m : M, Commute m x := fun m => Subtype.ext (hcent m m.2)
  have hord : orderOf x = 2 := by
    rw [← orderOf_injective M.subtype M.subtype_injective x]
    exact hz
  have hK : (Subgroup.zpowers x).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g (x ^ k) := (hxc g).zpow_right k
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hP : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hle : Subgroup.zpowers x ≤ CFSG.pCore 2 M := le_sSup ⟨hK, hP⟩
  exact hle (Subgroup.mem_zpowers x)

theorem coreAt_le_centralizer (z : G) : coreAt z ≤ centralizer ({z} : Set G) := by
  intro x hx
  unfold coreAt CFSG.inSubgroup at hx
  obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact p.2

theorem self_mem_coreAt {z : G} (hz : orderOf z = 2) : z ∈ coreAt z := by
  have hzM : z ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcent : ∀ m ∈ centralizer ({z} : Set G), m * z = z * m :=
    fun m hm => Subgroup.mem_centralizer_singleton_iff.mp hm
  unfold coreAt CFSG.inSubgroup
  exact Subgroup.mem_map.mpr ⟨⟨z, hzM⟩, mem_pCore_of_central hzM hz hcent, rfl⟩

theorem self_mem_centerAt {z : G} (hz : orderOf z = 2) : z ∈ centerAt z := by
  have hzQ : z ∈ coreAt z := self_mem_coreAt hz
  refine Subgroup.mem_map.mpr ⟨⟨z, hzQ⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (coreAt_le_centralizer z g.2)

end Helpers

section Transport

variable {H K : Type} [Group H] [Group K]

theorem natCard_comap_eq {ψ : H →* K} (hψ : Function.Injective ψ) {U : Subgroup K}
    (hU : U ≤ ψ.range) : Nat.card (U.comap ψ) = Nat.card U :=
  Nat.card_congr (((U.comap ψ).equivMapOfInjective ψ hψ).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hU))).toEquiv

theorem isElemAbelian_comap {ψ : H →* K} (hψ : Function.Injective ψ) {U : Subgroup K}
    (hU : CFSG.Open.IsElemAbelian 2 U) : CFSG.Open.IsElemAbelian 2 (U.comap ψ) := by
  obtain ⟨hcomm, hexp⟩ := hU
  have hC : IsMulCommutative (U.comap ψ) := by
    refine ⟨⟨fun a b => Subtype.ext (hψ ?_)⟩⟩
    simp only [Subgroup.coe_mul, map_mul]
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm
      ⟨ψ (a : H), a.2⟩ ⟨ψ (b : H), b.2⟩)
  refine ⟨hC, fun x hx => hψ ?_⟩
  simpa [map_pow] using hexp (ψ x) hx

theorem comap_inf_eq_bot {ψ : H →* K} (hψ : Function.Injective ψ) {U W : Subgroup K}
    {V : Subgroup H} (hWV : ∀ x ∈ V, ψ x ∈ W) (hUW : U ⊓ W = ⊥) :
    U.comap ψ ⊓ V = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxV⟩
  have h1 : ψ x ∈ U ⊓ W := ⟨hxU, hWV x hxV⟩
  rw [hUW, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  apply hψ
  rw [h1, map_one]

theorem map_center_le {P : Type} [Group P] {ψ : P →* K} {W : Subgroup K}
    (hψW : ∀ p, ψ p ∈ W) (hsurj : ∀ g ∈ W, ∃ p, ψ p = g) :
    ∀ x ∈ center P, ψ x ∈ (center W).map W.subtype := by
  intro x hx
  refine Subgroup.mem_map.mpr ⟨⟨ψ x, hψW x⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  rintro ⟨g, hg⟩
  obtain ⟨p, rfl⟩ := hsurj g hg
  apply Subtype.ext
  show ψ p * ψ x = ψ x * ψ p
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx p]

end Transport

section Bridge

open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def embAt (z : G) : CFSG.pCore 2 (centralizer ({z} : Set G)) →* G :=
  (centralizer ({z} : Set G)).subtype.comp (CFSG.pCore 2 (centralizer ({z} : Set G))).subtype

theorem embAt_injective (z : G) : Function.Injective (embAt z) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem embAt_mem_coreAt (z : G) (p : CFSG.pCore 2 (centralizer ({z} : Set G))) :
    embAt z p ∈ coreAt z := by
  unfold coreAt CFSG.inSubgroup
  exact Subgroup.mem_map.mpr ⟨p.1, p.2, rfl⟩

theorem exists_embAt_eq {z g : G} (hg : g ∈ coreAt z) : ∃ p, embAt z p = g := by
  unfold coreAt CFSG.inSubgroup at hg
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨⟨p, hp⟩, rfl⟩

theorem embAt_center (z : G) :
    ∀ x ∈ center (CFSG.pCore 2 (centralizer ({z} : Set G))), embAt z x ∈ centerAt z :=
  map_center_le (fun p => embAt_mem_coreAt z p) (fun _ hg => exists_embAt_eq hg)

theorem isCyclic_center_pCore {z : G} (hZ : IsCyclic (centerAt z)) :
    IsCyclic (center (CFSG.pCore 2 (centralizer ({z} : Set G)))) := by
  let f : center (CFSG.pCore 2 (centralizer ({z} : Set G))) →* G :=
    (embAt z).comp (center (CFSG.pCore 2 (centralizer ({z} : Set G)))).subtype
  let g : center (CFSG.pCore 2 (centralizer ({z} : Set G))) →* centerAt z :=
    f.codRestrict (centerAt z) (fun x => embAt_center z x.1 x.2)
  refine isCyclic_of_injective g ?_
  intro a b h
  have h2 : ((g a : centerAt z) : G) = ((g b : centerAt z) : G) := by rw [h]
  have h3 : embAt z (a : CFSG.pCore 2 (centralizer ({z} : Set G))) =
      embAt z (b : CFSG.pCore 2 (centralizer ({z} : Set G))) := h2
  exact Subtype.ext (embAt_injective z h3)

theorem bounds_of_bridge {P : Type} [Group P] [Finite P] [Fact (Nat.Prime 2)]
    [CFSG.IsElementaryAbelian 2 (P ⧸ center P)] {z : G} {c : P} {ψ : P →* G}
    (hψ : Function.Injective ψ) (hψc : ψ c = z) (hz1 : z ≠ 1)
    (hsurj : ∀ g ∈ coreAt z, ∃ p, ψ p = g) (hcen : ∀ x ∈ center P, ψ x ∈ centerAt z)
    (hZ : IsCyclic (center P)) {v : ℕ}
    (b : LinearMap.BilinForm (ZMod 2) (Additive (P ⧸ center P)))
    (hrule : ∀ x y : P, ⁅x, y⁆ =
      c ^ (b (Additive.ofMul (x : P ⧸ center P)) (Additive.ofMul (y : P ⧸ center P))).val)
    (hdim : Module.finrank (ZMod 2) (Additive (P ⧸ center P)) = 2 * v)
    (hnd : b.Nondegenerate) (halt : b.IsAlt) :
    (∀ U : Subgroup G, U ≤ coreAt z → CFSG.Open.IsElemAbelian 2 U →
      Nat.card U ≤ 2 ^ (v + 1)) ∧
    (∀ U : Subgroup G, U ≤ coreAt z → CFSG.Open.IsElemAbelian 2 U → U ⊓ centerAt z = ⊥ →
      Nat.card U ≤ 2 ^ v) ∧
    (∀ (s : ℕ) (f : Fin s → G), (∀ i, f i ∈ coreAt z) →
      (∀ i j, i ≠ j → ⁅f i, f j⁆ = z) → s ≤ 2 * v + 1) := by
  have hc : c ≠ 1 := by
    intro h
    apply hz1
    rw [← hψc, h, map_one]
  have hrange : ∀ U : Subgroup G, U ≤ coreAt z → U ≤ ψ.range :=
    fun U hU x hx => MonoidHom.mem_range.mpr (hsurj x (hU hx))
  refine ⟨?_, ?_, ?_⟩
  · intro U hU hUe
    rw [← natCard_comap_eq hψ (hrange U hU)]
    exact card_le_of_elemAbelian b hrule hdim hnd hc hZ (isElemAbelian_comap hψ hUe)
  · intro U hU hUe hUZ
    rw [← natCard_comap_eq hψ (hrange U hU)]
    exact card_le_of_disjoint b hrule hdim hnd hc (isElemAbelian_comap hψ hUe)
      (comap_inf_eq_bot hψ hcen hUZ)
  · intro s f hf hpair
    choose f' hf' using fun i => hsurj (f i) (hf i)
    have hcomm : ∀ i j, i ≠ j → ⁅f' i, f' j⁆ = c := by
      intro i j hij
      apply hψ
      rw [map_commutatorElement, hf' i, hf' j, hψc]
      exact hpair i j hij
    exact card_le_of_pairwise b hrule hdim halt hc f' hcomm

theorem eq_one_or_eq_of_sq_one {z y : G} (huniq : ∀ y' ∈ centerAt z, orderOf y' = 2 → y' = z)
    (hy : y ∈ centerAt z) (hy2 : y ^ 2 = 1) : y = 1 ∨ y = z := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hy2) with h | h
  · exact Or.inl (orderOf_eq_one_iff.mp h)
  · exact Or.inr (huniq y hy h)

theorem sq_eq_of_bridge {P : Type} [Group P] [CFSG.IsElementaryAbelian 2 (P ⧸ center P)]
    {z : G} {ψ : P →* G} (hψW : ∀ p, ψ p ∈ coreAt z)
    (hsurj : ∀ g ∈ coreAt z, ∃ p, ψ p = g) (hcen : ∀ x ∈ center P, ψ x ∈ centerAt z)
    (hexp4 : ∀ x ∈ coreAt z, x ^ 4 = 1)
    (huniq : ∀ y ∈ centerAt z, orderOf y = 2 → y = z) :
    ∀ x ∈ coreAt z, x ^ 2 = 1 ∨ x ^ 2 = z := by
  intro x hx
  obtain ⟨p, rfl⟩ := hsurj x hx
  have hsq : ∀ y : P ⧸ center P, y ^ 2 = 1 := fun y =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 (P ⧸ center P)) y
  have hp2 : p ^ 2 ∈ center P := by
    have h := hsq (p : P ⧸ center P)
    rw [← QuotientGroup.mk_pow] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  have hy : ψ p ^ 2 ∈ centerAt z := by
    rw [← map_pow ψ p 2]
    exact hcen _ hp2
  have hy2 : (ψ p ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact hexp4 _ (hψW p)
  exact eq_one_or_eq_of_sq_one huniq hy hy2

theorem comm_eq_of_bridge {P : Type} [Group P] [CFSG.IsElementaryAbelian 2 (P ⧸ center P)]
    {z : G} {ψ : P →* G} (hsurj : ∀ g ∈ coreAt z, ∃ p, ψ p = g)
    {b : LinearMap.BilinForm (ZMod 2) (Additive (P ⧸ center P))}
    (hrule : ∀ x y : P, ψ ⁅x, y⁆ =
      z ^ (b (Additive.ofMul (x : P ⧸ center P)) (Additive.ofMul (y : P ⧸ center P))).val) :
    ∀ x ∈ coreAt z, ∀ y ∈ coreAt z, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z := by
  intro x hx y hy
  obtain ⟨p, rfl⟩ := hsurj x hx
  obtain ⟨q, rfl⟩ := hsurj y hy
  rw [← map_commutatorElement, hrule p q]
  have hk := ZMod.val_lt (b (Additive.ofMul (p : P ⧸ center P)) (Additive.ofMul (q : P ⧸ center P)))
  obtain h0 | h1 : (b (Additive.ofMul (p : P ⧸ center P))
      (Additive.ofMul (q : P ⧸ center P))).val = 0 ∨
      (b (Additive.ofMul (p : P ⧸ center P)) (Additive.ofMul (q : P ⧸ center P))).val = 1 := by
    omega
  · left
    rw [h0, pow_zero]
  · right
    rw [h1, pow_one]

theorem selfCentralizing_of_bridge {z : G} (hM : IsCharacteristicP 2 (centralizer ({z} : Set G))) :
    ∀ h ∈ centralizer ({z} : Set G), (∀ q ∈ coreAt z, h * q = q * h) → h ∈ coreAt z := by
  intro h hh hcomm
  have hmem : (⟨h, hh⟩ : centralizer ({z} : Set G)) ∈ centralizer
      ((CFSG.pCore 2 (centralizer ({z} : Set G)) : Subgroup (centralizer ({z} : Set G))) :
        Set (centralizer ({z} : Set G))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    exact (hcomm _ (embAt_mem_coreAt z ⟨x, hx⟩)).symm
  have hP := hM hmem
  unfold coreAt CFSG.inSubgroup
  exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩, hP, rfl⟩

theorem centerAt_transport {z : G} (hcyc : IsCyclic (center (coreAt z)))
    (hcard : Nat.card (center (coreAt z)) = 4) :
    IsCyclic (centerAt z) ∧ Nat.card (centerAt z) = 4 := by
  unfold centerAt
  refine ⟨?_, ?_⟩
  · let e := (center (coreAt z)).equivMapOfInjective (coreAt z).subtype
      (coreAt z).subtype_injective
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  · rw [Subgroup.card_map_of_injective (coreAt z).subtype_injective, hcard]

theorem wB_of_setEq {z : G} {Z M Q : Subgroup G} (hz : z ∈ Z) (hM : M = centralizer ({z} : Set G))
    (hset : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ ((M ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) =
      {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) :
    ∀ g : G, g⁻¹ * z * g ∈ centralizer (Z : Set G) → g⁻¹ * z * g ∈ Q := by
  intro g hg
  subst hM
  have hmem : g⁻¹ * z * g ∈ {w | ∃ g' : G, g'⁻¹ * z * g' = w} ∩
      ((centralizer ({z} : Set G) ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) := by
    refine ⟨⟨g, rfl⟩, Subgroup.mem_inf.mpr ⟨?_, hg⟩⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hg) z hz).symm
  rw [hset] at hmem
  exact hmem.2

theorem exists_fused_of_nonempty {z : G} {Q : Subgroup G}
    (hne : (({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z}).Nonempty) :
    ∃ g : G, g⁻¹ * z * g ∈ Q ∧ g⁻¹ * z * g ≠ z := by
  obtain ⟨w, ⟨⟨g, rfl⟩, hwQ⟩, hwz⟩ := hne
  exact ⟨g, hwQ, fun h => hwz (Set.mem_singleton_iff.mpr h)⟩

end Bridge

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem exists_central_c {z : G} (hz : orderOf z = 2) :
    ∃ c : CFSG.pCore 2 (centralizer ({z} : Set G)), embAt z c = z :=
  ⟨⟨⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩,
    mem_pCore_of_central (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hz
      (fun m hm => Subgroup.mem_centralizer_singleton_iff.mp hm)⟩, rfl⟩

end Assembly

theorem coreQ_eq_coreAt {G : Type} [Group G] [Finite G] {z : G}
    (hset : CFSG.Yardstones.M3aba7dc4b8a8.GF2RankFourSetting G z) :
    CFSG.Yardstones.M3aba7dc4b8a8.coreQ z = coreAt z := by
  obtain ⟨-, -, hchar, -, -, hMmax, hsymp, B, hB, hBM⟩ := hset
  have hchar' : IsCharacteristicPType G 2 := CFSG.GH74.isCharTwoType_iff.mp hchar
  obtain ⟨-, hFQ, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.gf2_witness_centralizer_and_rank (G := G) hchar'
      (M := centralizer ({z} : Set G)) (B := B) hMmax hsymp hB hBM rfl rfl
  exact hFQ

theorem exists_config {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (hset : CFSG.Yardstones.M3aba7dc4b8a8.GF2RankFourSetting G z)
    (hnex : ¬ IsExtraspecialPGroup 2 (CFSG.Yardstones.M3aba7dc4b8a8.coreQ z))
    (hexp : ∀ x ∈ CFSG.Yardstones.M3aba7dc4b8a8.coreQ z, x ^ 4 = 1) : ∃ n, Config z n := by
  have hQeq := coreQ_eq_coreAt hset
  have hnex' : ¬ IsExtraspecialPGroup 2 (coreAt z) := by rw [← hQeq]; exact hnex
  have hexp' : ∀ x ∈ coreAt z, x ^ 4 = 1 := by rw [← hQeq]; exact hexp
  obtain ⟨hnab, -, hchar, he, hz, hMmax, hsymp, B, hB, hBM⟩ := hset
  have hchar' : IsCharacteristicPType G 2 := CFSG.GH74.isCharTwoType_iff.mp hchar
  have he4 : 4 ≤ CFSG.twoLocalOddRank G := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank G]; exact he
  have he3 : 3 ≤ CFSG.twoLocalOddRank G := le_trans (by norm_num) he4
  obtain ⟨hZcyc, hZcard, -, -, -, -, v, hv4, hQv, -, hvuniq, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.gf2_center_four_width_at_least_four_at_rank_four (G := G)
      hchar' he4
      (M := centralizer ({z} : Set G)) (B := B) hMmax hsymp hB hBM rfl hnex' hexp' rfl
  obtain ⟨-, z3, -, -, hz3uniq, -, -, hEA, ⟨vF, ⟨-, hcardF, hfinF⟩, -⟩, b, hcomm, -, hAlt,
      hnd, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.gf2_fused_center_four_involution_image (G := G) hchar' he3
      (M := centralizer ({z} : Set G)) (B := B) hMmax hsymp hB hBM rfl hnex' hexp'
  obtain ⟨⟨z'', -, -, -, -, -, hMZ, -⟩, -, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.gf2_witness_centralizer_and_rank (G := G) hchar'
      (M := centralizer ({z} : Set G))
      (B := B) hMmax hsymp hB hBM rfl rfl
  obtain ⟨hne, -, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.gf2_center_four_nonempty_core_fusion (G := G) inferInstance
      hnab hchar' he4
    (M := centralizer ({z} : Set G)) (B := B) hMmax hsymp hB hBM rfl hnex' hexp'
    (Z := centerAt z) rfl (self_mem_centerAt hz) hz
  obtain ⟨z4, -, -, hz4uniq, hcyc4⟩ :=
    open CFSG.LocalAnalysis.GorensteinLyons in
    gf2_center_four_all_cyclic_root_images_and_weak_closure_obstruction (G := G) hchar' he3
      (M := centralizer ({z} : Set G)) (B := B) hMmax hsymp hB hBM rfl hnex' hexp'
      (centerAt z) rfl
  obtain ⟨_xE, _bb, _hxy, _hAlt, _hnd, _ιι, _hinj, _hh, hF⟩ := hcyc4
  obtain ⟨hWA, hWBset, -⟩ := hF _ rfl
  have hzz4 : z = z4 := hz4uniq z (self_mem_centerAt hz) hz
  subst z4
  have hzz3 : z = z3 := hz3uniq z (self_mem_centerAt hz) hz
  subst z3
  have hvF : vF = v := hvuniq vF hcardF
  rw [hvF] at hfinF
  have hcyc := centerAt_transport hZcyc hZcard
  have hMcharP : IsCharacteristicP 2 (centralizer ({z} : Set G)) := hchar' _ hMmax.1
  obtain ⟨c, hc_eq⟩ := exists_central_c hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    norm_num at hz
  haveI := hEA
  obtain ⟨hel, hdisj, hpair⟩ := bounds_of_bridge (c := c) (embAt_injective z) hc_eq hz1
    (fun g hg => exists_embAt_eq hg) (embAt_center z) (isCyclic_center_pCore hcyc.1) b
    (by intro x y; apply embAt_injective z; rw [map_pow, hc_eq]; exact hcomm x y) hfinF hnd hAlt
  have hsq := sq_eq_of_bridge (ψ := embAt z) (embAt_mem_coreAt z)
    (fun g hg => exists_embAt_eq hg) (embAt_center z) hexp' hz4uniq
  have hcommEq := comm_eq_of_bridge (ψ := embAt z) (fun g hg => exists_embAt_eq hg) hcomm
  have hself := selfCentralizing_of_bridge hMcharP
  have hWC := exists_fused_of_nonempty hne
  have hWB := wB_of_setEq (self_mem_centerAt hz) rfl hWBset
  refine ⟨v, ?_⟩
  exact
    { orderOf_eq := hz
      three_le := by omega
      mem_center := self_mem_centerAt hz
      center_cyclic := hcyc.1
      card_center := hcyc.2
      normalizer_center := hMZ.symm
      selfCentralizing := hself
      sq_eq := hsq
      comm_eq := hcommEq
      card_core := hQv
      card_elem_le := hel
      card_elem_le_of_disjoint := hdisj
      card_pairwise_le := hpair
      center_le_iff := hWA
      mem_core_of_centralizes := hWB
      exists_fused := hWC }

end CFSG.GF2Type.CenterFour
