module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Cert
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFieldFusion
public import CFSG.Goldschmidt75.Transfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open scoped commutatorElement

theorem card_Z0 :
    Nat.card Z0 = 4 := by
  refine le_antisymm card_Z0_le ?_
  have hf : ∀ k : Fin 4, wordPerm (tg ([0, 4, 8, 12].get ⟨k.val, by simp⟩)) ∈ Z0 :=
    fun k => mem_Z0.2 ⟨_, List.get_mem _ _, rfl⟩
  have hinj : Function.Injective (fun k : Fin 4 => (⟨_, hf k⟩ : Z0)) := by
    intro a b hab
    have h := congrArg Subtype.val hab
    have hlt : ∀ k : Fin 4, [0, 4, 8, 12].get ⟨k.val, by simp⟩ < 64 := by decide
    have := tg_injective (hlt a) (hlt b) h
    fin_cases a <;> fin_cases b <;> first | rfl | simp at this
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

variable {G : Type} [Group G]

theorem mem_commutator_of_mem_zStar [Finite G] {K P : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hP : IsSylowTwoIn P K) {z : G} (hz : z ∈ P ⊓ zStarIn K) : z ∈ ⁅P, P⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨T, hT⟩ := hP.2
  set Q : Sylow 2 (Jhat K) := T.mapSurjective (jq_surjective K) with hQ
  have hzK : z ∈ K := hP.1 hz.1
  have hzc : jq K ⟨z, hzK⟩ ∈ center (Jhat K) := (mem_zStarIn_iff hzK).1 hz.2
  have hzQ : jq K ⟨z, hzK⟩ ∈ (Q : Subgroup (Jhat K)) := by
    rw [hQ, Sylow.coe_mapSurjective, hT]
    exact ⟨⟨z, hzK⟩, mem_subgroupOf.mpr hz.1, rfl⟩
  have hzG : jq K ⟨z, hzK⟩ ∈ commutator (Jhat K) := by
    rw [commutator_jhat hK]
    exact mem_top _
  have h1 := Goldschmidt75.mem_commutator_of_mem_center Q hzc hzQ hzG
  rw [hQ, Sylow.coe_mapSurjective, hT, ← Subgroup.map_commutator] at h1
  obtain ⟨c, hc, hcz⟩ := h1
  have hcP : (c : G) ∈ P := by
    have hle : ⁅P.subgroupOf K, P.subgroupOf K⁆ ≤ P.subgroupOf K :=
      Subgroup.commutator_le.2 fun a ha b hb =>
        mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    exact mem_subgroupOf.mp (hle hc)
  have hcz' : (c : G) = z := eq_of_jq_eq hP.1 hP2 hcP hz.1 hcz
  rw [← hcz']
  have h2 : (⁅P.subgroupOf K, P.subgroupOf K⁆).map K.subtype = ⁅P, P⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hP.1]
  rw [← h2]
  exact ⟨c, hc, rfl⟩

theorem ker_mul_self_of_elem [Finite G] {K P : Subgroup G} (hP : IsSylowTwoIn P K)
    {q : Jhat K →* Equiv.Perm (Fin 42)} (hqker : q.ker = center (Jhat K))
    (hZ : ∀ z ∈ P ⊓ zStarIn K, z * z = 1) : ∀ e ∈ q.ker, e * e = 1 := by
  intro e he
  rw [hqker] at he
  obtain ⟨z, hzP, hzK, rfl⟩ := exists_mem_of_mem_center hP he
  have hzZ : z ∈ P ⊓ zStarIn K := mem_inf.mpr ⟨hzP, (mem_zStarIn_iff hzK).2 he⟩
  rw [← map_mul]
  have : (⟨z, hzK⟩ : K) * ⟨z, hzK⟩ = 1 := Subtype.ext (hZ z hzZ)
  rw [this, map_one]

variable {K P : Subgroup G} {q : Jhat K →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat K}

theorem mem_centralizer_P_iff
    [Finite G] (hP : IsSylowTwoIn P K) (hQ : IsQSetting q l)
    (hk2 : ∀ e ∈ q.ker, e * e = 1)
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ K, jq K ⟨p, hp⟩ = e) {y : G} (hy : y ∈ P) :
    y ∈ centralizer (P : Set G) ↔ q (jq K ⟨y, hP.1 hy⟩) ∈ Z0 := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  constructor
  · intro hc
    refine (mem_Z0_iff_comm hP hQ.qsurj hQ.ker hT hy).2 fun w hw => ?_
    have hwy : w * y = y * w := (mem_centralizer_iff.mp hc) w hw
    have h1 : y⁻¹ * w⁻¹ * y * w = 1 := by
      calc y⁻¹ * w⁻¹ * y * w = y⁻¹ * w⁻¹ * (y * w) := by group
        _ = y⁻¹ * w⁻¹ * (w * y) := by rw [hwy]
        _ = 1 := by group
    rw [h1]
    exact one_mem _
  · intro hyZ
    refine mem_centralizer_iff.mpr fun p hp => ?_
    have h1 := hQ.comm_of_Z0_ker2 hk2 ((hT (jq K ⟨p, hP.1 hp⟩)).2 ⟨p, hp, _, rfl⟩) hyZ
    apply eq_of_jq_eq hP.1 hP2 (P.mul_mem hp hy) (P.mul_mem hy hp)
    show jq K (⟨p, hP.1 hp⟩ * ⟨y, hP.1 hy⟩) = jq K (⟨y, hP.1 hy⟩ * ⟨p, hP.1 hp⟩)
    rw [map_mul, map_mul]
    exact h1

theorem exists_over
    (hQ : IsQSetting q l) (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ K, jq K ⟨p, hp⟩ = e)
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) : ∃ p ∈ P, ∃ hp : p ∈ K, q (jq K ⟨p, hp⟩) = t := by
  obtain ⟨e, he⟩ := hQ.qsurj t (T0_le_S ht)
  obtain ⟨p, hpP, hpK, rfl⟩ := (hT e).1 (he ▸ ht)
  exact ⟨p, hpP, hpK, he⟩

theorem exists_commutator_over
    (hQ : IsQSetting q l)
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ K, jq K ⟨p, hp⟩ = e)
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ Z0) :
    ∃ u ∈ ⁅P, P⁆, ∃ hu : u ∈ K, q (jq K ⟨u, hu⟩) = t := by
  obtain ⟨a, haP, haK, ha⟩ := exists_over hQ hT (tg_mem_T0 1 (by norm_num))
  obtain ⟨b, hbP, hbK, hb⟩ := exists_over hQ hT (tg_mem_T0 16 (by norm_num))
  obtain ⟨c, hcP, hcK, hc⟩ := exists_over hQ hT (tg_mem_T0 24 (by norm_num))
  have hcomm : ∀ {x y : G} (hx : x ∈ K) (hy : y ∈ K), q (jq K ⟨⁅x, y⁆, K.mul_mem
      (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)⟩) =
      q (jq K ⟨x, hx⟩) * q (jq K ⟨y, hy⟩) * (q (jq K ⟨x, hx⟩))⁻¹ * (q (jq K ⟨y, hy⟩))⁻¹ := by
    intro x y hx hy
    have e1 : (⟨⁅x, y⁆, K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)⟩ :
        K) = ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : K)⁻¹ * (⟨y, hy⟩ : K)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv]
  have habK : ⁅a, b⁆ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem haK hbK) (K.inv_mem haK)) (K.inv_mem hbK)
  have hacK : ⁅a, c⁆ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem haK hcK) (K.inv_mem haK)) (K.inv_mem hcK)
  have h4 : q (jq K ⟨⁅a, b⁆, habK⟩) = wordPerm (tg 4) := by
    rw [hcomm haK hbK, ha, hb, tg4_comm]
    group
  have h8 : q (jq K ⟨⁅a, c⁆, hacK⟩) = wordPerm (tg 8) := by
    rw [hcomm haK hcK, ha, hc, tg8_comm]
    group
  have hab : ⁅a, b⁆ ∈ ⁅P, P⁆ := commutator_mem_commutator haP hbP
  have hac : ⁅a, c⁆ ∈ ⁅P, P⁆ := commutator_mem_commutator haP hcP
  obtain ⟨k, hk, rfl⟩ := mem_Z0.1 ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · refine ⟨1, one_mem _, one_mem _, ?_⟩
    rw [show (⟨1, one_mem K⟩ : K) = 1 from rfl, map_one, map_one, wordPerm_tg_zero]
  · exact ⟨_, hab, habK, h4⟩
  · exact ⟨_, hac, hacK, h8⟩
  · refine ⟨⁅a, b⁆ * ⁅a, c⁆, mul_mem hab hac, K.mul_mem habK hacK, ?_⟩
    have e1 : (⟨⁅a, b⁆ * ⁅a, c⁆, K.mul_mem habK hacK⟩ : K) = ⟨⁅a, b⁆, habK⟩ * ⟨⁅a, c⁆, hacK⟩ :=
      rfl
    rw [e1, map_mul, map_mul, h4, h8, tg4_mul_tg8]

private theorem commutator_le_self' (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem elementaryCenterSylow :
    ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
      (∀ z ∈ P ⊓ zStarIn K, z * z = 1) →
      IsElemTwo (P ⊓ centralizer (P : Set G)) ∧
        Nat.card ↥(P ⊓ centralizer (P : Set G)) = 4 * Nat.card ↥(P ⊓ zStarIn K) ∧
        P ⊓ centralizer (P : Set G) ≤ ⁅P, P⁆ := by
  intro G _ _ K P hK hL hP hZ
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hK hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hk2 := ker_mul_self_of_elem hP hqker hZ
  have hZP : P ⊓ centralizer (P : Set G) = pullP K P hP.1 (Z0.comap q) := by
    ext y
    rw [mem_pullP, mem_inf]
    constructor
    · rintro ⟨hy, hc⟩
      exact ⟨hy, (mem_centralizer_P_iff hP hQ hk2 hT hy).1 hc⟩
    · rintro ⟨hy, hyZ⟩
      exact ⟨hy, (mem_centralizer_P_iff hP hQ hk2 hT hy).2 hyZ⟩
  obtain ⟨ζ, -⟩ := exists_zeta hP hqker
  have hU := hQ.isElemTwo_U1_comap hk2
  refine ⟨?_, ?_, ?_⟩
  · rw [hZP]
    exact isElemTwo_pullP hP2 ⟨fun a ha b hb => hU.1 a (Z0_le_U1 ha) b (Z0_le_U1 hb),
      fun a ha => hU.2 a (Z0_le_U1 ha)⟩
  · rw [hZP, card_pullP hP2 hT (comap_mono (show Z0 ≤ T0 from inf_le_right)),
      card_comap_eq q Z0 (fun t ht => hqsurj t (T0_le_S ht.2)), card_Z0,
      Nat.card_congr ζ.toEquiv]
  · intro y hy
    rw [hZP] at hy
    obtain ⟨hyP, hyZ⟩ := mem_pullP.1 hy
    obtain ⟨u, hu, huK, hq⟩ := exists_commutator_over hQ hT hyZ
    have huP : u ∈ P := commutator_le_self' P hu
    have hv : u⁻¹ * y ∈ P ⊓ zStarIn K := by
      refine ⟨P.mul_mem (P.inv_mem huP) hyP, (mem_zStarIn_iff (hP.1 (P.mul_mem
        (P.inv_mem huP) hyP))).2 ?_⟩
      rw [← hqker, MonoidHom.mem_ker]
      have e1 : (⟨u⁻¹ * y, hP.1 (P.mul_mem (P.inv_mem huP) hyP)⟩ : K) =
          (⟨u, huK⟩ : K)⁻¹ * ⟨y, hP.1 hyP⟩ := rfl
      rw [e1, map_mul, map_mul, map_inv, map_inv, hq, inv_mul_cancel]
    have := mul_mem hu (mem_commutator_of_mem_zStar hK hP hv)
    rwa [mul_inv_cancel_left] at this

end CFSG.ComponentClassification.GrSLit.L34Facts
