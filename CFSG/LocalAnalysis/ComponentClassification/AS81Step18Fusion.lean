module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Fix
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFourGroup

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowOf_le_centralizer {N H K : Subgroup G} {t : G} (hHN : H ≤ N)
    (hH : ¬ 2 ∣ H.relIndex N) (htH : t ∈ H) (ht : t ^ 2 = 1) (hK : Odd (Nat.card K))
    (hHt : ∀ h ∈ H, h * t * h⁻¹ * t⁻¹ ∈ K) :
    ∃ P : Subgroup G, IsSylowOf 2 P N ∧ P ≤ centralizer ({t} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 H
  obtain ⟨a, haH, hat⟩ := AS76b.exists_conj_mem_of_isSylowOf hQ htH (n := 1)
    (by rw [pow_one]; exact ht)
  have hPH : IsSylowOf 2 (rightConjugate Q a) H := by
    have h := AschbacherTheorem3.isSylowOf_rightConjugate hQ a
    rwa [(rightConjugate_eq_self_iff H a).mpr (le_normalizer haH)] at h
  have hPN : IsSylowOf 2 (rightConjugate Q a) N := by
    rw [isSylowOf_iff] at hPH ⊢
    refine ⟨hPH.1.trans hHN, hPH.2.1, fun h2 => ?_⟩
    rw [← relIndex_mul_relIndex _ H N hPH.1 hHN] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hPH.2.2 h
    · exact hH h
  refine ⟨_, hPN, fun p hp => ?_⟩
  have htP : t ∈ rightConjugate Q a := (mem_rightConjugate_iff _ _ _).mpr hat
  have hc : p * t * p⁻¹ * t⁻¹ ∈ K ⊓ rightConjugate Q a :=
    ⟨hHt p (hPH.le hp), (rightConjugate Q a).mul_mem ((rightConjugate Q a).mul_mem
      ((rightConjugate Q a).mul_mem hp htP) ((rightConjugate Q a).inv_mem hp))
      ((rightConjugate Q a).inv_mem htP)⟩
  have hbot : K ⊓ rightConjugate Q a = ⊥ := by
    have h2 : IsPGroup 2 ↥(K ⊓ rightConjugate Q a) := hPN.isPGroup.to_inf_right
    rcases h2.card_eq_or_dvd with h | h
    · exact card_eq_one.mp h
    · exact absurd (even_iff_two_dvd.mpr (h.trans (card_dvd_of_le inf_le_left)))
        (Nat.not_even_iff_odd.mpr hK)
  rw [hbot, mem_bot, mul_inv_eq_one] at hc
  rw [mem_centralizer_singleton_iff]
  calc p * t = p * t * p⁻¹ * p := by group
    _ = t * p := by rw [hc]

structure FusionModel {Ω : Type} [Group Ω] (M T : Subgroup Ω) : Prop where
  le : M ≤ T
  normal : T ≤ normalizer (M : Set Ω)
  index : Nat.card T ≤ 2 * Nat.card M
  even : Even (Nat.card M)
  center : ∀ Y P : Subgroup Ω, M ≤ Y → Y ≤ T → IsSylowOf 2 P Y → Nat.card (centerIn P) = 2
  fusion : ∀ Y : Subgroup Ω, M ≤ Y → Y ≤ T → ∀ σ ∈ Y, ∀ τ ∈ Y, orderOf σ = 2 → orderOf τ = 2 →
    ¬ 2 ∣ (centralizer ({σ} : Set Ω)).relIndex Y → 2 ∣ (centralizer ({τ} : Set Ω)).relIndex Y →
    ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ ¬ p ∣ Nat.card (T ⊓ centralizer ({σ} : Set Ω) : Subgroup Ω) ∧
      ∃ x ∈ M ⊓ centralizer ({τ} : Set Ω), x ≠ 1 ∧ x ^ p = 1 ∧
        ∀ N' : Subgroup Ω, N' ≤ M ⊓ centralizer ({τ} : Set Ω) →
          M ⊓ centralizer ({τ} : Set Ω) ≤ normalizer (N' : Set Ω) → Odd (Nat.card N') → x ∉ N'

section Action

variable {L : Subgroup G} {Ω : Type} [Group Ω] {M : Subgroup Ω}
  {φ : normalizer (L : Set G) →* Ω}

omit [Finite G] in
theorem ker_actionHom (hφ : IsActionHom L M φ) :
    φ.ker = (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  exact hφ.eq_one_iff n

omit [Finite G] in
theorem le_range_actionHom (hφ : IsActionHom L M φ) : M ≤ φ.range := fun x hx => by
  obtain ⟨a, ha, hae⟩ := hφ.exists_eq x hx
  exact ⟨_, hae⟩

omit [Finite G] in
theorem relIndex_centralizer_eq_card_map (hφ : IsActionHom L M φ) {H : Subgroup G}
    (hH : H ≤ normalizer (L : Set G)) :
    (H ⊓ centralizer (L : Set G)).relIndex H =
      Nat.card ((H.subgroupOf (normalizer (L : Set G))).map φ) := by
  rw [inf_relIndex_left, ← relIndex_subgroupOf hH, ← ker_actionHom hφ, relIndex_ker]

omit [Finite G] in
theorem odd_orderOf_of_mem_inf (hZ : Odd (Nat.card (center ↥L))) {d : G} (hdL : d ∈ L)
    (hdC : d ∈ centralizer (L : Set G)) : Odd (orderOf d) := by
  have hdZ : (⟨d, hdL⟩ : ↥L) ∈ center ↥L :=
    mem_center_iff.mpr fun y => Subtype.ext ((mem_centralizer_iff.mp hdC) y y.2)
  have h1 := Subgroup.orderOf_dvd_natCard (center ↥L) hdZ
  rw [Subgroup.orderOf_mk] at h1
  exact hZ.of_dvd_nat h1

omit [Finite G] in
theorem orderOf_actionHom (hφ : IsActionHom L M φ)
    (hCL : Odd (Nat.card (centralizer (L : Set G)))) {r : normalizer (L : Set G)}
    (hr : orderOf (r : G) = 2) : orderOf (φ r) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr2 : r ^ 2 = 1 := Subtype.ext (by rw [coe_pow, ← hr, pow_orderOf_eq_one, coe_one])
  refine orderOf_eq_prime (by rw [← map_pow, hr2, map_one]) fun h1 => ?_
  have hrC := (hφ.eq_one_iff r).mp h1
  have := Subgroup.orderOf_dvd_natCard _ hrC
  rw [hr] at this
  exact (Nat.not_even_iff_odd.mpr hCL) (even_iff_two_dvd.mpr this)

omit [Finite G] in
theorem exists_lift_commute (hφ : IsActionHom L M φ) (hZ : Odd (Nat.card (center ↥L)))
    {t : normalizer (L : Set G)} (ht2 : (t : G) ^ 2 = 1) {x : Ω} (hx : x ∈ M)
    (hxt : x * φ t = φ t * x) :
    ∃ (h : G) (hh : h ∈ L), φ ⟨h, le_normalizer hh⟩ = x ∧ h * t = t * h := by
  obtain ⟨a, ha, hae⟩ := hφ.exists_eq x hx
  have htinv : (t : G)⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
  set d : G := a⁻¹ * t * a * t with hd
  have hdA : d ∈ L := by
    have h1 : (t : G) * a * (t : G)⁻¹ ∈ L := (mem_normalizer_iff.mp t.2 a).mp ha
    rw [htinv] at h1
    have h2 := L.mul_mem (L.inv_mem ha) h1
    rwa [show a⁻¹ * ((t : G) * a * t) = d by rw [hd]; group] at h2
  have hdK : d ∈ centralizer (L : Set G) := by
    have h1 : φ (⟨a, le_normalizer ha⟩⁻¹ * t * ⟨a, le_normalizer ha⟩ * t) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hae]
      calc x⁻¹ * φ t * x * φ t = x⁻¹ * (x * φ t) * φ t := by rw [mul_assoc x⁻¹, hxt]
        _ = φ t * φ t := by group
        _ = φ (t * t) := (map_mul φ t t).symm
        _ = 1 := by
          rw [show t * t = 1 from Subtype.ext (by rw [← sq]; simpa using ht2), map_one]
    have := (hφ.eq_one_iff _).mp h1
    simpa [hd] using this
  have htd : (t : G) * d * t = d⁻¹ := by
    rw [hd]
    calc (t : G) * (a⁻¹ * t * a * t) * t = t * a⁻¹ * t * a * (t * t) := by group
      _ = t * a⁻¹ * t * a := by rw [← sq, ht2, mul_one]
      _ = (a⁻¹ * t * a * t)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, htinv, inv_inv]
          group
  obtain ⟨m, hm⟩ := odd_orderOf_of_mem_inf hZ hdA hdK
  set k := m + 1 with hk
  have hd2k : d ^ (2 * k) = d := by
    rw [show 2 * k = orderOf d + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  refine ⟨a * d ^ k, L.mul_mem ha (pow_mem hdA k), ?_, ?_⟩
  · have h1 : φ ⟨a * d ^ k, le_normalizer (L.mul_mem ha (pow_mem hdA k))⟩ =
        φ ⟨a, le_normalizer ha⟩ * φ ⟨d, le_normalizer hdA⟩ ^ k := by
      rw [← map_pow, ← map_mul]
      rfl
    rw [h1, hae, (hφ.eq_one_iff _).mpr hdK, one_pow, mul_one]
  · have htdk : (t : G) * d ^ k * t = (d ^ k)⁻¹ := by
      rw [← inv_pow, ← htd, show (t : G) * d * t = t * d * (t : G)⁻¹ by rw [htinv], conj_pow,
        htinv]
    have hta : (t : G) * a * t = a * d := by
      rw [hd]
      group
    have key : (t : G) * (a * d ^ k) * t = a * d ^ k := by
      calc (t : G) * (a * d ^ k) * t = (t * a * t) * (t * d ^ k * t) := by
            rw [show (t : G) * a * t * (t * d ^ k * t) = t * a * (t * t) * d ^ k * t by group,
              ← sq, ht2]
            group
        _ = a * d * (d ^ k)⁻¹ := by rw [hta, htdk]
        _ = a * d ^ k := by
            have e2 : d = d ^ k * d ^ k := by rw [← pow_add, ← two_mul, hd2k]
            calc a * d * (d ^ k)⁻¹ = a * (d * (d ^ k)⁻¹) := by group
              _ = a * (d ^ k * d ^ k * (d ^ k)⁻¹) := by rw [← e2]
              _ = a * d ^ k := by group
    calc a * d ^ k * t = t * (t * (a * d ^ k) * t) := by
          rw [show (t : G) * ((t : G) * (a * d ^ k) * t) = t * t * (a * d ^ k) * t by group,
            ← sq, ht2, one_mul]
      _ = t * (a * d ^ k) := by rw [key]

omit [Finite G] in
theorem mem_of_actionHom_mem (hφ : IsActionHom L M φ)
    (hCL : Odd (Nat.card (centralizer (L : Set G)))) {r : G} (hrN : r ∈ normalizer (L : Set G))
    (hr2 : r ^ 2 = 1) (hrM : φ ⟨r, hrN⟩ ∈ M) : r ∈ L := by
  obtain ⟨a, ha, hae⟩ := hφ.exists_eq _ hrM
  set c := a⁻¹ * r with hc
  have hcC : c ∈ centralizer (L : Set G) := by
    have h1 : φ ((⟨a, le_normalizer ha⟩ : normalizer (L : Set G))⁻¹ * ⟨r, hrN⟩) = 1 := by
      rw [map_mul, map_inv, hae, inv_mul_cancel]
    simpa using (hφ.eq_one_iff _).mp h1
  have hac : a * c = c * a := mem_centralizer_iff.mp hcC a ha
  have hr : r = a * c := by rw [hc]; group
  have hc2 : c ^ 2 = (a ^ 2)⁻¹ := by
    have h1 : (a * c) ^ 2 = 1 := by rw [← hr]; exact hr2
    rw [Commute.mul_pow hac 2] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hc2L : c ^ 2 ∈ L := by rw [hc2]; exact L.inv_mem (pow_mem ha 2)
  obtain ⟨j, hj⟩ : Odd (orderOf c) := hCL.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hcC)
  have hcL : c ∈ L := by
    have e : c = (c ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [e]
    exact pow_mem hc2L _
  rw [hr]
  exact L.mul_mem ha hcL

end Action

section Sylow

variable {L : Subgroup G} {Ω : Type} [Group Ω] [Finite Ω] {M : Subgroup Ω}
  {φ : normalizer (L : Set G) →* Ω}

omit [Finite G] [Finite Ω] in
theorem injective_actionHom_comp (hφ : IsActionHom L M φ)
    (hCL : Odd (Nat.card (centralizer (L : Set G)))) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (L : Set G)) : Function.Injective (φ.comp (inclusion hPN)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hs
  have hsC : (s : G) ∈ centralizer (L : Set G) := (hφ.eq_one_iff _).mp hs
  have hbot : P ⊓ centralizer (L : Set G) = ⊥ := by
    have h2 : IsPGroup 2 ↥(P ⊓ centralizer (L : Set G)) := hP.to_inf_left
    rcases h2.card_eq_or_dvd with h | h
    · exact card_eq_one.mp h
    · exact absurd (even_iff_two_dvd.mpr (h.trans (card_dvd_of_le inf_le_right)))
        (Nat.not_even_iff_odd.mpr hCL)
  have : (s : G) ∈ P ⊓ centralizer (L : Set G) := ⟨s.2, hsC⟩
  rw [hbot, mem_bot] at this
  exact (mem_bot).mpr (Subtype.ext this)

theorem isSylowOf_range_actionHom_comp {P : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (hPN : P ≤ normalizer (L : Set G)) : IsSylowOf 2 (φ.comp (inclusion hPN)).range φ.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · exact hP.isPGroup.of_surjective _ (φ.comp (inclusion hPN)).rangeRestrict_surjective
  · rw [← index_comap]
    intro h2
    have hle : P.subgroupOf (normalizer (L : Set G)) ≤ (φ.comp (inclusion hPN)).range.comap φ :=
      fun n hn => ⟨⟨n, hn⟩, rfl⟩
    have h1 := (hP.of_le hPN le_top)
    rw [isSylowOf_iff] at h1
    exact h1.2.2 (h2.trans (index_dvd_of_le hle))

omit [Finite G] in
theorem centerIn_eq_map_center' (A : Subgroup G) : centerIn A = (center ↥A).map A.subtype := by
  ext x
  constructor
  · rintro ⟨hxA, hxC⟩
    exact ⟨⟨x, hxA⟩, mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hxC y y.2),
      rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_centralizer_iff.mpr fun a ha =>
      congrArg Subtype.val (mem_center_iff.mp hy ⟨a, ha⟩)⟩

omit [Finite G] [Finite Ω] in
theorem card_centerIn_eq_of_mulEquiv {A : Subgroup G} {B : Subgroup Ω} (e : ↥A ≃* ↥B) :
    Nat.card (centerIn A) = Nat.card (centerIn B) := by
  rw [centerIn_eq_map_center', centerIn_eq_map_center', card_map_of_injective A.subtype_injective,
    card_map_of_injective B.subtype_injective, ← map_center_eq e,
    card_map_of_injective e.injective]

theorem card_centerIn_of_fusionModel {T : Subgroup Ω} (hD : FusionModel M T)
    (hφ : IsActionHom L M φ) (hφT : φ.range ≤ T)
    (hCL : Odd (Nat.card (centralizer (L : Set G)))) {P : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (hPN : P ≤ normalizer (L : Set G)) : Nat.card (centerIn P) = 2 := by
  have hinj := injective_actionHom_comp hφ hCL hP.isPGroup hPN
  rw [card_centerIn_eq_of_mulEquiv (MonoidHom.ofInjective hinj)]
  exact hD.center _ _ (le_range_actionHom hφ) hφT (isSylowOf_range_actionHom_comp hP hPN)

theorem centerIn_le_of_card_eq_two {Y P : Subgroup Ω} (hMY : M ≤ Y)
    (hYM : Y ≤ normalizer (M : Set Ω)) (hM : Even (Nat.card M)) (hP : IsSylowOf 2 P Y)
    (hZ : Nat.card (centerIn P) = 2) : centerIn P ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPM : IsSylowOf 2 (P ⊓ M) M := hP.inf_of_le_normalizer hMY hYM
  have hQ : M.subgroupOf P ≠ ⊥ := by
    intro h
    have h1 : P ⊓ M = ⊥ := by
      rw [inf_comm, ← subgroupOf_map_subtype, h, Subgroup.map_bot]
    rw [isSylowOf_iff, h1, relIndex_bot_left] at hPM
    exact hPM.2.2 (even_iff_two_dvd.mp hM)
  have hQn : (M.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (hYM (hP.le g.2)) n).mp hn
    simpa using this⟩
  have hnil : Group.IsNilpotent ↥P := hP.isPGroup.isNilpotent
  obtain ⟨w, hw1⟩ := ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hQ)
  obtain ⟨hwM, hwZ⟩ := mem_inf.mp w.2
  set v : Ω := ((w : ↥P) : Ω) with hv
  have hvM : v ∈ M := mem_subgroupOf.mp hwM
  have hvZ : v ∈ centerIn P :=
    ⟨(w : ↥P).2, mem_centralizer_iff.mpr fun s hs =>
      congrArg Subtype.val (mem_center_iff.mp hwZ ⟨s, hs⟩)⟩
  have hv1 : v ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  have hov : 2 ≤ orderOf v := by
    have h0 : 0 < orderOf v := orderOf_pos v
    have h1 : orderOf v ≠ 1 := fun h => hv1 (orderOf_eq_one_iff.mp h)
    omega
  have heq : zpowers v = centerIn P :=
    eq_of_le_of_card_ge (zpowers_le.mpr hvZ) (by rw [hZ, Nat.card_zpowers]; exact hov)
  rw [← heq]
  exact zpowers_le.mpr hvM

omit [Finite Ω] in
theorem not_two_dvd_relIndex_of_sylow {z : G}
    (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hSz : S ≤ centralizer ({z} : Set G)) :
    ¬ 2 ∣ (centralizer ({φ ⟨z, hzL (mem_centralizer_singleton_iff.mpr rfl)⟩} : Set Ω)).relIndex
      φ.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← index_comap]
  intro h2
  have hSN : S ≤ normalizer (L : Set G) := hSz.trans hzL
  have hle : S.subgroupOf (normalizer (L : Set G)) ≤
      (centralizer ({φ ⟨z, hzL (mem_centralizer_singleton_iff.mpr rfl)⟩} : Set Ω)).comap φ := by
    intro n hn
    rw [mem_comap, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hSz (mem_subgroupOf.mp hn)))
  have h1 := hS.of_le hSN le_top
  rw [isSylowOf_iff] at h1
  exact h1.2.2 (h2.trans (index_dvd_of_le hle))

theorem rightConjugate_eq_of_fusionModel {T : Subgroup Ω} (hD : FusionModel M T)
    (hφ : IsActionHom L M φ) (hφT : φ.range ≤ T) (hZ3 : Nat.card (center ↥L) ∣ 3)
    (hCL : Odd (Nat.card (centralizer (L : Set G)))) {z : G} (hz : orderOf z = 2)
    (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hSz : S ≤ centralizer ({z} : Set G)) {g : G}
    (hg : z ∈ normalizer (rightConjugate L g : Set G)) : rightConjugate L g = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMY := le_range_actionHom hφ
  have hZodd : Odd (Nat.card (center ↥L)) := Odd.of_dvd_nat (by decide) hZ3
  have hzN : z ∈ normalizer (L : Set G) := hzL (mem_centralizer_singleton_iff.mpr rfl)
  have hSN : S ≤ normalizer (L : Set G) := hSz.trans hzL
  set t := g * z * g⁻¹ with ht
  have htN : t ∈ normalizer (L : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.mp hg (g⁻¹ * x * g)
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff] at h1
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group,
      show g * (z * (g⁻¹ * x * g) * z⁻¹) * g⁻¹ = t * x * t⁻¹ by rw [ht]; group] at h1
  have ht2 : orderOf t = 2 := by
    rw [ht, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz
  have htsq : t ^ 2 = 1 := by rw [← ht2, pow_orderOf_eq_one]
  set tN : normalizer (L : Set G) := ⟨t, htN⟩ with htNdef
  set zN : normalizer (L : Set G) := ⟨z, hzN⟩ with hzNdef
  have hσ := orderOf_actionHom hφ hCL (r := zN) hz
  have hτ := orderOf_actionHom hφ hCL (r := tN) ht2
  have hσc := not_two_dvd_relIndex_of_sylow (φ := φ) hzL hS hSz
  have hτc : ¬ 2 ∣ (centralizer ({φ tN} : Set Ω)).relIndex φ.range := by
    intro h2
    obtain ⟨p, hp, hp3, hpσ, x, hx, hx1, hxp, hxN⟩ :=
      hD.fusion _ hMY hφT (φ zN) ⟨_, rfl⟩ (φ tN) ⟨_, rfl⟩ hσ hτ hσc h2
    have : Fact p.Prime := ⟨hp⟩
    have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
    obtain ⟨h, hhL, hhx, hht⟩ := exists_lift_commute hφ hZodd (t := tN) htsq hx.1
      (mem_centralizer_singleton_iff.mp hx.2)
    set m := Nat.card (center ↥L) with hm
    have hhN : h ∈ normalizer (L : Set G) := le_normalizer hhL
    have hhp : h ^ p ∈ centralizer (L : Set G) := by
      have h1 : φ ⟨h ^ p, pow_mem hhN p⟩ = 1 := by
        rw [show (⟨h ^ p, pow_mem hhN p⟩ : normalizer (L : Set G)) = ⟨h, hhN⟩ ^ p from Subtype.ext (by simp),
          map_pow, hhx, hxp]
      exact (hφ.eq_one_iff _).mp h1
    have hu1 : (h ^ m) ^ p = 1 := by
      have hZ : (⟨h ^ p, pow_mem hhL p⟩ : ↥L) ∈ center ↥L :=
        mem_center_iff.mpr fun y => Subtype.ext ((mem_centralizer_iff.mp hhp) y y.2)
      have h1 : (⟨⟨h ^ p, pow_mem hhL p⟩, hZ⟩ : ↥(center ↥L)) ^ m = 1 := pow_card_eq_one'
      have h2 := congrArg (fun w : ↥(center ↥L) => ((w : ↥L) : G)) h1
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
      rw [← pow_mul, mul_comm, pow_mul]
      exact h2
    have huL : h ^ m ∈ L := pow_mem hhL m
    have hφu : φ ⟨h ^ m, pow_mem hhN m⟩ = x ^ m := by
      rw [show (⟨h ^ m, pow_mem hhN m⟩ : normalizer (L : Set G)) = ⟨h, hhN⟩ ^ m from Subtype.ext (by simp), map_pow,
        hhx]
    have hcop : m.Coprime (orderOf x) := by
      rw [hxo]
      exact Nat.Coprime.coprime_dvd_left hZ3
        ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
    have hct : g⁻¹⁻¹ * z * g⁻¹ = t := by rw [inv_inv]
    have hut : h ^ m ∈ centralizer ({g⁻¹⁻¹ * z * g⁻¹} : Set G) := by
      rw [hct, mem_centralizer_singleton_iff]
      exact (Commute.pow_left hht m).eq
    refine false_of_pElement hCL hzL (c := g⁻¹) hp ?_ huL hut (k := 1)
      (by rw [pow_one]; exact hu1) ?_
    ·
      rw [relIndex_centralizer_eq_card_map hφ hzL]
      intro hdvd
      apply hpσ
      refine hdvd.trans (card_dvd_of_le ?_)
      rintro _ ⟨n, hn, rfl⟩
      refine ⟨hφT ⟨n, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hn))
    ·
      rw [hct]
      intro N' hN'le hN'n hN'o huN'
      have hN'N : N' ≤ normalizer (L : Set G) := fun n hn => le_normalizer (hN'le hn).1
      refine hxN ((N'.subgroupOf (normalizer (L : Set G))).map φ) ?_ ?_ ?_ ?_
      · rintro _ ⟨n, hn, rfl⟩
        replace hn : (n : G) ∈ N' := hn
        refine ⟨hφ.map_mem _ (hN'le hn).1, mem_centralizer_singleton_iff.mpr ?_⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.mp (hN'le hn).2)
      · intro y hy
        obtain ⟨k', hk'L, hk'y, hk't⟩ := exists_lift_commute hφ hZodd (t := tN) htsq hy.1
          (mem_centralizer_singleton_iff.mp hy.2)
        have hk'N' : k' ∈ normalizer (N' : Set G) :=
          hN'n ⟨hk'L, mem_centralizer_singleton_iff.mpr hk't⟩
        rw [← hk'y]
        refine AS76b.mem_normalizer_of_map_conj_le ?_
        rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
        refine ⟨⟨k', le_normalizer hk'L⟩ * n * ⟨k', le_normalizer hk'L⟩⁻¹, ?_, ?_⟩
        · replace hn : (n : G) ∈ N' := hn
          show k' * (n : G) * k'⁻¹ ∈ N'
          exact (mem_normalizer_iff.mp hk'N' n).mp hn
        · simp [MulAut.conj_apply]
      · exact hN'o.of_dvd_nat ((card_map_dvd _ _).trans
          (dvd_of_eq (Nat.card_congr (subgroupOfEquivOfLe hN'N).toEquiv)))
      · rw [← hk]
        refine pow_mem ?_ k
        rw [← hφu]
        exact ⟨⟨h ^ m, pow_mem hhN m⟩, mem_subgroupOf.mpr huN', rfl⟩
  obtain ⟨P, hPN, hPt⟩ := exists_isSylowOf_le_centralizer (N := normalizer (L : Set G))
    (H := ((centralizer ({φ tN} : Set Ω)).comap φ).map (normalizer (L : Set G)).subtype)
    (K := centralizer (L : Set G)) (map_subtype_le _) (by
      change ¬ 2 ∣ ((((centralizer ({φ tN} : Set Ω)).comap φ).map
        (normalizer (L : Set G)).subtype).subgroupOf (normalizer (L : Set G))).index
      rw [subgroupOf, comap_map_eq_self_of_injective (normalizer (L : Set G)).subtype_injective,
        index_comap]
      exact hτc)
    ⟨tN, mem_centralizer_singleton_iff.mpr rfl, rfl⟩ htsq hCL (by
      rintro _ ⟨n, hn, rfl⟩
      have h1 : φ (n * tN * n⁻¹ * tN⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, mem_comap.mp hn |>
          mem_centralizer_singleton_iff.mp]
        group
      exact (hφ.eq_one_iff _).mp h1)
  have hNodd : ¬ 2 ∣ (normalizer (L : Set G)).relIndex ⊤ := by
    have h1 := hS
    rw [isSylowOf_iff] at h1
    intro h2
    apply h1.2.2
    rw [← relIndex_mul_relIndex S _ ⊤ hSN le_top]
    exact h2.mul_left _
  have hPG : IsSylowOf 2 P ⊤ := by
    rw [isSylowOf_iff] at hPN ⊢
    refine ⟨le_top, hPN.2.1, fun h2 => ?_⟩
    rw [← relIndex_mul_relIndex P _ ⊤ hPN.1 le_top] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hPN.2.2 h
    · exact hNodd h
  have hS'G : IsSylowOf 2 (rightConjugate P g) ⊤ := by
    have h := AschbacherTheorem3.isSylowOf_rightConjugate hPG g
    rwa [rightConjugate_top] at h
  have hPt' : P ≤ centralizer ({t} : Set G) := hPt
  have hS'z : rightConjugate P g ≤ centralizer ({z} : Set G) := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 := mem_centralizer_singleton_iff.mp (hPt' hx)
    rw [mem_centralizer_singleton_iff]
    have e : x * z = g⁻¹ * ((g * x * g⁻¹) * t) * g := by rw [ht]; group
    have e' : z * x = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [ht]; group
    rw [e, e', h1]
  have hS'L : rightConjugate P g ≤ normalizer (rightConjugate L g : Set G) :=
    rightConjugate_le_normalizer_rightConjugate hPN.le g
  exact rightConjugate_eq_of_sylow_le hz hzL
    (fun S' hS' hS'z => card_centerIn_of_fusionModel hD hφ hφT hCL hS' (hS'z.trans hzL))
    hS'G hS'z hS'L

theorem mem_of_fusionModel {T : Subgroup Ω} (hD : FusionModel M T) (hφ : IsActionHom L M φ)
    (hφT : φ.range ≤ T) (hCL : Odd (Nat.card (centralizer (L : Set G)))) {z : G}
    (hz : orderOf z = 2) (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hSz : S ≤ centralizer ({z} : Set G)) : z ∈ L := by
  have hSN : S ≤ normalizer (L : Set G) := hSz.trans hzL
  have hzS : z ∈ centerIn S := mem_centerIn_of_le_centralizer hS hz hSz
  have hzN : z ∈ normalizer (L : Set G) := hSN hzS.1
  have hinj := injective_actionHom_comp hφ hCL hS.isPGroup hSN
  have hP := isSylowOf_range_actionHom_comp (φ := φ) hS hSN
  have hcen : centerIn (φ.comp (inclusion hSN)).range ≤ M := by
    refine centerIn_le_of_card_eq_two (le_range_actionHom hφ) (hφT.trans hD.normal) hD.even hP ?_
    rw [← card_centerIn_eq_of_mulEquiv (MonoidHom.ofInjective hinj)]
    exact card_centerIn_of_fusionModel hD hφ hφT hCL hS hSN
  have hzZ : φ ⟨z, hzN⟩ ∈ centerIn (φ.comp (inclusion hSN)).range := by
    refine ⟨⟨⟨z, hzS.1⟩, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨s, rfl⟩
    rw [MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (s : G) * z = z * s
    exact mem_centralizer_iff.mp hzS.2 s s.2
  exact mem_of_actionHom_mem hφ hCL hzN (by rw [← hz, pow_orderOf_eq_one]) (hcen hzZ)

omit [Finite G] in
theorem exists_mem_inf_of_fusionModel {T : Subgroup Ω} (hD : FusionModel M T)
    (hφ : IsActionHom L M φ) (hφT : φ.range ≤ T) (hCL : Odd (Nat.card (centralizer (L : Set G))))
    {R : Subgroup G} (hRN : R ≤ normalizer (L : Set G)) (hRe : IsElemAbelian 2 R)
    (hR4 : Nat.card R = 4) : ∃ r ∈ R ⊓ L, r ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 R := isPGroup_two_of_isElemAbelian hRe
  have hinj := injective_actionHom_comp hφ hCL hR2 hRN
  have hcard : Nat.card (φ.comp (inclusion hRN)).range = 4 := by
    rw [← hR4]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hRT : (φ.comp (inclusion hRN)).range ≤ T := by
    rintro _ ⟨s, rfl⟩
    exact hφT ⟨_, rfl⟩
  have hprod := card_sup_mul_card_inf (H := M) (R := (φ.comp (inclusion hRN)).range)
    (hRT.trans hD.normal)
  have hsup : Nat.card (M ⊔ (φ.comp (inclusion hRN)).range : Subgroup Ω) ≤ 2 * Nat.card M :=
    (card_le_of_le (sup_le hD.le hRT)).trans hD.index
  have hM0 : 0 < Nat.card M := Nat.card_pos
  have hinf : 1 < Nat.card (M ⊓ (φ.comp (inclusion hRN)).range : Subgroup Ω) := by
    rw [hcard] at hprod
    by_contra hlt
    push Not at hlt
    nlinarith
  have := Finite.one_lt_card_iff_nontrivial.mp hinf
  obtain ⟨w, hw1⟩ := exists_ne (1 : ↥(M ⊓ (φ.comp (inclusion hRN)).range))
  obtain ⟨hwM, s, hs⟩ := mem_inf.mp w.2
  refine ⟨s, ⟨s.2, ?_⟩, fun h1 => hw1 (Subtype.ext ?_)⟩
  · refine mem_of_actionHom_mem hφ hCL (hRN s.2) (hRe.2 s s.2) ?_
    rw [show φ ⟨(s : G), hRN s.2⟩ = (φ.comp (inclusion hRN)) s from rfl, hs]
    exact hwM
  · rw [← hs, show s = 1 from Subtype.ext h1, map_one]
    rfl

end Sylow

section Model

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem eq_or_eq_of_card_le_two_mul {M Y T : Subgroup Ω} (hMY : M ≤ Y) (hYT : Y ≤ T)
    (h : Nat.card T ≤ 2 * Nat.card M) : Y = M ∨ Y = T := by
  obtain ⟨a, ha⟩ := card_dvd_of_le hMY
  obtain ⟨b, hb⟩ := card_dvd_of_le hYT
  have hM0 : 0 < Nat.card M := Nat.card_pos
  have hY0 : 0 < Nat.card Y := Nat.card_pos
  have hT0 : 0 < Nat.card T := Nat.card_pos
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, mul_zero] at ha
      omega
    · exact h0
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · rw [h0, mul_zero] at hb
      omega
    · exact h0
  have hab : a * b ≤ 2 := by
    rw [hb, ha] at h
    have : Nat.card M * (a * b) ≤ Nat.card M * 2 := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hM0
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · left
    have ha1 : a = 1 := by omega
    rw [ha1, mul_one] at ha
    exact (eq_of_le_of_card_ge hMY ha.le).symm
  · right
    have hb1 : b = 1 := by nlinarith
    rw [hb1, mul_one] at hb
    exact eq_of_le_of_card_ge hYT hb.le

theorem card_centerIn_eq_of_isSylowOf {P P' K : Subgroup Ω} (h : IsSylowOf 2 P K)
    (h' : IsSylowOf 2 P' K) : Nat.card (centerIn P') = Nat.card (centerIn P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := h.exists_mem_conj h'
  have heq : P' = P.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [hk x, mem_map_equiv, MulAut.conj_symm_apply]
  exact (card_centerIn_eq_of_mulEquiv ((P.equivMapOfInjective _ (MulAut.conj k).injective).trans
    (MulEquiv.subgroupCongr heq.symm))).symm

omit [Finite Ω] in
theorem not_mem_of_oddCore_eq_bot {C : Subgroup Ω} (hC : CFSG.oddCore ↥C = ⊥) {x : Ω}
    (hx1 : x ≠ 1) (N' : Subgroup Ω) (hN'C : N' ≤ C) (hN'n : C ≤ normalizer (N' : Set Ω))
    (hN'o : Odd (Nat.card N')) : x ∉ N' := by
  intro hx
  have hn : (N'.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hN'C).mpr hN'n
  have ho : Odd (Nat.card (N'.subgroupOf C)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hN'C).toEquiv]
  have hle := SmallLocal.le_oddCore_of_normal_odd hn ho
  rw [hC, le_bot_iff] at hle
  apply hx1
  have : (⟨x, hN'C hx⟩ : ↥C) ∈ N'.subgroupOf C := hx
  rw [hle, mem_bot] at this
  exact congrArg Subtype.val this

omit [Finite Ω] in
theorem map_conj_inf_centralizer_of_mem_normalizer {Γ : Subgroup Ω} {c : Ω}
    (hc : c ∈ normalizer (Γ : Set Ω)) (t : Ω) :
    (Γ ⊓ centralizer ({t} : Set Ω)).map (MulAut.conj c).toMonoidHom =
      Γ ⊓ centralizer ({c * t * c⁻¹} : Set Ω) := by
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply, mem_inf, mem_inf, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  have h1 : c⁻¹ * y * c ∈ Γ ↔ y ∈ Γ := by
    rw [mem_normalizer_iff] at hc
    rw [hc, show c * (c⁻¹ * y * c) * c⁻¹ = y by group]
  rw [h1]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · calc y * (c * t * c⁻¹) = c * ((c⁻¹ * y * c) * t) * c⁻¹ := by group
      _ = c * (t * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
      _ = c * t * c⁻¹ * y := by group
  · calc c⁻¹ * y * c * t = c⁻¹ * (y * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * t * c⁻¹ * y) * c := by rw [h]
      _ = t * (c⁻¹ * y * c) := by group

omit [Finite Ω] in
theorem card_inf_centralizer_conj_of_mem_normalizer {Γ : Subgroup Ω} {c : Ω}
    (hc : c ∈ normalizer (Γ : Set Ω)) (t : Ω) :
    Nat.card (Γ ⊓ centralizer ({c * t * c⁻¹} : Set Ω) : Subgroup Ω) =
      Nat.card (Γ ⊓ centralizer ({t} : Set Ω) : Subgroup Ω) := by
  rw [← map_conj_inf_centralizer_of_mem_normalizer hc t,
    card_map_of_injective (MulAut.conj c).injective]

omit [Finite Ω] in
theorem relIndex_centralizer_mul_card (Y : Subgroup Ω) (σ : Ω) :
    (centralizer ({σ} : Set Ω)).relIndex Y *
      Nat.card (Y ⊓ centralizer ({σ} : Set Ω) : Subgroup Ω) = Nat.card Y := by
  rw [inf_comm]
  exact relIndex_mul_card _ _

end Model

end CFSG.ComponentClassification.AS81
