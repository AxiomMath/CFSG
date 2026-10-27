module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalBasic
public import CFSG.LocalAnalysis.OddStandard.ONanIdOne
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ComponentClassification.GrSLit.ONanBal

open Subgroup CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.F2 CFSG.ABGLocalTools

@[expose] def theta {G : Type} [Group G] (y : G) : Subgroup G :=
  (pPrimeCore 2 (centralizer ({y} : Set G))).map (centralizer ({y} : Set G)).subtype

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem theta_le_centralizer (y : G) : theta y ≤ centralizer ({y} : Set G) :=
  map_subtype_le _

theorem odd_card_theta (y : G) : Odd (Nat.card (theta y)) := by
  rw [theta, card_map_of_injective (centralizer ({y} : Set G)).subtype_injective]
  exact (pPrimeCore_two_facts (X := centralizer ({y} : Set G))).2

omit [Finite G] in
theorem conj_mem_oddCore_map {K : Subgroup G} {n : G} (hn : n ∈ normalizer (K : Set G)) {y : G}
    (hy : y ∈ (pPrimeCore 2 K).map K.subtype) :
    n * y * n⁻¹ ∈ (pPrimeCore 2 K).map K.subtype := by
  have hn' : ∀ k : G, k ∈ K ↔ n * k * n⁻¹ ∈ K := mem_normalizer_iff.1 hn
  let α : K ≃* K :=
    { toFun := fun k => ⟨n * k * n⁻¹, (hn' k).1 k.2⟩
      invFun := fun k => ⟨n⁻¹ * k * n, by
        have := (hn' (n⁻¹ * k * n)).2 (by rw [show n * (n⁻¹ * k * n) * n⁻¹ = k by group]; exact k.2)
        exact this⟩
      left_inv := fun k => Subtype.ext (by simp only; group)
      right_inv := fun k => Subtype.ext (by simp only; group)
      map_mul' := fun a b => Subtype.ext (by
        change n * (↑a * ↑b) * n⁻¹ = n * ↑a * n⁻¹ * (n * ↑b * n⁻¹)
        group) }
  have hmap := pPrimeCore_map_iso 2 α
  obtain ⟨k, hk, rfl⟩ := hy
  rw [← hmap]
  exact ⟨α k, ⟨k, hk, rfl⟩, rfl⟩

omit [Finite G] in
theorem mem_normalizer_centralizer {y n : G} (h : n * y * n⁻¹ = y ∨ n * y * n⁻¹ = y⁻¹) :
    n ∈ normalizer (centralizer ({y} : Set G) : Set G) := by
  have key : ∀ m : G, (m * y * m⁻¹ = y ∨ m * y * m⁻¹ = y⁻¹) →
      ∀ k : G, k ∈ centralizer ({y} : Set G) → m * k * m⁻¹ ∈ centralizer ({y} : Set G) := by
    intro m hm k hk
    rw [mem_centralizer_singleton_iff] at hk ⊢
    have hk' : k * y⁻¹ = y⁻¹ * k := by
      calc k * y⁻¹ = y⁻¹ * (y * k) * y⁻¹ := by group
        _ = y⁻¹ * (k * y) * y⁻¹ := by rw [hk]
        _ = y⁻¹ * k := by group
    have e : m * k * m⁻¹ * (m * y * m⁻¹) = m * y * m⁻¹ * (m * k * m⁻¹) := by
      calc m * k * m⁻¹ * (m * y * m⁻¹) = m * (k * y) * m⁻¹ := by group
        _ = m * (y * k) * m⁻¹ := by rw [hk]
        _ = m * y * m⁻¹ * (m * k * m⁻¹) := by group
    rcases hm with h1 | h1
    · rwa [h1] at e
    · rw [h1] at e
      calc m * k * m⁻¹ * y = y * (y⁻¹ * (m * k * m⁻¹)) * y⁻¹ * y * y := by group
        _ = y * (m * k * m⁻¹ * y⁻¹) * y⁻¹ * y * y := by rw [e]
        _ = y * (m * k * m⁻¹) := by group
  have hinv : n⁻¹ * y * n⁻¹⁻¹ = y ∨ n⁻¹ * y * n⁻¹⁻¹ = y⁻¹ := by
    rcases h with h1 | h1
    · left
      calc n⁻¹ * y * n⁻¹⁻¹ = n⁻¹ * y * n := by rw [inv_inv]
        _ = n⁻¹ * (n * y * n⁻¹) * n := by rw [h1]
        _ = y := by group
    · right
      calc n⁻¹ * y * n⁻¹⁻¹ = n⁻¹ * (y⁻¹)⁻¹ * n := by rw [inv_inv, inv_inv]
        _ = n⁻¹ * (n * y * n⁻¹)⁻¹ * n := by rw [h1]
        _ = y⁻¹ := by group
  rw [mem_normalizer_iff]
  intro k
  refine ⟨key n h k, fun hk => ?_⟩
  have := key n⁻¹ hinv _ hk
  rwa [show n⁻¹ * (n * k * n⁻¹) * n⁻¹⁻¹ = k by group] at this

end General

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G}

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0

theorem exists_conj_x_mod_theta (D : FusCtx G v1 v2 v3 s t) (hone : OneClass G) {g : G}
    (hg : g ∈ centralizer ({𝔷} : Set G)) :
    ∃ o ∈ theta 𝔷, (o * g) * 𝔵 * (o * g)⁻¹ = 𝔵 ∨ (o * g) * 𝔵 * (o * g)⁻¹ = 𝔵⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (KQ 𝔷) := Fintype.ofFinite _
  set Cz := centralizer ({𝔷} : Set G) with hCz
  have hτ1 : πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ ≠ 1 := by
    rw [Ne, πQ_eq_one_iff]
    exact D.x_notMem_zpowers_z
  have hττ : πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ = 1 := by
    rw [← map_mul, πQ_eq_one_iff]
    exact D.x_sq_mem_zpowers
  have hconj : ∀ k : Cz, πQ 𝔷 k * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * (πQ 𝔷 k)⁻¹ =
      πQ 𝔷 ⟨(k : G) * 𝔵 * (k : G)⁻¹, mul_mem (mul_mem k.2 D.x_mem_Cz) (inv_mem k.2)⟩ := by
    intro k
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hiso : ∀ h : KQ 𝔷, h * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * h⁻¹ * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ =
      πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * (h * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * h⁻¹) →
      h * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * h⁻¹ = πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ := by
    intro h hh
    obtain ⟨k, rfl⟩ := πQ_surjective 𝔷 h
    rw [hconj k] at hh ⊢
    rw [← map_mul, ← map_mul] at hh
    have hc := (πQ_eq_iff _ _).1 hh
    rw [πQ_eq_iff]
    rcases D.conj_x_of_comm_mod hone k.2 hc with h1 | h1
    · show ((k : G) * 𝔵 * (k : G)⁻¹)⁻¹ * 𝔵 ∈ zpowers 𝔷
      rw [h1, inv_mul_cancel]
      exact one_mem _
    · show ((k : G) * 𝔵 * (k : G)⁻¹)⁻¹ * 𝔵 ∈ zpowers 𝔷
      rw [h1, inv_inv]
      exact D.x_sq_mem_zpowers
  obtain ⟨N, hNn, hNo, hN⟩ := CFSG.ZStar.glauberman_zStar (KQ 𝔷) _ hτ1 hττ hiso
  have hcen : zpowers (zIn 𝔷) ≤ center Cz :=
    zpowers_le.2 (Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (mem_centralizer_singleton_iff.1 y.2))
  have hNle : N ≤ (pPrimeCore 2 Cz).map (QuotientGroup.mk' (zpowers (zIn 𝔷))) := by
    rw [← CFSG.central_p_subgroup_prime_core_quotient _ hcen D.isPGroup_zpowers_zIn_z]
    exact le_sSup ⟨hNn, Nat.coprime_two_left.2 hNo⟩
  have hk := hNle (hN (πQ 𝔷 ⟨g, hg⟩))
  rw [hconj] at hk
  obtain ⟨o', ho', he⟩ := hk
  have he' : πQ 𝔷 o' = πQ 𝔷 (⟨g * 𝔵 * g⁻¹, mul_mem (mul_mem hg D.x_mem_Cz) (inv_mem hg)⟩ *
      (⟨𝔵, D.x_mem_Cz⟩ : Cz)⁻¹) := by
    rw [map_mul, map_inv]
    exact he
  have hc := (πQ_eq_iff _ _).1 he'
  set c : G := (o' : G)⁻¹ * (g * 𝔵 * g⁻¹ * 𝔵⁻¹) with hcdef
  have hcz : c ∈ zpowers 𝔷 := hc
  have hcx : c * 𝔵 = 𝔵 ∨ c * 𝔵 = 𝔵⁻¹ := by
    rcases D.mem_zpowers_z.1 hcz with h1 | h1
    · left
      rw [h1, one_mul]
    · right
      rw [h1, D.x_inv_eq, ← D.x_comm_z]
  have hcxC : c * 𝔵 ∈ Cz := by
    rcases hcx with h1 | h1
    · rw [h1]
      exact D.x_mem_Cz
    · rw [h1]
      exact inv_mem D.x_mem_Cz
  have hx4 : (c * 𝔵) ^ 2 ^ 2 = 1 := by
    rcases hcx with h1 | h1 <;> rw [h1]
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, D.x_pow_four]
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, inv_pow, D.x_pow_four, inv_one]
  have hgx4 : (g * 𝔵 * g⁻¹) ^ 2 ^ 2 = 1 := by
    rw [conj_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, D.x_pow_four]
    group
  set u : Cz := ⟨c * 𝔵, hcxC⟩ with hu
  set v : Cz := ⟨g * 𝔵 * g⁻¹, mul_mem (mul_mem hg D.x_mem_Cz) (inv_mem hg)⟩ with hv
  have hu2 : IsPGroup 2 (zpowers u) :=
    isPGroup_zpowers_of_pow_two (k := 2) (Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      exact hx4))
  have hv2 : IsPGroup 2 (zpowers v) :=
    isPGroup_zpowers_of_pow_two (k := 2) (Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      exact hgx4))
  have hvo : (v : G) = o' * (u : G) := by
    show g * 𝔵 * g⁻¹ = (o' : G) * (c * 𝔵)
    rw [hcdef]
    group
  have huv : u⁻¹ * v ∈ pPrimeCore 2 Cz := by
    have e : u⁻¹ * v = u⁻¹ * o' * u⁻¹⁻¹ := by
      apply Subtype.ext
      rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hvo]
      group
    rw [e]
    exact (pPrimeCore_normal (p := 2) (G := Cz)).conj_mem o' ho' u⁻¹
  obtain ⟨m, hm, hmv⟩ := exists_conj_of_inv_mul_mem (pPrimeCore_two_facts (X := Cz)).2 hu2 hv2 huv
  refine ⟨(m : G), ⟨m, hm, rfl⟩, ?_⟩
  have hmv' : (m : G) * (g * 𝔵 * g⁻¹) * (m : G)⁻¹ = c * 𝔵 := congrArg Subtype.val hmv
  have e : (m : G) * g * 𝔵 * ((m : G) * g)⁻¹ = c * 𝔵 := by
    rw [← hmv']
    group
  rw [e]
  exact hcx

theorem centralizer_x_le_z (D : FusCtx G v1 v2 v3 s t) :
    centralizer ({𝔵} : Set G) ≤ centralizer ({𝔷} : Set G) := by
  intro y hy
  have h := mem_centralizer_singleton_iff.1 hy
  rw [mem_centralizer_singleton_iff, ← D.xel_sq]
  calc y * (𝔵 * 𝔵) = y * 𝔵 * 𝔵 := by group
    _ = 𝔵 * 𝔵 * y := by rw [h, mul_assoc, h, ← mul_assoc]

theorem theta_x_le_theta_z (D : FusCtx G v1 v2 v3 s t) (hone : OneClass G) :
    theta 𝔵 ≤ theta 𝔷 := by
  set Cz := centralizer ({𝔷} : Set G) with hCz
  have hle : theta 𝔵 ≤ Cz := (theta_le_centralizer 𝔵).trans (centralizer_x_le_z D)
  set A := (theta 𝔵).subgroupOf Cz with hA
  set f := QuotientGroup.mk' (pPrimeCore 2 Cz) with hf
  have hMn : (A.map f).Normal := by
    refine ⟨fun q hq c => ?_⟩
    obtain ⟨a, ha, rfl⟩ := hq
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 Cz) c
    obtain ⟨o, ho, hoc⟩ := exists_conj_x_mod_theta D hone c.2
    obtain ⟨o₀, ho₀, ho₀e⟩ := ho
    have hn : (o : G) * c ∈ normalizer (centralizer ({𝔵} : Set G) : Set G) :=
      mem_normalizer_centralizer hoc
    have hnA : (o : G) * c * a * ((o : G) * c)⁻¹ ∈ theta 𝔵 :=
      conj_mem_oddCore_map hn (mem_subgroupOf.1 ha)
    have hc : c = o₀⁻¹ * (o₀ * c) := by group
    refine ⟨o₀ * c * a * (o₀ * c)⁻¹, mem_subgroupOf.2 ?_, ?_⟩
    · have e : ((o₀ * c * a * (o₀ * c)⁻¹ : Cz) : G) = (o : G) * c * a * ((o : G) * c)⁻¹ := by
        rw [← ho₀e]
        rfl
      rw [e]
      exact hnA
    · have h1 : f o₀ = 1 := (QuotientGroup.eq_one_iff _).2 ho₀
      rw [map_mul, map_mul, map_inv, map_mul, h1, one_mul, QuotientGroup.mk'_apply]
  have hMo : Odd (Nat.card (A.map f)) := by
    have hdvd : Nat.card (A.map f) ∣ Nat.card A :=
      Subgroup.card_dvd_of_surjective (f.subgroupMap_surjective A)
    have hA' : Nat.card A = Nat.card (theta 𝔵) :=
      Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
    exact Odd.of_dvd_nat (hA' ▸ odd_card_theta 𝔵) hdvd
  have hbot : A.map f = ⊥ := by
    have h := le_sSup (s := {K : Subgroup (Cz ⧸ pPrimeCore 2 Cz) |
      K.Normal ∧ Nat.Coprime 2 (Nat.card K)}) ⟨hMn, Nat.coprime_two_left.2 hMo⟩
    change _ ≤ pPrimeCore 2 (Cz ⧸ pPrimeCore 2 Cz) at h
    rw [(pPrimeCore_two_facts (X := Cz)).1] at h
    exact le_bot_iff.1 h
  intro y hy
  have hyA : (⟨y, hle hy⟩ : Cz) ∈ A := mem_subgroupOf.2 hy
  have h1 : f ⟨y, hle hy⟩ ∈ A.map f := mem_map_of_mem f hyA
  rw [hbot, mem_bot, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

end CFSG.ComponentClassification.GrSLit.ONanBal
