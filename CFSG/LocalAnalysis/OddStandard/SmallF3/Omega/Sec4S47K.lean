module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47Odd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private theorem Sec4FSetup.cent_A_le_cent_t (h : Sec4FSetup t L S z A B φ) {c : G}
    (hc : c ∈ centralizer (A : Set G)) : c ∈ centralizer ({t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hc t h.t_mem_A).symm

theorem Sec4FSetup.normalizer_B_le (h : Sec4FSetup t L S z A B φ) :
    L ⊓ normalizer (B : Set G) ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) := by
  intro u hu
  obtain ⟨huL, huB⟩ := Subgroup.mem_inf.mp hu
  have hfwd : ∀ u : G, u ∈ L → u ∈ normalizer (B : Set G) → ∀ x ∈ A, u * x * u⁻¹ ∈ A := by
    intro u huL huB x hx
    obtain ⟨b, hb, hxb⟩ := h.mem_A_cases hx
    have hub : u * b * u⁻¹ ∈ B := (Subgroup.mem_set_normalizer_iff.mp huB b).mp hb
    have hut : u * t * u⁻¹ = t := by
      rw [show u * t = t * u from (h.t_cent_L huL).symm]
      group
    rcases hxb with rfl | rfl
    · exact h.B_le_A hub
    · have hsplit : u * (b * t) * u⁻¹ = (u * b * u⁻¹) * (u * t * u⁻¹) := by group
      rw [hsplit, hut]
      exact A.mul_mem (h.B_le_A hub) h.t_mem_A
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (h.t_cent_L huL).symm, ?_⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨hfwd u huL huB x, fun hx => ?_⟩
  have h2 := hfwd u⁻¹ (L.inv_mem huL) ((normalizer (B : Set G)).inv_mem huB) _ hx
  have h3 : u⁻¹ * (u * x * u⁻¹) * u = x := by group
  rwa [inv_inv, h3] at h2

theorem Sec4FSetup.oddCore_le_of_index_two (h : Sec4FSetup t L S z A B φ) {K : Subgroup G}
    (hidx : K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2) :
    oddCoreIn (centralizer (A : Set G)) ≤ K := by
  intro o ho
  have hoC : o ∈ centralizer (A : Set G) := (oddCoreIn_normal _).1 ho
  have hoX : o ∈ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) :=
    ⟨h.cent_A_le_cent_t hoC, Subgroup.centralizer_le_normalizer (A : Set G) hoC⟩
  have hidx' : (K.subgroupOf (centralizer ({t} : Set G) ⊓ normalizer (A : Set G))).index = 2 :=
    hidx
  obtain ⟨k, hk⟩ := odd_orderOf_of_mem_oddCoreIn ho
  set x : ↥(centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) := ⟨o, hoX⟩
  have hxo : orderOf x = orderOf o := Subgroup.orderOf_mk o hoX
  have hx1 : x ^ (2 * k + 1) = 1 := by rw [← hk, ← hxo]; exact pow_orderOf_eq_one x
  have hxsq : x = (x ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, show (k + 1) * 2 = (2 * k + 1) + 1 by ring, pow_succ, hx1, one_mul]
  have hmem : x ∈ K.subgroupOf (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) := by
    rw [hxsq]
    exact Subgroup.sq_mem_of_index_two hidx' _
  exact (Subgroup.mem_subgroupOf).mp hmem

theorem Sec4FSetup.B_le_of_index_two (h : Sec4FSetup t L S z A B φ) {K : Subgroup G}
    (hidx : K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2) : B ≤ K := by
  set X : Subgroup G := centralizer ({t} : Set G) ⊓ normalizer (A : Set G) with hXdef
  have hidx' : (K.subgroupOf X).index = 2 := hidx
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ K := by
    intro a ha b hb
    have key : (⟨a, ha⟩ : ↥X) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥X)⁻¹ * (⟨b, hb⟩ : ↥X)⁻¹ ∈
        K.subgroupOf X := by
      simp only [Subgroup.mul_mem_iff_of_index_two hidx', inv_mem_iff]
      tauto
    exact (Subgroup.mem_subgroupOf).mp key
  have hconj : ∀ k ∈ X, ∀ x ∈ K, x ∈ X → k * x * k⁻¹ ∈ K := by
    intro k hk x hx hxX
    have hn := Subgroup.normal_of_index_eq_two hidx'
    have := hn.conj_mem ⟨x, hxX⟩ ((Subgroup.mem_subgroupOf).mpr hx) ⟨k, hk⟩
    exact (Subgroup.mem_subgroupOf).mp this
  obtain ⟨σ, hσA, hσ01⟩ := sec4F_exists_alt 0 1
  obtain ⟨m, hmN, hmσ⟩ := h.exists_realizes_alt hσA
  have hmt : m * t * m⁻¹ = t := by
    have := hmσ none
    rwa [Equiv.optionCongr_apply, Option.map_none, h.pt_none] at this
  have hmX : m ∈ X := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hmN⟩
    calc m * t = m * t * m⁻¹ * m := by group
      _ = t * m := by rw [hmt]
  set a : G := sec4MPt t φ (some 0) with ha_def
  have haA : a ∈ A := sec4MPt_mem_A h.data (some 0)
  have haX : a ∈ X :=
    ⟨h.mem_cent_t_of_mem_A haA, Subgroup.le_normalizer haA⟩
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left (h.A_sq haA)
  have hma : m * a * m⁻¹ = sec4MPt t φ (some 1) := by
    rw [ha_def, hmσ (some 0), Equiv.optionCongr_apply, Option.map_some, hσ01]
  set v : Fin 7 → ZMod 2 := sec4MW 0 + sec4MW 1 with hv_def
  have hv : IsEvenVec v := isEvenVec_add (sec4MW_even 0) (sec4MW_even 1)
  have hw : vecWeight v = 2 := by
    rw [hv_def]
    decide
  have hφv : φ v = a * m * a⁻¹ * m⁻¹ := by
    have h1 := sec4MPt_mul h.data (some 0) (some 1)
    have h2 : sec4MV (some (0 : Fin 7)) + sec4MV (some 1) = v := rfl
    rw [h2] at h1
    rw [← h1, ← hma, hainv, ha_def]
    group
  have hφvK : φ v ∈ K := hφv ▸ hcomm a haX m hmX
  have hφvX : φ v ∈ X := by
    have hφvA : φ v ∈ A := h.B_le_A (IsPermModuleVia.mem h.data.bdata.perm hv)
    exact ⟨h.mem_cent_t_of_mem_A hφvA, Subgroup.le_normalizer hφvA⟩
  rw [← IsPermModuleVia.closure_conjClassIn h.data.bdata.perm hv (Or.inl hw),
    Subgroup.closure_le]
  rintro y ⟨k, hk, rfl⟩
  exact hconj k (h.normalizer_B_le hk) (φ v) hφvK hφvX

theorem Sec4FSetup.inf_cent_le_of_index_two (h : Sec4FSetup t L S z A B φ) {K : Subgroup G}
    (hidx : K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2) (htK : t ∉ K) :
    K ⊓ centralizer (A : Set G) ≤ B ⊔ oddCoreIn (centralizer (A : Set G)) := by
  rintro k ⟨hkK, hkC⟩
  have hBK := h.B_le_of_index_two hidx
  have hOK := h.oddCore_le_of_index_two hidx
  rw [← h.sup_oddCore] at hkC
  have hcomm : ∀ a ∈ A, ∀ o ∈ oddCoreIn (centralizer (A : Set G)), a * o = o * a :=
    fun a ha o ho => Subgroup.mem_centralizer_iff.mp ((oddCoreIn_normal _).1 ho) a ha
  obtain ⟨a, haA, o, ho, rfl⟩ := sec4F_mem_sup_comm hcomm hkC
  obtain ⟨b, hb, hab⟩ := h.mem_A_cases haA
  rcases hab with rfl | rfl
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right ho)
  · exfalso
    apply htK
    have ht : t = b⁻¹ * (b * t * o) * o⁻¹ := by group
    rw [ht]
    exact K.mul_mem (K.mul_mem (K.inv_mem (hBK hb)) hkK) (K.inv_mem (hOK ho))

theorem Sec4FSetup.mem_or_mul_mem_of_index_two (h : Sec4FSetup t L S z A B φ) {K : Subgroup G}
    (hidx : K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2) (htK : t ∉ K)
    {m : G} (hm : m ∈ centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) : m ∈ K ∨ m * t ∈ K := by
  have hidx' : (K.subgroupOf (centralizer ({t} : Set G) ⊓ normalizer (A : Set G))).index = 2 :=
    hidx
  have htX : t ∈ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) :=
    ⟨h.mem_cent_t_of_mem_A h.t_mem_A, Subgroup.le_normalizer h.t_mem_A⟩
  by_cases hmK : m ∈ K
  · exact Or.inl hmK
  · right
    have key := (Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨m, hm⟩) (b := ⟨t, htX⟩))
    simp only [Subgroup.mem_subgroupOf] at key
    exact key.mpr (iff_of_false hmK htK)

end CFSG.OddStandard.SmallF3.Omega
