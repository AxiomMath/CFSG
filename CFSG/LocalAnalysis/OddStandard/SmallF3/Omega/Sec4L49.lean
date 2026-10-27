module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4AData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem zpowers_eq_one_or_of_orderOf_two {H : Type} [Group H] {t : H}
    (ht : orderOf t = 2) {p : H} (hp : p ∈ Subgroup.zpowers t) : p = 1 ∨ p = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have ht2 : t ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ht2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

private theorem mem_sup_zpowers_cases {t u x : G} (ht : orderOf t = 2) (hu : orderOf u = 2)
    (hut : u * t = t * u) (hx : x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers t) :
    x = 1 ∨ x = u ∨ x = t ∨ x = t * u := by
  have hcomm : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_left (show Commute u t from hut) i).zpow_right j).eq
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (CFSG.OddStandard.SmallF3.HarrisU33.mem_sup_iff_of_commute hcomm).mp hx
  rcases zpowers_eq_one_or_of_orderOf_two hu ha with rfl | rfl <;>
    rcases zpowers_eq_one_or_of_orderOf_two ht hb with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inr (Or.inl (by simp)))
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr (Or.inr hut))

private theorem mem_centralizer_conj_iff {K : Subgroup G} {m x : G}
    (hK : m ∈ normalizer (K : Set G)) :
    x ∈ centralizer (K : Set G) ↔ m * x * m⁻¹ ∈ centralizer (K : Set G) := by
  have hKm : ∀ k : G, k ∈ K ↔ m * k * m⁻¹ ∈ K :=
    fun k => Subgroup.mem_normalizer_iff.mp hK k
  have hKm' : ∀ k : G, k ∈ K ↔ m⁻¹ * k * m ∈ K :=
    fun k => Subgroup.mem_normalizer_iff''.mp hK k
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro k hk
    have hk' : m⁻¹ * k * m ∈ K := (hKm' k).mp hk
    have hcomm := hx (m⁻¹ * k * m) hk'
    calc k * (m * x * m⁻¹)
        = (m * (m⁻¹ * k * m) * m⁻¹) * (m * x * m⁻¹) := by group
      _ = m * ((m⁻¹ * k * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * k * m)) * m⁻¹ := by rw [hcomm]
      _ = (m * x * m⁻¹) * k := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro k hk
    have hk' : m * k * m⁻¹ ∈ K := (hKm k).mp hk
    have hcomm := hx (m * k * m⁻¹) hk'
    calc k * x
        = m⁻¹ * ((m * k * m⁻¹) * (m * x * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * x * m⁻¹) * (m * k * m⁻¹)) * m := by rw [hcomm]
      _ = x * k := by group

theorem sec4_centK_u {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
    {φ : (Fin 7 → ZMod 2) → G} (hD : Sec4AData t L S z A B φ) {u : G} (huB : u ∈ B)
    (hu2 : orderOf u = 2) (hu6 : InducesTypeSome L u 7 1 6 (-1)) {K : Subgroup G}
    (hK : IsComponentIn K (L ⊓ centralizer ({u} : Set G))) (huK : u ∈ K)
    (hK43 : IsTwoU43 (K ⧸ oddCore K)) : centralizer (K : Set G) ⊓ B = zpowers u := by
  obtain ⟨v, hv, hφv⟩ := (hD.bdata.perm.2.2.1 u).mp huB
  have hv0 : v ≠ 0 := by
    intro h0
    have hu1 : u = 1 := by
      rw [← hφv, h0, IsPermModuleVia.map_zero hD.bdata.perm]
    rw [hu1, orderOf_one] at hu2
    exact absurd hu2 (by decide)
  have hw : vecWeight v = 6 := by
    have hphi : InducesTypeSome L (φ v) 7 1 6 (-1) := by rwa [hφv]
    exact (hD.bdata.type6 v hv hv0).mpr hphi
  have hres := hD.bdata.centK v hv hw K (by rwa [hφv]) (by rwa [hφv]) hK43
  rwa [hφv] at hres

theorem sec4_inf_centralizer_K [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
    {φ : (Fin 7 → ZMod 2) → G} (hctx : Sec4Ctx G t L S z) (hD : Sec4AData t L S z A B φ)
    {u : G} {K : Subgroup G} (hKL : K ≤ L) (huB : u ∈ B)
    (hcent : centralizer (K : Set G) ⊓ B = zpowers u) :
    A ⊓ centralizer (K : Set G) = zpowers u ⊔ zpowers t := by
  haveI : IsMulCommutative ↥A := hD.isMax.2.1.1
  have hcomm : ∀ b ∈ B, ∀ p ∈ zpowers t, b * p = p * b := by
    intro b hb p hp
    have hbA : b ∈ A := by rw [hD.A_eq]; exact Subgroup.mem_sup_left hb
    have hpA : p ∈ A := by rw [hD.A_eq]; exact Subgroup.mem_sup_right hp
    exact congrArg Subtype.val (mul_comm' (⟨b, hbA⟩ : A) ⟨p, hpA⟩)
  have htC : t ∈ centralizer (K : Set G) :=
    Subgroup.centralizer_le hKL
      (sec4_t_mem_centralizer hctx.toSec4Setting.toSec3SettingLB.toSec3Setting)
  have huC : u ∈ centralizer (K : Set G) := by
    have hu : u ∈ centralizer (K : Set G) ⊓ B := by
      rw [hcent]
      exact Subgroup.mem_zpowers u
    exact hu.1
  refine le_antisymm ?_ ?_
  · intro a ha
    rw [Subgroup.mem_inf] at ha
    obtain ⟨haA, haC⟩ := ha
    rw [hD.A_eq] at haA
    obtain ⟨b, hb, p, hp, rfl⟩ :=
      (CFSG.OddStandard.SmallF3.HarrisU33.mem_sup_iff_of_commute hcomm).mp haA
    have hpC : p ∈ centralizer (K : Set G) := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      exact (centralizer (K : Set G)).zpow_mem htC k
    have hbC : b ∈ centralizer (K : Set G) := by
      have hbp : b * p ∈ centralizer (K : Set G) := haC
      have : b = (b * p) * p⁻¹ := by group
      rw [this]
      exact (centralizer (K : Set G)).mul_mem hbp ((centralizer (K : Set G)).inv_mem hpC)
    have hbu : b ∈ zpowers u := by
      rw [← hcent]
      exact ⟨hbC, hb⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbu) (Subgroup.mem_sup_right hp)
  · refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr ⟨?_, huC⟩
      rw [hD.A_eq]
      exact Subgroup.mem_sup_left huB
    · refine Subgroup.zpowers_le.mpr ⟨?_, htC⟩
      rw [hD.A_eq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem sec4_centralizer_normalizes [Finite G] (h39 : Asc82Lemma39) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {u : G} {K : Subgroup G} (hu2 : orderOf u = 2) (huL : u ∈ L)
    (huK : u ∈ K) (hK : IsComponentIn K (L ⊓ centralizer ({u} : Set G)))
    (hK43 : IsTwoU43 (K ⧸ oddCore K)) {m : G} (hm : m ∈ centralizer ({u} : Set G)) :
    m ∈ normalizer (K : Set G) := by
  obtain ⟨hKC, hKF, huniq⟩ := h39 G t L hS u K hu2 huL huK hK hK43
  exact mem_normalizer_of_conjugate_eq
    (huniq (CFSG.conjugate K m) (hKC.conjugate hm) (hKF.conjugate m))

theorem sec4_mem_normalizer_inf_centralizer {A K : Subgroup G} {m : G}
    (hA : m ∈ normalizer (A : Set G)) (hK : m ∈ normalizer (K : Set G)) :
    m ∈ normalizer ((A ⊓ centralizer (K : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  have hAiff := Subgroup.mem_normalizer_iff.mp hA x
  constructor
  · rintro ⟨hxA, hxC⟩
    exact ⟨hAiff.mp hxA, (mem_centralizer_conj_iff hK).mp hxC⟩
  · rintro ⟨hxA, hxC⟩
    exact ⟨hAiff.mpr hxA, (mem_centralizer_conj_iff hK).mpr hxC⟩

theorem sec4_dichotomy {t u : G} (ht2 : orderOf t = 2) (hu2 : orderOf u = 2)
    (hut : u * t = t * u) (hne : t ≠ u) (P : G → Prop) (hP : ∀ m, P m → m * u = u * m)
    (hN : ∀ m, P m → m ∈ normalizer ((zpowers u ⊔ zpowers t : Subgroup G) : Set G)) :
    (∀ m, P m → m * t = t * m) ∨
      ((∃ h : G, h⁻¹ * t * h = t * u) ∧
        ∀ m, P m → m ∈ normalizer ((zpowers u ⊔ zpowers t : Subgroup G) : Set G)) := by
  by_cases hall : ∀ m, P m → m * t = t * m
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨m₀, hm₀P, hm₀ne⟩ := hall
    have htD : t ∈ (Subgroup.zpowers u ⊔ Subgroup.zpowers t : Subgroup G) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hsD : m₀ * t * m₀⁻¹ ∈ (Subgroup.zpowers u ⊔ Subgroup.zpowers t : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp (hN m₀ hm₀P) t).mp htD
    have hcases := mem_sup_zpowers_cases ht2 hu2 hut hsD
    have ht_ne_one : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht2
      exact absurd ht2 (by decide)
    have hne_t : m₀ * t * m₀⁻¹ ≠ t := by
      intro h
      exact hm₀ne (by
        calc m₀ * t = (m₀ * t * m₀⁻¹) * m₀ := by group
          _ = t * m₀ := by rw [h])
    have hne_one : m₀ * t * m₀⁻¹ ≠ 1 := by
      intro h
      apply ht_ne_one
      calc t = m₀⁻¹ * (m₀ * t * m₀⁻¹) * m₀ := by group
        _ = m₀⁻¹ * 1 * m₀ := by rw [h]
        _ = 1 := by group
    have hm₀u : m₀ * u = u * m₀ := hP m₀ hm₀P
    have hne_u : m₀ * t * m₀⁻¹ ≠ u := by
      intro h
      apply hne
      have h' : u * m₀⁻¹ = m₀⁻¹ * u := by
        calc u * m₀⁻¹ = m₀⁻¹ * (m₀ * u) * m₀⁻¹ := by group
          _ = m₀⁻¹ * (u * m₀) * m₀⁻¹ := by rw [hm₀u]
          _ = m₀⁻¹ * u := by group
      calc t = m₀⁻¹ * (m₀ * t * m₀⁻¹) * m₀ := by group
        _ = m₀⁻¹ * u * m₀ := by rw [h]
        _ = u := by rw [← h', mul_assoc, inv_mul_cancel, mul_one]
    refine ⟨⟨m₀⁻¹, ?_⟩, hN⟩
    rw [inv_inv]
    rcases hcases with h1 | h2 | h3 | h4
    · exact absurd h1 hne_one
    · exact absurd h2 hne_u
    · exact absurd h3 hne_t
    · exact h4

theorem asc82Lemma49_of (h39 : Asc82Lemma39) (hAD : Asc82ADataExists) (hK6 : Asc82FactK6) :
    Asc82Lemma49 := by
  intro G _ _ t L S z hctx A hA u huAL hu2 hu6
  obtain ⟨A₀, B, φ, hD⟩ := hAD G t L S z hctx
  have hAeq : A = A₀ := hD.unique A hA
  rw [hAeq] at huAL ⊢
  have huB : u ∈ B := by
    rw [← hD.B_eq]
    exact huAL
  have huL : u ∈ L := (Subgroup.mem_inf.mp huAL).2
  obtain ⟨K, hK, huK, hK43⟩ :=
    hK6 G L (sec4_isOmega7Group hctx.toSec4Setting) u huL hu2 hu6
  have hcent := sec4_centK_u hD huB hu2 hu6 hK huK hK43
  have hAK := sec4_inf_centralizer_K hctx hD (hK.1.trans inf_le_left) huB hcent
  have hut : u * t = t * u :=
    Subgroup.mem_centralizer_iff.mp
      (sec4_t_mem_centralizer hctx.toSec4Setting.toSec3SettingLB.toSec3Setting) u huL
  have hne : t ≠ u := by
    rintro rfl
    exact sec4_t_not_mem hctx.toSec4Setting huL
  let P : G → Prop := fun m => m ∈ normalizer (A₀ : Set G) ∧ m * u = u * m
  have hP : ∀ m, P m → m * u = u * m := fun _ hm => hm.2
  have hN : ∀ m, P m → m ∈ normalizer ((zpowers u ⊔ zpowers t : Subgroup G) : Set G) := by
    intro m hm
    have hmK : m ∈ normalizer (K : Set G) :=
      sec4_centralizer_normalizes h39 hctx.toSec4Setting.toSec3SettingLB hu2 huL huK hK hK43 (by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact hm.2.symm)
    have hmN := sec4_mem_normalizer_inf_centralizer hm.1 hmK
    rwa [hAK] at hmN
  have hdich := sec4_dichotomy hctx.involution hu2 hut hne P hP hN
  rcases hdich with h | ⟨hex, hnorm⟩
  · left
    intro m hm hmu
    exact h m ⟨hm, hmu⟩
  · right
    exact ⟨hex, fun m hm hmu => hnorm m ⟨hm, hmu⟩⟩

end CFSG.OddStandard.SmallF3.Omega
