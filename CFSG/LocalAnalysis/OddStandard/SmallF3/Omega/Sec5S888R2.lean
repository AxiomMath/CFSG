module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

open Subgroup

open scoped commutatorElement

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

private lemma s888_mem_zpowers_iff_of_orderOf_eq_two {g x : G} (hg : orderOf g = 2) :
    x ∈ zpowers g ↔ x = 1 ∨ x = g := by
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf g k, hg, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

private lemma s888_commute_of_commutator_eq_one {x y : G}
    (h : x * y * x⁻¹ * y⁻¹ = 1) : x * y = y * x :=
  commutatorElement_eq_one_iff_mul_comm.mp (show ⁅x, y⁆ = 1 from h)

private lemma s888_zpowers_commute {z w₁ w₂ : G} (h₁ : w₁ ∈ zpowers z)
    (h₂ : w₂ ∈ zpowers z) : w₁ * w₂ = w₂ * w₁ := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp h₁
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp h₂
  exact ((Commute.refl z).zpow_left i).zpow_right j

private lemma s888_mul_zpow_comm {R : Subgroup G} {z x w : G} (hx : x ∈ R)
    (hw : w ∈ zpowers z) (hzcent : ∀ a ∈ R, a * z = z * a) : x * w = w * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact Commute.zpow_right (show Commute x z from hzcent x hx) k

theorem card_inf_centralizer_of_extra {R : Subgroup G} {z : G} (hR : Nat.card ↥R = 32)
    (hz : z ∈ R) (hz2 : z * z = 1)
    (hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ zpowers z)
    (hcent : ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x ∈ zpowers z) {e : G} (he : e ∈ R)
    (hez : e ∉ zpowers z) : Nat.card ↥(R ⊓ centralizer ({e} : Set G)) = 16 := by
  classical
  have hz1 : z ≠ 1 := by
    intro h1
    have hbot : zpowers z = ⊥ := Subgroup.zpowers_eq_bot.mpr h1
    have hRbot : R = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have hxzp : x ∈ zpowers z := by
        apply hcent x hx
        intro y hy
        have hc : x * y * x⁻¹ * y⁻¹ ∈ zpowers z := hcomm x hx y hy
        rw [hbot, Subgroup.mem_bot] at hc
        exact s888_commute_of_commutator_eq_one hc
      rwa [hbot, Subgroup.mem_bot] at hxzp
    rw [hRbot] at hR
    have h1' : (1 : ℕ) = 32 := by simpa using hR
    omega
  have hzord : orderOf z = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rwa [pow_two]) hz1
  have hzcent : ∀ x ∈ R, x * z = z * x := by
    intro x hx
    have hmem : ⁅x, z⁆ ∈ zpowers z := hcomm x hx z hz
    rw [s888_mem_zpowers_iff_of_orderOf_eq_two hzord] at hmem
    rcases hmem with h1 | h1
    · exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · exfalso
      have h2 : x * z * x⁻¹ = 1 := by
        have h3 : x * z * x⁻¹ * z⁻¹ = z := h1
        have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
        rw [hz_inv] at h3
        exact mul_right_cancel (by rw [one_mul]; exact h3)
      have h5 : z = 1 := by
        calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
          _ = x⁻¹ * 1 * x := by rw [h2]
          _ = 1 := by group
      exact hz1 h5
  have hy : ∃ y ∈ R, e * y ≠ y * e := by
    by_contra h
    push Not at h
    exact hez (hcent e he h)
  obtain ⟨y, hyR, hyne⟩ := hy
  have hyz : ⁅y, e⁆ = z := by
    have hmem : ⁅y, e⁆ ∈ zpowers z := hcomm y hyR e he
    rw [s888_mem_zpowers_iff_of_orderOf_eq_two hzord] at hmem
    rcases hmem with h1 | h1
    · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h1).symm hyne
    · exact h1
  let φ : ↥R →* ↥(zpowers z) :=
    { toFun := fun x => ⟨⁅(x : G), e⁆, hcomm (x : G) x.2 e he⟩
      map_one' := by
        apply Subtype.ext
        show ⁅(1 : G), e⁆ = (1 : G)
        rw [commutatorElement_one_left]
      map_mul' := by
        intro x y
        apply Subtype.ext
        show ⁅(x : G) * (y : G), e⁆ =
          ⁅(x : G), e⁆ * ⁅(y : G), e⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hxc : (x : G) * ⁅(y : G), e⁆ * (x : G)⁻¹ =
            ⁅(y : G), e⁆ := by
          have hwz : ⁅(y : G), e⁆ ∈ zpowers z := hcomm (y : G) y.2 e he
          rw [s888_mul_zpow_comm x.2 hwz hzcent]
          group
        rw [hxc]
        exact s888_zpowers_commute (hcomm (y : G) y.2 e he) (hcomm (x : G) x.2 e he) }
  have hker : φ.ker = (R ⊓ centralizer ({e} : Set G)).subgroupOf R := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      intro h' hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hx1 : ⁅(x : G), e⁆ = 1 := by
        exact congrArg (fun y : ↥(zpowers z) => (y : G)) h
      exact (commutatorElement_eq_one_iff_mul_comm.mp hx1).symm
    · rintro ⟨_, hce⟩
      apply Subtype.ext
      show ⁅(x : G), e⁆ = (1 : G)
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hce e (Set.mem_singleton e)).symm
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff]
    intro w _
    rw [MonoidHom.mem_range]
    have hwz : (w : G) ∈ zpowers z := w.2
    rw [s888_mem_zpowers_iff_of_orderOf_eq_two hzord] at hwz
    rcases hwz with h1 | h1
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      show ⁅(1 : G), e⁆ = (w : G)
      rw [commutatorElement_one_left, h1]
    · refine ⟨⟨y, hyR⟩, ?_⟩
      apply Subtype.ext
      show ⁅y, e⁆ = (w : G)
      rw [hyz, h1]
  have hrangecard : Nat.card ↥φ.range = 2 := by
    rw [hrange, Subgroup.card_top, Nat.card_zpowers, hzord]
  have hkercard : Nat.card ↥φ.ker = 16 := by
    have h := card_ker_mul_card_range φ
    rw [hrangecard, hR] at h
    omega
  calc Nat.card ↥(R ⊓ centralizer ({e} : Set G))
      = Nat.card ↥((R ⊓ centralizer ({e} : Set G)).subgroupOf R) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
    _ = Nat.card ↥φ.ker := by rw [← hker]
    _ = 16 := hkercard

private theorem s888_card_le_two_of_isCyclic {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (T : Subgroup A) (hT : ∀ x ∈ T, x * x = 1) : Nat.card T ≤ 2 := by
  classical
  have := Fintype.ofFinite A
  have h2 := IsCyclic.card_pow_eq_one_le (α := A) (n := 2) (by norm_num)
  have hinj : Function.Injective
      (fun t : T =>
        (⟨(t : A), by simpa [pow_two] using hT t t.2⟩ : {x : A // x ^ 2 = 1})) := by
    intro a b h
    exact Subtype.ext (congrArg (fun x : {x : A // x ^ 2 = 1} => (x : A)) h)
  have h3 := Nat.card_le_card_of_injective _ hinj
  have h4 : Nat.card {x : A // x ^ 2 = 1} =
      (Finset.univ.filter (fun x : A => x ^ 2 = 1)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem card_le_two_of_sq_eq_one [Finite G] {C P : Subgroup G} (hPC : P ≤ C)
    (hcyc : ∀ S : Sylow 2 ↥C, IsCyclic (S : Subgroup ↥C)) (hsq : ∀ x ∈ P, x * x = 1) :
    Nat.card ↥P ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq' : ∀ x ∈ P.subgroupOf C, x * x = 1 := by
    intro x hx
    exact Subtype.ext (by
      simpa using hsq (x : G) (Subgroup.mem_subgroupOf.mp hx))
  have hP'p : IsPGroup 2 ↥(P.subgroupOf C) := by
    intro x
    exact ⟨1, by
      apply Subtype.ext
      simpa [pow_two] using hsq' (x : ↥C) x.2⟩
  obtain ⟨S, hP'S⟩ := hP'p.exists_le_sylow
  haveI : IsCyclic ↥(S : Subgroup ↥C) := hcyc S
  haveI : IsCyclic ↥(P.subgroupOf C) := Subgroup.isCyclic_of_le hP'S
  have h1 : Nat.card ↥(P.subgroupOf C) ≤ 2 := by
    have h := s888_card_le_two_of_isCyclic (⊤ : Subgroup ↥(P.subgroupOf C))
      (fun x _ => by
        apply Subtype.ext
        simpa using hsq' (x : ↥C) x.2)
    rwa [Subgroup.card_top] at h
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv).symm.le.trans h1

end CFSG.OddStandard.SmallF3.Omega
