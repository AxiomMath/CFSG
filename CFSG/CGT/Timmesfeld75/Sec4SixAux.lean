module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.CGT.Timmesfeld75

open scoped commutatorElement

section Perfect

variable {K X : Type*} [Group K] [Group X]

theorem exists_ne_one_ne_of_four_le_card (S : Subgroup X) [Finite S] (hS : 4 ≤ Nat.card S) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have := Fintype.ofFinite S
  rw [Nat.card_eq_fintype_card] at hS
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 (by omega : 2 < Fintype.card S)
  by_cases ha : a = 1
  · exact ⟨b, b.2, c, c.2, fun h => hab (ha ▸ (Subtype.ext h).symm), fun h => hac
      (ha ▸ (Subtype.ext h).symm), fun h => hbc (Subtype.ext h)⟩
  · by_cases hb : b = 1
    · exact ⟨a, a.2, c, c.2, fun h => ha (Subtype.ext h), fun h => hbc (hb ▸ (Subtype.ext h).symm),
        fun h => hac (Subtype.ext h)⟩
    · exact ⟨a, a.2, b, b.2, fun h => ha (Subtype.ext h), fun h => hb (Subtype.ext h),
        fun h => hab (Subtype.ext h)⟩

theorem commutator_eq_top_of_transitive (ι : X →* K) {S : Subgroup X} [Finite S]
    (hS4 : 4 ≤ Nat.card S)
    (htrans : ∀ x ∈ S, x ≠ 1 → ∀ y ∈ S, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (S : Set X), g * x * g⁻¹ = y)
    (hcl : Subgroup.normalClosure ((S.map ι : Subgroup K) : Set K) = ⊤) :
    commutator K = ⊤ := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hx₀1, hy₀1, hxy⟩ := exists_ne_one_ne_of_four_le_card S hS4
  obtain ⟨g, -, hg⟩ := htrans x₀ hx₀ hx₀1 y₀ hy₀ hy₀1
  have hw : y₀ * x₀⁻¹ ∈ S := S.mul_mem hy₀ (S.inv_mem hx₀)
  have hw1 : y₀ * x₀⁻¹ ≠ 1 := fun h => hxy (mul_inv_eq_one.1 h).symm
  have hcomm : ι (y₀ * x₀⁻¹) ∈ commutator K := by
    have : ι (y₀ * x₀⁻¹) = ⁅ι g, ι x₀⁆ := by
      rw [← hg, commutatorElement_def]
      simp [map_mul, map_inv]
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hS : S.map ι ≤ commutator K := by
    rintro _ ⟨s, hs, rfl⟩
    by_cases hs1 : s = 1
    · rw [hs1, map_one]
      exact Subgroup.one_mem _
    · obtain ⟨g', -, hg'⟩ := htrans _ hw hw1 s hs hs1
      rw [← hg', map_mul, map_mul, map_inv]
      exact (inferInstance : (commutator K).Normal).conj_mem _ hcomm _
  have hle : Subgroup.normalClosure ((S.map ι : Subgroup K) : Set K) ≤ commutator K :=
    Subgroup.normalClosure_le_normal hS
  rw [hcl] at hle
  exact top_le_iff.1 hle

end Perfect

section Six

variable {Y : Type*} [Group Y] [Finite Y]

theorem two_pow_modEq_eq {r m k : ℕ} (hr : r = 13 ∨ r = 19) (hm : m ≤ 6) (hk : k ≤ m)
    (h : 2 ^ m ≡ 2 ^ k [MOD r]) : k = m := by
  rcases hr with rfl | rfl <;> interval_cases m <;> interval_cases k <;>
    first | rfl | (exfalso; revert h; decide)

theorem sylow_centralizes_of_card_two_pow (N : Subgroup Y) [N.Normal] {m : ℕ}
    (hNcard : Nat.card N = 2 ^ m) (hm : m ≤ 6) {r : ℕ} (hr : r = 13 ∨ r = 19)
    (P : Sylow r Y) : ∀ p ∈ (P : Subgroup Y), ∀ n ∈ N, p * n = n * p := by
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> decide
  have : Fact r.Prime := ⟨hrp⟩
  let _ : MulAction (P : Subgroup Y) N :=
    MulAction.compHom N ((MulAut.conjNormal : Y →* MulAut N).comp (P : Subgroup Y).subtype)
  have hsmul : ∀ (p : (P : Subgroup Y)) (x : N), ((p • x : N) : Y) = (p : Y) * x * (p : Y)⁻¹ :=
    fun p x => MulAut.conjNormal_apply (p : Y) x
  have hmod := (P.isPGroup').card_modEq_card_fixedPoints N
  let F : Subgroup Y := N ⊓ Subgroup.centralizer ((P : Subgroup Y) : Set Y)
  have hFle : F ≤ N := inf_le_left
  have hFcard : Nat.card (MulAction.fixedPoints (P : Subgroup Y) N) = Nat.card F := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : Y), x.1.2, Subgroup.mem_centralizer_iff.2 fun p hp => ?_⟩
        invFun := fun y => ⟨⟨(y : Y), y.2.1⟩, fun p => Subtype.ext ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have h1 := congrArg Subtype.val (x.2 ⟨p, hp⟩)
      rw [hsmul] at h1
      change p * (x.1 : Y) = (x.1 : Y) * p
      have h2 : (p * (x.1 : Y) * p⁻¹) = (x.1 : Y) := h1
      calc p * (x.1 : Y) = (p * (x.1 : Y) * p⁻¹) * p := by group
        _ = (x.1 : Y) * p := by rw [h2]
    · rw [hsmul]
      have h1 : (p : Y) * (y : Y) = (y : Y) * (p : Y) :=
        Subgroup.mem_centralizer_iff.1 y.2.2 (p : Y) p.2
      show (p : Y) * (y : Y) * (p : Y)⁻¹ = (y : Y)
      rw [h1]
      group
  obtain ⟨k, hk, hFk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hNcard ▸ Subgroup.card_dvd_of_le hFle)
  have hkm : k = m := by
    rw [hFcard, hFk, hNcard] at hmod
    exact two_pow_modEq_eq hr hm hk hmod
  subst hkm
  have hFN : F = N :=
    Subgroup.eq_of_le_of_card_ge hFle (by rw [hNcard, hFk])
  intro p hp n hn
  have hnF : n ∈ F := hFN ▸ hn
  exact Subgroup.mem_centralizer_iff.1 hnF.2 p hp

theorem normal_le_center_of_perfect_quotient (N : Subgroup Y) [N.Normal]
    (hNab : ∀ n ∈ N, ∀ n' ∈ N, n * n' = n' * n) {m : ℕ} (hNcard : Nat.card N = 2 ^ m)
    (hm : m ≤ 6) {r : ℕ} (hr : r = 13 ∨ r = 19) (hperf : commutator (Y ⧸ N) = ⊤)
    (hsimple : IsSimpleGroup ((Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N)))
    (hrB : r ∣ Nat.card ((Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N))) : N ≤ Subgroup.center Y := by
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> decide
  have : Fact r.Prime := ⟨hrp⟩
  have := hsimple
  let π : Y →* (Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N) :=
    (QuotientGroup.mk' (Subgroup.center (Y ⧸ N))).comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P⟩ : Nonempty (Sylow r Y) := inferInstance
  have hPC := sylow_centralizes_of_card_two_pow N hNcard hm hr P
  have hPπ : ∃ p ∈ (P : Subgroup Y), π p ≠ 1 := by
    by_contra hcon
    have hall : ∀ p ∈ (P : Subgroup Y), π p = 1 := fun p hp => by
      by_contra h1
      exact hcon ⟨p, hp, h1⟩
    have hle : (P : Subgroup Y) ≤ π.ker := fun p hp => MonoidHom.mem_ker.2 (hall p hp)
    have h1 := Subgroup.index_dvd_of_le hle
    have h2 : π.ker.index = Nat.card ((Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N)) := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective π hπ, Subgroup.card_top]
    exact P.not_dvd_index ((h2 ▸ hrB).trans h1)
  obtain ⟨p, hpP, hpπ⟩ := hPπ
  let C : Subgroup Y := Subgroup.centralizer (N : Set Y)
  have hCnormal : C.Normal := Subgroup.normal_centralizer
  have hpC : p ∈ C := Subgroup.mem_centralizer_iff.2 fun n hn => (hPC p hpP n hn).symm
  have hCπ : C.map π = ⊤ := by
    have : (C.map π).Normal := hCnormal.map π hπ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map π) with h | h
    · exfalso
      have hmem : π p ∈ C.map π := Subgroup.mem_map_of_mem π hpC
      rw [h, Subgroup.mem_bot] at hmem
      exact hpπ hmem
    · exact h
  have hdecomp : ∀ yb : Y ⧸ N, ∃ c ∈ C,
      (QuotientGroup.mk c : Y ⧸ N)⁻¹ * yb ∈ Subgroup.center (Y ⧸ N) := by
    intro yb
    have hb : (QuotientGroup.mk yb : (Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N)) ∈ C.map π := by
      rw [hCπ]
      trivial
    obtain ⟨c, hc, hcb⟩ := hb
    exact ⟨c, hc, QuotientGroup.eq.1 hcb⟩
  let Cb : Subgroup (Y ⧸ N) := C.map (QuotientGroup.mk' N)
  have hCb : Cb.Normal := hCnormal.map _ (QuotientGroup.mk'_surjective N)
  have hcomm : ∀ y₁ y₂ : Y ⧸ N, ⁅y₁, y₂⁆ ∈ Cb := by
    intro y₁ y₂
    obtain ⟨c₁, hc₁, hz₁⟩ := hdecomp y₁
    obtain ⟨c₂, hc₂, hz₂⟩ := hdecomp y₂
    let ρ : (Y ⧸ N) →* (Y ⧸ N) ⧸ Cb := QuotientGroup.mk' Cb
    have hρ : ∀ c ∈ C, ρ (QuotientGroup.mk c) = 1 := fun c hc =>
      (QuotientGroup.eq_one_iff _).2 ⟨c, hc, rfl⟩
    have e1 : ρ y₁ = ρ ((QuotientGroup.mk c₁ : Y ⧸ N)⁻¹ * y₁) :=
      calc ρ y₁ = ρ (QuotientGroup.mk c₁) * ρ ((QuotientGroup.mk c₁ : Y ⧸ N)⁻¹ * y₁) := by
            rw [← map_mul]
            group
        _ = ρ ((QuotientGroup.mk c₁ : Y ⧸ N)⁻¹ * y₁) := by rw [hρ c₁ hc₁, one_mul]
    have e2 : ρ y₂ = ρ ((QuotientGroup.mk c₂ : Y ⧸ N)⁻¹ * y₂) :=
      calc ρ y₂ = ρ (QuotientGroup.mk c₂) * ρ ((QuotientGroup.mk c₂ : Y ⧸ N)⁻¹ * y₂) := by
            rw [← map_mul]
            group
        _ = ρ ((QuotientGroup.mk c₂ : Y ⧸ N)⁻¹ * y₂) := by rw [hρ c₂ hc₂, one_mul]
    have hzz : (QuotientGroup.mk c₂ : Y ⧸ N)⁻¹ * y₂ * ((QuotientGroup.mk c₁ : Y ⧸ N)⁻¹ * y₁) =
        (QuotientGroup.mk c₁ : Y ⧸ N)⁻¹ * y₁ * ((QuotientGroup.mk c₂ : Y ⧸ N)⁻¹ * y₂) :=
      Subgroup.mem_center_iff.1 hz₁ _
    have hρcomm : ρ y₁ * ρ y₂ = ρ y₂ * ρ y₁ := by
      rw [e1, e2, ← map_mul, ← map_mul, hzz]
    have h1 : ρ ⁅y₁, y₂⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hρcomm
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hCbtop : Cb = ⊤ := by
    have : (⊤ : Subgroup (Y ⧸ N)) ≤ Cb := by
      rw [← hperf]
      exact Subgroup.commutator_le.2 fun g₁ _ g₂ _ => hcomm g₁ g₂
    exact top_le_iff.1 this
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : (QuotientGroup.mk y : Y ⧸ N) ∈ Cb := by
    rw [hCbtop]
    trivial
  obtain ⟨c, hc, hcy⟩ := hy
  have hn' : c⁻¹ * y ∈ N := QuotientGroup.eq.1 hcy
  have hnc : n * c = c * n := Subgroup.mem_centralizer_iff.1 hc n hn
  have hnn' : n * (c⁻¹ * y) = (c⁻¹ * y) * n := hNab n hn _ hn'
  have e : y = c * (c⁻¹ * y) := by group
  rw [e]
  calc c * (c⁻¹ * y) * n = c * ((c⁻¹ * y) * n) := mul_assoc _ _ _
    _ = c * (n * (c⁻¹ * y)) := by rw [hnn']
    _ = (c * n) * (c⁻¹ * y) := (mul_assoc _ _ _).symm
    _ = (n * c) * (c⁻¹ * y) := by rw [hnc]
    _ = n * (c * (c⁻¹ * y)) := mul_assoc _ _ _

end Six

end CFSG.CGT.Timmesfeld75
