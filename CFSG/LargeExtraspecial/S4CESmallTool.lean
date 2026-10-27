module

public import CFSG.LargeExtraspecial.S4CEToolTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup
open scoped commutatorElement Pointwise

theorem mem_commutator_of_perfect {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hperf : commutator G = ⊤) {H : Subgroup G} (hidx : ¬ p ∣ H.index) {z : G}
    (hz : z ∈ center G) (hzH : z ∈ H) {n : ℕ} (hzp : z ^ p ^ n = 1) : z ∈ ⁅H, H⁆ := by
  let φ : ↥H →* Abelianization ↥H := Abelianization.of
  have hτ1 : MonoidHom.transfer φ z = 1 := by
    have hker : commutator G ≤ (MonoidHom.transfer φ).ker :=
      Abelianization.commutator_subset_ker _
    rw [hperf] at hker
    exact hker (mem_top z)
  have hτ2 := MonoidHom.transfer_eq_pow φ z fun k g₀ _ => by
    have hk : z ^ k ∈ center G := pow_mem hz k
    rw [mem_center_iff] at hk
    rw [mul_assoc, ← hk g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have hmem : (⟨z ^ H.index, pow_mem hzH _⟩ : ↥H) ∈ commutator ↥H := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hτ2.symm.trans hτ1
  have hzi : z ^ H.index ∈ ⁅H, H⁆ := by
    rw [← map_subtype_commutator]
    exact ⟨_, hmem, rfl⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hzp)
  have hcop : Nat.Coprime H.index (orderOf z) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hidx).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem hzi m

theorem card_sup_le_of_le_normalizer {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) : Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  have hcoe : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    coe_mul_of_right_le_normalizer_left A B hB
  calc Nat.card ↥(A ⊔ B) = Nat.card ↑((A : Set G) * (B : Set G)) := by rw [← hcoe]; rfl
    _ ≤ Nat.card (A : Set G) * Nat.card (B : Set G) := Set.natCard_mul_le
    _ = Nat.card A * Nat.card B := rfl

theorem commutator_eq_bot_of_isMulCommutative {G : Type*} [Group G] {S : Subgroup G}
    (hS : IsMulCommutative S) : ⁅S, S⁆ = ⊥ := by
  rw [eq_bot_iff, commutator_le]
  intro x hx y hy
  rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val (hS.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem commutatorElement_mul_left_of_mem_center {G : Type*} [Group G] {u u' v : G}
    (h : ⁅u', v⁆ ∈ center G) : ⁅u * u', v⁆ = ⁅u, v⁆ * ⁅u', v⁆ := by
  have hc := mem_center_iff.mp h
  calc ⁅u * u', v⁆ = u * ⁅u', v⁆ * (v * u⁻¹ * v⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅u', v⁆ * u * (v * u⁻¹ * v⁻¹) := by rw [hc u]
    _ = ⁅u', v⁆ * ⁅u, v⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅u, v⁆ * ⁅u', v⁆ := (hc _).symm

theorem commutatorElement_mul_right_of_mem_center {G : Type*} [Group G] {u v v' : G}
    (h : ⁅u, v'⁆ ∈ center G) : ⁅u, v * v'⁆ = ⁅u, v⁆ * ⁅u, v'⁆ := by
  have hc := mem_center_iff.mp h
  calc ⁅u, v * v'⁆ = u * v * u⁻¹ * ⁅u, v'⁆ * v⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅u, v'⁆ * (u * v * u⁻¹) * v⁻¹ := by rw [hc (u * v * u⁻¹)]
    _ = ⁅u, v'⁆ * ⁅u, v⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅u, v⁆ * ⁅u, v'⁆ := (hc _).symm

namespace CEHyp

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {K : Type*} [Group K]
  {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
  (h : CEHyp π E a X E₀)
include h

theorem card_E_eq : Nat.card E = Nat.card E₀ := by
  rw [← h.map_eq]
  refine Nat.card_congr (Equiv.ofBijective (fun e : E => (⟨π e, e, e.2, rfl⟩ : E.map π))
    ⟨fun e e' hee => Subtype.ext (h.eq_of_mem e.2 e'.2 (congrArg Subtype.val hee)), ?_⟩)
  rintro ⟨_, e, he, rfl⟩
  exact ⟨⟨e, he⟩, rfl⟩

theorem commutator_eq_top (hperf : E₀ ≤ ⁅E₀, stabIn X a⁆) : commutator K = ⊤ := by
  have hle := h.le_ker_of_le_commutator hperf (Abelianization.of (G := K))
    fun x y => Commute.all _ _
  rw [Abelianization.ker_of] at hle
  exact h.eq_top_of_normal (k := 1) (by rwa [Eb_one])

theorem commutator_stabIn_le : ⁅E₀, stabIn X a⁆ ≤ E₀ := by
  rw [commutator_le]
  intro e he g hg
  obtain ⟨x, rfl⟩ : g ∈ π.range := h.range_eq ▸ hg.1
  rw [← h.map_eq] at he ⊢
  obtain ⟨e', he', rfl⟩ := he
  refine ⟨⁅e', x⁆, ?_, by rw [map_commutatorElement]⟩
  rw [commutatorElement_def, show e' * x * e'⁻¹ * x⁻¹ = e' * (x * e'⁻¹ * x⁻¹) by group]
  exact mul_mem he' (h.conj_mem_of_apply_eq hg.2 (inv_mem he'))

theorem le_commutator_of_card_eq_four [Finite (V ≃ₗ[ZMod 2] V)] (hE₀ : Nat.card E₀ = 4)
    {c₁ c₂ : V ≃ₗ[ZMod 2] V} (h₁ : c₁ ∈ ⁅E₀, stabIn X a⁆) (h₂ : c₂ ∈ ⁅E₀, stabIn X a⁆)
    (h₁₁ : c₁ ≠ 1) (h₂₁ : c₂ ≠ 1) (h₁₂ : c₁ ≠ c₂) : E₀ ≤ ⁅E₀, stabIn X a⁆ := by
  set C := ⁅E₀, stabIn X a⁆ with hCdef
  have hCE : C ≤ E₀ := h.commutator_stabIn_le
  have h3 : 3 ≤ Nat.card C := by
    have hsub : ({1, c₁, c₂} : Set (V ≃ₗ[ZMod 2] V)) ⊆ (C : Set (V ≃ₗ[ZMod 2] V)) := by
      rintro x (rfl | rfl | rfl)
      · exact one_mem C
      · exact h₁
      · exact h₂
    have hcard : ({1, c₁, c₂} : Set (V ≃ₗ[ZMod 2] V)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨1, c₁, c₂, h₁₁.symm, h₂₁.symm, h₁₂, rfl⟩
    rw [← hcard, ← Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hdvd : Nat.card C ∣ 4 := hE₀ ▸ card_dvd_of_le hCE
  have hC4 : Nat.card C = 4 := by
    have hle : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card C <;> simp_all
  exact (eq_of_le_of_card_ge hCE (by rw [hC4, hE₀])).ge

theorem isMulCommutative_of_isCyclic {S : Subgroup K} (hS : IsCyclic (S.map π)) :
    IsMulCommutative S := by
  let f : S →* S.map π := (π.comp S.subtype).codRestrict (S.map π) fun x => ⟨x, x.2, rfl⟩
  refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f fun x hx => ?_
  have hx' : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (mem_center_iff.mp (h.mem_center_of_mem_ker hx') y)

theorem eq_one_of_mem_ker_of_pow_eq_one [Finite K] (hK : commutator K = ⊤) {p : ℕ}
    [hp : Fact p.Prime] (hpX : ¬ p ^ 2 ∣ Nat.card X) {z : K} (hz : π z = 1) (hzp : z ^ p = 1) :
    z = 1 := by
  by_contra hz1
  let S : Sylow p K := default
  have hzc := h.mem_center_of_mem_ker hz
  have hzS : z ∈ (S : Subgroup K) := by
    have : (zpowers z).Normal := Subgroup.normal_of_le_center (zpowers_le.mpr hzc)
    have hpz : IsPGroup p (zpowers z) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime hzp hz1)
    exact hpz.le_sylow_of_normal S (mem_zpowers z)
  have hSX : (S : Subgroup K).map π ≤ X := h.range_eq ▸ map_le_range π _
  have : Finite ((S : Subgroup K).map π) :=
    Finite.of_surjective (fun x : (S : Subgroup K) => (⟨π x, x, x.2, rfl⟩ : (S : Subgroup K).map π))
      (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (S.isPGroup'.map π)
  have hk1 : k ≤ 1 := by
    by_contra hk1
    apply hpX
    have hd := card_dvd_of_le hSX
    rw [hk] at hd
    exact (pow_dvd_pow p (by omega)).trans hd
  have hcyc : IsCyclic ((S : Subgroup K).map π) := by
    interval_cases k
    · rw [pow_zero] at hk
      have : Subsingleton ((S : Subgroup K).map π) := (Nat.card_eq_one_iff_unique.mp hk).1
      infer_instance
    · exact isCyclic_of_prime_card (by rw [hk, pow_one])
  have hcomm := commutator_eq_bot_of_isMulCommutative (h.isMulCommutative_of_isCyclic hcyc)
  have := mem_commutator_of_perfect hK S.not_dvd_index hzc hzS (n := 1) (by rwa [pow_one])
  exact hz1 (by rwa [hcomm, mem_bot] at this)

theorem ker_eq_bot_of_sq_not_dvd [Finite K] (hperf : E₀ ≤ ⁅E₀, stabIn X a⁆) {U : Subgroup K}
    (hU : U ⊓ π.ker = ⊥) {m : ℕ} (hm : Odd m) (hX : Nat.card X = Nat.card U * m)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card X) : π.ker = ⊥ := by
  have hodd := h.odd_card_ker hperf hU hm hX
  have hK := h.commutator_eq_top hperf
  by_contra hne
  have h1 : Nat.card π.ker ≠ 1 := fun h1 => hne ((card_eq_one).mp h1)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hw1 : (w : K) = 1 := h.eq_one_of_mem_ker_of_pow_eq_one hK (hsq p hp hp2) w.2 (by
    rw [← Subgroup.coe_pow, ← hw, pow_orderOf_eq_one, Subgroup.coe_one])
  rw [show w = 1 from Subtype.ext hw1, orderOf_one] at hw
  exact hp.one_lt.ne hw

end CEHyp

end CFSG.LargeExtraspecial.S4
