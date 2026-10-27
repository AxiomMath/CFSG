module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltFixedCard

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem a6sq_alt_big {n r : ℕ} (hn : 14 ≤ n) (hr : 1 ≤ r) (h2r : 2 * r ≤ n) :
    5760 < 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial := by
  have hQ : 0 < 2 ^ (r - 1) * r.factorial := by positivity
  rcases (by omega : r ≥ 6 ∨ r ≤ 5) with h6 | h5
  · have h1 : (6 : ℕ).factorial ≤ r.factorial := Nat.factorial_le h6
    have h2 : 2 ^ 5 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 5 * (6 : ℕ).factorial ≤ 2 ^ (r - 1) * r.factorial := Nat.mul_le_mul h2 h1
    have h4 : 2 ^ (r - 1) * r.factorial ≤ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial :=
      Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
    norm_num [Nat.factorial] at h3
    omega
  · have hk : 14 - 2 * r ≤ n - 2 * r := by omega
    have hf : (14 - 2 * r).factorial ≤ (n - 2 * r).factorial := Nat.factorial_le hk
    have hmul : 2 ^ (r - 1) * r.factorial * (14 - 2 * r).factorial ≤
        2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial := Nat.mul_le_mul_left _ hf
    refine lt_of_lt_of_le ?_ hmul
    interval_cases r <;> norm_num [Nat.factorial]

theorem a6sq_alt_numeric {n r : ℕ} (hn : 8 ≤ n) (hev : Even n) (hr : 1 ≤ r) (h2r : 2 * r ≤ n)
    (hC : 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial ≤ 5760)
    (h360 : 360 ∣ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial)
    (hS : 129600 ∣ n.factorial / 2) : n = 10 := by
  have hn14 : n < 14 := by
    by_contra h
    have := a6sq_alt_big (by omega) hr h2r
    omega
  obtain ⟨m, hm⟩ := hev
  have hn' : n = 8 ∨ n = 10 ∨ n = 12 := by omega
  rcases hn' with rfl | rfl | rfl
  · exfalso
    revert hS
    decide
  · rfl
  · exfalso
    have hr6 : r ≤ 6 := by omega
    interval_cases r <;> revert hC h360 <;> norm_num [Nat.factorial]

section Five

theorem a6sq_map_centralizer_subtype {G : Type*} [Group G] (H : Subgroup G) (x : H) :
    (centralizer ({x} : Set H)).map H.subtype = H ⊓ centralizer {(x : G)} := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨g.2, mem_centralizer_singleton_iff.mpr ?_⟩
    have := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg)
    simpa using this
  · intro hg
    obtain ⟨hgH, hgC⟩ := Subgroup.mem_inf.mp hg
    refine ⟨⟨g, hgH⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
    simpa using mem_centralizer_singleton_iff.mp hgC

theorem a6sq_card_centralizer_mulEquiv {S T : Type*} [Group S] [Group T] (θ : S ≃* T) (z : S) :
    Nat.card (centralizer ({θ z} : Set T)) = Nat.card (centralizer ({z} : Set S)) := by
  have hmap : (centralizer ({z} : Set S)).map θ.toMonoidHom = centralizer ({θ z} : Set T) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x * z = z * x := mem_centralizer_singleton_iff.1 hx
      refine mem_centralizer_singleton_iff.2 ?_
      change θ x * θ z = θ z * θ x
      rw [← map_mul, ← map_mul, hx']
    · intro ht
      have ht' : t * θ z = θ z * t := mem_centralizer_singleton_iff.1 ht
      refine ⟨θ.symm t, mem_centralizer_singleton_iff.2 ?_, by simp⟩
      apply θ.injective
      simpa [map_mul] using ht'
  rw [← hmap]
  exact Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective

open Equiv Equiv.Perm in
theorem a6sq_cycleType_five (g : Perm (Fin 10)) (hg : orderOf g = 5) :
    g.cycleType = {5} ∨ g.cycleType = {5, 5} := by
  have hmem : ∀ b ∈ g.cycleType, b = 5 := by
    intro b hb
    have h1 : b ∣ 5 := hg ▸ Equiv.Perm.dvd_of_mem_cycleType hb
    have h2 : 2 ≤ b := Equiv.Perm.two_le_of_mem_cycleType hb
    have hp : Nat.Prime 5 := by norm_num
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · omega
    · exact h
  have hrep := Multiset.eq_replicate_of_mem hmem
  have hs := Equiv.Perm.sum_cycleType_le g
  generalize hm : Multiset.card g.cycleType = m at hrep
  rw [hrep, Multiset.sum_replicate, Fintype.card_fin] at hs
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : g = 1 := Equiv.Perm.cycleType_eq_zero.1 (by simpa using hrep)
    rw [this, orderOf_one] at hg
    exact absurd hg (by norm_num)
  have hm2 : m ≤ 2 := by simp at hs; omega
  rcases (by omega : m = 1 ∨ m = 2) with rfl | rfl
  · left; simpa using hrep
  · right; simpa [Multiset.replicate_succ] using hrep

open Equiv Equiv.Perm in
theorem card_alt_inf_centralizer_five_lt (g : Perm (Fin 10)) (hg : orderOf g = 5) :
    Nat.card ↥(alternatingGroup (Fin 10) ⊓ centralizer ({g} : Set (Perm (Fin 10)))) < 360 := by
  classical
  rcases a6sq_cycleType_five g hg with hc | hc
  ·
    have hS : Nat.card (centralizer ({g} : Set (Perm (Fin 10)))) = 600 := by
      rw [Equiv.Perm.nat_card_centralizer, hc, Fintype.card_fin]
      simp [Nat.factorial]
    have hsupp : g.support.card = 5 := by
      have := Equiv.Perm.sum_cycleType g
      rw [hc] at this
      simpa using this.symm
    have hfix : 2 ≤ (g.supportᶜ).card := by
      rw [Finset.card_compl, hsupp, Fintype.card_fin]
      omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by omega : 1 < (g.supportᶜ).card)
    have hug : g u = u := by simpa using hu
    have hvg : g v = v := by simpa using hv
    have hodd : Equiv.swap u v ∈ centralizer ({g} : Set (Perm (Fin 10))) := by
      rw [Subgroup.mem_centralizer_singleton_iff, Equiv.mul_swap_eq_swap_mul, hug, hvg]
    have hd : (alternatingGroup (Fin 10)).relIndex (centralizer ({g} : Set (Perm (Fin 10)))) =
        2 := by
      have hdvd : (alternatingGroup (Fin 10)).relIndex
          (centralizer ({g} : Set (Perm (Fin 10)))) ∣ 2 := by
        have h := Subgroup.relIndex_dvd_index_of_normal (alternatingGroup (Fin 10))
          (centralizer ({g} : Set (Perm (Fin 10))))
        rwa [alternatingGroup.index_eq_two] at h
      have hne : (alternatingGroup (Fin 10)).relIndex
          (centralizer ({g} : Set (Perm (Fin 10)))) ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        intro hle
        have := hle hodd
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap huv] at this
        exact absurd this (by decide)
      exact ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left hne
    have hrel := Subgroup.relIndex_mul_card (H := alternatingGroup (Fin 10))
      (K := centralizer ({g} : Set (Perm (Fin 10))))
    rw [hd, hS] at hrel
    omega
  · have hS : Nat.card (centralizer ({g} : Set (Perm (Fin 10)))) = 50 := by
      rw [Equiv.Perm.nat_card_centralizer, hc, Fintype.card_fin]
      simp [Nat.factorial]
    have hle : Nat.card ↥(alternatingGroup (Fin 10) ⊓ centralizer ({g} : Set (Perm (Fin 10)))) ≤
        Nat.card (centralizer ({g} : Set (Perm (Fin 10)))) :=
      Subgroup.card_le_of_le inf_le_right
    omega

theorem card_centralizer_alt_five_lt (x : alternatingGroup (Fin 10)) (hx : orderOf x = 5) :
    Nat.card (centralizer ({x} : Set (alternatingGroup (Fin 10)))) < 360 := by
  have hg : orderOf (x : Equiv.Perm (Fin 10)) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have hmap : Nat.card ((centralizer ({x} : Set (alternatingGroup (Fin 10)))).map
      (alternatingGroup (Fin 10)).subtype) =
        Nat.card (centralizer ({x} : Set (alternatingGroup (Fin 10)))) :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin 10)).subtype_injective
  rw [a6sq_map_centralizer_subtype] at hmap
  rw [← hmap]
  exact card_alt_inf_centralizer_five_lt _ hg

end Five

theorem a6sq_alt_false {S : Type} [Group S] [Finite S] {n : ℕ}
    (θ : S ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (hev : Even n) {τ : MulAut S}
    (hτ : orderOf τ = 2) (hC : Nat.card (fixedSubgroup τ) ≤ 5760)
    (h360 : 360 ∣ Nat.card (fixedSubgroup τ)) (hS : 129600 ∣ Nat.card S) {A : Subgroup S}
    (hA6 : Nonempty (↥A ⧸ center ↥A ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * τ b = τ b * a) : False := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨r, hr1, hr2, hr⟩ := card_fixedSubgroup_alt (by omega) θ hτ
  have hSn : Nat.card S = n.factorial / 2 := by
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  rw [hr] at hC h360
  rw [hSn] at hS
  have hn10 : n = 10 := a6sq_alt_numeric hn hev hr1 hr2 hC h360 hS
  subst hn10
  have hAcard : Nat.card A = 360 * Nat.card (center ↥A) := a6sq_card_A hA6
  have h5 : 5 ∣ Nat.card A := ⟨72 * Nat.card (center ↥A), by rw [hAcard]; ring⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hxS : orderOf (x : S) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have hb : orderOf (τ (x : S)) = 5 :=
    (orderOf_injective τ.toMonoidHom τ.injective (x : S)).trans hxS
  have hAle : A ≤ centralizer ({τ (x : S)} : Set S) := by
    intro a ha
    rw [mem_centralizer_singleton_iff]
    exact hcomm a ha x x.2
  have hcardle : Nat.card A ≤ Nat.card (centralizer ({τ (x : S)} : Set S)) :=
    Subgroup.card_le_of_le hAle
  have hθb : orderOf (θ (τ (x : S))) = 5 :=
    (orderOf_injective θ.toMonoidHom θ.injective _).trans hb
  have hlt := card_centralizer_alt_five_lt _ hθb
  rw [a6sq_card_centralizer_mulEquiv θ] at hlt
  have hpos : 0 < Nat.card (center ↥A) := Nat.card_pos
  omega

end CFSG.ComponentClassification.CatFC
