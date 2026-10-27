module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltFixedCard
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
  (cycleType_eq_replicate_two nat_card_centralizer_perm_two exists_odd_mem_centralizer_perm)

theorem card_centralizer_singleton_mulEquiv_alt {S T : Type*} [Group S] [Group T]
    (θ : S ≃* T) (z : S) :
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

theorem natCard_multiplicative_zmod_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem map_centralizer_subtype_eq_inf {G : Type*} [Group G] (H : Subgroup G) (x : H) :
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

theorem even_of_cycleType_replicate {n m : ℕ} (π : Equiv.Perm (Fin n))
    (hc : π.cycleType = Multiset.replicate m 2) (hs : Equiv.Perm.sign π = 1) : m % 2 = 0 := by
  have h := Equiv.Perm.sign_of_cycleType π
  rw [hc, Multiset.sum_replicate, Multiset.card_replicate, hs, smul_eq_mul] at h
  obtain ⟨k, hk⟩ := (neg_one_pow_eq_one_iff_even (by decide)).1 h.symm
  omega

theorem two_mul_card_centralizer_alt {n : ℕ} (hn : 2 ≤ n) (g : alternatingGroup (Fin n))
    {m : ℕ} (hg2 : (g : Equiv.Perm (Fin n)) * g = 1) (hg1 : (g : Equiv.Perm (Fin n)) ≠ 1)
    (hm : 1 ≤ m) (hc : (g : Equiv.Perm (Fin n)).cycleType = Multiset.replicate m 2) :
    2 * Nat.card (centralizer ({g} : Set (alternatingGroup (Fin n)))) =
      (n - 2 * m).factorial * (2 ^ m * m.factorial) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hS := nat_card_centralizer_perm_two (g : Equiv.Perm (Fin n)) hm hc
  have hmap : Nat.card ((centralizer ({g} : Set (alternatingGroup (Fin n)))).map
      (alternatingGroup (Fin n)).subtype) =
        Nat.card (centralizer ({g} : Set (alternatingGroup (Fin n)))) :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective
  rw [map_centralizer_subtype_eq_inf] at hmap
  have hd : (alternatingGroup (Fin n)).relIndex
      (centralizer ({(g : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))) = 2 := by
    have hdvd : (alternatingGroup (Fin n)).relIndex
        (centralizer ({(g : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))) ∣ 2 := by
      have h := Subgroup.relIndex_dvd_index_of_normal (alternatingGroup (Fin n))
        (centralizer ({(g : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n))))
      rwa [alternatingGroup.index_eq_two] at h
    have hne : (alternatingGroup (Fin n)).relIndex
        (centralizer ({(g : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro hle
      obtain ⟨t, ht, hs⟩ := exists_odd_mem_centralizer_perm (g : Equiv.Perm (Fin n)) hg2 hg1
      have htA : t ∈ alternatingGroup (Fin n) := hle ht
      rw [Equiv.Perm.mem_alternatingGroup, hs] at htA
      exact absurd htA (by decide)
    exact ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left hne
  have hrel := Subgroup.relIndex_mul_card (H := alternatingGroup (Fin n))
    (K := centralizer ({(g : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n))))
  rw [hd, hmap] at hrel
  rw [hrel, hS, mul_assoc]

theorem inner_numeric_false : ∀ m < 6, ∀ j < 8, 1 ≤ m → m % 2 = 0 →
    j.factorial * (2 ^ m * m.factorial) ≠ 1440 ∧ j.factorial * (2 ^ m * m.factorial) ≠ 10080 := by
  decide

theorem inner_numeric {n m : ℕ} (hm : 1 ≤ m) (hm2 : m % 2 = 0)
    (h : (n - 2 * m).factorial * (2 ^ m * m.factorial) = 1440 ∨
      (n - 2 * m).factorial * (2 ^ m * m.factorial) = 10080) : False := by
  have hQ : 0 < 2 ^ m * m.factorial := by positivity
  have hm6 : m < 6 := by
    by_contra hc
    have h1 : (6 : ℕ).factorial ≤ m.factorial := Nat.factorial_le (by omega)
    have h2 : 2 ^ 6 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 6 * (6 : ℕ).factorial ≤ 2 ^ m * m.factorial := Nat.mul_le_mul h2 h1
    have h4 : 2 ^ m * m.factorial ≤ (n - 2 * m).factorial * (2 ^ m * m.factorial) :=
      Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    norm_num [Nat.factorial] at h3
    rcases h with h | h <;> omega
  have hj8 : n - 2 * m < 8 := by
    by_contra hc
    have h1 : (8 : ℕ).factorial ≤ (n - 2 * m).factorial := Nat.factorial_le (by omega)
    have h2 : (8 : ℕ).factorial * 1 ≤ (n - 2 * m).factorial * (2 ^ m * m.factorial) :=
      Nat.mul_le_mul h1 hQ
    norm_num [Nat.factorial] at h2
    rcases h with h | h <;> omega
  obtain ⟨j, hj⟩ : ∃ j, n - 2 * m = j := ⟨_, rfl⟩
  rw [hj] at h hj8
  rcases h with h | h
  · exact (inner_numeric_false m hm6 j hj8 hm hm2).1 h
  · exact (inner_numeric_false m hm6 j hj8 hm hm2).2 h

theorem outer_numeric_false : ∀ r < 6, ∀ j < 7, 1 ≤ r →
    2 ^ (r - 1) * r.factorial * j.factorial ≠ 360 ∧
      2 ^ (r - 1) * r.factorial * j.factorial ≠ 2520 := by
  decide

theorem outer_numeric {n r : ℕ} (hr : 1 ≤ r)
    (h : 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial = 360 ∨
      2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial = 2520) : False := by
  have hQ : 0 < 2 ^ (r - 1) * r.factorial := by positivity
  have hr6 : r < 6 := by
    by_contra hc
    have h1 : (6 : ℕ).factorial ≤ r.factorial := Nat.factorial_le (by omega)
    have h2 : 2 ^ 5 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 5 * (6 : ℕ).factorial ≤ 2 ^ (r - 1) * r.factorial := Nat.mul_le_mul h2 h1
    have h4 : 2 ^ (r - 1) * r.factorial ≤ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial :=
      Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
    norm_num [Nat.factorial] at h3
    rcases h with h | h <;> omega
  have hj7 : n - 2 * r < 7 := by
    by_contra hc
    have h1 : (7 : ℕ).factorial ≤ (n - 2 * r).factorial := Nat.factorial_le (by omega)
    have h2 : (n - 2 * r).factorial ≤ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial :=
      Nat.le_mul_of_pos_left _ hQ
    norm_num [Nat.factorial] at h1
    rcases h with h | h <;> omega
  obtain ⟨j, hj⟩ : ∃ j, n - 2 * r = j := ⟨_, rfl⟩
  rw [hj] at h hj7
  rcases h with h | h
  · exact (outer_numeric_false r hr6 j hj7 hr).1 h
  · exact (outer_numeric_false r hr6 j hj7 hr).2 h

theorem alt_not_centralizer_Z2_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (θ : S ≃* alternatingGroup (Fin n)) {k : ℕ} (hk : k = 6 ∨ k = 7) (z : S)
    (hz : orderOf z = 2) :
    ¬ Nonempty (↥(centralizer ({z} : Set S)) ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin k)) := by
  rintro ⟨e⟩
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hC : Nat.card (centralizer ({z} : Set S)) = 2 * (k.factorial / 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, nat_card_alternatingGroup, Nat.card_fin,
      natCard_multiplicative_zmod_two]
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz, sq] at h
    exact h
  have hgg : θ z * θ z = 1 := by rw [← map_mul, hzz, map_one]
  have hg2 : (θ z : Equiv.Perm (Fin n)) * (θ z : Equiv.Perm (Fin n)) = 1 := by
    have h := congrArg Subtype.val hgg
    simpa using h
  have hg1 : (θ z : Equiv.Perm (Fin n)) ≠ 1 := by
    intro h
    have hz1 : z = 1 := θ.injective (by rw [map_one]; exact Subtype.ext (by simpa using h))
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨m, hm1, -, hc⟩ := cycleType_eq_replicate_two (θ z : Equiv.Perm (Fin n)) hg2 hg1
  have hmeven : m % 2 = 0 :=
    even_of_cycleType_replicate _ hc (Equiv.Perm.mem_alternatingGroup.1 (θ z).2)
  have hF := two_mul_card_centralizer_alt (by omega) (θ z) hg2 hg1 hm1 hc
  have hT := card_centralizer_singleton_mulEquiv_alt θ z
  have hFF : (n - 2 * m).factorial * (2 ^ m * m.factorial) = 4 * (k.factorial / 2) := by
    rw [← hF, hT, hC]
    ring
  rcases hk with rfl | rfl
  · exact inner_numeric hm1 hmeven (Or.inl (by rw [hFF]; decide))
  · exact inner_numeric hm1 hmeven (Or.inr (by rw [hFF]; decide))

theorem alt_not_fixedSubgroup_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (θ : S ≃* alternatingGroup (Fin n)) {k : ℕ} (hk : k = 6 ∨ k = 7) {σ : MulAut S}
    (hσ : orderOf σ = 2) : ¬ Nonempty (↥(fixedSubgroup σ) ≃* alternatingGroup (Fin k)) := by
  rintro ⟨e⟩
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hFix : Nat.card (fixedSubgroup σ) = k.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have hS : Nat.card S = n.factorial / 2 := by
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  by_cases h7 : 7 ≤ n
  · obtain ⟨r, hr1, -, hr⟩ := card_fixedSubgroup_alt h7 θ hσ
    rw [hFix] at hr
    rcases hk with rfl | rfl
    · exact outer_numeric hr1 (Or.inl (hr.symm.trans (by decide)))
    · exact outer_numeric hr1 (Or.inr (hr.symm.trans (by decide)))
  · have hle : Nat.card (fixedSubgroup σ) ≤ Nat.card S :=
      Subgroup.card_le_card_group (fixedSubgroup σ)
    rw [hFix, hS] at hle
    have hn' : n = 5 ∨ n = 6 := by omega
    rcases hk with rfl | rfl <;> rcases hn' with rfl | rfl
    · exact absurd hle (by decide)
    ·
      have htop : fixedSubgroup σ = ⊤ :=
        (Subgroup.card_eq_iff_eq_top (fixedSubgroup σ)).1 (hFix.trans hS.symm)
      have hσ1 : σ = 1 := by
        refine MulEquiv.ext fun x => ?_
        have hx : x ∈ fixedSubgroup σ := by
          rw [htop]
          exact Subgroup.mem_top x
        have hx' : σ x = x := hx
        simpa using hx'
      rw [hσ1, orderOf_one] at hσ
      exact absurd hσ (by decide)
    · exact absurd hle (by decide)
    · exact absurd hle (by decide)

end CFSG.ComponentClassification.CatFC
