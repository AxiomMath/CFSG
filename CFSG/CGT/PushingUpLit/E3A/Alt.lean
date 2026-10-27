module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit.E3A

open CFSG CFSG.RankThree.PartOne Equiv
open scoped Nat

theorem five_dvd_card_block {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNaturalAltModule X n) : 5 ∣ Nat.card X := by
  obtain ⟨f, -⟩ := hnat
  have h2 : 2 ∣ (2 * n + 1)! := Nat.dvd_factorial (by norm_num) (by omega)
  have h5 : 5 ∣ (2 * n + 1)! := Nat.dvd_factorial (by norm_num) (by omega)
  have hnt : Nontrivial (Fin (2 * n + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h1 : 5 ∣ Nat.card (alternatingGroup (Fin (2 * n + 1))) := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    have h3 : 2 * ((2 * n + 1)! / 2) = (2 * n + 1)! := Nat.mul_div_cancel' h2
    rw [← h3] at h5
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 5 2) h5)
  have h4 : Nat.card (X ⧸ pCore 2 X) = Nat.card (alternatingGroup (Fin (2 * n + 1))) :=
    Nat.card_congr f.toEquiv
  rw [← h4] at h1
  have h6 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 X)
  rw [h6]
  exact h1.mul_right _

theorem cycleType_eq_of_orderOf_five {k : ℕ} (hk : k ≤ 9) {σ : Perm (Fin k)}
    (h : orderOf σ = 5) : σ.cycleType = {5} := by
  have hl := Perm.lcm_cycleType σ
  have hmem : ∀ a ∈ σ.cycleType, a = 5 := by
    intro a ha
    have hd : a ∣ 5 := by
      rw [← h, ← hl]
      exact Multiset.dvd_lcm ha
    have h2 := Perm.two_le_of_mem_cycleType ha
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hd with h1 | h1
    · omega
    · exact h1
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 5 :=
    Multiset.eq_replicate_card.2 hmem
  have hsum : σ.cycleType.sum ≤ k := by
    have := Perm.sum_cycleType_le σ
    simpa using this
  have hne : σ.cycleType ≠ 0 := by
    intro h0
    have : σ = 1 := Perm.cycleType_eq_zero.1 h0
    rw [this, orderOf_one] at h
    omega
  have hcard_pos : 0 < Multiset.card σ.cycleType := by
    rcases Nat.eq_zero_or_pos (Multiset.card σ.cycleType) with h0 | h0
    · exact absurd (Multiset.card_eq_zero.1 h0) hne
    · exact h0
  have hcard : Multiset.card σ.cycleType = 1 := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    omega
  rw [hrep, hcard]
  rfl

theorem card_centralizer_of_orderOf_five {k : ℕ} (hk : k ≤ 9) {σ : Perm (Fin k)}
    (h : orderOf σ = 5) : Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin k)))) =
      (k - 5)! * 5 := by
  rw [Perm.nat_card_centralizer, cycleType_eq_of_orderOf_five hk h]
  simp

theorem not_card_eq_eight {Q : Subgroup (Perm (Fin 9))} {σ : Perm (Fin 9)} (h : orderOf σ = 5)
    (hQC : Q ≤ Subgroup.centralizer ({σ} : Set (Perm (Fin 9))))
    (hQA : Q ≤ alternatingGroup (Fin 9)) : Nat.card Q ≠ 8 := by
  classical
  intro hQ
  set C : Subgroup (Perm (Fin 9)) := Subgroup.centralizer ({σ} : Set (Perm (Fin 9))) with hC
  have hCcard : Nat.card C = 120 :=
    (card_centralizer_of_orderOf_five (by norm_num) h).trans (by norm_num [Nat.factorial])
  have hsupp : σ.support.card = 5 := by
    rw [← Perm.sum_cycleType, cycleType_eq_of_orderOf_five (by norm_num) h]
    rfl
  have hcompl : 1 < (σ.supportᶜ).card := by
    rw [Finset.card_compl, hsupp]
    simp
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcompl
  have hσa : σ a = a := by
    have := Finset.mem_compl.1 ha
    simpa using this
  have hσb : σ b = b := by
    have := Finset.mem_compl.1 hb
    simpa using this
  have htC : swap a b ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg, mul_swap_eq_swap_mul, hσa, hσb]
  let s : ↥C →* ℤˣ := Perm.sign.comp C.subtype
  have hsurj : Function.Surjective s := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one s⟩
    · exact ⟨⟨swap a b, htC⟩, by
        show Perm.sign (swap a b) = -1
        exact Perm.sign_swap hab⟩
  have hidx : s.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
    simp
  have hker : Nat.card s.ker = 60 := by
    have := Subgroup.card_mul_index s.ker
    rw [hidx, Nat.card_eq_fintype_card (α := ↥C)] at this
    rw [← Nat.card_eq_fintype_card, hCcard] at this
    omega
  have hle : Q.subgroupOf C ≤ s.ker := by
    intro x hx
    have hxA : (x : Perm (Fin 9)) ∈ alternatingGroup (Fin 9) := hQA (Subgroup.mem_subgroupOf.1 hx)
    show Perm.sign (x : Perm (Fin 9)) = 1
    exact Perm.mem_alternatingGroup.1 hxA
  have hdvd : Nat.card (Q.subgroupOf C) ∣ Nat.card s.ker := Subgroup.card_dvd_of_le hle
  have hcardQ : Nat.card (Q.subgroupOf C) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
  rw [hcardQ, hQ, hker] at hdvd
  omega

theorem false_of_alt {G : Type} [Group G] [Finite G] {X R : Subgroup G} {n k : ℕ} (hn : 2 ≤ n)
    (hk6 : 6 ≤ k) (hk9 : k ≤ 9) (e : G ≃* alternatingGroup (Fin k))
    (hR : Nat.card R = if k ≤ 7 then 4 else 8) (hnat : IsNaturalAltModule ↥X n)
    (hXC : X ≤ Subgroup.centralizer (R : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : 5 ∣ Nat.card ↥X := five_dvd_card_block hn hnat
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5 h5
  let ι : G →* Perm (Fin k) := (alternatingGroup (Fin k)).subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  set σ : Perm (Fin k) := ι (y : G) with hσdef
  have hσ : orderOf σ = 5 := by
    rw [hσdef, orderOf_injective ι hι, Subgroup.orderOf_coe, hy]
  have hQC : R.map ι ≤ Subgroup.centralizer ({σ} : Set (Perm (Fin k))) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg, hσdef, ← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_centralizer_iff.1 (hXC y.2) r hr).symm
  have hcard : Nat.card (R.map ι) = Nat.card R := Subgroup.card_map_of_injective hι
  have hdvd : Nat.card (R.map ι) ∣ (k - 5)! * 5 := by
    rw [← card_centralizer_of_orderOf_five hk9 hσ]
    exact Subgroup.card_dvd_of_le hQC
  rw [hcard] at hdvd
  by_cases hk7 : k ≤ 7
  · have hR4 : Nat.card R = 4 := by simpa [hk7] using hR
    rw [hR4] at hdvd
    interval_cases k <;> simp at hdvd
  · have hR8 : Nat.card R = 8 := by simpa [hk7] using hR
    rw [hR8] at hdvd
    by_cases hk8 : k = 8
    · subst hk8
      norm_num [Nat.factorial] at hdvd
    · have hk9' : k = 9 := by omega
      subst hk9'
      have hQA : R.map ι ≤ alternatingGroup (Fin 9) := by
        rintro _ ⟨r, -, rfl⟩
        exact (e r).2
      exact not_card_eq_eight hσ hQC hQA (by rw [hcard, hR8])

end CFSG.CGT.PushingUpLit.E3A
