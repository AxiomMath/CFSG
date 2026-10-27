module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

open Equiv Equiv.Perm in
theorem exists_sq_of_involution_perm_six (a : Equiv.Perm (Fin 6)) (ha : a * a = 1)
    (hs : Equiv.Perm.sign a = 1) : ∃ c : Equiv.Perm (Fin 6), Equiv.Perm.sign c = 1 ∧ c * c = a := by
  by_cases h1 : a = 1
  · exact ⟨1, by simp, by simp [h1]⟩
  have hord : orderOf a = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact ha) h1
  have hmem : ∀ n ∈ a.cycleType, n = 2 := by
    intro n hn
    have h2 : n ∣ 2 := hord ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have h3 := Equiv.Perm.two_le_of_mem_cycleType hn
    exact (Nat.dvd_prime Nat.prime_two).1 h2 |>.resolve_left (by omega)
  obtain ⟨k, hk⟩ : ∃ k, a.cycleType = Multiset.replicate k 2 :=
    ⟨Multiset.card a.cycleType, Multiset.eq_replicate.2 ⟨rfl, hmem⟩⟩
  have hsum : a.cycleType.sum = a.support.card := Equiv.Perm.sum_cycleType a
  have hle : a.support.card ≤ 6 := by
    simpa using Finset.card_le_univ a.support
  have hsign := Equiv.Perm.sign_of_cycleType a
  rw [hk] at hsum hsign
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsum hsign
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h1 (Equiv.Perm.cycleType_eq_zero.1 (by simpa using hk))
  have hkeven : Even k := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have : Odd (k * 2 + k) := by
      obtain ⟨r, hr⟩ := hodd
      exact ⟨3 * r + 1, by omega⟩
    rw [hs, this.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  have hk2 : k = 2 := by
    obtain ⟨r, hr⟩ := hkeven
    omega
  subst hk2
  set a₀ : Perm (Fin 6) := swap (0 : Fin 6) 1 * swap 2 3 with ha₀
  have hct0 : a₀.cycleType = {2, 2} :=
    cycleType_swap_mul_swap_of_nodup (x := (0 : Fin 6)) (y := 1) (z := 2) (t := 3) (by decide)
  have hconj : IsConj a a₀ := Equiv.Perm.isConj_iff_cycleType_eq.2 (by rw [hk, hct0]; rfl)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  set g₀ : Perm (Fin 6) := swap (0 : Fin 6) 2 * swap 2 1 * swap 1 3 * swap 4 5 with hg₀
  have hg₀sq : g₀ * g₀ = a₀ := by decide
  have hg₀sign : sign g₀ = 1 := by simp [hg₀, Equiv.Perm.sign_mul]
  refine ⟨c⁻¹ * g₀ * c, ?_, ?_⟩
  · simp [Equiv.Perm.sign_mul, hg₀sign]
  · calc c⁻¹ * g₀ * c * (c⁻¹ * g₀ * c) = c⁻¹ * (g₀ * g₀) * c := by group
      _ = c⁻¹ * a₀ * c := by rw [hg₀sq]
      _ = a := by rw [← hc]; group

theorem a6_involution_sq :
    ∀ a : alternatingGroup (Fin 6), a * a = 1 → ∃ c : alternatingGroup (Fin 6), c * c = a := by
  intro a ha
  have ha' : (a : Equiv.Perm (Fin 6)) * a = 1 := congrArg Subtype.val ha
  obtain ⟨c, hc, hcc⟩ :=
    exists_sq_of_involution_perm_six a ha' (Equiv.Perm.mem_alternatingGroup.1 a.2)
  exact ⟨⟨c, Equiv.Perm.mem_alternatingGroup.2 hc⟩, Subtype.ext hcc⟩

theorem exists_sq_of_quotient_sq {K : Type*} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (hN : Odd (Nat.card N)) {u : K} (hu : u * u = 1) (hu1 : u ≠ 1) {cb : K ⧸ N}
    (hcb : cb * cb = QuotientGroup.mk' N u) : ∃ g : K, g * g = u := by
  have hinv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution u :=
    ⟨hu1, by rw [pow_two]; exact hu⟩
  have hcent : cb ∈ centralizer ({QuotientGroup.mk' N u} : Set (K ⧸ N)) := by
    rw [mem_centralizer_singleton_iff, ← hcb]
    group
  obtain ⟨c, hcu, hcmk⟩ :=
    CFSG.GorensteinWalter.exists_centralizer_lift_of_odd_kernel N hN hinv cb hcent
  have hcu' : c * u = u * c := mem_centralizer_singleton_iff.1 hcu
  have hmk : ∀ k : ℕ, QuotientGroup.mk' N (c ^ k) = cb ^ k := fun k => by rw [map_pow, hcmk]
  have hcb4 : cb ^ 4 = 1 := by
    have : cb ^ 4 = (cb * cb) * (cb * cb) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [this, hcb, ← map_mul, hu, map_one]
  have hc4 : c ^ 4 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, hmk]
    exact hcb4
  have hq : Odd (orderOf (c ^ 4)) :=
    Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hc4)
  obtain ⟨r, hr⟩ := hq
  set q := orderOf (c ^ 4) with hqdef
  have hq4 : (c ^ 4) ^ q = 1 := pow_orderOf_eq_one _
  have hg4 : (c ^ (q * q)) ^ 4 = 1 := by
    have : (c ^ (q * q)) ^ 4 = ((c ^ 4) ^ q) ^ q := by
      rw [← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [this, hq4, one_pow]
  have hgcb : QuotientGroup.mk' N (c ^ (q * q)) = cb := by
    rw [hmk]
    have : q * q = 4 * (r * r + r) + 1 := by rw [hr]; ring
    rw [this, pow_succ, pow_mul, hcb4, one_pow, one_mul]
  set g := c ^ (q * q) with hgdef
  have hgu : g * u = u * g := (Commute.pow_left (show Commute c u from hcu') _).eq
  have hgg : QuotientGroup.mk' N (g * g) = QuotientGroup.mk' N u := by
    rw [map_mul, hgcb, hcb]
  have hoN : u⁻¹ * (g * g) ∈ N := by
    have := (QuotientGroup.eq (a := u) (b := g * g)).1 hgg.symm
    simpa using this
  have hcomm : Commute u⁻¹ (g * g) :=
    (show Commute g u from hgu).symm.inv_left.mul_right (show Commute g u from hgu).symm.inv_left
  have hu4 : u ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hu, one_mul]
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have ho4 : (u⁻¹ * (g * g)) ^ 4 = 1 := by
    rw [hcomm.mul_pow, hui, hu4, one_mul, ← sq, ← pow_mul, show 2 * 4 = 4 * 2 from rfl, pow_mul,
      hg4, one_pow]
  have hdvd4 : orderOf (u⁻¹ * (g * g)) ∣ 4 := orderOf_dvd_of_pow_eq_one ho4
  have hdvdN : orderOf (u⁻¹ * (g * g)) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hoN
  have hodd : Odd (orderOf (u⁻¹ * (g * g))) := Odd.of_dvd_nat hN hdvdN
  have hone : orderOf (u⁻¹ * (g * g)) = 1 := by
    have hle : orderOf (u⁻¹ * (g * g)) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
    generalize orderOf (u⁻¹ * (g * g)) = d at hdvd4 hodd hle ⊢
    interval_cases d
    · exact absurd hodd (by decide)
    · rfl
    · exact absurd hodd (by decide)
    · exact absurd hdvd4 (by decide)
    · exact absurd hodd (by decide)
  refine ⟨g, ?_⟩
  have h1 : u⁻¹ * (g * g) = 1 := orderOf_eq_one_iff.1 hone
  calc g * g = u * (u⁻¹ * (g * g)) := by group
    _ = u := by rw [h1, mul_one]

theorem exists_sq_of_involution_mem_sup {K : Type*} [Group K] [Finite K]
    {N₁ N₂ : Subgroup (K ⧸ fusionOddCore K)} (e₁ : N₁ ≃* alternatingGroup (Fin 6))
    (e₂ : N₂ ≃* alternatingGroup (Fin 6)) (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hd : Disjoint N₁ N₂) {u : K} (hu : u * u = 1)
    (hmem : (QuotientGroup.mk u : K ⧸ fusionOddCore K) ∈ N₁ ⊔ N₂) : ∃ g : K, g * g = u := by
  by_cases hu1 : u = 1
  · exact ⟨1, by rw [hu1, one_mul]⟩
  have hBA : N₂ ≤ centralizer (N₁ : Set (K ⧸ fusionOddCore K)) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hc a ha b hb
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hBA hmem
  have hsq : (a * b) * (a * b) = 1 := by
    rw [← hab, ← QuotientGroup.mk_mul, hu, QuotientGroup.mk_one]
  have hab2 : a * a * (b * b) = 1 := by
    have : (a * b) * (a * b) = a * a * (b * b) := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hc a ha b hb]
        _ = a * a * (b * b) := by group
    rw [← this]
    exact hsq
  have haa : a * a = 1 := by
    have h1 : a * a ∈ N₁ := mul_mem ha ha
    have h2 : a * a ∈ N₂ := by
      have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hab2
      rw [this]
      exact inv_mem (mul_mem hb hb)
    exact Subgroup.disjoint_def.1 hd h1 h2
  have hbb : b * b = 1 := by
    rw [haa, one_mul] at hab2
    exact hab2
  obtain ⟨c₁, hc₁⟩ := a6_involution_sq (e₁ ⟨a, ha⟩) (by
    rw [← map_mul]
    have : (⟨a, ha⟩ : N₁) * ⟨a, ha⟩ = 1 := Subtype.ext haa
    rw [this, map_one])
  obtain ⟨c₂, hc₂⟩ := a6_involution_sq (e₂ ⟨b, hb⟩) (by
    rw [← map_mul]
    have : (⟨b, hb⟩ : N₂) * ⟨b, hb⟩ = 1 := Subtype.ext hbb
    rw [this, map_one])
  have hc₁' : ((e₁.symm c₁ : N₁) : K ⧸ fusionOddCore K) * (e₁.symm c₁ : N₁) = a := by
    have := congrArg (fun y => ((e₁.symm y : N₁) : K ⧸ fusionOddCore K)) hc₁
    simpa [map_mul] using this
  have hc₂' : ((e₂.symm c₂ : N₂) : K ⧸ fusionOddCore K) * (e₂.symm c₂ : N₂) = b := by
    have := congrArg (fun y => ((e₂.symm y : N₂) : K ⧸ fusionOddCore K)) hc₂
    simpa [map_mul] using this
  refine exists_sq_of_quotient_sq (fusionOddCore K) (odd_natCard_fusionOddCore K) hu hu1
    (cb := ((e₁.symm c₁ : N₁) : K ⧸ fusionOddCore K) * (e₂.symm c₂ : N₂)) ?_
  have hcomm := hc _ (e₁.symm c₁).2 _ (e₂.symm c₂).2
  calc ((e₁.symm c₁ : N₁) : K ⧸ fusionOddCore K) * (e₂.symm c₂ : N₂) *
        (((e₁.symm c₁ : N₁) : K ⧸ fusionOddCore K) * (e₂.symm c₂ : N₂))
      = ((e₁.symm c₁ : N₁) : K ⧸ fusionOddCore K) *
          (((e₂.symm c₂ : N₂) : K ⧸ fusionOddCore K) * (e₁.symm c₁ : N₁)) *
          (e₂.symm c₂ : N₂) := by group
    _ = ((e₁.symm c₁ : N₁) : K ⧸ fusionOddCore K) *
          (((e₁.symm c₁ : N₁) : K ⧸ fusionOddCore K) * (e₂.symm c₂ : N₂)) *
          (e₂.symm c₂ : N₂) := by rw [← hcomm]
    _ = a * b := by rw [← hc₁', ← hc₂']; group
    _ = QuotientGroup.mk' (fusionOddCore K) u := by rw [← hab]; rfl

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}

theorem InnerConfig.conj_z_not_mem_sup (h : InnerConfig G A z t T₀) {K : Subgroup G}
    {N₁ N₂ : Subgroup (↥K ⧸ fusionOddCore ↥K)} (e₁ : N₁ ≃* alternatingGroup (Fin 6))
    (e₂ : N₂ ≃* alternatingGroup (Fin 6)) (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hd : Disjoint N₁ N₂) (g : G) (hgK : g * z * g⁻¹ ∈ K) :
    (QuotientGroup.mk (⟨g * z * g⁻¹, hgK⟩ : ↥K) : ↥K ⧸ fusionOddCore ↥K) ∉ N₁ ⊔ N₂ := by
  intro hmem
  have hu : (⟨g * z * g⁻¹, hgK⟩ : ↥K) * ⟨g * z * g⁻¹, hgK⟩ = 1 := by
    apply Subtype.ext
    show g * z * g⁻¹ * (g * z * g⁻¹) = 1
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  obtain ⟨s, hs⟩ := exists_sq_of_involution_mem_sup e₁ e₂ hc hd hu hmem
  refine h.z_not_square ⟨g⁻¹ * (s : G) * g, ?_⟩
  have hs' : (s : G) * s = g * z * g⁻¹ := congrArg Subtype.val hs
  calc g⁻¹ * (s : G) * g * (g⁻¹ * (s : G) * g) = g⁻¹ * ((s : G) * s) * g := by group
    _ = z := by rw [hs']; group

end CFSG.EvenSporadicStandard.Fin76b
