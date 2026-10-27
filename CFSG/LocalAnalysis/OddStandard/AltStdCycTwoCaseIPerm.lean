module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoCaseI
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalInvolutionOddCore

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two

open Subgroup Equiv Equiv.Perm AltStdSec

variable {n : ℕ}

private theorem ne_of_fix_of_moved {σ : Perm (Fin n)} (hσσ : ∀ i, σ (σ i) = i) {k m : Fin n}
    (hk : σ k = k) (hm : σ m ≠ m) : k ≠ m ∧ k ≠ σ m := by
  refine ⟨fun h => hm (by rw [← h]; exact hk), fun h => hm ?_⟩
  have h1 := hk
  rw [h, hσσ] at h1
  exact h1.symm

private theorem uniform_of_comm_fix {σ s : Perm (Fin n)} (hσ2 : σ * σ = 1) (hsσ : s * σ = σ * s)
    (hcommF : ∀ π₀ : Perm (Fin n), π₀ * σ = σ * π₀ → (∀ k, σ k = k → π₀ k = k) →
      π₀ * s = s * π₀) :
    (∀ i, σ i ≠ i → s i = i) ∨ (∀ i, σ i ≠ i → s i = σ i) := by
  classical
  have hσσ : ∀ i, σ (σ i) = i := fun i => by rw [← Perm.mul_apply, hσ2, Perm.one_apply]
  have hes : ∀ i, σ (s i) = s (σ i) := fun i => by rw [← Perm.mul_apply, ← hsσ, Perm.mul_apply]
  have hswapP : ∀ i, swap i (σ i) * σ = σ * swap i (σ i) := fun i => by
    rw [mul_swap_eq_swap_mul, hσσ i, swap_comm]
  have hpair : ∀ i, σ i ≠ i → s i = i ∨ s i = σ i := fun i hi =>
    apply_mem_of_comm_swap (Ne.symm hi) (hcommF _ (hswapP i) fun k hk => by
      obtain ⟨h1, h2⟩ := ne_of_fix_of_moved hσσ hk hi
      exact swap_apply_of_ne_of_ne h1 h2)
  by_cases hex : ∃ i₀, σ i₀ ≠ i₀
  · obtain ⟨i₀, hi₀⟩ := hex
    have key : ∀ j, σ j ≠ j → j ≠ i₀ → j ≠ σ i₀ → ∃ π : Perm (Fin n), π * σ = σ * π ∧
        (∀ k, σ k = k → π k = k) ∧ π i₀ = j ∧ π (σ i₀) = σ j := by
      intro j hj hji hje
      have hej : σ j ≠ i₀ := fun h' => hje (by rw [← h', hσσ])
      refine ⟨swap i₀ j * swap (σ i₀) (σ j), ?_, ?_, ?_, ?_⟩
      · have h1 : σ * swap i₀ j = swap (σ i₀) (σ j) * σ := mul_swap_eq_swap_mul σ i₀ j
        have h2 : σ * swap (σ i₀) (σ j) = swap i₀ j * σ := by
          rw [mul_swap_eq_swap_mul, hσσ, hσσ]
        have hcomm : swap i₀ j * swap (σ i₀) (σ j) = swap (σ i₀) (σ j) * swap i₀ j :=
          swap_mul_swap_comm hi₀.symm hej.symm hje hj.symm
        calc swap i₀ j * swap (σ i₀) (σ j) * σ = swap (σ i₀) (σ j) * swap i₀ j * σ := by
              rw [hcomm]
          _ = swap (σ i₀) (σ j) * (σ * swap (σ i₀) (σ j)) := by rw [mul_assoc, ← h2]
          _ = (σ * swap i₀ j) * swap (σ i₀) (σ j) := by rw [← mul_assoc, ← h1]
          _ = σ * (swap i₀ j * swap (σ i₀) (σ j)) := by rw [mul_assoc]
      · intro k hk
        obtain ⟨h1, h2⟩ := ne_of_fix_of_moved hσσ hk hi₀
        obtain ⟨h3, h4⟩ := ne_of_fix_of_moved hσσ hk hj
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne h2 h4, swap_apply_of_ne_of_ne h1 h3]
      · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hi₀.symm hej.symm, swap_apply_left]
      · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hej hj]
    rcases hpair i₀ hi₀ with h1 | h1
    · left
      intro j hj
      by_cases hji : j = i₀
      · rw [hji]; exact h1
      by_cases hje : j = σ i₀
      · rw [hje, ← hes, h1]
      obtain ⟨π, hπ, hπF, hπi, -⟩ := key j hj hji hje
      have := congrArg (fun f : Perm (Fin n) => f i₀) (hcommF π hπ hπF)
      simp only [Perm.mul_apply, h1, hπi] at this
      exact this.symm
    · right
      intro j hj
      by_cases hji : j = i₀
      · rw [hji]; exact h1
      by_cases hje : j = σ i₀
      · rw [hje, ← hes, h1]
      obtain ⟨π, hπ, hπF, hπi, hπe⟩ := key j hj hji hje
      have := congrArg (fun f : Perm (Fin n) => f i₀) (hcommF π hπ hπF)
      simp only [Perm.mul_apply, h1, hπi, hπe] at this
      exact this.symm
  · push Not at hex
    exact Or.inl fun i hi => absurd (hex i) hi

private theorem fix_cases_of_card_three {σ s : Perm (Fin n)} (hs2 : s * s = 1) (hsσ : s * σ = σ * s)
    (h3 : (fixFin σ).card = 3) :
    (∀ i, σ i = i → s i = i) ∨
      ∃ p q : Fin n, p ≠ q ∧ σ p = p ∧ σ q = q ∧ ∀ i, σ i = i → s i = swap p q i := by
  classical
  have hes : ∀ i, σ (s i) = s (σ i) := fun i => by rw [← Perm.mul_apply, ← hsσ, Perm.mul_apply]
  have hss : ∀ i, s (s i) = i := fun i => by rw [← Perm.mul_apply, hs2, Perm.one_apply]
  have hsF : ∀ i, σ i = i → σ (s i) = s i := fun i hi => by rw [hes, hi]
  by_cases hFs : ∀ i, σ i = i → s i = i
  · exact Or.inl hFs
  push Not at hFs
  obtain ⟨p, hp, hsp⟩ := hFs
  obtain ⟨q, hq⟩ : ∃ q, s p = q := ⟨_, rfl⟩
  have hqF : σ q = q := by rw [← hq]; exact hsF p hp
  have hpq : p ≠ q := fun h => hsp (by rw [hq]; exact h.symm)
  have hsq : s q = p := by rw [← hq, hss]
  have hrest : ∀ r, σ r = r → r ≠ p → r ≠ q → s r = r := by
    intro r hr hrp hrq
    by_contra hsr
    have hsrp : s r ≠ p := fun h => hrq (s.injective (h.trans hsq.symm))
    have hsrq : s r ≠ q := fun h => hrp (s.injective (h.trans hq.symm))
    have hmem : s r ∈ (((fixFin σ).erase p).erase q).erase r :=
      Finset.mem_erase.2 ⟨hsr, Finset.mem_erase.2 ⟨hsrq, Finset.mem_erase.2
        ⟨hsrp, mem_fixFin.2 (hsF r hr)⟩⟩⟩
    have hcard : ((((fixFin σ).erase p).erase q).erase r).card = 0 := by
      have h1 := Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hrq, Finset.mem_erase.2
        ⟨hrp, mem_fixFin.2 hr⟩⟩)
      have h2 := Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hpq.symm, mem_fixFin.2 hqF⟩)
      have h4 := Finset.card_erase_of_mem (mem_fixFin.2 hp)
      omega
    rw [Finset.card_eq_zero] at hcard
    rw [hcard] at hmem
    exact Finset.notMem_empty _ hmem
  refine Or.inr ⟨p, q, hpq, hp, hqF, fun i hi => ?_⟩
  by_cases hip : i = p
  · rw [hip, swap_apply_left, hq]
  by_cases hiq : i = q
  · rw [hiq, swap_apply_right, hsq]
  rw [swap_apply_of_ne_of_ne hip hiq, hrest i hi hip hiq]

theorem perm_cases_of_comm_fix {σ s : Perm (Fin n)} (hσ2 : σ * σ = 1) (hs2 : s * s = 1)
    (hsσ : s * σ = σ * s)
    (hfix : ∀ π₀ : Perm (Fin n), π₀ * σ = σ * π₀ → ∀ i, σ i ≠ i → (π₀ * s * π₀⁻¹ * s⁻¹) i = i)
    (hcomm : (fixFin σ).card ≠ 3 → ∀ π₀ : Perm (Fin n), π₀ * σ = σ * π₀ → π₀ * s = s * π₀) :
    s = 1 ∨ s = σ ∨ ∃ p q : Fin n, p ≠ q ∧ σ p = p ∧ σ q = q ∧
      ((fixFin σ).card = 2 ∨ (fixFin σ).card = 3) ∧ (s = swap p q ∨ s = σ * swap p q) := by
  classical
  by_cases h3 : (fixFin σ).card = 3
  swap
  · rcases perm_cases_of_forall_comm hσ2 (hcomm h3) with h | h | ⟨p, q, hpq, hiff, hs⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨p, q, hpq, (hiff p).2 (Or.inl rfl), (hiff q).2 (Or.inr rfl),
        Or.inl ?_, hs⟩)
      have : fixFin σ = {p, q} := by
        ext i
        rw [mem_fixFin, hiff]
        simp
      rw [this, Finset.card_pair hpq]
  have hes : ∀ i, σ (s i) = s (σ i) := fun i => by rw [← Perm.mul_apply, ← hsσ, Perm.mul_apply]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hss : ∀ i, s (s i) = i := fun i => by rw [← Perm.mul_apply, hs2, Perm.one_apply]
  have hcommF : ∀ π₀ : Perm (Fin n), π₀ * σ = σ * π₀ → (∀ k, σ k = k → π₀ k = k) →
      π₀ * s = s * π₀ := by
    intro π₀ hπ₀ hid
    have hk : π₀ * s * π₀⁻¹ * s⁻¹ = 1 := by
      refine Perm.ext fun i => ?_
      by_cases hi : σ i = i
      · have h1 : σ (s i) = s i := by rw [hes, hi]
        have h2 : π₀⁻¹ (s i) = s i := by
          rw [Perm.inv_eq_iff_eq]
          exact (hid _ h1).symm
        simp only [Perm.mul_apply, hsinv, h2, hss, Perm.one_apply, hid i hi]
      · rw [hfix π₀ hπ₀ i hi, Perm.one_apply]
    calc π₀ * s = π₀ * s * π₀⁻¹ * s⁻¹ * (s * π₀) := by group
      _ = s * π₀ := by rw [hk, one_mul]
  have hunif := uniform_of_comm_fix hσ2 hsσ hcommF
  rcases fix_cases_of_card_three hs2 hsσ h3 with hF | ⟨p, q, hpq, hp, hq, hF⟩
  · rcases hunif with hu | hu
    · left
      refine Perm.ext fun i => ?_
      by_cases hi : σ i = i
      · rw [hF i hi, Perm.one_apply]
      · rw [hu i hi, Perm.one_apply]
    · right; left
      refine Perm.ext fun i => ?_
      by_cases hi : σ i = i
      · rw [hF i hi, hi]
      · rw [hu i hi]
  · have hpσ : ∀ i, σ i ≠ i → swap p q i = i := fun i hi =>
      swap_apply_of_ne_of_ne (fun h => hi (by rw [h]; exact hp))
        (fun h => hi (by rw [h]; exact hq))
    refine Or.inr (Or.inr ⟨p, q, hpq, hp, hq, Or.inr h3, ?_⟩)
    rcases hunif with hu | hu
    · left
      refine Perm.ext fun i => ?_
      by_cases hi : σ i = i
      · exact hF i hi
      · rw [hu i hi, hpσ i hi]
    · right
      refine Perm.ext fun i => ?_
      by_cases hi : σ i = i
      · have h1 : σ (s i) = s i := by rw [hes, hi]
        rw [Perm.mul_apply, ← hF i hi, h1]
      · rw [hu i hi, Perm.mul_apply, hpσ i hi]

theorem fix_of_mem_oddNormal {t : Perm (Fin n)} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    {D : Subgroup (Perm (Fin n))} (hDodd : Odd (Nat.card D))
    (hDt : D ≤ centralizer ({t} : Set (Perm (Fin n))))
    (hDn : ∀ g : Perm (Fin n), g * t = t * g → ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    {d : Perm (Fin n)} (hd : d ∈ D) :
    (∀ i, t i ≠ i → d i = i) ∧ ((fixFin t).card ≠ 3 → d = 1) := by
  classical
  have htord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have htt : ∀ ω, t (t ω) = ω := fun ω => by rw [← Perm.mul_apply, ht2, Perm.one_apply]
  have hDC : D ≤ (⊤ : Subgroup (Perm (Fin n))) ⊓ centralizer ({t} : Set (Perm (Fin n))) :=
    fun x hx => ⟨mem_top x, hDt hx⟩
  have hnorm : (D.subgroupOf
      ((⊤ : Subgroup (Perm (Fin n))) ⊓ centralizer ({t} : Set (Perm (Fin n))))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hDn g (mem_centralizer_singleton_iff.1 g.2.2) x hx
  have hodd : Odd (Nat.card (D.subgroupOf
      ((⊤ : Subgroup (Perm (Fin n))) ⊓ centralizer ({t} : Set (Perm (Fin n)))))) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
  have hdO : (⟨d, hDC hd⟩ :
      ↥((⊤ : Subgroup (Perm (Fin n))) ⊓ centralizer ({t} : Set (Perm (Fin n))))) ∈
      CFSG.oddCore
        ↥((⊤ : Subgroup (Perm (Fin n))) ⊓ centralizer ({t} : Set (Perm (Fin n)))) :=
    ComponentClassification.SmallLocal.le_oddCore_of_normal_odd hnorm hodd
      (Subgroup.mem_subgroupOf.2 hd)
  refine ⟨fun i hi => ComponentClassification.SymmetricLocal.oddCore_apply_eq_self
    inf_le_right (inf_le_inf_right _ le_top) htt hdO hi, fun h3 => ?_⟩
  have h3' : Nat.card {ω // t ω = ω} ≠ 3 := by
    have h := card_fixedPoints_eq t
    exact fun h' => h3 (h.symm.trans h')
  have hbot :=
    (ComponentClassification.SymmetricLocal.involution_permutation_centralizer_odd_core
      (H := ⊤) le_top htord).1 h3'
  rw [hbot] at hdO
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hdO)

end CFSG.OddStandard.AltStdCycTwo.Two
