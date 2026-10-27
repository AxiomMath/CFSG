module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GH74.QTGen4.Ku

abbrev perm5Cent (c : Equiv.Perm (Fin 5)) : Finset (Equiv.Perm (Fin 5)) :=
  Finset.univ.filter (fun x => c * x = x * c)

theorem perm5_cent_check :
    ∀ c : Equiv.Perm (Fin 5), c ≠ 1 → c ^ 8 = 1 → 8 ∣ (perm5Cent c).card →
      (perm5Cent c).card = 8 ∧
        ∃ x ∈ perm5Cent c, ∃ y ∈ perm5Cent c, x * y ≠ y * x := by
  decide +kernel

theorem card_eq_card_filter_mem (H : Subgroup (Equiv.Perm (Fin 5))) [DecidablePred (· ∈ H)] :
    Nat.card H = (Finset.univ.filter (· ∈ H)).card := by
  classical
  exact (Nat.card_eq_fintype_card).trans (Fintype.card_subtype (· ∈ H))

theorem not_isMulCommutative_of_card_eq_eight_perm5 (K : Subgroup (Equiv.Perm (Fin 5)))
    (hK : Nat.card K = 8) : ¬ IsMulCommutative K := by
  classical
  intro hcomm
  have hcomm' : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm (⟨a, ha⟩ : K) ⟨b, hb⟩)
  obtain ⟨c, hcK, hc1⟩ : ∃ c ∈ K, c ≠ 1 := by
    by_contra h
    have h' : ∀ z ∈ K, z = 1 := fun z hz => by
      by_contra hne
      exact h ⟨z, hz, hne⟩
    have hbot : K = ⊥ := (Subgroup.eq_bot_iff_forall K).2 h'
    rw [hbot, Subgroup.card_bot] at hK
    omega
  have hpow : c ^ 8 = 1 := by
    have hd : orderOf (⟨c, hcK⟩ : K) ∣ 8 := hK ▸ orderOf_dvd_natCard (⟨c, hcK⟩ : K)
    have h8 : (⟨c, hcK⟩ : K) ^ 8 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
    have := congrArg Subtype.val h8
    simpa using this
  have hKH : K ≤ Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 5))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hcomm' c hcK x hx
  have hcardC : Nat.card (Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 5))))
      = (perm5Cent c).card := by
    rw [card_eq_card_filter_mem]
    congr 1
    ext x
    simp [perm5Cent, Subgroup.mem_centralizer_iff]
  have h8 : 8 ∣ (perm5Cent c).card := by
    have h1 := Subgroup.card_dvd_of_le hKH
    rwa [hK, hcardC] at h1
  obtain ⟨hcard, x, hx, y, hy, hxy⟩ := perm5_cent_check c hc1 hpow h8
  have hKf : (Finset.univ.filter (· ∈ K)).card = 8 := by
    rw [← card_eq_card_filter_mem K]
    exact hK
  have hsub : Finset.univ.filter (· ∈ K) ⊆ perm5Cent c := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, perm5Cent] at hz ⊢
    exact hcomm' c hcK z hz
  have heq : Finset.univ.filter (· ∈ K) = perm5Cent c :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have memK : ∀ z, z ∈ perm5Cent c → z ∈ K := by
    intro z hz
    rw [← heq] at hz
    simpa using hz
  exact hxy (hcomm' x (memK x hx) y (memK y hy))

end CFSG.GH74.QTGen4.Ku

end
