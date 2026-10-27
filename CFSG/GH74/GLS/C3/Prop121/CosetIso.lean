module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm

namespace CosetIso

variable {G : Type} [Group G]

theorem card_alt (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem exists_stab_iso {n : ℕ} (hn : 5 ≤ n) {K L : Subgroup G} (hKL : K ≤ L)
    (lam : ↥L ≃* alternatingGroup (Fin (n + 1))) (eK : ↥K ≃* alternatingGroup (Fin n))
    (hperf : commutator ↥L = ⊤) :
    ∃ lam' : ↥L ≃* alternatingGroup (Fin (n + 1)),
      ∀ l : ↥L, (l : G) ∈ K ↔
        ((lam' l : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) 0 = 0 := by
  classical
  have hL : Nat.card L = (n + 1).factorial / 2 := by
    rw [Nat.card_congr lam.toEquiv, card_alt _ (by omega)]
  have hK : Nat.card K = n.factorial / 2 := by
    rw [Nat.card_congr eK.toEquiv, card_alt _ (by omega)]
  set K' : Subgroup ↥L := K.subgroupOf L with hK'def
  have hK'card : Nat.card ↥K' = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
  have hidx : K'.index = n + 1 := by
    have h1 := K'.index_mul_card
    rw [hK'card, hK, hL] at h1
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (by norm_num : 0 < 2) (by omega : 2 ≤ n)
    have hc0 : 0 < c := by
      have := Nat.factorial_pos n
      omega
    have h2 : n.factorial / 2 = c := by rw [hc]; omega
    have h3 : (n + 1).factorial / 2 = (n + 1) * c := by
      rw [Nat.factorial_succ, hc, ← mul_assoc, mul_comm (n + 1) 2, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rw [h2, h3] at h1
    exact Nat.eq_of_mul_eq_mul_right hc0 h1
  have : IsSimpleGroup (alternatingGroup (Fin (n + 1))) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have : IsSimpleGroup ↥L := lam.isSimpleGroup
  have : Finite ↥L := by
    apply Nat.finite_of_card_ne_zero
    rw [hL]
    have := Nat.factorial_pos (n + 1)
    have h2 : 2 ∣ (n + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    omega
  let Ω := ↥L ⧸ K'
  have hΩ : Nat.card Ω = n + 1 := hidx
  have : Finite Ω := inferInstance
  let e0 : Ω ≃ Fin (n + 1) := (Finite.equivFin Ω).trans (finCongr hΩ)
  let b : Ω := QuotientGroup.mk 1
  let e : Ω ≃ Fin (n + 1) := e0.trans (Equiv.swap (e0 b) 0)
  have heb : e b = 0 := by simp [e]
  let pc : Perm Ω →* Perm (Fin (n + 1)) :=
    { toFun := e.permCongr
      map_one' := by ext x; simp [Equiv.permCongr_apply]
      map_mul' := e.permCongr_mul }
  let ρ : ↥L →* Perm (Fin (n + 1)) := pc.comp (MulAction.toPermHom ↥L Ω)
  have hρ : ∀ (l : ↥L) (i : Fin (n + 1)), ρ l i = e (l • e.symm i) := by
    intro l i
    simp [ρ, pc, Equiv.permCongr_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply]
  have hstab : ∀ l : ↥L, (l : G) ∈ K ↔ ρ l 0 = 0 := by
    intro l
    rw [hρ, ← heb, Equiv.symm_apply_apply, e.apply_eq_iff_eq]
    show (l : G) ∈ K ↔ l • (QuotientGroup.mk 1 : Ω) = QuotientGroup.mk 1
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simp [K', Subgroup.mem_subgroupOf]
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      have hall : ∀ l : ↥L, (l : G) ∈ K := by
        intro l
        apply (hstab l).2
        have h1 : l ∈ ρ.ker := by rw [h]; trivial
        rw [MonoidHom.mem_ker] at h1
        rw [h1]; rfl
      have h2 : K' = ⊤ := by
        rw [eq_top_iff]
        intro l _
        exact Subgroup.mem_subgroupOf.2 (hall l)
      rw [h2, Subgroup.index_top] at hidx
      omega
  have hsign : ∀ l : ↥L, Equiv.Perm.sign (ρ l) = 1 := by
    have h1 : (⊤ : Subgroup ↥L) ≤ ((Equiv.Perm.sign : Perm (Fin (n + 1)) →* ℤˣ).comp ρ).ker := by
      rw [← hperf]
      refine Subgroup.commutator_le.2 (fun a _ b _ => ?_)
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
    intro l
    have h2 := h1 (Subgroup.mem_top l)
    rwa [MonoidHom.mem_ker] at h2
  let ρ' : ↥L →* alternatingGroup (Fin (n + 1)) :=
    ρ.codRestrict (alternatingGroup (Fin (n + 1)))
      (fun l => Equiv.Perm.mem_alternatingGroup.2 (hsign l))
  have hρ'inj : Function.Injective ρ' := fun a b h => hinj (congrArg Subtype.val h)
  have hρ'bij : Function.Bijective ρ' :=
    hρ'inj.bijective_of_nat_card_le (le_of_eq (Nat.card_congr lam.toEquiv.symm))
  exact ⟨MulEquiv.ofBijective ρ' hρ'bij, fun l => hstab l⟩

theorem isThreeCycle_of_fixed {σ : Perm (Fin 6)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) (hp : σ 0 = 0) :
    σ.IsThreeCycle := by
  have hall : ∀ k ∈ σ.cycleType, k = 3 := by
    intro k hk
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hk
    have hd : k ∣ 3 := (Equiv.Perm.dvd_of_mem_cycleType hk).trans (orderOf_dvd_of_pow_eq_one h3)
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · omega
    · exact h
  have hsupp : σ.support.card ≤ 5 := by
    have h2 : σ.support ⊆ Finset.univ.erase 0 := by
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      exact (Equiv.Perm.mem_support.1 hx) hp
    calc σ.support.card ≤ (Finset.univ.erase (0 : Fin 6)).card := Finset.card_le_card h2
      _ = 5 := by simp
  have hne : σ.cycleType ≠ 0 := fun h => h1 (Equiv.Perm.cycleType_eq_zero.1 h)
  have hsum := Equiv.Perm.sum_cycleType σ
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate.2 ⟨rfl, hall⟩
  have hs : σ.cycleType.sum = Multiset.card σ.cycleType * 3 := by
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate, smul_eq_mul]
  have hpos : 0 < Multiset.card σ.cycleType := Multiset.card_pos.2 hne
  have hcard : Multiset.card σ.cycleType = 1 := by omega
  show σ.cycleType = {3}
  rw [hrep, hcard]
  rfl

theorem threeCycle_transfer {n : ℕ} {L : Subgroup G}
    (hAut : n ≠ 5 → ∀ α : MulAut (alternatingGroup (Fin (n + 1))),
      ∃ σ : Perm (Fin (n + 1)), ∀ a : alternatingGroup (Fin (n + 1)),
        ((α a : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) = σ * a * σ⁻¹)
    (lam lam' : ↥L ≃* alternatingGroup (Fin (n + 1))) (l : ↥L) (hl3 : l ^ 3 = 1) (hl1 : l ≠ 1)
    (hl : n ≠ 5 → ((lam l : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))).IsThreeCycle)
    (h0 : ((lam' l : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) 0 = 0) :
    ((lam' l : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))).IsThreeCycle := by
  by_cases h5 : n = 5
  · subst h5
    have h3 : ((lam' l : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ 3 = 1 := by
      have : (lam' l) ^ 3 = 1 := by rw [← map_pow, hl3, map_one]
      simpa using congrArg Subtype.val this
    have hne : ((lam' l : alternatingGroup (Fin 6)) : Perm (Fin 6)) ≠ 1 := by
      intro h
      apply hl1
      apply lam'.injective
      apply Subtype.ext
      simpa using h
    exact isThreeCycle_of_fixed h3 hne h0
  · obtain ⟨σ, hσ⟩ := hAut h5 (lam.symm.trans lam')
    have h1 : ((lam' l : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) =
        σ * ((lam l : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) * σ⁻¹ := by
      have := hσ (lam l)
      simpa using this
    rw [h1]
    have hl' := hl h5
    unfold Equiv.Perm.IsThreeCycle at hl' ⊢
    rw [Equiv.Perm.cycleType_conj]
    exact hl'

end CosetIso

end CFSG.GH74.GLS.C3.Prop121
