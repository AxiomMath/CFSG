module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G33RF

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

section A7

open Equiv in
theorem swap_mul_swap_eq_three_cycles : ∀ α β γ δ : Fin 7,
    (α ≠ β ∧ α ≠ γ ∧ α ≠ δ ∧ β ≠ γ ∧ β ≠ δ ∧ γ ≠ δ) →
      swap α β * swap γ δ = (swap α γ * swap γ β) * (swap α γ * swap γ δ) := by decide +kernel

open Equiv in
theorem three_cycle_cube : ∀ α γ β : Fin 7, (α ≠ γ ∧ α ≠ β ∧ γ ≠ β) →
    (swap α γ * swap γ β) ^ 3 = 1 := by decide +kernel

variable {Kb : Type} [Group Kb]

@[expose] noncomputable def fixedEquivA7 (e7 : Kb ≃* alternatingGroup (Fin 7)) (σ : MulAut Kb) :
    ↥(fixedSubgroup Kb σ) ≃*
      ↥(centralizer ({psiEquiv e7 σ} : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) := by
  have hfix : ∀ k : Kb, σ k = k ↔
      psiEquiv e7 σ * ((e7 k : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        ((e7 k : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * psiEquiv e7 σ := by
    intro k
    constructor
    · intro h
      have h1 := psi_apply e7 σ k
      rw [h] at h1
      calc psiEquiv e7 σ * ((e7 k : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
          = (psiEquiv e7 σ * ((e7 k : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
              (psiEquiv e7 σ)⁻¹) * psiEquiv e7 σ := by group
        _ = ((e7 k : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * psiEquiv e7 σ := by
          rw [← h1]
    · intro h
      apply e7.injective
      apply Subtype.ext
      rw [psi_apply, h, mul_inv_cancel_right]
  let f : ↥(fixedSubgroup Kb σ) →*
      ↥(centralizer ({psiEquiv e7 σ} : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) :=
    ((alternatingGroup (Fin 7)).subtype.comp (e7.toMonoidHom.comp
      (fixedSubgroup Kb σ).subtype)).codRestrict
      (centralizer ({psiEquiv e7 σ} : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7))
      (fun k => ⟨mem_centralizer_singleton_iff.2 ((hfix k).1 k.2).symm, (e7 k).2⟩)
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    have h1 := congrArg (fun w : ↥(centralizer ({psiEquiv e7 σ} : Set (Equiv.Perm (Fin 7))) ⊓
      alternatingGroup (Fin 7)) => (w : Equiv.Perm (Fin 7))) hab
    exact Subtype.ext (e7.injective (Subtype.ext h1))
  · rintro ⟨w, hwc, hwA⟩
    have hk : σ (e7.symm ⟨w, hwA⟩) = e7.symm ⟨w, hwA⟩ := by
      rw [hfix]
      simpa using (mem_centralizer_singleton_iff.1 hwc).symm
    exact ⟨⟨e7.symm ⟨w, hwA⟩, hk⟩, Subtype.ext (by simp [f])⟩

theorem fixedEquivA7_apply (e7 : Kb ≃* alternatingGroup (Fin 7)) (σ : MulAut Kb)
    (k : ↥(fixedSubgroup Kb σ)) :
    ((fixedEquivA7 e7 σ k : ↥(centralizer ({psiEquiv e7 σ} : Set (Equiv.Perm (Fin 7))) ⊓
      alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) =
      ((e7 (k : Kb) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := rfl

open Equiv in
theorem swap_comm_of_ne {a b p q : Fin 7} (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    swap p q * swap a b = swap a b * swap p q := by
  rw [Equiv.mul_swap_eq_swap_mul, Equiv.swap_apply_of_ne_of_ne (Ne.symm hpa) (Ne.symm hqa),
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hpb) (Ne.symm hqb)]

open Equiv in
theorem three_cycle_comm_swap {a b p q r : Fin 7} (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a)
    (hqb : q ≠ b) (hra : r ≠ a) (hrb : r ≠ b) :
    (swap p q * swap q r) * swap a b = swap a b * (swap p q * swap q r) := by
  calc (swap p q * swap q r) * swap a b = swap p q * (swap q r * swap a b) := by group
    _ = swap p q * (swap a b * swap q r) := by rw [swap_comm_of_ne hqa hqb hra hrb]
    _ = (swap p q * swap a b) * swap q r := by group
    _ = (swap a b * swap p q) * swap q r := by rw [swap_comm_of_ne hpa hpb hqa hqb]
    _ = swap a b * (swap p q * swap q r) := by group

theorem card_support_le_of_fixed (t : Equiv.Perm (Fin 7)) (S : Finset (Fin 7))
    (hS : ∀ x ∈ S, t x = x) : t.support.card + S.card ≤ 7 := by
  have hdisj : Disjoint t.support S := by
    rw [Finset.disjoint_left]
    intro x hx hxS
    exact (Equiv.Perm.mem_support.1 hx) (hS x hxS)
  calc t.support.card + S.card = (t.support ∪ S).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ Fintype.card (Fin 7) := Finset.card_le_univ _
    _ = 7 := Fintype.card_fin 7

theorem odd_involution_swap_of_fixed {t : Equiv.Perm (Fin 7)} (ht2 : orderOf t = 2)
    (hodd : t ∉ alternatingGroup (Fin 7)) (S : Finset (Fin 7)) (hS : ∀ x ∈ S, t x = x)
    (hcard : 2 ≤ S.card) : t.cycleType = {2} := by
  rcases odd_involution_cycleType ht2 hodd with h | h
  · exact h
  · exfalso
    have h1 := card_support_le_of_fixed t S hS
    have h2 := Equiv.Perm.sum_cycleType t
    rw [h] at h2
    have h3 : ({2, 2, 2} : Multiset ℕ).sum = 6 := by decide
    omega

open Equiv in
theorem perm_dichotomy {s u : Perm (Fin 7)} (hss : s * s = 1)
    (hsodd : s ∉ alternatingGroup (Fin 7)) (hsct : s.cycleType = {2})
    (huA : u ∈ alternatingGroup (Fin 7)) (huu : u * u = 1) (hu1 : u ≠ 1) (hus : s * u = u * s) :
    (∃ g ∈ alternatingGroup (Fin 7), g * (s * u) * g⁻¹ = s) ∨
      ∃ c₁ c₂ : Perm (Fin 7), c₁ ∈ alternatingGroup (Fin 7) ∧ c₂ ∈ alternatingGroup (Fin 7) ∧
        c₁ ^ 3 = 1 ∧ c₂ ^ 3 = 1 ∧ c₁ * s = s * c₁ ∧ c₂ * s = s * c₂ ∧ u = c₁ * c₂ := by
  classical
  obtain ⟨a, b, hab, hsab⟩ := Equiv.Perm.isSwap_iff_cycleType.mpr hsct
  have hsa : s a = b := by rw [hsab]; exact Equiv.swap_apply_left a b
  have hsb : s b = a := by rw [hsab]; exact Equiv.swap_apply_right a b
  have hcomm : ∀ x, u (s x) = s (u x) := fun x => by
    have := congrArg (fun w : Perm (Fin 7) => w x) hus
    simpa [Equiv.Perm.mul_apply] using this.symm
  have huinv : ∀ x, u (u x) = x := fun x => by
    have := congrArg (fun w : Perm (Fin 7) => w x) huu
    simpa [Equiv.Perm.mul_apply] using this
  have hsign_s : Equiv.Perm.sign s = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hsodd
    · exact h
  have hsign_u : Equiv.Perm.sign u = 1 := Equiv.Perm.mem_alternatingGroup.1 huA
  by_cases hua : u a = a
  ·
    right
    have hub : u b = b := by
      have := hcomm a
      rw [hsa, hua, hsa] at this
      exact this
    obtain ⟨α, hα⟩ : ∃ α, u α ≠ α := by
      by_contra hcon
      push Not at hcon
      exact hu1 (Equiv.ext hcon)
    obtain ⟨β, hβ⟩ : ∃ β, β = u α := ⟨_, rfl⟩
    have huβ : u β = α := by rw [hβ]; exact huinv α
    have hαa : α ≠ a := fun h => hα (by rw [h]; exact hua)
    have hαb : α ≠ b := fun h => hα (by rw [h]; exact hub)
    have hβa : β ≠ a := fun h => hαa (by rw [← huβ, h, hua])
    have hβb : β ≠ b := fun h => hαb (by rw [← huβ, h, hub])
    have hαβ : α ≠ β := fun h => hα (by rw [← hβ]; exact h.symm)
    have hswu : swap α β * u = u * swap α β := by
      rw [Equiv.mul_swap_eq_swap_mul, ← hβ, huβ, Equiv.swap_comm]
    have ht'a : (swap α β * u) a = a := by
      rw [Equiv.Perm.mul_apply, hua]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hαa) (Ne.symm hβa)
    have ht'b : (swap α β * u) b = b := by
      rw [Equiv.Perm.mul_apply, hub]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hαb) (Ne.symm hβb)
    have ht'α : (swap α β * u) α = α := by
      rw [Equiv.Perm.mul_apply, ← hβ]
      exact Equiv.swap_apply_right α β
    have ht'β : (swap α β * u) β = β := by
      rw [Equiv.Perm.mul_apply, huβ]
      exact Equiv.swap_apply_left α β
    have ht'sq : (swap α β * u) * (swap α β * u) = 1 := by
      calc swap α β * u * (swap α β * u) = swap α β * (u * swap α β) * u := by group
        _ = swap α β * (swap α β * u) * u := by rw [hswu]
        _ = (swap α β * swap α β) * (u * u) := by group
        _ = 1 := by rw [Equiv.swap_mul_self, huu, one_mul]
    have ht'odd : swap α β * u ∉ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hαβ, hsign_u]
      decide
    have ht'1 : swap α β * u ≠ 1 := fun h => ht'odd (h ▸ one_mem _)
    have ht'2 : orderOf (swap α β * u) = 2 := orderOf_eq_prime (by rw [sq]; exact ht'sq) ht'1
    have hdist : ({a, b, α, β} : Finset (Fin 7)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hαβ]
      · simp [hαb.symm, hβb.symm]
      · simp [hab, hαa.symm, hβa.symm]
    have ht'ct : (swap α β * u).cycleType = {2} :=
      odd_involution_swap_of_fixed ht'2 ht'odd {a, b, α, β} (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ht'a
        · exact ht'b
        · exact ht'α
        · exact ht'β) (by omega)
    obtain ⟨γ, δ, hγδ, hsw⟩ := Equiv.Perm.isSwap_iff_cycleType.mpr ht'ct
    have hγ : (swap α β * u) γ ≠ γ := by rw [hsw, Equiv.swap_apply_left]; exact hγδ.symm
    have hδ : (swap α β * u) δ ≠ δ := by rw [hsw, Equiv.swap_apply_right]; exact hγδ
    have hγa : γ ≠ a := fun h => hγ (by rw [h]; exact ht'a)
    have hγb : γ ≠ b := fun h => hγ (by rw [h]; exact ht'b)
    have hγα : γ ≠ α := fun h => hγ (by rw [h]; exact ht'α)
    have hγβ : γ ≠ β := fun h => hγ (by rw [h]; exact ht'β)
    have hδa : δ ≠ a := fun h => hδ (by rw [h]; exact ht'a)
    have hδb : δ ≠ b := fun h => hδ (by rw [h]; exact ht'b)
    have hδα : δ ≠ α := fun h => hδ (by rw [h]; exact ht'α)
    have hδβ : δ ≠ β := fun h => hδ (by rw [h]; exact ht'β)
    have hu_eq : u = swap α β * swap γ δ := by
      rw [← hsw, Equiv.swap_mul_self_mul]
    refine ⟨swap α γ * swap γ β, swap α γ * swap γ δ, ?_, ?_, three_cycle_cube α γ β
      ⟨Ne.symm hγα, hαβ, hγβ⟩, three_cycle_cube α γ δ ⟨Ne.symm hγα, fun h => hδα h.symm, hγδ⟩, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hγα),
        Equiv.Perm.sign_swap hγβ]
      decide
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hγα),
        Equiv.Perm.sign_swap hγδ]
      decide
    · rw [hsab]
      exact three_cycle_comm_swap hαa hαb hγa hγb hβa hβb
    · rw [hsab]
      exact three_cycle_comm_swap hαa hαb hγa hγb hδa hδb
    · rw [hu_eq]
      exact swap_mul_swap_eq_three_cycles α β γ δ ⟨hαβ, Ne.symm hγα, fun h => hδα h.symm, fun h => hγβ h.symm, fun h => hδβ h.symm, hγδ⟩
  ·
    left
    have hsx : ∀ x, x ≠ a → x ≠ b → s x = x := fun x h1 h2 => by
      rw [hsab]; exact Equiv.swap_apply_of_ne_of_ne h1 h2
    have hua' : u a = b := by
      by_contra hne
      have h1 := hcomm a
      rw [hsa, hsx (u a) hua hne] at h1
      exact hab (u.injective h1).symm
    have hub' : u b = a := by
      have := hcomm a
      rw [hsa, hua', hsb] at this
      exact this
    have hta : (s * u) a = a := by rw [Equiv.Perm.mul_apply, hua', hsb]
    have htb : (s * u) b = b := by rw [Equiv.Perm.mul_apply, hub', hsa]
    have htsq : (s * u) * (s * u) = 1 := by
      calc s * u * (s * u) = s * (u * s) * u := by group
        _ = s * (s * u) * u := by rw [← hus]
        _ = (s * s) * (u * u) := by group
        _ = 1 := by rw [hss, huu, one_mul]
    have htodd : s * u ∉ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hsign_s, hsign_u]
      decide
    have ht1 : s * u ≠ 1 := fun h => htodd (h ▸ one_mem _)
    have ht2 : orderOf (s * u) = 2 := orderOf_eq_prime (by rw [sq]; exact htsq) ht1
    have htct : (s * u).cycleType = {2} :=
      odd_involution_swap_of_fixed ht2 htodd {a, b} (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hta
        · exact htb) (by rw [Finset.card_pair hab])
    exact exists_alt_conj_of_odd htodd htsq
      (Equiv.Perm.isConj_iff_cycleType_eq.2 (by rw [htct, hsct]))

open Equiv in
theorem autLevelRF_of_A7 (e7 : Kb ≃* alternatingGroup (Fin 7)) : AutLevelRF Kb := by
  classical
  intro B hB hSyl E hEB hE hE8 σ' hσ'B hσ'2 hσ'inn hσ'c hns q hqB hq2 hqO
  have hinn : ∀ x : MulAut Kb, psiEquiv e7 x ∈ alternatingGroup (Fin 7) ↔ x ∈ innAut Kb := by
    intro x
    have h := (Subgroup.mem_map_equiv (f := psiEquiv e7) (K := innAut Kb) (x := psiEquiv e7 x))
    rw [psi_map_innAut e7] at h
    simpa using h
  obtain ⟨s, hs⟩ : ∃ s, psiEquiv e7 σ' = s := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, psiEquiv e7 q = u := ⟨_, rfl⟩
  have hs2 : orderOf s = 2 := by rw [← hs, MulEquiv.orderOf_eq]; exact hσ'2
  have hss : s * s = 1 := by have := pow_orderOf_eq_one s; rwa [hs2, sq] at this
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs2; omega
  have hsodd : s ∉ alternatingGroup (Fin 7) := fun h => hσ'inn ((hinn σ').1 (hs ▸ h))
  have huA : u ∈ alternatingGroup (Fin 7) := hu ▸ (hinn q).2 hqB.2
  have hu2 : orderOf u = 2 := by rw [← hu, MulEquiv.orderOf_eq]; exact hq2
  have huu : u * u = 1 := by have := pow_orderOf_eq_one u; rwa [hu2, sq] at this
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
  have hus : s * u = u * s := by
    rw [← hs, ← hu, ← map_mul, ← map_mul, hσ'c q hqB]
  have hsct : s.cycleType = {2} := by
    rcases odd_involution_cycleType hs2 hsodd with h | h
    · exact h
    · exfalso
      have h24 := IVK.A7.card_centralizer_A7_two_two_two h (by rw [sq]; exact hss) hs1
      have hcard := Nat.card_congr (fixedEquivA7 e7 σ').toEquiv
      rw [hs, h24] at hcard
      omega
  rcases perm_dichotomy hss hsodd hsct huA huu hu1 hus with
    ⟨g, hg, hgsu⟩ | ⟨c₁, c₂, hc₁A, hc₂A, hc₁3, hc₂3, hc₁s, hc₂s, huc⟩
  · refine ⟨(psiEquiv e7).symm g, (hinn _).1 (by simpa using hg), ?_⟩
    apply (psiEquiv e7).injective
    have h1 : psiEquiv e7 ((psiEquiv e7).symm g * (σ' * q) * ((psiEquiv e7).symm g)⁻¹) =
        g * (s * u) * g⁻¹ := by
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hs, hu]
    rw [h1, hgsu, ← hs]
  · exfalso
    apply hqO
    subst hs
    subst hu
    set Cp : Subgroup (Equiv.Perm (Fin 7)) :=
      centralizer ({psiEquiv e7 σ'} : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) with hCp
    have hmem : ∀ c : Equiv.Perm (Fin 7), c ∈ alternatingGroup (Fin 7) →
        c * psiEquiv e7 σ' = psiEquiv e7 σ' * c → c ∈ Cp := fun c hcA hcs =>
      ⟨mem_centralizer_singleton_iff.2 hcs, hcA⟩
    let c₁' : ↥Cp := ⟨c₁, hmem c₁ hc₁A hc₁s⟩
    let c₂' : ↥Cp := ⟨c₂, hmem c₂ hc₂A hc₂s⟩
    let u' : ↥Cp := ⟨psiEquiv e7 q, hmem _ huA hus.symm⟩
    have hodd3 : ∀ c : ↥Cp, (c : Equiv.Perm (Fin 7)) ^ 3 = 1 → c ∈ oResidual 2 ↥Cp := by
      intro c hc
      apply Subgroup.subset_closure
      show Nat.Coprime (orderOf c) 2
      have h1 : orderOf c ∣ 3 := by
        apply orderOf_dvd_of_pow_eq_one
        apply Subtype.ext
        simpa using hc
      exact Nat.Coprime.coprime_dvd_left h1 (by norm_num)
    have hu'eq : u' = c₁' * c₂' := Subtype.ext huc
    have hu'O : u' ∈ oResidual 2 ↥Cp := by
      rw [hu'eq]
      exact (oResidual 2 ↥Cp).mul_mem (hodd3 c₁' hc₁3) (hodd3 c₂' hc₂3)
    let ε := fixedEquivA7 e7 σ'
    have hu'map : u' ∈ (oResidual 2 ↥(fixedSubgroup Kb σ')).map ε.toMonoidHom := by
      rw [map_oResidual_equiv ε]
      exact hu'O
    obtain ⟨c, hcO, hcε⟩ := hu'map
    refine ⟨c, hcO, ?_⟩
    apply (psiEquiv e7).injective
    rw [psi_conj]
    have h2 : ((ε c : ↥Cp) : Equiv.Perm (Fin 7)) = psiEquiv e7 q := congrArg Subtype.val hcε
    rw [fixedEquivA7_apply] at h2
    exact h2

end A7

end CFSG.GH74.GLS.C3.Layer1.Thm1G33
