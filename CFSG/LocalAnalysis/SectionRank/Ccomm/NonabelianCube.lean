module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.SectionRank.Ccomm

open Subgroup
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [Group S] [Finite S]

theorem nonabelian_prime_cube_central_structure (hcard : Nat.card S = p ^ 3)
    (hnc : ∃ a b : S, a * b ≠ b * a) :
    commutator S = center S ∧ Nat.card (center S) = p ∧
      (∀ a b : S ⧸ center S, a * b = b * a) ∧ (∀ a : S ⧸ center S, a ^ p = 1) ∧
      Nat.card (S ⧸ center S) = p ^ 2 ∧
      (∀ T : Subgroup S, Nat.card T = p ^ 2 → center S ≤ T ∧ T.Normal ∧
        (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧ centralizer (T : Set S) = T) ∧
      (∀ α : MulAut S, (∀ x : S, x⁻¹ * α x ∈ center S) → ∃ g : S, α = MulAut.conj g) := by
  have hS : IsPGroup p S := IsPGroup.of_card hcard
  have hp1 := hp.out.one_lt
  obtain ⟨a₀, b₀, hab₀⟩ := hnc
  have hnotcomm : ¬ ∀ a b : S, a * b = b * a := fun h => hab₀ (h a₀ b₀)
  have hnt : Nontrivial S := ⟨⟨a₀ * b₀, b₀ * a₀, hab₀⟩⟩
  have hcyc : ¬ IsCyclic (S ⧸ center S) := fun _ => hnotcomm fun a b =>
    ((QuotientGroup.mk' (center S)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk'])).is_comm.comm a b
  obtain ⟨k, hk⟩ := (hS.to_subgroup (center S)).exists_card_eq
  have hcardQ : Nat.card (S ⧸ center S) * p ^ k = p ^ 3 := by
    rw [← hk, ← card_eq_card_quotient_mul_card_subgroup, hcard]
  have hk0 : k ≠ 0 := by
    have := hS.center_nontrivial
    rintro rfl
    rw [pow_zero, card_eq_one] at hk
    exact (nontrivial_iff_ne_bot _).1 this hk
  have hk3 : k ≠ 3 := by
    rintro rfl
    apply hnotcomm
    have htop : center S = ⊤ := (card_eq_iff_eq_top _).1 (hk.trans hcard.symm)
    intro a b
    exact (mem_center_iff.1 (htop ▸ mem_top b) a)
  have hk2 : k ≠ 2 := by
    rintro rfl
    have hQ : Nat.card (S ⧸ center S) = p := by
      have : p ^ 3 = p * p ^ 2 := by ring
      rw [this] at hcardQ
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos 2) hcardQ
    exact hcyc (isCyclic_of_prime_card hQ)
  have hk1 : k = 1 := by
    have hk3' : k ≤ 3 := by
      have := card_le_card_group (center S)
      rw [hk, hcard] at this
      exact (Nat.pow_le_pow_iff_right hp1).1 this
    omega
  subst hk1
  rw [pow_one] at hk
  have hQ2 : Nat.card (S ⧸ center S) = p ^ 2 := by
    have : p ^ 3 = p ^ 2 * p := by ring
    rw [this, pow_one] at hcardQ
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos hcardQ
  have hQcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ2).is_comm.comm
  have hcomZ : commutator S ≤ center S := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (center S) ⁅a, b⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hQcomm _ _
  have hcom : commutator S = center S := by
    refine eq_of_le_of_card_ge hcomZ ?_
    rw [hk]
    have hne : commutator S ≠ ⊥ := fun h => by
      have htop := (commutator_eq_bot_iff_center_eq_top S).1 h
      exact hnotcomm fun a b => mem_center_iff.1 (htop ▸ mem_top b) a
    obtain ⟨j, hj⟩ := (hS.to_subgroup (commutator S)).exists_card_eq
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at hj
      exact hne hj
    rw [hj]
    exact Nat.le_self_pow hj0 p
  have hQpow : ∀ q : S ⧸ center S, q ^ p = 1 := by
    intro q
    have hord : orderOf q ∣ p ^ 2 := hQ2 ▸ orderOf_dvd_natCard q
    obtain ⟨i, hi, hqi⟩ := (Nat.dvd_prime_pow hp.out).1 hord
    have hi2 : i ≠ 2 := by
      rintro rfl
      exact hcyc (isCyclic_of_orderOf_eq_card q (hqi.trans hQ2.symm))
    have : orderOf q ∣ p ^ 1 := hqi ▸ pow_dvd_pow p (by omega)
    rw [pow_one] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hT : ∀ T : Subgroup S, Nat.card T = p ^ 2 → center S ≤ T ∧ T.Normal ∧
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧ centralizer (T : Set S) = T := by
    intro T hT
    have hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy => congrArg Subtype.val
      ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hT).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hTidx : T.index = p := by
      have h := T.card_mul_index
      rw [hT, hcard, show p ^ 3 = p ^ 2 * p by ring] at h
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos 2) h
    have hTn : T.Normal := normal_of_index_eq_minFac_card (by
      rw [hTidx, hcard, Nat.Prime.pow_minFac hp.out (by norm_num)])
    have hZT : center S ≤ T := by
      rw [← hcom, _root_.commutator_def, commutator_le]
      intro a _ b _
      have hcardST : Nat.card (S ⧸ T) = p := by rw [← index_eq_card]; exact hTidx
      have : IsCyclic (S ⧸ T) := isCyclic_of_prime_card hcardST
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' T ⁅a, b⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact IsCyclic.isMulCommutative.is_comm.comm _ _
    have hcen : centralizer (T : Set S) = T := by
      have hTC : T ≤ centralizer (T : Set S) := fun x hx =>
        mem_centralizer_iff.2 fun y hy => hTab y hy x hx
      by_contra hne
      have hlt : T < centralizer (T : Set S) := lt_of_le_of_ne hTC (Ne.symm hne)
      obtain ⟨j, hj⟩ := (hS.to_subgroup (centralizer (T : Set S))).exists_card_eq
      have hj3 : j ≤ 3 := by
        have := card_le_card_group (centralizer (T : Set S))
        rw [hj, hcard] at this
        exact (Nat.pow_le_pow_iff_right hp1).1 this
      have hj2 : 2 < j := by
        have := card_lt_of_lt hlt
        rw [hT, hj] at this
        exact (Nat.pow_lt_pow_iff_right hp1).1 this
      have hCtop : centralizer (T : Set S) = ⊤ := by
        rw [← card_eq_iff_eq_top, hj, show j = 3 by omega, hcard]
      have hTZ : T ≤ center S := fun t ht => mem_center_iff.2 fun g =>
        (mem_centralizer_iff.1 (hCtop ▸ mem_top g) t ht).symm
      have h1 := card_le_of_le hTZ
      rw [hT, hk] at h1
      have h2 : p < p ^ 2 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 2 := Nat.pow_lt_pow_right hp1 (by norm_num)
      omega
    exact ⟨hZT, hTn, hTab, hcen⟩
  refine ⟨hcom, hk, hQcomm, hQpow, hQ2, hT, ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : S, x ∉ center S := by
    by_contra h
    push Not at h
    exact hnotcomm fun a b => mem_center_iff.1 (h b) a
  obtain ⟨y, hy⟩ : ∃ y : S, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hx (mem_center_iff.2 fun g => (h g).symm)
  have hgen : closure ({x, y} : Set S) = ⊤ := by
    set K₀ := closure ({x, y} : Set S) with hK₀
    have hxK : x ∈ K₀ := subset_closure (Set.mem_insert x _)
    have hyK : y ∈ K₀ := subset_closure (Set.mem_insert_of_mem x rfl)
    have hc : ⁅x, y⁆ ∈ center S := hcomZ (commutator_mem_commutator (mem_top x) (mem_top y))
    have hc1 : ⁅x, y⁆ ≠ 1 := fun h => hy (commutatorElement_eq_one_iff_mul_comm.1 h)
    have hZK : center S ≤ K₀ := by
      have hz : zpowers ⁅x, y⁆ = center S := by
        refine eq_of_le_of_card_ge ((zpowers_le).2 hc) ?_
        rw [hk, Nat.card_zpowers]
        have hdvd : orderOf ⁅x, y⁆ ∣ p := by
          have := Subgroup.orderOf_dvd_natCard (center S) hc
          rwa [hk] at this
        rcases (Nat.dvd_prime hp.out).1 hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hc1
        · rw [h]
      rw [← hz, zpowers_le, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxK hyK) (inv_mem hxK)) (inv_mem hyK)
    obtain ⟨j, hj⟩ := (hS.to_subgroup K₀).exists_card_eq
    have hlt : center S < K₀ := lt_of_le_of_ne hZK (fun h => hx (h ▸ hxK))
    have hj1 : 1 < j := by
      have := card_lt_of_lt hlt
      rw [hk, hj] at this
      exact (Nat.pow_lt_pow_iff_right hp1).1 (by rwa [pow_one])
    have hj3 : j ≤ 3 := by
      have := card_le_card_group K₀
      rw [hj, hcard] at this
      exact (Nat.pow_le_pow_iff_right hp1).1 this
    have hj2 : j ≠ 2 := by
      rintro rfl
      have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hj).is_comm.comm ⟨x, hxK⟩ ⟨y, hyK⟩
      exact hy (congrArg Subtype.val this)
    rw [← card_eq_iff_eq_top, hj, show j = 3 by omega, hcard]
  set A := (autQuotient (center S)).ker with hAdef
  have hA : ∀ α : MulAut S, α ∈ A ↔ ∀ s, s⁻¹ * α s ∈ center S := fun α =>
    mem_ker_autQuotient (center S)
  set Inn := (MulAut.conj : S →* MulAut S).range with hInndef
  have hInnA : Inn ≤ A := by
    rintro _ ⟨g, rfl⟩
    rw [hA]
    intro s
    have e : s⁻¹ * (MulAut.conj g) s = ⁅s⁻¹, g⁆ := by
      rw [MulAut.conj_apply, commutatorElement_def, inv_inv]
      group
    rw [e, ← hcom]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  have hInn : Nat.card Inn = p ^ 2 := by
    have hker : (MulAut.conj : S →* MulAut S).ker = center S := by
      ext g
      rw [MonoidHom.mem_ker, mem_center_iff]
      constructor
      · intro h s
        have := congrArg (fun φ : MulAut S => φ s) h
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc s * g = g * s * g⁻¹ * g := by rw [this]
          _ = g * s := by group
      · intro h
        ext s
        rw [MulAut.conj_apply, MulAut.one_apply, ← h s]
        group
    rw [← hQ2, ← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv.symm
  have hAle : Nat.card A ≤ p ^ 2 := by
    let f : A → center S × center S := fun α =>
      (⟨x⁻¹ * (α : MulAut S) x, (hA _).1 α.2 x⟩, ⟨y⁻¹ * (α : MulAut S) y, (hA _).1 α.2 y⟩)
    have hf : Function.Injective f := by
      intro α β hαβ
      have hx' : (α : MulAut S) x = (β : MulAut S) x :=
        mul_left_cancel (congrArg (fun z : center S × center S => (z.1 : S)) hαβ)
      have hy' : (α : MulAut S) y = (β : MulAut S) y :=
        mul_left_cancel (congrArg (fun z : center S × center S => (z.2 : S)) hαβ)
      apply Subtype.ext
      ext s
      have hs : s ∈ closure ({x, y} : Set S) := hgen ▸ mem_top s
      induction hs using closure_induction with
      | mem s hs =>
        rcases hs with rfl | hs
        · exact hx'
        · rw [Set.mem_singleton_iff.1 hs]
          exact hy'
      | one => rw [map_one, map_one]
      | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
      | inv a _ ha => rw [map_inv, map_inv, ha]
    calc Nat.card A ≤ Nat.card (center S × center S) := Nat.card_le_card_of_injective f hf
      _ = p ^ 2 := by rw [Nat.card_prod, hk, sq]
  have hInnEq : Inn = A := eq_of_le_of_card_ge hInnA (by rw [hInn]; exact hAle)
  intro α hα
  have hmem : α ∈ Inn := hInnEq ▸ (hA α).2 hα
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg.symm⟩

end CFSG.SectionRank.Ccomm
