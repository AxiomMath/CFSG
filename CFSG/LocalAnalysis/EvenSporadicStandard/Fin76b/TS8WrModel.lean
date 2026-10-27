module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8Wr

open Equiv Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

abbrev Pt : Type := Equiv.Perm (Fin 10 ⊕ Fin 10)

@[expose] def sw : Pt := Equiv.sumComm (Fin 10) (Fin 10)

theorem sw_mul_sw : sw * sw = 1 := by
  ext x
  rcases x with x | x <;> rfl

theorem sw_mul_sumCongr (a b : Equiv.Perm (Fin 10)) :
    sw * Equiv.Perm.sumCongr a b = Equiv.Perm.sumCongr b a * sw := by
  ext x
  rcases x with x | x <;> rfl

theorem sumCongr_one_one : Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 10)) 1 = (1 : Pt) := by
  ext x
  rcases x with x | x <;> rfl

theorem sumCongr_inv (a b : Equiv.Perm (Fin 10)) :
    (Equiv.Perm.sumCongr a b)⁻¹ = Equiv.Perm.sumCongr a⁻¹ b⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [Equiv.Perm.sumCongr_mul, mul_inv_cancel, mul_inv_cancel, sumCongr_one_one]

theorem sumCongr_sw_sumCongr (p q p' q' : Equiv.Perm (Fin 10)) :
    Equiv.Perm.sumCongr p q * sw * Equiv.Perm.sumCongr p' q' =
      Equiv.Perm.sumCongr (p * q') (q * p') * sw := by
  rw [mul_assoc, sw_mul_sumCongr, ← mul_assoc, Equiv.Perm.sumCongr_mul]

@[expose] def wrSet (M : Subgroup (Equiv.Perm (Fin 10))) : Subgroup Pt where
  carrier := {g | ∃ a ∈ M, ∃ b ∈ M,
    g = Equiv.Perm.sumCongr a b ∨ g = Equiv.Perm.sumCongr a b * sw}
  one_mem' := ⟨1, M.one_mem, 1, M.one_mem, Or.inl sumCongr_one_one.symm⟩
  mul_mem' := by
    rintro g h ⟨a, ha, b, hb, rfl | rfl⟩ ⟨a', ha', b', hb', rfl | rfl⟩
    · exact ⟨a * a', M.mul_mem ha ha', b * b', M.mul_mem hb hb',
        Or.inl (Equiv.Perm.sumCongr_mul a b a' b')⟩
    · refine ⟨a * a', M.mul_mem ha ha', b * b', M.mul_mem hb hb', Or.inr ?_⟩
      rw [← mul_assoc, Equiv.Perm.sumCongr_mul]
    · refine ⟨a * b', M.mul_mem ha hb', b * a', M.mul_mem hb ha', Or.inr ?_⟩
      exact sumCongr_sw_sumCongr a b a' b'
    · refine ⟨a * b', M.mul_mem ha hb', b * a', M.mul_mem hb ha', Or.inl ?_⟩
      rw [← mul_assoc, sumCongr_sw_sumCongr, mul_assoc, sw_mul_sw, mul_one]
  inv_mem' := by
    rintro g ⟨a, ha, b, hb, rfl | rfl⟩
    · exact ⟨a⁻¹, M.inv_mem ha, b⁻¹, M.inv_mem hb, Or.inl (sumCongr_inv a b)⟩
    · refine ⟨b⁻¹, M.inv_mem hb, a⁻¹, M.inv_mem ha, Or.inr ?_⟩
      have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right sw_mul_sw
      rw [mul_inv_rev, sumCongr_inv, hswinv, sw_mul_sumCongr]

theorem wrSet_mono {M M' : Subgroup (Equiv.Perm (Fin 10))} (h : M ≤ M') :
    wrSet M ≤ wrSet M' := by
  rintro g ⟨a, ha, b, hb, hg⟩
  exact ⟨a, h ha, b, h hb, hg⟩

noncomputable def wrPar (M : Subgroup (Equiv.Perm (Fin 10))) (p : ↥M × ↥M × Bool) : Pt :=
  Equiv.Perm.sumCongr (p.1 : Equiv.Perm (Fin 10)) (p.2.1 : Equiv.Perm (Fin 10)) *
    (if p.2.2 then sw else 1)

theorem wrPar_mem (M : Subgroup (Equiv.Perm (Fin 10))) (p : ↥M × ↥M × Bool) :
    wrPar M p ∈ wrSet M := by
  obtain ⟨a, b, e⟩ := p
  cases e
  · exact ⟨a, a.2, b, b.2, Or.inl (by simp [wrPar])⟩
  · exact ⟨a, a.2, b, b.2, Or.inr (by simp [wrPar])⟩

theorem sumCongr_inj {p q p' q' : Equiv.Perm (Fin 10)}
    (h : Equiv.Perm.sumCongr p q = Equiv.Perm.sumCongr p' q') : p = p' ∧ q = q' := by
  constructor
  · refine Equiv.ext fun x => ?_
    have := congrArg (fun g : Pt => g (Sum.inl x)) h
    simpa using this
  · refine Equiv.ext fun x => ?_
    have := congrArg (fun g : Pt => g (Sum.inr x)) h
    simpa using this

theorem wrPar_injective (M : Subgroup (Equiv.Perm (Fin 10))) :
    Function.Injective (wrPar M) := by
  rintro ⟨a, b, e⟩ ⟨a', b', e'⟩ h
  simp only [wrPar] at h
  cases e <;> cases e'
  · simp only [Bool.false_eq_true, if_false, if_true, mul_one] at h
    obtain ⟨h1, h2⟩ := sumCongr_inj h
    exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2) rfl)
  · exfalso
    simp only [Bool.false_eq_true, if_false, if_true, mul_one] at h
    have := congrArg (fun g : Pt => g (Sum.inl 0)) h
    simp [sw] at this
  · exfalso
    simp only [Bool.false_eq_true, if_false, if_true, mul_one] at h
    have := congrArg (fun g : Pt => g (Sum.inl 0)) h
    simp [sw] at this
  · simp only [if_true] at h
    have h' : Equiv.Perm.sumCongr (a : Equiv.Perm (Fin 10)) (b : Equiv.Perm (Fin 10)) =
        Equiv.Perm.sumCongr (a' : Equiv.Perm (Fin 10)) (b' : Equiv.Perm (Fin 10)) := by
      have := congrArg (· * sw) h
      simpa [mul_assoc, sw_mul_sw] using this
    obtain ⟨h1, h2⟩ := sumCongr_inj h'
    exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2) rfl)

theorem wrPar_surjective (M : Subgroup (Equiv.Perm (Fin 10))) :
    Function.Surjective (fun p : ↥M × ↥M × Bool => (⟨wrPar M p, wrPar_mem M p⟩ : wrSet M)) := by
  rintro ⟨g, a, ha, b, hb, hg⟩
  rcases hg with rfl | rfl
  · exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, false), by simp [wrPar]⟩
  · exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, true), by simp [wrPar]⟩

theorem card_wrSet (M : Subgroup (Equiv.Perm (Fin 10))) :
    Nat.card (wrSet M) = Nat.card M * Nat.card M * 2 := by
  let f : ↥M × ↥M × Bool → wrSet M := fun p => ⟨wrPar M p, wrPar_mem M p⟩
  have hf : Function.Bijective f :=
    ⟨fun p q h => wrPar_injective M (congrArg Subtype.val h), wrPar_surjective M⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  ring

abbrev Wfull : Subgroup Pt := wrSet A6Models.autA6

abbrev Sig : Subgroup Pt := wrSet P0

theorem Sig_le_Wfull : Sig ≤ Wfull := wrSet_mono P0_le_autA6

theorem card_Wfull : Nat.card Wfull = 2 ^ 11 * 2025 := by
  rw [card_wrSet, card_autA6]
  norm_num

theorem card_Sig : Nat.card Sig = 2 ^ 11 := by
  rw [card_wrSet, card_P0]
  norm_num

abbrev sigSub : Subgroup Wfull := Sig.subgroupOf Wfull

theorem card_sigSub : Nat.card sigSub = 2 ^ 11 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Sig_le_Wfull).toEquiv, card_Sig]

theorem isPGroup_sigSub : IsPGroup 2 sigSub := IsPGroup.of_card (n := 11) card_sigSub

noncomputable def sigSylow : Sylow 2 Wfull where
  toSubgroup := sigSub
  isPGroup' := isPGroup_sigSub
  is_maximal' := by
    intro Q hQ hle
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    have h1 : Nat.card Q ∣ Nat.card Wfull := Subgroup.card_subgroup_dvd_card Q
    have h2 : Nat.card sigSub ∣ Nat.card Q := Subgroup.card_dvd_of_le hle
    rw [card_Wfull] at h1
    rw [card_sigSub, hk] at h2
    have hk1 : 11 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
    have hk2 : k ≤ 11 := by
      by_contra hlt
      rw [not_le] at hlt
      rw [hk] at h1
      have h3 : 2 ^ 11 * 2 ∣ 2 ^ 11 * 2025 := by
        have : 2 ^ 12 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hlt
        rw [pow_succ] at this
        exact this.trans h1
      have h4 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h3
      norm_num at h4
    have hkeq : k = 11 := le_antisymm hk2 hk1
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hk, card_sigSub, hkeq]

theorem exists_conj_mem_sigSub {S : Subgroup Wfull} (hS : IsPGroup 2 S) :
    ∃ m : Wfull, ∀ x ∈ S, m⁻¹ * x * m ∈ sigSub := by
  obtain ⟨Q, hQ⟩ := hS.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq Wfull sigSylow Q
  refine ⟨m, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup Wfull) := hQ hx
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have heq : (MulAut.conj m)⁻¹ • x = m⁻¹ * x * m := rfl
  rw [heq] at hxQ
  exact hxQ

end CFSG.EvenSporadicStandard.Fin76b.TS8Wr
