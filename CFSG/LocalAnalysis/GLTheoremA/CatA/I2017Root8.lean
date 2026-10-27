module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017Alt7
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownPerm
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open Equiv Equiv.Perm Finset
open scoped commutatorElement

theorem pow_transport_apply {Q A : Type*} [Group Q] [Group A] (e : Q ≃* A) (α : MulAut Q) (k : ℕ)
    (x : A) : (((e.symm.trans α).trans e : MulAut A) ^ k) x = e ((α ^ k) (e.symm x)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply]
    simp

theorem root8_aux {n : ℕ} {β : MulAut ↥(alternatingGroup (Fin n))} (hβ : β ^ 3 = 1)
    {J₂ : Subgroup ↥(alternatingGroup (Fin n))} (hJ₂ : GLAPComponent 3 (fixSubgroup β) J₂)
    (hJ8 : IsAltPType 3 J₂ 8) :
    ∃ s : Finset (Fin n), s.card = 8 ∧ J₂ = (alternatingGroup.ofSubtype s).range := by
  classical
  haveI : Nontrivial ↥J₂ := AltDown.nontrivial_of_glaPComponent Nat.prime_three hJ₂
  haveI : Group.IsPerfect ↥J₂ := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ₂)
  have hne : J₂ ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J₂).1 inferInstance
  have hcardJ : ∀ (m : ℕ), (↥J₂ ≃* ↥(alternatingGroup (Fin m))) → 5 ≤ m → m = 8 := by
    intro m f hm5
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin m)) :=
      alternatingGroup.isSimpleGroup (by simpa using hm5)
    obtain ⟨g⟩ := AltDown.nonempty_pSimple_equiv Nat.prime_three hJ₂
      (alternatingGroup.center_eq_bot (by simp; omega)) f
    obtain ⟨h8⟩ := hJ8
    have hZ8 : Subgroup.center ↥(alternatingGroup (Fin 8)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    have g8 : PSimple 3 J₂ ≃* ↥(alternatingGroup (Fin 8)) :=
      (QuotientGroup.congr (Subgroup.center (PQuot 3 J₂)) (Subgroup.center ↥(alternatingGroup (Fin 8)))
        h8 (Subgroup.map_center_eq h8)).trans
        ((QuotientGroup.quotientMulEquivOfEq hZ8).trans QuotientGroup.quotientBot)
    have hc := Nat.card_congr (g.symm.trans g8).toEquiv
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_fin, Nat.card_fin] at hc
    have hm2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h82 : 2 ∣ (8 : ℕ).factorial := Nat.dvd_factorial (by norm_num) (by norm_num)
    have hf : m.factorial = (8 : ℕ).factorial := (Nat.div_left_inj hm2 h82).1 hc
    exact (Nat.factorial_inj (by omega)).1 hf
  have h24 : ∀ (H : Subgroup ↥(alternatingGroup (Fin n))) (m : ℕ),
      (↥H ≃* ↥(alternatingGroup (Fin m))) → J₂ ≤ H → 5 ≤ m := by
    intro H m f hJH
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card ↥J₂ ∣ 24 := by
      refine (Subgroup.card_dvd_of_le hJH).trans ?_
      rw [Nat.card_congr f.toEquiv]
      refine (AltDown.natCard_alternatingGroup_dvd_factorial (Fin m)).trans ?_
      simpa using AltDown.factorial_dvd_twentyFour hlt
    exact AltDown.false_of_isPerfect_of_card_dvd_twentyFour h1
  have hn5 : 5 ≤ n := h24 ⊤ n Subgroup.topEquiv le_top
  by_cases hβ1 : β = 1
  · subst hβ1
    have htop : fixSubgroup (1 : MulAut ↥(alternatingGroup (Fin n))) = ⊤ := by
      ext x
      simp [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    rw [htop] at hJ₂
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn5)
    haveI : IsSimpleGroup ↥(⊤ : Subgroup ↥(alternatingGroup (Fin n))) :=
      Subgroup.topEquiv.isSimpleGroup
    have hJtop : J₂ = ⊤ := AltDown.eq_of_isSubnormal_of_isSimpleGroup hJ₂.2.1 hne
    have hn8 : n = 8 := hcardJ n ((MulEquiv.subgroupCongr hJtop).trans Subgroup.topEquiv) hn5
    refine ⟨Finset.univ, by simp [hn8], ?_⟩
    rw [hJtop, eq_comm, eq_top_iff]
    intro k _
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    exact Finset.subset_univ _
  · obtain ⟨x, -, hx3, rfl⟩ := AltDown.exists_conj_of_alt hn5 Nat.prime_three (by norm_num) hβ hβ1
    have hJF := AltDown.le_range_ofSubtype_of_glaPComponent Nat.prime_three (by norm_num) hx3 hJ₂
    set s : Finset (Fin n) := ((x : Equiv.Perm (Fin n)).support)ᶜ with hs
    obtain ⟨eF⟩ := AltDown.nonempty_range_ofSubtype_equiv s s.card rfl
    have hm5 : 5 ≤ s.card := h24 _ s.card eF hJF
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin s.card)) :=
      alternatingGroup.isSimpleGroup (by simpa using hm5)
    haveI : IsSimpleGroup ↥(alternatingGroup.ofSubtype s).range := eF.isSimpleGroup
    have hFC : (alternatingGroup.ofSubtype s).range ≤ fixSubgroup (MulAut.conj x) := fun k hk =>
      AltDown.mem_fixSubgroup_conj.2 (Subtype.ext (AltDown.commute_of_mem_range_ofSubtype_compl hk).eq)
    have hJeq := AltDown.eq_of_isSubnormal_of_isSimpleGroup
      (glaPComponent_of_le Nat.prime_three hJ₂ hJF hFC).2.1 hne
    exact ⟨s, hcardJ s.card ((MulEquiv.subgroupCongr hJeq).trans eF) hm5, hJeq⟩

theorem root8_of_fix_component {Q : Type} [Group Q] [Finite Q] {n : ℕ}
    (e : Q ≃* ↥(alternatingGroup (Fin n))) {α : MulAut Q} (hα : α ^ 3 = 1) {J₁ : Subgroup Q}
    (hJ₁ : GLAPComponent 3 (fixSubgroup α) J₁) (hJ8 : IsAltPType 3 J₁ 8) : IsRootAlt e J₁ 8 := by
  classical
  set β : MulAut ↥(alternatingGroup (Fin n)) := (e.symm.trans α).trans e with hβdef
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun x => ?_
    rw [pow_transport_apply e α 3 x, hα, MulAut.one_apply, MulAut.one_apply, e.apply_symm_apply]
  have hfix : (fixSubgroup α).map e.toMonoidHom = fixSubgroup β := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : α x = x := hx
      show β (e x) = e x
      rw [hβdef, MulEquiv.trans_apply, MulEquiv.trans_apply, e.symm_apply_apply, hx']
    · intro hy
      have hy' : β y = y := hy
      refine ⟨e.symm y, ?_, by simp⟩
      show α (e.symm y) = e.symm y
      have h1 : e (α (e.symm y)) = y := hy'
      calc α (e.symm y) = e.symm (e (α (e.symm y))) := (e.symm_apply_apply _).symm
        _ = e.symm y := by rw [h1]
  have hkerbot : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  have hker : Nat.Coprime 3 (Nat.card ↥(fixSubgroup α ⊓ e.toMonoidHom.ker)) := by
    rw [hkerbot, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hJ₂ : GLAPComponent 3 (fixSubgroup β) (J₁.map e.toMonoidHom) := by
    rw [← hfix]
    exact glaPComponent_map Nat.prime_three e.toMonoidHom hker hJ₁
  have hJ8' : IsAltPType 3 (J₁.map e.toMonoidHom) 8 := by
    obtain ⟨f⟩ := nonempty_pQuot_equiv_map Nat.prime_three (ψ := e.toMonoidHom)
      (by rw [hkerbot, Subgroup.card_bot]; norm_num) J₁
    obtain ⟨g⟩ := hJ8
    exact ⟨f.symm.trans g⟩
  obtain ⟨s, hs8, hJs⟩ := root8_aux hβ3 hJ₂ hJ8'
  refine ⟨?_, ?_⟩
  · obtain ⟨eF⟩ := AltDown.nonempty_range_ofSubtype_equiv s 8 hs8
    exact ⟨((Subgroup.equivMapOfInjective J₁ e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hJs)).trans eF⟩
  · have hmov : movedLettersOf e J₁ = (s : Set (Fin n)) := by
      ext i
      constructor
      · rintro ⟨h, hh, hhi⟩
        have hmem : e h ∈ (alternatingGroup.ofSubtype s).range := hJs ▸ ⟨h, hh, rfl⟩
        rw [alternatingGroup.mem_range_ofSubtype_iff] at hmem
        exact hmem (Equiv.Perm.mem_support.2 hhi)
      · intro hi
        have hi' : i ∈ s := hi
        have h7 : (s.erase i).card = 7 := by rw [Finset.card_erase_of_mem hi', hs8]
        obtain ⟨v, hv⟩ : (s.erase i).Nonempty := Finset.card_pos.1 (by omega)
        have h6 : ((s.erase i).erase v).card = 6 := by rw [Finset.card_erase_of_mem hv, h7]
        obtain ⟨w, hw⟩ : ((s.erase i).erase v).Nonempty := Finset.card_pos.1 (by omega)
        obtain ⟨hwv, hw'⟩ := Finset.mem_erase.1 hw
        obtain ⟨hwi, hws⟩ := Finset.mem_erase.1 hw'
        obtain ⟨hvi, hvs⟩ := Finset.mem_erase.1 hv
        set σ : Equiv.Perm (Fin n) := Equiv.swap i v * Equiv.swap v w with hσdef
        have hσ : σ ∈ alternatingGroup (Fin n) := by
          rw [Equiv.Perm.mem_alternatingGroup, hσdef, Equiv.Perm.sign_mul,
            Equiv.Perm.sign_swap (Ne.symm hvi), Equiv.Perm.sign_swap (Ne.symm hwv)]
          simp
        have hσs : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin n))) ∈ (alternatingGroup.ofSubtype s).range := by
          rw [alternatingGroup.mem_range_ofSubtype_iff]
          intro u hu
          have hu' := Equiv.Perm.support_mul_le _ _ hu
          rw [Equiv.Perm.support_swap (Ne.symm hvi), Equiv.Perm.support_swap (Ne.symm hwv)] at hu'
          simp only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton] at hu'
          rcases hu' with (rfl | rfl) | (rfl | rfl) <;> assumption
        rw [← hJs] at hσs
        obtain ⟨h, hh, hhe⟩ := hσs
        refine ⟨h, hh, ?_⟩
        have hσe : ((e h : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) = σ :=
          congrArg Subtype.val hhe
        rw [hσe, hσdef, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hvi) (Ne.symm hwi),
          Equiv.swap_apply_left]
        exact hvi
    rw [MovesExactly, hmov, Set.ncard_coe_finset, hs8]


theorem root7_of_le_root8 {Q : Type} [Group Q] [Finite Q] {n : ℕ}
    (e : Q ≃* ↥(alternatingGroup (Fin n))) {J₁ I : Subgroup Q} (hJ : IsRootAlt e J₁ 8)
    (hIJ : I ≤ J₁) (hI : Nonempty (↥I ≃* ↥(alternatingGroup (Fin 7)))) : IsRootAlt e I 7 := by
  classical
  obtain ⟨-, hmov⟩ := hJ
  set s : Finset (Fin n) := (Set.toFinite (movedLettersOf e J₁)).toFinset with hsdef
  have hs : #s = 8 := by
    rw [hsdef, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    exact hmov
  have hmemS : ∀ i, i ∈ s ↔ i ∈ movedLettersOf e J₁ := fun i => Set.Finite.mem_toFinset _
  set H : Subgroup ↥(alternatingGroup (Fin n)) := I.map e.toMonoidHom with hHdef
  have hHs : ∀ h ∈ H, ∀ i ∉ s, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) i = i := by
    rintro _ ⟨k, hk, rfl⟩ i hi
    by_contra hne
    exact hi ((hmemS i).2 ⟨k, hIJ hk, hne⟩)
  have hH : Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7))) := by
    obtain ⟨eI⟩ := hI
    exact ⟨(Subgroup.equivMapOfInjective I e.toMonoidHom e.injective).symm.trans eI⟩
  obtain ⟨i₀, hi₀s, hfix⟩ := i2017_exists_fixed_alt7 hs hHs hH
  set t : Finset (Fin n) := s.erase i₀ with htdef
  have ht : #t = 7 := by
    rw [htdef, Finset.card_erase_of_mem hi₀s, hs]
  have hHt : ∀ h ∈ H, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)).support ⊆ t := by
    intro h hh i hi
    have his : i ∈ s := by
      by_contra his
      exact (Equiv.Perm.mem_support.1 hi) (hHs h hh i his)
    refine Finset.mem_erase.2 ⟨?_, his⟩
    rintro rfl
    exact (Equiv.Perm.mem_support.1 hi) (hfix h hh)
  set A : Subgroup ↥(alternatingGroup (Fin n)) := (alternatingGroup.ofSubtype t).range with hAdef
  have hHA : H ≤ A := fun h hh => (alternatingGroup.mem_range_ofSubtype_iff t h).2 (hHt h hh)
  have hAcard : Nat.card ↥A = 2520 := by
    obtain ⟨eA⟩ := AltDown.nonempty_range_ofSubtype_equiv t 7 ht
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hHcard : Nat.card ↥H = 2520 := by
    obtain ⟨eI⟩ := hI
    have h1 := Nat.card_congr (Subgroup.equivMapOfInjective I e.toMonoidHom e.injective).toEquiv
    have h2 := Nat.card_congr eI.toEquiv
    have h3 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup]
      simp [Nat.factorial]
    show Nat.card ↥(I.map e.toMonoidHom) = 2520
    omega
  have hHeqA : H = A := Subgroup.eq_of_le_of_card_ge hHA (by rw [hAcard, hHcard])
  have hmov' : movedLettersOf e I = (t : Set (Fin n)) := by
    ext i
    constructor
    · rintro ⟨k, hk, hki⟩
      have his : i ∈ s := (hmemS i).2 ⟨k, hIJ hk, hki⟩
      have hi0 : i ≠ i₀ := by
        rintro rfl
        exact hki (hfix _ ⟨k, hk, rfl⟩)
      exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hi0, his⟩)
    · intro hi
      obtain ⟨hi0, his⟩ := Finset.mem_erase.1 (Finset.mem_coe.1 hi)
      have hti : i ∈ t := Finset.mem_coe.1 hi
      obtain ⟨v, hv⟩ : (t.erase i).Nonempty := Finset.card_pos.1 (by
        rw [Finset.card_erase_of_mem hti, ht]; norm_num)
      have hcard6 : ((t.erase i).erase v).card = 5 := by
        rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem hti, ht]
      obtain ⟨w, hw⟩ : ((t.erase i).erase v).Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨hwv, hw'⟩ := Finset.mem_erase.1 hw
      obtain ⟨hwi, hws⟩ := Finset.mem_erase.1 hw'
      obtain ⟨hvi, hvt⟩ := Finset.mem_erase.1 hv
      set σ : Equiv.Perm (Fin n) := Equiv.swap i v * Equiv.swap v w with hσdef
      have hσ : σ ∈ alternatingGroup (Fin n) := by
        rw [Equiv.Perm.mem_alternatingGroup, hσdef, Equiv.Perm.sign_mul,
          Equiv.Perm.sign_swap (Ne.symm hvi), Equiv.Perm.sign_swap (Ne.symm hwv)]
        simp
      have hσt : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin n))) ∈ A := by
        rw [hAdef, alternatingGroup.mem_range_ofSubtype_iff]
        intro u hu
        have hu' := Equiv.Perm.support_mul_le _ _ hu
        rw [Equiv.Perm.support_swap (Ne.symm hvi), Equiv.Perm.support_swap (Ne.symm hwv)] at hu'
        simp only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton] at hu'
        rcases hu' with (rfl | rfl) | (rfl | rfl) <;> assumption
      rw [← hHeqA] at hσt
      obtain ⟨k, hk, hkσ⟩ := Subgroup.mem_map.1 hσt
      refine ⟨k, hk, ?_⟩
      have hσe : ((e k : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) = σ :=
        congrArg Subtype.val hkσ
      rw [hσe, hσdef, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hvi) (Ne.symm hwi),
        Equiv.swap_apply_left]
      exact hvi
  refine ⟨hI, ?_⟩
  unfold MovesExactly
  rw [hmov', Set.ncard_coe_finset, ht]

end CFSG.LocalAnalysis.GLTheoremA.I2017
