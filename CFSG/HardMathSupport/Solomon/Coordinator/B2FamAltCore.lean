module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamAltCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Proving
  Equiv Equiv.Perm Equiv.Perm.OnCycleFactors Function

namespace B2FamAlt

open B3FamAlt

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem cycle_sq_eq_one {σ : Perm Ω} (hσ : σ ^ 2 = 1) {c : Perm Ω}
    (hc : c ∈ σ.cycleFactorsFinset) : c ^ 2 = 1 ∧ sign c = -1 := by
  have hcard : c.support.card = 2 :=
    I1420.IsSubnormalQuotient.card_support_cycle Nat.prime_two hσ ⟨c, hc⟩
  have hcyc : c.IsCycle := (mem_cycleFactorsFinset_iff.1 hc).1
  refine ⟨?_, ?_⟩
  · have := pow_orderOf_eq_one c
    rwa [hcyc.orderOf, hcard] at this
  · rw [hcyc.sign, hcard]
    norm_num

theorem mul_mem_centAlt {σ : Perm Ω} (hσ : σ ^ 2 = 1) {c d : Perm Ω}
    (hc : c ∈ σ.cycleFactorsFinset) (hd : d ∈ σ.cycleFactorsFinset) : c * d ∈ centAlt σ := by
  refine mem_centAlt.2 ⟨((self_mem_cycle_factors_commute hc).mul_left
    (self_mem_cycle_factors_commute hd)).eq, ?_⟩
  rw [Perm.sign_mul, (cycle_sq_eq_one hσ hc).2, (cycle_sq_eq_one hσ hd).2]
  norm_num

theorem conj_mul_eq_of_mem_primeCore {σ : Perm Ω} (hσ : σ ^ 2 = 1) {o : Perm Ω}
    (ho : o ∈ GLAPPrimeCoreOf 2 (centAlt σ)) {c d : Perm Ω} (hc : c ∈ σ.cycleFactorsFinset)
    (hd : d ∈ σ.cycleFactorsFinset) : o * (c * d) * o⁻¹ = c * d := by
  have hoC : o ∈ centAlt σ := GLAPPrimeCoreOf_le _ ho
  have hoσ : o * σ = σ * o := (mem_centAlt.1 hoC).1
  have hc' := conj_mem_cycleFactors hoσ hc
  have hd' := conj_mem_cycleFactors hoσ hd
  have hcomm : ∀ a ∈ σ.cycleFactorsFinset, ∀ b ∈ σ.cycleFactorsFinset, Commute a b := by
    intro a ha b hb
    by_cases h : a = b
    · rw [h]
    · exact cycleFactorsFinset_mem_commute σ ha hb h
  set w := c * d * o * (c * d)⁻¹ * o⁻¹ with hwdef
  have hw : w ∈ GLAPPrimeCoreOf 2 (centAlt σ) :=
    Subgroup.mul_mem _ (GLAPPrimeCoreOf_conj_mem (c * d) (mul_mem_centAlt hσ hc hd) o ho)
      (Subgroup.inv_mem _ ho)
  have hweq : w = c * d * ((o * c * o⁻¹) * (o * d * o⁻¹))⁻¹ := by
    rw [hwdef]; group
  have hab : Commute (c * d) ((o * c * o⁻¹) * (o * d * o⁻¹)) :=
    ((hcomm c hc _ hc').mul_right (hcomm c hc _ hd')).mul_left
      ((hcomm d hd _ hc').mul_right (hcomm d hd _ hd'))
  have hsq : ∀ a ∈ σ.cycleFactorsFinset, ∀ b ∈ σ.cycleFactorsFinset, (a * b) ^ 2 = 1 := by
    intro a ha b hb
    rw [(hcomm a ha b hb).mul_pow, (cycle_sq_eq_one hσ ha).1, (cycle_sq_eq_one hσ hb).1, one_mul]
  have hw2 : w ^ 2 = 1 := by
    rw [hweq, hab.inv_right.mul_pow, hsq c hc d hd, inv_pow, hsq _ hc' _ hd', inv_one, one_mul]
  have h1 : orderOf w = 1 :=
    Nat.eq_one_of_dvd_coprimes (coprime_card_GLAPPrimeCoreOf Nat.prime_two (centAlt σ))
      (orderOf_dvd_of_pow_eq_one hw2) (Subgroup.orderOf_dvd_natCard _ hw)
  have h2 : w = 1 := orderOf_eq_one_iff.1 h1
  have h3 : c * d * o = o * (c * d) := by
    calc c * d * o = w * (o * (c * d)) := by rw [hwdef]; group
      _ = o * (c * d) := by rw [h2, one_mul]
  calc o * (c * d) * o⁻¹ = c * d * o * o⁻¹ := by rw [h3]
    _ = c * d := by group

theorem eq_or_eq_of_mul_eq {σ : Perm Ω} {c d c' d' : Perm Ω} (hc : c ∈ σ.cycleFactorsFinset)
    (hd : d ∈ σ.cycleFactorsFinset) (hc' : c' ∈ σ.cycleFactorsFinset)
    (hd' : d' ∈ σ.cycleFactorsFinset) (hcd : c ≠ d) (hcd' : c' ≠ d') (h : c' * d' = c * d) :
    c' = c ∨ c' = d := by
  have hsupp : ∀ a ∈ σ.cycleFactorsFinset, ∀ b ∈ σ.cycleFactorsFinset, a ≠ b →
      (a * b).support = a.support ∪ b.support :=
    fun a ha b hb hab => (cycleFactorsFinset_pairwise_disjoint σ ha hb hab).support_mul
  obtain ⟨y, hy⟩ := (mem_cycleFactorsFinset_iff.1 hc').1.nonempty_support
  have hy' : y ∈ (c * d).support := by
    rw [← h, hsupp c' hc' d' hd' hcd']
    exact Finset.mem_union_left _ hy
  rw [hsupp c hc d hd hcd, Finset.mem_union] at hy'
  rcases hy' with hyc | hyd
  · left
    rw [cycle_is_cycleOf hy hc', cycle_is_cycleOf hyc hc]
  · right
    rw [cycle_is_cycleOf hy hc', cycle_is_cycleOf hyd hd]

theorem commute_cycle_of_mem_primeCore {σ : Perm Ω} (hσ : σ ^ 2 = 1) {o : Perm Ω}
    (ho : o ∈ GLAPPrimeCoreOf 2 (centAlt σ)) {c : Perm Ω} (hc : c ∈ σ.cycleFactorsFinset) :
    Commute o c := by
  have hoC : o ∈ centAlt σ := GLAPPrimeCoreOf_le _ ho
  have hoσ : o * σ = σ * o := (mem_centAlt.1 hoC).1
  have hcopo : Nat.Coprime 2 (orderOf o) :=
    (coprime_card_GLAPPrimeCoreOf Nat.prime_two (centAlt σ)).coprime_dvd_right
      (Subgroup.orderOf_dvd_natCard _ ho)
  by_cases h3 : 3 ≤ σ.cycleFactorsFinset.card
  ·
    have hconj : o * c * o⁻¹ = c := by
      have h2 : 1 < (σ.cycleFactorsFinset.erase c).card := by
        rw [Finset.card_erase_of_mem hc]; omega
      obtain ⟨d₁, hd₁, d₂, hd₂, h12⟩ := Finset.one_lt_card.1 h2
      rw [Finset.mem_erase] at hd₁ hd₂
      have hc' := conj_mem_cycleFactors hoσ hc
      have key : ∀ d ∈ σ.cycleFactorsFinset, d ≠ c → o * c * o⁻¹ = c ∨ o * c * o⁻¹ = d := by
        intro d hd hdc
        have hd' := conj_mem_cycleFactors hoσ hd
        have hne : o * c * o⁻¹ ≠ o * d * o⁻¹ := by
          intro h
          apply hdc
          have := congrArg (fun x => o⁻¹ * x * o) h
          simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at this
          exact this.symm
        have heq : (o * c * o⁻¹) * (o * d * o⁻¹) = c * d := by
          rw [← conj_mul_eq_of_mem_primeCore hσ ho hc hd]
          group
        exact eq_or_eq_of_mul_eq hc hd hc' hd' (Ne.symm hdc) hne heq
      rcases key d₁ hd₁.2 hd₁.1 with h | h₁
      · exact h
      · rcases key d₂ hd₂.2 hd₂.1 with h | h₂
        · exact h
        · exact absurd (h₁.symm.trans h₂) h12
    show o * c = c * o
    calc o * c = o * c * o⁻¹ * o := by group
      _ = c * o := by rw [hconj]
  ·
    push Not at h3
    let o' : Subgroup.centralizer ({σ} : Set (Perm Ω)) :=
      ⟨o, Subgroup.mem_centralizer_singleton_iff.2 hoσ⟩
    have hdvd2 : orderOf (toPermHom σ o') ∣ 2 := by
      refine (orderOf_dvd_natCard _).trans ?_
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe]
      interval_cases σ.cycleFactorsFinset.card <;> decide
    have hdvdo : orderOf (toPermHom σ o') ∣ orderOf o := by
      have := orderOf_map_dvd (toPermHom σ) o'
      rwa [Subgroup.orderOf_mk] at this
    have h1 : toPermHom σ o' = 1 :=
      orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcopo hdvd2 hdvdo)
    exact (mem_ker_toPermHom_iff σ o').1 (MonoidHom.mem_ker.2 h1) c hc

theorem fix_of_mem_primeCore {σ : Perm Ω} (hσ : σ ^ 2 = 1) {o : Perm Ω}
    (ho : o ∈ GLAPPrimeCoreOf 2 (centAlt σ)) (x : Ω) (hx : σ x ≠ x) : o x = x := by
  have hoC : o ∈ centAlt σ := GLAPPrimeCoreOf_le _ ho
  have hcop : Nat.Coprime 2 (orderOf o) :=
    (coprime_card_GLAPPrimeCoreOf Nat.prime_two (centAlt σ)).coprime_dvd_right
      (Subgroup.orderOf_dvd_natCard _ ho)
  have hker : (⟨o, (mem_centAlt.1 hoC |>.1 |> Subgroup.mem_centralizer_singleton_iff.2)⟩ :
      Subgroup.centralizer ({σ} : Set (Perm Ω))) ∈ (toPermHom σ).ker :=
    (mem_ker_toPermHom_iff σ _).2 fun c hc => commute_cycle_of_mem_primeCore hσ ho hc
  have hrange : o ∈ (kerParam σ).range := by
    rw [kerParam_range_eq]
    exact ⟨_, hker, rfl⟩
  obtain ⟨⟨u, v⟩, huv⟩ := hrange
  have hv1 : v = 1 := by
    have hm : (u, v) ^ orderOf o = 1 := by
      apply kerParam_injective σ
      rw [map_pow, huv, map_one, pow_orderOf_eq_one]
    have hvm : v ^ orderOf o = 1 := congrArg Prod.snd hm
    have hvp : v ^ 2 = 1 := by
      funext c
      apply Subtype.ext
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (v c).2
      have hcp := (cycle_sq_eq_one hσ c.2).1
      show ((v c : Subgroup.zpowers c.val) ^ 2 : Subgroup.zpowers c.val).val = 1
      rw [Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hcp, one_zpow]
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop.symm
      (orderOf_dvd_of_pow_eq_one hvm) (orderOf_dvd_of_pow_eq_one hvp))
  subst hv1
  rw [← huv, kerParam_apply]
  have hx' : σ.cycleOf x ∈ σ.cycleFactorsFinset := by
    rw [cycleOf_mem_cycleFactorsFinset_iff, Perm.mem_support]; exact hx
  simp only [hx', dite_true]
  rfl

theorem core {σ : Perm Ω} (hσ : σ ^ 2 = 1) {J : Subgroup (Perm Ω)}
    (hJ : GLAPComponent 2 (centAlt σ) J) :
    ∀ g ∈ J, ∀ o ∈ GLAPPrimeCoreOf 2 (centAlt σ), o * g = g * o := by
  set X := centAlt σ with hX
  set O := GLAPPrimeCoreOf 2 X with hO
  have hOX : O ≤ X := GLAPPrimeCoreOf_le _
  have hJX : J ≤ X := hJ.1
  have hcopO : Nat.Coprime 2 (Nat.card O) := coprime_card_GLAPPrimeCoreOf Nat.prime_two X
  have key : (∀ o ∈ O, o = 1) ∨ ∀ g (hg : g ∈ J), rho σ ⟨g, hJX hg⟩ = 1 := by
    by_cases hf : Nat.card (Function.fixedPoints σ) ≤ 4
    · have : Group.IsSolvable (Perm (Function.fixedPoints σ)) := Equiv.Perm.isSolvable hf
      exact Or.inr (hom_eq_one_of_solvable Nat.prime_two hJ (rho σ))
    · left
      have h5 : 5 ≤ Nat.card (Function.fixedPoints σ) := by omega
      let N : Subgroup (Perm (Function.fixedPoints σ)) := (O.subgroupOf X).map (rho σ)
      have hmemN : ∀ o (ho : o ∈ O), rho σ ⟨o, hOX ho⟩ ∈ N := fun o ho => ⟨⟨o, hOX ho⟩, ho, rfl⟩
      have hofs : ∀ o (ho : o ∈ O), ofSubtype (rho σ ⟨o, hOX ho⟩) = o := by
        intro o ho
        exact ofSubtype_rho (hOX ho) (fun x hx => fix_of_mem_primeCore hσ ho x hx)
      have hNalt : N ≤ alternatingGroup (Function.fixedPoints σ) := by
        rintro _ ⟨⟨o, hoX⟩, ho, rfl⟩
        have ho' : o ∈ O := ho
        have h1 := sign_ofSubtype (rho σ ⟨o, hoX⟩)
        rw [hofs o ho'] at h1
        rw [mem_alternatingGroup, ← h1]
        exact (mem_centAlt.1 hoX).2
      have hnormN : (N.subgroupOf (alternatingGroup (Function.fixedPoints σ))).Normal := by
        refine ⟨fun n hn g => ?_⟩
        obtain ⟨⟨o, hoX⟩, ho, hon⟩ := (Subgroup.mem_subgroupOf.1 hn :
          (n : Perm (Function.fixedPoints σ)) ∈ N)
        set τ : Perm (Function.fixedPoints σ) := (g : Perm (Function.fixedPoints σ)) with hτ
        set τ' : Perm Ω := ofSubtype τ with hτ'
        have hτ'X : τ' ∈ X := mem_centAlt.2
          ⟨(disjoint_ofSubtype_of_memFixedPoints_self τ).commute.eq, by
            rw [hτ', sign_ofSubtype]; exact mem_alternatingGroup.1 g.2⟩
        have hconj : τ' * o * τ'⁻¹ ∈ O := GLAPPrimeCoreOf_conj_mem τ' hτ'X o ho
        rw [Subgroup.mem_subgroupOf]
        refine ⟨⟨τ' * o * τ'⁻¹, X.mul_mem (X.mul_mem hτ'X hoX) (X.inv_mem hτ'X)⟩, hconj, ?_⟩
        have hρτ : rho σ ⟨τ', hτ'X⟩ = τ := by
          ext ⟨x, hx⟩
          rw [rho_apply]
          exact ofSubtype_apply_of_mem τ hx
        have : rho σ (⟨τ', hτ'X⟩ * ⟨o, hoX⟩ * ⟨τ', hτ'X⟩⁻¹) = τ * n * τ⁻¹ := by
          rw [map_mul, map_mul, map_inv, hρτ, hon]
        exact this
      have : IsSimpleGroup (alternatingGroup (Function.fixedPoints σ)) :=
        alternatingGroup.isSimpleGroup h5
      have := hnormN
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (N.subgroupOf (alternatingGroup (Function.fixedPoints σ))) with hbot | htop
      · intro o ho
        have h1 : rho σ ⟨o, hOX ho⟩ = 1 := by
          have hn := hmemN o ho
          have hn' : (⟨rho σ ⟨o, hOX ho⟩, hNalt hn⟩ : alternatingGroup (Function.fixedPoints σ)) ∈
              N.subgroupOf _ := hn
          rw [hbot, Subgroup.mem_bot] at hn'
          exact congrArg Subtype.val hn'
        ext x
        by_cases hx : σ x = x
        · exact fix_of_rho_eq_one h1 x hx
        · exact fix_of_mem_primeCore hσ ho x hx
      ·
        exfalso
        have hle : alternatingGroup (Function.fixedPoints σ) ≤ N := fun a ha => by
          have : (⟨a, ha⟩ : alternatingGroup (Function.fixedPoints σ)) ∈
              N.subgroupOf (alternatingGroup (Function.fixedPoints σ)) := by rw [htop]; trivial
          exact this
        have hdvd : Nat.card (alternatingGroup (Function.fixedPoints σ)) ∣ Nat.card O := by
          calc _ ∣ Nat.card N := Subgroup.card_dvd_of_le hle
            _ ∣ Nat.card (O.subgroupOf X) := Subgroup.card_map_dvd _ _
            _ = Nat.card O := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOX).toEquiv
        have hcopA := hcopO.coprime_dvd_right hdvd
        have hnt : Nontrivial (Function.fixedPoints σ) :=
          Finite.one_lt_card_iff_nontrivial.1 (by omega)
        have hcard : Nat.card (alternatingGroup (Function.fixedPoints σ)) * 2 =
            Nat.card (Perm (Function.fixedPoints σ)) := by
          rw [← alternatingGroup.index_eq_two (α := Function.fixedPoints σ)]
          exact Subgroup.card_mul_index _
        have h4 : 4 ∣ Nat.card (Perm (Function.fixedPoints σ)) := by
          rw [Nat.card_perm]
          exact Nat.dvd_trans (by decide : 4 ∣ Nat.factorial 4)
            (Nat.factorial_dvd_factorial (by omega))
        have h2 : 2 ∣ Nat.card (alternatingGroup (Function.fixedPoints σ)) := by omega
        exact absurd (Nat.Coprime.coprime_dvd_right h2 hcopA) (by decide)
  rcases key with h | h
  · intro g hg o ho
    rw [h o ho]
    simp
  · intro g hg o ho
    have hgX := hJX hg
    exact comm_of_fix (mem_centAlt.1 hgX).1 (fun x hx => fix_of_rho_eq_one (h g hg) x hx)
      (fun x hx => fix_of_mem_primeCore hσ ho x hx)

end B2FamAlt

end CFSG.HardMathSupport.Solomon.Coordinator
