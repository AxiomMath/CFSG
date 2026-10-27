module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20AltCent
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Proving
  Equiv Equiv.Perm Equiv.Perm.OnCycleFactors Function

namespace B3FamAlt

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

@[expose] def centAlt (σ : Perm Ω) : Subgroup (Perm Ω) :=
  Subgroup.centralizer ({σ} : Set (Perm Ω)) ⊓ alternatingGroup Ω

theorem mem_centAlt {σ g : Perm Ω} :
    g ∈ centAlt σ ↔ g * σ = σ * g ∧ sign g = 1 := by
  simp [centAlt, Subgroup.mem_centralizer_singleton_iff, mem_alternatingGroup]

theorem comm_apply {σ g : Perm Ω} (h : g * σ = σ * g) (x : Ω) : g (σ x) = σ (g x) :=
  congrArg (fun f : Perm Ω => f x) h

theorem cycle_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : Perm Ω} (hσ : σ ^ p = 1)
    {c : Perm Ω} (hc : c ∈ σ.cycleFactorsFinset) : c ^ p = 1 ∧ sign c = 1 := by
  have hcard : c.support.card = p :=
    I1420.IsSubnormalQuotient.card_support_cycle hp hσ ⟨c, hc⟩
  have hcyc : c.IsCycle := (mem_cycleFactorsFinset_iff.1 hc).1
  refine ⟨?_, ?_⟩
  · have := pow_orderOf_eq_one c
    rwa [hcyc.orderOf, hcard] at this
  · rw [hcyc.sign, hcard, (hp.odd_of_ne_two hp2).neg_one_pow]
    simp

theorem conj_mem_cycleFactors {σ o c : Perm Ω} (ho : o * σ = σ * o)
    (hc : c ∈ σ.cycleFactorsFinset) : o * c * o⁻¹ ∈ σ.cycleFactorsFinset := by
  have := Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset
    (g := σ) (k := o) (c := c) (Subgroup.mem_centralizer_singleton_iff.2 ho) hc
  simpa [ConjAct.toConjAct_smul] using this

theorem fix_of_mem_primeCore {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : Perm Ω} (hσ : σ ^ p = 1)
    {o : Perm Ω} (ho : o ∈ GLAPPrimeCoreOf p (centAlt σ)) (x : Ω) (hx : σ x ≠ x) : o x = x := by
  have hoC : o ∈ centAlt σ := GLAPPrimeCoreOf_le _ ho
  have hoσ : o * σ = σ * o := (mem_centAlt.1 hoC).1
  have hcop : Nat.Coprime p (orderOf o) :=
    (coprime_card_GLAPPrimeCoreOf hp (centAlt σ)).coprime_dvd_right
      (Subgroup.orderOf_dvd_natCard _ ho)
  have hcomm : ∀ c ∈ σ.cycleFactorsFinset, Commute o c := by
    intro c hc
    obtain ⟨hcp, hcs⟩ := cycle_pow_eq_one hp hp2 hσ hc
    have hcC : c ∈ centAlt σ := mem_centAlt.2
      ⟨(self_mem_cycle_factors_commute hc).eq, hcs⟩
    have hw : c * o * c⁻¹ * o⁻¹ ∈ GLAPPrimeCoreOf p (centAlt σ) :=
      Subgroup.mul_mem _ (GLAPPrimeCoreOf_conj_mem c hcC o ho) (Subgroup.inv_mem _ ho)
    have hc' := conj_mem_cycleFactors hoσ hc
    obtain ⟨hcp', -⟩ := cycle_pow_eq_one hp hp2 hσ hc'
    have hcc' : Commute c (o * c * o⁻¹) := by
      by_cases h : c = o * c * o⁻¹
      · rw [← h]
      · exact cycleFactorsFinset_mem_commute σ hc hc' h
    have hweq : c * o * c⁻¹ * o⁻¹ = c * (o * c * o⁻¹)⁻¹ := by group
    have hw1 : (c * o * c⁻¹ * o⁻¹) ^ p = 1 := by
      rw [hweq, (hcc'.inv_right).mul_pow, hcp, inv_pow, hcp', inv_one, mul_one]
    have h1 : orderOf (c * o * c⁻¹ * o⁻¹) ∣ p := orderOf_dvd_of_pow_eq_one hw1
    have h2 : orderOf (c * o * c⁻¹ * o⁻¹) ∣ Nat.card (GLAPPrimeCoreOf p (centAlt σ)) :=
      Subgroup.orderOf_dvd_natCard _ hw
    have h3 := Nat.eq_one_of_dvd_coprimes
      (coprime_card_GLAPPrimeCoreOf hp (centAlt σ) |>.symm |>.symm) h1 h2
    have h4 : c * o * c⁻¹ * o⁻¹ = 1 := orderOf_eq_one_iff.1 h3
    have h5 : c * o = o * c := by
      have := congrArg (· * (o * c)) h4
      simp only [one_mul] at this
      calc c * o = c * o * c⁻¹ * o⁻¹ * (o * c) := by group
        _ = o * c := by rw [h4, one_mul]
    exact h5.symm
  have hker : (⟨o, (mem_centAlt.1 hoC |>.1 |> Subgroup.mem_centralizer_singleton_iff.2)⟩ :
      Subgroup.centralizer ({σ} : Set (Perm Ω))) ∈ (toPermHom σ).ker :=
    (mem_ker_toPermHom_iff σ _).2 hcomm
  have hrange : o ∈ (kerParam σ).range := by
    rw [kerParam_range_eq]
    exact ⟨_, hker, rfl⟩
  obtain ⟨⟨u, v⟩, huv⟩ := hrange
  have hv1 : v = 1 := by
    have hm : (u, v) ^ orderOf o = 1 := by
      apply kerParam_injective σ
      rw [map_pow, huv, map_one, pow_orderOf_eq_one]
    have hvm : v ^ orderOf o = 1 := congrArg Prod.snd hm
    have hvp : v ^ p = 1 := by
      funext c
      apply Subtype.ext
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (v c).2
      have hcp := (cycle_pow_eq_one hp hp2 hσ c.2).1
      show ((v c : Subgroup.zpowers c.val) ^ p : Subgroup.zpowers c.val).val = 1
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

noncomputable def restrFix (σ : Perm Ω) :
    Subgroup.centralizer ({σ} : Set (Perm Ω)) →* Perm (Function.fixedPoints σ) where
  toFun g := (g : Perm Ω).subtypePerm
    (fun _ => apply_mem_fixedPoints_iff_mem_of_mem_centralizer g.2)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

noncomputable def rho (σ : Perm Ω) : ↥(centAlt σ) →* Perm (Function.fixedPoints σ) :=
  (restrFix σ).comp (Subgroup.inclusion inf_le_left)

theorem rho_apply (σ : Perm Ω) (g : ↥(centAlt σ)) (x : Function.fixedPoints σ) :
    ((rho σ g x : Function.fixedPoints σ) : Ω) = (g : Perm Ω) x := by
  simp [rho, restrFix]
  rfl

theorem fix_of_rho_eq_one {σ : Perm Ω} {g : ↥(centAlt σ)} (h : rho σ g = 1) (x : Ω)
    (hx : σ x = x) : (g : Perm Ω) x = x := by
  have := congrArg (fun f : Perm (Function.fixedPoints σ) => ((f ⟨x, hx⟩ : _) : Ω)) h
  simpa [rho_apply] using this

theorem ofSubtype_rho {σ o : Perm Ω} (hoX : o ∈ centAlt σ) (hS : ∀ x, σ x ≠ x → o x = x) :
    ofSubtype (rho σ ⟨o, hoX⟩) = o := by
  ext x
  by_cases hx : σ x = x
  · exact (ofSubtype_apply_of_mem (rho σ ⟨o, hoX⟩) hx).trans (rho_apply σ ⟨o, hoX⟩ ⟨x, hx⟩)
  · exact (ofSubtype_apply_of_not_mem (rho σ ⟨o, hoX⟩) hx).trans (hS x hx).symm

theorem comm_of_fix {σ g o : Perm Ω} (hg : g * σ = σ * g) (hgF : ∀ x, σ x = x → g x = x)
    (hoS : ∀ x, σ x ≠ x → o x = x) : o * g = g * o := by
  ext x
  by_cases hx : σ x = x
  · have hox : σ (o x) = o x := by
      by_contra hne
      have h1 := hoS _ hne
      have h2 : o x = x := o.injective h1
      exact hne (by rw [h2]; exact hx)
    simp only [Perm.mul_apply]
    rw [hgF x hx, hgF _ hox]
  · have hgx : σ (g x) ≠ g x := by
      rw [← comm_apply hg x]
      exact fun h => hx (g.injective h)
    simp only [Perm.mul_apply]
    rw [hoS x hx, hoS _ hgx]

theorem core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : Perm Ω} (hσ : σ ^ p = 1)
    {J : Subgroup (Perm Ω)} (hJ : GLAPComponent p (centAlt σ) J) :
    ∀ g ∈ J, ∀ o ∈ GLAPPrimeCoreOf p (centAlt σ), o * g = g * o := by
  set X := centAlt σ with hX
  set O := GLAPPrimeCoreOf p X with hO
  have hOX : O ≤ X := GLAPPrimeCoreOf_le _
  have hJX : J ≤ X := hJ.1
  have hcopO : Nat.Coprime p (Nat.card O) := coprime_card_GLAPPrimeCoreOf hp X
  have key : (∀ o ∈ O, o = 1) ∨ ∀ g (hg : g ∈ J), rho σ ⟨g, hJX hg⟩ = 1 := by
    by_cases hf : Nat.card (Function.fixedPoints σ) ≤ 4
    · have : Group.IsSolvable (Perm (Function.fixedPoints σ)) := Equiv.Perm.isSolvable hf
      exact Or.inr (hom_eq_one_of_solvable hp hJ (rho σ))
    · have h5 : 5 ≤ Nat.card (Function.fixedPoints σ) := by omega
      let N : Subgroup (Perm (Function.fixedPoints σ)) := (O.subgroupOf X).map (rho σ)
      have hmemN : ∀ o (ho : o ∈ O), rho σ ⟨o, hOX ho⟩ ∈ N := fun o ho => ⟨⟨o, hOX ho⟩, ho, rfl⟩
      have hofs : ∀ o (ho : o ∈ O), ofSubtype (rho σ ⟨o, hOX ho⟩) = o := by
        intro o ho
        exact ofSubtype_rho (hOX ho) (fun x hx => fix_of_mem_primeCore hp hp2 hσ ho x hx)
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
      · left
        intro o ho
        have h1 : rho σ ⟨o, hOX ho⟩ = 1 := by
          have hn := hmemN o ho
          have hn' : (⟨rho σ ⟨o, hOX ho⟩, hNalt hn⟩ : alternatingGroup (Function.fixedPoints σ)) ∈
              N.subgroupOf _ := hn
          rw [hbot, Subgroup.mem_bot] at hn'
          exact congrArg Subtype.val hn'
        ext x
        by_cases hx : σ x = x
        · exact fix_of_rho_eq_one h1 x hx
        · exact fix_of_mem_primeCore hp hp2 hσ ho x hx
      · right
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
        have hcopP : Nat.Coprime p (Nat.card (Perm (Function.fixedPoints σ))) := by
          rw [← hcard]
          exact hcopA.mul_right ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
        exact hom_eq_one_of_coprime hp hJ (rho σ) hcopP
  rcases key with h | h
  · intro g hg o ho
    rw [h o ho]
    simp
  · intro g hg o ho
    have hgX := hJX hg
    exact comm_of_fix (mem_centAlt.1 hgX).1 (fun x hx => fix_of_rho_eq_one (h g hg) x hx)
      (fun x hx => fix_of_mem_primeCore hp hp2 hσ ho x hx)

end B3FamAlt

end CFSG.HardMathSupport.Solomon.Coordinator
