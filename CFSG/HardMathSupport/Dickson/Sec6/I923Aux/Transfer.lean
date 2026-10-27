module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.Goldschmidt.Steps.G37Quot

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def NoL2Layer {P : Type} [Group P] (ψ : MulAut P) : Prop :=
  ∀ A : Subgroup P, GLAPComponent 3 (fixSubgroup ψ) A → ∀ r : ℕ, 10 ≤ r →
    ¬ IsTypeL2 r (barOf 3 A)

theorem typeL2_barOf_of_central {Y P : Type} [Group Y] [Finite Y] [Group P] [Finite P]
    (π : Y →* P) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    (α : MulAut Y) (ψ : MulAut P) (hαψ : ∀ y, π (α y) = ψ (π y))
    {J : Subgroup Y} (hJ : GLAPComponent 3 (fixSubgroup α) J) {r : ℕ}
    (hr : IsTypeL2 r (barOf 3 J)) :
    ∃ A : Subgroup P, GLAPComponent 3 (fixSubgroup ψ) A ∧ IsTypeL2 r (barOf 3 A) := by
  have hA := glaPComponent_map_fixSubgroup π hker α ψ hαψ hπ Nat.prime_three hJ
  refine ⟨J.map π, hA, ?_⟩
  have hJq : CFSG.Open.IsQuasisimple (barOf 3 J) :=
    isQuasisimple_barOf_of_glaPComponent Nat.prime_three hJ
  have hAq : CFSG.Open.IsQuasisimple (barOf 3 (J.map π)) :=
    isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  let φ : ↥J →* ↥(J.map π) := π.subgroupMap J
  have hφ : Function.Surjective φ := π.subgroupMap_surjective J
  let f₀ : ↥J →* barOf 3 (J.map π) := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(J.map π))).comp φ
  have hk : GLAPPrimeCore 3 ↥J ≤ f₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 (map_gLAPPrimeCore_le' 3 φ hφ ⟨x, hx, rfl⟩)
  let f : barOf 3 J →* barOf 3 (J.map π) := QuotientGroup.lift _ f₀ hk
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥(J.map π)) y
    obtain ⟨j, rfl⟩ := hφ a
    exact ⟨QuotientGroup.mk j, rfl⟩
  have hkc : f.ker ≤ Subgroup.center (barOf 3 J) := by
    have hJq' : CFSG.IsQuasisimple (barOf 3 J) :=
      ⟨Group.isPerfect_def.2 hJq.1, hJq.2, exists_not_comm_of_quasisimple hJq⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hJq' (f.normal_ker) with h | h
    · exfalso
      have hall : ∀ y : barOf 3 (J.map π), y = 1 := by
        intro y
        obtain ⟨x, rfl⟩ := hf y
        have : x ∈ f.ker := by rw [h]; exact Subgroup.mem_top x
        exact this
      have hsub : Subsingleton (barOf 3 (J.map π)) := ⟨fun a b => (hall a).trans (hall b).symm⟩
      have hs2 : Subsingleton (barOf 3 (J.map π) ⧸ Subgroup.center (barOf 3 (J.map π))) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 (J.map π)))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
    · exact h
  have hperf : Group.IsPerfect (barOf 3 J) := Group.isPerfect_def.2 hJq.1
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf f hf hkc
  obtain ⟨F, hF, hFin, hcard, ⟨g⟩⟩ := hr
  exact ⟨F, hF, hFin, hcard, ⟨e.symm.trans g⟩⟩

theorem noL2_of_descent {Y P : Type} [Group Y] [Finite Y] [Group P]
    (e : (Y ⧸ Subgroup.center Y) ≃* P) (α : MulAut Y) {ψ : MulAut P}
    (hψ : MulAut.congr e (centerDescend Y α) = ψ) (h : NoL2Layer ψ)
    {J : Subgroup Y} (hJ : GLAPComponent 3 (Lemma510Ns.fixSub α) J) {r : ℕ} (hr : 10 ≤ r) :
    ¬ IsTypeL2 r (barOf 3 J) := by
  intro hT
  have : Finite P := Finite.of_equiv (Y ⧸ Subgroup.center Y) e.toEquiv
  let π : Y →* P := (e : (Y ⧸ Subgroup.center Y) →* P).comp (QuotientGroup.mk' (Subgroup.center Y))
  have hπ : Function.Surjective π := fun p => by
    obtain ⟨q, rfl⟩ := e.surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨y, rfl⟩
  have hker : π.ker ≤ Subgroup.center Y := by
    intro y hy
    have h1 : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 :=
      e.injective (by simpa [π] using hy)
    exact (QuotientGroup.eq_one_iff y).1 h1
  have hαψ : ∀ y, π (α y) = ψ (π y) := fun y => by
    rw [← hψ]
    exact descend_compat e α y
  obtain ⟨A, hA, hAT⟩ := typeL2_barOf_of_central π hπ hker α ψ hαψ hJ hT
  exact h A hA r hr hAT

theorem center_eq_bot_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center S := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 this b).symm)

theorem isQuasisimple_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : CFSG.Open.IsQuasisimple S := by
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : ⁅a, b⁆ ∈ commutator S := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hnab)).trans
      (QuotientGroup.quotientBot (G := S))).isSimpleGroup

theorem noL2_of_simple_fixed {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (hs : IsSimpleGroup ↥(fixSubgroup ψ)) (hnab : ∃ a b : ↥(fixSubgroup ψ), a * b ≠ b * a)
    (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r ↥(fixSubgroup ψ)) : NoL2Layer ψ := by
  intro A hA r hr hT
  have hq : CFSG.Open.IsQuasisimple ↥(fixSubgroup ψ) := isQuasisimple_of_simple hnab
  have hAD : A = fixSubgroup ψ :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hq hA.2.1 (glaPComponent_perfect hA)
      (glaPComponent_ne_bot hA)
  have hAq := isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  subst hAD
  generalize fixSubgroup ψ = D at *
  have hcore : GLAPPrimeCore 3 ↥D = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥D) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (barOf 3 D) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            rw [h]
            exact Subgroup.mem_top _
      have hs2 : Subsingleton (barOf 3 D ⧸ Subgroup.center (barOf 3 D)) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 D))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
  have e : barOf 3 D ≃* ↥D :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientBot (G := ↥D))
  exact hL2 r hr (l2fld_isTypeL2_of_mulEquiv e hT)

theorem noL2_of_simple_commutator_fixed {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (S : Subgroup P) (hSD : S = ⁅fixSubgroup ψ, fixSubgroup ψ⁆) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r ↥S) :
    NoL2Layer ψ := by
  intro A hA r hr hT
  have hq : CFSG.Open.IsQuasisimple ↥S := isQuasisimple_of_simple hnab
  have hAD : A ≤ fixSubgroup ψ := hA.1
  have hAS : A ≤ S := by
    have hperf := glaPComponent_perfect hA
    calc A = ⁅A, A⁆ := hperf.symm
      _ ≤ ⁅fixSubgroup ψ, fixSubgroup ψ⁆ := Subgroup.commutator_mono hAD hAD
      _ = S := hSD.symm
  have hSDle : S ≤ fixSubgroup ψ := by
    rw [hSD]
    exact Subgroup.commutator_le.2 fun a ha b hb =>
      (fixSubgroup ψ).mul_mem ((fixSubgroup ψ).mul_mem ((fixSubgroup ψ).mul_mem ha hb)
        ((fixSubgroup ψ).inv_mem ha)) ((fixSubgroup ψ).inv_mem hb)
  have hsn : IsSubnormal A S := isSubnormal_of_le_of_le hA.2.1 hAS hSDle
  have hAeq : A = S :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hq hsn (glaPComponent_perfect hA)
      (glaPComponent_ne_bot hA)
  have hAq := isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  subst hAeq
  have hcore : GLAPPrimeCore 3 ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥A) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (barOf 3 A) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            rw [h]
            exact Subgroup.mem_top _
      have hs2 : Subsingleton (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 A))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
  have e : barOf 3 A ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientBot (G := ↥A))
  exact hL2 r hr (l2fld_isTypeL2_of_mulEquiv e hT)

theorem noL2_of_not_three_dvd_fixed {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (h3 : ¬ 3 ∣ Nat.card ↥(fixSubgroup ψ)) : NoL2Layer ψ := by
  intro A hA r hr hT
  have hAq := isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  have hAD : A ≤ fixSubgroup ψ := hA.1
  have hcop : Nat.Coprime 3 (Nat.card ↥A) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd => h3 ?_
    exact hd.trans (Subgroup.card_dvd_of_le hAD)
  have h : GLAPPrimeCore 3 ↥A = ⊤ := by
    refine top_le_iff.1 (le_sSup ?_)
    exact ⟨Subgroup.normal_top, by rw [Subgroup.card_top]; exact hcop⟩
  have hsub : Subsingleton (barOf 3 A) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [QuotientGroup.eq]
        rw [h]
        exact Subgroup.mem_top _
  have hs2 : Subsingleton (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) :=
    (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 A))).subsingleton
  exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial

end CFSG.HardMathSupport.Dickson.Sec6.I923
