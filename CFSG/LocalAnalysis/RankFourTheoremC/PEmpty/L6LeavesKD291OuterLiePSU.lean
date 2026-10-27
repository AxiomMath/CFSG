module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTransfer
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSU)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator

theorem psu_pRank_fixed {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSU n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) (hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2)) (α : MulAut K)
    (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    p ∣ f ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = (ℓ ^ (f / p)) ^ 2 ∧
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ (f / p)) F₀))) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
  classical
  obtain ⟨⟨hℓ, hf, hn, hne⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hne' : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have h : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) F) := isPrimeFormGram_one
  have hdiv' : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := hdiv
  obtain ⟨θ⟩ : Nonempty (K ≃* primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    ⟨(e.trans (unitaryPSUEquiv h (by omega)).symm).trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization h hC1 hn hne').1).symm⟩
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ inner (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  set σ := primeFormFieldFactor h hC1 hn hne' β with hσdef
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hβp, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    have hD : β ∈ primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [← ker_primeFormFieldFactor h hC1 hn hne']
      exact hσ1
    exact hβout (mem_inner_of_mem_primeFormD h hn hne' hp hdiv' hD hβp)
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hne' hp hp2 β hβord σ hσdef.symm hσord
  set u := primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) M with hu
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hfσ
  have hβu : β * u = u * fσ := by
    rw [← hM]
    group
  have hZ' : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hdiv'
  obtain ⟨hpf, hcard, -, -, -, hinj, hrange, -, -, -, -⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσord n hn hne' hZ'
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσord with hh₀
  refine ⟨hpf, fixSubfield σ, inferInstance, Subtype.finite, hcard, ?_⟩
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (primeFormP h₀
      ((1 : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)))) ≤
      CFSG.Open.pRank p (fixedSubgroup fσ) :=
    pRank_top_le_pRank_fixed_of_embedding hp1 (primeSubfieldPSU h hp hp2 hσord n) hinj fσ
      fun a => by
        have : primeSubfieldPSU h hp hp2 hσord n a ∈ fieldFixedPSU h n σ := by
          rw [← hrange]; exact ⟨a, rfl⟩
        exact this
  have h2 : CFSG.Open.pRank p (fixedSubgroup fσ) ≤ CFSG.Open.pRank p (fixedSubgroup β) :=
    pRank_fixed_le_of_intertwine hp1 (u : MulAut _).symm β fσ fun x => by
      have := congrArg (fun g : MulAut _ => g ((u : MulAut _).symm x)) hβu
      simp only [MulAut.mul_apply, MulEquiv.apply_symm_apply] at this
      rw [this]
      simp
  have h3 : CFSG.Open.pRank p (fixedSubgroup β) ≤ CFSG.Open.pRank p (fixedSubgroup α) :=
    pRank_fixed_le_of_intertwine hp1 θ α β fun x => by
      rw [hβdef]
      simp [MulAut.congr_apply]
  have hn1 : 1 ≤ n := by omega
  obtain ⟨θ₀⟩ : Nonempty (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) ≃* StatedProj (StatedSU n (ℓ ^ (f / p))
        (fixSubfield σ))) :=
    ⟨(Classical.choice (unitary_prime_form_full_semilinear_realization h₀ isPrimeFormGram_one
      hn hq₀).1).trans (unitaryPSUEquiv h₀ hn1)⟩
  have h4 : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ (f / p))
      (fixSubfield σ)))) = CFSG.Open.pRank p (⊤ : Subgroup (primeFormP h₀
        ((1 : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)))) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 θ₀).symm
  omega

theorem two_le_pRank_statedProj_PSU {p n f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 3 ≤ n)
    (hf₀ : 1 ≤ f₀) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = (p ^ f₀) ^ 2) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n (p ^ f₀) F₀))) := by
  have hq5 : 5 ≤ p ^ f₀ := le_trans hp5 (Nat.le_self_pow (by omega) p)
  have hm : StatedClassicalModel (StatedProj (StatedSU n (p ^ f₀) F₀)) .PSU n p f₀ := by
    refine ⟨⟨hp, hf₀, hn, fun h => ?_⟩, F₀, inferInstance, inferInstance, hF₀,
      ⟨MulEquiv.refl _⟩⟩
    exact absurd ((Prod.mk.inj h).2 ▸ hq5) (by norm_num)
  obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by omega) hm
  rcases hcases with ⟨ht, -⟩ | ⟨-, h1 | h1⟩ | ⟨ht, -⟩ | h1
  · exact absurd ht (by decide)
  · omega
  · omega
  · exact absurd ht (by decide)
  · omega

theorem outerFixedRankDefAt_PSU : OuterFixedRankDefAt .PSU := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  have hcl : StatedClassicalModel K .PSU n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨-, hf, hn3, -⟩ := hadm
  have hdiv : ¬ ℓ ∣ Nat.gcd n (ℓ ^ f + 1) := by
    intro h
    have h1 : ℓ ∣ ℓ ^ f + 1 := h.trans (Nat.gcd_dvd_right _ _)
    have h2 : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h1))
  have hq₀ : ¬(n = 3 ∧ ℓ ^ (f / ℓ) = 2) := by
    rintro ⟨-, h2⟩
    rcases Nat.eq_zero_or_pos (f / ℓ) with h0 | h0
    · rw [h0, pow_zero] at h2
      omega
    · have : 5 ≤ ℓ ^ (f / ℓ) := le_trans hp5 (Nat.le_self_pow (by omega) ℓ)
      omega
  obtain ⟨hpf, F₀, _, _, hcard, hrank⟩ := psu_pRank_fixed hcl hp (by omega) hdiv hq₀ α hαp hαin
  have hf0 : 1 ≤ f / ℓ := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have := two_le_pRank_statedProj_PSU hp hp5 hn3 hf0 hcard
  exact Or.inl (by omega)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
