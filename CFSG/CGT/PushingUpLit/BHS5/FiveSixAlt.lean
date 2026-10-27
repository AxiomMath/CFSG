module

public import CFSG.CGT.PushingUpLit.BHS5.SLFixed
public import CFSG.CGT.PushingUpLit.BHS5.SymGlue

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_fixed_commV_of_inf_bot (hV : ∀ v : V, v ^ 2 = 1) {E₀ T₁ : Subgroup (MulAut V)}
    (hbot : commV E₀ ⊓ fixV E₀ = ⊥) (hne : E₀ ≠ ⊥) (hT₁ : IsPGroup 2 ↥T₁)
    (hT₁N : ∀ t ∈ T₁, ∀ x ∈ E₀, t * x * t⁻¹ ∈ E₀) :
    ∃ u ∈ commV E₀, u ∈ fixV T₁ ∧ u ∉ fixV E₀ := by
  have hcomm : commV E₀ ≠ ⊥ := by
    intro h
    apply hne
    rw [commV_eq_commSub, commSub_eq_bot_iff] at h
    refine (Subgroup.eq_bot_iff_forall E₀).2 fun x hx => MulEquiv.ext fun v => ?_
    exact h (Subgroup.mem_top v) x hx
  have hinv : ∀ t ∈ T₁, ∀ m ∈ commV E₀, t m ∈ commV E₀ := by
    intro t ht m hm
    rw [commV_eq_commSub] at hm ⊢
    exact map_commSub_mem (D := ⊤) (X := E₀) (b := t) (hT₁N t ht) (fun _ _ => trivial) m hm
  obtain ⟨m, hm, hm1, hmfix⟩ := B1.exists_fixed_ne_one hV hT₁ hinv hcomm
  refine ⟨m, hm, hmfix, fun hmE => hm1 ?_⟩
  have : m ∈ commV E₀ ⊓ fixV E₀ := ⟨hm, hmE⟩
  rwa [hbot, Subgroup.mem_bot] at this

theorem exists_fixed_commV_odd (hV : ∀ v : V, v ^ 2 = 1) {E₀ T₁ : Subgroup (MulAut V)}
    (hodd : Odd (Nat.card E₀)) (hne : E₀ ≠ ⊥) (hT₁ : IsPGroup 2 ↥T₁)
    (hT₁N : ∀ t ∈ T₁, ∀ x ∈ E₀, t * x * t⁻¹ ∈ E₀) :
    ∃ u ∈ commV E₀, u ∈ fixV T₁ ∧ u ∉ fixV E₀ := by
  have h := (B1.coprime_decomp hV hodd (M := ⊤) (fun _ _ _ _ => trivial)).2
  refine exists_fixed_commV_of_inf_bot hV ?_ hne hT₁ hT₁N
  rw [commV_eq_commSub, inf_comm]
  simpa using h

theorem exists_fixed_commV_alt (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 2 ≤ m)
    {G E₀ A T₁ : Subgroup (MulAut V)} (hEG : E₀ ≤ G) (hsub : CFSG.Open.IsSubnormal E₀ G)
    (hAG : A ≤ G) (hA : IsOff A)
    (hnat : IsAltNatSection E₀ (commV E₀) (commV E₀ ⊓ fixV E₀) (2 * m + 1))
    (hEA : ⁅E₀, A⁆ ≠ ⊥) (hT₁ : IsPGroup 2 ↥T₁)
    (hT₁N : ∀ t ∈ T₁, ∀ x ∈ E₀, t * x * t⁻¹ ∈ E₀) :
    ∃ u ∈ commV E₀, u ∈ fixV T₁ ∧ u ∉ fixV E₀ := by
  have hbot := (two_sixteen_alt hV hm hA hAG hEG hsub hnat hEA).2.1
  have hne : E₀ ≠ ⊥ := by
    rintro rfl
    apply hEA
    simp
  exact exists_fixed_commV_of_inf_bot hV hbot hne hT₁ hT₁N

omit [Finite V] in
theorem altOf_eq_opResidual {E : Subgroup (MulAut V)} {m : ℕ} (θ : ↥E ≃* Equiv.Perm (Fin m)) :
    altOf θ = opResidual 2 E := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxE, hxA⟩ := (mem_altOf θ).1 hx
    have hxA' : θ ⟨x, hxE⟩ ∈ Subgroup.closure {σ : Equiv.Perm (Fin m) | σ.IsThreeCycle} := by
      rw [Equiv.Perm.closure_three_cycles_eq_alternating]
      exact hxA
    have key : ∀ σ ∈ Subgroup.closure {σ : Equiv.Perm (Fin m) | σ.IsThreeCycle},
        ((θ.symm σ : ↥E) : MulAut V) ∈ opResidual 2 E := by
      intro σ hσ
      induction hσ using Subgroup.closure_induction with
      | mem σ hσ =>
        refine mem_opResidual_of_coprime (θ.symm σ).2 ?_
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hσ.orderOf]
        decide
      | one => simp
      | mul a b _ _ ha hb => simpa using (opResidual 2 E).mul_mem ha hb
      | inv a _ ha => simpa using (opResidual 2 E).inv_mem ha
    have := key _ hxA'
    simpa using this
  · refine opResidual_le_of_three_cycles θ fun σ hσ => ?_
    exact (mem_altOf θ).2 ⟨(θ.symm σ).2, by simpa using hσ.mem_alternatingGroup⟩

omit [Finite V] in
theorem opResidual_conjSub {Γ : Type*} [Group Γ] (g : Γ) (X : Subgroup Γ) :
    opResidual 2 (conjSub g X) = conjSub g (opResidual 2 X) := by
  have key : ∀ (g : Γ) (X : Subgroup Γ),
      conjSub g (opResidual 2 X) ≤ opResidual 2 (conjSub g X) := by
    intro g X
    rw [conjSub, opResidual, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro x ⟨hxX, hxo⟩
    refine mem_opResidual_of_coprime (mem_conjSub_of_mem hxX) ?_
    have := MulEquiv.orderOf_eq (MulAut.conj g) x
    show (orderOf ((MulAut.conj g) x)).Coprime 2
    rw [this]
    exact hxo
  apply le_antisymm
  · have h1 := key g⁻¹ (conjSub g X)
    have e1 : conjSub g⁻¹ (conjSub g X) = X := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    rw [e1] at h1
    have h2 := conjSub_mono g h1
    have e2 : conjSub g (conjSub g⁻¹ (opResidual 2 (conjSub g X))) =
        opResidual 2 (conjSub g X) := by
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    rwa [e2] at h2
  · exact key g X

end CFSG.CGT.PushingUpLit.BHS5
