module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenCert

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.SolMax.SwapP2.ExactAbs

open scoped commutatorElement

section Induced

variable {S Γ : Type*} [Group S] [Group Γ] (P N : Subgroup Γ) (e : S ≃* P)
  (hnorm : ∀ μ ∈ N, Normalizes μ P)

@[expose] noncomputable def indAutFun (μ : N) : MulAut S :=
  { toFun := fun s => e.symm ⟨(μ : Γ) * (e s : Γ) * (μ : Γ)⁻¹, (hnorm μ μ.2 _).1 (e s).2⟩
    invFun := fun s => e.symm ⟨(μ : Γ)⁻¹ * (e s : Γ) * (μ : Γ),
      ((hnorm μ μ.2).inv_conj _).1 (e s).2⟩
    left_inv := fun s => by
      apply e.injective
      apply Subtype.ext
      simp only [MulEquiv.apply_symm_apply]
      group
    right_inv := fun s => by
      apply e.injective
      apply Subtype.ext
      simp only [MulEquiv.apply_symm_apply]
      group
    map_mul' := fun a b => by
      apply e.injective
      apply Subtype.ext
      simp only [MulEquiv.apply_symm_apply, map_mul, Subgroup.coe_mul]
      group }

theorem indAutFun_spec (μ : N) (s : S) :
    ((e (indAutFun P N e hnorm μ s) : P) : Γ) = (μ : Γ) * (e s : Γ) * (μ : Γ)⁻¹ := by
  change ((e (e.symm ⟨(μ : Γ) * (e s : Γ) * (μ : Γ)⁻¹, _⟩) : P) : Γ) = _
  rw [MulEquiv.apply_symm_apply]

@[expose] noncomputable def indAut : N →* MulAut S :=
  MonoidHom.mk' (indAutFun P N e hnorm) fun a b => by
    apply MulEquiv.ext
    intro s
    apply e.injective
    apply Subtype.ext
    rw [MulAut.mul_apply, indAutFun_spec, indAutFun_spec, indAutFun_spec]
    simp only [Subgroup.coe_mul]
    group

theorem indAut_spec (μ : N) (s : S) :
    ((e (indAut P N e hnorm μ s) : P) : Γ) = (μ : Γ) * (e s : Γ) * (μ : Γ)⁻¹ :=
  indAutFun_spec P N e hnorm μ s

theorem indAut_injective (hcent : ∀ x ∈ N, (∀ p ∈ P, x * p = p * x) → x = 1) :
    Function.Injective (indAut P N e hnorm) := by
  rw [injective_iff_map_eq_one]
  intro μ hμ
  have hcomm : ∀ p ∈ P, (μ : Γ) * p = p * (μ : Γ) := by
    intro p hp
    obtain ⟨s, rfl⟩ : ∃ s : S, ((e s : P) : Γ) = p := ⟨e.symm ⟨p, hp⟩, by simp⟩
    have h1 := indAut_spec P N e hnorm μ s
    rw [hμ, MulAut.one_apply] at h1
    calc (μ : Γ) * (e s : Γ) = ((μ : Γ) * (e s : Γ) * (μ : Γ)⁻¹) * μ := by group
      _ = (e s : Γ) * μ := by rw [← h1]
  exact Subtype.ext (hcent μ μ.2 hcomm)

end Induced

theorem prime_card_of_comm {G : Type*} [Group G] [IsSimpleGroup G] (hc : ∀ a b : G, a * b = b * a) :
    (Nat.card G).Prime := by
  haveI : IsMulCommutative G := ⟨⟨hc⟩⟩
  exact (Group.is_simple_iff_prime_card.1 inferInstance)

theorem commutator_eq_top_of_simple_card {G : Type*} [Group G] [IsSimpleGroup G]
    (hp : ¬ (Nat.card G).Prime) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    refine hp (prime_card_of_comm fun a b => ?_)
    have : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 this)
  · exact h

theorem factorization_two_le_one {m : ℕ} (h0 : 0 < m) (h : m ≤ 2) : m.factorization 2 ≤ 1 := by
  interval_cases m
  · simp
  · rw [Nat.factorization_def _ Nat.prime_two]
    decide +kernel

theorem exists_conj_mem_of_two_part {A : Type*} [Group A] [Finite A] (H : Subgroup A)
    (h : (Nat.card A).factorization 2 ≤ (Nat.card H).factorization 2) {x : A} (hx : x * x = 1) :
    ∃ σ : A, σ * x * σ⁻¹ ∈ H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 H) := inferInstance
  let T : Subgroup A := (T₀ : Subgroup H).map H.subtype
  have hTH : T ≤ H := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hcardT : Nat.card T = 2 ^ (Nat.card A).factorization 2 := by
    have h1 : Nat.card T = Nat.card (T₀ : Subgroup H) :=
      (Nat.card_congr
        ((T₀ : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm
    have h2 : Nat.card (T₀ : Subgroup H) = 2 ^ (Nat.card H).factorization 2 :=
      T₀.card_eq_multiplicity
    have h3 : (Nat.card H).factorization 2 ≤ (Nat.card A).factorization 2 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (Subgroup.card_subgroup_dvd_card H) 2
    rw [h1, h2, le_antisymm h3 h]
  have hcov := cover_of_sylow (N := ⊤) (T := T) (K := ⊤) le_rfl le_top
    (by rw [Subgroup.card_top, hcardT]) (H : Set A) (by
      intro t ht _
      exact Or.inr ⟨1, Subgroup.one_mem _, t, hTH ht, by simp⟩)
  rcases hcov x (Subgroup.mem_top x) hx with h1 | ⟨μ, -, ρ, hρ, hμ⟩
  · exact ⟨1, by rw [h1]; simpa using H.one_mem⟩
  · exact ⟨μ, hμ ▸ hρ⟩

theorem hAut_of_two_part {S Γ : Type*} [Group S] [Group Γ] [Finite S] (P N : Subgroup Γ)
    (e : S ≃* P) (hnorm : ∀ μ ∈ N, Normalizes μ P)
    (hcent : ∀ x ∈ N, (∀ p ∈ P, x * p = p * x) → x = 1) [Finite N]
    (h2 : (Nat.card (MulAut S)).factorization 2 ≤ (Nat.card N).factorization 2) :
    ∀ τ : MulAut S, τ * τ = 1 → ∃ σ : MulAut S, ∃ ν ∈ N,
      ∀ s : S, ((e ((σ * τ * σ⁻¹) s) : P) : Γ) = ν * (e s : Γ) * ν⁻¹ := by
  haveI : Finite (MulAut S) := Finite.of_injective (fun f : MulAut S => (f : S → S))
    (fun f g h => MulEquiv.ext (congrFun h))
  have hinj := indAut_injective P N e hnorm hcent
  have hH : Nat.card (indAut P N e hnorm).range = Nat.card N :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  intro τ hτ
  obtain ⟨σ, hσ⟩ := exists_conj_mem_of_two_part (indAut P N e hnorm).range (by rw [hH]; exact h2) hτ
  obtain ⟨ν, hν⟩ := hσ
  refine ⟨σ, ν, ν.2, fun s => ?_⟩
  rw [← hν]
  exact indAut_spec P N e hnorm ν s

theorem card_mulAut_eq {G : Type*} [Group G] (hc : Subgroup.center G = ⊥) :
    Nat.card (MulAut G) = Nat.card (Outer G) * Nat.card G := by
  have hinner : Nat.card (inner G) = Nat.card G := by
    have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply le_antisymm _ bot_le
      intro x hx
      have hcentral : x ∈ Subgroup.center G := by
        apply Subgroup.mem_center_iff.mpr
        intro y
        have hconj := congrArg (fun f : MulAut G => f y) hx
        change x * y * x⁻¹ = y at hconj
        have heq := congrArg (fun z : G => z * x) hconj
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
      rwa [hc] at hcentral
    change Nat.card (MulAut.conj : G →* MulAut G).range = _
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hquot := (inner G).card_eq_card_quotient_mul_card_subgroup
  rw [hinner] at hquot
  exact hquot

theorem coreStmt_of_model (n : ℕ) (c : FCCert) (hc : c.ok n = true) {S : Type*} [Group S]
    [Finite S] (e : S ≃* c.ctx.chP.sub n) (hperf : commutator S = ⊤) {a : ℕ}
    (hout : (Nat.card (Outer S)).factorization 2 ≤ a)
    (hk : a + (c.ctx.chP.order n).factorization 2 ≤ (c.ctx.chN.order n).factorization 2) :
    CoreStmt S := by
  obtain ⟨-, -, hPN, hnorm, hcent, hcP, hcN⟩ := Ctx.sound n c.ctx (c.ctx_ok n hc)
  have hcenter : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hcomm : ∀ p ∈ c.ctx.chP.sub n,
        ((e x : c.ctx.chP.sub n) : Equiv.Perm (Fin n)) * p = p * ((e x : c.ctx.chP.sub n) :
          Equiv.Perm (Fin n)) := by
      intro p hp
      have := Subgroup.mem_center_iff.1 hx (e.symm ⟨p, hp⟩)
      have h2 := congrArg (fun y => ((e y : c.ctx.chP.sub n) : Equiv.Perm (Fin n))) this
      simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h2
      exact h2.symm
    have h1 := hcent _ (hPN (e x).2) hcomm
    have : e x = 1 := Subtype.ext h1
    have : x = 1 := e.injective (by rw [this, map_one])
    simpa using this
  haveI : Finite (c.ctx.chN.sub n) := inferInstance
  refine coreStmt_of_cert n c hc e
    (commutator_eq_of_equiv _ e hperf) ?_
  refine hAut_of_two_part _ _ e hnorm hcent ?_
  have hS : Nat.card S = c.ctx.chP.order n := by
    rw [Nat.card_congr e.toEquiv, hcP]
  rw [card_mulAut_eq hcenter, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply, hcN, hS]
  omega

end CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
