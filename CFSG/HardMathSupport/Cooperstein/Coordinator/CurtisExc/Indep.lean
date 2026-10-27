module

public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CoxeterSystem

section Datum

variable {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p)

theorem n_inv_mul_nW (s : B) (b : W) :
    ∃ h ∈ D.H, (D.n s)⁻¹ * D.nW b = D.nW (cs.simple s * b) * h := by
  rcases cs.length_simple_mul b s with hup | hdown
  · refine ⟨(D.nW b)⁻¹ * (D.n s * D.n s)⁻¹ * D.nW b, D.nW_normH b (inv_mem (D.n_sq s)), ?_⟩
    rw [D.nW_simple_mul b s hup]
    group
  · have hb : b = cs.simple s * (cs.simple s * b) := by
      rw [← mul_assoc, cs.simple_mul_simple_self s, one_mul]
    have hlen : cs.length (cs.simple s * (cs.simple s * b)) =
        cs.length (cs.simple s * b) + 1 := by
      rw [← hb]; omega
    refine ⟨1, one_mem _, ?_⟩
    conv_lhs => rw [hb]
    rw [D.nW_simple_mul _ s hlen, mul_one]
    group

theorem nW_inv_mul_aux (ω : List B) (hω : cs.IsReduced ω) (b : W) :
    ∃ h ∈ D.H, (D.nW (cs.wordProd ω))⁻¹ * D.nW b = D.nW ((cs.wordProd ω)⁻¹ * b) * h := by
  induction ω generalizing b with
  | nil =>
    refine ⟨1, one_mem _, ?_⟩
    rw [cs.wordProd_nil, D.nW_one]
    simp
  | cons s ω ih =>
    obtain ⟨hred, hlen⟩ := CurtisDatum.reduced_cons hω
    obtain ⟨h₁, hh₁, e₁⟩ := n_inv_mul_nW D s b
    obtain ⟨h₂, hh₂, e₂⟩ := ih hred (cs.simple s * b)
    refine ⟨h₂ * h₁, mul_mem hh₂ hh₁, ?_⟩
    have e : (cs.wordProd (s :: ω))⁻¹ * b = (cs.wordProd ω)⁻¹ * (cs.simple s * b) := by
      rw [cs.wordProd_cons, mul_inv_rev, cs.inv_simple, mul_assoc]
    rw [e, cs.wordProd_cons, D.nW_simple_mul _ _ hlen, mul_inv_rev, mul_assoc, e₁, ← mul_assoc,
      e₂, mul_assoc]

theorem nW_inv_mul (a b : W) : ∃ h ∈ D.H, (D.nW a)⁻¹ * D.nW b = D.nW (a⁻¹ * b) * h := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced a
  exact nW_inv_mul_aux D ω hω b

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

variable [Finite G]

theorem form_nW_mul {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    {f : Module.Dual k V} (hf : ∀ z ∈ CFSG.Quasithin.SmithCurtis.augSub ρ D.L, f z = 0)
    (hfy : f y = 1) {ω : List B} (hω : cs.IsReduced ω) {h : G} (hh : h ∈ D.H) :
    f (ρ (D.nW (cs.wordProd ω) * h) y) = χ h * D.coinvScalar χ μ ω := by
  have h1 := D.coinv_formula ρ hω ht.1
  rw [D.coinvOp_eigen ρ ht.2.2.1 ht.2.2.2] at h1
  have h2 := hf _ h1
  rw [map_sub, map_smul, hfy, smul_eq_mul, mul_one, sub_eq_zero] at h2
  rw [← act_mul, ht.2.2.1 h hh, map_smul, map_smul, h2, smul_eq_mul]

variable {D ρ}

theorem linearIndependent_translates [Fact p.Prime] [CharP k p] (hρ : IsSimpleRep ρ) {y : V}
    {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) {m : ℕ} (w : Fin m → W)
    (hsep : ∀ i j, i ≠ j → ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (w i)⁻¹ * w j →
      ∃ s ∈ ω, μ s = D.dScalar χ s) :
    LinearIndependent k fun i => ρ (D.nW (w i)) y := by
  obtain ⟨f, hf, hfy⟩ := D.exists_form hρ ht.1 ht.2.1
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have key : ∀ j, f (ρ ((D.nW (w i))⁻¹ * D.nW (w j)) y) = if j = i then 1 else 0 := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [inv_mul_cancel, map_one, Module.End.one_apply, hfy]
      simp
    · simp only [hji, ite_false]
      obtain ⟨h, hh, e⟩ := nW_inv_mul D (w i) (w j)
      obtain ⟨ω, hω, hωe⟩ := cs.exists_isReduced ((w i)⁻¹ * w j)
      rw [e, hωe, form_nW_mul D ρ ht hf hfy hω hh]
      obtain ⟨s, hs, hμ⟩ := hsep i j (Ne.symm hji) ω hω hωe.symm
      have : D.coinvScalar χ μ ω = 0 := by
        unfold CurtisDatum.coinvScalar
        exact List.prod_eq_zero (List.mem_map.mpr ⟨s, hs, sub_eq_zero.mpr hμ⟩)
      rw [this, mul_zero]
  have h2 := congrArg (fun z => f (ρ (D.nW (w i))⁻¹ z)) hc
  simp only [map_sum, map_smul, map_zero, act_mul] at h2
  simp only [key, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h2
  exact h2

theorem card_le_finrank [Fact p.Prime] [CharP k p] [Module.Finite k V] (hρ : IsSimpleRep ρ)
    {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) {m : ℕ} (w : Fin m → W)
    (hsep : ∀ i j, i ≠ j → ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (w i)⁻¹ * w j →
      ∃ s ∈ ω, μ s = D.dScalar χ s) :
    m ≤ Module.finrank k V := by
  simpa using (linearIndependent_translates hρ ht w hsep).fintype_card_le_finrank

end Datum

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
