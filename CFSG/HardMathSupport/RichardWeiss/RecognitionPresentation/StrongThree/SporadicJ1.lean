module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Families
public import CFSG.Sporadic.Bridge.J1
public import CFSG.Sporadic.Schreier.J1Outer

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open TauCeti

theorem exists_eq_conj_of_mulEquiv_J1
    {H : Type*} [Group H]
    (g : H ≃* CFSG.Blueprint.NativeSporadic.J1) (φ : MulAut H) :
    ∃ k : H, φ = MulAut.conj k := by
  obtain ⟨j, hj⟩ := CFSG.Sporadic.Schreier.at_j1_schreier.2.1 ((g.symm.trans φ).trans g)
  refine ⟨g.symm j, MulEquiv.ext fun k => ?_⟩
  have h := congrArg (fun ψ : MulAut CFSG.Blueprint.NativeSporadic.J1 => g.symm (ψ (g k))) hj
  simpa using h

theorem eq_top_of_forall_inner {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (hinner : ∀ φ : MulAut ↥K, ∃ k : ↥K, φ = MulAut.conj k)
    (hKc : Subgroup.centralizer (K : Set X) = ⊥) : K = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨k, hk⟩ := hinner (MulAut.conjNormal x)
  have hc : (k : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun ψ : MulAut ↥K => ((ψ ⟨y, hy⟩ : ↥K) : X)) hk
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * x := by group
      _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h]
      _ = (k : X)⁻¹ * x * y := by group
  rw [hKc, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc ▸ k.2

theorem gls3PlusCase_J1 :
    Gls3PlusCase (.sporadic .J1) := by
  unfold Gls3PlusCase
  intro X _ _ _ K hKn _ _ hiso hKc P hP _
  exfalso
  have := hKn
  obtain ⟨e⟩ := hiso
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have g : ↥K ≃* CFSG.Blueprint.NativeSporadic.J1 := e.trans f.symm
  have htop : K = ⊤ := eq_top_of_forall_inner (exists_eq_conj_of_mulEquiv_J1 g) hKc
  have hcard : Nat.card X = 175560 := by
    rw [← CFSG.Sporadic.J1.card_J1, ← Nat.card_congr g.toEquiv, htop, Subgroup.card_top]
  have hE : ∀ k : ℕ, (∃ E : Subgroup X, E ≤ (P : Subgroup X) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k) → k ≤ 1 := by
    rintro k ⟨E, -, -, hEk⟩
    have h1 : 3 ^ k ∣ 175560 := by
      have h := Subgroup.card_subgroup_dvd_card E
      rwa [hEk, hcard] at h
    by_contra hk
    have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (show 2 ≤ k by omega)
    exact absurd (h9.trans h1) (by norm_num)
  have hpR : CFSG.Open.pRank 3 (P : Subgroup X) ≤ 1 := by
    unfold CFSG.Open.pRank
    apply csSup_le'
    intro k hk
    exact hE k hk
  omega

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
