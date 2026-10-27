module

public import CFSG.Certificates.Kernel.GGToral.PkCoroot
public import CFSG.Certificates.Kernel.GGToral.PkAlcove
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertSound

public section

namespace CFSG.KC.GGToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType CFSG.StandardType.StepTwoToralCert

variable {τ : Tag} {p : ℕ}

theorem cowAct_add_smul (u : WeylGroup τ) (a b : ZMod p) (x y : Fin τ.rank → ZMod p) :
    cowAct u (a • x + b • y) = a • cowAct u x + b • cowAct u y := by
  funext i
  simp only [cowAct, latChar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

@[expose] def PlaneFree (π : Equiv.Perm (Fin τ.rank)) (M R : Set (Fin τ.rank → ZMod p)) : Prop :=
  ∃ G : Submonoid (WeylGroup τ), (∀ u ∈ G, CommutesPi π u) ∧ R ⊆ M ∧
    (∀ u ∈ G, ∀ e ∈ M, cowAct u e ∈ M) ∧ (∀ e ∈ M, ∃ u ∈ G, cowAct u e ∈ R) ∧
    ∀ r ∈ R, ∀ e ∈ M, (∃ t : ZMod p, e = t • r) ∨
      ∃ a c : ZMod p, a • r + c • e ≠ 0 ∧ a • r + c • e ∉ M

@[expose] def CaseFacts (p : ℕ) (π : Equiv.Perm (Fin τ.rank))
    (V : Submodule (ZMod p) (Fin τ.rank → ZMod p)) (b : Fin τ.rank → ZMod p)
    (O : Set (Fin τ.rank → ℤ)) : Prop :=
  3 ≤ Module.finrank (ZMod p) ↥(V ⊓ annSub p O) ∨
  (∃ S : Submodule (ZMod p) (Fin τ.rank → ZMod p), S ≤ V ∧
    S ≤ Submodule.span (ZMod p) (insert b ((V : Set (Fin τ.rank → ZMod p)) ∩
      latEigenCoroot p τ.symmetrizedCartan π O)) ∧
    Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) S + 1) ∨
  ∃ M R : Set (Fin τ.rank → ZMod p), PlaneFree π M R ∧
    ∀ t ∈ V, t ≠ 0 → t ∉ M → ∃ s ∈ Submodule.span (ZMod p) (insert b
      ((V : Set (Fin τ.rank → ZMod p)) ∩ latEigenCoroot p τ.symmetrizedCartan π O)), s ≠ 0 ∧
      ∃ u : WeylGroup τ, CommutesPi π u ∧ cowAct u s = t

theorem PlaneFree.exists_not_mem (hp : p.Prime) {π : Equiv.Perm (Fin τ.rank)}
    {M R : Set (Fin τ.rank → ZMod p)} (hM : PlaneFree π M R)
    {D : Submodule (ZMod p) (Fin τ.rank → ZMod p)} (hD : Module.finrank (ZMod p) D = 2) :
    ∃ d ∈ D, d ≠ 0 ∧ d ∉ M := by
  obtain ⟨G, -, -, hcl, hlink, hnp⟩ := hM
  by_contra hcon
  push Not at hcon
  obtain ⟨d1, hd1, hd10, d2, hd2, hind⟩ := tcExists_two_independent hp D hD
  have hd20 : d2 ≠ 0 := fun h => hind 0 (by rw [h, zero_smul])
  obtain ⟨u, huG, hur⟩ := hlink d1 (hcon d1 hd1 hd10)
  have he := hcl u huG d2 (hcon d2 hd2 hd20)
  rcases hnp _ hur _ he with ⟨t, ht⟩ | ⟨a, c, hne, hnot⟩
  · apply hind t
    have h1 : cowAct u ((1 : ZMod p) • d2 + (-t) • d1) = 0 := by
      rw [cowAct_add_smul, ht, one_smul, neg_smul, add_neg_cancel]
    have h2 := congrArg (cowAct u⁻¹) h1
    rw [cowAct_inv_cowAct, cowAct_zero, one_smul, neg_smul, ← sub_eq_add_neg] at h2
    exact sub_eq_zero.mp h2
  · apply hnot
    rw [← cowAct_add_smul]
    have hmem : a • d1 + c • d2 ∈ D := D.add_mem (D.smul_mem a hd1) (D.smul_mem c hd2)
    have hne' : a • d1 + c • d2 ≠ 0 := fun h => hne (by rw [← cowAct_add_smul, h, cowAct_zero])
    exact hcl u huG _ (hcon _ hmem hne')

theorem caseFacts_certConcl (hp : p.Prime) {π : Equiv.Perm (Fin τ.rank)}
    {V : Submodule (ZMod p) (Fin τ.rank → ZMod p)} {b : Fin τ.rank → ZMod p}
    {O : Set (Fin τ.rank → ℤ)} (h : CaseFacts p π V b O)
    {D : Submodule (ZMod p) (Fin τ.rank → ZMod p)} (hD : QualPlane p V D)
    (hcard : Nat.card ↥(V ⊓ annSub p O) ≤ p ^ 2) : CertConcl p π V b O D := by
  have hfin : Module.finrank (ZMod p) D = 2 := finrank_eq_two_of_natCard hp D hD.2.1
  rcases h with h3 | ⟨S, hSV, hSspan, hdim⟩ | ⟨M, R, hM, hwit⟩
  · have h4 := natCard_ge_pow hp _ h3
    have h5 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  · have hne := inf_ne_bot_of_finrank_zmod hp hD.1 hSV (by omega)
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨s, hSspan hs.2, hs0, 1, commutesPi_one π, by rw [cowAct_one]; exact hs.1⟩
  · obtain ⟨d, hdD, hd0, hdM⟩ := hM.exists_not_mem hp hfin
    obtain ⟨s, hs, hs0, u, hu, hsu⟩ := hwit d (hD.1 hdD) hd0 hdM
    exact ⟨s, hs, hs0, u, hu, by rw [hsu]; exact hdD⟩

end CFSG.KC.GGToral
