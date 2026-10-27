module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Torus

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TwistedDiag


theorem weyl_smul_neg (w : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ℤ) :
    w • (-x) = -(w • x) := by
  rw [← weylMatrix_mulVec, Matrix.mulVec_neg, weylMatrix_mulVec]

theorem permLattice_neg' (x : Fin Tag.E6.rank → ℤ) :
    permLattice e6Rho (-x) = -(permLattice e6Rho x) := rfl

theorem permLattice_permLattice' (x : Fin Tag.E6.rank → ℤ) :
    permLattice e6Rho (permLattice e6Rho x) = x := by
  funext i
  simp only [permLattice, Function.comp_apply]
  rw [CFSG.RankThree.E6.e6Rho_symm, show e6Rho (e6Rho i) = i by revert i; decide]

theorem twE6W0_smul_smul (x : Fin Tag.E6.rank → ℤ) : twE6W0 • (twE6W0 • x) = x := by
  rw [twE6W0_smul, twE6W0_smul, permLattice_neg', neg_neg, permLattice_permLattice']

theorem twE6W0_mul_self : twE6W0 * twE6W0 = 1 :=
  eq_of_smul_single_eq fun j => by
    rw [mul_smul, twE6W0_smul_smul, one_smul]

theorem twE6W0_inv : twE6W0⁻¹ = twE6W0 := inv_eq_of_mul_eq_one_right twE6W0_mul_self

@[expose] def delta (w : WeylGroup Tag.E6) : WeylGroup Tag.E6 := weylTwist TwistTag.E6 w

theorem delta_smul_permLattice (w : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ) :
    delta w • permLattice e6Rho v = permLattice e6Rho (w • v) :=
  weylTwist_smul_permLattice TwistTag.E6 w v

theorem w0_mul_delta_mul_w0_inv (w : WeylGroup Tag.E6) :
    twE6W0 * delta w * twE6W0⁻¹ = w :=
  eq_of_smul_single_eq fun j => by
    rw [twE6W0_inv, mul_smul, mul_smul]
    generalize (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = x
    calc twE6W0 • (delta w • (twE6W0 • x)) = twE6W0 • (delta w • (-(permLattice e6Rho x))) := by
          rw [twE6W0_smul x]
      _ = twE6W0 • (-(permLattice e6Rho (w • x))) := by
          rw [weyl_smul_neg, delta_smul_permLattice]
      _ = w • x := by
          rw [twE6W0_smul, permLattice_neg', neg_neg, permLattice_permLattice']

variable {Ω : Type} [Field Ω] (Fr : Ω →+* Ω)

theorem canonicalRep_mem_monomial (w : WeylGroup Tag.E6) :
    canonicalRep (coxeterSystem Tag.E6) Ω w ∈ monomialSubgroup Tag.E6 Ω :=
  Subgroup.mem_sup_right (canonicalRep_mem_closure _ _ w)

theorem n0_mem_monomial : n0 Ω ∈ monomialSubgroup Tag.E6 Ω := canonicalRep_mem_monomial _

theorem theta_canonicalRep (w : WeylGroup Tag.E6) :
    theta Fr (canonicalRep (coxeterSystem Tag.E6) Ω w) =
      n0 Ω * canonicalRep (coxeterSystem Tag.E6) Ω (delta w) * (n0 Ω)⁻¹ := by
  rw [theta_apply]
  congr 2
  exact twistHom_canonicalRep TwistTag.E6 Ω Fr w

theorem mem_monomial_theta_canonicalRep (w : WeylGroup Tag.E6) :
    theta Fr (canonicalRep (coxeterSystem Tag.E6) Ω w) ∈ monomialSubgroup Tag.E6 Ω := by
  rw [theta_canonicalRep]
  exact mul_mem (mul_mem n0_mem_monomial (canonicalRep_mem_monomial _))
    (inv_mem n0_mem_monomial)

theorem mapsRootLines_theta_canonicalRep (w : WeylGroup Tag.E6) :
    MapsRootLines (theta Fr (canonicalRep (coxeterSystem Tag.E6) Ω w) :
      (Module.End Ω (RootModule Tag.E6 Ω))ˣ) w := by
  rw [theta_canonicalRep]
  have h := ((mapsRootLines_canonicalRep (R := Ω) twE6W0).mul
    (mapsRootLines_canonicalRep (R := Ω) (delta w))).mul
    (mapsRootLines_canonicalRep (R := Ω) twE6W0).inv
  rw [w0_mul_delta_mul_w0_inv] at h
  exact h

theorem exists_torus_mul_of_mapsRootLines {g : ModGL Tag.E6 Ω}
    (hg : g ∈ monomialSubgroup Tag.E6 Ω) {w : WeylGroup Tag.E6}
    (hw : MapsRootLines (g : (Module.End Ω (RootModule Tag.E6 Ω))ˣ) w) :
    ∃ k ∈ torusGroup Tag.E6 Ω, g = canonicalRep (coxeterSystem Tag.E6) Ω w * k := by
  obtain ⟨w', k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hg
  have hmaps : MapsRootLines ((k * canonicalRep (coxeterSystem Tag.E6) Ω w' : ModGL Tag.E6 Ω) :
      (Module.End Ω (RootModule Tag.E6 Ω))ˣ) w' := by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w')
  have hww : w' = w := MapsRootLines.unique hmaps hw
  subst hww
  refine ⟨(canonicalRep (coxeterSystem Tag.E6) Ω w')⁻¹ * k * canonicalRep (coxeterSystem Tag.E6) Ω w',
    ?_, by group⟩
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem (canonicalRep_mem_normalizer
    (R := Ω) w')) k).1 hk
  simpa using this

theorem exists_lift [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (w : WeylGroup Tag.E6) :
    ∃ m ∈ monomialSubgroup Tag.E6 Ω ⊓ thetaFixed Fr,
      MapsRootLines (m : (Module.End Ω (RootModule Tag.E6 Ω))ˣ) w := by
  obtain ⟨k, hk, hkeq⟩ := exists_torus_mul_of_mapsRootLines
    (mem_monomial_theta_canonicalRep Fr w) (mapsRootLines_theta_canonicalRep Fr w)
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hk
  have hroot : ∀ i, ∃ z : Ωˣ, z ^ (q + 1) = a i := fun i => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((a i : Ωˣ) : Ω) (Nat.succ_pos q)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.succ_ne_zero q)] at hz
      exact (a i).ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose b hb using hroot
  have hbT := rootDiagUnit_mem_torusGroup (K := Ω) (τ := Tag.E6) b
  refine ⟨canonicalRep (coxeterSystem Tag.E6) Ω w * rootDiagUnit Tag.E6 b,
    ⟨mul_mem (canonicalRep_mem_monomial w) (DiagTorus.torusGroup_le_monomialSubgroup hbT),
      mul_mem (canonicalRep_mem_adjointGroup _ Ω w) (torusGroup_le_adjointGroup_E6 hbT), ?_⟩, ?_⟩
  · change theta Fr _ = _
    rw [map_mul, hkeq, theta_rootDiagUnit Fr hFr, mul_assoc, ← rootDiagUnit_mul]
    congr 2
    funext i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    rw [← hb i, pow_succ, mul_comm (b i ^ q) (b i), mul_assoc, mul_inv_cancel, mul_one]
  · have h := (mapsRootLines_canonicalRep (R := Ω) w).mul (mapsRootLines_of_mem_torusGroup hbT)
    rwa [mul_one] at h

theorem card_monomial_thetaFixed [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq : (q : Ω) = 0) :
    Nat.card ↥(monomialSubgroup Tag.E6 Ω ⊓ thetaFixed Fr) = (q + 1) ^ 6 * 51840 := by
  obtain ⟨-, ⟨ρ, -, hρ, -, -, hker⟩, -⟩ := Weyl_normalizer_quotient Tag.E6 Ω
  set N' := monomialSubgroup Tag.E6 Ω ⊓ thetaFixed Fr with hN'
  have hle : N' ≤ monomialSubgroup Tag.E6 Ω := inf_le_left
  let ρN : N' →* WeylGroup Tag.E6 := ρ.comp (Subgroup.inclusion hle)
  have hsurj : Function.Surjective ρN := fun w => by
    obtain ⟨m, hm, hmw⟩ := exists_lift Fr hFr w
    refine ⟨⟨m, hm⟩, ?_⟩
    exact MapsRootLines.unique (hρ ⟨m, hle hm⟩) hmw
  have hTle : thetaTorus Ω q ≤ N' := fun x hx => by
    rw [← torus_inf_thetaFixed Fr hFr] at hx
    exact ⟨DiagTorus.torusGroup_le_monomialSubgroup hx.1, hx.2⟩
  have hkerN : ρN.ker = (thetaTorus Ω q).subgroupOf N' := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← torus_inf_thetaFixed Fr hFr]
    constructor
    · intro h
      have h1 : Subgroup.inclusion hle m ∈ ρ.ker := h
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact ⟨h1, m.2.2⟩
    · intro h
      have h1 : Subgroup.inclusion hle m ∈ ρ.ker := by
        rw [hker, Subgroup.mem_subgroupOf]
        exact h.1
      exact h1
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρN.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρN hsurj).toEquiv, hkerN,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv, natCard_thetaTorus hq,
    CFSG.RankThree.E6.card_weylGroup_E6] at h1
  rw [h1]
  ring

end TwistedDiag

end CFSG.HardMathSupport.Lang.E6Descent
