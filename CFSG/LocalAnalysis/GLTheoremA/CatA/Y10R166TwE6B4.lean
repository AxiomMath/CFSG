module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B3
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Normalizer

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.HardMathSupport.Lang.E6Descent

namespace TwE6B

variable {Ω : Type} [Field Ω] [CharP Ω 2]

private theorem eq_one_of_mul_self_eq_one {ε : Ω} (h : ε * ε = 1) : ε = 1 := by
  have hsq : ε ^ 2 = 1 := by rw [pow_two]; exact h
  rcases (sq_eq_one_iff.mp hsq) with h1 | h1
  · exact h1
  · rw [h1]
    exact CharTwo.neg_eq 1

end TwE6B

open TwE6B

section Certs

variable {Ω : Type} [Field Ω] [CharP Ω 2]

theorem theta_pinnedX {Fr : Ω →+* Ω} {n : ℕ} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (c : Ω) :
    TwistedDiag.theta Fr (pinnedX Tag.E6 Ω α c) =
      pinnedX Tag.E6 Ω (-α) (c ^ (2 ^ n)) := by
  obtain ⟨ε₁, h₁, hF⟩ := exists_twistHom_pinnedX TwistTag.E6 Fr (α := α) hα
  have hρα : IsRoot Tag.E6 (permLattice e6Rho α) := hα.permLattice TwistTag.E6.cartan_perm
  obtain ⟨ε₂, h₂, hN⟩ := exists_canonicalRep_mul_pinnedX_mul_inv Ω twE6W0 hρα
  have hε : ε₂ * ε₁ = 1 := eq_one_of_mul_self_eq_one (by
    rw [mul_mul_mul_comm, h₂, h₁, one_mul])
  have hF' : ∀ c : Ω, twistE6 Ω Fr (pinnedX Tag.E6 Ω α c) =
      pinnedX Tag.E6 Ω (permLattice e6Rho α) (ε₁ * Fr c) := by
    intro c
    exact hF c
  rw [TwistedDiag.theta_apply, hF' c,
    show TwistedDiag.n0 Ω = canonicalRep (coxeterSystem Tag.E6) Ω twE6W0 from rfl,
    hN (ε₁ * Fr c), twE6W0_smul, TwistedDiag.permLattice_permLattice']
  congr 1
  rw [hFr c, ← mul_assoc, hε, one_mul]

def twE6C (Fr : Ω →+* Ω) : Subgroup (ModGL Tag.E6 Ω) :=
  ⁅TwistedDiag.thetaFixed Fr, TwistedDiag.thetaFixed Fr⁆

def twE6Block (Fr : Ω →+* Ω) : Subgroup (ModGL Tag.E6 Ω) :=
  subsystemGroup Tag.E6 Ω support56 ⊓ TwistedDiag.thetaFixed Fr

theorem mem_twE6Block {Fr : Ω →+* Ω} {g : ModGL Tag.E6 Ω} :
    g ∈ twE6Block Fr ↔
      g ∈ subsystemGroup Tag.E6 Ω support56 ∧ g ∈ TwistedDiag.thetaFixed Fr :=
  Iff.rfl

theorem mem_twE6C {Fr : Ω →+* Ω} {g : ModGL Tag.E6 Ω} :
    g ∈ twE6C Fr ↔ g ∈ ⁅TwistedDiag.thetaFixed Fr, TwistedDiag.thetaFixed Fr⁆ :=
  Iff.rfl

theorem twE6Block_le_fixed (Fr : Ω →+* Ω) : twE6Block Fr ≤ TwistedDiag.thetaFixed Fr :=
  inf_le_right

theorem twE6Block_le_subsystem (Fr : Ω →+* Ω) :
    twE6Block Fr ≤ subsystemGroup Tag.E6 Ω support56 := inf_le_left

theorem twE6Block_le_C_of_perfect (Fr : Ω →+* Ω)
    (hperf : ⁅twE6Block Fr, twE6Block Fr⁆ = twE6Block Fr) : twE6Block Fr ≤ twE6C Fr := by
  rw [← hperf]
  exact Subgroup.commutator_mono (twE6Block_le_fixed Fr) (twE6Block_le_fixed Fr)

theorem twE6_block_Phi {Fr : Ω →+* Ω} {n : ℕ} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    [IsAlgClosed Ω] :
    ∃ (Φ : Matrix.SpecialLinearGroup (Fin 3) Ω ≃* Matrix.SpecialLinearGroup (Fin 3) Ω)
      (b : Fin 3 → Fin 3 → Ωˣ),
      (∀ g : ↥(subsystemGroup Tag.E6 Ω support56),
        ((Φ (a2Equiv₂ Ω g) : Matrix.SpecialLinearGroup (Fin 3) Ω) :
          Matrix (Fin 3) (Fin 3) Ω) = a2Mat₂ (TwistedDiag.theta Fr (g : ModGL Tag.E6 Ω))) ∧
      (∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((Φ (Matrix.SpecialLinearGroup.transvection hij t) :
          Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
          1 + single j i ((b i j : Ω) * frobPow (Ω := Ω) n t)) := by
  classical
  have hθ' : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      TwistedDiag.theta Fr (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain56 j i) (e * frobPow (Ω := Ω) n c) := by
    intro i j hij
    refine ⟨1, by norm_num, fun c => ?_⟩
    rw [theta_pinnedX (Ω := Ω) hFr (isRoot_chainRoot56 hij) c,
      (chainRoot_swap chain56 i j).symm, frobPow_apply, one_mul]
  have hinj : Function.Injective (TwistedDiag.theta Fr) := by
    intro a b h
    rw [TwistedDiag.theta_apply, TwistedDiag.theta_apply] at h
    have h2 : twistE6 Ω Fr a = twistE6 Ω Fr b := mul_left_cancel (mul_right_cancel h)
    exact twistHom_injective TwistTag.E6 Ω Fr h2
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56,
      TwistedDiag.theta Fr g ∈ subsystemGroup Tag.E6 Ω support56 :=
    twE6_theta_maps_block_of_chainRoot n (TwistedDiag.theta Fr) hinj hθ'
  let θQ : subsystemGroup Tag.E6 Ω support56 →* subsystemGroup Tag.E6 Ω support56 :=
    { toFun := fun g => ⟨TwistedDiag.theta Fr (g : ModGL Tag.E6 Ω), hQ g g.2⟩
      map_one' := Subtype.ext (map_one (TwistedDiag.theta Fr))
      map_mul' := fun a b => Subtype.ext (map_mul (TwistedDiag.theta Fr) _ _) }
  let Φ₀ : Matrix.SpecialLinearGroup (Fin 3) Ω →* Matrix.SpecialLinearGroup (Fin 3) Ω :=
    (a2Equiv₂ Ω).toMonoidHom.comp (θQ.comp (a2Equiv₂ Ω).symm.toMonoidHom)
  have hΦ₀ : ∀ g : subsystemGroup Tag.E6 Ω support56,
      ((Φ₀ (a2Equiv₂ Ω g) : Matrix.SpecialLinearGroup (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω) = a2Mat₂ (TwistedDiag.theta Fr (g : ModGL Tag.E6 Ω)) := fun g => by
    change ((a2Equiv₂ Ω (θQ ((a2Equiv₂ Ω).symm (a2Equiv₂ Ω g))) :
      Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = _
    rw [MulEquiv.symm_apply_apply, a2Equiv₂_apply, coe_a2Rep₂]
    rfl
  choose s hs hρ using fun (i j : Fin 3) (hij : i ≠ j) =>
    CFSG.RankThree.Classical2.a2Mat₂_pinnedX_chainRoot56 (Ω := Ω) hij
  choose e he hθe using hθ'
  have hsymm : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      (a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t) =
        ⟨pinnedX Tag.E6 Ω (chainRoot chain56 i j) ((s i j hij : Ω) * t),
          CFSG.RankThree.Classical2.pinnedX_chainRoot56_mem hij _⟩ := by
    intro i j hij t
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₂_apply, coe_a2Rep₂, hρ i j hij, ← mul_assoc, (hs i j hij), one_mul]
    rfl
  set b : Fin 3 → Fin 3 → Ωˣ := fun i j => if hij : i ≠ j then
    Units.mkOfMulEqOne ((s j i hij.symm : Ω) * e i j hij * frobPow (Ω := Ω) n (s i j hij))
      ((s j i hij.symm : Ω) * e i j hij * frobPow (Ω := Ω) n (s i j hij)) (by
        have h1 := (hs j i hij.symm)
        have h2 := he i j hij
        have h3 : frobPow (Ω := Ω) n (s i j hij) * frobPow (Ω := Ω) n (s i j hij) = 1 := by
          rw [← map_mul, (hs i j hij), map_one]
        linear_combination (e i j hij * e i j hij *
          (frobPow (Ω := Ω) n (s i j hij) * frobPow (Ω := Ω) n (s i j hij))) * h1 +
          (frobPow (Ω := Ω) n (s i j hij) * frobPow (Ω := Ω) n (s i j hij)) * h2 + h3) else 1
    with hbdef
  have hb : ∀ (i j : Fin 3) (hij : i ≠ j), (b i j : Ω) =
      (s j i hij.symm : Ω) * e i j hij * frobPow (Ω := Ω) n (s i j hij) := by
    intro i j hij
    simp [hbdef, hij]
  have hΦt : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Φ₀ (Matrix.SpecialLinearGroup.transvection hij t) :
        Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
        1 + single j i ((b i j : Ω) * frobPow (Ω := Ω) n t) := by
    intro i j hij t
    change ((a2Equiv₂ Ω (θQ ((a2Equiv₂ Ω).symm
      (Matrix.SpecialLinearGroup.transvection hij t))) :
      Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = _
    rw [hsymm i j hij t, a2Equiv₂_apply, coe_a2Rep₂]
    change a2Mat₂ (TwistedDiag.theta Fr
      (pinnedX Tag.E6 Ω (chainRoot chain56 i j) ((s i j hij : Ω) * t))) = _
    rw [hθe i j hij, hρ j i hij.symm, hb i j hij, map_mul]
    congr 2
    ring
  have hΦinj : Function.Injective Φ₀ := by
    intro A B hAB
    have h1 := (a2Equiv₂ Ω).injective hAB
    have h2 : TwistedDiag.theta Fr ((a2Equiv₂ Ω).symm A) =
        TwistedDiag.theta Fr ((a2Equiv₂ Ω).symm B) := congrArg Subtype.val h1
    exact (a2Equiv₂ Ω).symm.injective (Subtype.ext (hinj h2))
  have hΦsurj : Function.Surjective Φ₀ := by
    rw [← MonoidHom.range_eq_top]
    have hmem : ∀ (k l : Fin 3) (hkl : k ≠ l) (t : Ω),
        Matrix.SpecialLinearGroup.transvection hkl t ∈ Φ₀.range := by
      intro k l hkl t
      obtain ⟨t', ht'⟩ := frobPow_surjective (Ω := Ω) n
        ((((b l k)⁻¹ : Ωˣ) : Ω) * t)
      refine ⟨Matrix.SpecialLinearGroup.transvection (Ne.symm hkl) t', Subtype.ext ?_⟩
      rw [hΦt]
      congr 2
      rw [ht']
      simp [mul_assoc]
    exact sl3_eq_top_of_adjacent _ (hmem 0 1 (by decide)) (hmem 1 2 (by decide))
      (hmem 1 0 (by decide)) (hmem 2 1 (by decide))
  let Φ : Matrix.SpecialLinearGroup (Fin 3) Ω ≃*
      Matrix.SpecialLinearGroup (Fin 3) Ω := MulEquiv.ofBijective Φ₀ ⟨hΦinj, hΦsurj⟩
  exact ⟨Φ, b, hΦ₀, hΦt⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
