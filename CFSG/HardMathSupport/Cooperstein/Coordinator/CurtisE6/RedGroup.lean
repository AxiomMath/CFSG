module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Interfaces
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.ChiPow
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Hat
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OuterBound
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.QuasithinUnique.Setup CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem card_dvd_of_surj {G' L : Type} [Group G'] [Finite G'] [Group L] (π : G' →* L)
    (hs : Function.Surjective π) : Nat.card L ∣ Nat.card G' := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hs).toEquiv] at h1
  exact ⟨Nat.card π.ker, h1⟩

theorem card_fix_zpowers {W : Type} [CommGroup W] [Finite W] (x : MulAut W) :
    Nat.card {w : W // x w = w} = Nat.card ↥(fixV (Subgroup.zpowers x)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ⟨fun h y hy => ?_, fun h => ?_⟩)
  · have hx : x ∈ MulAction.stabilizer (MulAut W) w := by
      rw [MulAction.mem_stabilizer_iff]; exact h
    have := (Subgroup.zpowers_le (H := MulAction.stabilizer (MulAut W) w)).2 hx hy
    exact MulAction.mem_stabilizer_iff.1 this
  · exact h x (Subgroup.mem_zpowers x)

theorem lift_fix {G' L k V : Type} [Group G'] [Finite G'] [Group L] [Field k] [AddCommGroup V]
    [Module k V] (π : G' →* L) (hs : Function.Surjective π)
    (hodd : ∀ x ∈ π.ker, ∀ j : ℕ, x ^ (2 ^ j) = 1 → x = 1) (ρ : Representation k L V)
    (Z : Subgroup L) (hZ : ∀ x ∈ Z, x ^ 2 = 1) :
    ∃ A : Subgroup G', (A = ⊥ ↔ Z = ⊥) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ Nat.card A = Nat.card Z ∧
      fixSub (ρ.comp π) A = fixSub ρ Z := by
  obtain ⟨A, hA, hsq, hcard⟩ := exists_two_lift π hs hodd Z hZ
  refine ⟨A, ⟨fun h => ?_, fun h => ?_⟩, hsq, hcard, ?_⟩
  · rw [← hA, h, Subgroup.map_bot]
  · rw [← Subgroup.card_eq_one, hcard, h, Subgroup.card_bot]
  · rw [fixSub_comp, hA]


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem expr_of_eq {α : MulAut ↥(adjointGroup .E6 K)} {g : ↥(adjointGroup .E6 K)}
    {a : Fin Tag.E6.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ}
    (h : α = MulAut.conj g * exactNormalAut .E6 K a σ ε) (x : ↥(adjointGroup .E6 K)) :
    (α x : ModGL .E6 K) = (g : ModGL .E6 K) * rootDiagUnit .E6 a * exactQ .E6 K ε *
      Units.map (entrywiseHom σ.toRingHom) (x : ModGL .E6 K) * (exactQ .E6 K ε)⁻¹ *
        (rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹ := by
  rw [h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_exactNormalAut, Subgroup.coe_inv]
  simp only [mul_assoc]

theorem psiAut_sq {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) :
    psiAut L e hb * psiAut L e hb = 1 := by
  have hbb : b * b ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mul_mem _ hb hb
  rw [← psiAut_mul e hb hb hbb]
  revert hbb
  rw [hb2]
  intro hbb
  exact psiAut_one e hbb

theorem mem_of_theta_one {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L) (hirr : X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hel : IsElemAbelian2 E)
    (eS : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(adjointGroup .E6 K))
    (Θ : MulAut ↥(adjointGroup .E6 K) →* RingAut K × Multiplicative (ZMod (exactE .E6)))
    (hΘker : ∀ α : MulAut ↥(adjointGroup .E6 K), α ∈ Θ.ker ↔
      ∃ (g : ↥(adjointGroup .E6 K)) (a : Fin Tag.E6.rank → Kˣ), ∀ h : ↥(adjointGroup .E6 K),
        (α h : ModGL .E6 K) = (g : ModGL .E6 K) * rootDiagUnit .E6 a * (h : ModGL .E6 K) *
          (rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹)
    (hinn : E6InnerOfSqOne) {b : MulAut W} (hb : b ∈ E)
    (h1 : Θ (psiAut L eS (hEN hb)) = 1) : b ∈ L := by
  obtain ⟨g, a, hga⟩ := (hΘker _).1 h1
  have hsq := psiAut_sq eS (hEN hb) (by rw [← pow_two]; exact hel.2 b hb)
  obtain ⟨s, hs⟩ := hinn K _ hsq ⟨g, a, hga⟩
  exact mem_of_psiAut_inner hW hperf hirr hEN hel eS hb s fun x => by
    rw [← hs]; rfl

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
