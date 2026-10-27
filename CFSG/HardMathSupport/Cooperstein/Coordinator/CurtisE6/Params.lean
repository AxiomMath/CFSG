module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.ChiPow
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OuterBound
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSix
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Lift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.OuterType

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.QuasithinUnique.Setup


variable {K : Type} [Field K] [Finite K] [CharP K 2]

structure HatData (K : Type) [Field K] [Finite K] [CharP K 2] (L : Type) [Group L] where
  f : L →* ↥(adjointGroup .E6 K)
  hf : Function.Surjective f
  hfk : f.ker ≤ Subgroup.center L
  hperf : commutator L = ⊤
  π : ↥(e6Data_valid.minGroup K) →* L
  hπs : Function.Surjective π
  hπf : ∀ x, f (π x) = Isogeny.e6IsogenyT K x

namespace HatData

variable {L : Type} [Group L] (D : HatData K L)

theorem ker_le : D.π.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup K) := by
  intro x hx
  have h1 : Isogeny.e6IsogenyT K x = 1 := by
    rw [← D.hπf, MonoidHom.mem_ker.1 hx]; exact map_one _
  exact Isogeny.ker_e6IsogenyT_le_center K (MonoidHom.mem_ker.2 h1)

theorem hodd : ∀ x ∈ D.π.ker, ∀ j : ℕ, x ^ (2 ^ j) = 1 → x = 1 := by
  intro x hx j hj
  have h1 : Isogeny.e6IsogenyT K x = 1 := by
    rw [← D.hπf, MonoidHom.mem_ker.1 hx]; exact map_one _
  refine e6Cover_hodd x ?_ ⟨j, hj⟩
  rw [Subgroup.mem_comap, h1]
  exact Subgroup.one_mem _

end HatData

section Outer

variable {L : Type} [Group L] [Finite L] (D : HatData K L) {n : ℕ}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {m : ℕ}

theorem outer_type_L (hK : Nat.card K = 2 ^ n) {ρ : Representation k L (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) (ρ.comp D.π) y χ J)
    (a : N6 → Kˣ) (σ : K ≃+* K) (ε : ℕ) (φ : MulAut L)
    (hφ : ∀ x, D.f (φ x) = exactNormalAut .E6 K a σ ε (D.f x))
    (B : (Fin m → k) ≃ₗ[k] (Fin m → k)) (hB : ∀ s v, ρ (φ s) (B v) = B (ρ s v)) :
    (∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K (exactPerm .E6 ε i) (sU σ u)) =
        χ (e6Data_valid.hm K i u)) ∧
      ∀ i : N6, i ∈ J ↔ exactPerm .E6 ε i ∈ J := by
  have : Finite ↥(e6Data_valid.minGroup K) := CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid
  have hperf : commutator ↥(e6Data_valid.minGroup K) = ⊤ :=
    Group.isPerfect_def.1 (CFSG.LieType.CurtisTits.isPerfect_e6 K)
  obtain ⟨N, hN⟩ := exists_lift_aut D.π D.hπs D.ker_le hperf
    (fun E _ _ p hp hc => CFSG.StandardType.LayerCycExc.e6_minGroup_exists_section hK E p hp hc) φ
  refine outer_type (simpleRep_comp D.π D.hπs hρ) ht a σ ε N ?_ B ?_
  · intro x
    rw [← D.hπf, hN, hφ, D.hπf]
  · intro x v
    show ρ (D.π (N x)) (B v) = B (ρ (D.π x) v)
    rw [hN]
    exact hB _ v

end Outer

section OuterParams

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} [Finite ↥L] {n : ℕ}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {m : ℕ}

theorem outer_params (hK : Nat.card K = 2 ^ n)
    (eS : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(adjointGroup .E6 K))
    (D : HatData K ↥L) (hDf : ∀ x, D.f x = eS (QuotientGroup.mk x))
    {ρ : Representation k ↥L (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) (ρ.comp D.π) y χ J)
    {b : MulAut W} (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (B : Module.End k (Fin m → k)) (hBu : IsUnit B)
    (hBρ : ∀ s : ↥L, B * ρ s = ρ (X1.conjAut L hb s) * B) :
    ∃ (g : ↥(adjointGroup .E6 K)) (a : N6 → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE .E6)),
      psiAut L eS hb = MulAut.conj g * exactNormalAut .E6 K a σ ε ∧
      (∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K (exactPerm .E6 ε i) (sU σ u)) =
        χ (e6Data_valid.hm K i u)) ∧
      ∀ i : N6, i ∈ J ↔ exactPerm .E6 ε i ∈ J := by
  obtain ⟨g, a, σ, ε, hαe⟩ := exists_conj_mul_exactNormalAut (K := K) (τ := .E6) (Or.inl rfl)
    (psiAut L eS hb)
  obtain ⟨g0, hg0⟩ := D.hf g
  have hbij : Function.Bijective B := (Module.End.isUnit_iff B).1 hBu
  let φ' : MulAut ↥L := (X1.conjAut L hb).trans (MulAut.conj g0⁻¹)
  have hφ'x : ∀ x, φ' x = g0⁻¹ * X1.conjAut L hb x * g0 := fun x => by
    simp [φ', MulAut.conj_apply]
  have hf1 : ∀ x : ↥L, D.f (X1.conjAut L hb x) = psiAut L eS hb (D.f x) := by
    intro x
    rw [hDf, hDf, psiAut_mk]
  have hφ : ∀ x, D.f (φ' x) = exactNormalAut .E6 K a σ ε (D.f x) := by
    intro x
    rw [hφ'x, map_mul, map_mul, map_inv, hg0, hf1, hαe, MulAut.mul_apply, MulAut.conj_apply]
    group
  have hρg : Function.Bijective (ρ g0⁻¹) :=
    (Module.End.isUnit_iff _).1 ((Group.isUnit g0⁻¹).map ρ)
  have hρg1 : ρ g0 * ρ g0⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  let B' : (Fin m → k) ≃ₗ[k] (Fin m → k) :=
    LinearEquiv.ofBijective (ρ g0⁻¹ * B) (by rw [Module.End.mul_eq_comp]; exact hρg.comp hbij)
  have hB' : ∀ s v, ρ (φ' s) (B' v) = B' (ρ s v) := by
    intro s v
    have e1 : ∀ w, B' w = ρ g0⁻¹ (B w) := fun w => rfl
    rw [e1, e1, hφ'x, map_mul, map_mul]
    have e2 : ρ g0 (ρ g0⁻¹ (B v)) = B v := by
      have := congrArg (fun T : Module.End k (Fin m → k) => T (B v)) hρg1
      simpa using this
    show ρ g0⁻¹ (ρ (X1.conjAut L hb s) (ρ g0 (ρ g0⁻¹ (B v)))) = ρ g0⁻¹ (B (ρ s v))
    rw [e2]
    have := congrArg (fun T : Module.End k (Fin m → k) => T v) (hBρ s)
    simp only [Module.End.mul_apply] at this
    rw [this]
  obtain ⟨h1, h2⟩ := outer_type_L D hK hρ ht a σ ε φ' hφ B' hB'
  exact ⟨g, a, σ, ε, hαe, h1, h2⟩

end OuterParams

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
