module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneCoordsDefs
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerStatements
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64LagrangianCompletion
import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneJhat
import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneECoordsSq

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise


local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem epsOne_ecoords (hQ : EpsOneLagrangianNormalizerStmt)
    {G : Type} [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (normalizer ((pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔
        zpowers z : Subgroup G) : Set G)) z =
      z • (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G)) :
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let τ : ↥(binarySymMatrices 3) → G := fun B => tauHom φ he (Multiplicative.ofAdd B)
    let θ₂ : ↥(binarySymMatrices 3) × ZMod 2 → G := fun x => τ x.1 * z ^ x.2.val
    let θ₁ : (E × ZMod 2) × ZMod 2 → G := fun x =>
      ((φ.symm (n x.1.1 (x.1.2 + Q x.1.1)) : L) : G) * z ^ x.2.val
    let A₂ := pullSub φ (pointwiseStabilizer b (lagrangianOf e))
    let R₂ := A₂ ⊔ zpowers z
    let N₂ := normalizer (R₂ : Set G)
    let D₂ := CFSG.Assembly.pCoreOf 2 N₂
    let A₁ := pullSub φ (pointRadical b hb u f)
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    ∀ κ₂ lam : ZMod 2,
      (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2), d⁻¹ * z * d = θ₂ (C, 1) →
        d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C, ε)) →
      (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
        d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
      lam = 1 → ¬ IsElementaryAbelian 2 (sp6C₂ φ he z) →
      let Q₂ := normalizer (D₂ : Set G)
      let Dhat₂ := CFSG.Assembly.pCoreOf 2 Q₂
      let Jh := Dhat₂ ⊓ centralizer (sp6E₂ φ he z : Set G)
      ∀ cV : G → (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2),
        EpsOneVCoords Jh (sp6E₂ φ he z) (sp6C₂ φ he z) z (leviHom φ he)
          (fun c => symThreeDiag (sp6ν₂ φ he z c : M₃)) cV →
        ∃ (u : Bool) (cE : G → M₃), EpsOneECoords Jh (sp6E₂ φ he z) cV u cE := by
  intro u f E n Q r τ θ₂ θ₁ A₂ R₂ N₂ D₂ A₁ B₁ N₁ D₁ κ₂ lam h₂ h₁ hlam hC₂ Q₂ Dhat₂ Jh cV hcV
  obtain ⟨-, hJD, hJz, -, -, -⟩ := epsOne_jhat_structure hQ hG hL hLn hZ hmodel T hT hzT hz hH
    hb hnd hV φ e he hfull κ₂ lam h₂ h₁ hlam hC₂
  have hJD' : Jh ⊓ D₂ = sp6C₂ φ he z := hJD
  have hJz' : Jh ⊔ zpowers z = Dhat₂ := hJz
  obtain ⟨-, C₁, E₂', h4'⟩ := standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion
    hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull κ₂ lam h₂ h₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE₂N, hE₂F, hE₂c, hE₂card, hE₂uniq,
    hE₂sq, -, -, -, -, -, -, -, -, hE₂C₂, -, -, -, -, -, ν, ε, hνz, -, -, -, -, hδsurj, hδE, -,
    hCform, hε0, -, -, -⟩ := h4'
  have hspec := Classical.epsilon_spec (p := fun E : Subgroup G =>
    (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512) ⟨E₂', hE₂F, hE₂c, hE₂card⟩
  have hE : E₂' = sp6E₂ φ he z := (hE₂uniq _ hspec.1 hspec.2.1 hspec.2.2).symm
  subst hE
  have hε : ε = 1 := by
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) ε with h | h
    · exact absurd (elemAbelian_of_sq_eq_one (hε0 h).1) hC₂
    · exact h
  subst hε
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzN : z ∈ N₂ := le_normalizer (mem_sup_right (mem_zpowers z))
  have hzDh : z ∈ Dhat₂ := by
    rw [← hJz']
    exact mem_sup_right (mem_zpowers z)
  have hCD : ∀ c ∈ sp6C₂ φ he z, c ∈ D₂ := fun c hc => (mem_inf.1 hc).1
  have hCJ : sp6C₂ φ he z ≤ Jh := fun c hc => by
    rw [← hJD'] at hc
    exact (mem_inf.1 hc).1
  have hνeq : ∀ d ∈ D₂, sp6ν₂ φ he z d = ν d := fun d hd => by
    have hs := Classical.epsilon_spec (p := fun B : ↥(binarySymMatrices 3) =>
      z⁻¹ * (d⁻¹ * z * d) = tauHom φ he (Multiplicative.ofAdd B)) ⟨ν d, hνz d hd⟩
    exact tauHom_injective φ he (hs.symm.trans (hνz d hd))
  have hsq1 : ∀ w, symThreeSquare 1 w = ECoords.sqS w := fun w =>
    Subtype.ext (one_smul (ZMod 2) _)
  have hpol1 : ∀ w v, symThreeSquarePolar 1 w v = symThreePolarSym w v := fun w v =>
    Subtype.ext (one_smul (ZMod 2) _)
  have hbase : ECoords.ECBase (tauHom φ he) (leviHom φ he) z (sp6ν₂ φ he z) (sp6C₂ φ he z)
      (sp6E₂ φ he z) Jh cV :=
    { vc := hcV
      τ_inj := tauHom_injective φ he
      lev_τ := fun g B => leviHom_conj_tauHom φ he g B
      C_Jh := hCJ
      E_Jh := hE₂C₂.trans hCJ
      E_sq := fun x hx => by rw [← pow_two]; exact hE₂sq x hx
      E_cent := fun x hx e' he' => (mem_centralizer_iff.1 (mem_inf.1 hx).2 e' he').symm
      card_E := hE₂card
      z_Jh := fun x hx => by
        refine mem_inf.2 ⟨mul_mem (mul_mem hzDh (mem_inf.1 hx).1) (inv_mem hzDh), ?_⟩
        refine mem_centralizer_iff.2 fun e' he' => ?_
        have hm : z⁻¹ * e' * z⁻¹⁻¹ ∈ sp6E₂ φ he z := hE₂N z⁻¹ (inv_mem hzN) e' he'
        rw [inv_inv] at hm
        have hc := mem_centralizer_iff.1 (mem_inf.1 hx).2 _ hm
        calc e' * (z * x * z⁻¹) = z * (z⁻¹ * e' * z * x) * z⁻¹ := by group
          _ = z * (x * (z⁻¹ * e' * z)) * z⁻¹ := by rw [hc]
          _ = z * x * z⁻¹ * e' := by group
      z_E := fun e' he' => by
        have heD : e' ∈ D₂ := hCD e' (hE₂C₂ he')
        have heinv : e'⁻¹ = e' :=
          inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hE₂sq e' he')
        refine ⟨ν e', (hδE e' (hE₂C₂ he')).2 he', ?_⟩
        have h1 := hνz e' heD
        beta_reduce at h1
        rw [hzinv, heinv] at h1
        rw [hzinv, heinv, ← h1]
        group
      C_sq := fun c hc => by
        rw [hνeq c (hCD c hc), ← pow_two, (hCform c hc c hc).1]
        beta_reduce
        rw [ZMod.val_zero, pow_zero, mul_one, hsq1]
      C_comm := fun c hc d hd => by
        rw [hνeq c (hCD c hc), hνeq d (hCD d hd), (hCform c hc d hd).2]
        beta_reduce
        rw [ZMod.val_zero, pow_zero, mul_one, hpol1]
      δ_surj := fun w => by
        obtain ⟨c, hc, hcw⟩ := hδsurj w
        exact ⟨c, hc, by rw [hνeq c (hCD c hc), hcw]⟩ }
  exact hbase.exists_ecoords

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
