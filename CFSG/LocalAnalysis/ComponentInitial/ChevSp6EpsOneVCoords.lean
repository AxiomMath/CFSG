module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerStatements
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64LagrangianCompletion
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneCoordsDefs
public import Certificates.Certificate3362
import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneVCoordsBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise


local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)


theorem epsOne_vcoords (hQ : EpsOneLagrangianNormalizerStmt)
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
      ∃ cV, EpsOneVCoords Jh (sp6E₂ φ he z) (sp6C₂ φ he z) z (leviHom φ he)
        (fun c => symThreeDiag (sp6ν₂ φ he z c : M₃)) cV := by
  intro u f E n Q r τ θ₂ θ₁ A₂ R₂ N₂ D₂ A₁ B₁ N₁ D₁ κ₂ lam h₂ h₁ hlam hC₂ Q₂ Dhat₂ Jh
  have hzC : z ∈ centralizer (L : Set G) := map_subtype_le _ hzT
  obtain ⟨-, C₁, E₂', h4'⟩ := standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion
    hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull κ₂ lam h₂ h₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE₂F, hE₂c, hE₂card, hE₂uniq, hE₂sq,
    hA₂E₂, -, -, -, -, hDzC, -, -, hE₂C₂, -, -, -, -, -, ν, ε, hνz, hνmul, hνsurj, hνA, hνlev,
    -, hδE, -, -, hε0, hε1, -, -⟩ := h4'
  have hspec := Classical.epsilon_spec (p := fun E : Subgroup G =>
    (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512) ⟨E₂', hE₂F, hE₂c, hE₂card⟩
  have hE : E₂' = sp6E₂ φ he z := (hE₂uniq _ hspec.1 hspec.2.1 hspec.2.2).symm
  subst hE
  have hε : ε = 1 := by
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) ε with h | h
    · exact absurd (elemAbelian_of_sq_eq_one (hε0 h).1) hC₂
    · exact h
  obtain ⟨hexp, hAsq, -⟩ := hε1 hε
  have hlam1 : ∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
      d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (b (a.1 : V) (v.1 : V)) • r + ε • a, ε) := by
    intro d hd a v ε' hda
    have := h₁ d hd a v ε' hda
    rwa [hlam, one_mul] at this
  obtain ⟨-, hν₂, -, hQC, hQE, -, -, -, hκz, -, ⟨Ψ, -, -, -, hΨlev, -⟩, -, -, hDDh, hDhcard,
    hzt, hztmul, hztE, hztsurj, hztlev, hCDh, hcen, -⟩ :=
    hQ G hG L hL hLn hZ hmodel T hT z hzT hz hH V b hb hnd hV φ e he hfull hlam1 hexp
  have hlevQ : ∀ g : GL (Fin 3) (ZMod 2), leviHom φ he g ∈ Q₂ := fun g => by
    obtain ⟨hg, -⟩ := hΨlev g
    exact hg
  have hDhQ : Dhat₂ ≤ Q₂ := pCoreOf_le 2 Q₂
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzD : z ∈ D₂ :=
    (Set.ext_iff.1 hDzC z).2 ⟨z, mem_zpowers z, 1, one_mem _, mul_one z⟩
  have hzC₂ : z ∉ sp6C₂ φ he z := by
    intro hzc
    have h1 := congrArg Prod.fst (hκz 1 1 (one_mem _))
    have hv : (1 : ZMod 2).val = 1 := rfl
    simp only [hv, pow_one, mul_one, hzc, ↓reduceIte] at h1
    exact absurd h1 (by decide)
  have hDC : ∀ d ∈ D₂, d ∈ sp6C₂ φ he z ∨ z * d ∈ sp6C₂ φ he z := by
    intro d hd
    obtain ⟨t, ht, c, hc, rfl⟩ := (Set.ext_iff.1 hDzC d).1 hd
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
    have hk : z ^ k = z ^ (k % 2) := by
      rw [← zpow_mod_orderOf z k, hz]
      norm_num
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · left
      change z ^ k * c ∈ sp6C₂ φ he z
      rw [hk, h0, zpow_zero, one_mul]
      exact hc
    · right
      change z * (z ^ k * c) ∈ sp6C₂ φ he z
      rw [hk, h0, zpow_one, ← mul_assoc, hz2, one_mul]
      exact hc
  have hJ : Jhat.JBase (tauHom φ he) (leviHom φ he) z ν A₂ D₂ (sp6C₂ φ he z) (sp6E₂ φ he z)
      Dhat₂ :=
    { τ_inj := tauHom_injective φ he
      mem_A := fun a => mem_pullSub_iff φ he
      lev_τ := fun g B => leviHom_conj_tauHom φ he g B
      lev_z := fun g => mul_comm_z hzC (leviHom_mem φ he g)
      z_sq := hz2
      z_D := hzD
      z_C := hzC₂
      D_C := hDC
      C_eq := rfl
      E_C := hE₂C₂
      A_E := hA₂E₂
      E_sq := fun x hx => by rw [← pow_two]; exact hE₂sq x hx
      zcomm := hνz
      ν_mul := hνmul
      ν_A := hνA
      ν_E := hδE
      ν_surj := hνsurj
      ν_lev := hνlev
      A_sq := hAsq
      D_Dh := hDDh
      Dh_card := hDhcard
      Dh_E := fun t ht x hx => hQE t (hDhQ ht) x hx
      lev_Dh := fun g t ht => conj_mem_pCoreOf 2 (hlevQ g) ht
      zt_C := hzt
      zt_mul := hztmul
      zt_E := hztE
      zt_surj := hztsurj
      zt_lev := fun g t ht => hztlev _ (hlevQ g) t ht
      C_Dh := fun c hc t ht => (hcen c (hCDh hc)).2 hc t ht }
  obtain ⟨cV, hcV⟩ := hJ.vc_exists
  have hνeq : ∀ c ∈ sp6C₂ φ he z, sp6ν₂ φ he z c = ν c := fun c hc =>
    Multiplicative.ofAdd.injective
      (tauHom_injective φ he ((hν₂ c (hJ.C_D hc)).symm.trans (hνz c (hJ.C_D hc))))
  exact ⟨cV, { hcV with on_C₂ := fun c hc => by rw [hcV.on_C₂ c hc, hνeq c hc] }⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
