module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerStatements
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64LagrangianCompletion
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneJhatComm

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}

variable {G : Type} [Group G]

namespace JBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {A D C E Dh : Subgroup G}

theorem ker_mem_D_of_sq (h : JBase τ lev z ν A D C E Dh) {j : G}
    (hj : j ∈ Dh ⊓ centralizer (E : Set G)) (hsq : j * z * (j * z) = 1) : j ∈ D := by
  refine (h.zt_E j (mem_inf.1 hj).1).1 ?_
  have hzinv := h.z_inv
  have hjz : (j * z)⁻¹ = j * z := inv_eq_of_mul_eq_one_right hsq
  have e : z⁻¹ * (j⁻¹ * z * j) = j * j := by
    have e1 : j⁻¹ = z * (j * z)⁻¹ := by group
    rw [e1, hjz, hzinv]
    calc z * (z * (j * z) * z * j) = (z * z) * j * (z * z) * j := by group
      _ = j * j := by rw [h.z_sq, mul_one, one_mul]
  rw [e]
  exact h.sq_mem_E hj

theorem ker_conj_z_mem_D (h : JBase τ lev z ν A D C E Dh) {x : G}
    (hxJ : x ∈ normalizer ((Dh ⊓ centralizer (E : Set G) : Subgroup G) : Set G))
    (hxDh : x ∈ normalizer (Dh : Set G)) : x * z * x⁻¹ ∈ D := by
  have htDh : x * z * x⁻¹ ∈ Dh := (mem_normalizer_iff.1 hxDh z).1 h.z_Dh
  have htJ : x * z * x⁻¹ ∉ Dh ⊓ centralizer (E : Set G) := fun ht =>
    h.z_not_mem_J ((mem_normalizer_iff.1 hxJ z).2 ht)
  rcases h.good_all htDh with h1 | h1
  · exact absurd h1 htJ
  · have e : x * z * x⁻¹ * z * z = x * z * x⁻¹ := by rw [mul_assoc _ z z, h.z_sq, mul_one]
    have hsq : x * z * x⁻¹ * z * z * (x * z * x⁻¹ * z * z) = 1 := by
      rw [e]
      calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
        _ = 1 := by rw [h.z_sq, mul_one, mul_inv_cancel]
    have hmem := h.ker_mem_D_of_sq h1 hsq
    rw [← e]
    exact mul_mem hmem h.z_D

theorem ker_conj_mem_C (h : JBase τ lev z ν A D C E Dh) {x : G}
    (hxE : ∀ j ∈ Dh ⊓ centralizer (E : Set G), x * j * x⁻¹ * j⁻¹ ∈ E) {c : G} (hc : c ∈ C) :
    x * c * x⁻¹ ∈ C := by
  have e : x * c * x⁻¹ = x * c * x⁻¹ * c⁻¹ * c := by group
  rw [e]
  exact mul_mem (h.E_C (hxE c (h.C_le_J hc))) hc

theorem ker_conj_mem_D (h : JBase τ lev z ν A D C E Dh) {x : G}
    (hxJ : x ∈ normalizer ((Dh ⊓ centralizer (E : Set G) : Subgroup G) : Set G))
    (hxDh : x ∈ normalizer (Dh : Set G))
    (hxE : ∀ j ∈ Dh ⊓ centralizer (E : Set G), x * j * x⁻¹ * j⁻¹ ∈ E) {d : G} (hd : d ∈ D) :
    x * d * x⁻¹ ∈ D := by
  rcases h.D_C d hd with h1 | h1
  · exact h.C_D (h.ker_conj_mem_C hxE h1)
  · have e : x * d * x⁻¹ = x * z * x⁻¹ * (x * (z * d) * x⁻¹) := by
      calc x * d * x⁻¹ = x * (z * z) * d * x⁻¹ := by rw [h.z_sq, mul_one]
        _ = x * z * x⁻¹ * (x * (z * d) * x⁻¹) := by group
    rw [e]
    exact mul_mem (h.ker_conj_z_mem_D hxJ hxDh) (h.C_D (h.ker_conj_mem_C hxE h1))

theorem ker_inv {J E : Subgroup G} {x : G} (hxJ : x ∈ normalizer (J : Set G))
    (hxE : ∀ j ∈ J, x * j * x⁻¹ * j⁻¹ ∈ E) : ∀ j ∈ J, x⁻¹ * j * x⁻¹⁻¹ * j⁻¹ ∈ E := by
  intro j hj
  have hj' : x⁻¹ * j * x⁻¹⁻¹ ∈ J := (mem_normalizer_iff.1 (inv_mem hxJ) j).1 hj
  have h1 := inv_mem (hxE _ hj')
  have e : (x * (x⁻¹ * j * x⁻¹⁻¹) * x⁻¹ * (x⁻¹ * j * x⁻¹⁻¹)⁻¹)⁻¹ = x⁻¹ * j * x⁻¹⁻¹ * j⁻¹ := by
    group
  rwa [e] at h1

theorem ker_mem_normalizer_D (h : JBase τ lev z ν A D C E Dh) {x : G}
    (hxJ : x ∈ normalizer ((Dh ⊓ centralizer (E : Set G) : Subgroup G) : Set G))
    (hxDh : x ∈ normalizer (Dh : Set G))
    (hxE : ∀ j ∈ Dh ⊓ centralizer (E : Set G), x * j * x⁻¹ * j⁻¹ ∈ E) :
    x ∈ normalizer (D : Set G) := by
  refine mem_normalizer_iff.2 fun d => ⟨fun hd => h.ker_conj_mem_D hxJ hxDh hxE hd, fun hd => ?_⟩
  have := h.ker_conj_mem_D (inv_mem hxJ) (inv_mem hxDh) (ker_inv hxJ hxE) hd
  have e : x⁻¹ * (x * d * x⁻¹) * x⁻¹⁻¹ = d := by group
  rwa [e] at this

theorem ker_mem_J (h : JBase τ lev z ν A D C E Dh) (hCE : ¬ C ≤ E) {x : G} (hx : x ∈ Dh)
    (hxE : ∀ j ∈ Dh ⊓ centralizer (E : Set G), x * j * x⁻¹ * j⁻¹ ∈ E) :
    x ∈ Dh ⊓ centralizer (E : Set G) := by
  rcases h.good_all hx with h1 | h1
  · exact h1
  exfalso
  apply hCE
  have hzinv := h.z_inv
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ Dh ⊓ centralizer (E : Set G), x = y * z :=
    ⟨x * z, h1, by rw [mul_assoc, h.z_sq, mul_one]⟩
  have hzE : ∀ j ∈ Dh ⊓ centralizer (E : Set G), z * j * z⁻¹ * j⁻¹ ∈ E := by
    intro j hj
    have he₁ := hxE j hj
    have e2 : z * j * z⁻¹ * j⁻¹ = y⁻¹ * (y * z * j * (y * z)⁻¹ * j⁻¹) * y *
        (y⁻¹ * j * y * j⁻¹) := by
      group
    rw [e2, mul_assoc y⁻¹, comm_of_J hy he₁, inv_mul_cancel_left]
    refine mul_mem he₁ ?_
    have := h.comm_mem_E hy (inv_mem hj)
    rwa [inv_inv] at this
  have hJD : Dh ⊓ centralizer (E : Set G) ≤ D := by
    intro j hj
    refine (h.zt_E j (mem_inf.1 hj).1).1 ?_
    have := hzE _ (inv_mem hj)
    have e : z * j⁻¹ * z⁻¹ * j⁻¹⁻¹ = z⁻¹ * (j⁻¹ * z * j) := by
      rw [inv_inv, hzinv]
      group
    rwa [e] at this
  have hDhD : Dh ≤ D := by
    rw [← h.J_sup_z]
    exact sup_le hJD (zpowers_le.2 h.z_D)
  intro c hc
  obtain ⟨t, ht, htc⟩ := h.zt_surj c hc
  have hzt := (h.zt_E t ht).2 (hDhD ht)
  have e : c = z⁻¹ * (t⁻¹ * z * t) * ((z⁻¹ * (t⁻¹ * z * t))⁻¹ * c) := by group
  rw [e]
  exact mul_mem hzt htc

end JBase

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem epsOne_jhat_kernel (hQ : EpsOneLagrangianNormalizerStmt)
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
      ∀ x ∈ normalizer (Jh : Set G), x ∈ normalizer (Dhat₂ : Set G) →
        (∀ j ∈ Jh, x * j * x⁻¹ * j⁻¹ ∈ sp6E₂ φ he z) → x ∈ Jh := by
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
  obtain ⟨-, -, -, hQC, hQE, hκadd, hκ0, hκsurj, hκz, -, ⟨Ψ, -, -, hΨκ, hΨlev, -, hΨDh, -⟩, -, -,
    hDDh, hDhcard, hzt, hztmul, hztE, hztsurj, hztlev, hCDh, hcen, -⟩ :=
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
  intro x hxJ hxDh hxE
  have hxQ : x ∈ Q₂ := hJ.ker_mem_normalizer_D hxJ hxDh hxE
  have hfix : ∀ w : Fin 3 → ZMod 2, ((Ψ ⟨x, hxQ⟩).right : M₃) *ᵥ w = w := by
    intro w
    obtain ⟨d, hd, hκd⟩ := hκsurj (0, w)
    have hdC : d ∈ sp6C₂ φ he z := by
      by_contra hdC
      have := congrArg Prod.fst hκd
      simp only [hdC, ↓reduceIte] at this
      exact absurd this (by decide)
    have he₁ : x * d * x⁻¹ * d⁻¹ ∈ sp6E₂ φ he z := hxE d (hJ.C_le_J hdC)
    have hκ1 := hΨκ ⟨x, hxQ⟩ d hd
    have e : x * d * x⁻¹ = x * d * x⁻¹ * d⁻¹ * d := by group
    rw [e, hκadd _ (hJ.E_D he₁) _ hd, (hκ0 _ (hJ.E_D he₁)).2 he₁, zero_add, hκd] at hκ1
    have h3 := congrArg Prod.snd hκ1
    simp only [aglLin, zero_smul, add_zero] at h3
    exact h3.symm
  have hright : (Ψ ⟨x, hxQ⟩).right = 1 :=
    Units.ext (Matrix.ext_iff_mulVec.2 fun w => by rw [hfix w, Units.val_one, one_mulVec])
  have hxDh' : x ∈ Dhat₂ := (hΨDh ⟨x, hxQ⟩).2 hright
  have hCE : ¬ sp6C₂ φ he z ≤ sp6E₂ φ he z := fun hle =>
    hC₂ (elemAbelian_of_sq_eq_one fun c hc => by rw [pow_two]; exact hJ.E_sq c (hle hc))
  exact hJ.ker_mem_J hCE hxDh' hxE

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
