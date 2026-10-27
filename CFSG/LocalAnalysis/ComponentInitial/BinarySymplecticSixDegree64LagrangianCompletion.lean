module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64CentralPointExclusion
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64MiddleSubgroupFull
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64CentralLiftFull
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64CompletionCommon
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64CentralAlternatives
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NoncentralAlternatives

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion
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
    let I₂ : Set G := {x | ∃ B : ↥(binarySymMatrices 3), symThreeDiag (B : M₃) = 0 ∧ τ B = x}
    let F₂ : Set G := {d | d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ I₂}
    let A₁ := pullSub φ (pointRadical b hb u f)
    let b₁ : G := ((φ.symm (n 0 1) : L) : G)
    let I₁ := zpowers b₁
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    let F₁ : Set G := {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ I₁}
    let J := A₁ ⊓ A₂
    let J₀ : Set G := (A₁ : Set G) ∩ I₂
    ∀ κ₂ lam : ZMod 2,
      (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2), d⁻¹ * z * d = θ₂ (C, 1) →
        d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C, ε)) →
      (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
        d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
      κ₂ = 0 ∧ ∃ C₁ E₂ : Subgroup G,
        let E₁ : Set G := (C₁ : Set G) ∩ F₁
        let K₀ := C₁ ⊓ D₂
        let M : Set G := (C₁ : Set G) ∩ F₂
        let C₂ := D₂ ⊓ centralizer (E₂ : Set G)
        let Z₁ := (center C₁).map C₁.subtype
        C₁ ≤ D₁ ∧ (∀ m ∈ N₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁) ∧ Nat.card C₁ = 1024 ∧
        zpowers z ⊔ C₁ = D₁ ∧ C₁ ⊓ B₁ = A₁ ∧ closure {x | ∃ y ∈ C₁, y ^ 2 = x} ≤ I₁ ∧
        Nat.card ↥E₁ = 64 ∧ Nat.card J = 8 ∧ Nat.card ↥J₀ = 4 ∧
        (J : Set G) = (I₁ : Set G) * J₀ ∧ (I₁ : Set G) ∩ J₀ = {1} ∧
        Nat.card K₀ = 64 ∧ Nat.card ↥M = 32 ∧ (∀ k ∈ K₀, ∀ k' ∈ K₀, k * k' = k' * k) ∧
        conjClass K₀ z = z • (J : Set G) ∧ ⁅K₀, A₂⁆ = ⊥ ∧
        (∀ m ∈ N₂, ∀ x ∈ E₂, m * x * m⁻¹ ∈ E₂) ∧ (E₂ : Set G) ⊆ F₂ ∧ IsMulCommutative E₂ ∧
        Nat.card E₂ = 512 ∧
        (∀ E' : Subgroup G, (E' : Set G) ⊆ F₂ → IsMulCommutative E' → Nat.card E' = 512 →
          E' = E₂) ∧
        (∀ x ∈ E₂, x ^ 2 = 1) ∧ A₂ ≤ E₂ ∧ F₂ = (zpowers z : Set G) * (E₂ : Set G) ∧
        E₂ ⊓ R₂ = A₂ ∧
        (∀ m ∈ N₂, ∀ c ∈ C₂, m * c * m⁻¹ ∈ C₂) ∧ Nat.card C₂ = 4096 ∧
        (D₂ : Set G) = (zpowers z : Set G) * (C₂ : Set G) ∧ C₂ ⊓ R₂ = A₂ ∧
        (C₂ : Set G) ∩ F₂ = E₂ ∧ E₂ ≤ C₂ ∧ (∀ x ∈ E₂, ∀ c ∈ C₂, x * c = c * x) ∧
        C₁ ⊓ C₂ = K₀ ∧ (C₁ : Set G) ∩ E₂ = M ∧
        (∀ x ∈ A₂ ⊔ K₀, ∀ y ∈ A₂ ⊔ K₀, x * y = y * x) ∧ Nat.card (A₂ ⊔ K₀ : Subgroup G) = 512 ∧
        ∃ (ν₂ : G → ↥(binarySymMatrices 3)) (ε : ZMod 2),
          (∀ d ∈ D₂, z⁻¹ * (d⁻¹ * z * d) = τ (ν₂ d)) ∧
          (∀ c ∈ C₂, ∀ c' ∈ C₂, ν₂ (c * c') = ν₂ c + ν₂ c') ∧
          (∀ B : ↥(binarySymMatrices 3), ∃ c ∈ C₂, ν₂ c = B) ∧ (∀ c ∈ C₂, ν₂ c = 0 ↔ c ∈ A₂) ∧
          (∀ (g : GL (Fin 3) (ZMod 2)), ∀ c ∈ C₂,
            leviHom φ he g * c * (leviHom φ he g)⁻¹ ∈ C₂ ∧
            ν₂ (leviHom φ he g * c * (leviHom φ he g)⁻¹) = symThreeCongr g (ν₂ c)) ∧
          (∀ w : Fin 3 → ZMod 2, ∃ c ∈ C₂, symThreeDiag (ν₂ c : M₃) = w) ∧
          (∀ c ∈ C₂, symThreeDiag (ν₂ c : M₃) = 0 ↔ c ∈ E₂) ∧
          (∀ (g : GL (Fin 3) (ZMod 2)), ∀ c ∈ C₂,
            symThreeDiag (ν₂ (leviHom φ he g * c * (leviHom φ he g)⁻¹) : M₃) =
              (g : M₃) *ᵥ symThreeDiag (ν₂ c : M₃)) ∧
          (∀ c ∈ C₂, ∀ d ∈ C₂,
            c ^ 2 = θ₂ (symThreeSquare ε (symThreeDiag (ν₂ c : M₃)), 0) ∧
            c⁻¹ * d⁻¹ * c * d =
              θ₂ (symThreeSquarePolar ε (symThreeDiag (ν₂ c : M₃)) (symThreeDiag (ν₂ d : M₃)),
                0)) ∧
          (ε = 0 → (∀ c ∈ C₂, c ^ 2 = 1) ∧ (∀ c ∈ C₂, ∀ d ∈ C₂, c * d = d * c) ∧
            (center C₂).map C₂.subtype = C₂) ∧
          (ε = 1 → Monoid.exponent C₂ = 4 ∧ closure {x | ∃ c ∈ C₂, c ^ 2 = x} = A₂ ∧
            ((⁅C₂, C₂⁆ : Subgroup G) : Set G) = I₂ ∧ (center C₂).map C₂.subtype = E₂ ∧
            ∀ c ∈ C₂, c ^ 2 = 1 ↔ c ∈ E₂) ∧
          (lam = 0 →
            (∀ x ∈ E₁, ∀ y ∈ C₁, x * y = y * x) ∧
            (∀ c ∈ C₁, ∀ v : E × ZMod 2, z⁻¹ * (c⁻¹ * z * c) = θ₁ (v, 0) →
              c ^ 2 = θ₁ ((ε * (Q v.1 + v.2)) • r, 0)) ∧
            (ε = 0 → (∀ c ∈ C₁, c ^ 2 = 1) ∧ (∀ c ∈ C₁, ∀ d ∈ C₁, c * d = d * c) ∧ Z₁ = C₁) ∧
            (ε = 1 → ⁅C₁, C₁⁆ = I₁ ∧ closure {x | ∃ y ∈ C₁, y ^ 2 = x} = I₁ ∧
              (Z₁ : Set G) = E₁ ∧
              Nonempty (↥(center C₁) ≃* Multiplicative (ZMod 4 × (Fin 4 → ZMod 2)))) ∧
            ∃ e₀ ∈ E₁, e₀ ∈ D₂ ∧ z⁻¹ * (e₀⁻¹ * z * e₀) = b₁ ∧ e₀ ^ 2 = b₁ ^ ε.val ∧
              (K₀ : Set G) = M * (zpowers e₀ : Set G) ∧
              E₁ ∩ (C₂ : Set G) = (J : Set G) * (zpowers e₀ : Set G)) ∧
          (lam = 1 →
            ⁅C₁, C₁⁆ = I₁ ∧ closure {x | ∃ y ∈ C₁, y ^ 2 = x} = I₁ ∧
            Nat.card (center C₁) = 4 ∧ Z₁ ⊓ A₁ = I₁ ∧ E₁ = ((A₁ ⊔ Z₁ : Subgroup G) : Set G) ∧
            Z₁ ≤ C₂ ∧ (K₀ : Set G) = M * (Z₁ : Set G) ∧
            E₁ ∩ (C₂ : Set G) = (J : Set G) * (Z₁ : Set G) ∧
            (ε = 0 → Nonempty (↥(center C₁) ≃* Multiplicative (ZMod 2 × ZMod 2))) ∧
            (ε = 1 → Nonempty (↥(center C₁) ≃* Multiplicative (ZMod 4))) ∧
            closure {x | ∃ y ∈ Z₁, y ^ 2 = x} = zpowers (b₁ ^ ε.val)) := by
  obtain ⟨-, hzC, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, hσsurj, hσker, hσcol, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ, D₂, F₂', ν₂, hD₂, hFD₂, hD₂N, hRF₂, hD₂n, hF₂'n, -, -, hν₂z, hν₂eq, hν₂surj, hact₂,
    hF₂'mem, hprod₂, hD₂H, -, -, hfaith₂⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  have hRD₂ := hRF₂.trans hFD₂
  obtain ⟨-, hfull₁⟩ := degree64_point_fusion_of_lagrangian he hb hnd φ hzC hsup hinf hz hV hD₂N
    hD₂n hν₂z hν₂eq hν₂surj hact₂
  obtain ⟨lam₀, D₁, F₁, ν₁, hD₁, hFD₁, hD₁N, hBF₁, hD₁n, -, hD₁c, -, -, -, -, hν₁z, -, hν₁surj,
    hact₁, -, hprod₁, hD₁H, -, hb₁c, -, -, -, -, -, -, ⟨hγD₁, -, hF₁mem, -⟩, -, -⟩ :=
    degree64_point_two_group he hb hnd φ hzC hsup hinf hz hfull₁
  have hBD₁ := hBF₁.trans hFD₁
  obtain ⟨F₂, E₂, hF₂, hE₂F, hE₂c, hE₂card, hE₂uniq, hF₂zE, hE₂R, hF₂sq, hY⟩ :=
    degree64_middle_subgroup_full he φ hzC hinf hz hD₂N hD₂n hν₂surj hact₂ hRD₂ hfaith₂
  have h3 :=
    standard_binary_symplectic_six_degree64_central_point_action_excludes_noncentral_lagrangian
      hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull
  subst hD₂ hD₁
  obtain ⟨-, hmain3, -, -, htrans⟩ := h3
  set D₁ := CFSG.Assembly.pCoreOf 2 (normalizer ((ptSub φ z hb e : Subgroup G) : Set G))
    with hD₁def
  set D₂ := CFSG.Assembly.pCoreOf 2 (normalizer ((radSub φ z e : Subgroup G) : Set G))
    with hD₂def
  have hpure : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + ε • ν₂ d, ε)) :=
    fun d hd B ε => htrans d hd (ν₂ d) B ε (hν₂z d hd)
  have hκ : ∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) →
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ • symThreePolarSym
          (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε)) := by
    intro d hd C B ε h
    have h1 := Multiplicative.ofAdd.injective
      (radHom_injective φ he hzC hz hinf ((hν₂z d hd).symm.trans h))
    have h2 : ν₂ d = C := congrArg Prod.fst h1
    rw [← h2]
    exact hact₂ d hd B ε
  have hKz : ∀ j ∈ pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ⊓
      pullSub φ (pointwiseStabilizer b (lagrangianOf e)), ∃ k ∈ D₁ ⊓ D₂,
        k⁻¹ * z * k = z * j := fun j hj =>
    exists_mem_inf_conj_eq he hb hnd φ hzC hsup hinf hz hD₂N hD₂n hν₂z hν₂eq hν₂surj hact₂ hRD₂
      hD₁n hBD₁ hν₁z hact₁ hprod₁ hj
  have hF₁ : ∀ d : G, d ∈ F₁ ↔ d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz) :=
    fun d => ⟨fun h => ⟨hFD₁ h, (hF₁mem d (hFD₁ h)).2 h⟩, fun h => (hF₁mem d h.1).1 h.2⟩
  have hF₂eq : F₂ = F₂' := by
    ext d
    rw [hF₂, hF₂'mem]
    refine and_congr_right fun hd => ?_
    rw [← tauHom_nu he φ hzC hz hν₂z hd]
    constructor
    · rintro ⟨B, hB, hBx⟩
      rw [← Multiplicative.ofAdd.injective (tauHom_injective φ he hBx)]
      exact hB
    · intro h
      exact ⟨_, h, rfl⟩
  have hF₂n : ∀ m ∈ normalizer ((radSub φ z e : Subgroup G) : Set G), ∀ x ∈ F₂,
      m * x * m⁻¹ ∈ F₂ := by
    rw [hF₂eq]
    exact hF₂'n
  have hb₁eq := ptB₁_eq he hb φ hzC hz
  intro u f E n Q r τ θ₂ θ₁ A₂ R₂ N₂ D₂' I₂ F₂s A₁ b₁ I₁ B₁ N₁ D₁' F₁s J J₀ κ₂ lam hκ₂ hlam
  have hb₁' : ptB₁ he hb φ hzC hz = b₁ := hb₁eq
  have hκ₂' : ∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) →
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε)) :=
    fun d hd C B ε h => hκ₂ d hd C B ε h
  have hact₁' : ∀ d ∈ D₁, ∀ (v : (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) × ZMod 2)
      (ε : ZMod 2), d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) •
          ((0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))), (1 : ZMod 2)) + ε • ν₁ d, ε)) :=
    fun d hd v ε => hlam d hd (ν₁ d) v ε (hν₁z d hd)
  have hκ₂0 : κ₂ = 0 := (hmain3 κ₂ lam hκ₂ hlam).1
  obtain ⟨C₁, g, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hcl, hgC, hgD₂, hgz, hgcen, hdata₀, hdata₁⟩ :
      ∃ (C₁ : Subgroup G) (g : G), C₁ ≤ D₁ ∧
        (∀ m ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G), ∀ c ∈ C₁,
          m * c * m⁻¹ ∈ C₁) ∧
        Nat.card C₁ = 1024 ∧ zpowers z ⊔ C₁ = D₁ ∧
        C₁ ⊓ ptSub φ z hb e = pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ∧
        closure {x | ∃ y ∈ C₁, y ^ 2 = x} ≤ zpowers (ptB₁ he hb φ hzC hz) ∧
        g ∈ C₁ ∧ g ∈ D₂ ∧ z⁻¹ * (g⁻¹ * z * g) = ptB₁ he hb φ hzC hz ∧
        (∀ c ∈ C₁, g * c = c * g) ∧
        (lam = 0 → ∃ (τ₁ : G → (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) × ZMod 2)
          (β : ZMod 2),
          (∀ c ∈ C₁, z⁻¹ * c⁻¹ * z * c =
            ptHom he hb φ hzC hz (Multiplicative.ofAdd (τ₁ c, 0))) ∧
          (∀ c ∈ C₁, ∀ c' ∈ C₁, τ₁ (c * c') = τ₁ c + τ₁ c') ∧
          (∀ v, ∃ c ∈ C₁, τ₁ c = v) ∧
          (∀ c ∈ C₁, τ₁ c = 0 ↔
            c ∈ pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))) ∧
          (∀ c ∈ C₁, c ^ 2 = ptHom he hb φ hzC hz (Multiplicative.ofAdd
            ((β * OddQuadraticFive.qV (ptQuad e) (τ₁ c)) • OddQuadraticFive.rV, 0))) ∧
          ⁅C₁, C₁⁆ ≤ zpowers (ptB₁ he hb φ hzC hz) ∧
          (∀ x ∈ C₁, z⁻¹ * (x⁻¹ * z * x) ∈ zpowers (ptB₁ he hb φ hzC hz) →
            ∀ y ∈ C₁, x * y = y * x) ∧
          Nat.card ↥((C₁ : Set G) ∩ {d | d ∈ D₁ ∧
            z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)}) = 64 ∧
          τ₁ g = ((0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))), (1 : ZMod 2))) ∧
        (lam = 1 → ⁅C₁, C₁⁆ = zpowers (ptB₁ he hb φ hzC hz) ∧
          closure {x | ∃ y ∈ C₁, y ^ 2 = x} = zpowers (ptB₁ he hb φ hzC hz) ∧
          Nat.card (center C₁) = 4 ∧
          (C₁ : Set G) ∩ {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)} =
            ((pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ⊔
              (center C₁).map C₁.subtype : Subgroup G) : Set G) ∧
          (center C₁).map C₁.subtype ⊓ ptSub φ z hb e ≤ zpowers (ptB₁ he hb φ hzC hz) ∧
          (center C₁).map C₁.subtype ≤ D₂ ∧
          g ∈ (center C₁).map C₁.subtype ∧ g ∉ ptSub φ z hb e) := by
    rcases zmod_two_eq_zero_or_eq_one lam with h0 | h1
    · obtain ⟨-, C₁, τ₁, β, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hτz, hτmul, hτsurj, hτker, hsq, hCC,
        hsq₀, hEc, hEcard, e₀, he₀C, he₀τ, -, he₀D₂⟩ :=
        degree64_central_lift_full he hb hnd φ hzC hsup hinf hz σ hσ hσcol hσker h0 hD₁N hD₁n
          hBD₁ hD₁H hν₁z hν₁surj hact₁' hprod₁ hb₁c hD₂N hD₂n hν₂z hν₂eq hν₂surj hact₂ hRD₂ hprod₂
          hκ₂'
      have he₀z : z⁻¹ * (e₀⁻¹ * z * e₀) = ptB₁ he hb φ hzC hz := by
        have h := hτz e₀ he₀C
        rw [he₀τ] at h
        rw [ptB₁, ← h]
        group
      refine ⟨C₁, e₀, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hsq₀, he₀C, he₀D₂, he₀z,
        fun c hc => hEc e₀ he₀C (by rw [he₀z]; exact mem_zpowers _) c hc,
        fun _ => ⟨τ₁, β, hτz, hτmul, hτsurj, hτker, hsq, hCC, hEc, hEcard, he₀τ⟩,
        fun h => absurd (h0.symm.trans h) (by decide)⟩
    · obtain ⟨C₁, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hC₁C, hC₁sq, hZc, hCF⟩ :=
        degree64_noncentral_point he hb hnd φ hzC hsup hinf hz h1 hD₁N hD₁n hBD₁ hν₁surj hact₁'
          hprod₁
      obtain ⟨hZB, hZz, ⟨g, hgZ, hgB⟩, hZD⟩ :=
        noncentral_center_facts he hb hnd φ hzC hinf hz h1 hD₁N hD₁n hD₁H hν₁surj hact₁' hb₁c
          hC₁D hC₁n hC₁z hC₁B hZc hCF hact₂ hRD₂ hprod₂ σ hσ hσker hκ₂'
      obtain ⟨hgC, hgc⟩ := mem_map_center_subtype_iff.1 hgZ
      exact ⟨C₁, g, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hC₁sq.le, hgC, hZD hgZ, hZz g hgZ hgB,
        fun c hc => (hgc c hc).symm, fun h => absurd (h1.symm.trans h) (by decide),
        fun _ => ⟨hC₁C, hC₁sq, hZc, hCF, hZB, hZD, hgZ, hgB⟩⟩
  have hC₁sq : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz) := fun c hc =>
    hcl (subset_closure ⟨c, hc, rfl⟩)
  obtain ⟨hK₀c, hK₀card, hMcard, hKconj', hK₀A, hME, hE₂sq, hE₂n, hCn, hCcard, hDzC, hCR, hCF₂,
    hEC, hνs, hνk, hδs, hC₁C₂, hC₁E₂, hPc, hPcard, hK₀eq, hE₁card, hE₁C₂, ε, hεf, hε0, hε1,
    hgsq⟩ :=
    degree64_completion_common he hb hnd φ hzC hinf hz hD₂n hν₂z hν₂surj hpure hRD₂ hD₂H hD₁H
      hγD₁ hF₁ hKz hC₁D hC₁n hC₁z hC₁B hC₁sq hgC hgD₂ hgz hgcen hF₂ hF₂n hE₂F hE₂c hE₂card
      hE₂uniq hF₂zE hE₂R hF₂sq hY
  have hF₂D : F₂ ≤ D₂ := fun x hx => ((hF₂ x).1 hx).1
  have hb₁ord := orderOf_ptB₁ he hb φ hzC hz
  refine ⟨hκ₂0, C₁, E₂, ?_⟩
  intro E₁ K₀ M C₂ Z₁
  have hI₁ : I₁ = zpowers (ptB₁ he hb φ hzC hz) := by rw [hb₁']
  have hF₂s : (F₂ : Set G) = F₂s := Set.ext fun d => hF₂ d
  have hF₁s : (F₁ : Set G) = F₁s := Set.ext fun d => by
    rw [SetLike.mem_coe, hF₁, hb₁']
    exact Iff.rfl
  have hE₁s : E₁ = ((C₁ ⊓ F₁ : Subgroup G) : Set G) := by rw [coe_inf, hF₁s]
  have hMs : M = ((C₁ ⊓ F₂ : Subgroup G) : Set G) := by rw [coe_inf, hF₂s]
  have hJ₀s : J₀ = ((A₁ ⊓ altSub φ he : Subgroup G) : Set G) := by rw [coe_inf]; rfl
  have hC₂D : C₂ ≤ D₂ := inf_le_left
  have hJmul : (J : Set G) = (I₁ : Set G) * J₀ := by
    have hIN : zpowers (ptB₁ he hb φ hzC hz) ≤ normalizer ((A₁ ⊓ altSub φ he : Subgroup G) :
        Set G) := by
      rw [zpowers_le]
      refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => ?_)
      exact radA_comm he φ (altSub_le_radA he φ (mem_inf.1 hx).2) (ptB₁_mem_radA he hb φ hzC hz)
    rw [hI₁, hJ₀s, ← coe_mul_of_left_le_normalizer_right _ _ hIN,
      zpowers_sup_ptA_inf_altSub he hb φ hzC hz]
  have hIJ₀ : (I₁ : Set G) ∩ J₀ = {1} := by
    rw [hI₁, hJ₀s]
    ext x
    rw [Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe, mem_inf, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, -, h2⟩
      have h := mem_inf.2 ⟨h1, h2⟩
      rw [zpowers_ptB₁_inf_altSub he hb φ hzC hz, mem_bot] at h
      exact h
    · rintro rfl
      exact ⟨one_mem _, one_mem _, one_mem _⟩
  have hC₂F₂ : (C₂ : Set G) ∩ F₂s = E₂ := by
    rw [← hF₂s]
    ext x
    rw [Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe, SetLike.mem_coe, ← hCF₂ x, hF₂]
    constructor
    · rintro ⟨hxC, hxD, hxI⟩
      refine ⟨hxC, ?_⟩
      obtain ⟨B, hB, hBx⟩ := hxI
      rw [← tauHom_nu he φ hzC hz hν₂z hxD] at hBx
      rw [← Multiplicative.ofAdd.injective (tauHom_injective φ he hBx)]
      exact hB
    · rintro ⟨hxC, hx0⟩
      refine ⟨hxC, hC₂D hxC, _, hx0, ?_⟩
      exact tauHom_nu he φ hzC hz hν₂z (hC₂D hxC)
  have hθ₂ : ∀ X : ↥(binarySymMatrices 3), θ₂ (X, 0) = tauHom φ he (Multiplicative.ofAdd X) :=
    fun X => by
      change tauHom φ he (Multiplicative.ofAdd X) * z ^ (0 : ZMod 2).val = _
      rw [ZMod.val_zero, pow_zero, mul_one]
  refine ⟨hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, by rw [hI₁]; exact hcl, ?_,
    card_ptA_inf_radA he hb φ, ?_, hJmul, hIJ₀, hK₀card, ?_, hK₀c, hKconj', hK₀A, hE₂n,
    ?_, hE₂c, hE₂card, ?_, hE₂sq, ?_, ?_, hE₂R, hCn, hCcard, hDzC, hCR, hC₂F₂, hEC,
    fun x hx c hc => mem_centralizer_iff.1 (mem_inf.1 hc).2 x hx, hC₁C₂, ?_, hPc, hPcard,
    ν₂, ε, fun d hd => (tauHom_nu he φ hzC hz hν₂z hd).symm,
    fun c hc c' hc' => nu_mul he φ hzC hinf hz hν₂z hpure (hC₂D hc) (hC₂D hc'), hνs, hνk,
    fun g' c hc => ⟨hCn _ (leviHom_mem_normalizer_radSub φ he hzC hz g') c hc,
      nu_conj_levi he φ hzC hz hν₂z hD₂n g' (hC₂D hc)⟩, hδs,
    fun c hc => ⟨fun h => (hCF₂ c).1 ⟨hc, h⟩, fun h => ((hCF₂ c).2 h).2⟩, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [hE₁s, SetLike.coe_sort_coe]
    exact hE₁card
  · rw [hJ₀s, SetLike.coe_sort_coe]
    exact card_ptA_inf_altSub he hb φ
  · rw [hMs, SetLike.coe_sort_coe]
    exact hMcard
  · rw [← hF₂s]
    exact hE₂F
  · intro E' hE'F hE'c hE'card
    refine hE₂uniq E' ?_ hE'c hE'card
    rw [← hF₂s] at hE'F
    exact hE'F
  · intro x hx
    have h : x ∈ E₂ ⊓ radSub φ z e := by
      rw [hE₂R]
      exact hx
    exact (mem_inf.1 h).1
  · rw [← hF₂s]
    exact hF₂zE
  · rw [hMs, ← coe_inf, hC₁E₂]
  ·
    intro g' c hc
    rw [nu_conj_levi he φ hzC hz hν₂z hD₂n g' (hC₂D hc)]
    exact symThreeDiag_congr _ _ (ν₂ c).2
  · intro c hc d hd
    obtain ⟨h1, h2⟩ := hεf c hc d hd
    rw [hθ₂, hθ₂]
    exact ⟨h1, h2⟩
  · intro h0
    obtain ⟨hsq0, hcomm0⟩ := hε0 h0
    refine ⟨hsq0, hcomm0, ?_⟩
    ext x
    rw [mem_map_center_subtype_iff]
    exact ⟨fun h => h.1, fun hx => ⟨hx, fun y hy => hcomm0 y hy x hx⟩⟩
  · intro h1
    obtain ⟨hexp, hcl1, hcomm1, hcen1, hinv1⟩ := hε1 h1
    exact ⟨hexp, hcl1, by rw [hcomm1]; rfl, hcen1, hinv1⟩
  ·
    intro hl
    obtain ⟨τ₁, β, hτz, hτmul, hτsurj, hτker, hsq, hCC, hEc, hEcard, hgτ⟩ := hdata₀ hl
    obtain ⟨hsqε, -, hε0', hε1'⟩ := degree64_central_alternatives he hb hnd φ hzC hinf hz hC₁D
      hC₁B hτz hτmul hτsurj hτker hsq hCC hcl hEc hEcard hgC hgτ hgsq
    refine ⟨fun x hx y hy => ?_, fun c hc v hv => ?_, fun h0 => ?_, fun h1 => ?_, g, ?_, hgD₂,
      by rw [hgz, hb₁'], by rw [hgsq, hb₁'], by rw [hMs]; exact hK₀eq, ?_⟩
    · obtain ⟨hxC, -, hxI⟩ := hx
      exact hEc x hxC (by rw [← hI₁]; exact hxI) y hy
    · have h1 := hτz c hc
      have h2 : ptHom he hb φ hzC hz (Multiplicative.ofAdd (τ₁ c, 0)) =
          ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 0)) := by
        rw [← h1]
        refine (Eq.trans ?_ hv)
        group
      have h3 : τ₁ c = v := congrArg Prod.fst (Multiplicative.ofAdd.injective
        (ptHom_injective he hb φ hzC hz hinf h2))
      rw [hsqε c hc, h3]
      rfl
    · obtain ⟨hsq0, hcomm0⟩ := hε0' h0
      refine ⟨hsq0, hcomm0, ?_⟩
      ext x
      rw [mem_map_center_subtype_iff]
      exact ⟨fun h => h.1, fun hx => ⟨hx, fun y hy => hcomm0 y hy x hx⟩⟩
    · obtain ⟨hC, hS, hZiff, hiso⟩ := hε1' h1
      refine ⟨by rw [hI₁]; exact hC, by rw [hI₁]; exact hS, ?_, hiso⟩
      ext x
      rw [SetLike.mem_coe, hZiff x, hE₁s, coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
        SetLike.mem_coe, hF₁]
      exact ⟨fun h => ⟨h.1, hC₁D h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    · rw [hE₁s, coe_inf]
      exact ⟨hgC, (mem_inf.1 (by exact (show g ∈ C₁ ⊓ F₁ from
        mem_inf.2 ⟨hgC, (hF₁ g).2 ⟨hC₁D hgC, by rw [hgz]; exact mem_zpowers _⟩⟩))).2⟩
    · rw [hE₁s, ← coe_inf]
      exact hE₁C₂
  ·
    intro hl
    obtain ⟨hC₁C, hC₁sq', hZc, hCF, hZB, hZD, hgZ, hgB⟩ := hdata₁ hl
    have hZK : (center C₁).map C₁.subtype ≤ C₁ ⊓ D₂ := le_inf (map_subtype_le _) hZD
    have hKC : C₁ ⊓ D₂ ≤ C₂ := by
      rw [← hC₁C₂]
      exact inf_le_right
    have hZE : (center C₁).map C₁.subtype ≤ C₁ ⊓ F₁ ⊓ C₂ := by
      intro x hx
      have hxF : x ∈ (C₁ : Set G) ∩ {d | d ∈ D₁ ∧
          z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)} := by
        rw [hCF]
        exact mem_sup_right hx
      exact mem_inf.2 ⟨mem_inf.2 ⟨hxF.1, (hF₁ x).2 hxF.2⟩, hKC (hZK hx)⟩
    have hJE : pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ⊓
        pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ≤ C₁ ⊓ F₁ ⊓ C₂ := by
      intro x hx
      have h : x ∈ ((C₁ ⊓ F₁ ⊓ C₂ : Subgroup G) : Set G) := by
        rw [hE₁C₂]
        exact ⟨x, hx, 1, one_mem _, mul_one x⟩
      exact h
    obtain ⟨hZA, hZC₂, hKZ, hEZ, hiso0, hiso1, hZsq⟩ :=
      degree64_noncentral_alternatives he hb φ hzC hz hD₁N hD₁H hC₁D hC₁B hZc hCF hb₁c hZB hZK
        hKC (inf_le_inf_left _ hF₂D) hZE hJE hgZ hgB hgz hgsq hK₀eq hE₁C₂
    refine ⟨by rw [hI₁]; exact hC₁C, by rw [hI₁]; exact hC₁sq', hZc, by rw [hI₁]; exact hZA,
      ?_, hZC₂, by rw [hMs]; exact hKZ, ?_, hiso0, hiso1, by rw [← hb₁']; exact hZsq⟩
    · have h2 : (F₁ : Set G) = {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈
          zpowers (ptB₁ he hb φ hzC hz)} := Set.ext fun d => hF₁ d
      rw [hE₁s, coe_inf, h2]
      exact hCF
    · rw [hE₁s, ← coe_inf]
      exact hEZ

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
