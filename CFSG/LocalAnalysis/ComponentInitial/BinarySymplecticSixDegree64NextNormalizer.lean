module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64LagrangianCompletion
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NextOddKernel

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem standard_binary_symplectic_six_elementary_lagrangian_next_normalizer
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
        Nat.card ↥E₁ = 64 ∧ Nat.card K₀ = 64 ∧ Nat.card ↥M = 32 ∧ Nat.card J = 8 ∧
        Nat.card ↥J₀ = 4 ∧
        (∀ m ∈ N₂, ∀ x ∈ E₂, m * x * m⁻¹ ∈ E₂) ∧ (E₂ : Set G) ⊆ F₂ ∧ IsMulCommutative E₂ ∧
        Nat.card E₂ = 512 ∧
        (∀ E' : Subgroup G, (E' : Set G) ⊆ F₂ → IsMulCommutative E' → Nat.card E' = 512 →
          E' = E₂) ∧
        IsElementaryAbelian 2 E₂ ∧
        (∀ m ∈ N₂, ∀ c ∈ C₂, m * c * m⁻¹ ∈ C₂) ∧ Nat.card C₂ = 4096 ∧
        (D₂ : Set G) = (zpowers z : Set G) * (C₂ : Set G) ∧ C₂ ⊓ R₂ = A₂ ∧
        (C₂ : Set G) ∩ F₂ = E₂ ∧ C₁ ⊓ C₂ = K₀ ∧ (C₁ : Set G) ∩ E₂ = M ∧
        (∀ k ∈ K₀, ∀ k' ∈ K₀, k * k' = k' * k) ∧ conjClass K₀ z = z • (J : Set G) ∧
        ⁅K₀, A₂⁆ = ⊥ ∧
        ∃ (ν₂ : G → ↥(binarySymMatrices 3)) (ε : ZMod 2),
          (∀ d ∈ D₂, z⁻¹ * (d⁻¹ * z * d) = τ (ν₂ d)) ∧
          (∀ c ∈ C₂, c ^ 2 = θ₂ (symThreeSquare ε (symThreeDiag (ν₂ c : M₃)), 0)) ∧
          (ε = 0 →
            let P := A₂ ⊔ K₀
            let V₁ := D₁ ⊔ A₂
            let B := zpowers z ⊔ A₁ ⊔ A₂ ⊔ K₀
            let Q₀ : Set G := (K₀ : Set G) ∩ F₁
            let N := normalizer (B : Set G) ⊓ centralizer ({b₁} : Set G)
            let X := normalizer (C₂ : Set G)
            let K := (CFSG.oddCore (centralizer (C₂ : Set G))).map
              (centralizer (C₂ : Set G)).subtype
            IsElementaryAbelian 2 P ∧ Nat.card P = 512 ∧
            (∃ Q : Subgroup G, (Q : Set G) = Q₀ ∧ IsElementaryAbelian 2 Q ∧ Nat.card Q = 16) ∧
            Nat.card B = 4096 ∧ Nat.card V₁ = 16384 ∧ B ≤ V₁ ∧
            (∀ v ∈ V₁, ∀ x ∈ B, v * x * v⁻¹ ∈ B) ∧ I₁ ≤ P ∧ P ≤ B ∧
            (∀ Y : Subgroup G, I₁ ≤ Y → Y ≤ B → Nat.card Y = 512 → (∀ y ∈ Y, y ^ 2 ∈ I₁) →
              (∀ y ∈ Y, ∀ y' ∈ Y, y⁻¹ * y'⁻¹ * y * y' ∈ I₁) → Y = P) ∧
            (∀ m ∈ N, ∀ p ∈ P, m * p * m⁻¹ ∈ P) ∧ V₁ ≤ N ∧
            (∀ m : G, (m ∈ N ∧ ∀ x ∈ B, m * x * m⁻¹ * x⁻¹ ∈ P) ↔ m ∈ A₁ ⊔ D₂) ∧
            (A₁ ⊔ D₂) ⊓ centralizer (P : Set G) = C₂ ∧
            N ≤ X ∧ V₁ ≤ X ∧ V₁ ⊓ C₂ = P ∧ C₂.relIndex (V₁ ⊔ C₂) = 32 ∧
            (∀ c ∈ C₂, c * z = z * c ↔ c ∈ A₂) ∧
            (fun c => z⁻¹ * c⁻¹ * z * c) '' (C₂ : Set G) = A₂ ∧
            (∃ hzX : z ∈ X,
              centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)} =
                (N₂.subgroupOf X).map (QuotientGroup.mk' (C₂.subgroupOf X)) ∧ N₂ ≤ X ∧
              (∃ ψ : Multiplicative (ZMod 2) × GL (Fin 3) (ZMod 2) ≃*
                  centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)},
                ∀ (s : ZMod 2) (g : GL (Fin 3) (ZMod 2)) (h : z ^ s.val * leviHom φ he g ∈ X),
                  (ψ (Multiplicative.ofAdd s, g) : X ⧸ C₂.subgroupOf X) =
                    QuotientGroup.mk ⟨_, h⟩) ∧
              (∀ S : Sylow 2 (X ⧸ C₂.subgroupOf X),
                (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) ∈ S →
                  ∃ y ∈ S, y * (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) ≠
                    (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) * y) ∧
              CFSG.Assembly.pCore 2 (X ⧸ C₂.subgroupOf X) = ⊥) ∧
            centralizer (C₂ : Set G) = C₂ ⊔ K ∧ C₂ ⊓ K = ⊥ ∧ Odd (Nat.card K) ∧
            (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) ∧ (∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧
            (∀ k ∈ K, z * k * z⁻¹ = k⁻¹) ∧
            (∃ κ : X →* MulAut C₂,
              (∀ (x : X) (c : C₂), ((κ x c : C₂) : G) = x * c * (x : G)⁻¹) ∧
              κ.ker = (C₂ ⊔ K).subgroupOf X) ∧
            IsElementaryAbelian 2 C₂ ∧ Nat.card C₂ = 2 ^ 12 ∧ Nat.card A₂ = 2 ^ 6 ∧
            (∃ Ψ : Multiplicative ((Fin 6 → ZMod 2) × (Fin 6 → ZMod 2)) ≃* C₂,
              (∀ u v, z * (Ψ (Multiplicative.ofAdd (u, v)) : G) * z⁻¹ =
                Ψ (Multiplicative.ofAdd (u, u + v))) ∧
              ∀ u v, (Ψ (Multiplicative.ofAdd (u, v)) : G) ∈ A₂ ↔ u = 0) ∧
            (center C₂).map C₂.subtype = C₂ ∧
            (lam = 0 → IsElementaryAbelian 2 C₁ ∧ Z₁ = C₁) ∧
            (lam = 1 → ⁅C₁, C₁⁆ = I₁ ∧ closure {x | ∃ y ∈ C₁, y ^ 2 = x} = I₁ ∧
              IsElementaryAbelian 2 Z₁ ∧ Nat.card Z₁ = 4 ∧
              E₁ = ((A₁ ⊔ Z₁ : Subgroup G) : Set G) ∧ Z₁ ≤ C₂)) := by
  obtain ⟨-, hzC, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, hRc, -, -, -, -, hker, -, -, -, ⟨σ, hσsurj, hσker, hσcol, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ, D₂, F₂', ν₂', hD₂, hFD₂, hD₂N, hRF₂, hD₂n, -, -, -, hν₂z, hν₂eq, hν₂surj, hact₂,
    -, hprod₂, hD₂H, -, -, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  have hRD₂ := hRF₂.trans hFD₂
  obtain ⟨-, hfull₁⟩ := degree64_point_fusion_of_lagrangian he hb hnd φ hzC hsup hinf hz hV hD₂N
    hD₂n hν₂z hν₂eq hν₂surj hact₂
  obtain ⟨lam₀, D₁, F₁, ν₁, hD₁, hFD₁, hD₁N, hBF₁, hD₁n, -, -, -, -, -, -, hν₁z, -, hν₁surj,
    hact₁, -, hprod₁, hD₁H, -, hb₁c, -, -, -, -, -, -, ⟨hγD₁, -, hF₁mem, -⟩, -, -⟩ :=
    degree64_point_two_group he hb hnd φ hzC hsup hinf hz hfull₁
  have hBD₁ := hBF₁.trans hFD₁
  have h3 :=
    standard_binary_symplectic_six_degree64_central_point_action_excludes_noncentral_lagrangian
      hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull
  subst hD₂ hD₁
  obtain ⟨-, -, -, -, htrans⟩ := h3
  set D₁ := CFSG.Assembly.pCoreOf 2 (normalizer ((ptSub φ z hb e : Subgroup G) : Set G))
    with hD₁def
  set D₂ := CFSG.Assembly.pCoreOf 2 (normalizer ((radSub φ z e : Subgroup G) : Set G))
    with hD₂def
  have hpure : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + ε • ν₂' d, ε)) :=
    fun d hd B ε => htrans d hd (ν₂' d) B ε (hν₂z d hd)
  have hD₂A : ∀ d ∈ D₂, ∀ a ∈ pullSub φ (pointwiseStabilizer b (lagrangianOf e)),
      d * a = a * d := by
    intro d hd a ha
    obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    have h := hpure d hd (Multiplicative.toAdd B) 0
    rw [zero_smul, add_zero, radHom_tau, ofAdd_toAdd] at h
    exact comm_of_inv_mul_mul_eq h
  have hKz : ∀ j ∈ pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ⊓
      pullSub φ (pointwiseStabilizer b (lagrangianOf e)), ∃ k ∈ D₁ ⊓ D₂,
        k⁻¹ * z * k = z * j := fun j hj =>
    exists_mem_inf_conj_eq he hb hnd φ hzC hsup hinf hz hD₂N hD₂n hν₂z hν₂eq hν₂surj hact₂ hRD₂
      hD₁n hBD₁ hν₁z hact₁ hprod₁ hj
  have hF₁ : ∀ d : G, d ∈ F₁ ↔ d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz) :=
    fun d => ⟨fun h => ⟨hFD₁ h, (hF₁mem d (hFD₁ h)).2 h⟩, fun h => (hF₁mem d h.1).1 h.2⟩
  have hb₁eq := ptB₁_eq he hb φ hzC hz
  intro u f E n Q r τ θ₂ θ₁ A₂ R₂ N₂ D₂' I₂ F₂s A₁ b₁ I₁ B₁ N₁ D₁' F₁s J J₀ κ₂ lam hκ₂ hlam
  have hb₁' : ptB₁ he hb φ hzC hz = b₁ := hb₁eq
  have h4 := standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion hG hL hLn hZ
    hmodel T hT hzT hz hH hb hnd hV φ e he hfull
  obtain ⟨hκ0, C₁, E₂, h4'⟩ := h4 κ₂ lam hκ₂ hlam
  obtain ⟨hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hcl, hE₁card, hJcard, hJ₀card, -, -, hK₀card, hMcard,
    hK₀c, hKconj, hK₀A, hE₂n, hE₂F, hE₂c, hE₂card, hE₂uniq, hE₂sq, -, -, hE₂R, hC₂n, hC₂card,
    hDzC, hC₂R, hC₂F₂, -, -, hC₁C₂, hC₁E₂, -, hPcard, ν, ε, hνz, hνmul, hνs, hνk, -, -, -, -,
    hsqf, hε0, -, hlam0, hlam1⟩ := h4'
  refine ⟨hκ0, C₁, E₂, ?_⟩
  intro E₁ K₀ M C₂ Z₁
  refine ⟨hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hcl, hE₁card, hK₀card, hMcard, hJcard, hJ₀card, hE₂n,
    hE₂F, hE₂c, hE₂card, hE₂uniq, elemAbelian_of_sq_eq_one hE₂sq, hC₂n, hC₂card, hDzC, hC₂R,
    hC₂F₂, hC₁C₂, hC₁E₂, hK₀c, hKconj, hK₀A, ν, ε, hνz, fun c hc => (hsqf c hc c hc).1,
    fun h0 => ?_⟩
  intro P V₁ B Q₀ N X K
  obtain ⟨hC₂sq, -, hC₂cen⟩ := hε0 h0
  have hν₂z' : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν d, 1)) := by
    intro d hd
    rw [radHom_one_eq φ he hzC hz]
    have h := hνz d hd
    calc d⁻¹ * z * d = z * (z⁻¹ * (d⁻¹ * z * d)) := by group
      _ = z * tauHom φ he (Multiplicative.ofAdd (ν d)) := by rw [h]
  have hC₂D : C₂ ≤ D₂ := inf_le_left
  have hzB₁ : z ∈ ptSub φ z hb e := mem_sup_right (mem_zpowers z)
  have hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁ := hC₁n z (le_normalizer hzB₁)
  have hC₁sq' : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz) := fun c hc => by
    rw [hb₁']
    exact hcl (Subgroup.subset_closure ⟨c, hc, rfl⟩)
  obtain ⟨hBcard, hV₁card, hBV₁, hBn, hV₁N, hPB, hIP, -, hA₁V₁, -, hγB, hBNP⟩ :=
    degree64_next_block he hb hnd φ hzC hinf hz (D₁ := D₁) (C₁ := C₁) (D₂ := D₂) (C₂ := C₂)
      (K₀ := K₀) (P := P) (B := B) (V₁ := V₁) hD₁N hD₁n hD₁H hγD₁ hb₁c hC₁D hC₁n hC₁z hC₁B hC₁c
      hC₁sq' hD₂n hRD₂ hD₂H hν₂z' hKz hC₂R hC₁C₂ rfl rfl rfl rfl hPcard
  rw [hb₁'] at hV₁N hIP
  have hPC₂ : P ≤ C₂ := (P_le_and_elemAbelian φ hC₂R hC₁C₂ hC₂sq).1
  have hQ₀ : Nat.card (K₀ ⊓ F₁ : Subgroup G) = 16 :=
    card_Q₀ he hb hnd φ hzC hinf hz hD₂H hRD₂ hD₁H hC₁D hC₁B hC₁z hzC₁ hKz hF₁
  have hA₁B : ∀ a ∈ pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))), ∀ x ∈ B,
      a⁻¹ * x⁻¹ * a * x ∈ J := fun a ha x hx => hA₁V₁ a ha x (hBV₁ hx)
  obtain ⟨hJB, hBB⟩ := degree64_block_comm he hb hnd φ hzC hz (C₁ := C₁) (D₂ := D₂) (K₀ := K₀)
    (P := P) (B := B) hC₂sq hC₂R hC₁C₂ rfl rfl rfl hγB hA₁B
  have hK₀J : ∀ j ∈ J, ∃ k ∈ K₀, z⁻¹ * (k⁻¹ * z * k) = j := by
    intro j hj
    have hzj : z * j ∈ conjClass K₀ z := by
      rw [hKconj]
      exact Set.smul_mem_smul_set hj
    obtain ⟨k, hk, hkz⟩ := mem_conjClass_iff_right.1 hzj
    exact ⟨k, hk, by rw [hkz]; group⟩
  have hk₁ : ∃ k ∈ K₀, z⁻¹ * (k⁻¹ * z * k) = tauHom φ he (Multiplicative.ofAdd (jSym 0 1 0)) :=
    hK₀J _ ((mem_ptA_inf_radA_iff he hb φ).2 ⟨0, 1, 0, rfl⟩)
  have huniq : ∀ Y : Subgroup G, Y ≤ B → Nat.card Y = 512 → (∀ y ∈ Y, y ^ 2 ∈ I₁) → Y = P :=
    fun Y hYB hYc hYsq => degree64_next_unique he hb hnd φ hzC hsup hinf hz σ hσ hσcol hσker
      (D₁ := D₁) (C₁ := C₁) (D₂ := D₂) (C₂ := C₂) (K₀ := K₀) (P := P) (B := B) (F₁ := F₁) hC₁D
      hC₁B hC₁sq' hC₂D hC₂sq hC₂R hC₁C₂ rfl rfl rfl hF₁ hPcard hQ₀ hγB hA₁B hBNP hk₁ hYB hYc
      (fun y hy => by rw [hb₁']; exact hYsq y hy)
  have hPsq : ∀ p ∈ P, p ^ 2 = 1 := fun p hp => hC₂sq p (hPC₂ hp)
  have hNP : ∀ m ∈ N, ∀ p ∈ P, m * p * m⁻¹ ∈ P := fun m hm p hp =>
    conj_mem_of_unique hPB hPsq (fun Y hYB hYc hYsq => huniq Y hYB (hYc.trans hPcard) hYsq)
      (mem_inf.1 hm).1 hp
  obtain ⟨hKer, hCen, hNX⟩ := degree64_next_kernel he hb hnd φ hzC hsup hz σ hσ hσcol hσker
    (C₁ := C₁) (D₂ := D₂) (C₂ := C₂) (K₀ := K₀) (P := P) (B := B) hD₂n hRD₂ hD₂H hν₂z' hD₂A
    hprod₂ hC₂D hC₂n hC₂R hC₂sq hC₁C₂ hDzC hνmul hνk rfl rfl rfl hPcard hBNP hBB hJB hK₀J
    (by rw [hb₁']; exact hNP)
  rw [hb₁'] at hKer hNX
  have hV₁X : V₁ ≤ X := hV₁N.trans hNX
  obtain ⟨hV₁C₂, hrel⟩ := degree64_next_V₁ he hb hnd φ hzC hinf hz (D₁ := D₁) (C₁ := C₁)
    (D₂ := D₂) (C₂ := C₂) (K₀ := K₀) (P := P) (V₁ := V₁) hD₁n hC₁z hzC₁ hRD₂ hC₂D hC₂R hC₁C₂ rfl
    rfl rfl (hPB.trans hBV₁) hV₁X hV₁card hPcard hC₂card
  have : (C₂.subgroupOf X).Normal := Subgroup.normal_in_normalizer
  have hquot := degree64_next_quotient he φ hzC hinf hz σ hσ (D₂ := D₂) (C₂ := C₂) (V₁ := V₁)
    (X := X) rfl hRc hRD₂ hν₂z' hD₂A hD₂H hprod₂ hC₂D hC₂n hC₂R hC₂sq hDzC hνs hC₂card hV₁X hrel
  obtain ⟨hK1, hK2, hK3, hK4, hK5, hK6, hK7⟩ := degree64_next_odd_kernel he φ hzC hinf hz
    (D₂ := D₂) (C₂ := C₂) (X := X) rfl hRc hν₂z' hD₂H hC₂D hC₂n hC₂R hC₂sq hνs hC₂card
  obtain ⟨Ψ, hΨz, hΨA⟩ := degree64_next_jordan he φ hzC hz hν₂z' hC₂D hC₂n hC₂R hC₂sq hνmul hνk
    hνs hC₂card
  have hfixA : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ A₂ := by
    intro c hc
    constructor
    · intro hcz
      have h : c ∈ C₂ ⊓ radSub φ z e := by
        refine mem_inf.2 ⟨hc, ?_⟩
        rw [← hD₂H]
        exact mem_inf.2 ⟨hC₂D hc, mem_centralizer_singleton_iff.2 hcz⟩
      rw [hC₂R] at h
      exact h
    · intro ha
      exact mul_comm_z hzC (pullSub_le φ _ ha)
  have himg : (fun c => z⁻¹ * c⁻¹ * z * c) '' (C₂ : Set G) = A₂ := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      have h : z⁻¹ * c⁻¹ * z * c = z⁻¹ * (c⁻¹ * z * c) := by group
      change z⁻¹ * c⁻¹ * z * c ∈ A₂
      rw [h, ← tauHom_nu he φ hzC hz hν₂z' (hC₂D hc)]
      exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
    · intro hx
      obtain ⟨M, hM⟩ := (mem_pullSub_iff φ he).1 hx
      obtain ⟨c, hc, hcM⟩ := hνs (Multiplicative.toAdd M)
      refine ⟨c, hc, ?_⟩
      have h : z⁻¹ * c⁻¹ * z * c = z⁻¹ * (c⁻¹ * z * c) := by group
      change z⁻¹ * c⁻¹ * z * c = x
      rw [h, ← tauHom_nu he φ hzC hz hν₂z' (hC₂D hc), hcM, ofAdd_toAdd, hM]
  refine ⟨(P_le_and_elemAbelian φ hC₂R hC₁C₂ hC₂sq).2, hPcard, ⟨K₀ ⊓ F₁, ?_, ?_, hQ₀⟩, hBcard,
    hV₁card, hBV₁, hBn, hIP, hPB, fun Y _ hYB hYc hYsq _ => huniq Y hYB hYc hYsq, hNP, hV₁N,
    hKer, hCen, hNX, hV₁X, hV₁C₂, hrel, hfixA, himg, hquot, hK1, hK2, hK3, hK4, hK5, hK6, hK7,
    elemAbelian_of_sq_eq_one hC₂sq, by rw [hC₂card]; norm_num,
    by rw [card_pullSub_radA he φ]; norm_num, ⟨Ψ, hΨz, hΨA⟩, hC₂cen, fun hl => ?_, fun hl => ?_⟩
  · ext x
    rw [SetLike.mem_coe, mem_inf, hF₁, hb₁']
    exact Iff.rfl
  · exact elemAbelian_of_sq_eq_one fun x hx => hC₂sq x (hPC₂ (mem_sup_right (mem_inf.1 hx).1))
  · obtain ⟨-, -, hε0', -, -⟩ := hlam0 hl
    obtain ⟨hsq1, -, hZ⟩ := hε0' h0
    exact ⟨elemAbelian_of_sq_eq_one hsq1, hZ⟩
  · obtain ⟨hcomm, hclos, hZc, -, hE₁eq, hZC₂, -, -, -, -, -⟩ := hlam1 hl
    exact ⟨hcomm, hclos, elemAbelian_of_sq_eq_one fun x hx => hC₂sq x (hZC₂ hx),
      by rw [card_map_of_injective C₁.subtype_injective]; exact hZc, hE₁eq, hZC₂⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
