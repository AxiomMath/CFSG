module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64ParameterCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64CentralLift

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem standard_binary_symplectic_six_degree64_central_point_action_excludes_noncentral_lagrangian
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
    let b₁ : G := ((φ.symm (n 0 1) : L) : G)
    let I₁ := zpowers b₁
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    let F₁ : Set G := {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ I₁}
    let S : Set G := {s | ∃ h : s ∈ L, linOf (φ ⟨s, h⟩) u = u ∧ linOf (φ ⟨s, h⟩) f = f}
    (∀ g : bilinIsometryGroup (b.restrict E), ∃ s : L, linOf (φ s) u = u ∧ linOf (φ s) f = f ∧
      ∀ w : E, linOf (φ s) (w : V) =
        ((((g : LinearMap.GeneralLinearGroup (ZMod 2) E) : E →ₗ[ZMod 2] E) w : E) : V)) ∧
    (∀ κ₂ lam : ZMod 2,
      (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2), d⁻¹ * z * d = θ₂ (C, 1) →
        d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C, ε)) →
      (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
        d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
      κ₂ = 0 ∧
      (lam = 0 → ∃ C₁ : Subgroup G, C₁ ≤ D₁ ∧ (∀ m ∈ N₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁) ∧
        Nat.card C₁ = 1024 ∧ zpowers z ⊔ C₁ = D₁ ∧ C₁ ⊓ B₁ = A₁ ∧
        closure {x | ∃ y ∈ C₁, y ^ 2 = x} ≤ I₁ ∧
        (∀ x ∈ (C₁ : Set G) ∩ F₁, ∀ y ∈ C₁, x * y = y * x) ∧
        Nat.card ↥((C₁ : Set G) ∩ F₁) = 64 ∧
        (∃ e₀ ∈ (C₁ : Set G) ∩ F₁, z⁻¹ * (e₀⁻¹ * z * e₀) = b₁ ∧
          (∀ s ∈ S, e₀⁻¹ * (s⁻¹ * e₀ * s) ∈ I₁) ∧ e₀ ∈ D₂) ∧
        Nat.card (C₁ ⊓ D₂ : Subgroup G) = 64 ∧
        conjClass (C₁ ⊓ D₂) z = z • ((A₁ ⊓ A₂ : Subgroup G) : Set G) ∧
        ⁅C₁ ⊓ D₂, A₂⁆ = ⊥)) ∧
    ⁅A₂, D₂⁆ = ⊥ ∧ (center D₂).map D₂.subtype = A₂ ∧
    (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2), d⁻¹ * z * d = θ₂ (C, 1) →
      d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + ε • C, ε)) := by
  obtain ⟨-, hzC, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, hσsurj, hσker, hσcol, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ, D₂, F₂', ν₂, hD₂, hFD₂, hD₂N, hRF₂, hD₂n, -, -, -, hν₂z, hν₂eq, hν₂surj, hact₂, -,
    hprod₂, hD₂H, -, -, hfaith₂⟩ := degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  have hRD₂ := hRF₂.trans hFD₂
  obtain ⟨-, hfull₁⟩ := degree64_point_fusion_of_lagrangian he hb hnd φ hzC hsup hinf hz hV hD₂N
    hD₂n hν₂z hν₂eq hν₂surj hact₂
  obtain ⟨lam₀, D₁, F₁', ν₁, hD₁, hFD₁, hD₁N, hBF₁, hD₁n, -, hD₁c, -, -, -, -, hν₁z, -, hν₁surj,
    hact₁, -, hprod₁, hD₁H, -, hb₁c, -, -, -, -, -, -, -, -, -⟩ :=
    degree64_point_two_group he hb hnd φ hzC hsup hinf hz hfull₁
  have hBD₁ := hBF₁.trans hFD₁
  obtain ⟨hKconj, hKc, -, -⟩ := degree64_intersections he hb hnd φ hzC hsup hinf hz hD₂N hD₂n
    hν₂z hν₂eq hν₂surj hact₂ hRD₂ hD₂H hD₁N hD₁n hBD₁ hD₁H hν₁z hact₁ hprod₁ σ hσcol hσker
    hσsurj hfull₁ hfull
  subst hD₂ hD₁
  set D₁ := CFSG.Assembly.pCoreOf 2 (normalizer ((ptSub φ z hb e : Subgroup G) : Set G))
    with hD₁def
  set D₂ := CFSG.Assembly.pCoreOf 2 (normalizer ((radSub φ z e : Subgroup G) : Set G))
    with hD₂def
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
  have hmain : ∀ κ₂ lam : ZMod 2,
      (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
        d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) →
        d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
          radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
            (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε))) →
      (∀ d ∈ D₁, ∀ (v : (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) × ZMod 2) (ε : ZMod 2),
        d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
          ptHom he hb φ hzC hz (Multiplicative.ofAdd (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) •
            ((0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))), (1 : ZMod 2)) + ε • ν₁ d, ε))) →
      κ₂ = 0 ∧ (lam = 0 → ∃ C₁ : Subgroup G, C₁ ≤ D₁ ∧
        (∀ m ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G), ∀ c ∈ C₁,
          m * c * m⁻¹ ∈ C₁) ∧ Nat.card C₁ = 1024 ∧ zpowers z ⊔ C₁ = D₁ ∧
        C₁ ⊓ ptSub φ z hb e = pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ∧
        closure {x | ∃ y ∈ C₁, y ^ 2 = x} ≤ zpowers (ptB₁ he hb φ hzC hz) ∧
        (∀ x ∈ C₁, z⁻¹ * (x⁻¹ * z * x) ∈ zpowers (ptB₁ he hb φ hzC hz) →
          ∀ y ∈ C₁, x * y = y * x) ∧
        Nat.card ↥((C₁ : Set G) ∩ {d | d ∈ D₁ ∧
          z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)}) = 64 ∧
        ∃ e₀ ∈ C₁, z⁻¹ * (e₀⁻¹ * z * e₀) = ptB₁ he hb φ hzC hz ∧
          (∀ x ∈ (normalizer ((ptSub φ z hb e : Subgroup G) : Set G) ⊓
            centralizer ({z} : Set G) : Subgroup G),
            e₀⁻¹ * x⁻¹ * e₀ * x ∈ zpowers (ptB₁ he hb φ hzC hz)) ∧ e₀ ∈ D₂) := by
    intro κ₂ lam hκ₂ hlam
    rcases zmod_two_eq_zero_or_eq_one lam with h0 | h1
    · obtain ⟨hκ0, hC⟩ := degree64_central_lift he hb hnd φ hzC hsup hinf hz σ hσ hσcol hσker h0
        hD₁N hD₁n hBD₁ hD₁H hν₁z hν₁surj hlam hprod₁ hb₁c hD₂N hD₂n hν₂z hν₂eq hν₂surj hact₂
        hRD₂ hprod₂ hκ₂
      exact ⟨hκ0, fun _ => hC⟩
    · obtain ⟨C₁, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, -, -, hZc, hCF⟩ :=
        degree64_noncentral_point he hb hnd φ hzC hsup hinf hz h1 hD₁N hD₁n hBD₁ hν₁surj hlam
          hprod₁
      have hκ0 := kappa_eq_zero_of_lam_eq_one he hb hnd φ hzC hinf hz h1 hD₁N hD₁n hD₁H hν₁surj
        hlam hb₁c hC₁D hC₁n hC₁z hC₁B hZc hCF hact₂ hRD₂ hprod₂ σ hσ hσker hκ₂
      exact ⟨hκ0, fun h => absurd (h1.symm.trans h) (by decide)⟩
  have hκ0 : κ = 0 := (hmain κ lam₀ hκ hact₁).1
  obtain ⟨hZ₂, hcomm₂, hfix₂⟩ := center_eq_radA_of_kappa_zero he φ hzC hinf hz hκ hκ0 hν₂z
    hν₂surj hRD₂ hD₂H
  have hb₁eq := ptB₁_eq he hb φ hzC hz
  have hKz : ∀ j ∈ pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ⊓
      pullSub φ (pointwiseStabilizer b (lagrangianOf e)), ∃ k ∈ D₁ ⊓ D₂,
        k⁻¹ * z * k = z * j := fun j hj =>
    exists_mem_inf_conj_eq he hb hnd φ hzC hsup hinf hz hD₂N hD₂n hν₂z hν₂eq hν₂surj hact₂ hRD₂
      hD₁n hBD₁ hν₁z hact₁ hprod₁ hj
  have hzD₂ : z ∈ D₂ := hRD₂ (mem_sup_right (mem_zpowers z))
  intro u f E n Q r τ θ₂ θ₁ A₂ R₂ N₂ D₂' A₁ b₁ I₁ B₁ N₁ D₁' F₁ S
  refine ⟨fun g => ?_, fun κ₂ lam hκ₂ hlam => ?_, hcomm₂, hZ₂, fun d hd C B ε h => ?_⟩
  ·
    set k := (MulEquiv.ofBijective (pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0)))
      (pairRestrict_bijective hb (bilin_f_u he))).symm g with hk
    have hks : pairRestrict b _ _ k = g := pairRestrict_ptLevi he hb g
    have hφ : φ ⟨ptLevi he hb φ g, ptLevi_mem he hb φ g⟩ = (k : bilinIsometryGroup b) := by
      change φ (φ.symm (k : bilinIsometryGroup b)) = _
      exact MulEquiv.apply_symm_apply φ _
    refine ⟨⟨ptLevi he hb φ g, ptLevi_mem he hb φ g⟩, ?_, ?_, fun w => ?_⟩
    · rw [hφ]
      exact (mem_pairStabilizer.1 k.2).1
    · rw [hφ]
      exact (mem_pairStabilizer.1 k.2).2
    · rw [hφ, ← hks]
      exact (pairRestrict_apply k w).symm
  ·
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
    obtain ⟨hκ₂0, hC⟩ := hmain κ₂ lam hκ₂' hact₁'
    refine ⟨hκ₂0, fun hlam0 => ?_⟩
    obtain ⟨C₁, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hsq, hEc, hEcard, e₀, he₀C, he₀z, he₀N,
      he₀D₂⟩ := hC hlam0
    obtain ⟨-, -, hfix⟩ := center_eq_radA_of_kappa_zero he φ hzC hinf hz hκ₂' hκ₂0 hν₂z hν₂surj
      hRD₂ hD₂H
    rw [hb₁eq] at hsq hEc hEcard he₀z he₀N
    refine ⟨C₁, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hsq, fun x hx y hy => hEc x hx.1 hx.2.2 y hy,
      hEcard, ⟨e₀, ⟨he₀C, hC₁D he₀C, ?_⟩, he₀z, fun s hs => ?_, he₀D₂⟩, ?_, ?_, ?_⟩
    · change z⁻¹ * (e₀⁻¹ * z * e₀) ∈ zpowers b₁
      rw [he₀z]
      exact mem_zpowers _
    ·
      obtain ⟨hsL, hsu, -⟩ := hs
      have hsV : s ∈ pullSub φ (vecStabilizer b (e (Sum.inl 0))) :=
        mem_pullSub.2 ⟨hsL, hsu⟩
      rw [← (ptA_facts he hb hnd φ).2.2.2.2.1] at hsV
      have hsN : s ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) :=
        (mem_normalizer_ptSub_iff_of_mem he hb hnd φ hzC hinf hz hsL).2 (mem_inf.1 hsV).1
      have h := he₀N s (mem_inf.2 ⟨hsN, mem_centralizer_singleton_iff.2 (mul_comm_z hzC hsL)⟩)
      have h2 : e₀⁻¹ * (s⁻¹ * e₀ * s) = e₀⁻¹ * s⁻¹ * e₀ * s := by group
      rw [h2]
      exact h
    ·
      have hrel : C₁.relIndex D₁ = 2 := by
        have h := Subgroup.relIndex_mul_card (H := C₁) (K := D₁)
        rw [inf_of_le_left hC₁D, hC₁c, hD₁c] at h
        omega
      have hzK : z ∈ D₁ ⊓ D₂ :=
        mem_inf.2 ⟨hBD₁ (mem_sup_right (mem_zpowers z)), hzD₂⟩
      have hzC₁ : z ∉ C₁ := by
        intro h
        have h1 : z ∈ pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) :=
          hC₁B ▸ mem_inf.2 ⟨h, mem_sup_right (mem_zpowers z)⟩
        have h2 : z ∈ L ⊓ zpowers z := mem_inf.2 ⟨(ptA_facts he hb hnd φ).1 h1, mem_zpowers z⟩
        rw [hinf, mem_bot] at h2
        rw [h2, orderOf_one] at hz
        exact absurd hz (by norm_num)
      have hle := Subgroup.relIndex_le_of_le_right (H := C₁)
        (inf_le_left : D₁ ⊓ D₂ ≤ D₁) (by rw [hrel]; norm_num)
      rw [hrel] at hle
      have hne1 : C₁.relIndex (D₁ ⊓ D₂) ≠ 1 := fun h => hzC₁ ((Subgroup.relIndex_eq_one.1 h) hzK)
      have h := Subgroup.relIndex_mul_card (H := C₁) (K := D₁ ⊓ D₂)
      rw [hKc, ← inf_assoc, inf_of_le_left hC₁D] at h
      rcases (show C₁.relIndex (D₁ ⊓ D₂) = 0 ∨ C₁.relIndex (D₁ ⊓ D₂) = 2 by omega) with h0 | h2
      · rw [h0, zero_mul] at h
        omega
      · rw [h2] at h
        change Nat.card (C₁ ⊓ D₂ : Subgroup G) = 64
        omega
    ·
      have hzC₁n : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁ :=
        hC₁n z (le_normalizer (mem_sup_right (mem_zpowers z)))
      change conjClass (C₁ ⊓ D₂) z = z • ((pullSub φ (pointRadical b hb (e (Sum.inl 0))
        (e (Sum.inr 0))) ⊓ pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Subgroup G) :
          Set G)
      refine Set.Subset.antisymm ?_ ?_
      · rw [← hKconj]
        exact conjClass_mono (inf_le_inf_right _ hC₁D) z
      · rintro _ ⟨j, hj, rfl⟩
        obtain ⟨k, hk, hkz⟩ := exists_mem_inf_conj_eq_of_sup hb φ hKz hC₁z hzC₁n hzD₂ hj
        change z * j ∈ conjClass (C₁ ⊓ D₂) z
        exact mem_conjClass_iff_right.2 ⟨k, hk, hkz⟩
    ·
      change ⁅C₁ ⊓ D₂, pullSub φ (pointwiseStabilizer b (lagrangianOf e))⁆ = ⊥
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x hx
      refine mem_centralizer_iff.2 fun a ha => ?_
      have h := hfix x (mem_inf.1 hx).2 a ha
      calc a * x = x * (x⁻¹ * a * x) := by group
        _ = x * a := by rw [h]
  ·
    have h1 := hκ d hd C B ε h
    rw [hκ0, zero_smul, add_zero] at h1
    exact h1

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
