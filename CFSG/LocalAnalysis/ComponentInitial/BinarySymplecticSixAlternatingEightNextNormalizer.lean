module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightNextNormalizerJordan

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

section Setting

variable {G : Type} [Group G] {L : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {b : BilinForm (ZMod 2) V}

theorem card_tauSet_alt (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
    (he : IsSymplecticBasis b e) : Nat.card (tauSet φ e (fun B => ∀ i, B i i = 0)) = 8 := by
  have hset : tauSet φ e (fun B => ∀ i, B i i = 0) =
      Set.range fun v : Fin 3 → ZMod 2 =>
        tauHom φ he (Multiplicative.ofAdd (DegreeEight.altLabel v)) := by
    ext x
    rw [mem_tauSet_iff φ he]
    constructor
    · rintro ⟨B, hB, rfl⟩
      refine ⟨symThreeOff ((Multiplicative.toAdd B : binarySymMatrices 3) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)), ?_⟩
      beta_reduce
      rw [← eq_altLabel_of_diag_eq_zero (B := Multiplicative.toAdd B) (funext hB), ofAdd_toAdd]
    · rintro ⟨v, rfl⟩
      exact ⟨_, fun i => congrFun (symThreeDiag_altLabel v) i, rfl⟩
  rw [hset, Nat.card_range_of_injective fun v w h => DegreeEight.altLabel_injective
    (Multiplicative.ofAdd.injective (tauHom_injective φ he h)), natCard_vecThree]

end Setting

theorem standard_binary_symplectic_six_alternating_eight_next_normalizer {G : Type}
    [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
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
    (halt : conjClass (normalizer ((pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔
        zpowers z : Subgroup G) : Set G)) z = z • tauSet φ e (fun B => ∀ i, B i i = 0)) :
    let A₂ := pullSub φ (pointwiseStabilizer b (lagrangianOf e))
    let R₂ := A₂ ⊔ zpowers z
    let N₂ := normalizer (R₂ : Set G)
    let D₂ := CFSG.Assembly.pCoreOf 2 N₂
    let I₂ := tauSet φ e (fun B => ∀ i, B i i = 0)
    let lev : GL (Fin 3) (ZMod 2) → G := fun g => leviHom φ he g
    ∃ C₂ : Subgroup G,
      let X := normalizer (C₂ : Set G)
      let K := (CFSG.oddCore (centralizer (C₂ : Set G))).map (centralizer (C₂ : Set G)).subtype
      C₂ ≤ D₂ ∧ (∀ x ∈ C₂, ∀ y ∈ C₂, x * y = y * x) ∧ Nat.card C₂ = 512 ∧
      (∀ F : Subgroup G, F ≤ D₂ → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → Nat.card F = 512 →
        F = C₂) ∧
      IsElementaryAbelian 2 C₂ ∧ (∀ g ∈ N₂, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂) ∧
      (∀ F : Subgroup G, F ≤ N₂ → IsElementaryAbelian 2 F → Nat.card F = 512 → F = C₂) ∧
      (∀ S₂ : Sylow 2 N₂, Nat.card S₂ = 2 ^ 13 ∧ C₂ ≤ (S₂ : Subgroup N₂).map N₂.subtype ∧
        (C₂.subgroupOf ((S₂ : Subgroup N₂).map N₂.subtype)).Characteristic ∧
        (∀ P : Sylow 2 G, (P : Subgroup G) ≠ (S₂ : Subgroup N₂).map N₂.subtype) ∧
        ∀ P : Sylow 2 G, (S₂ : Subgroup N₂).map N₂.subtype ≤ P →
          (S₂ : Subgroup N₂).map N₂.subtype < (P : Subgroup G) ⊓
              normalizer (((S₂ : Subgroup N₂).map N₂.subtype : Subgroup G) : Set G) ∧
            (P : Subgroup G) ⊓
              normalizer (((S₂ : Subgroup N₂).map N₂.subtype : Subgroup G) : Set G) ≤ X) ∧
      2 ^ 5 ∣ Nat.card (X ⧸ C₂.subgroupOf X) ∧
      (∃ hzX : z ∈ X, orderOf (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) = 2 ∧
        centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)} =
          (N₂.subgroupOf X).map (QuotientGroup.mk' (C₂.subgroupOf X)) ∧
        (∃ ψ : Multiplicative (ZMod 2) × GL (Fin 3) (ZMod 2) ≃*
            centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X)},
          ∀ (s : ZMod 2) (g : GL (Fin 3) (ZMod 2)) (h : z ^ s.val * lev g ∈ X),
            (ψ (Multiplicative.ofAdd s, g) : X ⧸ C₂.subgroupOf X) = QuotientGroup.mk ⟨_, h⟩) ∧
        (∀ P : Sylow 2 (X ⧸ C₂.subgroupOf X),
          (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) ∈ P →
            ∃ y ∈ P, y * QuotientGroup.mk ⟨z, hzX⟩ ≠
              (QuotientGroup.mk ⟨z, hzX⟩ : X ⧸ C₂.subgroupOf X) * y) ∧
        CFSG.Assembly.pCore 2 (X ⧸ C₂.subgroupOf X) = ⊥) ∧
      centralizer (C₂ : Set G) = C₂ ⊔ K ∧ C₂ ⊓ K = ⊥ ∧ Odd (Nat.card K) ∧
      (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) ∧ (∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧
      (∀ k ∈ K, z * k * z⁻¹ = k⁻¹) ∧
      (∃ κ : X →* MulAut C₂, (∀ (x : X) (c : C₂), ((κ x c : C₂) : G) = x * c * (x : G)⁻¹) ∧
        κ.ker = (C₂ ⊔ K).subgroupOf X) ∧
      (∀ c ∈ C₂, c * z = z * c ↔ c ∈ A₂) ∧ Nat.card A₂ = 2 ^ 6 ∧
      {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} = I₂ ∧ Nat.card I₂ = 2 ^ 3 ∧
      (∃ Ψ : Multiplicative ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) ≃* C₂,
        (∀ u v w, z * (Ψ (Multiplicative.ofAdd (u, v, w)) : G) * z⁻¹ =
          Ψ (Multiplicative.ofAdd (u, u + v, w))) ∧
        (∀ u v w, (Ψ (Multiplicative.ofAdd (u, v, w)) : G) ∈ A₂ ↔ u = 0) ∧
        ∀ u v w, (Ψ (Multiplicative.ofAdd (u, v, w)) : G) ∈ I₂ ↔ u = 0 ∧ w = 0) ∧
      (IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) → X ≠ ⊤) := by
  classical
  obtain ⟨-, hzC, hsup, hinf, -⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths.{0} hG hL hLn hZ hmodel T hT hzT hz hH
  have halt' : AltOrbit z φ e := altOrbit_of_eq φ he halt
  intro A₂ R₂ N₂ D₂ I₂ lev
  obtain ⟨C₁, hC₁D, -, hC₁z, hC₁B, hC₁N, -, hC₁sq, -, -, hkey⟩ :=
    exists_extraspecial hzC hsup hinf hz hb hnd hV φ he halt'
  obtain ⟨C₂, hC₂D, hC₂ab, hC₂c, hC₂R, hC₂z', hC₂uniq, hC₂N, hC₂z, hC₂comm, hC₂lab⟩ :=
    abelian_subgroup_structure hzC hsup hinf hz hb hnd hV φ he halt'
  obtain ⟨-, hKe, -, -, hKimg, -, -, -⟩ :=
    kSubgroup_structure hzC hsup hinf hz hb hnd hV φ he halt' hC₁D hC₁N hC₁z hC₁B hC₁sq hkey
      hC₂D hC₂ab hC₂R hC₂z hC₂lab
  have hC₂e : IsElementaryAbelian 2 C₂ := by
    have hj : tauHom φ he (Multiplicative.ofAdd (jSym 0 1 0)) ∈
        (J₀Sub hzC hinf hz hb φ he : Set G) :=
      (mem_J₀_iff hzC hinf hz hb φ he).2 ⟨1, 0, rfl⟩
    rw [← hKimg] at hj
    obtain ⟨k, hk, hkc⟩ := hj
    exact isElementaryAbelian_C₂ hzC hsup hinf hz hb hnd hV φ he halt' hC₂D hC₂ab hC₂R hC₂N
      hC₂z hk.2 hkc (mul_self_of_isElementaryAbelian hKe hk)
  refine ⟨C₂, ?_⟩
  intro X K
  have hzN : z ∈ N₂ := le_normalizer (mem_sup_right (mem_zpowers z))
  have hzX : z ∈ X := by
    change z ∈ normalizer (C₂ : Set G)
    rw [mem_normalizer_iff]
    intro c
    refine ⟨hC₂N z hzN c, fun hc => ?_⟩
    have h1 := hC₂N z⁻¹ (inv_mem hzN) _ hc
    rwa [show z⁻¹ * (z * c * z⁻¹) * z⁻¹⁻¹ = c by group] at h1
  obtain ⟨hAe, hAc, -, -⟩ := pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  obtain ⟨hYab, hYeq, hbot, hKodd, hKn, hKinv⟩ :=
    centralizer_structure hzC hsup hinf hz hb hnd hV φ he halt' hC₂c hC₂R hC₂z hC₂e hC₂N hC₂comm
  obtain ⟨Ψ, hΨz, hΨA, hΨI⟩ :=
    exists_jordan hzC hsup hinf hz hb hnd hV φ he halt' hC₂D hC₂c hC₂R hC₂e hC₂lab
  have hκker := ker_conjAutOf C₂
  rw [hYeq] at hκker
  refine ⟨hC₂D, hC₂ab, hC₂c, hC₂uniq, hC₂e, hC₂N,
    fun F hFN hFe hFc => eq_C₂_of_isElementaryAbelian hzC hsup hinf hz hb hnd hV φ he halt' hC₂D
      hC₂c hC₂R hC₂z' hC₂z hC₂e hFN hFe hFc,
    fun S₂ => ⟨card_sylow_N₂ hzC hsup hinf hz hb hnd hV φ he halt' S₂,
      C₂_le_sylow φ hC₂D hC₂e hC₂N S₂,
      characteristic_C₂ hzC hsup hinf hz hb hnd hV φ he halt' hC₂D hC₂c hC₂R hC₂z' hC₂z hC₂e
        hC₂N S₂,
      fun P => ne_sylow hzC hsup hinf hz hb hnd hV φ he halt' S₂ P,
      fun P hP => lt_inf_normalizer hzC hsup hinf hz hb hnd hV φ he halt' hC₂D hC₂c hC₂R hC₂z'
        hC₂z hC₂e hC₂N S₂ P hP⟩,
    two_pow_five_dvd hzC hsup hinf hz hb hnd hV φ he halt' hC₂D hC₂c hC₂R hC₂z' hC₂z hC₂e hC₂N,
    ⟨hzX, orderOf_mk_z hzC hinf hz hb hnd hV φ he hC₂z hzX,
      centralizer_eq_map hzC hsup hinf hz hb hnd hV φ he halt' hC₂D hC₂R hC₂z hC₂e hC₂comm hzX,
      exists_mulEquiv hzC hsup hinf hz hb hnd hV φ he halt' hC₂D hC₂R hC₂z' hC₂z hC₂e hC₂N hC₂comm
        hzX,
      fun P _ => exists_ne_comm hzC hsup hinf hz hb hnd hV φ he halt' hC₂D hC₂c hC₂R hC₂z' hC₂z
        hC₂e hC₂N hC₂comm hzX P,
      pCore_eq_bot hzC hsup hinf hz hb hnd hV φ he halt' hC₂D hC₂c hC₂R hC₂z' hC₂z hC₂e hC₂N
        hC₂comm hzX⟩,
    hYeq, hbot, hKodd,
    fun x hx y hy => hYab x (hYeq ▸ mem_sup_right hx) y (hYeq ▸ mem_sup_right hy),
    hKn, hKinv, ⟨conjAutOf C₂, coe_conjAutOf_apply C₂, hκker⟩, hC₂z, hAc,
    hC₂comm.trans (tauSet_alt_eq_radI hzC hinf hz φ he).symm, card_tauSet_alt φ he,
    ⟨Ψ, hΨz, hΨA, hΨI⟩, fun hsimp hnab hXtop => ?_⟩
  have hC₂n : C₂.Normal := normalizer_eq_top_iff.1 hXtop
  rcases hsimp.eq_bot_or_eq_top_of_normal C₂ with h | h
  · rw [h, Subgroup.card_bot] at hC₂c
    norm_num at hC₂c
  · obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (hC₂ab x (h ▸ mem_top x) y (h ▸ mem_top y))

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
