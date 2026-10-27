module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixRadicalLabels
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullCosetTwoGroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits RadicalLabels
open LinearMap (BilinForm)
open scoped Pointwise commutatorElement

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {G : Type*} [Group G] {L : Subgroup G}
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
variable (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e)

@[expose] def altSub : Subgroup G where
  carrier := {x | ∃ B : 𝕍, symThreeDiag (B : M₃) = 0 ∧ tauHom φ he (Multiplicative.ofAdd B) = x}
  mul_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨C, hC, rfl⟩
    refine ⟨B + C, ?_, by rw [ofAdd_add, map_mul]⟩
    rw [AddSubgroup.coe_add, symThreeDiag_add, hB, hC, add_zero]
  one_mem' := ⟨0, rfl, by rw [ofAdd_zero, map_one]⟩
  inv_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    refine ⟨B, hB, ?_⟩
    rw [← map_inv, inv_eq_of_mul_eq_one_left]
    rw [← ofAdd_add, symThree_add_self, ofAdd_zero]

theorem mem_altSub {x : G} :
    x ∈ altSub φ he ↔ ∃ B : 𝕍, symThreeDiag (B : M₃) = 0 ∧
      tauHom φ he (Multiplicative.ofAdd B) = x :=
  Iff.rfl

variable {z : G} (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2)
  (hinf : L ⊓ zpowers z = ⊥)

local notation "ℛ" => radSub φ z e
local notation "𝒩" => normalizer ((radSub φ z e : Subgroup G) : Set G)

instance radSub_subgroupOf_normal :
    ((radSub φ z e).subgroupOf (normalizer ((radSub φ z e : Subgroup G) : Set G))).Normal :=
  Subgroup.normal_in_normalizer

abbrev θN (hinf : L ⊓ zpowers z = ⊥) :
    (radSub φ z e).subgroupOf (normalizer ((radSub φ z e : Subgroup G) : Set G)) ≃*
      Multiplicative (𝕍 × ZMod 2) :=
  radLabelOf φ he hzC hz hinf le_normalizer

theorem coe_θN_symm (x : Multiplicative (𝕍 × ZMod 2)) :
    (((θN φ he hzC hz hinf).symm x : 𝒩) : G) = radHom φ he hzC hz x :=
  rfl

omit hzC hz in
theorem z_mem_radSub : z ∈ ℛ :=
  mem_sup_right (mem_zpowers z)

theorem radHom_one_eq (B : 𝕍) :
    radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) =
      z * tauHom φ he (Multiplicative.ofAdd B) := by
  rw [radHom_apply, zPow_one, mul_comm_z hzC (tauHom_mem φ he _)]

theorem mem_smul_radA_iff {x : G} :
    x ∈ z • (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G) ↔
      ∃ B : 𝕍, radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    exact ⟨Multiplicative.toAdd B, by rw [radHom_one_eq, ofAdd_toAdd]; rfl⟩
  · rintro ⟨B, rfl⟩
    rw [radHom_one_eq]
    exact Set.smul_mem_smul_set ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩)

omit [Group G] in
theorem mem_map_subtype_iff {G : Type*} [Group G] {N : Subgroup G} {D : Subgroup N} {x : G} :
    x ∈ D.map N.subtype ↔ ∃ h : x ∈ N, (⟨x, h⟩ : N) ∈ D := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d.2, hd⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

include hinf in
theorem degree64_lagrangian_two_group
    (hker : (MulAction.toPermHom 𝒩 (conjClass 𝒩 z)).ker = (radSub φ z e).subgroupOf 𝒩)
    (σ : (𝒩 ⊓ centralizer ({z} : Set G) : Subgroup G) →* GL (Fin 3) (ZMod 2))
    (hσ : ∀ (n : (𝒩 ⊓ centralizer ({z} : Set G) : Subgroup G)) (a : G) (ha : a ∈ L) (B : M₃),
      Bᵀ = B → LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
      ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
        LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
          fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)
    (hfull : conjClass 𝒩 z = z • (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G)) :
    ∃ (κ₂ : ZMod 2) (D₂ F₂ : Subgroup G) (ν₂ : G → 𝕍),
      D₂ = CFSG.Assembly.pCoreOf 2 𝒩 ∧ F₂ ≤ D₂ ∧ D₂ ≤ 𝒩 ∧ ℛ ≤ F₂ ∧
      (∀ n ∈ 𝒩, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂) ∧ (∀ n ∈ 𝒩, ∀ f ∈ F₂, n * f * n⁻¹ ∈ F₂) ∧
      Nat.card D₂ = 8192 ∧ Nat.card F₂ = 1024 ∧
      (∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1))) ∧
      (∀ d ∈ D₂, ∀ d' ∈ D₂, ν₂ d = ν₂ d' ↔ d⁻¹ * d' ∈ ℛ) ∧
      (∀ C : 𝕍, ∃ d ∈ D₂, ν₂ d = C) ∧
      (∀ d ∈ D₂, ∀ (B : 𝕍) (ε : ZMod 2),
        d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε))) ∧
      (∀ d : G, d ∈ F₂ ↔ d ∈ D₂ ∧ symThreeDiag (ν₂ d : M₃) = 0) ∧
      (∀ m ∈ 𝒩, ∃ d ∈ D₂, ∃ c ∈ (𝒩 ⊓ centralizer ({z} : Set G) : Subgroup G), m = d * c) ∧
      D₂ ⊓ centralizer ({z} : Set G) = ℛ ∧
      (∀ d ∈ D₂, d ^ 2 ∈ ℛ) ∧ (∀ d ∈ D₂, ∀ d' ∈ D₂, ⁅d, d'⁆ ∈ ℛ) ∧
      (∀ m ∈ 𝒩, (∀ B : 𝕍, m⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) * m =
        radHom φ he hzC hz (Multiplicative.ofAdd (B, 1))) → m ∈ ℛ) := by
  classical
  set θ := θN φ he hzC hz hinf with hθ
  have hzN : z ∈ 𝒩 := le_normalizer (z_mem_radSub φ)
  set zN : 𝒩 := ⟨z, hzN⟩ with hzNdef
  have hzθ : zN = θ.symm (Multiplicative.ofAdd (0, 1)) :=
    Subtype.ext (by rw [coe_θN_symm, radHom_z])
  have hθv : ∀ x, ((θ.symm x : 𝒩) : G) = radHom φ he hzC hz x := fun x => rfl
  have hΩmem : ∀ B : 𝕍, radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) ∈ conjClass 𝒩 z :=
    fun B => by
      rw [hfull]
      exact (mem_smul_radA_iff φ he hzC hz).2 ⟨B, rfl⟩
  have hΩinv : ∀ x ∈ conjClass 𝒩 z, ∃ B : 𝕍,
      radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) = x := fun x hx => by
    rw [hfull] at hx
    exact (mem_smul_radA_iff φ he hzC hz).1 hx
  set AN := (pullSub φ (pointwiseStabilizer b (lagrangianOf e))).subgroupOf 𝒩 with hAN
  set IN := (altSub φ he).subgroupOf 𝒩 with hIN
  have hA : ∀ x : 𝒩, x ∈ AN ↔ ∃ B : 𝕍, x = θ.symm (Multiplicative.ofAdd (B, 0)) := by
    intro x
    rw [hAN, mem_subgroupOf, mem_pullSub_iff φ he]
    constructor
    · rintro ⟨B, hB⟩
      exact ⟨Multiplicative.toAdd B, Subtype.ext (by rw [hθv, radHom_tau, ofAdd_toAdd, hB])⟩
    · rintro ⟨B, rfl⟩
      exact ⟨Multiplicative.ofAdd B, by rw [hθv, radHom_tau]⟩
  have hI : ∀ x : 𝒩, x ∈ IN ↔ ∃ B : 𝕍,
      symThreeDiag (B : M₃) = 0 ∧ x = θ.symm (Multiplicative.ofAdd (B, 0)) := by
    intro x
    rw [hIN, mem_subgroupOf, mem_altSub]
    constructor
    · rintro ⟨B, hB, hBx⟩
      exact ⟨B, hB, Subtype.ext (by rw [hθv, radHom_tau, hBx])⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B, hB, by rw [hθv, radHom_tau]⟩
  have hΩ : ∀ (m : 𝒩) (B : 𝕍), ∃ B' : 𝕍,
      m⁻¹ * (θ.symm (Multiplicative.ofAdd (B, 1)) : 𝒩) * m =
        θ.symm (Multiplicative.ofAdd (B', 1)) := by
    intro m B
    obtain ⟨B', hB'⟩ := hΩinv _ (conj_mem_conjClass_right m.2 (hΩmem B))
    exact ⟨B', Subtype.ext hB'.symm⟩
  have hfaith' : ∀ m ∈ 𝒩, (∀ B : 𝕍, m⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) * m =
      radHom φ he hzC hz (Multiplicative.ofAdd (B, 1))) → m ∈ ℛ := by
    intro m hm h
    have hk : (⟨m, hm⟩ : 𝒩) ∈ (MulAction.toPermHom 𝒩 (conjClass 𝒩 z)).ker := by
      rw [mem_ker_toPermHom_conjClass]
      intro x hx
      obtain ⟨B, rfl⟩ := hΩinv x hx
      have h1 := h B
      calc m * radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) * m⁻¹ =
          m * (m⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) * m) * m⁻¹ := by rw [h1]
        _ = _ := by group
    rw [hker, mem_subgroupOf] at hk
    exact hk
  have hfaith : ∀ m : 𝒩, (∀ B : 𝕍,
      m⁻¹ * (θ.symm (Multiplicative.ofAdd (B, 1)) : 𝒩) * m =
        θ.symm (Multiplicative.ofAdd (B, 1))) → m ∈ (radSub φ z e).subgroupOf 𝒩 := by
    intro m h
    rw [mem_subgroupOf]
    exact hfaith' m m.2 fun B => congrArg Subtype.val (h B)
  have htrans : ∀ B B' : 𝕍, ∃ m : 𝒩,
      m⁻¹ * (θ.symm (Multiplicative.ofAdd (B, 1)) : 𝒩) * m =
        θ.symm (Multiplicative.ofAdd (B', 1)) := by
    intro B B'
    obtain ⟨n, hn, hnx⟩ := mem_conjClass_iff_right.1 (hΩmem B)
    obtain ⟨n', hn', hnx'⟩ := mem_conjClass_iff_right.1 (hΩmem B')
    refine ⟨⟨n, hn⟩⁻¹ * ⟨n', hn'⟩, Subtype.ext ?_⟩
    change (n⁻¹ * n')⁻¹ * radHom φ he hzC hz _ * (n⁻¹ * n') = radHom φ he hzC hz _
    rw [← hnx, ← hnx']
    group
  have hstab : ∀ m : 𝒩, m⁻¹ * zN * m = zN → ∃ D : GL (Fin 3) (ZMod 2), ∀ B : 𝕍,
      m⁻¹ * (θ.symm (Multiplicative.ofAdd (B, 1)) : 𝒩) * m =
        θ.symm (Multiplicative.ofAdd (symThreeCongr D B, 1)) := by
    intro m hm
    have hm' : (m : G)⁻¹ * z * m = z := congrArg Subtype.val hm
    have hmz : (m : G)⁻¹ ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (m : G)⁻¹ * z = (m : G)⁻¹ * z * m * (m : G)⁻¹ := by group
        _ = z * (m : G)⁻¹ := by rw [hm']
    set n : (𝒩 ⊓ centralizer ({z} : Set G) : Subgroup G) :=
      ⟨(m : G)⁻¹, mem_inf.2 ⟨inv_mem m.2, hmz⟩⟩ with hn
    refine ⟨σ n, fun B => Subtype.ext ?_⟩
    have h1 := conj_radHom_of_sigma φ he hzC hz inf_le_right σ hσ n B 1
    change (m : G)⁻¹ * radHom φ he hzC hz _ * m = radHom φ he hzC hz _
    rw [← h1, hn]
    simp only [inv_inv]
  have hstab' : ∀ D : GL (Fin 3) (ZMod 2), ∃ m : 𝒩, ∀ B : 𝕍,
      m⁻¹ * (θ.symm (Multiplicative.ofAdd (B, 1)) : 𝒩) * m =
        θ.symm (Multiplicative.ofAdd (symThreeCongr D B, 1)) := by
    intro D
    refine ⟨⟨(leviHom φ he D)⁻¹,
      inv_mem (leviHom_mem_normalizer_radSub φ he hzC hz D)⟩, fun B => Subtype.ext ?_⟩
    change ((leviHom φ he D)⁻¹)⁻¹ * radHom φ he hzC hz _ * (leviHom φ he D)⁻¹ = radHom φ he hzC hz _
    rw [inv_inv, leviHom_conj_radHom]
  obtain ⟨κ, D, F, ν, hFD, hDn, hFn, hpc, hDc, hFc, hRF, ⟨hsqD, hcomD, -⟩, -, -, hνz, hνeq,
    hνsurj, hact, hFiff, hprod, hDH, -⟩ :=
    binary_symmetric_three_full_coset_two_group_structure ((radSub φ z e).subgroupOf 𝒩) θ zN hzθ
      AN IN hA hI hΩ hfaith htrans hstab hstab'
  set ν₂ : G → 𝕍 := fun g => if h : g ∈ 𝒩 then ν ⟨g, h⟩ else 0 with hν₂
  have hν₂ : ∀ (g : G) (h : g ∈ 𝒩), ν₂ g = ν ⟨g, h⟩ := fun g h => by
    simp only [hν₂, h, ↓reduceDIte]
  have hmemD : ∀ {x : G}, x ∈ D.map (Subgroup.subtype 𝒩) ↔
      ∃ h : x ∈ 𝒩, (⟨x, h⟩ : 𝒩) ∈ D :=
    mem_map_subtype_iff
  have hmemF : ∀ {x : G}, x ∈ F.map (Subgroup.subtype 𝒩) ↔
      ∃ h : x ∈ 𝒩, (⟨x, h⟩ : 𝒩) ∈ F :=
    mem_map_subtype_iff
  refine ⟨κ, D.map (Subgroup.subtype 𝒩), F.map (Subgroup.subtype 𝒩), ν₂, ?_, map_mono hFD,
    map_subtype_le _,
    fun r hr => hmemF.2 ⟨le_normalizer hr, hRF (by rw [mem_subgroupOf]; exact hr)⟩,
    fun n hn d hd => ?_, fun n hn f hf => ?_, ?_, ?_, fun d hd => ?_, fun d hd d' hd' => ?_,
    fun C => ?_, fun d hd B ε => ?_, fun d => ?_, fun m hm => ?_, ?_, fun d hd => ?_,
    fun d hd d' hd' => ?_, hfaith'⟩
  · rw [CFSG.Assembly.pCoreOf, hpc]
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    exact hmemD.2 ⟨mul_mem (mul_mem hn hd') (inv_mem hn),
      hDn.conj_mem _ hdD ⟨n, hn⟩⟩
  · obtain ⟨hf', hfF⟩ := hmemF.1 hf
    exact hmemF.2 ⟨mul_mem (mul_mem hn hf') (inv_mem hn),
      hFn.conj_mem _ hfF ⟨n, hn⟩⟩
  · rw [card_map_of_injective (subtype_injective _), hDc]
  · rw [card_map_of_injective (subtype_injective _), hFc]
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    have h1 := congrArg Subtype.val (hνz _ hdD)
    rw [hν₂ d hd', ← hθv, ← h1]
    rfl
  · obtain ⟨h1, h1D⟩ := hmemD.1 hd
    obtain ⟨h2, h2D⟩ := hmemD.1 hd'
    rw [hν₂ d h1, hν₂ d' h2, hνeq _ h1D _ h2D, mem_subgroupOf]
    rfl
  · obtain ⟨d, hdD, hdC⟩ := hνsurj C
    refine ⟨d, ⟨d, hdD, rfl⟩, ?_⟩
    rw [hν₂ d d.2]
    exact hdC
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    have h1 := congrArg Subtype.val (hact _ hdD B ε)
    rw [hν₂ d hd', ← hθv, ← hθv, ← h1]
    rfl
  · constructor
    · intro hdF
      obtain ⟨hd', hdF'⟩ := hmemF.1 hdF
      obtain ⟨hdD, hd0⟩ := (hFiff _).1 hdF'
      exact ⟨hmemD.2 ⟨hd', hdD⟩, by rw [hν₂ d hd']; exact hd0⟩
    · rintro ⟨hdD, hd0⟩
      obtain ⟨hd', hdD'⟩ := hmemD.1 hdD
      exact hmemF.2 ⟨hd', (hFiff _).2 ⟨hdD', by rw [hν₂ d hd'] at hd0; exact hd0⟩⟩
  · obtain ⟨d, hdD, c, hc, hdc⟩ := hprod ⟨m, hm⟩
    refine ⟨d, ⟨d, hdD, rfl⟩, c, mem_inf.2 ⟨c.2, ?_⟩, congrArg Subtype.val hdc⟩
    have hc' := mem_centralizer_singleton_iff.1 hc
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hc'
  · ext x
    rw [mem_inf, hmemD]
    constructor
    · rintro ⟨⟨hx, hxD⟩, hxz⟩
      have h1 : (⟨x, hx⟩ : 𝒩) ∈ D ⊓ centralizer {zN} := mem_inf.2 ⟨hxD,
        mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 hxz))⟩
      rw [hDH, mem_subgroupOf] at h1
      exact h1
    · intro hx
      have h1 : (⟨x, le_normalizer hx⟩ : 𝒩) ∈ (radSub φ z e).subgroupOf 𝒩 := by
        rw [mem_subgroupOf]
        exact hx
      rw [← hDH, mem_inf] at h1
      exact ⟨⟨le_normalizer hx, h1.1⟩, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 h1.2))⟩
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    have h1 := hsqD _ hdD
    rw [mem_subgroupOf] at h1
    exact h1
  · obtain ⟨h1, h1D⟩ := hmemD.1 hd
    obtain ⟨h2, h2D⟩ := hmemD.1 hd'
    have h3 := hcomD _ h1D _ h2D
    rw [mem_subgroupOf] at h3
    exact h3

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
