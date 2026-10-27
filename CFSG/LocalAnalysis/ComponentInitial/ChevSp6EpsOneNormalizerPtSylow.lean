module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtOrders
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtFull
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerE2Unique
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveOrthogonalGroup
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open SymplecticTorusWeyl
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

section Generic

variable {X : Type*} [Group X]

theorem exists_sylow_map_eq {p : ℕ} [Fact p.Prime] {P Y : Subgroup X} (hPY : P ≤ Y)
    (hp : IsPGroup p P) (hidx : ¬ p ∣ P.relIndex Y) :
    ∃ Q : Sylow p Y, (Q : Subgroup Y).map Y.subtype = P := by
  have hp' : IsPGroup p (P.subgroupOf Y) := hp.of_equiv (subgroupOfEquivOfLe hPY).symm
  refine ⟨hp'.toSylow hidx, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_subgroupOf.1 ((IsPGroup.mem_toSylow hp' hidx).1 hy)
  · intro hx
    exact ⟨⟨x, hPY hx⟩, (IsPGroup.mem_toSylow hp' hidx).2 (mem_subgroupOf.2 hx), rfl⟩

theorem relIndex_mul_card_of_le {P Y : Subgroup X} (hPY : P ≤ Y) :
    P.relIndex Y * Nat.card P = Nat.card Y := by
  have h := Subgroup.relIndex_mul_card (H := P) (K := Y)
  rwa [inf_of_le_left hPY] at h

theorem mem_of_mem_zpowers_sup [Finite X] {t : X} (ht : orderOf t = 2) {P C : Subgroup X}
    (hPC : P ≤ C) (htC : t ∉ C) (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) {x : X}
    (hx : x ∈ zpowers t ⊔ P) (hxC : x ∈ C) : x ∈ P := by
  have hle : zpowers t ≤ normalizer (P : Set X) := by
    rw [zpowers_le]
    exact mem_normalizer_of_conj_mem hn
  have hx' : x ∈ ((zpowers t ⊔ P : Subgroup X) : Set X) := hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hle] at hx'
  obtain ⟨u, hu, p, hp, rfl⟩ := hx'
  have huC : u ∈ C := by
    have h1 : u * p * p⁻¹ = u := by group
    rw [← h1]
    exact mul_mem hxC (inv_mem (hPC hp))
  have h2 : u ∈ zpowers t ⊓ C := mem_inf.2 ⟨hu, huC⟩
  rw [zpowers_inf_eq_bot_of_not_mem ht htC, mem_bot] at h2
  change u * p ∈ P
  rw [h2, one_mul]
  exact hp

end Generic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} {he : IsSymplecticBasis b e} {hb : b.IsAlt}
variable {G : Type} [Group G] {L : Subgroup G} {φ : L ≃* bilinIsometryGroup b} {z : G}
  {hzC : z ∈ centralizer (L : Set G)} {hz : orderOf z = 2}
variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}
variable {D₁ C₁ F₁ : Subgroup G} {ν₁ : G → pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2}

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)
local notation "𝒰₃" => Subgroup.map (leviHom φ he) (unitriangularGL 3 (ZMod 2))

section Orders

variable [Finite G] (h : PtFull he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
include h

omit [Finite G] h in
theorem card_L_of (φ' : L ≃* bilinIsometryGroup b) (he' : IsSymplecticBasis b e) :
    Nat.card L = 1451520 := by
  rw [Nat.card_congr φ'.toEquiv, Nat.card_congr (spCoord he').toEquiv,
    (symplectic_higher_order_and_Sylow (K := ZMod 2) 2 2 (Nat.card_zmod 2)
      (r := 3) (by norm_num)).1]
  decide

omit [Finite G] in
theorem PtFull.card_H : Nat.card (centralizer ({z} : Set G)) = 2903040 := by
  rw [← h.hsup]
  have hle : zpowers z ≤ normalizer (L : Set G) := by
    rw [zpowers_le]
    exact centralizer_le_normalizer _ hzC
  have h1 := natCard_sup_mul_inf hle
  rw [inf_comm, h.hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hz, card_L_of φ he,
    sup_comm] at h1
  rw [h1]

theorem PtFull.card_N₁₀ :
    Nat.card (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G) = 46080 := by
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ h.hV
  set ρ := ptStab he hb h.hnd φ hzC h.hsup h.hinf hz with hρ
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (ptStab_surjective he hb h.hnd φ hzC h.hsup h.hinf hz)).toEquiv,
    OddQuadraticFive.Orth.card_bilinIsometryGroup (finrank_pairOrth_eq he hb h.hnd)
      (fun x => hb x) (hb.restrict_nondegenerate_orthogonal_span_pair (bilin_f_u he) h.hnd),
    ker_ptStab] at h1
  have hBN : ℬ₁ ≤ 𝒩₁ ⊓ centralizer ({z} : Set G) :=
    le_inf le_normalizer (ptSub_le_centralizer he hb h.hnd φ h.hsup)
  rw [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv,
    (ptSub_facts he hb h.hnd φ hzC h.hinf hz).2.2.1] at h1
  rw [h1]

omit [Finite G] in
theorem PtFull.N₁_eq : 𝒩₁ = D₁ ⊔ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  refine le_antisymm (fun m hm => ?_) (sup_le h.hD₁N inf_le_left)
  obtain ⟨d, hd, c, hc, rfl⟩ := h.hprod₁ m hm
  exact mul_mem (mem_sup_left hd) (mem_sup_right hc)

omit [Finite G] in
theorem PtFull.N₂_eq : 𝒩₂ = D₂ ⊔ (𝒩₂ ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  refine le_antisymm (fun m hm => ?_) (sup_le h.hD₂N inf_le_left)
  obtain ⟨d, hd, c, hc, rfl⟩ := h.hprod₂ m hm
  exact mul_mem (mem_sup_left hd) (mem_sup_right hc)

theorem PtFull.card_N₁ : Nat.card 𝒩₁ = 2 ^ 15 * 45 := by
  have hle : (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ normalizer (D₁ : Set G) :=
    fun c hc => mem_normalizer_of_conj_mem fun d hd => h.hD₁n c (mem_inf.1 hc).1 d hd
  have h1 := natCard_sup_mul_inf hle
  have hinf' : (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G) ⊓ D₁ = ℬ₁ := by
    rw [inf_comm, ← inf_assoc, inf_of_le_left h.hD₁N, h.hD₁H]
  rw [hinf', (ptSub_facts he hb h.hnd φ hzC h.hinf hz).2.2.1, h.card_N₁₀, h.hD₁card,
    sup_comm, ← h.N₁_eq] at h1
  omega

omit [Finite G] in
theorem PtFull.card_N₂₀ :
    Nat.card (𝒩₂ ⊓ centralizer ({z} : Set G) : Subgroup G) = 21504 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ h.hσsurj).toEquiv,
    card_GL_three_two, h.hσker] at h1
  have hRN : ℛ ≤ (𝒩₂ ⊓ centralizer ({z} : Set G) : Subgroup G) :=
    le_inf le_normalizer (radSub_le_centralizer φ h.hsup)
  rw [Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv, card_radSub he φ hzC h.hinf hz] at h1
  rw [h1]

theorem PtFull.card_N₂ : Nat.card 𝒩₂ = 2 ^ 16 * 21 := by
  have hle : (𝒩₂ ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ normalizer (D₂ : Set G) :=
    fun c hc => mem_normalizer_of_conj_mem fun d hd => h.hD₂n c (mem_inf.1 hc).1 d hd
  have h1 := natCard_sup_mul_inf hle
  have hinf' : (𝒩₂ ⊓ centralizer ({z} : Set G) : Subgroup G) ⊓ D₂ = ℛ := by
    rw [inf_comm, ← inf_assoc, inf_of_le_left h.hD₂N, h.hD₂H]
  rw [hinf', card_radSub he φ hzC h.hinf hz, h.card_N₂₀, h.hD₂card, sup_comm, ← h.N₂_eq] at h1
  omega

omit [Finite G] h in
theorem leviHom_injective_of (he' : IsSymplecticBasis b e) : Function.Injective (leviHom φ he') :=
  (spHom_injective φ he').comp leviSp_injective

omit [Finite G] h in
theorem card_U₃_of (he' : IsSymplecticBasis b e) :
    Nat.card (Subgroup.map (leviHom φ he') (unitriangularGL 3 (ZMod 2))) = 8 := by
  rw [Subgroup.card_map_of_injective (leviHom_injective_of he'), card_unitriangularGL]

omit [Finite G] h in
theorem U₃_le_L (he' : IsSymplecticBasis b e) :
    Subgroup.map (leviHom φ he') (unitriangularGL 3 (ZMod 2)) ≤ L := by
  rintro _ ⟨g, -, rfl⟩
  exact leviHom_mem φ he' g

omit h in
theorem U₃_le_normalizer_A₂_of (he' : IsSymplecticBasis b e) :
    Subgroup.map (leviHom φ he') (unitriangularGL 3 (ZMod 2)) ≤ normalizer (𝒜₂ : Set G) := by
  rintro _ ⟨g, -, rfl⟩
  refine mem_normalizer_of_conj_mem fun a ha => ?_
  obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he').1 ha
  have h1 := leviHom_conj_tauHom' φ he' g (Multiplicative.toAdd B)
  rw [ofAdd_toAdd] at h1
  rw [h1]
  exact (mem_pullSub_iff φ he').2 ⟨_, rfl⟩

omit [Finite G] h in
theorem A₂_inf_U₃_of (he' : IsSymplecticBasis b e) :
    𝒜₂ ⊓ Subgroup.map (leviHom φ he') (unitriangularGL 3 (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxU⟩ := mem_inf.1 hx
  obtain ⟨g, -, rfl⟩ := hxU
  obtain ⟨B, hB⟩ := (mem_pullSub_iff φ he').1 hxA
  have h1 : tauSym 3 B = leviSp g := spHom_injective φ he' hB
  obtain ⟨-, hg⟩ := tauSym_eq_leviSp h1
  rw [hg, map_one]
  exact one_mem _

omit h in
theorem card_A₂U₃_of (he' : IsSymplecticBasis b e) :
    Nat.card (𝒜₂ ⊔ Subgroup.map (leviHom φ he') (unitriangularGL 3 (ZMod 2)) : Subgroup G) =
      512 := by
  have h1 := natCard_sup_mul_inf (X := G) (U₃_le_normalizer_A₂_of (φ := φ) he')
  rw [inf_comm, A₂_inf_U₃_of he', Subgroup.card_bot, mul_one, card_U₃_of he',
    card_pullSub_radA he' φ, sup_comm] at h1
  rw [h1]

omit [Finite G] h in
theorem A₁_le_A₂U₃_of (he' : IsSymplecticBasis b e) :
    𝒜₁ ≤ 𝒜₂ ⊔ Subgroup.map (leviHom φ he') (unitriangularGL 3 (ZMod 2)) := by
  intro x hx
  have hx' : x ∈ (𝒜₁ : Set G) := hx
  rw [coe_pullSub_pointRadical] at hx'
  obtain ⟨w, c, rfl⟩ := hx'
  have hw : (w : V) ∈ pointSpan e := by
    rw [pointSpan_eq_pairOrth he']
    exact w.2
  have h1 := spCoord_pointElt_eq he' hb hw c
  have h2 : ((φ.symm (pointElt hb (mem_pairOrth_left w.2) c) : L) : G) =
      spHom φ he' (spCoord he' (pointElt hb (mem_pairOrth_left w.2) c)) := by
    change _ = ((φ.symm ((spCoord he').symm (spCoord he' _)) : L) : G)
    rw [MulEquiv.symm_apply_apply]
  rw [h2, h1, map_mul]
  refine mul_mem (mem_sup_left ((mem_pullSub_iff φ he').2 ⟨_, rfl⟩)) (mem_sup_right ⟨_, ?_, rfl⟩)
  change t0Unit _ _ ∈ unitriangularGL 3 (ZMod 2)
  rw [mem_unitriangularGL, coe_t0Unit]
  exact isUnitriangular_t0Mat _ _

theorem PtFull.card_S_H : Nat.card (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃ : Subgroup G) = 2 ^ 10 := by
  have hAUL : 𝒜₂ ⊔ 𝒰₃ ≤ L := sup_le (pullSub_le φ _) (U₃_le_L he)
  rw [sup_assoc, card_zpowers_sup_of_not_mem hz (fun hz' => by
      have h2 : z ∈ L ⊓ zpowers z := mem_inf.2 ⟨hAUL hz', mem_zpowers z⟩
      rw [h.hinf, mem_bot] at h2
      rw [h2, orderOf_one] at hz
      exact absurd hz (by norm_num))
    (fun x hx => by rw [← mul_comm_z hzC (hAUL hx), mul_inv_cancel_right]; exact hx),
    card_A₂U₃_of he]
  norm_num

omit [Finite G] in
theorem PtFull.S_H_le_H : zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃ ≤ centralizer ({z} : Set G) := by
  rw [← h.hsup]
  exact sup_le (sup_le le_sup_right (le_sup_left.trans' (pullSub_le φ _)))
    ((U₃_le_L he).trans le_sup_left)

theorem PtFull.sylow_S_H : ∃ P : Sylow 2 (centralizer ({z} : Set G)),
    (P : Subgroup (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype =
      zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_sylow_map_eq h.S_H_le_H (IsPGroup.of_card h.card_S_H) ?_
  have h1 := relIndex_mul_card_of_le h.S_H_le_H
  rw [h.card_S_H, h.card_H] at h1
  have h2 : (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃ : Subgroup G).relIndex (centralizer ({z} : Set G)) = 2835 := by
    omega
  rw [h2]
  decide

omit [Finite G] h in
theorem leviHom_mem_N₂₀ (he' : IsSymplecticBasis b e) (hzC' : z ∈ centralizer (L : Set G))
    (hz' : orderOf z = 2) (g : GL (Fin 3) (ZMod 2)) :
    leviHom φ he' g ∈ (𝒩₂ ⊓ centralizer ({z} : Set G) : Subgroup G) :=
  mem_inf.2 ⟨leviHom_mem_normalizer_radSub φ he' hzC' hz' g,
    mem_centralizer_singleton_iff.2 (leviHom_mul_z φ he' hzC' g)⟩

omit [Finite G] in
theorem PtFull.sigma_levi (g : GL (Fin 3) (ZMod 2)) :
    σ ⟨leviHom φ he g, leviHom_mem_N₂₀ he hzC hz g⟩ = g := by
  refine symThreeCongrHom_injective (LinearEquiv.ext fun B => ?_)
  rw [symThreeCongrHom_apply, symThreeCongrHom_apply]
  have h1 := conj_tauHom_of_sigma φ he σ h.hσ ⟨leviHom φ he g, leviHom_mem_N₂₀ he hzC hz g⟩ B
  have h2 := leviHom_conj_tauHom' φ he g B
  exact Multiplicative.ofAdd.injective (tauHom_injective φ he (h1.symm.trans h2))

omit [Finite G] in
theorem PtFull.U₃_le_N₁ : 𝒰₃ ≤ 𝒩₁ := by
  rintro _ ⟨g, hg, rfl⟩
  have h1 := (mem_normalizer_ptSub_iff_sigma he hb h.hnd φ hzC h.hsup h.hinf hz σ h.hσcol
    h.hσker ⟨leviHom φ he g, leviHom_mem_N₂₀ he hzC hz g⟩).2
  rw [h.sigma_levi] at h1
  refine h1 ?_
  have hg' : g ∈ unitriangularGL 3 (ZMod 2) := hg
  rw [mem_unitriangularGL] at hg'
  rw [mem_vecStabGL]
  exact ⟨hg'.2 0, hg'.1 (by decide), hg'.1 (by decide)⟩

omit [Finite G] h in
theorem U₃_le_N₂_of (he' : IsSymplecticBasis b e) (hzC' : z ∈ centralizer (L : Set G))
    (hz' : orderOf z = 2) : Subgroup.map (leviHom φ he') (unitriangularGL 3 (ZMod 2)) ≤ 𝒩₂ := by
  rintro _ ⟨g, -, rfl⟩
  exact leviHom_mem_normalizer_radSub φ he' hzC' hz' g

omit [Finite G] in
theorem PtFull.S_H_le : zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃ ≤ 𝒩₁ ⊓ 𝒩₂ :=
  le_inf (sup_le (sup_le (zpowers_le.2 z_mem_N₁) h.A₂N₁) h.U₃_le_N₁)
    (sup_le (sup_le (zpowers_le.2 z_mem_N₂) fun _ ha => le_normalizer (mem_sup_left ha))
      (U₃_le_N₂_of he hzC hz))

omit [Finite G] h in
theorem B₁_le_S_H_of (he' : IsSymplecticBasis b e) :
    ℬ₁ ≤ zpowers z ⊔ 𝒜₂ ⊔ Subgroup.map (leviHom φ he') (unitriangularGL 3 (ZMod 2)) :=
  sup_le ((A₁_le_A₂U₃_of he').trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
    (le_sup_left.trans le_sup_left)

omit [Finite G] h in
theorem R₂_le_S_H_of (he' : IsSymplecticBasis b e) :
    ℛ ≤ zpowers z ⊔ 𝒜₂ ⊔ Subgroup.map (leviHom φ he') (unitriangularGL 3 (ZMod 2)) :=
  sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)

omit [Finite G] in
theorem PtFull.S_H_inf_D₁ : (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) ⊓ D₁ = ℬ₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (B₁_le_S_H_of he) (h.hBF₁.trans h.hFD₁))
  rw [← h.hD₁H]
  exact mem_inf.2 ⟨(mem_inf.1 hx).2, h.S_H_le_H (mem_inf.1 hx).1⟩

omit [Finite G] in
theorem PtFull.S_H_inf_D₂ : (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) ⊓ D₂ = ℛ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (R₂_le_S_H_of he) h.hRD₂)
  rw [← h.hD₂H]
  exact mem_inf.2 ⟨(mem_inf.1 hx).2, h.S_H_le_H (mem_inf.1 hx).1⟩

theorem PtFull.card_S₁ : Nat.card (D₁ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) : Subgroup G) = 2 ^ 15 := by
  have hle : zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃ ≤ normalizer (D₁ : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem fun d hd => h.hD₁n x (mem_inf.1 (h.S_H_le hx)).1 d hd
  have h1 := natCard_sup_mul_inf hle
  rw [h.S_H_inf_D₁, (ptSub_facts he hb h.hnd φ hzC h.hinf hz).2.2.1, h.card_S_H, h.hD₁card,
    sup_comm] at h1
  omega

theorem PtFull.card_S₂ : Nat.card (D₂ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) : Subgroup G) = 2 ^ 16 := by
  have hle : zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃ ≤ normalizer (D₂ : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem fun d hd => h.hD₂n x (mem_inf.1 (h.S_H_le hx)).2 d hd
  have h1 := natCard_sup_mul_inf hle
  rw [h.S_H_inf_D₂, card_radSub he φ hzC h.hinf hz, h.card_S_H, h.hD₂card, sup_comm] at h1
  omega

theorem PtFull.sylow_S₁ : ∃ P : Sylow 2 𝒩₁,
    (P : Subgroup 𝒩₁).map (𝒩₁).subtype = D₁ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : D₁ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) ≤ 𝒩₁ :=
    sup_le h.hD₁N (fun x hx => (mem_inf.1 (h.S_H_le hx)).1)
  refine exists_sylow_map_eq hle (IsPGroup.of_card h.card_S₁) ?_
  have h1 := relIndex_mul_card_of_le hle
  rw [h.card_S₁, h.card_N₁] at h1
  have h2 : (D₁ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) : Subgroup G).relIndex 𝒩₁ = 45 := by omega
  rw [h2]
  decide

theorem PtFull.sylow_S₂ : ∃ P : Sylow 2 𝒩₂,
    (P : Subgroup 𝒩₂).map (𝒩₂).subtype = D₂ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : D₂ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) ≤ 𝒩₂ :=
    sup_le h.hD₂N (fun x hx => (mem_inf.1 (h.S_H_le hx)).2)
  refine exists_sylow_map_eq hle (IsPGroup.of_card h.card_S₂) ?_
  have h1 := relIndex_mul_card_of_le hle
  rw [h.card_S₂, h.card_N₂] at h1
  have h2 : (D₂ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) : Subgroup G).relIndex 𝒩₂ = 21 := by omega
  rw [h2]
  decide

theorem PtFull.card_B_inf_H_le :
    Nat.card ((zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)))) ⊓ centralizer ({z} : Set G) :
      Subgroup G) ≤ 2 ^ 9 := by
  set B := zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) with hB
  have hK₀B : C₁ ⊓ C₂ ≤ B := le_sup_right.trans (le_sup_left.trans le_sup_right)
  have hsub : conjClass (C₁ ⊓ D₂) z ⊆ conjClass B z := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hK₀B (by rw [h.K₀_eq]; exact hk), rfl⟩
  have h8 : Nat.card (conjClass (C₁ ⊓ D₂) z) = 8 := by
    rw [h.hK₀z, card_smul_set, SetLike.coe_sort_coe, card_ptA_inf_radA he hb φ]
  have hle : 8 ≤ Nat.card (conjClass B z) := by
    rw [← h8, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub
  have h1 := card_eq_card_conjClass_mul B z
  rw [h.card_B] at h1
  have h2 := Nat.mul_le_mul_right (Nat.card (B ⊓ centralizer ({z} : Set G) : Subgroup G)) hle
  rw [← h1] at h2
  have key : Nat.card (B ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ 2 ^ 9 := by omega
  rw [hB] at key
  exact key

theorem PtFull.card_A₁A₂ : Nat.card (𝒜₁ ⊔ 𝒜₂ : Subgroup G) = 2 ^ 8 := by
  have h1 := natCard_sup_mul_inf (h.le_normalizer_A₁ h.A₂N₁)
  rw [inf_comm, card_ptA_inf_radA he hb φ, card_pullSub_radA he φ, h.card_A₁, sup_comm] at h1
  omega

theorem PtFull.card_S₁_inf_S₂ :
    Nat.card ((D₁ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃)) ⊓ (D₂ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃)) : Subgroup G) =
      2 ^ 13 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) with hB
  set SH := zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃ with hSH
  set S₁ := D₁ ⊔ SH with hS₁
  set S₂ := D₂ ⊔ SH with hS₂
  have hA₁S : 𝒜₁ ≤ SH := (A₁_le_A₂U₃_of he).trans
    (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hA₂S : 𝒜₂ ≤ SH := le_sup_right.trans le_sup_left
  have hzS : z ∈ SH := mem_sup_left (mem_sup_left (mem_zpowers z))
  have hBS₁ : B ≤ S₁ := sup_le (zpowers_le.2 (mem_sup_left h.zD₁))
    (sup_le (h.P₁D₁.trans le_sup_left) (sup_le (hA₂S.trans le_sup_right)
      (h.K₀D₁.trans le_sup_left)))
  have hBS₂ : B ≤ S₂ := sup_le (zpowers_le.2 (mem_sup_left h.zD₂))
    (sup_le (sup_le (hA₁S.trans le_sup_right) (h.K₀D₂.trans le_sup_left))
      (h.P₂D₂.trans le_sup_left))
  have hle : SH ⊔ B ≤ S₁ ⊓ S₂ :=
    sup_le (le_inf le_sup_right le_sup_right) (le_inf hBS₁ hBS₂)
  have hSHB : SH ⊓ B = zpowers z ⊔ (𝒜₁ ⊔ 𝒜₂) := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf (sup_le (zpowers_le.2 hzS)
      (sup_le hA₁S hA₂S)) (sup_le le_sup_left (sup_le ((le_sup_left.trans le_sup_left).trans
        le_sup_right) ((le_sup_left.trans le_sup_right).trans le_sup_right)))) ?_).symm
    have hA₁A₂L : 𝒜₁ ⊔ 𝒜₂ ≤ L := sup_le (pullSub_le φ _) (pullSub_le φ _)
    rw [card_zpowers_sup_of_not_mem hz (fun hz' => by
        have h2 : z ∈ L ⊓ zpowers z := mem_inf.2 ⟨hA₁A₂L hz', mem_zpowers z⟩
        rw [h.hinf, mem_bot] at h2
        rw [h2, orderOf_one] at hz
        exact absurd hz (by norm_num))
      (fun x hx => by rw [← mul_comm_z hzC (hA₁A₂L hx), mul_inv_cancel_right]; exact hx),
      h.card_A₁A₂]
    have h3 : Nat.card (B ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ 2 ^ 9 := by
      rw [hB]
      exact h.card_B_inf_H_le
    have h4 : SH ⊓ B ≤ B ⊓ centralizer ({z} : Set G) :=
      le_inf inf_le_right (inf_le_left.trans h.S_H_le_H)
    have h5 := Subgroup.card_le_of_le h4
    exact le_trans h5 (le_trans h3 (by norm_num))
  have hSN : SH ≤ normalizer (B : Set G) := fun x hx => mem_normalizer_of_conj_mem fun y hy =>
    h.conj_B_mem (mem_inf.1 (h.S_H_le hx)).1 (mem_inf.1 (h.S_H_le hx)).2 hy
  have h1 := natCard_sup_mul_inf hSN
  rw [hSHB, card_zpowers_sup_of_not_mem hz (fun hz' => by
        have hA₁A₂L : 𝒜₁ ⊔ 𝒜₂ ≤ L := sup_le (pullSub_le φ _) (pullSub_le φ _)
        have h2 : z ∈ L ⊓ zpowers z := mem_inf.2 ⟨hA₁A₂L hz', mem_zpowers z⟩
        rw [h.hinf, mem_bot] at h2
        rw [h2, orderOf_one] at hz
        exact absurd hz (by norm_num))
      (fun x hx => by
        rw [← mul_comm_z hzC ((sup_le (pullSub_le φ _) (pullSub_le φ _) :
          𝒜₁ ⊔ 𝒜₂ ≤ L) hx), mul_inv_cancel_right]
        exact hx),
    h.card_A₁A₂, h.card_S_H, h.card_B] at h1
  have hlow : 2 ^ 13 ≤ Nat.card (S₁ ⊓ S₂ : Subgroup G) := by
    have := Subgroup.card_le_of_le hle
    omega
  have hS₁₂N : S₁ ⊓ S₂ ≤ 𝒩₁ ⊓ 𝒩₂ := le_inf
    (inf_le_left.trans (sup_le h.hD₁N fun x hx => (mem_inf.1 (h.S_H_le hx)).1))
    (inf_le_right.trans (sup_le h.hD₂N fun x hx => (mem_inf.1 (h.S_H_le hx)).2))
  have hp : IsPGroup 2 (S₁ ⊓ S₂ : Subgroup G) :=
    (IsPGroup.of_card (n := 15) h.card_S₁).to_le inf_le_left
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le hS₁₂N
  rw [hk, h.hN₁₂] at hdvd
  have hdvd' : 2 ^ k ∣ 2 ^ 13 := by
    have hcop : Nat.Coprime (2 ^ k) 3 :=
      Nat.Coprime.pow_left k (by norm_num)
    exact hcop.dvd_of_dvd_mul_right (by simpa [show (24576 : ℕ) = 2 ^ 13 * 3 by norm_num]
      using hdvd)
  have hk13 : k ≤ 13 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd'
  have hup : Nat.card (S₁ ⊓ S₂ : Subgroup G) ≤ 2 ^ 13 := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk13
  omega

theorem PtFull.P₁_eq : 𝒜₁ ⊔ (C₁ ⊓ C₂) = C₁ ⊓ (D₂ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃)) := by
  have hA₁S : 𝒜₁ ≤ zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃ := (A₁_le_A₂U₃_of he).trans
    (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  refine le_antisymm (le_inf h.P₁C₁ (sup_le (hA₁S.trans le_sup_right)
    (h.K₀D₂.trans le_sup_left))) (fun x hx => ?_)
  obtain ⟨hxC, hxS⟩ := mem_inf.1 hx
  have hxN : x ∈ C₁ ⊓ 𝒩₂ := mem_inf.2 ⟨hxC, (sup_le h.hD₂N fun y hy =>
    (mem_inf.1 (h.S_H_le hy)).2 : D₂ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) ≤ 𝒩₂) hxS⟩
  have hxB := h.C₁_inf_N₂_le hxN
  have hxU : x ∈ zpowers z ⊔ (𝒜₁ ⊔ (C₁ ⊓ C₂)) := by
    rw [← h.U₁_eq]
    exact mem_inf.2 ⟨hxB, h.hC₁D hxC⟩
  exact mem_of_mem_zpowers_sup hz h.P₁C₁ h.z_not_mem_C₁ (fun y hy => conj_mem_sup
    (fun a ha => h.hA₁n z z_mem_N₁ a ha) (fun k hk => h.conj_K₀_mem z_mem_N₁ z_mem_N₂ hk) hy)
    hxU hxC

theorem PtFull.P₂_eq : 𝒜₂ ⊔ (C₁ ⊓ C₂) = C₂ ⊓ (D₁ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃)) := by
  refine le_antisymm (le_inf h.P₂C₂ (sup_le ((le_sup_right.trans le_sup_left).trans le_sup_right)
    (h.K₀D₁.trans le_sup_left))) (fun x hx => ?_)
  obtain ⟨hxC, hxS⟩ := mem_inf.1 hx
  have hxN : x ∈ C₂ ⊓ 𝒩₁ := mem_inf.2 ⟨hxC, (sup_le h.hD₁N fun y hy =>
    (mem_inf.1 (h.S_H_le hy)).1 : D₁ ⊔ (zpowers z ⊔ 𝒜₂ ⊔ 𝒰₃) ≤ 𝒩₁) hxS⟩
  have hxB := h.C₂_inf_N₁_le hxN
  have hxU : x ∈ zpowers z ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)) := by
    rw [← h.U₂_eq]
    exact mem_inf.2 ⟨hxB, h.C₂D₂ hxC⟩
  exact mem_of_mem_zpowers_sup hz h.P₂C₂ h.z_not_mem_C₂ (fun y hy => conj_mem_sup
    (fun a ha => h.conj_A₂_mem z_mem_N₂ ha) (fun k hk => h.conj_K₀_mem z_mem_N₁ z_mem_N₂ hk) hy)
    hxU hxC

end Orders

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
