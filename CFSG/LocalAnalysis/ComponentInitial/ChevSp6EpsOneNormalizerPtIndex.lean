module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtSylow
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtN
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtF1
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NoncentralPoint
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixMaximalElementaryRadicals

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

theorem card_mul_card_inf_of_mul_eq [Finite X] {H K N : Subgroup X} (hHN : H ≤ N) (hKN : K ≤ N)
    (hmul : ∀ n ∈ N, ∃ h ∈ H, h⁻¹ * n ∈ K) :
    Nat.card N * Nat.card (H ⊓ K : Subgroup X) = Nat.card H * Nat.card K := by
  classical
  let x₀ : X ⧸ K := ((1 : X) : X ⧸ K)
  have hstab : ∀ S : Subgroup X, MulAction.stabilizer S x₀ = K.subgroupOf S := by
    intro S
    ext s
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, Subgroup.smul_def]
    change ((s : X) • ((1 : X) : X ⧸ K)) = ((1 : X) : X ⧸ K) ↔ _
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
  have horb : MulAction.orbit N x₀ = MulAction.orbit H x₀ := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      obtain ⟨h, hh, hk⟩ := hmul n n.2
      refine ⟨⟨h, hh⟩, ?_⟩
      change ((h : X) • ((1 : X) : X ⧸ K)) = ((n : X) • ((1 : X) : X ⧸ K))
      rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul,
        mul_one, mul_one, QuotientGroup.eq]
      exact hk
    · rintro ⟨h, rfl⟩
      exact ⟨⟨h, hHN h.2⟩, rfl⟩
  have hN := MulAction.index_stabilizer N x₀
  have hH := MulAction.index_stabilizer H x₀
  rw [hstab, horb] at hN
  rw [hstab] at hH
  have hHK : Nat.card (K.subgroupOf H) = Nat.card (H ⊓ K : Subgroup X) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, (mem_inf.1 y.2).1⟩, (mem_inf.1 y.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h1 := Subgroup.card_mul_index (K.subgroupOf N)
  have h2 := Subgroup.card_mul_index (K.subgroupOf H)
  rw [Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv, hN] at h1
  rw [hHK, hH] at h2
  rw [← h1, ← h2]
  ring

end Generic

theorem eq_of_isElementaryAbelian_of_le {G : Type} [Group G] {L : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V} (hb : b.IsAlt)
    (hnd : b.Nondegenerate) (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    {Q Y₁ Y₂ : Subgroup G} (hQL : Q ≤ L) (hQ : IsPGroup 2 Q) (h₁ : Y₁ ≤ Q) (h₂ : Y₂ ≤ Q)
    (hY₁ : IsElementaryAbelian 2 Y₁) (hY₂ : IsElementaryAbelian 2 Y₂) (hc₁ : Nat.card Y₁ = 64)
    (hc₂ : Nat.card Y₂ = 64) : Y₁ = Y₂ := by
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hcard : ∀ Y : Subgroup G, Y ≤ L →
      Nat.card ((Y.subgroupOf L).map φ.toMonoidHom) = Nat.card Y := fun Y hY => by
    rw [card_map_of_injective hinj, Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv]
  have helem : ∀ Y : Subgroup G, IsElementaryAbelian 2 Y →
      IsElementaryAbelian 2 ((Y.subgroupOf L).map φ.toMonoidHom) := by
    intro Y hY
    refine isElementaryAbelian_of_forall ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (mul_comm_of_isElementaryAbelian hY (mem_subgroupOf.1 hx)
        (mem_subgroupOf.1 hy)))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul]
      have hxx : x * x = 1 :=
        Subtype.ext (mul_self_of_isElementaryAbelian hY (mem_subgroupOf.1 hx))
      rw [hxx, map_one]
  have hle : ∀ Y : Subgroup G, Y ≤ Q →
      (Y.subgroupOf L).map φ.toMonoidHom ≤ (Q.subgroupOf L).map φ.toMonoidHom := fun Y hY =>
    map_mono fun x hx => mem_subgroupOf.2 (hY (mem_subgroupOf.1 hx))
  have hQ' : IsPGroup 2 ((Q.subgroupOf L).map φ.toMonoidHom) :=
    (hQ.of_equiv (subgroupOfEquivOfLe hQL).symm).map _
  obtain ⟨P, hP⟩ := hQ'.exists_le_sylow
  obtain ⟨E, -, huniq⟩ := existsUnique_elementary_le_sylow hb hnd hV P
  have e₁ := huniq _ ⟨(hle Y₁ h₁).trans hP, helem Y₁ hY₁, by rw [hcard Y₁ (h₁.trans hQL), hc₁]⟩
  have e₂ := huniq _ ⟨(hle Y₂ h₂).trans hP, helem Y₂ hY₂, by rw [hcard Y₂ (h₂.trans hQL), hc₂]⟩
  have h3 : Y₁.subgroupOf L = Y₂.subgroupOf L := map_injective hinj (e₁.trans e₂.symm)
  rw [subgroupOf_inj, inf_of_le_left (h₁.trans hQL), inf_of_le_left (h₂.trans hQL)] at h3
  exact h3

theorem zmod_two_mul_self : ∀ a : ZMod 2, a * a = a := by
  decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} {he : IsSymplecticBasis b e} {hb : b.IsAlt}
variable {G : Type} [Group G] {L : Subgroup G} {φ : L ≃* bilinIsometryGroup b} {z : G}
  {hzC : z ∈ centralizer (L : Set G)} {hz : orderOf z = 2}
variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}
variable {D₁ C₁ F₁ : Subgroup G} {ν₁ : G → pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2}

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)
local notation "𝐛₁" => ptB₁ he hb φ hzC hz
local notation "𝒫₁" => 𝒜₁ ⊔ (C₁ ⊓ C₂)
local notation "𝒫₂" => 𝒜₂ ⊔ (C₁ ⊓ C₂)
local notation "𝔄" => (𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))
local notation "𝔅" => zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)))
local notation "𝔑" => normalizer ((zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) :
  Subgroup G) : Set G) ⊓ centralizer ({ptB₁ he hb φ hzC hz} : Set G)
local notation "𝒮_H" => zpowers z ⊔ 𝒜₂ ⊔ Subgroup.map (leviHom φ he) (unitriangularGL 3 (ZMod 2))
local notation "𝒴₀" => (𝒩₁ ⊓ 𝒩₂) ⊓ centralizer (Singleton.singleton z : Set G)

theorem conj_mem_L_of_mem_H (hzC' : z ∈ centralizer (L : Set G))
    (hsup : L ⊔ zpowers z = centralizer ({z} : Set G)) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) {a : G} (ha : a ∈ L) : x * a * x⁻¹ ∈ L := by
  rw [← hsup] at hx
  obtain ⟨l, hl, t, ht, rfl⟩ := (mem_sup_of_le_centralizer (zpowers_le_centralizer hzC')).1 hx
  have hta : a * t = t * a := mem_centralizer_iff.1 (zpowers_le_centralizer hzC' ht) a ha
  have e1 : l * t * a * (l * t)⁻¹ = l * a * l⁻¹ := by
    calc l * t * a * (l * t)⁻¹ = l * (t * a) * t⁻¹ * l⁻¹ := by group
      _ = l * (a * t) * t⁻¹ * l⁻¹ := by rw [hta]
      _ = l * a * l⁻¹ := by group
  rw [e1]
  exact mul_mem (mul_mem hl ha) (inv_mem hl)

section Index

variable [Finite G] (h : PtFull he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
include h

theorem PtFull.card_zA₁A₂ : Nat.card (zpowers z ⊔ (𝒜₁ ⊔ 𝒜₂) : Subgroup G) = 2 ^ 9 := by
  have hA₁A₂L : 𝒜₁ ⊔ 𝒜₂ ≤ L := sup_le (pullSub_le φ _) (pullSub_le φ _)
  rw [card_zpowers_sup_of_not_mem hz (fun hz' => by
      have h2 : z ∈ L ⊓ zpowers z := mem_inf.2 ⟨hA₁A₂L hz', mem_zpowers z⟩
      rw [h.hinf, mem_bot] at h2
      rw [h2, orderOf_one] at hz
      exact absurd hz (by norm_num))
    (fun x hx => by rw [← mul_comm_z hzC (hA₁A₂L hx), mul_inv_cancel_right]; exact hx),
    h.card_A₁A₂]
  norm_num

theorem PtFull.B_inf_H : 𝔅 ⊓ centralizer ({z} : Set G) = zpowers z ⊔ (𝒜₁ ⊔ 𝒜₂) := by
  have hle : zpowers z ⊔ (𝒜₁ ⊔ 𝒜₂) ≤ 𝔅 ⊓ centralizer ({z} : Set G) := by
    refine le_inf (sup_le le_sup_left (sup_le ((le_sup_left.trans le_sup_left).trans le_sup_right)
      ((le_sup_left.trans le_sup_right).trans le_sup_right))) ?_
    rw [← h.hsup]
    exact sup_le le_sup_right (sup_le (le_sup_left.trans' (pullSub_le φ _))
      (le_sup_left.trans' (pullSub_le φ _)))
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_zA₁A₂]; exact h.card_B_inf_H_le)).symm

theorem PtFull.B_inf_L_le : 𝔅 ⊓ L ≤ 𝒜₁ ⊔ 𝒜₂ := by
  intro x hx
  obtain ⟨hxB, hxL⟩ := mem_inf.1 hx
  have hxH : x ∈ centralizer ({z} : Set G) := by
    rw [← h.hsup]
    exact mem_sup_left hxL
  have h1 : x ∈ zpowers z ⊔ (𝒜₁ ⊔ 𝒜₂) := by
    rw [← h.B_inf_H]
    exact mem_inf.2 ⟨hxB, hxH⟩
  rw [sup_comm] at h1
  exact mem_of_mem_sup_zpowers (hzC := hzC) (sup_le (pullSub_le φ _) (pullSub_le φ _)) h.hinf h1
    hxL

theorem PtFull.map_conj_A₂ {x : G} (hxB : x ∈ normalizer ((𝔅 : Subgroup G) : Set G))
    (hxH : x ∈ centralizer ({z} : Set G)) :
    (𝒜₂).map (MulAut.conj x).toMonoidHom = 𝒜₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA₂B : 𝒜₂ ≤ 𝔅 := (le_sup_left.trans le_sup_right).trans le_sup_right
  have hA₂c : Nat.card (𝒜₂ : Subgroup G) = 64 := card_pullSub_radA he φ
  have hA₂e : IsElementaryAbelian 2 (𝒜₂ : Subgroup G) := isElementaryAbelian_of_forall
    (fun a ha a' ha' => congrArg Subtype.val
      (h.hE₂c.is_comm.comm ⟨a, h.hA₂E₂ ha⟩ ⟨a', h.hA₂E₂ ha'⟩))
    (fun a ha => (sq a).symm.trans (h.hE₂sq a (h.hA₂E₂ ha)))
  refine eq_of_isElementaryAbelian_of_le hb h.hnd h.hV φ (sup_le (pullSub_le φ _)
    (pullSub_le φ _)) (IsPGroup.of_card h.card_A₁A₂) ?_ le_sup_right ?_ hA₂e ?_ hA₂c
  · rintro _ ⟨a, ha, rfl⟩
    change x * a * x⁻¹ ∈ 𝒜₁ ⊔ 𝒜₂
    refine h.B_inf_L_le (mem_inf.2 ⟨(mem_normalizer_iff.1 hxB a).1 (hA₂B ha), ?_⟩)
    exact conj_mem_L_of_mem_H hzC h.hsup hxH (pullSub_le φ _ ha)
  · refine isElementaryAbelian_of_forall ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
      rw [← map_mul, ← map_mul, mul_comm_of_isElementaryAbelian hA₂e ha ha']
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, mul_self_of_isElementaryAbelian hA₂e ha, map_one]
  · rw [card_map_of_injective (MulAut.conj x).injective, hA₂c]

theorem PtFull.mem_N₂_of_normalizer_B {x : G} (hxB : x ∈ normalizer ((𝔅 : Subgroup G) : Set G))
    (hxH : x ∈ centralizer ({z} : Set G)) : x ∈ 𝒩₂ := by
  have hA := h.map_conj_A₂ hxB hxH
  have hxz : Commute x z := mem_centralizer_singleton_iff.1 hxH
  refine mem_normalizer_of_conj_mem fun r hr => ?_
  refine conj_mem_sup (P := 𝒜₂) (Q := zpowers z) (fun a ha => ?_) (fun t ht => ?_) hr
  · rw [← hA]
    exact ⟨a, ha, rfl⟩
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
    rw [(hxz.zpow_right k).eq, mul_inv_cancel_right]
    exact ht

omit [Finite G] in
theorem PtFull.mem_N₁_of_commute {x : G} (hx₂ : x ∈ 𝒩₂) (hxH : x ∈ centralizer ({z} : Set G))
    (hxb : x * 𝐛₁ = 𝐛₁ * x) : x ∈ 𝒩₁ := by
  let n : ↥(𝒩₂ ⊓ centralizer ({z} : Set G)) := ⟨x, mem_inf.2 ⟨hx₂, hxH⟩⟩
  have h1 := conj_tauHom_of_sigma φ he σ h.hσ n symE₁₁
  have h2 : x * 𝐛₁ * x⁻¹ = 𝐛₁ := by rw [hxb, mul_inv_cancel_right]
  rw [← ptB₁_eq_tauHom he hb φ hzC hz] at h1
  change x * 𝐛₁ * x⁻¹ = _ at h1
  rw [h2, ptB₁_eq_tauHom he hb φ hzC hz] at h1
  have h3 := congrArg (fun B : binarySymMatrices 3 => (B : M₃))
    (Multiplicative.ofAdd.injective (tauHom_injective φ he h1))
  have e00 := congrFun (congrFun h3 0) 0
  have e11 := congrFun (congrFun h3 1) 1
  have e22 := congrFun (congrFun h3 2) 2
  simp [symThreeCongr, Matrix.mul_apply, Fin.sum_univ_three, jMat, zmod_two_mul_self] at e00 e11 e22
  refine (mem_normalizer_ptSub_iff_sigma he hb h.hnd φ hzC h.hsup h.hinf hz σ h.hσcol h.hσker
    n).2 ?_
  rw [mem_vecStabGL]
  exact ⟨e00.symm, e11.symm, e22.symm⟩

theorem PtFull.N_inf_H : 𝔑 ⊓ centralizer ({z} : Set G) = 𝒴₀ := by
  refine le_antisymm (fun x hx => ?_) (fun y hy => ?_)
  · obtain ⟨hxN, hxH⟩ := mem_inf.1 hx
    obtain ⟨hxB, hxb⟩ := mem_inf.1 hxN
    have hx₂ := h.mem_N₂_of_normalizer_B hxB hxH
    exact mem_inf.2 ⟨mem_inf.2 ⟨h.mem_N₁_of_commute hx₂ hxH (mem_centralizer_singleton_iff.1 hxb),
      hx₂⟩, hxH⟩
  · obtain ⟨hy₁₂, hyH⟩ := mem_inf.1 hy
    obtain ⟨hy₁, hy₂⟩ := mem_inf.1 hy₁₂
    exact mem_inf.2 ⟨mem_inf.2 ⟨mem_normalizer_of_conj_mem fun w hw => h.conj_B_mem hy₁ hy₂ hw,
      mem_centralizer_singleton_iff.2 (h.hb₁c y hy₁)⟩, hyH⟩

theorem PtFull.D₁_le_N : D₁ ≤ 𝔑 := le_sup_left.trans h.S₁_le_N

theorem PtFull.D₂_le_N : D₂ ≤ 𝔑 := le_sup_left.trans h.S₂_le_N

omit [Finite G] in
theorem PtFull.B_le_N : 𝔅 ≤ 𝔑 := fun x hx => mem_inf.2 ⟨le_normalizer hx,
  mem_centralizer_singleton_iff.2 (h.hb₁c x (mem_inf.1 (h.B_le hx)).1)⟩

theorem PtFull.N_inf_N₁ : 𝔑 ⊓ 𝒩₁ = D₁ ⊔ 𝒴₀ := by
  refine le_antisymm (fun x hx => ?_) (sup_le (le_inf h.D₁_le_N h.hD₁N)
    (le_inf (fun y hy => (mem_inf.1 ((h.N_inf_H).ge hy)).1) (inf_le_left.trans inf_le_left)))
  obtain ⟨hxN, hx₁⟩ := mem_inf.1 hx
  obtain ⟨d, hd, c, hc, rfl⟩ := h.hprod₁ x hx₁
  have hcN : c ∈ 𝔑 := by
    have h1 := mul_mem (inv_mem (h.D₁_le_N hd)) hxN
    rwa [inv_mul_cancel_left] at h1
  have hcY : c ∈ 𝔑 ⊓ centralizer ({z} : Set G) := mem_inf.2 ⟨hcN, (mem_inf.1 hc).2⟩
  rw [h.N_inf_H] at hcY
  exact mul_mem (mem_sup_left hd) (mem_sup_right hcY)

theorem PtFull.N_inf_N₂ : 𝔑 ⊓ 𝒩₂ = D₂ ⊔ 𝒴₀ := by
  refine le_antisymm (fun x hx => ?_) (sup_le (le_inf h.D₂_le_N h.hD₂N)
    (le_inf (fun y hy => (mem_inf.1 ((h.N_inf_H).ge hy)).1) (inf_le_left.trans inf_le_right)))
  obtain ⟨hxN, hx₂⟩ := mem_inf.1 hx
  obtain ⟨d, hd, c, hc, rfl⟩ := h.hprod₂ x hx₂
  have hcN : c ∈ 𝔑 := by
    have h1 := mul_mem (inv_mem (h.D₂_le_N hd)) hxN
    rwa [inv_mul_cancel_left] at h1
  have hcY : c ∈ 𝔑 ⊓ centralizer ({z} : Set G) := mem_inf.2 ⟨hcN, (mem_inf.1 hc).2⟩
  rw [h.N_inf_H] at hcY
  exact mul_mem (mem_sup_left hd) (mem_sup_right hcY)

omit [Finite G] in
theorem PtFull.card_Y₀ : Nat.card (𝒴₀ : Subgroup G) = 3072 :=
  card_normalizer_inf_centralizer he hb h.hnd φ hzC h.hsup h.hinf hz σ h.hσcol h.hσker h.hσsurj

theorem PtFull.card_N_inf_N₁ : Nat.card (𝔑 ⊓ 𝒩₁ : Subgroup G) = 3 * 2 ^ 15 := by
  rw [h.N_inf_N₁]
  have hle : (𝒴₀ : Subgroup G) ≤ normalizer (D₁ : Set G) := fun y hy =>
    mem_normalizer_of_conj_mem fun d hd => h.hD₁n y (mem_inf.1 (mem_inf.1 hy).1).1 d hd
  have h1 := natCard_sup_mul_inf hle
  have hinf' : (𝒴₀ : Subgroup G) ⊓ D₁ = ℬ₁ := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_inf (le_inf le_normalizer
      (ptSub_le_normalizer_radSub he hb φ hzC hz)) (ptSub_le_centralizer he hb h.hnd φ h.hsup))
      (h.hBF₁.trans h.hFD₁))
    rw [← h.hD₁H]
    exact mem_inf.2 ⟨(mem_inf.1 hx).2, (mem_inf.1 (mem_inf.1 hx).1).2⟩
  rw [hinf', (ptSub_facts he hb h.hnd φ hzC h.hinf hz).2.2.1, h.card_Y₀, h.hD₁card,
    sup_comm] at h1
  omega

theorem PtFull.card_N_inf_N₂ : Nat.card (𝔑 ⊓ 𝒩₂ : Subgroup G) = 3 * 2 ^ 16 := by
  rw [h.N_inf_N₂]
  have hle : (𝒴₀ : Subgroup G) ≤ normalizer (D₂ : Set G) := fun y hy =>
    mem_normalizer_of_conj_mem fun d hd => h.hD₂n y (mem_inf.1 (mem_inf.1 hy).1).2 d hd
  have h1 := natCard_sup_mul_inf hle
  have hinf' : (𝒴₀ : Subgroup G) ⊓ D₂ = ℛ := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_inf (le_inf
      (radSub_le_normalizer_ptSub he hb h.hnd φ hzC) le_normalizer)
      (radSub_le_centralizer φ h.hsup)) h.hRD₂)
    rw [← h.hD₂H]
    exact mem_inf.2 ⟨(mem_inf.1 hx).2, (mem_inf.1 (mem_inf.1 hx).1).2⟩
  rw [hinf', card_radSub he φ hzC h.hinf hz, h.card_Y₀, h.hD₂card, sup_comm] at h1
  omega

theorem PtFull.N_inf_N₁_le : 𝔑 ⊓ 𝒩₁ ≤ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨hxN, hx₁⟩ := mem_inf.1 hx
  exact mem_inf.2 ⟨hxN, mem_normalizer_of_conj_mem fun y hy => mem_inf.2
    ⟨(mem_normalizer_iff.1 (mem_inf.1 hxN).1 y).1 (mem_inf.1 hy).1,
      h.hD₁n x hx₁ y (mem_inf.1 hy).2⟩⟩

theorem PtFull.N_inf_N₂_le : 𝔑 ⊓ 𝒩₂ ≤ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨hxN, hx₂⟩ := mem_inf.1 hx
  exact mem_inf.2 ⟨hxN, mem_normalizer_of_conj_mem fun y hy => mem_inf.2
    ⟨(mem_normalizer_iff.1 (mem_inf.1 hxN).1 y).1 (mem_inf.1 hy).1,
      h.hD₂n x hx₂ y (mem_inf.1 hy).2⟩⟩

theorem PtFull.z_not_mem_A : z ∉ 𝔄 := by
  intro hzA
  have h1 := h.card_B
  rw [sup_eq_right.2 (zpowers_le.2 hzA), h.card_A] at h1
  norm_num at h1

theorem PtFull.conj_mem_A {m : G} (hm : m ∈ 𝔑) {a : G} (ha : a ∈ 𝔄) : m * a * m⁻¹ ∈ 𝔄 :=
  conj_mem_sup (fun _ hp => h.conj_mem_P₁ hm hp) (fun _ hp => h.conj_mem_P₂ hm hp) ha

theorem PtFull.conj_z_mem_A {m : G} (hm : m ∈ 𝔑) : z⁻¹ * (m * z * m⁻¹) ∈ 𝔄 := by
  have hzN : zpowers z ≤ normalizer ((𝔄 : Subgroup G) : Set G) := zpowers_le.2
    (mem_normalizer_of_conj_mem fun a ha => h.conj_mem_A (h.B_le_N (mem_sup_left
      (mem_zpowers z))) ha)
  have hw : m * z * m⁻¹ ∈ 𝔅 :=
    (mem_normalizer_iff.1 (mem_inf.1 hm).1 z).1 (mem_sup_left (mem_zpowers z))
  have hw' : m * z * m⁻¹ ∈ ((zpowers z ⊔ 𝔄 : Subgroup G) : Set G) := hw
  rw [coe_mul_of_left_le_normalizer_right _ _ hzN] at hw'
  obtain ⟨t, ht, a, ha, hta⟩ := hw'
  beta_reduce at hta
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
  have hk : z ^ k = z ^ (k % 2) := by
    rw [← zpow_mod_orderOf z k, hz]
    norm_num
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    rw [hk, h0, zpow_zero, one_mul] at hta
    have h2 := h.conj_mem_A (inv_mem hm) (hta ▸ ha : m * z * m⁻¹ ∈ 𝔄)
    rw [show m⁻¹ * (m * z * m⁻¹) * m⁻¹⁻¹ = z by group] at h2
    exact h.z_not_mem_A h2
  · rw [hk, h1, zpow_one] at hta
    rw [← hta, inv_mul_cancel_left]
    exact ha

omit [Finite G] in
theorem PtFull.exists_D₁_conj {a : G} (ha : a ∈ 𝒜₁) : ∃ d ∈ D₁, d * z * d⁻¹ = z * a := by
  have h1 : z * a ∈ conjClass 𝒩₁ z := by
    rw [h.hfull₁]
    exact ⟨a, ha, rfl⟩
  obtain ⟨m, hm, hmz⟩ := h1
  obtain ⟨d, hd, c, hc, rfl⟩ := h.hprod₁ m hm
  refine ⟨d, hd, ?_⟩
  have hcz : c * z * c⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2, mul_inv_cancel_right]
  rw [← hmz, show d * c * z * (d * c)⁻¹ = d * (c * z * c⁻¹) * d⁻¹ by group, hcz]

omit [Finite G] in
theorem PtFull.exists_D₂_conj {a : G} (ha : a ∈ 𝒜₂) : ∃ d ∈ D₂, d * z * d⁻¹ = z * a := by
  have h1 : z * a ∈ conjClass 𝒩₂ z := by
    rw [h.hfull]
    exact ⟨a, ha, rfl⟩
  obtain ⟨m, hm, hmz⟩ := h1
  obtain ⟨d, hd, c, hc, rfl⟩ := h.hprod₂ m hm
  refine ⟨d, hd, ?_⟩
  have hcz : c * z * c⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2, mul_inv_cancel_right]
  rw [← hmz, show d * c * z * (d * c)⁻¹ = d * (c * z * c⁻¹) * d⁻¹ by group, hcz]

omit [Finite G] h in
theorem A_eq' : (𝔄 : Subgroup G) = 𝒜₂ ⊔ 𝒫₁ :=
  le_antisymm (sup_le le_sup_right (sup_le le_sup_left (le_sup_right.trans le_sup_right)))
    (sup_le (le_sup_left.trans le_sup_right) le_sup_left)

omit [Finite G] h in
theorem mem_normalizer_zP [Finite G] {P : Subgroup G} (hPn : ∀ m ∈ 𝔑, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    {k : G} (hk : k ∈ 𝔑) {p : G} (hp : p ∈ P) (hkz : k * z * k⁻¹ = z * p) :
    k ∈ normalizer ((zpowers z ⊔ P : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun u hu => ?_
  have hle : (zpowers z ⊔ P).map (MulAut.conj k).toMonoidHom ≤ zpowers z ⊔ P := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [MonoidHom.map_zpowers, zpowers_le]
      change k * z * k⁻¹ ∈ zpowers z ⊔ P
      rw [hkz]
      exact mul_mem (mem_sup_left (mem_zpowers z)) (mem_sup_right hp)
    · rintro _ ⟨q, hq, rfl⟩
      exact mem_sup_right (hPn k hk q hq)
  exact hle ⟨u, hu, rfl⟩

theorem PtFull.exists_mem_K₂ {n : G} (hn : n ∈ 𝔑) :
    ∃ d ∈ D₁, d⁻¹ * n ∈ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) := by
  have hw := h.conj_z_mem_A hn
  have hA₁B : 𝒜₁ ≤ 𝔅 := (le_sup_left.trans le_sup_left).trans le_sup_right
  have hA₁P₂ : 𝒜₁ ≤ normalizer ((𝒫₂ : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_of_conj_mem fun p hp => h.conj_mem_P₂ (h.B_le_N (hA₁B ha)) hp
  have hw' : z⁻¹ * (n * z * n⁻¹) ∈ ((𝒜₁ ⊔ 𝒫₂ : Subgroup G) : Set G) := by
    rw [← A_eq]
    exact hw
  rw [coe_mul_of_left_le_normalizer_right _ _ hA₁P₂] at hw'
  obtain ⟨a, ha, p, hp, hap⟩ := hw'
  beta_reduce at hap
  obtain ⟨d, hd, hdz⟩ := h.exists_D₁_conj ha
  have hdN := h.D₁_le_N hd
  have hkN : d⁻¹ * n ∈ 𝔑 := mul_mem (inv_mem hdN) hn
  refine ⟨d, hd, mem_inf.2 ⟨hkN, ?_⟩⟩
  rw [h.U₂_eq]
  have hnz : n * z * n⁻¹ = z * (a * p) := by
    rw [hap]
    group
  have hp' : d⁻¹ * p * d ∈ 𝒫₂ := by
    have h1 := h.conj_mem_P₂ (inv_mem hdN) hp
    rwa [inv_inv] at h1
  refine mem_normalizer_zP (fun m hm q hq => h.conj_mem_P₂ hm hq) hkN hp' ?_
  calc d⁻¹ * n * z * (d⁻¹ * n)⁻¹ = d⁻¹ * (n * z * n⁻¹) * d := by group
    _ = d⁻¹ * (z * a) * d * (d⁻¹ * p * d) := by rw [hnz]; group
    _ = d⁻¹ * (d * z * d⁻¹) * d * (d⁻¹ * p * d) := by rw [hdz]
    _ = z * (d⁻¹ * p * d) := by group

theorem PtFull.exists_mem_K₁ {n : G} (hn : n ∈ 𝔑) :
    ∃ d ∈ D₂, d⁻¹ * n ∈ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) := by
  have hw := h.conj_z_mem_A hn
  have hA₂B : 𝒜₂ ≤ 𝔅 := (le_sup_left.trans le_sup_right).trans le_sup_right
  have hA₂P₁ : 𝒜₂ ≤ normalizer ((𝒫₁ : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_of_conj_mem fun p hp => h.conj_mem_P₁ (h.B_le_N (hA₂B ha)) hp
  have hw' : z⁻¹ * (n * z * n⁻¹) ∈ ((𝒜₂ ⊔ 𝒫₁ : Subgroup G) : Set G) := by
    rw [← A_eq']
    exact hw
  rw [coe_mul_of_left_le_normalizer_right _ _ hA₂P₁] at hw'
  obtain ⟨a, ha, p, hp, hap⟩ := hw'
  beta_reduce at hap
  obtain ⟨d, hd, hdz⟩ := h.exists_D₂_conj ha
  have hdN := h.D₂_le_N hd
  have hkN : d⁻¹ * n ∈ 𝔑 := mul_mem (inv_mem hdN) hn
  refine ⟨d, hd, mem_inf.2 ⟨hkN, ?_⟩⟩
  rw [h.U₁_eq]
  have hnz : n * z * n⁻¹ = z * (a * p) := by
    rw [hap]
    group
  have hp' : d⁻¹ * p * d ∈ 𝒫₁ := by
    have h1 := h.conj_mem_P₁ (inv_mem hdN) hp
    rwa [inv_inv] at h1
  refine mem_normalizer_zP (fun m hm q hq => h.conj_mem_P₁ hm hq) hkN hp' ?_
  calc d⁻¹ * n * z * (d⁻¹ * n)⁻¹ = d⁻¹ * (n * z * n⁻¹) * d := by group
    _ = d⁻¹ * (z * a) * d * (d⁻¹ * p * d) := by rw [hnz]; group
    _ = d⁻¹ * (d * z * d⁻¹) * d * (d⁻¹ * p * d) := by rw [hdz]
    _ = z * (d⁻¹ * p * d) := by group

theorem PtFull.card_D₁_inf_K₂ :
    Nat.card (D₁ ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G)) : Subgroup G) = 2 ^ 9 := by
  have hD₂K₂ : D₂ ≤ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) :=
    (le_inf h.D₂_le_N h.hD₂N).trans h.N_inf_N₂_le
  have hBK₂ : 𝔅 ≤ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) :=
    (le_inf h.B_le_N (h.B_le.trans inf_le_right)).trans h.N_inf_N₂_le
  have hB₁B : ℬ₁ ≤ 𝔅 := sup_le ((le_sup_left.trans le_sup_left).trans le_sup_right) le_sup_left
  have hcen : (D₁ ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G))) ⊓
      centralizer ({z} : Set G) = ℬ₁ := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_inf (h.hBF₁.trans h.hFD₁)
      (hB₁B.trans hBK₂)) (ptSub_le_centralizer he hb h.hnd φ h.hsup))
    rw [← h.hD₁H]
    exact mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).1, (mem_inf.1 hx).2⟩
  have hcls : conjClass (D₁ ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G))) z =
      z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      obtain ⟨hd₁, hdK⟩ := mem_inf.1 hd
      have h1 : z⁻¹ * (d * z * d⁻¹) ∈ 𝒜₁ := h.conj_z_mem (h.hD₁N hd₁)
      have hzU : z ∈ 𝔅 ⊓ D₂ := mem_inf.2 ⟨mem_sup_left (mem_zpowers z), h.zD₂⟩
      have h2 : d * z * d⁻¹ ∈ 𝔅 ⊓ D₂ := (mem_normalizer_iff.1 (mem_inf.1 hdK).2 z).1 hzU
      have h3 : z⁻¹ * (d * z * d⁻¹) ∈ D₂ := mul_mem (inv_mem h.zD₂) (mem_inf.1 h2).2
      have h4 : z⁻¹ * (d * z * d⁻¹) ∈ 𝒜₁ ⊓ 𝒜₂ := by
        rw [← h.A₁_inf_D₂]
        exact mem_inf.2 ⟨h1, h3⟩
      exact ⟨_, h4, by change z * (z⁻¹ * (d * z * d⁻¹)) = d * z * d⁻¹; group⟩
    · rw [← h.hK₀z]
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨k, mem_inf.2 ⟨h.hC₁D (mem_inf.1 hk).1, hD₂K₂ (mem_inf.1 hk).2⟩, rfl⟩
  have h1 := card_eq_card_conjClass_mul (D₁ ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G))) z
  rw [hcls, card_smul_set, SetLike.coe_sort_coe, card_ptA_inf_radA he hb φ, hcen,
    (ptSub_facts he hb h.hnd φ hzC h.hinf hz).2.2.1] at h1
  rw [h1]
  norm_num

theorem PtFull.card_D₂_inf_K₁ :
    Nat.card (D₂ ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) : Subgroup G) = 2 ^ 10 := by
  have hD₁K₁ : D₁ ≤ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) :=
    (le_inf h.D₁_le_N h.hD₁N).trans h.N_inf_N₁_le
  have hBK₁ : 𝔅 ≤ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) :=
    (le_inf h.B_le_N (h.B_le.trans inf_le_left)).trans h.N_inf_N₁_le
  have hRB : ℛ ≤ 𝔅 := sup_le ((le_sup_left.trans le_sup_right).trans le_sup_right) le_sup_left
  have hcen : (D₂ ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G))) ⊓
      centralizer ({z} : Set G) = ℛ := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_inf h.hRD₂ (hRB.trans hBK₁))
      (radSub_le_centralizer φ h.hsup))
    rw [← h.hD₂H]
    exact mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).1, (mem_inf.1 hx).2⟩
  have hcls : conjClass (D₂ ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G))) z =
      z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      obtain ⟨hd₂, hdK⟩ := mem_inf.1 hd
      have h1 : z⁻¹ * (d * z * d⁻¹) ∈ 𝒜₂ := by
        have h0 := h.toLagBase.tau_nu (inv_mem hd₂)
        rw [inv_inv] at h0
        rw [← h0]
        exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
      have hzU : z ∈ 𝔅 ⊓ D₁ := mem_inf.2 ⟨mem_sup_left (mem_zpowers z), h.zD₁⟩
      have h2 : d * z * d⁻¹ ∈ 𝔅 ⊓ D₁ := (mem_normalizer_iff.1 (mem_inf.1 hdK).2 z).1 hzU
      have h3 : z⁻¹ * (d * z * d⁻¹) ∈ D₁ := mul_mem (inv_mem h.zD₁) (mem_inf.1 h2).2
      have h4 : z⁻¹ * (d * z * d⁻¹) ∈ 𝒜₁ ⊓ 𝒜₂ := by
        rw [← h.A₂_inf_D₁]
        exact mem_inf.2 ⟨h1, h3⟩
      exact ⟨_, h4, by change z * (z⁻¹ * (d * z * d⁻¹)) = d * z * d⁻¹; group⟩
    · rw [← h.hK₀z]
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨k, mem_inf.2 ⟨(mem_inf.1 hk).2, hD₁K₁ (h.hC₁D (mem_inf.1 hk).1)⟩, rfl⟩
  have h1 := card_eq_card_conjClass_mul (D₂ ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G))) z
  rw [hcls, card_smul_set, SetLike.coe_sort_coe, card_ptA_inf_radA he hb φ, hcen,
    card_radSub he φ hzC h.hinf hz] at h1
  rw [h1]
  norm_num

theorem PtFull.card_N_eq_K₂ : Nat.card (𝔑 : Subgroup G) =
    4 * Nat.card (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) : Subgroup G) := by
  have h1 := card_mul_card_inf_of_mul_eq h.D₁_le_N inf_le_left (fun n hn => h.exists_mem_K₂ hn)
  rw [h.card_D₁_inf_K₂, h.hD₁card] at h1
  omega

theorem PtFull.card_N_eq_K₁ : Nat.card (𝔑 : Subgroup G) =
    8 * Nat.card (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) : Subgroup G) := by
  have h1 := card_mul_card_inf_of_mul_eq h.D₂_le_N inf_le_left (fun n hn => h.exists_mem_K₁ hn)
  rw [h.card_D₂_inf_K₁, h.hD₂card] at h1
  omega

theorem PtFull.S₂_le_K₂ :
    D₂ ⊔ 𝒮_H ≤ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) := by
  have hle : D₂ ⊔ 𝒮_H ≤ 𝒩₂ := sup_le h.hD₂N fun _ hy => (mem_inf.1 (h.S_H_le hy)).2
  exact (le_inf h.S₂_le_N hle).trans h.N_inf_N₂_le

theorem PtFull.S₁_le_K₁ :
    D₁ ⊔ 𝒮_H ≤ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) := by
  have hle : D₁ ⊔ 𝒮_H ≤ 𝒩₁ := sup_le h.hD₁N fun _ hy => (mem_inf.1 (h.S_H_le hy)).1
  exact (le_inf h.S₁_le_N hle).trans h.N_inf_N₁_le

theorem PtFull.S₁_inf_K₂ : (D₁ ⊔ 𝒮_H) ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G)) =
    (D₁ ⊔ 𝒮_H) ⊓ (D₂ ⊔ 𝒮_H) := by
  have hle : (D₁ ⊔ 𝒮_H) ⊓ (D₂ ⊔ 𝒮_H) ≤
      (D₁ ⊔ 𝒮_H) ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G)) :=
    inf_le_inf_left _ h.S₂_le_K₂
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [h.card_S₁_inf_S₂]
  have h1 := card_mul_card_inf_of_mul_eq h.S₁_le_N inf_le_left (fun n hn =>
    let ⟨d, hd, hk⟩ := h.exists_mem_K₂ hn; ⟨d, mem_sup_left hd, hk⟩)
  rw [h.card_S₁, h.card_N_eq_K₂] at h1
  have hpos : 0 < Nat.card (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) : Subgroup G) :=
    Nat.card_pos
  have h2 : Nat.card (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) : Subgroup G) *
      (4 * Nat.card ((D₁ ⊔ 𝒮_H) ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G)) :
        Subgroup G)) =
      Nat.card (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) : Subgroup G) * 2 ^ 15 := by
    linarith
  have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
  omega

theorem PtFull.S₂_inf_K₁ : (D₂ ⊔ 𝒮_H) ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) =
    (D₁ ⊔ 𝒮_H) ⊓ (D₂ ⊔ 𝒮_H) := by
  have hle : (D₁ ⊔ 𝒮_H) ⊓ (D₂ ⊔ 𝒮_H) ≤
      (D₂ ⊔ 𝒮_H) ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) := by
    rw [inf_comm]
    exact inf_le_inf_left _ h.S₁_le_K₁
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [h.card_S₁_inf_S₂]
  have h1 := card_mul_card_inf_of_mul_eq h.S₂_le_N inf_le_left (fun n hn =>
    let ⟨d, hd, hk⟩ := h.exists_mem_K₁ hn; ⟨d, mem_sup_left hd, hk⟩)
  rw [h.card_S₂, h.card_N_eq_K₁] at h1
  have hpos : 0 < Nat.card (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) : Subgroup G) :=
    Nat.card_pos
  have h2 : Nat.card (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) : Subgroup G) *
      (8 * Nat.card ((D₂ ⊔ 𝒮_H) ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) :
        Subgroup G)) =
      Nat.card (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) : Subgroup G) * 2 ^ 16 := by
    linarith
  have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
  omega

theorem PtFull.coe_N_eq_S₁K₂ : (𝔑 : Set G) = ((D₁ ⊔ 𝒮_H : Subgroup G) : Set G) *
    ((𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  ext n
  constructor
  · intro hn
    obtain ⟨d, hd, hk⟩ := h.exists_mem_K₂ hn
    exact ⟨d, mem_sup_left hd, d⁻¹ * n, hk, mul_inv_cancel_left d n⟩
  · rintro ⟨s, hs, k, hk, rfl⟩
    exact mul_mem (h.S₁_le_N hs) (mem_inf.1 hk).1

theorem PtFull.coe_N_eq_S₂K₁ : (𝔑 : Set G) = ((D₂ ⊔ 𝒮_H : Subgroup G) : Set G) *
    ((𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  ext n
  constructor
  · intro hn
    obtain ⟨d, hd, hk⟩ := h.exists_mem_K₁ hn
    exact ⟨d, mem_sup_left hd, d⁻¹ * n, hk, mul_inv_cancel_left d n⟩
  · rintro ⟨s, hs, k, hk, rfl⟩
    exact mul_mem (h.S₂_le_N hs) (mem_inf.1 hk).1

theorem PtFull.relIndex_K₁_eq :
    (𝔑 ⊓ 𝒩₁).relIndex (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) =
      (𝔑 ⊓ 𝒩₂).relIndex (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G)) := by
  have h1 := relIndex_mul_card_of_le h.N_inf_N₁_le
  have h2 := relIndex_mul_card_of_le h.N_inf_N₂_le
  rw [h.card_N_inf_N₁] at h1
  rw [h.card_N_inf_N₂] at h2
  have h3 := h.card_N_eq_K₁
  have h4 := h.card_N_eq_K₂
  omega

theorem PtFull.relIndex_K₁_le_two :
    (𝔑 ⊓ 𝒩₁).relIndex (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) ≤ 2 := by
  obtain ⟨hDF, -, -, hidx⟩ := h.normalizer_D₁
  have hK₁D : 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) ≤ normalizer (D₁ : Set G) := by
    rw [hDF]
    exact h.K₁_le_normalizer_F₁
  have h1 := relIndex_mul_card_of_le h.N_inf_N₁_le
  have h2 := Subgroup.relIndex_mul_card (H := 𝒩₁)
    (K := 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G))
  have h3 : 𝒩₁ ⊓ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) = 𝔑 ⊓ 𝒩₁ :=
    le_antisymm (le_inf (inf_le_right.trans inf_le_left) inf_le_left)
      (le_inf inf_le_right h.N_inf_N₁_le)
  rw [h3] at h2
  have hpos : 0 < Nat.card (𝔑 ⊓ 𝒩₁ : Subgroup G) := Nat.card_pos
  have h4 : (𝔑 ⊓ 𝒩₁).relIndex (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) =
      (𝒩₁).relIndex (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) :=
    Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  rw [h4]
  have hne : (𝒩₁).relIndex (normalizer (D₁ : Set G)) ≠ 0 := by
    intro h0
    have h5 := Subgroup.relIndex_mul_card (H := 𝒩₁) (K := normalizer (D₁ : Set G))
    rw [h0, zero_mul] at h5
    exact (Nat.card_pos (α := normalizer (D₁ : Set G))).ne' h5.symm
  exact (relIndex_le_of_le_right hK₁D hne).trans hidx

end Index

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
