module

public import CFSG.CGT.Foote81L6.DescentDihedral
public import CFSG.CGT.Foote81L6.Star
public import CFSG.CGT.Foote81L6.DescentTools
public import CFSG.ClassicalInvolution.NormalQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

namespace FooteCore

variable {G : Type*} [Group G] [Finite G] {T : Subgroup G} {k n : ℕ}
  (D : FooteCore G T (k + 3) n)

@[expose] def descM (O : Subgroup G) : Subgroup G := O ⊔ zpowers D.a

theorem descM_normal {O : Subgroup G} [O.Normal]
    (haO : ∀ g : G, g * D.a * g⁻¹ * D.a⁻¹ ∈ O) : (D.descM O).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hle : D.descM O ≤ (D.descM O).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun o ho => ?_) (zpowers_le.2 ?_)
    · show g * o * g⁻¹ ∈ D.descM O
      exact mem_sup_left ((inferInstance : O.Normal).conj_mem o ho g)
    · show g * D.a * g⁻¹ ∈ D.descM O
      have : g * D.a * g⁻¹ = (g * D.a * g⁻¹ * D.a⁻¹) * D.a := by group
      rw [this]
      exact mul_mem (mem_sup_left (haO g)) (mem_sup_right (mem_zpowers _))
  exact hle hx

include D in
theorem T_inf_eq_bot_of_odd {O : Subgroup G} (hO : Odd (Nat.card O)) : T ⊓ O = ⊥ := by
  have hcop : Nat.Coprime (Nat.card T) (Nat.card O) := by
    rw [D.card_T]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hO)
  exact Subgroup.inf_eq_bot_of_coprime hcop

theorem T_inf_descM {O : Subgroup G} [O.Normal] (hO : Odd (Nat.card O)) :
    T ⊓ D.descM O = zpowers D.a := by
  refine le_antisymm (fun x hx => ?_) (le_inf (zpowers_le.2 D.a_mem_T) le_sup_right)
  obtain ⟨hxT, hxM⟩ := mem_inf.1 hx
  obtain ⟨o, ho, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer
    (by rw [normalizer_eq_top]; exact le_top : zpowers D.a ≤ normalizer (O : Set G))).1 hxM
  have hwT : w ∈ T := (zpowers_le.2 D.a_mem_T) hw
  have hoT : o ∈ T := by
    have : o = (o * w) * w⁻¹ := by group
    rw [this]
    exact mul_mem hxT (inv_mem hwT)
  have : o ∈ T ⊓ O := mem_inf.2 ⟨hoT, ho⟩
  rw [D.T_inf_eq_bot_of_odd hO, mem_bot] at this
  rw [this, one_mul]
  exact hw

theorem mem_zpowers_a_iff {x : G} : x ∈ zpowers D.a ↔ x = 1 ∨ x = D.a := by
  constructor
  · intro hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hx
    rw [zpow_eq_zpow_emod' j (show D.a ^ 2 = 1 by rw [sq]; exact D.a_mul_a)]
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
    · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem a_not_mem_B : D.a ∉ D.B := by
  intro h
  have : D.a ∈ D.A ⊓ D.B := mem_inf.2 ⟨D.a_mem, h⟩
  rw [D.A_inf_B, mem_bot] at this
  exact D.a_ne_one this

theorem B_inf_descM {O : Subgroup G} [O.Normal] (hO : Odd (Nat.card O)) :
    D.B ⊓ D.descM O = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxB, hxM⟩ := mem_inf.1 hx
  have : x ∈ T ⊓ D.descM O := mem_inf.2 ⟨D.B_le_T hxB, hxM⟩
  rw [D.T_inf_descM hO, D.mem_zpowers_a_iff] at this
  rcases this with rfl | rfl
  · exact one_mem _
  · exact absurd hxB D.a_not_mem_B

noncomputable def eA : ↥D.A ≃* DihedralGroup (2 ^ (k + 2)) := D.A_iso.some

theorem eA_a : D.eA ⟨D.a, D.a_mem⟩ = zc (k + 2) := by
  rcases eq_one_or_zc_of_comm (a := k + 2) (by omega) (c := D.eA ⟨D.a, D.a_mem⟩) (fun g => by
      obtain ⟨y, rfl⟩ := D.eA.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg D.eA (Subtype.ext (D.a_comm y (mem_sup_left y.2)))) with h | h
  · exact absurd (congrArg Subtype.val (D.eA.injective (h.trans D.eA.map_one.symm))) D.a_ne_one
  · exact h

@[expose] noncomputable def a₀ : G := (D.eA.symm (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))) : G)

theorem a₀_eq : D.a₀ = (D.eA.symm (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))) : G) := rfl

theorem a₀_mem : D.a₀ ∈ D.A := (D.eA.symm _).2

theorem a₀_mul_a₀ : D.a₀ * D.a₀ = D.a := by
  have h : D.eA.symm (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))) *
      D.eA.symm (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))) = ⟨D.a, D.a_mem⟩ := by
    rw [← map_mul, r_quarter_mul_self, ← D.eA_a, MulEquiv.symm_apply_apply]
  exact congrArg Subtype.val h

theorem orderOf_a₀ : orderOf D.a₀ = 4 := by
  rw [a₀, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_r_quarter]

theorem a₀_not_mem_zpowers_a : D.a₀ ∉ zpowers D.a := by
  intro h
  rcases D.mem_zpowers_a_iff.1 h with h1 | h1
  · have := D.orderOf_a₀
    rw [h1, orderOf_one] at this
    omega
  · have := D.orderOf_a₀
    rw [h1, D.a_order] at this
    omega

theorem a₀_inv : D.a₀⁻¹ = D.a₀ * D.a := by
  have h4 : D.a₀ * D.a₀ * (D.a₀ * D.a₀) = 1 := by rw [D.a₀_mul_a₀, D.a_mul_a]
  have : D.a₀ * (D.a₀ * D.a) = 1 := by
    rw [← D.a₀_mul_a₀]
    calc D.a₀ * (D.a₀ * (D.a₀ * D.a₀)) = D.a₀ * D.a₀ * (D.a₀ * D.a₀) := by group
      _ = 1 := h4
  exact (eq_inv_of_mul_eq_one_right this).symm

theorem conj_a₀ {g : G} (hg : g ∈ D.A ⊔ zpowers D.t) :
    g * D.a₀ * g⁻¹ = D.a₀ ∨ g * D.a₀ * g⁻¹ = D.a₀ * D.a := by
  obtain ⟨e⟩ := D.At_iso
  have ha₀At : D.a₀ ∈ D.A ⊔ zpowers D.t := mem_sup_left D.a₀_mem
  have hconjAt : g * D.a₀ * g⁻¹ ∈ D.A ⊔ zpowers D.t := mul_mem (mul_mem hg ha₀At) (inv_mem hg)
  have h4 : ∀ {u : G} (hu : u ∈ D.A ⊔ zpowers D.t), orderOf u = 4 →
      e ⟨u, hu⟩ = r ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 3))) ∨
        e ⟨u, hu⟩ = (r ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 3))))⁻¹ := by
    intro u hu hu4
    apply eq_quarter_of_orderOf_eq_four (k := k + 1)
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hu4
  have hord : orderOf (g * D.a₀ * g⁻¹) = 4 := by
    rw [← D.orderOf_a₀]
    exact (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc])).symm
  have hinv : (⟨D.a₀ * D.a, mul_mem ha₀At (mem_sup_left D.a_mem)⟩ : ↥(D.A ⊔ zpowers D.t)) =
      (⟨D.a₀, ha₀At⟩)⁻¹ := Subtype.ext (by simp [D.a₀_inv])
  rcases h4 ha₀At D.orderOf_a₀ with h1 | h1 <;> rcases h4 hconjAt hord with h2 | h2
  · left
    exact congrArg Subtype.val (e.injective (h2.trans h1.symm))
  · right
    have : e ⟨g * D.a₀ * g⁻¹, hconjAt⟩ = e (⟨D.a₀, ha₀At⟩⁻¹) := by rw [map_inv, h2, h1]
    rw [← hinv] at this
    exact congrArg Subtype.val (e.injective this)
  · right
    have : e ⟨g * D.a₀ * g⁻¹, hconjAt⟩ = e (⟨D.a₀, ha₀At⟩⁻¹) := by rw [map_inv, h2, h1, inv_inv]
    rw [← hinv] at this
    exact congrArg Subtype.val (e.injective this)
  · left
    exact congrArg Subtype.val (e.injective (h2.trans h1.symm))

section MapQuot

variable {X : Subgroup G} {N : Subgroup G} [N.Normal]

noncomputable def mapQuotHom (X : Subgroup G) (N : Subgroup G) [N.Normal] :
    ↥X →* ↥(X.map (QuotientGroup.mk' N)) :=
  ((QuotientGroup.mk' N).comp X.subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)

theorem mapQuotHom_surjective : Function.Surjective (mapQuotHom X N) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem mapQuotHom_ker : (mapQuotHom X N).ker = N.subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    have := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).1 this
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h)

noncomputable def mapQuotEquiv {H : Type*} [Group H] (φ : ↥X →* H) (hφ : Function.Surjective φ)
    (hker : φ.ker = N.subgroupOf X) : ↥(X.map (QuotientGroup.mk' N)) ≃* H :=
  (QuotientGroup.quotientKerEquivOfSurjective _ mapQuotHom_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (mapQuotHom_ker.trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ))

end MapQuot

variable {O : Subgroup G} [O.Normal]

theorem descM_subgroupOf_A (hO : Odd (Nat.card O)) {x : ↥D.A} :
    x ∈ (D.descM O).subgroupOf D.A ↔ (x : G) = 1 ∨ (x : G) = D.a := by
  rw [mem_subgroupOf, ← D.mem_zpowers_a_iff, ← D.T_inf_descM hO, mem_inf]
  exact ⟨fun h => ⟨D.A_le_T x.2, h⟩, fun h => h.2⟩

theorem descM_subgroupOf_At (hO : Odd (Nat.card O)) {x : ↥(D.A ⊔ zpowers D.t)} :
    x ∈ (D.descM O).subgroupOf (D.A ⊔ zpowers D.t) ↔ (x : G) = 1 ∨ (x : G) = D.a := by
  rw [mem_subgroupOf, ← D.mem_zpowers_a_iff, ← D.T_inf_descM hO, mem_inf]
  exact ⟨fun h => ⟨D.At_le_T x.2, h⟩, fun h => h.2⟩

theorem descM_subgroupOf_eq_bot (hO : Odd (Nat.card O)) {X : Subgroup G} (hX : X ≤ D.B) :
    (D.descM O).subgroupOf X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_subgroupOf] at hx
  have : (x : G) ∈ D.B ⊓ D.descM O := mem_inf.2 ⟨hX x.2, hx⟩
  rw [D.B_inf_descM hO, mem_bot] at this
  exact Subtype.ext this

noncomputable def descAEquiv (hO : Odd (Nat.card O)) [(D.descM O).Normal] :
    ↥(D.A.map (QuotientGroup.mk' (D.descM O))) ≃* DihedralGroup (2 ^ (k + 1)) :=
  mapQuotEquiv ((dihedralReduce (k + 1)).comp D.eA.toMonoidHom)
    ((dihedralReduce_surjective _).comp D.eA.surjective) (by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        dihedralReduce_eq_one_iff, D.descM_subgroupOf_A hO, ← D.eA_a, ← map_one D.eA]
      constructor
      · rintro (h | h)
        · left; exact congrArg Subtype.val (D.eA.injective h)
        · right; exact congrArg Subtype.val (D.eA.injective h)
      · rintro (h | h)
        · left; congr 1; exact Subtype.ext h
        · right; congr 1; exact Subtype.ext h)

noncomputable def descAtEquiv (hO : Odd (Nat.card O)) [(D.descM O).Normal] :
    ↥((D.A ⊔ zpowers D.t).map (QuotientGroup.mk' (D.descM O))) ≃* DihedralGroup (2 ^ (k + 2)) :=
  mapQuotEquiv ((dihedralReduce (k + 2)).comp D.eAt.toMonoidHom)
    ((dihedralReduce_surjective _).comp D.eAt.surjective) (by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        dihedralReduce_eq_one_iff, D.descM_subgroupOf_At hO, ← D.eAt_a, ← map_one D.eAt]
      constructor
      · rintro (h | h)
        · left; exact congrArg Subtype.val (D.eAt.injective h)
        · right; exact congrArg Subtype.val (D.eAt.injective h)
      · rintro (h | h)
        · left; congr 1; exact Subtype.ext h
        · right; congr 1; exact Subtype.ext h)

noncomputable def descBEquiv (hO : Odd (Nat.card O)) [(D.descM O).Normal] {X : Subgroup G}
    (hX : X ≤ D.B) : ↥(X.map (QuotientGroup.mk' (D.descM O))) ≃* ↥X :=
  mapQuotEquiv (MonoidHom.id _) Function.surjective_id (by
    rw [D.descM_subgroupOf_eq_bot hO hX]
    ext x
    simp)

section Descent

variable (hO : Odd (Nat.card O)) [(D.descM O).Normal]

local notation "ρ" => QuotientGroup.mk' (D.descM O)

include hO in
theorem mem_B_of_mk_eq {x y : G} (hx : x ∈ D.B) (hy : y ∈ D.B) (h : ρ x = ρ y) : x = y := by
  have h1 : x⁻¹ * y ∈ D.descM O := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
    exact h
  have : x⁻¹ * y ∈ D.B ⊓ D.descM O := mem_inf.2 ⟨mul_mem (inv_mem hx) hy, h1⟩
  rw [D.B_inf_descM hO, mem_bot] at this
  rw [← mul_inv_cancel_left x y, this, mul_one]

include hO in
theorem mk_eq_one_of_mem_B {x : G} (hx : x ∈ D.B) (h : ρ x = 1) : x = 1 :=
  D.mem_B_of_mk_eq hO hx (one_mem _) (by rw [h, map_one])

theorem map_sup_zpowers (X : Subgroup G) (g : G) :
    (X ⊔ zpowers g).map ρ = X.map ρ ⊔ zpowers (ρ g) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]

include hO in
theorem map_B_inf_centralizer :
    D.B.map ρ ⊓ centralizer ({ρ D.t} : Set (G ⧸ D.descM O)) =
      (D.B ⊓ centralizer ({D.t} : Set G)).map ρ := by
  apply le_antisymm
  · rintro _ ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
    have hc' := mem_centralizer_singleton_iff.1 hc
    rw [← map_mul, ← map_mul] at hc'
    have hm : y * D.t * (D.t * y)⁻¹ ∈ D.B := by
      have : y * D.t * (D.t * y)⁻¹ = y * (D.t * y⁻¹ * D.t⁻¹) := by group
      rw [this]
      exact mul_mem hy (D.conj_t_B _ (inv_mem hy))
    have h1 : ρ (y * D.t * (D.t * y)⁻¹) = 1 := by rw [map_mul, map_inv, hc', mul_inv_cancel]
    have := D.mk_eq_one_of_mem_B hO hm h1
    exact mul_inv_eq_one.1 this
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyB, hyc⟩ := mem_inf.1 hy
    refine mem_inf.2 ⟨⟨y, hyB, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hyc]

@[expose] noncomputable def descent :
    FooteCore (G ⧸ D.descM O) (T.map (QuotientGroup.mk' (D.descM O))) (k + 2) n where
  A := D.A.map ρ
  B := D.B.map ρ
  B₀ := D.B₀.map ρ
  B₁ := D.B₁.map ρ
  t := ρ D.t
  s := ρ D.s
  a := ρ D.a₀
  b₀ := ρ D.b₀
  b₁ := ρ D.b₁
  T_eq := (congrArg (Subgroup.map ρ) D.T_eq).trans (by
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers])
  A_inf_B := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    rw [mem_bot]
    have h1 : x⁻¹ * y ∈ T ⊓ D.descM O := by
      refine mem_inf.2 ⟨mul_mem (inv_mem (D.A_le_T hx)) (D.B_le_T hy), ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hxy
      exact QuotientGroup.eq.1 hxy.symm
    rw [D.T_inf_descM hO, D.mem_zpowers_a_iff] at h1
    have hyA : y ∈ D.A := by
      rcases h1 with h1 | h1
      · rw [← mul_inv_cancel_left x y, h1, mul_one]; exact hx
      · rw [← mul_inv_cancel_left x y, h1]; exact mul_mem hx D.a_mem
    have : y ∈ D.A ⊓ D.B := mem_inf.2 ⟨hyA, hy⟩
    rw [D.A_inf_B, mem_bot] at this
    rw [← hxy, this, map_one]
  A_comm_B := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, D.A_comm_B x hx y hy]
  conj_t_A := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨D.t * x * D.t⁻¹, D.conj_t_A x hx, by simp only [map_mul, map_inv]⟩
  conj_t_B := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨D.t * x * D.t⁻¹, D.conj_t_B x hx, by simp only [map_mul, map_inv]⟩
  t_sq := by rw [← map_pow, D.t_sq, map_one]
  two_le_m := by omega
  A_iso := ⟨D.descAEquiv hO⟩
  At_iso := ⟨(MulEquiv.subgroupCongr (D.map_sup_zpowers D.A D.t).symm).trans (D.descAtEquiv hO)⟩
  B_eq := by rw [D.B_eq, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers]
  B₀_inf_B₁ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    rw [mem_bot]
    have := D.mem_B_of_mk_eq hO (D.B₁_le_B hy) (D.B₀_le_B hx) hxy
    subst this
    have h0 : y ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨hx, hy⟩
    rw [D.B₀_inf_B₁, mem_bot] at h0
    rw [h0, map_one]
  B₀_comm_B₁ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, D.B₀_comm_B₁ x hx y hy]
  m_lt_n := by have := D.m_lt_n; omega
  B₀_iso := ⟨(D.descBEquiv hO D.B₀_le_B).trans D.B₀_iso.some⟩
  B₁_iso := ⟨(D.descBEquiv hO D.B₁_le_B).trans D.B₁_iso.some⟩
  s_sq := by rw [← map_pow, D.s_sq, map_one]
  conj_s_B₀ := by
    rw [← D.conj_s_B₀]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨D.s * x * D.s⁻¹, ⟨x, hx, rfl⟩, by simp [map_mul, map_inv]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨ρ x, ⟨x, hx, rfl⟩, by simp [map_mul, map_inv]⟩
  Bt_conj := by
    rintro _ ⟨x, hx, rfl⟩ hsq
    rw [← map_mul, ← map_pow] at hsq
    have hxt : (x * D.t) ^ 2 ∈ D.B := by
      have : (x * D.t) ^ 2 = x * (D.t * x * D.t⁻¹) * (D.t * D.t) := by rw [sq]; group
      rw [this, D.t_mul_t, mul_one]
      exact mul_mem hx (D.conj_t_B x hx)
    obtain ⟨y, hy, hyx⟩ := D.Bt_conj x hx (D.mk_eq_one_of_mem_B hO hxt hsq)
    exact ⟨ρ y, ⟨y, hy, rfl⟩, by rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, hyx]⟩
  CBt_iso := ⟨(MulEquiv.subgroupCongr (D.map_B_inf_centralizer hO)).trans
    ((D.descBEquiv hO inf_le_left).trans D.CBt_iso.some)⟩
  a_mem := ⟨D.a₀, D.a₀_mem, rfl⟩
  a_order := by
    have hne : ρ D.a₀ ≠ 1 := by
      intro h
      have : D.a₀ ∈ T ⊓ D.descM O :=
        mem_inf.2 ⟨D.A_le_T D.a₀_mem, (QuotientGroup.eq_one_iff _).1 h⟩
      rw [D.T_inf_descM hO] at this
      exact D.a₀_not_mem_zpowers_a this
    refine orderOf_eq_prime ?_ hne
    rw [← map_pow, sq, D.a₀_mul_a₀]
    exact (QuotientGroup.eq_one_iff _).2 (mem_sup_right (mem_zpowers _))
  a_comm := by
    intro x hx
    rw [← D.map_sup_zpowers] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rcases D.conj_a₀ hy with h | h
    · have := congrArg ρ h
      simp only [map_mul, map_inv] at this
      calc ρ y * ρ D.a₀ = ρ y * ρ D.a₀ * (ρ y)⁻¹ * ρ y := by group
        _ = ρ D.a₀ * ρ y := by rw [this]
    · have := congrArg ρ h
      simp only [map_mul, map_inv] at this
      have ha : ρ D.a = 1 := (QuotientGroup.eq_one_iff _).2 (mem_sup_right (mem_zpowers _))
      rw [ha, mul_one] at this
      calc ρ y * ρ D.a₀ = ρ y * ρ D.a₀ * (ρ y)⁻¹ * ρ y := by group
        _ = ρ D.a₀ * ρ y := by rw [this]
  b₀_mem := ⟨D.b₀, D.b₀_mem, rfl⟩
  b₀_order := by
    refine orderOf_eq_prime (by rw [← map_pow, sq, D.b₀_mul_b₀, map_one]) fun h => ?_
    exact D.b₀_ne_one (D.mk_eq_one_of_mem_B hO D.b₀_mem_B h)
  b₀_comm := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, D.b₀_comm x hx]
  b₁_mem := ⟨D.b₁, D.b₁_mem, rfl⟩
  b₁_order := by
    refine orderOf_eq_prime (by rw [← map_pow, sq, D.b₁_mul_b₁, map_one]) fun h => ?_
    exact D.b₁_ne_one (D.mk_eq_one_of_mem_B hO D.b₁_mem_B h)
  b₁_comm := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, D.b₁_comm x hx]

end Descent

end FooteCore

end CFSG.CGT.Foote81L6
