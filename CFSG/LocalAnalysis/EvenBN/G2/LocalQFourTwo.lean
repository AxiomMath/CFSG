module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFour
public import CFSG.LocalAnalysis.EvenBN.G2.LocalYFive

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open scoped commutatorElement Pointwise

namespace Model

section SbY

variable (K : Type) [Field K] [CharP K 2]

@[expose] def SbY : Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ b e f : K, g = g2N 0 b 0 0 e f}
  mul_mem' := by
    rintro _ _ ⟨b, e, f, rfl⟩ ⟨b', e', f', rfl⟩
    exact ⟨b + b', e + e', f + f' + b' * e, by
      rw [g2N_mul_coords]; refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring⟩
  one_mem' := ⟨0, 0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨b, e, f, rfl⟩
    exact ⟨b, e, f + b * e, by
      rw [g2N_inv_coords]; refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring⟩

variable {K}

theorem mem_SbY {g : ModGL .G2 K} : g ∈ SbY K ↔ ∃ b e f : K, g = g2N 0 b 0 0 e f := Iff.rfl

theorem commutator_g2N_SbY (b e f b' e' f' : K) :
    ⁅g2N 0 b 0 0 e f, g2N 0 b' 0 0 e' f'⁆ = g2N 0 0 0 0 0 (b * e' + e * b') := by
  rw [g2N_commutator_coords]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem SbY_le_D : SbY K ≤ Model.D K := by
  rintro _ ⟨b, e, f, rfl⟩
  rw [g2N_mem_D_iff]

theorem U_le_SbY : U K ≤ SbY K := by
  intro g hg
  obtain ⟨f, rfl⟩ := mem_U.1 hg
  exact ⟨0, 0, f, rfl⟩

theorem SbY_le_adjointGroup : SbY K ≤ adjointGroup .G2 K :=
  (SbY_le_D.trans D_le_S).trans (S_le_adjointGroup K)

theorem SbY_inf_centralizer : SbY K ⊓ centralizer (SbY K : Set (ModGL .G2 K)) = U K := by
  apply le_antisymm
  · rintro _ ⟨⟨b, e, f, rfl⟩, hc⟩
    have h1 := mem_centralizer_iff.1 hc _ ⟨0, 1, 0, rfl⟩
    have h2 := mem_centralizer_iff.1 hc _ ⟨1, 0, 0, rfl⟩
    have c1 : ⁅g2N 0 b 0 0 e f, g2N (0 : K) 0 0 0 1 0⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 h1.symm
    have c2 : ⁅g2N 0 b 0 0 e f, g2N (0 : K) 1 0 0 0 0⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 h2.symm
    rw [commutator_g2N_SbY, ← g2N_zero] at c1 c2
    obtain ⟨-, -, -, -, -, hb⟩ := g2N_injective c1
    obtain ⟨-, -, -, -, -, he⟩ := g2N_injective c2
    simp only [mul_one, mul_zero, add_zero, zero_add] at hb he
    rw [hb, he]
    exact mem_U.2 ⟨f, rfl⟩
  · refine le_inf U_le_SbY fun g hg => mem_centralizer_iff.2 ?_
    rintro _ ⟨b, e, f, rfl⟩
    obtain ⟨f', rfl⟩ := mem_U.1 hg
    have := commutator_g2N_SbY b e f 0 0 f'
    simp only [mul_zero, add_zero, g2N_zero] at this
    exact (commutatorElement_eq_one_iff_mul_comm.1 this)

variable [Finite K]

theorem card_SbY : Nat.card (SbY K) = Nat.card K ^ 3 := by
  refine card_eq_of_param (fun v => g2N 0 (v 0) 0 0 (v 1) (v 2))
    (g2N_comp_injective _ _ _ _ _ _ fun v w _ h2 _ _ h5 h6 => ?_) fun g => ?_
  · funext i
    fin_cases i
    exacts [h2, h5, h6]
  · rw [mem_SbY]
    exact ⟨fun ⟨b, e, f, h⟩ => ⟨![b, e, f], h.symm⟩, fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, h.symm⟩⟩

theorem S_inf_centralizer_J₁_four (hK : Nat.card K = 4) :
    S K ⊓ centralizer (J₁ K : Set (ModGL .G2 K)) = SbY K := by
  rw [(yamada_3_9_4_four (K := K) hK).2.2.1]
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_ <;> intro g hg <;> obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hg
    · exact ⟨s, 0, 0, pinnedX_a_eq_g2N s⟩
    · exact ⟨0, s, 0, pinnedX_b_eq_g2N s⟩
    · exact ⟨0, 0, s, pinnedX_c_eq_g2N s⟩
  · rintro _ ⟨b, e, f, rfl⟩
    have h : g2N (0 : K) b 0 0 e f =
        pinnedX .G2 K g2a b * pinnedX .G2 K g2b e * pinnedX .G2 K g2c f := by
      simp only [g2N, pinnedX_zero, one_mul, mul_one]
    rw [h]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (mem_rootSubgroup.2 ⟨b, rfl⟩)))
      (mem_sup_left (mem_sup_right (mem_rootSubgroup.2 ⟨e, rfl⟩))))
      (mem_sup_right (mem_rootSubgroup.2 ⟨f, rfl⟩))

omit [Finite K] in
theorem D_inf_rootSubgroup_r : Model.D K ⊓ rootSubgroup .G2 K g2r = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgD, hgr⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hgr
  rw [pinnedX_r_eq_g2N, g2N_mem_D_iff] at hgD
  rw [pinnedX_r_eq_g2N, hgD, g2N_zero]
  exact one_mem _

end SbY

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

section SbYFacts

variable
  [CharP K 2]

@[expose] noncomputable def sbY : Subgroup G := d.image (Model.SbY K)

@[expose] noncomputable def xb₁ : G :=
  d.emb ⟨g2N 0 1 0 0 0 0, Model.SbY_le_adjointGroup ⟨1, 0, 0, rfl⟩⟩

@[expose] noncomputable def x3ab₁ : G :=
  d.emb ⟨g2N 0 0 0 0 1 0, Model.SbY_le_adjointGroup ⟨0, 1, 0, rfl⟩⟩

theorem sbY_le_D : d.sbY ≤ d.D := d.image_mono Model.SbY_le_D

theorem U_le_sbY : d.U ≤ d.sbY := d.image_mono Model.U_le_SbY

theorem sbY_inf_centralizer : d.sbY ⊓ centralizer (d.sbY : Set G) = d.U := by
  rw [sbY, ← d.image_inf_centralizer _ Model.SbY_le_adjointGroup, Model.SbY_inf_centralizer]
  rfl

theorem xb₁_mem_sbY : d.xb₁ ∈ d.sbY :=
  d.emb_mem_image ⟨1, 0, 0, rfl⟩

theorem x3ab₁_mem_sbY : d.x3ab₁ ∈ d.sbY :=
  d.emb_mem_image ⟨0, 1, 0, rfl⟩

theorem exists_mem_sbY_commutator_eq {u₁ u₂ : G} (hu₁ : u₁ ∈ d.U) (hu₂ : u₂ ∈ d.U) :
    ∃ p ∈ d.sbY, ⁅p, d.xb₁⁆ = u₁ ∧ ⁅p, d.x3ab₁⁆ = u₂ := by
  obtain ⟨g₁, hg₁, rfl⟩ := d.mem_image.1 hu₁
  obtain ⟨g₂, hg₂, rfl⟩ := d.mem_image.1 hu₂
  obtain ⟨e, he⟩ := Model.mem_U.1 hg₁
  obtain ⟨b, hb⟩ := Model.mem_U.1 hg₂
  have hp : g2N (0 : K) b 0 0 e 0 ∈ adjointGroup .G2 K :=
    Model.SbY_le_adjointGroup ⟨b, e, 0, rfl⟩
  refine ⟨d.emb ⟨_, hp⟩, d.emb_mem_image ⟨b, e, 0, rfl⟩, ?_, ?_⟩
  · rw [xb₁, ← map_commutatorElement]
    refine congrArg d.emb (Subtype.ext ?_)
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [he, ← commutatorElement_def, Model.commutator_g2N_SbY]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · rw [x3ab₁, ← map_commutatorElement]
    refine congrArg d.emb (Subtype.ext ?_)
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hb, ← commutatorElement_def, Model.commutator_g2N_SbY]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem xb₁_mul_x3ab₁_ne : d.xb₁ * d.x3ab₁ ≠ d.x3ab₁ * d.xb₁ := by
  intro h
  have h1 : ⁅d.xb₁, d.x3ab₁⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
  rw [xb₁, x3ab₁, ← map_commutatorElement, ← map_one d.emb] at h1
  have h2 := congrArg Subtype.val (d.emb_injective h1)
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
  rw [← commutatorElement_def, Model.commutator_g2N_SbY, ← g2N_zero] at h2
  obtain ⟨-, -, -, -, -, h3⟩ := g2N_injective h2
  simp at h3

variable [Finite K]

theorem card_sbY : Nat.card d.sbY = Nat.card K ^ 3 :=
  (d.card_image Model.SbY_le_adjointGroup).trans Model.card_SbY

theorem S_inf_centralizer_J₁_four (hK4 : Nat.card K = 4) :
    d.S ⊓ centralizer (d.J₁ : Set G) = d.sbY := by
  rw [S, J₁, ← d.image_inf_centralizer _ (Model.torusFix_le_adjointGroup K g2c),
    Model.S_inf_centralizer_J₁_four hK4]
  rfl

theorem D_inf_centralizer_J₁_four (hK4 : Nat.card K = 4) :
    d.D ⊓ centralizer (d.J₁ : Set G) = d.sbY := by
  refine le_antisymm ?_ ?_
  · rw [← d.S_inf_centralizer_J₁_four hK4]
    exact inf_le_inf_right _ d.inclusions.2.2.2.2.2.2.2.1
  · rw [← d.S_inf_centralizer_J₁_four hK4]
    exact le_inf ((d.S_inf_centralizer_J₁_four hK4).le.trans d.sbY_le_D) inf_le_right

theorem D_inf_centralizer_J₃_four (hK4 : Nat.card K = 4) :
    d.D ⊓ centralizer (d.J₃ : Set G) = ⊥ := by
  have h3 := (d.yamada_3_9_4_four_G hK4).2.2.2 2 (by decide)
  have e : d.D ⊓ centralizer (d.J₃ : Set G) = d.D ⊓ (d.S ⊓ centralizer (d.Ji 2 : Set G)) := by
    rw [← inf_assoc, inf_eq_left.2 d.inclusions.2.2.2.2.2.2.2.1]
    rfl
  rw [e, h3, rootGroup]
  change d.image (Model.D K) ⊓ d.image (rootSubgroup .G2 K g2r) = ⊥
  rw [← d.image_inf, Model.D_inf_rootSubgroup_r, image, bot_subgroupOf, Subgroup.map_bot]

theorem U_inf_centralizer_J₃_four (hK4 : Nat.card K = 4) :
    d.U ⊓ centralizer (d.J₃ : Set G) = ⊥ := by
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  exact le_bot_iff.1 ((inf_le_inf_right _ (hUY.trans (hYX.trans (hXF.trans hFD)))).trans
    (d.D_inf_centralizer_J₃_four hK4).le)

end SbYFacts

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section QFourLocal

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem card_tD (h : Setup G L f t) (d : G2Data L K) :
    Nat.card (d.D ⊔ zpowers t : Subgroup G) = 2 * Nat.card d.D := by
  have htN : zpowers t ≤ normalizer (d.D : Set G) := (zpowers_le).2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun m hm =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hm))))
  have h1 := Common.card_sup_mul_card_inf_eq htN
  rw [inf_comm, h.zpowers_inf_L (E := d.D) (d.image_le _), Subgroup.card_bot, mul_one,
    h.card_zpowers_t] at h1
  rw [h1, mul_comm]

theorem card_yamadaD₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    Nat.card (yamadaD₁ d t) = Nat.card K ^ 6 := by
  obtain ⟨_, φ, -, -⟩ := h.yamada_5_3_4 d hK
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((d.D ⊔ zpowers t).subgroupOf (yamadaC₁ d t))
  rw [Nat.card_congr φ.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (h.tD_le_yamadaC₁ d hK)).toEquiv, h.card_tD d,
    d.cards.1, d.cards.2.2.2.2.2.1, h.card_yamadaC₁ d hK] at h1
  have h2 : 2 * Nat.card (yamadaD₁ d t) = 2 * Nat.card K ^ 6 := by rw [h1]; ring
  omega

omit [Finite G] in
theorem yamadaD₁_inf_centralizer_J₁_inf_D (d : G2Data L K) (hK4 : Nat.card K = 4) :
    yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ⊓ d.D = d.sbY := by
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  rw [inf_right_comm, inf_eq_right.2 hDD₁, d.D_inf_centralizer_J₁_four hK4]

theorem card_yamadaD₁_inf_centralizer_J₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4) :
    Nat.card (yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) : Subgroup G) = Nat.card K ^ 4 := by
  set X := yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) with hX
  have hXN : X ≤ normalizer (d.D : Set G) :=
    (inf_le_left.trans (h.yamadaD₁_le_yamadaC₁ d hK)).trans (h.yamadaC₁_le_normalizer_D d hK)
  have h1 := Common.card_sup_mul_card_inf_eq hXN
  have hsup : d.D ⊔ X = yamadaD₁ d t := by
    refine le_antisymm (sup_le le_sup_right inf_le_left) fun m hm => ?_
    obtain ⟨c, hc, n, hn, rfl⟩ := h.exists_mem_yamadaD₁_inf_centralizer_J₁_mul d hK hm
    exact mul_mem (mem_sup_right hc) (mem_sup_left hn)
  rw [hsup, inf_comm, yamadaD₁_inf_centralizer_J₁_inf_D d hK4, h.card_yamadaD₁ d hK,
    d.card_sbY, d.cards.2.2.2.2.2.1] at h1
  have hq : 0 < Nat.card K ^ 5 := by positivity
  have h2 : Nat.card K ^ 5 * Nat.card X = Nat.card K ^ 5 * Nat.card K ^ 4 := by
    rw [← h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hq h2

theorem yamadaD₁_inf_centralizer_J₁_inf_centralizer_J₃ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4) :
    yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ⊓ centralizer (d.J₃ : Set G) = ⊥ := by
  obtain ⟨hC₁U, hC₁t, -, -⟩ := h.two_core_C₁ d hK
  have hc₁ := h.cosetData_tU d hK
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨hxD₁, -⟩, hxJ₃⟩ := hx
  have hxC₁ := h.yamadaD₁_le_yamadaC₁ d hK hxD₁
  have hy : x⁻¹ * t * x * t ∈ d.U := hc₁.crossed_mem_of_mem ⟨yamadaC₁_le d t hxC₁, hC₁U hxC₁⟩
  have hy1 : x⁻¹ * t * x * t = 1 := by
    have hyJ : x⁻¹ * t * x * t ∈ d.U ⊓ centralizer (d.J₃ : Set G) := by
      refine ⟨hy, mem_centralizer_iff.2 fun j hj => ?_⟩
      have hjt : j * t = t * j :=
        mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hj))
      have hjx : j * x = x * j := (mem_centralizer_iff.1 hxJ₃ j hj)
      have hjx' : j * x⁻¹ = x⁻¹ * j := by
        rw [← (Commute.inv_right (hjx : Commute j x)).eq]
      calc j * (x⁻¹ * t * x * t) = x⁻¹ * (j * t) * x * t := by
            rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hjx']; group
        _ = x⁻¹ * t * (j * x) * t := by rw [hjt]; group
        _ = x⁻¹ * t * x * (j * t) := by rw [hjx]; group
        _ = x⁻¹ * t * x * t * j := by rw [hjt]; group
    rw [d.U_inf_centralizer_J₃_four hK4] at hyJ
    exact hyJ
  have hxt : x ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e : x⁻¹ * t * x = t := by
      calc x⁻¹ * t * x = x⁻¹ * t * x * t * t := by rw [mul_assoc _ t t, h.t_mul_t, mul_one]
        _ = t := by rw [hy1, one_mul]
    calc x * t = x * (x⁻¹ * t * x) := by rw [e]
      _ = t * x := by group
  have hxD : x ∈ d.D := h.mem_D_of_mem_tD_of_mem_yamadaD₁ d hK
    (by rw [← hC₁t]; exact ⟨hxC₁, hxt⟩) hxD₁
  have h1 : x ∈ d.D ⊓ centralizer (d.J₃ : Set G) := ⟨hxD, hxJ₃⟩
  rw [d.D_inf_centralizer_J₃_four hK4] at h1
  exact h1

end QFourLocal

end Setup

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section QFourB

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaD₁_inf_centralizer_J₁_le_yamadaB (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4) :
    yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ yamadaB d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) with hX
  have hJ₃K : d.J₃ ≤ L ⊓ centralizer (d.J₁ : Set G) := fun j hj =>
    ⟨d.image_le _ hj, mem_centralizer_iff.2 fun j' hj' => d.J₁_comm_J₃ hj' hj⟩
  have hJ₃B : d.J₃ ≤ yamadaB d := hJ₃K.trans (inf_centralizer_J₁_le_yamadaB d)
  have hJ₃X : d.J₃ ≤ normalizer (X : Set G) := fun j hj =>
    Common.mem_normalizer_inf
      (h.inf_normalizer_U_le_normalizer_yamadaD₁ d hK (d.J₃_le_inf_normalizer_U hj))
      (Subgroup.le_normalizer (hJ₃K hj).2)
  have hBN : ∀ {x : G}, x ∈ centralizer (d.J₁ : Set G) →
      x ∈ normalizer ((yamadaB d : Subgroup G) : Set G) := fun {x} hx =>
    mem_normalizer_iff.2 fun b => ⟨fun hb => conj_mem_yamadaB d hx hb, fun hb => by
      have := conj_mem_yamadaB d (inv_mem hx) hb
      rwa [inv_inv, show x⁻¹ * (x * b * x⁻¹) * x = b by group] at this⟩
  have h2 : IsPGroup 2 X := (h.isPGroup_yamadaD₁ d hK).to_le inf_le_left
  have hsolv : Group.IsSolvable X := by
    have := h2.isNilpotent
    infer_instance
  have hcop : (Nat.card d.J₃).Coprime (Nat.card X) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [hk, d.card_J₃, hK]
    exact (odd_two_pow_sub_one (by have := h.two_le; omega)).coprime_two_right.pow_right k
  intro x hx
  have hxH : x ∈ centralizer (d.J₁ : Set G) := (Subgroup.mem_inf.1 hx).2
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := X) (N := X ⊓ yamadaB d) (S := d.J₃) inf_le_left
    (fun y hy => Common.mem_normalizer_inf (Subgroup.le_normalizer hy)
      (hBN (Subgroup.mem_inf.1 hy).2))
    hJ₃X (fun j hj => Common.mem_normalizer_inf (hJ₃X hj) (hBN (hJ₃K hj).2)) hsolv hcop hx
    (fun j hj => Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx)
      ((mem_normalizer_iff.1 (hJ₃X hj) x).1 hx), by
      rw [show x⁻¹ * (j * x * j⁻¹) = (x⁻¹ * j * x⁻¹⁻¹) * j⁻¹ by group]
      exact mul_mem (conj_mem_yamadaB d (inv_mem hxH) (hJ₃B hj)) (inv_mem (hJ₃B hj))⟩)
  have hc1 : c = 1 := by
    have : c ∈ X ⊓ centralizer (d.J₃ : Set G) := hc
    rw [h.yamadaD₁_inf_centralizer_J₁_inf_centralizer_J₃ d hK hK4] at this
    exact this
  rw [hc1, one_mul]
  exact (Subgroup.mem_inf.1 hn).2

end QFourB

end Setup

theorem exists_mem_inv_mul_comm {G : Type*} [Group G] {P U : Subgroup G} {p₁ p₂ x : G}
    (hsurj : ∀ u₁ ∈ U, ∀ u₂ ∈ U, ∃ p ∈ P, ⁅p, p₁⁆ = u₁ ∧ ⁅p, p₂⁆ = u₂)
    (hx₁ : ⁅x, p₁⁆ ∈ U) (hx₂ : ⁅x, p₂⁆ ∈ U) :
    ∃ p ∈ P, p⁻¹ * x * p₁ = p₁ * (p⁻¹ * x) ∧ p⁻¹ * x * p₂ = p₂ * (p⁻¹ * x) := by
  obtain ⟨p, hp, h1, h2⟩ := hsurj _ hx₁ _ hx₂
  have key : ∀ q : G, ⁅p, q⁆ = ⁅x, q⁆ → p⁻¹ * x * q = q * (p⁻¹ * x) := by
    intro q hq
    rw [commutatorElement_def, commutatorElement_def] at hq
    have e : p * q * p⁻¹ = x * q * x⁻¹ := mul_right_cancel hq
    calc p⁻¹ * x * q = p⁻¹ * (x * q * x⁻¹) * x := by group
      _ = p⁻¹ * (p * q * p⁻¹) * x := by rw [e]
      _ = q * (p⁻¹ * x) := by group
  exact ⟨p, hp, key p₁ h1, key p₂ h2⟩

@[expose] def QFourSylowPackage
    {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] (d : G2Data L K)
    (V : Subgroup G) : Prop :=
  Nat.card (V ⊓ centralizer (V : Set G) : Subgroup G) = Nat.card K ^ 2 ∧
    (∀ z ∈ V ⊓ centralizer (V : Set G), z * z = 1) ∧
    (∀ v ∈ V, v * v ∈ V ⊓ centralizer (V : Set G)) ∧
    ∀ a ∈ d.sbY, ∀ b ∈ d.sbY, a * b ≠ b * a → ∀ x ∈ V, x * a = a * x → x * b = b * x →
      x ∈ V ⊓ centralizer (V : Set G)

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section QFourCore

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] in
theorem yamadaU₁_eq_four (d : G2Data L K) (t : G) (hK4 : Nat.card K = 4) :
    yamadaU₁ d t = yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ⊓
      centralizer ((yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) : Subgroup G) : Set G) :=
  ite_eq_right (by omega)

theorem yamadaU₁_eq_center_of_package (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4) {V : Subgroup G}
    (hXV : yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V) (hP : QFourSylowPackage d V) :
    yamadaU₁ d t = V ⊓ centralizer (V : Set G) ∧
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) = d.sbY ⊔ (V ⊓ centralizer (V : Set G)) ∧
      d.U ≤ V ⊓ centralizer (V : Set G) ∧ d.sbY ⊓ (V ⊓ centralizer (V : Set G)) = d.U := by
  obtain ⟨hZcard, -, -, hmem⟩ := hP
  set X := yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) with hX
  set Z := V ⊓ centralizer (V : Set G) with hZ
  have hsbX : d.sbY ≤ X := by
    rw [← yamadaD₁_inf_centralizer_J₁_inf_D d hK4]
    exact inf_le_left
  have hsbV : d.sbY ≤ V := hsbX.trans hXV
  have hne := d.xb₁_mul_x3ab₁_ne
  have hp₁ := d.xb₁_mem_sbY
  have hp₂ := d.x3ab₁_mem_sbY
  have hUZ : d.U ≤ Z := by
    intro u hu
    have hu' : u ∈ d.sbY ⊓ centralizer (d.sbY : Set G) := by
      rw [d.sbY_inf_centralizer]
      exact hu
    exact hmem _ hp₁ _ hp₂ hne u (hsbV hu'.1) (mem_centralizer_iff.1 hu'.2 _ hp₁).symm
      (mem_centralizer_iff.1 hu'.2 _ hp₂).symm
  have hsbZ : d.sbY ⊓ Z = d.U := by
    refine le_antisymm (fun z hz => ?_) (le_inf d.U_le_sbY hUZ)
    rw [← d.sbY_inf_centralizer]
    exact ⟨hz.1, mem_centralizer_iff.2 fun y hy => (mem_centralizer_iff.1 hz.2.2 y (hsbV hy))⟩
  have hXle : X ≤ d.sbY ⊔ Z := by
    intro x hx
    have hxC₁ := h.yamadaD₁_le_yamadaC₁ d hK (Subgroup.mem_inf.1 hx).1
    have hpC₁ : ∀ {p : G}, p ∈ d.sbY → p ∈ yamadaC₁ d t := fun hp =>
      h.yamadaD₁_le_yamadaC₁ d hK ((le_sup_right : d.D ≤ yamadaD₁ d t) (d.sbY_le_D hp))
    have hc₁ := ((h.elemModulo_U_yamadaC₁ d hK) _ hxC₁ _ (hpC₁ hp₁)).2
    have hc₂ := ((h.elemModulo_U_yamadaC₁ d hK) _ hxC₁ _ (hpC₁ hp₂)).2
    obtain ⟨p, hp, hz₁, hz₂⟩ := exists_mem_inv_mul_comm (P := d.sbY) (U := d.U)
      (fun _ hu₁ _ hu₂ => d.exists_mem_sbY_commutator_eq hu₁ hu₂) hc₁ hc₂
    have hzV : p⁻¹ * x ∈ V := mul_mem (inv_mem (hsbV hp)) (hXV hx)
    have hzZ := hmem _ hp₁ _ hp₂ hne _ hzV hz₁ hz₂
    rw [show x = p * (p⁻¹ * x) by group]
    exact mul_mem (mem_sup_left hp) (mem_sup_right hzZ)
  have hZN : d.sbY ≤ normalizer (Z : Set G) := fun s hs => by
    have hsV := hsbV hs
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 s hsV, mul_inv_cancel_right]
      exact hz
    · intro hz
      have e : s * z * s⁻¹ = z := by
        have h1 := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 s hsV
        calc s * z * s⁻¹ = s⁻¹ * (s * (s * z * s⁻¹)) := by group
          _ = s⁻¹ * ((s * z * s⁻¹) * s) := by rw [h1]
          _ = z := by group
      rwa [e] at hz
  have h1 := Common.card_sup_mul_card_inf_eq hZN
  rw [inf_comm, hsbZ, hZcard, d.card_sbY, d.cards.1] at h1
  have hcard : Nat.card (Z ⊔ d.sbY : Subgroup G) = Nat.card K ^ 4 := by
    have hq : 0 < Nat.card K := Nat.card_pos
    have h2 : Nat.card (Z ⊔ d.sbY : Subgroup G) * Nat.card K = Nat.card K ^ 4 * Nat.card K := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hq h2
  have hXeq : X = d.sbY ⊔ Z := by
    refine Subgroup.eq_of_le_of_card_ge hXle ?_
    rw [sup_comm, hcard, h.card_yamadaD₁_inf_centralizer_J₁ d hK hK4]
  have hZX : Z ≤ X := hXeq ▸ le_sup_right
  refine ⟨?_, hXeq, hUZ, hsbZ⟩
  rw [yamadaU₁_eq_four d t hK4]
  refine le_antisymm (fun u hu => ?_) (le_inf hZX ?_)
  · obtain ⟨huX, huc⟩ := Subgroup.mem_inf.1 hu
    exact hmem _ hp₁ _ hp₂ hne u (hXV huX) (mem_centralizer_iff.1 huc _ (hsbX hp₁)).symm
      (mem_centralizer_iff.1 huc _ (hsbX hp₂)).symm
  · rw [← Subgroup.le_centralizer_iff]
    exact hXV.trans (le_centralizer_iff.1 inf_le_right)

theorem exists_isSylowOf_yamadaB (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) :
    ∃ V : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 V (yamadaB d) ∧
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) with hX
  have hXB := h.yamadaD₁_inf_centralizer_J₁_le_yamadaB d hK hK4
  have hX2 : IsPGroup 2 X := (h.isPGroup_yamadaD₁ d hK).to_le inf_le_left
  obtain ⟨Q, hQ⟩ := (hX2.comap_subtype (K := yamadaB d)).exists_le_sylow
  refine ⟨(Q : Subgroup (yamadaB d)).map (yamadaB d).subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hXB hx⟩, hQ hx, rfl⟩

theorem le_centralizer_yamadaU₁_of_four (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4) {P : Subgroup G} (hPS : P ≤ d.S)
    (hPN : P ≤ normalizer (yamadaU₁ d t : Set G)) (hJP : d.J₁ ≤ normalizer (P : Set G))
    (hcomm : ∀ {p u : G}, p ∈ P → u ∈ yamadaU₁ d t → ⁅p, u⁆ ∈ d.U) :
    P ≤ centralizer (yamadaU₁ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU₁eq := yamadaU₁_eq_four d t hK4
  have hcenS : ∀ {u g : G}, u ∈ d.U → g ∈ d.S → u * g = g * u := fun {u g} hu hg => by
    rw [← (d.yamada_3_12_centers).1] at hu
    exact (mem_centralizer_iff.1 hu.2 g hg).symm
  have hJ₁U₁ : d.J₁ ≤ centralizer (yamadaU₁ d t : Set G) := by
    rw [← Subgroup.le_centralizer_iff, hU₁eq]
    exact inf_le_left.trans inf_le_right
  have hCN : normalizer (yamadaU₁ d t : Set G) ≤
      normalizer (centralizer (yamadaU₁ d t : Set G) : Set G) := by
    intro n hn
    refine mem_normalizer_of_conj_mem fun y hy => mem_centralizer_iff.2 fun x hx => ?_
    have hx' : n⁻¹ * x * n ∈ yamadaU₁ d t := by
      have := (mem_normalizer_iff.1 (inv_mem hn) x).1 hx
      rwa [inv_inv] at this
    have e := mem_centralizer_iff.1 hy _ hx'
    calc x * (n * y * n⁻¹) = n * ((n⁻¹ * x * n) * y) * n⁻¹ := by group
      _ = n * (y * (n⁻¹ * x * n)) * n⁻¹ := by rw [e]
      _ = n * y * n⁻¹ * x := by group
  set N := P ⊓ centralizer (yamadaU₁ d t : Set G) with hNdef
  have h2 : IsPGroup 2 P := d.isSylowOf_S.isPGroup.to_le hPS
  have hsolv : Group.IsSolvable P := by
    have := h2.isNilpotent
    infer_instance
  have hcop : (Nat.card d.J₁).Coprime (Nat.card P) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [hk, d.card_J₁, hK]
    exact (odd_two_pow_sub_one (by have := h.two_le; omega)).coprime_two_right.pow_right k
  intro p hp
  have hfix : ∀ j ∈ d.J₁, p⁻¹ * (j * p * j⁻¹) ∈ N := by
    intro j hj
    have hjp : j * p * j⁻¹ ∈ P := (mem_normalizer_iff.1 (hJP hj) p).1 hp
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hp) hjp, mem_centralizer_iff.2 fun u hu => ?_⟩
    have hju : j * u = u * j := (mem_centralizer_iff.1 (hJ₁U₁ hj) u hu).symm
    have hjc : ∀ {w : G}, w ∈ d.U → j * w * j⁻¹ = w := fun {w} hw => by
      rw [← mem_centralizer_iff.1 (d.J₁_le_centralizer_U hj) w hw, mul_inv_cancel_right]
    have hju' : j⁻¹ * u = u * j⁻¹ := by
      calc j⁻¹ * u = j⁻¹ * (u * j) * j⁻¹ := by group
        _ = j⁻¹ * (j * u) * j⁻¹ := by rw [← hju]
        _ = u * j⁻¹ := by group
    have hk1 : ⁅j * p * j⁻¹, u⁆ = ⁅p, u⁆ := by
      calc ⁅j * p * j⁻¹, u⁆ = j * p * (j⁻¹ * u) * j * p⁻¹ * j⁻¹ * u⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = j * p * (u * j⁻¹) * j * p⁻¹ * j⁻¹ * u⁻¹ := by rw [hju']
        _ = j * (p * u * p⁻¹ * u⁻¹) * (u * j⁻¹ * u⁻¹) := by group
        _ = j * ⁅p, u⁆ * j⁻¹ := by
            rw [← hju', mul_inv_cancel_right, commutatorElement_def]
        _ = ⁅p, u⁆ := hjc (hcomm hp hu)
    have hP3 : ∀ {g g' : G}, g ∈ P → g' ∈ P → ⁅g * g', u⁆ = ⁅g', u⁆ * ⁅g, u⁆ :=
      fun {g g'} hg hg' => by
        calc ⁅g * g', u⁆ = g * ⁅g', u⁆ * (u * g⁻¹ * u⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅g', u⁆ * g * (u * g⁻¹ * u⁻¹) := by rw [← hcenS (hcomm hg' hu) (hPS hg)]
          _ = ⁅g', u⁆ * ⁅g, u⁆ := by
              simp only [commutatorElement_def]
              group
    have h1 : ⁅p⁻¹ * (j * p * j⁻¹), u⁆ = 1 := by
      rw [hP3 (inv_mem hp) hjp, hk1, ← hP3 (inv_mem hp) hp, inv_mul_cancel,
        commutatorElement_one_left]
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (N := N) inf_le_left
    (fun x hx => Common.mem_normalizer_inf (le_normalizer hx) (hCN (hPN hx)))
    hJP (fun j hj => Common.mem_normalizer_inf (hJP hj) (le_normalizer (hJ₁U₁ hj)))
    hsolv hcop hp hfix
  have hcX : c ∈ yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) := by
    have h1 : c ∈ d.sbY := by
      rw [← d.S_inf_centralizer_J₁_four hK4]
      exact ⟨hPS (Subgroup.mem_inf.1 hc).1, (Subgroup.mem_inf.1 hc).2⟩
    rw [← yamadaD₁_inf_centralizer_J₁_inf_D d hK4] at h1
    exact (Subgroup.mem_inf.1 h1).1
  refine mul_mem (mem_centralizer_iff.2 fun x hx => ?_) (Subgroup.mem_inf.1 hn).2
  rw [hU₁eq] at hx
  exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 c hcX).symm

theorem yamadaU₁_spec_four (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4)
    (hpkg : ∀ V : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 V (yamadaB d) →
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V → QFourSylowPackage d V) :
    yamadaU₁ d t ≤ yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ∧ d.U ≤ yamadaU₁ d t ∧
      yamadaU₁ d t ⊓ d.D = d.U ∧
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) = d.sbY ⊔ yamadaU₁ d t := by
  obtain ⟨V, hV, hXV⟩ := h.exists_isSylowOf_yamadaB d hK hK4
  obtain ⟨hU₁, hXeq, hUZ, hsbZ⟩ := h.yamadaU₁_eq_center_of_package d hK hK4 hXV (hpkg V hV hXV)
  have hU₁X : yamadaU₁ d t ≤ yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) := by
    rw [yamadaU₁_eq_four d t hK4]
    exact inf_le_left
  refine ⟨hU₁X, hU₁ ▸ hUZ, ?_, hU₁ ▸ hXeq⟩
  refine le_antisymm (fun x hx => ?_) (le_inf (hU₁ ▸ hUZ)
    (d.U_le_sbY.trans d.sbY_le_D))
  obtain ⟨hxU₁, hxD⟩ := Subgroup.mem_inf.1 hx
  have hxsb : x ∈ d.sbY := by
    rw [← yamadaD₁_inf_centralizer_J₁_inf_D d hK4]
    exact ⟨hU₁X hxU₁, hxD⟩
  rw [← hsbZ]
  exact ⟨hxsb, hU₁ ▸ hxU₁⟩

theorem yamadaC₁_le_normalizer_yamadaU₁_four (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4)
    (hpkg : ∀ V : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 V (yamadaB d) →
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V → QFourSylowPackage d V) :
    yamadaC₁ d t ≤ normalizer (yamadaU₁ d t : Set G) := by
  obtain ⟨hU₁X, hUU₁, -, -⟩ := h.yamadaU₁_spec_four d hK hK4 hpkg
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t :=
    (hU₁X.trans inf_le_left).trans (h.yamadaD₁_le_yamadaC₁ d hK)
  refine le_normalizer_of_conj_mem fun c hc x hx => ?_
  have h1 := ((h.elemModulo_U_yamadaC₁ d hK) _ hc _ (hU₁C₁ hx)).2
  rw [commutatorElement_def] at h1
  rw [show c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x by group]
  exact mul_mem (hUU₁ h1) hx

theorem yamada_5_10_4_of_package (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4)
    (hpkg : ∀ V : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 V (yamadaB d) →
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V → QFourSylowPackage d V)
    {V : Subgroup G} (hV : CFSG.ABGLocalTools.IsSylowOf 2 V (yamadaB d))
    (hXV : yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V) :
    yamadaU₁ d t = V ⊓ centralizer (V : Set G) ∧ ElemModulo (yamadaU₁ d t) V := by
  have hP := hpkg V hV hXV
  obtain ⟨hU₁, -, -, -⟩ := h.yamadaU₁_eq_center_of_package d hK hK4 hXV hP
  refine ⟨hU₁, ?_⟩
  rw [hU₁]
  refine elemModulo_of_mul_self_mem (fun s hs => ?_) hP.2.2.1
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 s hs, mul_inv_cancel_right]
    exact hz
  · intro hz
    have e : s * z * s⁻¹ = z := by
      have h1 := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 s hs
      calc s * z * s⁻¹ = s⁻¹ * (s * (s * z * s⁻¹)) := by group
        _ = s⁻¹ * ((s * z * s⁻¹) * s) := by rw [h1]
        _ = z := by group
    rwa [e] at hz

theorem yamada_5_10_1_four_of_package (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4)
    (hpkg : ∀ V : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 V (yamadaB d) →
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V → QFourSylowPackage d V) :
    yamadaD₁ d t = d.D ⊔ yamadaU₁ d t ∧ yamadaU₁ d t ⊓ centralizer ({t} : Set G) = d.U ∧
      Nat.card (yamadaU₁ d t) = Nat.card K ^ 2 := by
  obtain ⟨V, hV, hXV⟩ := h.exists_isSylowOf_yamadaB d hK hK4
  obtain ⟨hU₁, -, -, -⟩ := h.yamadaU₁_eq_center_of_package d hK hK4 hXV (hpkg V hV hXV)
  obtain ⟨hU₁X, hUU₁, hU₁D, hXeq⟩ := h.yamadaU₁_spec_four d hK hK4 hpkg
  obtain ⟨-, hC₁t, -, -⟩ := h.two_core_C₁ d hK
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  refine ⟨le_antisymm (fun m hm => ?_) (sup_le hDD₁ (hU₁X.trans inf_le_left)), ?_, ?_⟩
  · obtain ⟨c, hc, n, hn, rfl⟩ := h.exists_mem_yamadaD₁_inf_centralizer_J₁_mul d hK hm
    rw [hXeq] at hc
    have hc' : c ∈ d.D ⊔ yamadaU₁ d t :=
      (sup_le_sup_right d.sbY_le_D (yamadaU₁ d t)) hc
    exact mul_mem hc' (mem_sup_left hn)
  · refine le_antisymm (fun x hx => ?_) (le_inf hUU₁ ((d.image_le _).trans h.L_le_centralizer))
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    have hxD₁ := (Subgroup.mem_inf.1 (hU₁X hx₁)).1
    have hxD : x ∈ d.D := h.mem_D_of_mem_tD_of_mem_yamadaD₁ d hK (by
      rw [← hC₁t]
      exact ⟨h.yamadaD₁_le_yamadaC₁ d hK hxD₁, hx₂⟩) hxD₁
    rw [← hU₁D]
    exact ⟨hx₁, hxD⟩
  · rw [hU₁, (hpkg V hV hXV).1]

theorem yamada_5_10_2_four_of_package (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4)
    (hpkg : ∀ V : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 V (yamadaB d) →
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V → QFourSylowPackage d V) :
    CFSG.IsElementaryAbelian 2 (yamadaU₁ d t) := by
  obtain ⟨V, hV, hXV⟩ := h.exists_isSylowOf_yamadaB d hK hK4
  have hP := hpkg V hV hXV
  obtain ⟨hU₁, -, -, -⟩ := h.yamadaU₁_eq_center_of_package d hK hK4 hXV hP
  rw [hU₁]
  refine isElementaryAbelian_of_forall (fun x hx y hy => ?_) hP.2.1
  exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x (Subgroup.mem_inf.1 hx).1)

theorem yamada_5_10_3_four_of_package (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4)
    (hpkg : ∀ V : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 V (yamadaB d) →
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V → QFourSylowPackage d V) :
    yamadaU₁ d t = yamadaD₁ d t ⊓ centralizer (yamadaD₁ d t : Set G) ∧
      yamadaU₁ d t ≤ yamadaF₁ d t := by
  obtain ⟨hU₁X, hUU₁, -, -⟩ := h.yamadaU₁_spec_four d hK hK4 hpkg
  have hU₁D₁ : yamadaU₁ d t ≤ yamadaD₁ d t := hU₁X.trans inf_le_left
  obtain ⟨-, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  obtain ⟨hNU, hND, -, -⟩ := d.yamada_3_13_2_G
  have hD₁ := (h.yamada_5_10_1_four_of_package d hK hK4 hpkg).1
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hDC₁ : d.D ≤ yamadaC₁ d t := le_sup_left.trans (h.tD_le_yamadaC₁ d hK)
  have hDU₁ : d.D ≤ centralizer (yamadaU₁ d t : Set G) := by
    refine h.le_centralizer_yamadaU₁_of_four d hK hK4 d.inclusions.2.2.2.2.2.2.2.1
      (hDC₁.trans (h.yamadaC₁_le_normalizer_yamadaU₁_four d hK hK4 hpkg)) (fun j hj => ?_)
      fun hp hu => ((h.elemModulo_U_yamadaC₁ d hK) _ (hDC₁ hp) _ (hU₁C₁ hu)).2
    have : j ∈ L ⊓ normalizer (d.D : Set G) := by
      rw [hND, ← hNU]
      exact d.J₁_le_inf_normalizer_U hj
    exact this.2
  have hab := (h.yamada_5_10_2_four_of_package d hK hK4 hpkg).1
  have hU₁Z : yamadaU₁ d t ≤ centralizer (yamadaD₁ d t : Set G) := by
    rw [← Subgroup.le_centralizer_iff, hD₁]
    refine sup_le hDU₁ fun x hx => mem_centralizer_iff.2 fun y hy => ?_
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : yamadaU₁ d t) ⟨x, hx⟩)
  have heq : yamadaU₁ d t = yamadaD₁ d t ⊓ centralizer (yamadaD₁ d t : Set G) := by
    refine le_antisymm (le_inf hU₁D₁ hU₁Z) fun z hz => ?_
    obtain ⟨hz₁, hz₂⟩ := Subgroup.mem_inf.1 hz
    have hU₁N : yamadaU₁ d t ≤ normalizer (d.D : Set G) :=
      hU₁C₁.trans (h.yamadaC₁_le_normalizer_D d hK)
    rw [hD₁] at hz₁
    obtain ⟨δ, hδ, x, hx, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁N z hz₁
    have hδZ : δ ∈ d.D ⊓ centralizer (d.D : Set G) := by
      refine ⟨hδ, mem_centralizer_iff.2 fun w hw => ?_⟩
      have hwD₁ : w ∈ yamadaD₁ d t := (le_sup_right : d.D ≤ yamadaD₁ d t) hw
      have h1 := mem_centralizer_iff.1 hz₂ w hwD₁
      have h2 := mem_centralizer_iff.1 (hU₁Z hx) w hwD₁
      calc w * δ = w * (δ * x) * x⁻¹ := by group
        _ = δ * x * w * x⁻¹ := by rw [h1]
        _ = δ * (x * w) * x⁻¹ := by group
        _ = δ * (w * x) * x⁻¹ := by rw [h2]
        _ = δ * w := by group
    rw [(d.yamada_3_12_centers).2.1] at hδZ
    exact mul_mem (hUU₁ hδZ) hx
  refine ⟨heq, fun x hx => ⟨⟨?_, hU₁C₁ hx⟩, hU₁D₁ hx⟩⟩
  refine h.mem_yamadaL₂_of_mem_centralizer_Y d hK ((h.yamada_5_6_1 d hK).2.1 (mem_sup_left
    (hU₁C₁ hx))) (mem_centralizer_iff.2 fun y hy => ?_)
  exact mem_centralizer_iff.1 (hU₁Z hx) y ((le_sup_right : d.D ≤ yamadaD₁ d t)
    (hFD (hXF (hYX hy))))

end QFourCore

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
