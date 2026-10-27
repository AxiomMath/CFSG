module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductEnd
import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

namespace ProductEndFourAux

theorem ordG2_four : ordG2 4 = 251596800 := by
  unfold ordG2
  norm_num

theorem isPerfect_of_isSimpleGroup_of_not_prime {H : Type} [Group H] [Finite H] [IsSimpleGroup H]
    (hp : ¬ (Nat.card H).Prime) : Group.IsPerfect H := by
  refine ⟨?_⟩
  rcases (Subgroup.commutator_normal (⊤ : Subgroup H) ⊤).eq_bot_or_eq_top with hb | ht
  · exfalso
    have hcomm : ∀ a b : H, a * b = b * a := fun a b => by
      have hm : ⁅a, b⁆ ∈ _root_.commutator H :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [_root_.commutator_def, hb, Subgroup.mem_bot] at hm
      exact commutatorElement_eq_one_iff_mul_comm.1 hm
    letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hcomm }
    exact hp (IsSimpleGroup.prime_card (α := H))
  · rw [_root_.commutator_def]
    exact ht

theorem commutator_g2Two {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) :
    ⁅_root_.commutator ↥(adjointGroup .G2 k), _root_.commutator ↥(adjointGroup .G2 k)⁆ =
        _root_.commutator ↥(adjointGroup .G2 k) ∧
      Nat.card ↥(_root_.commutator ↥(adjointGroup .G2 k)) = 6048 := by
  have hM : CFSG.Open.StatedClassicalModel ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆
      .PSU 3 3 1 := by
    rcases CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk with
      ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hM
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, hsimple⟩ := CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hM
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hM
  have hDM : (_root_.commutator ↥(adjointGroup .G2 k)).map (adjointGroup .G2 k).subtype =
      ⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let eD : ↥(_root_.commutator ↥(adjointGroup .G2 k)) ≃*
      ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ :=
    ((_root_.commutator ↥(adjointGroup .G2 k)).equivMapOfInjective _
      (adjointGroup .G2 k).subtype_injective).trans (MulEquiv.subgroupCongr hDM)
  have hs : IsSimpleGroup ↥(_root_.commutator ↥(adjointGroup .G2 k)) := eD.isSimpleGroup
  have hcardD : Nat.card ↥(_root_.commutator ↥(adjointGroup .G2 k)) = 6048 := by
    rw [Nat.card_congr eD.toEquiv, hcard]
  haveI : Finite ↥(_root_.commutator ↥(adjointGroup .G2 k)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardD]; norm_num)
  refine ⟨Subgroup.isPerfect_iff.1 (isPerfect_of_isSimpleGroup_of_not_prime ?_), hcardD⟩
  rw [hcardD]
  norm_num

end ProductEndFourAux

theorem not_sq_dvd_ordG2_four : ¬ 6048 ^ 2 ∣ ordG2 4 := by
  rw [ProductEndFourAux.ordG2_four]
  norm_num

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

namespace ProductEndFourAux

theorem fixedGroup_mulEquiv_of_outer {e : ℕ} (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e)
    {β : MulAut (adjointGroup .G2 K)} (hβo : orderOf β = 2)
    (hβ : β ∉ inner (adjointGroup .G2 K)) :
    ∃ (k : Type) (_ : Field k), Nat.card k = 2 ^ e ∧
      Nonempty ((β.toMonoidHom.eqLocus (MonoidHom.id _) : Subgroup (adjointGroup .G2 K)) ≃*
        adjointGroup .G2 k) := by
  obtain ⟨w, -, hw⟩ := Model.exists_inner_conj_eq_of_outer hK he hβo hβ
  obtain ⟨k, hkf, hk, ⟨ε⟩⟩ := ProductEndAux.fixedGroup_fieldAut_pow_mulEquiv hK he
  set Dg : Subgroup (adjointGroup .G2 K) := β.toMonoidHom.eqLocus (MonoidHom.id _)
  have hβg : ∀ g, β g = w⁻¹ ((Model.fieldAut K ^ e) (w g)) := fun g => by
    rw [hw, MulAut.mul_apply, MulAut.mul_apply]
  have hDgiff : ∀ g, g ∈ Dg ↔ (Model.fieldAut K ^ e) (w g) = w g := fun g => by
    change β g = g ↔ _
    rw [hβg g]
    constructor
    · intro h
      have := congrArg w h
      rwa [MulAut.apply_inv_self] at this
    · intro h
      rw [h, MulAut.inv_apply_self]
  have hmap : Dg.map w.toMonoidHom =
      (Model.fieldAut K ^ e).toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hDgiff g).1 hg
    · intro hy
      refine ⟨w⁻¹ y, (hDgiff _).2 ?_, by change w (w⁻¹ y) = y; rw [MulAut.apply_inv_self]⟩
      rw [MulAut.apply_inv_self]
      exact hy
  exact ⟨k, hkf, hk, ⟨((Dg.equivMapOfInjective w.toMonoidHom w.injective).trans
    (MulEquiv.subgroupCongr hmap)).trans ε⟩⟩

theorem exists_fixedGroup_of_outer_four (hK : Nat.card K = 4)
    {β : MulAut (adjointGroup .G2 K)} (hβ2 : β * β = 1)
    (hβ : β ∉ inner (adjointGroup .G2 K)) :
    (∃ D : Subgroup (adjointGroup .G2 K), (∀ g ∈ D, β g = g) ∧ ⁅D, D⁆ = D ∧
        Nat.card D = 6048) ∧
      ∃ E : Subgroup (adjointGroup .G2 K), (∀ g ∈ E, β g = g) ∧ IsElemAbelian 2 E ∧
        Nat.card E = 2 ^ 3 := by
  have hβ1 : β ≠ 1 := fun h => hβ (h ▸ one_mem _)
  have hβo : orderOf β = 2 := orderOf_eq_prime (by rw [sq]; exact hβ2) hβ1
  obtain ⟨k, _, hk, ⟨εD⟩⟩ :=
    fixedGroup_mulEquiv_of_outer (e := 1) (by rw [hK]; norm_num) le_rfl hβo hβ
  have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
  have hkfin : Finite k := Nat.finite_of_card_ne_zero (by rw [hk2]; norm_num)
  haveI : CharP k 2 := ProductEndAux.charP_two_of_card_two_pow (by norm_num) hk
  set Dg : Subgroup (adjointGroup .G2 K) := β.toMonoidHom.eqLocus (MonoidHom.id _)
  obtain ⟨hJperf, hJcard⟩ := commutator_g2Two hk2
  obtain ⟨Ek, hEk, -, hEkcard⟩ := ProductEndAux.exists_isElemAbelian_of_mul_self (K := k)
    (a := 1) (mul_one 1)
  refine ⟨⟨((_root_.commutator ↥(adjointGroup .G2 k)).map εD.symm.toMonoidHom).map Dg.subtype,
    fun g hg => map_subtype_le _ hg, ?_, ?_⟩,
    (Ek.map εD.symm.toMonoidHom).map Dg.subtype, fun g hg => map_subtype_le _ hg,
    SectionRank.isElemAbelian_map (SectionRank.isElemAbelian_map hEk _) _, ?_⟩
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hJperf]
  · rw [card_map_of_injective Dg.subtype_injective, card_map_of_injective εD.symm.injective,
      hJcard]
  · rw [card_map_of_injective Dg.subtype_injective, card_map_of_injective εD.symm.injective,
      hEkcard, hk2]

theorem inner_or_outer_aux_four (hK : Nat.card K = 4) {β : MulAut (adjointGroup .G2 K)}
    (hβ2 : β * β = 1) :
    (∃ E : Subgroup (adjointGroup .G2 K), IsElemAbelian 2 E ∧ Nat.card E = 4 ^ 3 ∧
        ∀ g ∈ E, β g = g) ∨
      ((∃ D : Subgroup (adjointGroup .G2 K), (∀ g ∈ D, β g = g) ∧ ⁅D, D⁆ = D ∧
          Nat.card D = 6048) ∧
        ∃ E : Subgroup (adjointGroup .G2 K), (∀ g ∈ E, β g = g) ∧ IsElemAbelian 2 E ∧
          Nat.card E = 2 ^ 3) := by
  by_cases hin : β ∈ inner (adjointGroup .G2 K)
  · left
    obtain ⟨a, rfl⟩ := hin
    have ha : a * a = 1 := Model.conj_injective (by rw [map_mul, hβ2, map_one])
    obtain ⟨E, hE, haE, hcard⟩ := ProductEndAux.exists_isElemAbelian_of_mul_self ha
    refine ⟨E, hE, by rw [hcard, hK], fun g hg => ?_⟩
    haveI := hE.1
    have hc : a * g = g * a := congrArg Subtype.val (mul_comm' (⟨a, haE⟩ : E) ⟨g, hg⟩)
    rw [MulAut.conj_apply, hc, mul_inv_cancel_right]
  · exact Or.inr (exists_fixedGroup_of_outer_four hK hβ2 hin)

end ProductEndFourAux

namespace Setup

theorem inner_or_outer_G2_four (h : Setup G L f t) (d : G2Data L K) (hK4 : Nat.card K = 4)
    {X : Subgroup G} (e : L ≃* X) {x : G} (hxX : x ∈ normalizer (X : Set G)) (hx2 : x * x = 1) :
    (∃ E : Subgroup G, E ≤ X ∧ E ≤ centralizer ({x} : Set G) ∧ IsElemAbelian 2 E ∧
        Nat.card E = 4 ^ 3) ∨
      ((∃ D : Subgroup G, D ≤ X ∧ D ≤ centralizer ({x} : Set G) ∧ ⁅D, D⁆ = D ∧
          Nat.card D = 6048) ∧
        ∃ E : Subgroup G, E ≤ X ∧ E ≤ centralizer ({x} : Set G) ∧ IsElemAbelian 2 E ∧
          Nat.card E = 2 ^ 3) := by
  classical
  obtain ⟨α, hαg⟩ : ∃ α : MulAut X, ∀ a : X, ((α a : X) : G) = x * a * x⁻¹ :=
    ⟨X.normalizerMonoidHom ⟨x, hxX⟩, fun a => rfl⟩
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    change ((α (α a) : X) : G) = ((a : X) : G)
    rw [hαg, hαg]
    calc x * (x * (a : G) * x⁻¹) * x⁻¹ = (x * x) * (a : G) * (x * x)⁻¹ := by group
      _ = a := by rw [hx2, inv_one, one_mul, mul_one]
  let ψ : X ≃* adjointGroup .G2 K := e.symm.trans d.equiv
  let φ : adjointGroup .G2 K →* G := X.subtype.comp ψ.symm.toMonoidHom
  have hφinj : Function.Injective φ := Subtype.val_injective.comp ψ.symm.injective
  let β : MulAut (adjointGroup .G2 K) := MulAut.congr ψ α
  have hβ2 : β * β = 1 := by rw [← map_mul, hα2, map_one]
  have hβφ : ∀ g, φ (β g) = x * φ g * x⁻¹ := fun g => by
    change ((ψ.symm (ψ (α (ψ.symm g))) : X) : G) = x * ((ψ.symm g : X) : G) * x⁻¹
    rw [MulEquiv.symm_apply_apply, hαg]
  have hmapX : ∀ S : Subgroup (adjointGroup .G2 K), S.map φ ≤ X := by
    rintro S _ ⟨g, -, rfl⟩
    exact (ψ.symm g).2
  have hmapC : ∀ S : Subgroup (adjointGroup .G2 K), (∀ g ∈ S, β g = g) →
      S.map φ ≤ centralizer ({x} : Set G) := by
    rintro S hS _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : x * φ g * x⁻¹ = φ g := by rw [← hβφ, hS g hg]
    calc φ g * x = (x * φ g * x⁻¹) * x := by rw [h1]
      _ = x * φ g := by group
  rcases ProductEndFourAux.inner_or_outer_aux_four hK4 hβ2 with
    ⟨E₀, hE₀, hcard, hfix⟩ | ⟨⟨D₀, hfixD, hperf, hcardD⟩, E₀, hfixE, hE₀, hcardE⟩
  · refine Or.inl ⟨E₀.map φ, hmapX E₀, hmapC E₀ hfix, SectionRank.isElemAbelian_map hE₀ φ, ?_⟩
    rw [card_map_of_injective hφinj, hcard]
  · refine Or.inr ⟨⟨D₀.map φ, hmapX D₀, hmapC D₀ hfixD, ?_, ?_⟩, E₀.map φ, hmapX E₀,
      hmapC E₀ hfixE, SectionRank.isElemAbelian_map hE₀ φ, ?_⟩
    · rw [← map_commutator, hperf]
    · rw [card_map_of_injective hφinj, hcardD]
    · rw [card_map_of_injective hφinj, hcardE]

theorem false_of_normalizes_both_four (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4) {G₀ : Subgroup G} (e : G₀ ≃* L)
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G)) (g : G)
    (h₁ : t ∈ normalizer ((G₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (h₂ : t ∈ normalizer (((G₀.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom :
      Subgroup G) : Set G)) : False := by
  have htt := h.t_mul_t
  set X₁ : Subgroup G := G₀.map (MulAut.conj g).toMonoidHom with hX₁
  set X₂ : Subgroup G :=
    (G₀.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom with hX₂
  let e₁ : L ≃* X₁ := e.symm.trans
    (G₀.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  let e₂ : L ≃* X₂ := e.symm.trans
    ((G₀.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
      ((G₀.map (MulAut.conj t).toMonoidHom).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective))
  have hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hab := mem_centralizer_iff.1 (h₁₂ ⟨b, hb, rfl⟩) a ha
    change (MulAut.conj g) a * (MulAut.conj g) ((MulAut.conj t) b) =
      (MulAut.conj g) ((MulAut.conj t) b) * (MulAut.conj g) a
    rw [← map_mul, ← map_mul]
    exact congrArg (MulAut.conj g) hab
  have hinf : X₁ ⊓ X₂ = ⊥ := by
    refine le_bot_iff.1 fun z hz => ?_
    have hzc : (e₁.symm ⟨z, hz.1⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro l
      apply e₁.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (hcomm _ (e₁ l).2 z hz.2)
    rw [h.center_eq, mem_bot] at hzc
    have hz1 : (⟨z, hz.1⟩ : X₁) = 1 := by
      have := congrArg e₁ hzc
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact mem_bot.2 (congrArg Subtype.val hz1)
  have key : ∀ E₁ E₂ : Subgroup G, E₁ ≤ X₁ → E₂ ≤ X₂ → E₁ ≤ centralizer ({t} : Set G) →
      E₂ ≤ centralizer ({t} : Set G) → IsElemAbelian 2 E₁ → IsElemAbelian 2 E₂ →
      2 * 4 ^ 3 < Nat.card E₁ * Nat.card E₂ → False := by
    intro E₁ E₂ hE₁ hE₂ hE₁t hE₂t hE₁a hE₂a hlt
    have hc : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
      hcomm a (hE₁ ha) b (hE₂ hb)
    have hEinf : E₁ ⊓ E₂ = ⊥ := by
      refine le_bot_iff.1 fun z hz => ?_
      have : z ∈ X₁ ⊓ X₂ := ⟨hE₁ hz.1, hE₂ hz.2⟩
      rwa [hinf] at this
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂ hc
    rw [hEinf, Subgroup.card_bot, mul_one] at hcard
    have hEt : E₂ ≤ centralizer (E₁ : Set G) := fun b hb =>
      mem_centralizer_iff.2 fun a ha => hc a ha b hb
    have : CFSG.IsElementaryAbelian 2 E₁ := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE₁a
    have : CFSG.IsElementaryAbelian 2 E₂ := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE₂a
    have hEE : IsElemAbelian 2 (E₁ ⊔ E₂ : Subgroup G) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
        (CFSG.IsElementaryAbelian.sup_of_le_centralizer hEt)
    obtain ⟨hb1, hb2⟩ := h.card_le_of_isElemAbelian d hK (sup_le hE₁t hE₂t) hEE
    rw [hK4] at hb2
    have hle := hb1.trans (Nat.mul_le_mul_left 2 hb2)
    rw [hcard] at hle
    exact absurd hlt (not_lt.2 hle)
  rcases h.inner_or_outer_G2_four d hK4 e₁ h₁ htt with
      ⟨E₁, hE₁X, hE₁t, hE₁a, hE₁c⟩ |
        ⟨⟨D₁, hD₁X, hD₁t, hD₁p, hD₁c⟩, E₁, hE₁X, hE₁t, hE₁a, hE₁c⟩ <;>
    rcases h.inner_or_outer_G2_four d hK4 e₂ h₂ htt with
      ⟨E₂, hE₂X, hE₂t, hE₂a, hE₂c⟩ |
        ⟨⟨D₂, hD₂X, hD₂t, hD₂p, hD₂c⟩, E₂, hE₂X, hE₂t, hE₂a, hE₂c⟩
  · exact key E₁ E₂ hE₁X hE₂X hE₁t hE₂t hE₁a hE₂a (by rw [hE₁c, hE₂c]; norm_num)
  · exact key E₁ E₂ hE₁X hE₂X hE₁t hE₂t hE₁a hE₂a (by rw [hE₁c, hE₂c]; norm_num)
  · exact key E₁ E₂ hE₁X hE₂X hE₁t hE₂t hE₁a hE₂a (by rw [hE₁c, hE₂c]; norm_num)
  ·
    have hc : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb =>
      hcomm a (hD₁X ha) b (hD₂X hb)
    have hDinf : D₁ ⊓ D₂ = ⊥ := by
      refine le_bot_iff.1 fun z hz => ?_
      have : z ∈ X₁ ⊓ X₂ := ⟨hD₁X hz.1, hD₂X hz.2⟩
      rwa [hinf] at this
    have hperf : ⁅D₁ ⊔ D₂, D₁ ⊔ D₂⁆ = D₁ ⊔ D₂ :=
      le_antisymm (commutator_le_self _)
        (sup_le (hD₁p.ge.trans (commutator_mono le_sup_left le_sup_left))
          (hD₂p.ge.trans (commutator_mono le_sup_right le_sup_right)))
    have hsub : D₁ ⊔ D₂ ≤ L := h.perfect_le hperf (sup_le hD₁t hD₂t)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D₁ D₂ hc
    rw [hDinf, Subgroup.card_bot, mul_one, hD₁c, hD₂c] at hcard
    have hdvd := Subgroup.card_dvd_of_le hsub
    rw [hcard, d.card_eq_ordG2, hK4] at hdvd
    exact not_sq_dvd_ordG2_four (by rw [sq]; exact hdvd)

theorem false_of_productConfig_four (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hK4 : Nat.card K = 4) {G₀ : Subgroup G}
    (hcomm : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) [Group.IsPerfect G₀]
    (hL : (Common.diagonalHom G₀ t hcomm).range = L)
    (hN : normalizer ((yamadaR d t : Subgroup G) : Set G) ≤
      normalizer ((G₀ ⊔ G₀.map (MulAut.conj t⁻¹).toMonoidHom : Subgroup G) : Set G)) : False := by
  have := h.simple
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨-, e, -⟩ := h.yamada_7_20 hcomm hL
  haveI hLq : IsSimpleGroup (L ⧸ center L) := h.std.1.2
  have hLs : IsSimpleGroup L :=
    ((QuotientGroup.quotientMulEquivOfEq h.center_eq).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hLab : ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
    intro hc
    obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_ne_mul_of_mem_L
    exact hxy (hc x hx y hy)
  have hLeven : Even (Nat.card L) := by
    rw [d.card_eq_ordG2, hK4, ProductEndFourAux.ordG2_four]
    decide
  have hZ0 : center G₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxe : e x ∈ center L := by
      rw [mem_center_iff]
      intro l
      obtain ⟨a, rfl⟩ := e.surjective l
      rw [← map_mul, ← map_mul, mem_center_iff.1 hx a]
    rw [h.center_eq, mem_bot] at hxe
    exact mem_bot.2 (e.injective (by rw [hxe, map_one]))
  have hZ : Odd (Nat.card (center G₀)) := by
    rw [hZ0, Subgroup.card_bot]
    exact odd_one
  have hq : CFSG.Open.IsQuasisimple G₀ := by
    refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
    exact (((QuotientGroup.quotientMulEquivOfEq hZ0).trans QuotientGroup.quotientBot).trans
      e).symm.symm.isSimpleGroup
  have h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G) := by
    have h1 : G₀.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (G₀ : Set G) := by
      rw [commutator_comm] at hcomm
      exact commutator_eq_bot_iff_le_centralizer.1 hcomm
    rwa [htinv] at h1
  have hδ : ∀ x ∈ G₀, x * (t * x * t⁻¹) ∈ L := by
    intro x hx
    rw [← hL]
    exact ⟨⟨x, hx⟩, by rw [Common.diagonalHom_apply, htinv]⟩
  have hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y := by
    intro y hy
    rw [← hL] at hy
    obtain ⟨⟨x, hx⟩, hxy⟩ := hy
    refine ⟨x, hx, ?_⟩
    rw [← hxy, Common.diagonalHom_apply, htinv]
  have hLG : L ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨x, hx, rfl⟩)
  have hR : IsSylowOf 2 (yamadaR d t) (L ⊔ zpowers t) := by
    have := h.isSylowOf_yamadaR d
    rwa [h.centralizer_L_inf] at this
  have hNR : normalizer ((yamadaR d t : Subgroup G) : Set G) ≤
      normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    simpa only [htinv] using hN
  exact Common.false_of_swap_configuration h.ht hLs hLab hLeven h.L_le_centralizer
    (fun H hH hp => h.perfect_le hp hH) hq hZ h₁₂ hδ hsurj hR hNR
    (fun H hH hp => h.perfect_le_sup_of_le_normalizer d hK e hq h₁₂ hLG hH hp)
    (fun g h₁ h₂ => h.false_of_normalizes_both_four d hK hK4 e h₁₂ g h₁ h₂)

end Setup

end Local

end CFSG.LocalAnalysis.EvenBN.G2
