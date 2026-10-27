module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LargeExtraspecial.S12Elim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

theorem s12_isSolvable_of_isPGroup_two {H : Type*} [Group H] [Finite H] (h : IsPGroup 2 H) :
    Group.IsSolvable H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.isNilpotent
  infer_instance

theorem s12_commutator_eq_top_of_simple {H : Type*} [Group H] [IsSimpleGroup H]
    (hH : ¬ Group.IsSolvable H) : commutator H = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator H) with h | h
  · exfalso
    apply hH
    rw [← IsSimpleGroup.comm_iff_isSolvable]
    intro a b
    have hab : ⁅a, b⁆ ∈ commutator H :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
    exact hab
  · exact h

theorem s12_commutatorElement_mul_mul {X : Type*} [Group X] {a b z w : X}
    (hza : Commute z a) (hzb : Commute z b) (hwa : Commute w a) (hwb : Commute w b)
    (hzw : Commute z w) : ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have hzc : Commute z (a * b * a⁻¹ * b⁻¹) :=
    ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  have hwc : Commute w (a * b * a⁻¹ * b⁻¹) :=
    ((hwa.mul_right hwb).mul_right hwa.inv_right).mul_right hwb.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹ = z * (a * w) * b * a⁻¹ * z⁻¹ * b⁻¹ * w⁻¹ := by
        group
    _ = z * (w * a) * b * a⁻¹ * z⁻¹ * b⁻¹ * w⁻¹ := by rw [← hwa.eq]
    _ = z * w * (a * b * a⁻¹) * (z⁻¹ * b⁻¹) * w⁻¹ := by group
    _ = z * w * (a * b * a⁻¹) * (b⁻¹ * z⁻¹) * w⁻¹ := by rw [(hzb.inv_inv).eq]
    _ = (z * w) * (a * b * a⁻¹ * b⁻¹) * z⁻¹ * w⁻¹ := by group
    _ = w * (z * (a * b * a⁻¹ * b⁻¹) * z⁻¹) * w⁻¹ := by rw [hzw.eq]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hzc.eq, mul_inv_cancel_right, hwc.eq, mul_inv_cancel_right]

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_hom_simple {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {K : Subgroup S.O} (hKM : K ≤ S.Mbar)
    (hKt : ∀ c ∈ K, c * t = t * c) (hLK : S.Lbar g ≤ normalizer (K : Set S.O))
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] (hH : ¬ Group.IsSolvable H)
    (ρ : K →* H) (hρ : Function.Surjective ρ)
    (hker : ∀ k ∈ ρ.ker, ∀ x : K, k * x = x * k) : False := by
  set W := commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hW
  set K₀ := K ⊓ S.fixSub12 W with hK₀
  have hKK₀ : ∀ c ∈ K, ∀ k ∈ K₀, c * k * c⁻¹ ∈ K₀ := fun c hc k hk =>
    ⟨K.mul_mem (K.mul_mem hc hk.1) (K.inv_mem hc), conj_mem_fixSub12 (hKt c hc) hk.2⟩
  have hpow : ∀ c : K, ((c : S.O) ^ 6) ∈ K₀ := fun c => by
    have h6 := s12_pow_six_apply htA.2.2.2.1 (x := ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (fun w hw => apply_mem_commSpace_of_commute (hKt c c.2) hw)
      (fun w hw => apply_mem_commSpace_of_commute (hKt _ (K.inv_mem c.2)) hw)
    exact ⟨K.pow_mem c.2 6, fun w hw => by rw [Subgroup.coe_pow, h6 w hw]⟩
  have hcomm : ∀ {x : S.O}, x ∈ S.Lbar g → x * t = t * x := fun {x} hx =>
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨x, hx⟩ ⟨t, ht⟩)
  have hLK₀ : ∀ ℓ ∈ S.Lbar g, ∀ k ∈ K₀, ℓ * k * ℓ⁻¹ ∈ K₀ := fun ℓ hℓ k hk =>
    ⟨(mem_normalizer_iff.mp (hLK hℓ) k).mp hk.1, conj_mem_fixSub12 (hcomm hℓ) hk.2⟩
  have haW := (S.timmesfeld_12_6 haQ hne ht htA).1
  have hK₀L : ∀ k ∈ K₀, k ∈ normalizer (S.Lbar g : Set S.O) := fun k hk =>
    (mem_normalizer_Lbar_iff_fix haQ hne hn (hKM hk.1)).mpr (hk.2 _ haW)
  let K₀' : Subgroup K := K₀.subgroupOf K
  have hmemK₀ : ∀ x : K, x ∈ K₀' ↔ (x : S.O) ∈ K₀ := fun x => Subgroup.mem_subgroupOf
  have hK₀n : K₀'.Normal := by
    constructor
    intro k hk c
    rw [hmemK₀] at hk ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hKK₀ c c.2 k hk
  have hH₀ : K₀'.map ρ = ⊤ := by
    have hn' : (K₀'.map ρ).Normal := hK₀n.map ρ hρ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K₀'.map ρ) with h | h
    · exfalso
      apply hH
      refine isSolvable_of_pow_six fun x => ?_
      obtain ⟨c, rfl⟩ := hρ x
      rw [← map_pow]
      have hc : c ^ 6 ∈ K₀' := by
        rw [hmemK₀, Subgroup.coe_pow]
        exact hpow c
      have := Subgroup.mem_map_of_mem ρ hc
      rwa [h, mem_bot] at this
    · exact h
  have hE : ∀ e ∈ K₀, e ∈ S.Lbar g → ∀ he : e ∈ K, ρ ⟨e, he⟩ = 1 := by
    let E' : Subgroup K := (K₀ ⊓ S.Lbar g).subgroupOf K
    have hmemE : ∀ x : K, x ∈ E' ↔ (x : S.O) ∈ K₀ ∧ (x : S.O) ∈ S.Lbar g := fun x =>
      Subgroup.mem_subgroupOf.trans Subgroup.mem_inf
    have hEn : (E'.map ρ).Normal := by
      constructor
      intro y hy h
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
      have hmem : h ∈ K₀'.map ρ := by
        rw [hH₀]
        exact Subgroup.mem_top h
      obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hmem
      refine Subgroup.mem_map.mpr ⟨k₀ * e * k₀⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      rw [hmemE] at he ⊢
      have hk₀' : (k₀ : S.O) ∈ K₀ := (hmemK₀ k₀).mp hk₀
      refine ⟨?_, ?_⟩
      · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hKK₀ k₀ k₀.2 e he.1
      · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
          (mem_normalizer_iff.mp (hK₀L k₀ hk₀') e).mp he.2
    have hE2 : IsPGroup 2 (E'.map ρ) := by
      rintro ⟨y, hy⟩
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
      refine ⟨1, Subtype.ext ?_⟩
      have he2 : e ^ 2 = 1 := by
        have he' := ((hmemE e).mp he).2
        apply Subtype.ext
        have : IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar haQ
        simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S.Lbar g) _ he'
      simp [← map_pow, he2]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E'.map ρ) with h | h
    · intro e he hel heK
      have : ρ ⟨e, heK⟩ ∈ E'.map ρ :=
        Subgroup.mem_map_of_mem ρ ((hmemE ⟨e, heK⟩).mpr ⟨he, hel⟩)
      rwa [h, mem_bot] at this
    · exfalso
      apply hH
      refine s12_isSolvable_of_isPGroup_two fun x => ?_
      have hx : x ∈ E'.map ρ := by
        rw [h]
        exact Subgroup.mem_top x
      obtain ⟨k, hk⟩ := hE2 ⟨x, hx⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hz : ∀ ℓ ∈ S.Lbar g, ∀ k ∈ K₀, ∀ x : K,
      (ℓ * k * ℓ⁻¹ * k⁻¹) * (x : S.O) = (x : S.O) * (ℓ * k * ℓ⁻¹ * k⁻¹) := by
    intro ℓ hℓ k hk x
    have hzK₀ : ℓ * k * ℓ⁻¹ * k⁻¹ ∈ K₀ := K₀.mul_mem (hLK₀ ℓ hℓ k hk) (K₀.inv_mem hk)
    have hzL : ℓ * k * ℓ⁻¹ * k⁻¹ ∈ S.Lbar g := by
      have h1 : k * ℓ⁻¹ * k⁻¹ ∈ S.Lbar g :=
        (mem_normalizer_iff.mp (hK₀L k hk) ℓ⁻¹).mp ((S.Lbar g).inv_mem hℓ)
      have h2 := (S.Lbar g).mul_mem hℓ h1
      rwa [show ℓ * (k * ℓ⁻¹ * k⁻¹) = ℓ * k * ℓ⁻¹ * k⁻¹ by group] at h2
    have h1 := hE _ hzK₀ hzL hzK₀.1
    have := congrArg Subtype.val (hker _ (MonoidHom.mem_ker.mpr h1) x)
    simpa using this
  have hcent : ⁅K₀, K₀⁆ ≤ centralizer (S.Lbar g : Set S.O) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [mem_centralizer_iff]
    intro ℓ hℓ
    have hca : ∀ x ∈ K, Commute (ℓ * a * ℓ⁻¹ * a⁻¹) x := fun x hx => hz ℓ hℓ a ha ⟨x, hx⟩
    have hcb : ∀ x ∈ K, Commute (ℓ * b * ℓ⁻¹ * b⁻¹) x := fun x hx => hz ℓ hℓ b hb ⟨x, hx⟩
    have hzbK : ℓ * b * ℓ⁻¹ * b⁻¹ ∈ K := (K₀.mul_mem (hLK₀ ℓ hℓ b hb) (K₀.inv_mem hb)).1
    have hconj : ℓ * ⁅a, b⁆ * ℓ⁻¹ =
        ⁅(ℓ * a * ℓ⁻¹ * a⁻¹) * a, (ℓ * b * ℓ⁻¹ * b⁻¹) * b⁆ := by
      simp only [commutatorElement_def]
      group
    have hab := s12_commutatorElement_mul_mul (hca a ha.1) (hca b hb.1) (hcb a ha.1)
      (hcb b hb.1) (hca _ hzbK)
    calc ℓ * ⁅a, b⁆ = (ℓ * ⁅a, b⁆ * ℓ⁻¹) * ℓ := by group
      _ = ⁅a, b⁆ * ℓ := by rw [hconj, hab]
  have h2 : IsPGroup 2 (⁅K₀, K₀⁆ : Subgroup S.O) := by
    refine (S.timmesfeld_12_4_2 haQ hne hn).to_le ?_
    have hle : ⁅K₀, K₀⁆ ≤ K₀ := Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_def]
      exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem hx hy) (K₀.inv_mem hx)) (K₀.inv_mem hy)
    intro x hx
    exact ⟨hKM (hle hx).1, hcent hx⟩
  apply hH
  refine s12_isSolvable_of_isPGroup_two fun y => ?_
  have hyc : y ∈ (⁅K₀', K₀'⁆ : Subgroup K).map ρ := by
    rw [Subgroup.map_commutator, hH₀, ← _root_.commutator_def,
      s12_commutator_eq_top_of_simple hH]
    exact Subgroup.mem_top y
  obtain ⟨c, hc, rfl⟩ := hyc
  have hcO : (c : S.O) ∈ ⁅K₀, K₀⁆ := by
    have : (c : S.O) ∈ (⁅K₀', K₀'⁆ : Subgroup K).map K.subtype := ⟨c, hc, rfl⟩
    rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (inf_le_left : K₀ ≤ K)] at this
  obtain ⟨k, hk⟩ := h2 ⟨(c : S.O), hcO⟩
  refine ⟨k, ?_⟩
  have hck : c ^ 2 ^ k = 1 := Subtype.ext (by
    have := congrArg Subtype.val hk
    simpa using this)
  rw [← map_pow, hck, map_one]

end Setting

end CFSG.LargeExtraspecial
