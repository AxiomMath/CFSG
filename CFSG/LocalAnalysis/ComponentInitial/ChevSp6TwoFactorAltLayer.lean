module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Defs

public noncomputable section

namespace CFSG.EvenSmallLie.Child3

open Subgroup

variable {G : Type} [Group G] (C : Subgroup G) (z : G) (lev : GL (Fin 3) (ZMod 2) →* G)

theorem laya_eq (hzX : z ∈ layX C) : laya C z = (QuotientGroup.mk ⟨z, hzX⟩ : LayF C) :=
  dite_eq_left hzX

@[expose] def layLeviHom (hLX : ∀ g, lev g ∈ layX C) : GL (Fin 3) (ZMod 2) →* LayF C :=
  (layπ C).comp (lev.codRestrict (layX C) hLX)

theorem lay_centralizer_facts (hz : orderOf z = 2) (hLX : ∀ g, lev g ∈ layX C)
    (hzX : z ∈ layX C)
    (ψ : Multiplicative (ZMod 2) × GL (Fin 3) (ZMod 2) ≃*
      centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : LayF C)})
    (hψ : ∀ (s : ZMod 2) (g : GL (Fin 3) (ZMod 2)) (h : z ^ s.val * lev g ∈ layX C),
      (ψ (Multiplicative.ofAdd s, g) : LayF C) = QuotientGroup.mk ⟨_, h⟩) :
    orderOf (laya C z) = 2 ∧ Function.Injective (layLeviHom C lev hLX) ∧
      (layLeviHom C lev hLX).range = layJL C lev ∧
      layJL C lev ≤ centralizer {laya C z} ∧ zpowers (laya C z) ⊓ layJL C lev = ⊥ ∧
      zpowers (laya C z) ⊔ layJL C lev = centralizer {laya C z} := by
  rw [laya_eq C z hzX]
  set ι := layLeviHom C lev hLX
  have hι : ∀ g, ι g = QuotientGroup.mk ⟨lev g, hLX g⟩ := fun g => rfl
  have h0 : ∀ g, (ψ (1, g) : LayF C) = ι g := by
    intro g
    have h' : z ^ (0 : ZMod 2).val * lev g ∈ layX C := by
      rw [ZMod.val_zero, pow_zero, one_mul]
      exact hLX g
    have := hψ 0 g h'
    rw [ofAdd_zero] at this
    rw [this, hι]
    exact congrArg _ (Subtype.ext (by simp))
  have hpow : ∀ s : ZMod 2, (ψ (Multiplicative.ofAdd s, 1) : LayF C) =
      (QuotientGroup.mk ⟨z, hzX⟩ : LayF C) ^ s.val := by
    intro s
    have h' : z ^ s.val * lev 1 ∈ layX C := by
      rw [map_one, mul_one]
      exact pow_mem hzX _
    rw [hψ s 1 h', ← QuotientGroup.mk_pow]
    exact congrArg _ (Subtype.ext (by simp))
  have h1 : (ψ (Multiplicative.ofAdd 1, 1) : LayF C) = QuotientGroup.mk ⟨z, hzX⟩ := by
    rw [hpow, show (1 : ZMod 2).val = 1 from rfl, pow_one]
  have ha2 : (QuotientGroup.mk ⟨z, hzX⟩ : LayF C) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨z, hzX⟩ : layX C) ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, ← hz, pow_orderOf_eq_one]
      rfl)
    rw [this, QuotientGroup.mk_one]
  have ha1 : (QuotientGroup.mk ⟨z, hzX⟩ : LayF C) ≠ 1 := by
    intro h
    have hψ1 : ψ (Multiplicative.ofAdd 1, 1) = ψ 1 := by
      apply Subtype.ext
      rw [map_one ψ]
      exact h1.trans h
    have := congrArg Prod.fst (ψ.injective hψ1)
    exact absurd (ofAdd_eq_one.mp this) (by decide)
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hψ1 : ψ (1, g) = ψ 1 := by
      apply Subtype.ext
      rw [map_one ψ]
      exact (h0 g).trans hg
    exact congrArg Prod.snd (ψ.injective hψ1)
  have hrange : ι.range = layJL C lev := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨lev g, hLX g⟩, mem_subgroupOf.mpr ⟨g, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨g, hg⟩ := mem_subgroupOf.mp hy
      exact ⟨g, by rw [hι]; exact congrArg _ (Subtype.ext hg)⟩
  have hJC : layJL C lev ≤ centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : LayF C)} := by
    rw [← hrange]
    rintro _ ⟨g, rfl⟩
    rw [← h0]
    exact (ψ (1, g)).2
  refine ⟨orderOf_eq_prime ha2 ha1, hinj, hrange, hJC, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx1
    rw [SetLike.mem_coe, ← hrange] at hx2
    obtain ⟨g, hg⟩ := hx2
    have hak : (QuotientGroup.mk ⟨z, hzX⟩ : LayF C) ^ k =
        (ψ ((Multiplicative.ofAdd (1 : ZMod 2), 1) ^ k) : LayF C) := by
      rw [map_zpow, SubgroupClass.coe_zpow, h1]
    have hψk : ψ ((Multiplicative.ofAdd (1 : ZMod 2), 1) ^ k) = ψ (1, g) :=
      Subtype.ext (by rw [← hak, h0, hg])
    have hg1 : g = 1 := (congrArg Prod.snd (ψ.injective hψk)).symm.trans (_root_.one_zpow k)
    rw [mem_bot, ← hg, hg1, map_one ι]
  · apply le_antisymm
    · exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) hJC
    · intro c hc
      obtain ⟨⟨s, g⟩, hp⟩ := ψ.surjective ⟨c, hc⟩
      have hc' : (⟨c, hc⟩ : ↥(centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : LayF C)})) =
          ψ (s, 1) * ψ (1, g) := by
        rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, hp]
      have hc'' : c = (ψ (s, 1) : LayF C) * ψ (1, g) := congrArg Subtype.val hc'
      rw [hc'', h0]
      refine mul_mem_sup ?_ (by rw [← hrange]; exact ⟨g, rfl⟩)
      obtain ⟨t, rfl⟩ : ∃ t : ZMod 2, Multiplicative.ofAdd t = s := ⟨s.toAdd, rfl⟩
      rw [hpow]
      exact pow_mem (mem_zpowers _) _

@[expose] def layK : Subgroup G :=
  (CFSG.oddCore (centralizer (C : Set G))).map (centralizer (C : Set G)).subtype

@[expose] def layKBar : Subgroup (LayF C) := ((layK C).subgroupOf (layX C)).map (layπ C)

theorem lay_kernel_facts [Finite G] (hK₃ : Odd (Nat.card (layK C)))
    (hK₄ : ∀ g ∈ layX C, ∀ k ∈ layK C, g * k * g⁻¹ ∈ layK C)
    (κ : layX C →* MulAut C)
    (hκ₁ : ∀ (x : layX C) (c : C), ((κ x c : C) : G) = x * c * (x : G)⁻¹)
    (hκ₂ : κ.ker = (C ⊔ layK C).subgroupOf (layX C)) :
    layKBar C ≤ layRo C ∧
    ∃ κF : LayF C →* MulAut C,
      (∀ (x : layX C) (c : C), ((κF (layπ C x) c : C) : G) = x * c * (x : G)⁻¹) ∧
      κF.ker = layKBar C := by
  have hCX : C ≤ layX C := le_normalizer
  have hKX : layK C ≤ layX C :=
    (map_subtype_le _).trans (centralizer_le_normalizer _)
  have hker : (layπ C).ker = C.subgroupOf (layX C) := QuotientGroup.ker_mk' _
  have hKn : ((layK C).subgroupOf (layX C)).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hK₄ g g.2 n hn⟩
  have hKBn : (layKBar C).Normal := hKn.map _ (QuotientGroup.mk'_surjective _)
  have hmapC : (C.subgroupOf (layX C)).map (layπ C) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr hker.ge
  have hmapCK : ((C ⊔ layK C).subgroupOf (layX C)).map (layπ C) = layKBar C := by
    rw [subgroupOf_sup hCX hKX, Subgroup.map_sup, hmapC, bot_sup_eq]
    rfl
  have hKBodd : Nat.Coprime 2 (Nat.card (layKBar C)) := by
    rw [Nat.coprime_two_left]
    refine Odd.of_dvd_nat ?_ (card_map_dvd _ _)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKX).toEquiv]
  have hKBR : layKBar C ≤ layRo C := le_sSup ⟨hKBn, hKBodd⟩
  have hCK : C.subgroupOf (layX C) ≤ (C ⊔ layK C).subgroupOf (layX C) :=
    subgroupOf_mono _ le_sup_left
  have hκC : C.subgroupOf (layX C) ≤ κ.ker := hκ₂ ▸ hCK
  have hκF : (QuotientGroup.lift _ κ hκC).ker = layKBar C := by
    rw [QuotientGroup.ker_lift, hκ₂]
    exact hmapCK
  exact ⟨hKBR, QuotientGroup.lift _ κ hκC, fun x c => hκ₁ x c, hκF⟩

end CFSG.EvenSmallLie.Child3
