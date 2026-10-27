module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveBarTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveConj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped Pointwise

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal

open SectionSix

namespace SixTools

section Abstract

variable {X : Type} [Group X]

theorem mem_zpowers_of_sq {a x : X} (ha : a ^ 2 = 1) (hx : x ∈ Subgroup.zpowers a) :
    x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨t, ht | ht⟩ := Int.even_or_odd' k
  · left
    rw [ht, zpow_mul, show a ^ (2 : ℤ) = 1 by rw [zpow_ofNat]; exact ha, one_zpow]
  · right
    rw [ht, zpow_add, zpow_mul, show a ^ (2 : ℤ) = 1 by rw [zpow_ofNat]; exact ha, one_zpow,
      one_mul, zpow_one]

theorem mem_sup_of_commute {Y Z : Subgroup X} (hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y * z = z * y)
    {x : X} (hx : x ∈ Y ⊔ Z) : ∃ y ∈ Y, ∃ z ∈ Z, x = y * z := by
  have hZN : Z ≤ Subgroup.normalizer (Y : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hy => hYZ y hy z hz
  have hx' : x ∈ ((Y ⊔ Z : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y Z hZN] at hx'
  obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp hx'
  exact ⟨y, hy, z, hz, hyz.symm⟩

theorem sq_eq_one_of_mem_sup {Y Z : Subgroup X} (hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y * z = z * y)
    (hY : ∀ y ∈ Y, y ^ 2 = 1) (hZ : ∀ z ∈ Z, z ^ 2 = 1) {x : X} (hx : x ∈ Y ⊔ Z) :
    x ^ 2 = 1 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_of_commute hYZ hx
  rw [(show Commute y z from hYZ y hy z hz).mul_pow, hY y hy, hZ z hz, one_mul]

variable [Finite X]

theorem card_sup_zpowers {a b : X} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) :
    Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup X) = 4 := by
  have hcomm : ∀ y ∈ Subgroup.zpowers a, ∀ z ∈ Subgroup.zpowers b, y * z = z * y := by
    intro y hy z hz
    rcases mem_zpowers_of_sq ha hy with rfl | rfl <;>
      rcases mem_zpowers_of_sq hb hz with rfl | rfl <;> simp [hc]
  have hN : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hy => hcomm y hy z hz
  have hbot : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxb⟩
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_of_sq ha hxa with h | h
    · exact h
    · rcases mem_zpowers_of_sq hb hxb with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hab
  rw [AschbacherTheorem3.card_sup_of_le_normalizer hN hbot, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_eq_prime ha ha1, orderOf_eq_prime hb hb1]

theorem elemAbelian_eight {a b c : X} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hcab : a * b = b * a) (hcac : a * c = c * a)
    (hcbc : b * c = c * b) (hcE : c ∉ ({1, a, b, a * b} : Set X)) :
    IsElemAbelian 2 ((Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers c) ∧
      Nat.card ((Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers c :
        Subgroup X) = 8 := by
  set E₂ := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hE₂def
  have hcomm₂ : ∀ y ∈ Subgroup.zpowers a, ∀ z ∈ Subgroup.zpowers b, y * z = z * y := by
    intro y hy z hz
    rcases mem_zpowers_of_sq ha hy with rfl | rfl <;>
      rcases mem_zpowers_of_sq hb hz with rfl | rfl <;> simp [hcab]
  have hmemE₂ : ∀ x ∈ E₂, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_of_commute hcomm₂ hx
    rcases mem_zpowers_of_sq ha hy with rfl | rfl <;>
      rcases mem_zpowers_of_sq hb hz with rfl | rfl <;> simp
  have hc1 : c ≠ 1 := fun h => hcE (by simp [h])
  have hcommE : ∀ y ∈ E₂, ∀ z ∈ Subgroup.zpowers c, y * z = z * y := by
    intro y hy z hz
    rcases mem_zpowers_of_sq hc hz with h | h
    · rw [h]; simp
    · rw [h]
      rcases hmemE₂ y hy with rfl | rfl | rfl | rfl
      · simp
      · exact hcac
      · exact hcbc
      · calc a * b * c = a * (b * c) := by group
          _ = a * (c * b) := by rw [hcbc]
          _ = (a * c) * b := by group
          _ = c * a * b := by rw [hcac]
          _ = c * (a * b) := by group
  have hsqE₂ : ∀ x ∈ E₂, x ^ 2 = 1 := fun x hx =>
    sq_eq_one_of_mem_sup hcomm₂ (fun y hy => by
      rcases mem_zpowers_of_sq ha hy with rfl | rfl <;> simp [ha])
      (fun z hz => by rcases mem_zpowers_of_sq hb hz with rfl | rfl <;> simp [hb]) hx
  refine ⟨TwoGroups.isElemAbelian_of_sq fun x hx => sq_eq_one_of_mem_sup hcommE hsqE₂
    (fun z hz => by rcases mem_zpowers_of_sq hc hz with h | h <;> rw [h] <;> simp [hc]) hx, ?_⟩
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer (E₂ : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hy => hcommE y hy z hz
  have hbot : E₂ ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxc⟩
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_of_sq hc hxc with h | h
    · exact h
    · exfalso
      apply hcE
      rw [← h]
      rcases hmemE₂ x hxE with h' | h' | h' | h' <;> simp [h']
  rw [AschbacherTheorem3.card_sup_of_le_normalizer hN hbot,
    card_sup_zpowers ha hb ha1 hb1 hab hcab, Nat.card_zpowers, orderOf_eq_prime hc hc1]

end Abstract

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem index_eq_of_preimage_eq (hyp : Hyp61 G D r Abar) {k l : Fin r}
    (h : aschbacherThm5Preimage D (Abar k) = aschbacherThm5Preimage D (Abar l)) : k = l := by
  apply hyp.hdistinct
  apply Subgroup.map_injective (quotientEmbedding_injective D)
  rw [map_quotientEmbedding, map_quotientEmbedding, h]

theorem mem_normalizer_of_fusion_conj (hC : Counterexample G D r Abar) {g y : G}
    (hy2 : ∃ n : ℕ, y ^ 2 ^ n = 1) (hy1 : y ≠ 1) {k m : Fin r}
    (hyk : aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar k)) y)
    (hym : aschbacherThm5Centralizes (aschbacherThm5Core (rightConjugate D g))
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)) y) :
    g ∈ Subgroup.normalizer (D : Set G) := by
  have hti := (centralizes_conj_iff D Abar g m y).mp hym
  obtain ⟨n, hn⟩ := hy2
  refine mem_normalizer_of_fusion hC m k (t := g * y * g⁻¹) ⟨n, ?_⟩ ?_ hti ?_
  · rw [conj_pow, hn]
    group
  · intro h
    apply hy1
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group]

theorem mul_mem_normalizer_of_two {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}
    (hyp : Hyp61 G D 2 Abar) {x y : G} (hx : x ∈ Subgroup.normalizer (D : Set G))
    (hy : y ∈ Subgroup.normalizer (D : Set G))
    (hxA : x ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar 0) : Set G))
    (hyA : y ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar 0) : Set G)) :
    x * y ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar 0) : Set G) := by
  have hmove : ∀ z ∈ Subgroup.normalizer (D : Set G),
      z ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar 0) : Set G) →
      (aschbacherThm5Preimage D (Abar 0)).map (MulAut.conj z).toMonoidHom =
        aschbacherThm5Preimage D (Abar 1) ∧
      (aschbacherThm5Preimage D (Abar 1)).map (MulAut.conj z).toMonoidHom =
        aschbacherThm5Preimage D (Abar 0) := by
    intro z hz hzA
    obtain ⟨l, hl⟩ := hyp.hperm z hz 0
    obtain ⟨l', hl'⟩ := hyp.hperm z hz 1
    have hl1 : l = 1 := by
      rcases (show l = 0 ∨ l = 1 by omega) with h | h
      · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (h ▸ hl)) hzA
      · exact h
    have hl'0 : l' = 0 := by
      rcases (show l' = 0 ∨ l' = 1 by omega) with h | h
      · exact h
      · exfalso
        have h01 : aschbacherThm5Preimage D (Abar 0) = aschbacherThm5Preimage D (Abar 1) := by
          apply Subgroup.map_injective (f := (MulAut.conj z).toMonoidHom) (MulAut.conj z).injective
          rw [hl, hl', hl1, h]
        exact absurd (index_eq_of_preimage_eq hyp h01) (show (0 : Fin 2) ≠ 1 by decide)
    exact ⟨hl1 ▸ hl, hl'0 ▸ hl'⟩
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  calc (aschbacherThm5Preimage D (Abar 0)).map (MulAut.conj (x * y)).toMonoidHom =
        ((aschbacherThm5Preimage D (Abar 0)).map (MulAut.conj y).toMonoidHom).map
          (MulAut.conj x).toMonoidHom := by
        rw [Subgroup.map_map, map_mul]
        rfl
    _ = (aschbacherThm5Preimage D (Abar 1)).map (MulAut.conj x).toMonoidHom := by
        rw [(hmove y hy hyA).1]
    _ = aschbacherThm5Preimage D (Abar 0) := (hmove x hx hxA).2

@[expose] noncomputable def factorMap (hyp : Hyp61 G D r Abar)
    (h : Subgroup.normalizer (D : Set G)) (k : Fin r) : Fin r :=
  Classical.choose (hyp.hperm h h.2 k)

theorem factorMap_spec (hyp : Hyp61 G D r Abar) (h : Subgroup.normalizer (D : Set G))
    (k : Fin r) :
    (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (h : G)).toMonoidHom =
      aschbacherThm5Preimage D (Abar (factorMap hyp h k)) :=
  Classical.choose_spec (hyp.hperm h h.2 k)

theorem factorMap_unique (hyp : Hyp61 G D r Abar) (h : Subgroup.normalizer (D : Set G))
    {k l : Fin r}
    (hl : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (h : G)).toMonoidHom =
      aschbacherThm5Preimage D (Abar l)) : factorMap hyp h k = l :=
  index_eq_of_preimage_eq hyp ((factorMap_spec hyp h k).symm.trans hl)

@[expose, instance_reducible] noncomputable def factorAction (hyp : Hyp61 G D r Abar) :
    MulAction (Subgroup.normalizer (D : Set G)) (Fin r) where
  smul h k := factorMap hyp h k
  one_smul k := factorMap_unique hyp 1 (by
    change (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (1 : G)).toMonoidHom = _
    rw [map_one]
    exact Subgroup.map_id _)
  mul_smul h₁ h₂ k := factorMap_unique hyp (h₁ * h₂) (by
    change (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj ((h₁ : G) * h₂)).toMonoidHom = _
    rw [show (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj ((h₁ : G) * h₂)).toMonoidHom =
        ((aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (h₂ : G)).toMonoidHom).map
          (MulAut.conj (h₁ : G)).toMonoidHom by rw [Subgroup.map_map, map_mul]; rfl,
      factorMap_spec hyp h₂ k, factorMap_spec hyp h₁]
    rfl)

theorem exists_fixed_factor (hyp : Hyp61 G D r Abar) (hr : Odd r) {Y : Subgroup G}
    (hYH : Y ≤ Subgroup.normalizer (D : Set G)) (hY2 : IsPGroup 2 Y) :
    ∃ m : Fin r, Y ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar m) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction (Subgroup.normalizer (D : Set G)) (Fin r) := factorAction hyp
  let : MulAction Y (Fin r) := MulAction.compHom _ (Subgroup.inclusion hYH)
  have hndvd : ¬ 2 ∣ Nat.card (Fin r) := by
    rw [Nat.card_fin]
    exact fun h => (Nat.not_even_iff_odd.mpr hr) (even_iff_two_dvd.mpr h)
  obtain ⟨m, hm⟩ := hY2.nonempty_fixed_point_of_prime_not_dvd_card (Fin r) hndvd
  refine ⟨m, fun y hy => ?_⟩
  have hfix : factorMap hyp ⟨y, hYH hy⟩ m = m := hm ⟨y, hy⟩
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have h1 := factorMap_spec hyp ⟨y, hYH hy⟩ m
  rw [hfix] at h1
  exact h1

theorem exists_lift_involution {W : Subgroup G} (hWH : W ≤ Subgroup.normalizer (D : Set G))
    {t : Bar D} (htW : t ∈ bar D W) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ s : Subgroup.normalizer (D : Set G), (s : G) ∈ W ∧ orderOf (s : G) = 2 ∧ toBar D s = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hzp := AschbacherToolkit.isPGroup_zpowers_of_orderOf_eq_two ho
  obtain ⟨V, hVW, hV2, hVt⟩ :=
    SectionSix.BarTools.lift_two_subgroup hWH hzp (Subgroup.zpowers_le.mpr htW)
  have htV : t ∈ bar D V := hVt ▸ Subgroup.mem_zpowers t
  obtain ⟨s, hsV, hst⟩ := (mem_bar_iff D V t).mp htV
  have hs2 : s ^ 2 = 1 := by
    apply toBar_injOn_of_isPGroup hV2 (V.pow_mem hsV 2) V.one_mem
    rw [map_pow, hst, ht2, map_one]
  have hs1 : (s : G) ≠ 1 := by
    intro h
    rw [show s = 1 from Subtype.ext h, map_one] at hst
    exact ht1 hst.symm
  refine ⟨s, hVW hsV, orderOf_eq_prime ?_ hs1, hst⟩
  have := congrArg Subtype.val hs2
  simpa using this

end SixTools

end DeltaLocal

end CFSG.ComponentClassification.AschbacherTheorem5
