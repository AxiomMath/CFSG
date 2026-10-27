module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableL3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableExc

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.GH74.GLS.IVK.GHInv
  CFSG.GH74.Generic.BProg.B2.PumpupTableTwoInv CFSG.GH74.Generic.BProg.B2.PumpupTableL3
open scoped MatrixGroups commutatorElement

section ShapeComponents

variable {Y : Type} [Group Y] [Finite Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem isComponent_eq_I (S : Shape Y F₁ F₂)
    (h₁ : CFSG.IsQuasisimple ↥S.I₁ ∨ Group.IsSolvable ↥S.I₁)
    (h₂ : CFSG.IsQuasisimple ↥S.I₂ ∨ Group.IsSolvable ↥S.I₂)
    {B : Subgroup Y} (hB : CFSG.IsComponent B) : B = S.I₁ ∨ B = S.I₂ := by
  have hperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hB.1.1
  have hnt : ∃ x ∈ B, x ≠ 1 := by
    have := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥B)
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  have hnab : ¬ ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    intro hab
    have h0 : ⁅B, B⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro b hb b' hb'
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hab b hb b' hb')
    rw [hperf] at h0
    obtain ⟨x, hx, hx1⟩ := hnt
    rw [h0] at hx
    exact hx1 (Subgroup.mem_bot.1 hx)
  have aux : ∀ I : Subgroup Y, I.Normal → (CFSG.IsQuasisimple ↥I ∨ Group.IsSolvable ↥I) →
      B ≤ I → I ≤ B := by
    intro I hI hq hBI
    rcases hq with hq | hs
    · have hIc : CFSG.IsComponent I := ⟨hq, hI.isSubnormal⟩
      rcases CFSG.LocalCores.component_subnormal_subgroup hIc hB.2 with h | h
      · exact h
      · exfalso
        apply hnab
        intro b hb b' hb'
        have h3 : ⁅b', b⁆ ∈ ⁅I, B⁆ := Subgroup.commutator_mem_commutator (hBI hb') hb
        rw [h, Subgroup.mem_bot] at h3
        exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
    · exfalso
      have hsB : Group.IsSolvable ↥B :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBI)
      have hp : Group.IsPerfect ↥B := hB.1.1
      have hn : Nontrivial ↥B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
      exact Group.IsPerfect.not_isSolvable ↥B hsB
  have := normal_I₁ S
  have := normal_I₂ S
  rcases CFSG.LocalCores.component_normal_subgroup hB (normal_I₁ S) with h1 | h1
  · exact Or.inl (le_antisymm h1 (aux _ (normal_I₁ S) h₁ h1))
  rcases CFSG.LocalCores.component_normal_subgroup hB (normal_I₂ S) with h2 | h2
  · exact Or.inr (le_antisymm h2 (aux _ (normal_I₂ S) h₂ h2))
  exfalso
  have hBJ : B ≤ S.I₁ ⊔ S.I₂ := by
    have hJ : (S.I₁ ⊔ S.I₂).Normal := inferInstance
    refine le_of_perfect_of_sup_zpowers (J := S.I₁ ⊔ S.I₂) (t := S.t) ?_ hperf
    exact S.gen
  apply hnab
  intro b hb b' hb'
  have hB1 : B ≤ Subgroup.centralizer (S.I₁ : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hB2 : B ≤ Subgroup.centralizer (S.I₂ : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
  have hc : S.I₁ ⊔ S.I₂ ≤ Subgroup.centralizer ({b} : Set Y) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (hB1 hb) a ha
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (hB2 hb) a ha
  have := Subgroup.mem_centralizer_singleton_iff.1 (hc (hBJ hb'))
  exact this.symm

theorem eq_of_involutions_of_component (S : Shape Y F₁ F₂) [Finite F₁] [Finite F₂]
    (h₁ : 3 ≤ Nat.card F₁) (h₂ : 3 ≤ Nat.card F₂) (hk₁ : ringChar F₁ ≠ 2) (hk₂ : ringChar F₂ ≠ 2)
    {B : Subgroup Y} (hB : CFSG.IsComponent B) {a b : Y} (haB : a ∈ B) (hbB : b ∈ B)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have key : ∀ {F : Type} [Field F] [Finite F] (_ : ringChar F ≠ 2) {I : Subgroup Y}
      (e : ↥I ≃* SL(2, F)) (_ : a ∈ I) (_ : b ∈ I), a = b := by
    intro F _ _ hk I e haI hbI
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hk
    have hsq : ∀ x : ↥I, (x : Y) * x = 1 → (x : Y) ≠ 1 → ((e x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
      intro x hx2 hx1
      refine CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (e x) ?_ ?_
      · rw [← map_pow, pow_two]
        have : x * x = 1 := Subtype.ext hx2
        rw [this, map_one]
      · intro h1
        apply hx1
        have : x = 1 := e.injective (by rw [h1, map_one])
        rw [this]; rfl
    have ea := hsq ⟨a, haI⟩ ha2 ha1
    have eb := hsq ⟨b, hbI⟩ hb2 hb1
    have : e ⟨a, haI⟩ = e ⟨b, hbI⟩ := Subtype.ext (ea.trans eb.symm)
    exact congrArg Subtype.val (e.injective this)
  rcases isComponent_eq_I S (isQuasisimple_or_isSolvable_of_equiv_sl2 h₁ S.e₁)
    (isQuasisimple_or_isSolvable_of_equiv_sl2 h₂ S.e₂) hB with rfl | rfl
  · exact key hk₁ S.e₁ haB hbB
  · exact key hk₂ S.e₂ haB hbB

end ShapeComponents

section Leaves

theorem three_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) : 3 ≤ p ^ f := by
  have := hp.two_le
  calc 3 ≤ p := by omega
    _ ≤ p ^ f := Nat.le_self_pow (by omega) p


theorem false_of_shape_centralizer {N : Type} [Group N] [Finite N] {H L : Subgroup N} {t : N}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (hLC : IsCompIn (H ⊓ Subgroup.centralizer ({t} : Set N)) L) (htH : t ∈ H)
    (h2 : HasTwoInvolutions L)
    (S : Shape ↥(Subgroup.centralizer ({(⟨t, htH⟩ : ↥H)} : Set ↥H)) F₁ F₂)
    (h₁ : 3 ≤ Nat.card F₁) (h₂ : 3 ≤ Nat.card F₂) (hk₁ : ringChar F₁ ≠ 2) (hk₂ : ringChar F₂ ≠ 2) :
    False := by
  have hB := isCompIn_centralizer_subgroupOf htH hLC
  have hLH : L ≤ H := hLC.1.trans inf_le_left
  have hLt : ∀ c (hc : c ∈ L), (⟨c, hLH hc⟩ : ↥H) ∈
      Subgroup.centralizer ({(⟨t, htH⟩ : ↥H)} : Set ↥H) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLC.1 hc).2)
  obtain ⟨a, haL, b, hbL, ha2, hb2, ha1, hb1, hab⟩ := h2
  let aY : ↥(Subgroup.centralizer ({(⟨t, htH⟩ : ↥H)} : Set ↥H)) := ⟨⟨a, hLH haL⟩, hLt a haL⟩
  let bY : ↥(Subgroup.centralizer ({(⟨t, htH⟩ : ↥H)} : Set ↥H)) := ⟨⟨b, hLH hbL⟩, hLt b hbL⟩
  have haB : aY ∈ (L.subgroupOf H).subgroupOf (Subgroup.centralizer ({(⟨t, htH⟩ : ↥H)} : Set ↥H)) := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact haL
  have hbB : bY ∈ (L.subgroupOf H).subgroupOf (Subgroup.centralizer ({(⟨t, htH⟩ : ↥H)} : Set ↥H)) := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hbL
  have haY2 : aY * aY = 1 := Subtype.ext (Subtype.ext ha2)
  have hbY2 : bY * bY = 1 := Subtype.ext (Subtype.ext hb2)
  have haY1 : aY ≠ 1 := fun h => ha1 (congrArg (fun x : ↥(Subgroup.centralizer
    ({(⟨t, htH⟩ : ↥H)} : Set ↥H)) => ((x : ↥H) : N)) h)
  have hbY1 : bY ≠ 1 := fun h => hb1 (congrArg (fun x : ↥(Subgroup.centralizer
    ({(⟨t, htH⟩ : ↥H)} : Set ↥H)) => ((x : ↥H) : N)) h)
  have := eq_of_involutions_of_component S h₁ h₂ hk₁ hk₂ hB.2 haB hbB haY2 hbY2 haY1 hbY1
  exact hab (congrArg (fun x : ↥(Subgroup.centralizer ({(⟨t, htH⟩ : ↥H)} : Set ↥H)) =>
    ((x : ↥H) : N)) this)

section Certified


theorem pumpupIn_g2 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    PumpupEmptyIn (fun X _ => LieModel X .G2 0 p f) := by
  intro N _ _ H t L hs htH hH
  have ht2 : orderOf (⟨t, htH⟩ : ↥H) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hs.inv
  obtain ⟨F, _, _, S, hcard, -⟩ := exists_shape_G2 hp hp2 hH _ ht2
  have h3 : 3 ≤ Nat.card F := by rw [hcard]; exact three_le_pow hp hp2 hf
  have hk : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hcard
  exact false_of_shape_centralizer hs.comp htH (hasTwoInvolutions_of_shapeInCent hs) S h3 h3 hk hk

theorem pumpupIn_d4
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    PumpupEmptyIn (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro N _ _ H t L hs htH hH
  have ht2 : orderOf (⟨t, htH⟩ : ↥H) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hs.inv
  obtain ⟨F₁, F₂, _, _, _, _, S, hc₁, hc₂, -⟩ := exists_shape_D4 hp hp2 hH _ ht2
  have h3 : 3 ≤ p ^ f := three_le_pow hp hp2 hf
  have h₁ : 3 ≤ Nat.card F₁ := by
    rw [hc₁]
    calc 3 ≤ p ^ f := h3
      _ ≤ (p ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h₂ : 3 ≤ Nat.card F₂ := by rw [hc₂]; exact h3
  have hk₁ : ringChar F₁ ≠ 2 :=
    CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 (f := f * 3)
      (by rw [hc₁, ← pow_mul])
  have hk₂ : ringChar F₂ ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hc₂
  exact false_of_shape_centralizer hs.comp htH (hasTwoInvolutions_of_shapeInCent hs) S h₁ h₂ hk₁ hk₂

end Certified

end Leaves

end CFSG.GH74.Generic.BProg.B2.PumpupTableExc
