module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Statements
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Sec8B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Base G t L S z g B → z ∈ B ∧ ∀ b ∈ B, b ≠ 1 → b ∈ conjClassIn L z

private theorem sec8_t_mem_sylow {G : Type} [Group G] [Finite G] {t : G} {S : Subgroup G}
    (hSyl : IsSylow2Of S (centralizer ({t} : Set G))) (ht : orderOf t = 2) : t ∈ S := by
  have hpS : IsPGroup 2 S := hSyl.2.1
  have hzt2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have htcentS : t ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSyl.1 hy)
  have hztN : zpowers t ≤ normalizer (S : Set G) := by
    rw [zpowers_le]
    exact Subgroup.centralizer_le_normalizer (S : Set G) htcentS
  have hQ2 : IsPGroup 2 (S ⊔ zpowers t : Subgroup G) := hpS.to_sup_of_normal_left' hzt2 hztN
  have hQle : S ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le hSyl.1 (zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have hQS : S ⊔ zpowers t = S := IsSylow2Of.eq_of_le hSyl hQle hQ2 le_sup_left
  have htQ : t ∈ (S ⊔ zpowers t : Subgroup G) := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  rwa [hQS] at htQ

private theorem sec8_mem_sup {G : Type} [Group G] {t : G} {B : Subgroup G} (ht2 : t * t = 1)
    (hcomm : ∀ b ∈ B, b * t = t * b) {y : G} (hy : y ∈ (zpowers t ⊔ B : Subgroup G)) :
    y ∈ B ∨ ∃ b ∈ B, y = t * b := by
  let S : Subgroup G :=
    { carrier := {y | y ∈ B ∨ ∃ b ∈ B, y = t * b}
      one_mem' := Or.inl B.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨a', ha', rfl⟩) (hb | ⟨b', hb', rfl⟩)
        · exact Or.inl (B.mul_mem ha hb)
        · exact Or.inr ⟨a * b', B.mul_mem ha hb',
            by rw [← mul_assoc a t, hcomm a ha]; group⟩
        · exact Or.inr ⟨a' * b, B.mul_mem ha' hb, by group⟩
        · refine Or.inl ?_
          rw [show (t * a') * (t * b') = a' * b' by
            calc (t * a') * (t * b') = (t * (a' * t)) * b' := by group
              _ = (t * (t * a')) * b' := by rw [hcomm a' ha']
              _ = (t * t) * (a' * b') := by group
              _ = a' * b' := by rw [ht2, one_mul]]
          exact B.mul_mem ha' hb'
      inv_mem' := by
        rintro a (ha | ⟨a', ha', rfl⟩)
        · exact Or.inl (B.inv_mem ha)
        · refine Or.inr ⟨a'⁻¹, B.inv_mem ha', ?_⟩
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, hcomm a'⁻¹ (B.inv_mem ha')] }
  have hle : (zpowers t ⊔ B : Subgroup G) ≤ S := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact Or.inr ⟨1, B.one_mem, (mul_one t).symm⟩
    · intro b hb
      exact Or.inl hb
  exact hle hy

theorem asc82Lemma86_of (h68 : Asc82Lemma68) (h85 : Asc82Lemma85) (hB : Asc82Sec8B) :
    Asc82Lemma86 := by
  intro G _ _ t L S z g B hctx
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hzB : z ∈ B := (hB G t L S z g B hctx.toSec8Base).1
  have hz2 : orderOf z = 2 := hctx.pocket.1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hne : g⁻¹ * t * g ≠ t := by
    intro h
    have htz : t * z = t := by rw [← hctx.tz, h]
    exact hz1 (mul_left_cancel (a := t) (by rw [htz, mul_one]))
  have hmem : g⁻¹ * t * g ∈ cosetSet t B := by
    rw [hctx.tz]
    exact ⟨z, hzB, rfl⟩
  have h85c : S ⊓ L = S ⊓ CFSG.conjugate L g := h85 G t L S z g B hctx
  have hBg : B ≤ CFSG.conjugate L g := fun x hx => by
    have hx' : x ∈ S ⊓ L := ⟨(hctx.B_le hx).2, (hctx.B_le hx).1⟩
    rw [h85c] at hx'
    exact hx'.2
  have h68res := h68 G t L hS hctx.omega6m B hctx.B_e16 (fun x hx => (hctx.B_le hx).1)
    g hne hmem hBg
  have hsyl : IsSylow2Of (zpowers t) (centralizer (L : Set G)) := h68res.1
  have htS : t ∈ S := sec8_t_mem_sylow hctx.sylow hS.involution
  refine IsSylow2Of.eq_of_le hsyl inf_le_right ?_ ?_
  · exact hctx.sylow.2.1.to_le inf_le_left
  · rw [zpowers_le]
    exact ⟨htS, hsyl.1 (Subgroup.mem_zpowers t)⟩

theorem asc82Lemma8B_of (h68 : Asc82Lemma68) (h84 : Asc82Lemma84Z) (h85 : Asc82Lemma85)
    (hB : Asc82Sec8B) : Asc82Lemma8B := by
  intro G _ _ t L S z g B hctx
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hzB : z ∈ B := (hB G t L S z g B hctx.toSec8Base).1
  have hB1 : ∀ b ∈ B, b ≠ 1 → b ∈ conjClassIn L z :=
    (hB G t L S z g B hctx.toSec8Base).2
  have hz2 : orderOf z = 2 := hctx.pocket.1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hne : g⁻¹ * t * g ≠ t := by
    intro h
    have htz : t * z = t := by rw [← hctx.tz, h]
    exact hz1 (mul_left_cancel (a := t) (by rw [htz, mul_one]))
  have hmem : g⁻¹ * t * g ∈ cosetSet t B := by
    rw [hctx.tz]
    exact ⟨z, hzB, rfl⟩
  have h85c : S ⊓ L = S ⊓ CFSG.conjugate L g := h85 G t L S z g B hctx
  have hBg : B ≤ CFSG.conjugate L g := fun x hx => by
    have hx' : x ∈ S ⊓ L := ⟨(hctx.B_le hx).2, (hctx.B_le hx).1⟩
    rw [h85c] at hx'
    exact hx'.2
  have h68res := h68 G t L hS hctx.omega6m B hctx.B_e16 (fun x hx => (hctx.B_le hx).1)
    g hne hmem hBg
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.involution, pow_orderOf_eq_one]
  have hcommB : ∀ b ∈ B, b * t = t * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le (hctx.B_le hb).1)
  refine ⟨?_, ?_⟩
  · simpa only [Nsub8, Asub8] using h68res.2
  · ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨?_, ?_⟩
      · by_cases hb1 : b = 1
        · simpa [hb1] using IsConj.refl t
        · obtain ⟨l, hlL, hlb⟩ := hB1 b hb hb1
          have hlt : l * t = t * l :=
            Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hlL)
          have htz : IsConj t (t * z) := isConj_iff.mpr ⟨g⁻¹, by simpa using hctx.tz⟩
          have hstep : l * (t * z) * l⁻¹ = t * (l * z * l⁻¹) := by
            have h1 : l * (t * z) * l⁻¹ = (l * t) * z * l⁻¹ := by group
            rw [h1, hlt]
            group
          have hstep' : IsConj (t * z) (t * b) := by
            rw [hlb]
            exact isConj_iff.mpr ⟨l, hstep⟩
          exact IsConj.trans htz hstep'
      · rw [Asub8]
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers t) hb
    · rintro ⟨hxconj, hxA⟩
      have hxA' : x ∈ (zpowers t ⊔ B : Subgroup G) := hxA
      rcases sec8_mem_sup ht2 hcommB hxA' with hxB | ⟨b, hb, hxb⟩
      · exfalso
        have hxt : IsConj x t := IsConj.symm hxconj
        obtain ⟨c, hc⟩ := hxconj
        have hx2 : orderOf x = 2 := by
          have h := (SemiconjBy.orderOf_eq (c : G) hc).symm
          rwa [hS.involution] at h
        have hx1 : x ≠ 1 := by
          intro h
          rw [h, orderOf_one] at hx2
          omega
        obtain ⟨l, hlL, hlx⟩ := hB1 x hxB hx1
        have hzx : IsConj z x := isConj_iff.mpr ⟨l, by rw [hlx]⟩
        have hzt : IsConj z t := IsConj.trans hzx hxt
        have htmem : t ∈ conjClassIn L z := by
          have htinf : t ∈ {y : G | IsConj z y} ∩ (centralizer ({t} : Set G) : Set G) :=
            ⟨hzt, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
          rwa [h84 G t L S z g B hctx] at htinf
        obtain ⟨l', hl'L, hl't⟩ := htmem
        have hl't_comm : l' * t = t * l' :=
          Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hl'L)
        have hzt_eq : z = t := by
          have hz_eq : z = l'⁻¹ * t * l' := by rw [hl't]; group
          rw [hz_eq]
          calc l'⁻¹ * t * l' = l'⁻¹ * (t * l') := by group
            _ = l'⁻¹ * (l' * t) := by rw [← hl't_comm]
            _ = t := by group
        have hg1 : g⁻¹ * t * g = 1 := by rw [hctx.tz, hzt_eq, ht2]
        have ht1 : t = 1 := by
          have h : g⁻¹ * t = g⁻¹ := by
            calc g⁻¹ * t = g⁻¹ * t * g * g⁻¹ := by group
              _ = 1 * g⁻¹ := by rw [hg1]
              _ = g⁻¹ := by rw [one_mul]
          exact mul_left_cancel (a := g⁻¹) (by simpa using h)
        have h2 : orderOf t = 2 := hS.involution
        have h1 : orderOf t = 1 := by rw [ht1, orderOf_one]
        omega
      · exact ⟨b, hb, hxb⟩

end CFSG.OddStandard.SmallF3.Omega
