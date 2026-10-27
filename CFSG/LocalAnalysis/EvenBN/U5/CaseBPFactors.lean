module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3EThree

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups commutatorElement

section Sec52FacGeneric

variable {G : Type} [Group G]

def sec52FacFst (A B E : Subgroup G) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Subgroup G where
  carrier := {a | a ∈ A ∧ ∃ b ∈ B, a * b ∈ E}
  one_mem' := ⟨one_mem _, 1, one_mem _, by simpa using one_mem E⟩
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
    refine ⟨mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
    have e : a * a' * (b * b') = (a * b) * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [hAB a' ha' b hb]
        _ = (a * b) * (a' * b') := by group
    rw [e]
    exact mul_mem hab hab'
  inv_mem' := by
    rintro a ⟨ha, b, hb, hab⟩
    refine ⟨inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
    have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
      rw [mul_inv_rev, hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)]
    rw [e]
    exact inv_mem hab

theorem sec52FacFst_le {A B E : Subgroup G} {hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a} :
    sec52FacFst A B E hAB ≤ A := fun _ hx => hx.1

theorem sec52FacFst_sq [Finite G] {A B E V₁ V₂ : Subgroup G} {hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a}
    (hinf : A ⊓ B = ⊥) (hV₁ : V₁ ≤ A) (hV₂ : V₂ ≤ B) (hE : ∀ x ∈ E, x * x ∈ V₁ ⊔ V₂) :
    ∀ x ∈ sec52FacFst A B E hAB, x * x ∈ V₁ := by
  rintro x ⟨hxA, b, hbB, hxb⟩
  obtain ⟨v₁, hv₁, v₂, hv₂, e⟩ := exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => hAB x (hV₁ hx) y (hV₂ hy)) (hE _ hxb)
  have e2 : (x * b) * (x * b) = (x * x) * (b * b) := by
    calc (x * b) * (x * b) = x * (b * x) * b := by group
      _ = x * (x * b) * b := by rw [hAB x hxA b hbB]
      _ = (x * x) * (b * b) := by group
  rw [e2] at e
  have := (eq_of_mul_eq_mul_of_inf_eq_bot hinf (mul_mem hxA hxA) (hV₁ hv₁) (mul_mem hbB hbB)
    (hV₂ hv₂) e).1
  rw [this]
  exact hv₁

theorem sec52Fac_elemAbMod_of_sq {N E : Subgroup G} (hcen : ∀ n ∈ N, ∀ g ∈ E, n * g = g * n)
    (hsq : ∀ x ∈ E, x * x ∈ N) : ElemAbMod N E := by
  refine ⟨hsq, fun x hx y hy => ?_⟩
  have hx2 := hsq x hx
  have hy2 := hsq y hy
  have hxy2 := hsq _ (mul_mem hx hy)
  have e : ⁅x, y⁆ = (x * y) * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by
    have k : y⁻¹ * (x * x)⁻¹ = (x * x)⁻¹ * y⁻¹ := (hcen _ (inv_mem hx2) _ (inv_mem hy)).symm
    rw [commutatorElement_def]
    calc x * y * x⁻¹ * y⁻¹ = (x * y) * (x * y) * (y⁻¹ * (x * x)⁻¹) * y⁻¹ := by group
      _ = (x * y) * (x * y) * ((x * x)⁻¹ * y⁻¹) * y⁻¹ := by rw [k]
      _ = (x * y) * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hxy2 (inv_mem hx2)) (inv_mem hy2)

end Sec52FacGeneric

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

theorem sec52Fac_δ_mem_Zp (hB : d.CaseBHyp) (c : d.CaseBData) (h11 : Sec52Sylow hB c)
    {x : c.Kc} (hx : (x : G) ∈ CFSG.centerIn c.Qc) : c.δ hB x ∈ d.Zp := by
  have hxQ : (x : G) ∈ c.Qc := hx.1
  have hxP : c.δ hB x ∈ d.P := by
    rw [← h11.map_δ]
    exact ⟨x, hxQ, rfl⟩
  rw [← d.sec2_2_three.2.2.2.2]
  refine ⟨hxP, mem_centralizer_iff.2 fun p hp => ?_⟩
  rw [SetLike.mem_coe, ← h11.map_δ] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.1 hx.2 q hq)

theorem sec52Fac_δ_image (hB : d.CaseBHyp) (c : d.CaseBData) (h11 : Sec52Sylow hB c)
    {X : Subgroup G} (hXQ : X ≤ c.Qc) (hE : ElemAbMod (CFSG.centerIn c.Qc) X) :
    (X.subgroupOf c.Kc).map (c.δ hB) ≤ d.P ∧
      ElemAbMod d.Zp ((X.subgroupOf c.Kc).map (c.δ hB)) ∧
      Nat.card ((X.subgroupOf c.Kc).map (c.δ hB)) = Nat.card X := by
  have hXK : X ≤ c.Kc := hXQ.trans inf_le_right
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · rw [← h11.map_δ]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hXQ)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    exact sec52Fac_δ_mem_Zp hB c h11 (hE.1 x hx)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_commutatorElement]
    exact sec52Fac_δ_mem_Zp hB c h11 (hE.2 x hx y hy)
  · rw [Subgroup.card_map_of_injective (c.injective_δ hB)]
    exact Nat.card_congr (subgroupOfEquivOfLe hXK).toEquiv

theorem sec52_factors (hB : d.CaseBHyp) (c : d.CaseBData) (h11 : CaseBData.Sec52Sylow hB c) :
    CaseBData.Sec52Factors hB c := by
  have hd : d.Hyp := hB.hyp
  have hττ : ∀ x : G, (MulAut.conj d.t).toMonoidHom ((MulAut.conj d.t).toMonoidHom x) = x := by
    intro x
    change d.t * (d.t * x * d.t⁻¹) * d.t⁻¹ = x
    rw [hd.t_inv']
    calc d.t * (d.t * x * d.t) * d.t = (d.t * d.t) * x * (d.t * d.t) := by group
      _ = x := by rw [hd.t_mul_t, one_mul, mul_one]
  have hES : d.E ≤ c.S := c.E_le_S hB
  have hEt : d.E.map (MulAut.conj d.t).toMonoidHom = d.E :=
    map_conj_eq_of_mem_normalizer (hd.t_mem_normalizer_E_caseB hB.gms)
  have hQK : c.Qc ≤ c.Kc := inf_le_right
  have hQtK : c.Qt ≤ c.Kt := Subgroup.map_mono hQK
  have hcomm : ∀ a ∈ c.Qc, ∀ b ∈ c.Qt, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (c.Kt_le_centralizer_Kc hB (hQtK hb)) a (hQK ha)
  have hinf : c.Qc ⊓ c.Qt = ⊥ := le_bot_iff.1 ((inf_le_inf hQK hQtK).trans (c.Kc_inf_Kt hB).le)
  have hEab : ElemAbMod d.V d.E := hd.elemAbMod_V_E hB.gms
  have hEcard : Nat.card d.E = (2 ^ f) ^ 14 := hd.card_E hB.gms
  have hV₁ : CFSG.centerIn c.Qc ≤ c.Qc := inf_le_left
  have hV₂ : CFSG.centerIn c.Qt ≤ c.Qt := inf_le_left
  have hEsq : ∀ x ∈ d.E, x * x ∈ CFSG.centerIn c.Qc ⊔ CFSG.centerIn c.Qt := fun x hx =>
    h11.V_eq ▸ hEab.1 x hx
  set E₁ : Subgroup G := sec52FacFst c.Qc c.Qt d.E hcomm with hE₁
  have hE₁Q : E₁ ≤ c.Qc := sec52FacFst_le
  have hE₁ab : ElemAbMod (CFSG.centerIn c.Qc) E₁ :=
    sec52Fac_elemAbMod_of_sq (fun n hn g hg => (mem_centralizer_iff.1 hn.2 g (hE₁Q hg)).symm)
      (sec52FacFst_sq hinf hV₁ hV₂ hEsq)
  obtain ⟨hδP, hδab, hδcard⟩ := sec52Fac_δ_image hB c h11 hE₁Q hE₁ab
  obtain ⟨-, hδle, hδeq⟩ := d.sec2_2_modZp hδP hδab
  have hE₁le : Nat.card E₁ ≤ (2 ^ f) ^ 7 := hδcard ▸ hδle
  set E₂ : Subgroup G := E₁.map (MulAut.conj d.t).toMonoidHom with hE₂
  have hE₂Q : E₂ ≤ c.Qt := Subgroup.map_mono hE₁Q
  have hE₂card : Nat.card E₂ = Nat.card E₁ :=
    Subgroup.card_map_of_injective (MulAut.conj d.t).injective
  have hE₁₂inf : E₁ ⊓ E₂ = ⊥ := le_bot_iff.1 ((inf_le_inf hE₁Q hE₂Q).trans hinf.le)
  have hE₂N : E₂ ≤ normalizer (E₁ : Set G) := fun b hb =>
    mem_normalizer_of_mem_centralizer' (mem_centralizer_iff.2 fun a ha =>
      hcomm a (hE₁Q ha) b (hE₂Q hb))
  have hsup : Nat.card (E₁ ⊔ E₂ : Subgroup G) = Nat.card E₁ * Nat.card E₁ := by
    have := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq hE₂N
    rwa [hE₁₂inf, Subgroup.card_bot, mul_one, hE₂card] at this
  have hEle : d.E ≤ E₁ ⊔ E₂ := by
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm (h11.S_eq ▸ hES he)
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ha, b, hb, he⟩) (Subgroup.mem_sup_right ?_)
    obtain ⟨q, hq, rfl⟩ := hb
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj d.t).toMonoidHom he
    rw [hEt, map_mul, hττ] at h1
    exact ⟨q, ⟨hq, (MulAut.conj d.t).toMonoidHom a, ⟨a, ha, rfl⟩,
      by rw [hcomm q hq _ ⟨a, ha, rfl⟩]; exact h1⟩, rfl⟩
  have hmm : (2 ^ f) ^ 7 * (2 ^ f) ^ 7 = (2 ^ f) ^ 14 := by ring
  have hn : Nat.card E₁ = (2 ^ f) ^ 7 := by
    have h1 : Nat.card d.E ≤ Nat.card (E₁ ⊔ E₂ : Subgroup G) := Subgroup.card_le_of_le hEle
    rw [hEcard, hsup, ← hmm] at h1
    exact le_antisymm hE₁le (Nat.mul_self_le_mul_self_iff.1 h1)
  have hEeq : d.E = E₁ ⊔ E₂ := by
    refine Subgroup.eq_of_le_of_card_ge hEle ?_
    rw [hsup, hn, hEcard, hmm]
  have hE₁E : E₁ ≤ d.E := hEeq ▸ le_sup_left
  have hW₂ : c.W₂ = E₁ := by
    apply le_antisymm
    · rintro x ⟨hxE, hxK⟩
      exact ⟨⟨hES hxE, hxK⟩, 1, one_mem _, by simpa using hxE⟩
    · exact le_inf hE₁E (hE₁Q.trans hQK)
  have hW₂t : c.W₂t = E₂ := by
    rw [CaseBData.W₂t, hW₂]
  refine ⟨?_, ?_, ?_⟩
  · rw [hW₂, hW₂t]
    exact hEeq
  · rw [hW₂, hW₂t]
    exact hE₁₂inf
  · rw [hW₂]
    exact hδeq (hδcard.trans hn).ge

end CaseBData

end Data

namespace CaseBParts

theorem sec52Factors : Sec52FactorsStatement :=
  fun _ _ _ _ _ _ _ _ hB c h11 => Data.CaseBData.sec52_factors hB c h11

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
