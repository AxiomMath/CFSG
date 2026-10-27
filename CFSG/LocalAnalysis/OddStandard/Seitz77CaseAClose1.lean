module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseBasic
public import CFSG.LocalAnalysis.OddStandard.Seitz77UElem
public import CFSG.LocalAnalysis.OddStandard.Seitz77V1ActCertified

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

theorem Hyp.isSylowOf_centralizer_adj
    {G : Type} [Group G] [Finite G] {A : Subgroup G} (h : Hyp G A)
    (d : Datum A) {V₁ V₂ : Subgroup G} (hR : Radicals d.V V₁ V₂) {W : Subgroup G}
    (hW : W = V₁ ∨ W = V₂) :
    IsSylowOf 2 (W ⊔ zpowers d.t) (centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G)) :=
  h.facts.isSylowOf_centralizer d hR (alpha_of_certificates h d) hW
    (h.centralizer_radical_le d hR hW)

section A1

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F}
  {φ : G → RingAut F} (S : SylowA d W S₁ S₀ W₀ ι κ φ)

include S

namespace SylowA

theorem not_conj_mem_S₀
    (h : Hyp G A) {x : G} (hx : x ∈ S₀) (hx2 : x * x = 1) :
    ¬ IsConj d.t x := by
  intro hconj
  obtain ⟨V₁, V₂, hR⟩ := h.exists_radicals d
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hP := d.P_isSylow_centralizer
  have hS₁p : IsPGroup 2 S₁ := S.sylow_S₁.isPGroup
  have key : ∀ E : Subgroup G, IsPGroup 2 E → (∀ y ∈ E, y * x = x * y) →
      ∃ k : G, k * x * k⁻¹ = d.t ∧ ∀ y ∈ E, k * y * k⁻¹ ∈ d.P := by
    intro E hE hEc
    have hE'p : IsPGroup 2 (E.map (MulAut.conj g⁻¹).toMonoidHom) := hE.map _
    have hE'c : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({d.t} : Set G) := by
      intro z hz
      rw [mem_centralizer_singleton_iff]
      rw [mem_map_conj_iff, inv_inv] at hz
      have h1 := hEc _ hz
      rw [← hg] at h1
      calc z * d.t = g⁻¹ * (g * z * g⁻¹ * (g * d.t * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * d.t * g⁻¹ * (g * z * g⁻¹)) * g := by rw [h1]
        _ = d.t * z := by group
    obtain ⟨c, hc, hcP⟩ := exists_conj_le_of_isSylowOf hP hE'p hE'c
    have hct : c * d.t = d.t * c := mem_centralizer_singleton_iff.mp hc
    refine ⟨c * g⁻¹, ?_, fun y hy => ?_⟩
    · calc c * g⁻¹ * x * (c * g⁻¹)⁻¹ = c * (g⁻¹ * x * g) * c⁻¹ := by group
        _ = c * d.t * c⁻¹ := by rw [← hg]; group
        _ = d.t := by rw [hct]; group
    · have hy' : g⁻¹ * y * g ∈ E.map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [mem_map_conj_iff]
        simpa [mul_assoc] using hy
      have := hcP _ hy'
      have e : c * g⁻¹ * y * (c * g⁻¹)⁻¹ = c * (g⁻¹ * y * g) * c⁻¹ := by group
      rw [e]
      exact this
  by_cases hxW : x ∈ W
  ·
    have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 8) (by rw [S.card_W])
    obtain ⟨k, -, hkW⟩ := key W hWp (fun y hy => S.comm_of_mem_W hy hxW)
    have hle : W.map (MulAut.conj k).toMonoidHom ≤ d.P := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hz
      simpa using hkW y hy
    have hab := isElemAbelian_map_conj (fun a ha b hb => S.comm_of_mem_W ha hb)
      (fun a ha => S.mul_self_of_mem_W ha) k
    have hE := isElemAbelian_of_forall_two hab.1 hab.2
    have := h.card_elem_le d hR hle hE
    rw [card_map_conj, S.card_W] at this
    omega
  · have hxW₀ : x ∉ W₀ := fun h' => hxW (S.W₀_le_W h')
    have hcomm : ∀ e ∈ W₀, e * x = x * e := fun e he => (S.commute_of_mem_W₀ hx he).symm
    have hcx : zpowers x ≤ centralizer ({x} : Set G) := by
      rw [zpowers_le, mem_centralizer_singleton_iff]
    have hW₀x : W₀ ≤ centralizer ({x} : Set G) := fun e he => by
      rw [mem_centralizer_singleton_iff]
      exact hcomm e he
    have hExab : IsElemAbelian 2 (W₀ ⊔ zpowers x) :=
      isElemAbelian_sup_zpowers (isElemAbelian_of_le S.isElemAbelian_W S.W₀_le_W) hcomm hx2
    have hExcard : Nat.card ↥(W₀ ⊔ zpowers x) = 32 := by
      have := card_eq_two_mul_card_inf (F := W₀ ⊔ zpowers x) (V := W₀) (t := x)
        (mem_sup_right (mem_zpowers x)) hxW₀ (fun y hy => (mem_sup_zpowers_iff hcomm hx2).1 hy)
      rw [this, inf_eq_right.mpr le_sup_left, S.card_W₀]
    have hExp : IsPGroup 2 ↥(W₀ ⊔ zpowers x) :=
      IsPGroup.of_card (n := 5) (by rw [hExcard]; norm_num)
    obtain ⟨k, -, hkE⟩ := key (W₀ ⊔ zpowers x) hExp (fun y hy => by
      have := (sup_le hW₀x hcx) hy
      exact mem_centralizer_singleton_iff.mp this)
    set Ex'' := (W₀ ⊔ zpowers x).map (MulAut.conj k).toMonoidHom with hEx''
    have hEx''P : Ex'' ≤ d.P := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hz
      simpa using hkE y hy
    have hab := isElemAbelian_map_conj (fun a ha b hb => comm_of_isElemAbelian_two hExab ha hb)
      (fun a ha => mul_self_of_isElemAbelian_two hExab ha) k
    have hEx''ab := isElemAbelian_of_forall_two hab.1 hab.2
    have hEx''card : Nat.card Ex'' = 32 := by rw [hEx'', card_map_conj, hExcard]
    set Q : Subgroup G := S₀ ⊓ centralizer ({x} : Set G) with hQ
    have hQp : IsPGroup 2 Q := hS₁p.to_le ((inf_le_left).trans S.S₀_le_S₁)
    have hQc : Q ≤ centralizer ((W₀ ⊔ zpowers x : Subgroup G) : Set G) := by
      intro q hq
      rw [mem_centralizer_iff]
      intro e he
      have hq' : q ∈ S₀ := hq.1
      have hqx : q * x = x * q := mem_centralizer_singleton_iff.mp hq.2
      have hEc : W₀ ⊔ zpowers x ≤ centralizer ({q} : Set G) := by
        refine sup_le (fun w hw => ?_) ?_
        · rw [mem_centralizer_singleton_iff]
          exact (S.commute_of_mem_W₀ hq' hw).symm
        · rw [zpowers_le, mem_centralizer_singleton_iff]
          exact hqx.symm
      exact mem_centralizer_singleton_iff.mp (hEc he)
    have hQ'c : Q.map (MulAut.conj k).toMonoidHom ≤ centralizer (Ex'' : Set G) := by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := mem_map.mp hz
      rw [mem_centralizer_iff]
      intro e he
      obtain ⟨e₀, he₀, rfl⟩ := mem_map.mp he
      have := mem_centralizer_iff.mp (hQc hq) e₀ he₀
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc k * e₀ * k⁻¹ * (k * q * k⁻¹) = k * (e₀ * q) * k⁻¹ := by group
        _ = k * (q * e₀) * k⁻¹ := by rw [this]
        _ = k * q * k⁻¹ * (k * e₀ * k⁻¹) := by group
    have hQ'p : IsPGroup 2 (Q.map (MulAut.conj k).toMonoidHom) := hQp.map _
    have hbound : Nat.card (Q.map (MulAut.conj k).toMonoidHom) ≤ 32 := by
      rcases (h.card_elem_eq_iff d hR hEx''P hEx''ab).1 hEx''card with h1 | h1
      · have hsyl := h.isSylowOf_centralizer_adj d hR (W := V₁) (Or.inl rfl)
        rw [← h1] at hsyl
        exact (card_le_of_isSylowOf_of_le hsyl hQ'p hQ'c).trans hEx''card.le
      · have hsyl := h.isSylowOf_centralizer_adj d hR (W := V₂) (Or.inr rfl)
        rw [← h1] at hsyl
        exact (card_le_of_isSylowOf_of_le hsyl hQ'p hQ'c).trans hEx''card.le
    rw [card_map_conj] at hbound
    have : 256 ≤ Nat.card Q := S.card_inf_centralizer_ge hx
    omega

end SylowA

end A1

end CFSG.OddStandard.Seitz77
