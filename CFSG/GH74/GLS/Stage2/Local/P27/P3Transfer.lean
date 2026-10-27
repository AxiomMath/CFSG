module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import Mathlib.GroupTheory.IndexNormal
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup

section Transfer

variable {X : Type*} [Group X] [Finite X]

theorem transfer_normal_of_sep {P Q : Subgroup X} (hP : IsPGroup 2 ↥P) (hPidx : ¬ 2 ∣ P.index)
    (hQP : Q ≤ P) (hQ2 : Q.relIndex P = 2) {s : X} (hsP : s ∈ P) (hsQ : s ∉ Q) (hs2 : s * s = 1)
    (hsep : ∀ g : X, g⁻¹ * s * g ∈ P → g⁻¹ * s * g ∉ Q) :
    ∃ (N : Subgroup X) (_ : N.Normal), IsCyclic (X ⧸ N) ∧ IsPGroup 2 (X ⧸ N) ∧ s ∉ N := by
  have hidx : (Q.subgroupOf P).index = 2 := hQ2
  have hnorm : (Q.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hidx
  have hmul : ∀ a b : X, a ∈ P → b ∈ P → a ∉ Q → b ∉ Q → a⁻¹ * b ∈ Q := by
    intro a b ha hb haQ hbQ
    have h := Subgroup.mul_mem_iff_of_index_two (H := Q.subgroupOf P) hidx
      (a := ⟨a⁻¹, P.inv_mem ha⟩) (b := ⟨b, hb⟩)
    have h1 : (⟨a⁻¹, P.inv_mem ha⟩ : ↥P) ∈ Q.subgroupOf P ↔ False := by
      simp only [Subgroup.mem_subgroupOf, iff_false]
      intro h'
      exact haQ (by simpa using Q.inv_mem h')
    have h2 : (⟨b, hb⟩ : ↥P) ∈ Q.subgroupOf P ↔ False := by
      simp only [Subgroup.mem_subgroupOf, iff_false]
      exact hbQ
    have h3 : (⟨a⁻¹, P.inv_mem ha⟩ : ↥P) * ⟨b, hb⟩ ∈ Q.subgroupOf P := by
      rw [h]
      rw [h1, h2]
    simpa [Subgroup.mem_subgroupOf] using h3
  have key := CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (X := X) (p := 2) (P := P) (Q := Q)
    (u := s) hP hPidx
    (fun t ht q hq => by
      have := hnorm.conj_mem ⟨q, hQP hq⟩ (by simpa [Subgroup.mem_subgroupOf] using hq) ⟨t, ht⟩
      simpa [Subgroup.mem_subgroupOf] using this)
    ⟨s, hsP, fun t ht => by
      by_cases htQ : t ∈ Q
      · exact ⟨0, by simpa using htQ⟩
      · exact ⟨1, by simpa using hmul s t hsP ht hsQ htQ⟩⟩
    hsP hsQ
    (fun g k _ => by
      have : s ^ (2 * k) = 1 := by
        rw [pow_mul, pow_two, hs2, one_pow]
      rw [this]
      simp)
    (fun g hgP _ => by
      by_cases hgQ : g⁻¹ * s * g ∈ Q
      · exact Or.inl hgQ
      · refine Or.inr (?_)
        have := hmul s (g⁻¹ * s * g) hsP hgP hsQ hgQ
        simpa using this)
  rcases key with h | ⟨g, hgQ, -, -⟩
  · exact h
  · exact absurd hgQ (hsep g (hQP hgQ))

omit [Finite X] in
theorem commutator_le_of_isCyclic_quotient {N : Subgroup X} [N.Normal] (hN : IsCyclic (X ⧸ N)) :
    commutator X ≤ N := by
  have hc : IsMulCommutative (X ⧸ N) :=
    ⟨⟨fun a b => (IsCyclic.commGroup (α := X ⧸ N)).mul_comm a b⟩⟩
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.1 hc

omit [Finite X] in
theorem le_of_perfect_of_isCyclic_quotient {J N : Subgroup X} [N.Normal] (hJ : ⁅J, J⁆ = J)
    (hN : IsCyclic (X ⧸ N)) : J ≤ N := by
  have h2 : ⁅J, J⁆ ≤ commutator X := Subgroup.commutator_mono le_top le_top
  rw [← hJ]
  exact h2.trans (commutator_le_of_isCyclic_quotient hN)

omit [Finite X] in
theorem mem_sup_of_comm {D₁ D₂ : Subgroup X} (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) {w : X} :
    w ∈ D₁ ⊔ D₂ ↔ ∃ a ∈ D₁, ∃ b ∈ D₂, a * b = w := by
  constructor
  · intro hw
    rw [Subgroup.sup_eq_closure] at hw
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hw
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, D₂.one_mem, by simp⟩
      · exact ⟨1, D₁.one_mem, x, hx, by simp⟩
    · exact ⟨1, D₁.one_mem, 1, D₂.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
      refine ⟨a₁ * a₂, D₁.mul_mem ha₁ ha₂, b₁ * b₂, D₂.mul_mem hb₁ hb₂, ?_⟩
      have h := hcomm a₂ ha₂ b₁ hb₁
      calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by simp only [mul_assoc]
        _ = a₁ * (b₁ * a₂) * b₂ := by rw [h]
        _ = a₁ * b₁ * (a₂ * b₂) := by simp only [mul_assoc]
    · rintro _ _ ⟨a, ha, b, hb, rfl⟩
      refine ⟨a⁻¹, D₁.inv_mem ha, b⁻¹, D₂.inv_mem hb, ?_⟩
      rw [mul_inv_rev]
      exact hcomm a⁻¹ (D₁.inv_mem ha) b⁻¹ (D₂.inv_mem hb)
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

omit [Finite X] in
theorem relIndex_sup_comm_eq_two {D₁ D₂ T₁ : Subgroup X} (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a)
    (hinter : D₁ ⊓ D₂ = ⊥) (hT₁ : T₁ ≤ D₁) (h2 : T₁.relIndex D₁ = 2) :
    (T₁ ⊔ D₂).relIndex (D₁ ⊔ D₂) = 2 := by
  have h2' : (T₁.subgroupOf D₁).index = 2 := h2
  obtain ⟨a₀, ha₀⟩ := (Subgroup.index_eq_two_iff).1 h2'
  have hcomm' : ∀ a ∈ T₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb => hcomm a (hT₁ ha) b hb
  have key : ∀ d₁ ∈ D₁, ∀ d₂ ∈ D₂, d₁ * d₂ ∈ T₁ ⊔ D₂ ↔ d₁ ∈ T₁ := by
    intro d₁ hd₁ d₂ hd₂
    constructor
    · intro h
      obtain ⟨t, ht, e, he, hte⟩ := (mem_sup_of_comm hcomm').1 h
      have h1 : t⁻¹ * d₁ ∈ D₁ ⊓ D₂ := by
        refine ⟨D₁.mul_mem (D₁.inv_mem (hT₁ ht)) hd₁, ?_⟩
        have : t⁻¹ * d₁ = e * d₂⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hte]; group
        rw [this]
        exact D₂.mul_mem he (D₂.inv_mem hd₂)
      rw [hinter, Subgroup.mem_bot] at h1
      have : d₁ = t := by
        have := inv_mul_eq_one.1 h1
        exact this.symm
      rw [this]
      exact ht
    · intro h
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right hd₂)
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨(a₀ : X), Subgroup.mem_sup_left a₀.2⟩, fun b => ?_⟩
  obtain ⟨w, hw⟩ := b
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := (mem_sup_of_comm hcomm).1 hw
  have hx := ha₀ ⟨d₁, hd₁⟩
  simp only [Subgroup.mem_subgroupOf] at hx ⊢
  have e1 : d₁ * d₂ * (a₀ : X) = (d₁ * (a₀ : X)) * d₂ := by
    rw [mul_assoc, ← hcomm (a₀ : X) a₀.2 d₂ hd₂, ← mul_assoc]
  show Xor (d₁ * d₂ * (a₀ : X) ∈ T₁ ⊔ D₂) (d₁ * d₂ ∈ T₁ ⊔ D₂)
  rw [e1, key _ (D₁.mul_mem hd₁ a₀.2) d₂ hd₂, key d₁ hd₁ d₂ hd₂]
  exact hx

theorem inter_le_of_transfer {P M D₁ D₂ T₁ J : Subgroup X} (hP : IsPGroup 2 ↥P) (hPidx : ¬ 2 ∣ P.index)
    (hD₁ : D₁ ≤ P) (hPdec : ∀ w ∈ P, ∃ a ∈ D₁, ∃ b ∈ D₂, a * b = w)
    (hT₁M : T₁ ≤ M) (hD₂M : D₂ ≤ M)
    (hrefl : ∀ a ∈ D₁, a ∉ T₁ → a * a = 1) (hM : M.relIndex P = 2) (hMP : M ≤ P)
    (hJ : ⁅J, J⁆ = J) (hD₂c : D₂ ≤ commutator X)
    (hsep : ∀ a ∈ D₁, a ∉ T₁ → ∀ g : X, g⁻¹ * a * g ∈ P → g⁻¹ * a * g ∉ M) :
    P ⊓ J ≤ M := by
  intro w hw
  obtain ⟨hwP, hwJ⟩ := Subgroup.mem_inf.1 hw
  obtain ⟨a, ha, b, hb, hab⟩ := hPdec w hwP
  by_contra hwM
  have haT₁ : a ∉ T₁ := by
    intro haT
    exact hwM (hab ▸ M.mul_mem (hT₁M haT) (hD₂M hb))
  have haP : a ∈ P := hD₁ ha
  have haM : a ∉ M := by
    have := hsep a ha haT₁ 1 (by simpa using haP)
    simpa using this
  obtain ⟨N, hN, hcyc, -, haN⟩ := transfer_normal_of_sep hP hPidx hMP hM haP haM (hrefl a ha haT₁)
    (hsep a ha haT₁)
  have hJN : J ≤ N := le_of_perfect_of_isCyclic_quotient hJ hcyc
  have hbN : b ∈ N := commutator_le_of_isCyclic_quotient hcyc (hD₂c hb)
  apply haN
  have : a = w * b⁻¹ := by rw [← hab]; group
  rw [this]
  exact N.mul_mem (hJN hwJ) (N.inv_mem hbN)

end Transfer

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem inter_le_of_transfer_amb {X P M D₁ D₂ T₁ J : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 2 P X)
    (hJX : J ≤ X) (hD₁ : D₁ ≤ P) (hD₂ : D₂ ≤ P) (hPeq : P ≤ D₁ ⊔ D₂)
    (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a)
    (hT₁M : T₁ ≤ M) (hD₂M : D₂ ≤ M) (hrefl : ∀ a ∈ D₁, a ∉ T₁ → a * a = 1)
    (hM : M.relIndex P = 2) (hMP : M ≤ P)
    (hJ : ⁅J, J⁆ = J) (hD₂c : D₂ ≤ ⁅X, X⁆)
    (hsep : ∀ a ∈ D₁, a ∉ T₁ → ∀ g ∈ X, g⁻¹ * a * g ∈ P → g⁻¹ * a * g ∉ M) :
    P ⊓ J ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPX : P ≤ X := hP.le
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP
  obtain ⟨-, hP2, hPidx⟩ := hP
  have hJ' : ⁅J.subgroupOf X, J.subgroupOf X⁆ = J.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJX]
    exact hJ
  have hD₂c' : D₂.subgroupOf X ≤ commutator ↥X := by
    intro y hy
    have h1 : (y : G) ∈ ⁅X, X⁆ := hD₂c hy
    have h2 : (y : G) ∈ (commutator ↥X).map X.subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact h1
    obtain ⟨y', hy', hyy⟩ := h2
    have : y' = y := Subtype.ext hyy
    rwa [← this]
  have key := inter_le_of_transfer (X := ↥X) (P := P.subgroupOf X) (M := M.subgroupOf X)
    (D₁ := D₁.subgroupOf X) (D₂ := D₂.subgroupOf X) (T₁ := T₁.subgroupOf X) (J := J.subgroupOf X)
    hP2.comap_subtype hPidx (fun y hy => hD₁ hy)
    (fun w hw => by
      obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_of_comm hcomm).1 (hPeq hw)
      exact ⟨⟨a, hPX (hD₁ ha)⟩, ha, ⟨b, hPX (hD₂ hb)⟩, hb, Subtype.ext hab⟩)
    (fun y hy => hT₁M hy) (fun y hy => hD₂M hy)
    (fun a ha haT => by
      have := hrefl (a : G) ha haT
      exact Subtype.ext (by simpa using this))
    (by rw [Subgroup.relIndex_subgroupOf hPX]; exact hM)
    (fun y hy => hMP hy) hJ' hD₂c'
    (fun a ha haT g hg => by
      exact hsep (a : G) ha haT (g : G) g.2 hg)
  intro w hw
  obtain ⟨hwP, hwJ⟩ := Subgroup.mem_inf.1 hw
  have := key (Subgroup.mem_inf.2 ⟨(show (⟨w, hPX hwP⟩ : ↥X) ∈ P.subgroupOf X from hwP),
    (show (⟨w, hJX hwJ⟩ : ↥X) ∈ J.subgroupOf X from hwJ)⟩)
  exact this

end Ambient


end CFSG.GH74.GLS.Stage2.Local.P27
