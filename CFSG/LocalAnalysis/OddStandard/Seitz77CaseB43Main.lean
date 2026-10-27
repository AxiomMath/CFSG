module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB43Glue
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB43Perm
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB43Sylow
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseBCoreMain

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

structure CommonSylow {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
    (c₁ : CaseB A V₁ d.t) (c₂ : CaseB A V₂ d.t) (M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G) {k : Type}
    [Field k] (e : ↥A₁ ≃* ↥(unipAll k)) : Prop where
  F₁ : c₁.Factors M₁ M₂
  F₂ : c₂.Factors N₁ N₂
  syl : SylowB c₁ V₂ M₁ M₂ S A₁ B₁ e
  S_sylow₂ : IsSylowOf 2 S c₂.Ninf
  A_eq : S ⊓ N₁ = A₁
  B_eq : S ⊓ N₂ = B₁
  W₁_eq : c₁.W = radIn A₁ e (radOne k) ⊔ cs d.t (radIn A₁ e (radOne k))
  W₂_eq : c₂.W = radIn A₁ e (radTwo k) ⊔ cs d.t (radIn A₁ e (radTwo k))

section Main

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
  {c₁ : CaseB A V₁ d.t} {c₂ : CaseB A V₂ d.t}
  {M₁ M₂ S A₁ B₁ : Subgroup G} {k : Type} [Field k] {e : ↥A₁ ≃* ↥(unipAll k)}

theorem SylowB.torus_mem_N (Sy : SylowB c₁ V₂ M₁ M₂ S A₁ B₁ e) (hV₂ : V₂ ≤ d.V)
    {x : G} (hxA : ∀ a ∈ A₁, x * a * x⁻¹ ∈ A₁) (hxM : ∀ m ∈ M₂, x * m = m * x) {μ : k}
    (hμ : ∀ a a' : ↥A₁, (a' : G) = x * a * x⁻¹ →
      coordA (e a') = μ * coordA (e a) ∧ coordB (e a') = μ * coordB (e a)) :
    x ∈ c₂.N := by
  have P := Sy.swapPair
  have hB : ∀ b ∈ B₁, x * b = b * x := fun b hb => hxM b (by rw [Sy.B₁_eq] at hb; exact hb.2)
  refine Subgroup.mem_normalizer_fintype fun g hg => ?_
  rw [Sy.W'_eq hV₂ c₂] at hg ⊢
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_forall_comm (O := radIn A₁ e (radTwo k))
    (E := cs d.t (radIn A₁ e (radTwo k))) (fun u hu v hv => P.comm_X_cs radIn_le hu hv) hg
  have hvB : v ∈ B₁ := P.cs_le radIn_le hv
  have hxv : x * v * x⁻¹ = v := by rw [hB v hvB]; group
  have hxu : x * u * x⁻¹ ∈ radIn A₁ e (radTwo k) := by
    obtain ⟨a, ha, rfl⟩ := mem_radIn.mp hu
    refine mem_radIn.mpr ⟨⟨x * (a : G) * x⁻¹, hxA _ a.2⟩, ?_, rfl⟩
    rw [mem_radTwo]
    have := (hμ a ⟨x * (a : G) * x⁻¹, hxA _ a.2⟩ rfl).1
    rw [this, (mem_radTwo _).mp ha, mul_zero]
  have e1 : x * (u * v) * x⁻¹ = (x * u * x⁻¹) * v := by
    calc x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group
      _ = (x * u * x⁻¹) * v := by rw [hxv]
  rw [e1]
  exact mul_mem (mem_sup_left hxu) (mem_sup_right hv)

end Main

theorem caseB_common_sylow
    {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} (h : Hyp G A) (d : Datum A)
    (hR : Radicals d.V V₁ V₂) (c₁ : CaseB A V₁ d.t) (c₂ : CaseB A V₂ d.t) :
    ∃ (M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G) (k : Type) (_ : Field k) (e : ↥A₁ ≃* ↥(unipAll k)),
      CommonSylow c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ e := by
  obtain ⟨M₁, M₂, S, A₁, B₁, k, hkF, e, F₁, Sy⟩ := c₁.exists_sylowB h d hR
  obtain ⟨N₁, N₂, S', A₁', B₁', k', hk'F, e', F₂, Sy'⟩ := c₂.exists_sylowB h d hR.symm_B42
  have hV₁ : V₁ ≤ d.V := hR.le₁
  have hV₂ : V₂ ≤ d.V := hR.le₂
  have hSS : S = S' := sylowB_eq_of_two Sy Sy' hV₁ hV₂
  have hZ₁ : c₁.OddCoreCentral := CaseB.oddCoreCentral h d hR (Or.inl rfl) c₁
  have hZ₂ : c₂.OddCoreCentral := CaseB.oddCoreCentral h d hR (Or.inr rfl) c₂
  obtain ⟨x, -, hxodd, -, -, hxA, hxM₂, μ, hμ0, hμ1, hμ⟩ := Sy.exists_torus_centralizes hZ₁
  have hxN : x ∈ c₂.N := Sy.torus_mem_N hV₂ hxA hxM₂ hμ
  have hxN₁ : ∀ m ∈ N₁, x * m * x⁻¹ ∈ N₁ := fun m hm => F₂.conj_mem_of_odd hZ₂ hxN hxodd hm
  have hxB : ∀ b ∈ B₁, x * b = b * x := fun b hb => hxM₂ b (by rw [Sy.B₁_eq] at hb; exact hb.2)
  have hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro s hs
    rw [Sy.prod] at hs ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_forall_comm (O := A₁) (E := B₁) Sy.swapPair.comm hs
    have e1 : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * b := by
      calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
        _ = (x * a * x⁻¹) * b := by rw [hxB b hb]; group
    rw [e1]
    exact mul_mem (mem_sup_left (hxA a ha)) (mem_sup_right hb)
  have hxA' : ∀ a ∈ A₁', x * a * x⁻¹ ∈ A₁' := by
    intro a ha
    rw [Sy'.A₁_eq] at ha ⊢
    rw [← hSS]
    rw [← hSS] at ha
    exact ⟨hxS a ha.1, hxN₁ a ha.2⟩
  have hcard : Nat.card ↥A₁' = 64 := by
    have : Nat.card ↥A₁' = Nat.card ↥(unipAll k') := Nat.card_congr e'.toEquiv
    rw [this, card_unipAll, Sy'.card_k]
    norm_num
  have hsup : A₁' ⊔ B₁' = A₁ ⊔ B₁ := by rw [← Sy'.prod, ← Sy.prod, hSS]
  have P := Sy.swapPair
  have P' := Sy'.swapPair
  have hS₂ : IsSylowOf 2 S c₂.Ninf := hSS ▸ Sy'.S₀_sylow
  rcases P.decomp_eq P' Sy.card_k hμ0 hμ1 hxA hxB hμ hcard hsup hxA' with h1 | h1
  · have hB1 : B₁' = B₁ := by rw [P'.B_eq, P.B_eq, h1]
    refine ⟨M₁, M₂, N₁, N₂, S, A₁, B₁, k, hkF, e, ⟨F₁, F₂, Sy, hS₂, ?_, ?_, Sy.W_eq hV₁,
      Sy.W'_eq hV₂ c₂⟩⟩
    · rw [hSS, ← h1, Sy'.A₁_eq]
    · rw [hSS, ← hB1, Sy'.B₁_eq]
  · have hB1 : B₁' = A₁ := by
      rw [P'.B_eq, h1, P.B_eq, ← cs_mul, P.t_sq, cs_one]
    refine ⟨M₁, M₂, N₂, N₁, S, A₁, B₁, k, hkF, e, ⟨F₁, F₂.symm, Sy, hS₂, ?_, ?_, Sy.W_eq hV₁,
      Sy.W'_eq hV₂ c₂⟩⟩
    · rw [hSS, ← hB1, Sy'.B₁_eq]
    · rw [hSS, ← h1, Sy'.A₁_eq]

end CFSG.OddStandard.Seitz77
