module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8AData
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MBFacts

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

structure BData (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X) where
  h4 : S.Sec4 F T₁
  D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF)
  D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)
  hq₁ : D₁.q0 = .homocyclic
  hq₂ : D₂.q0 = .homocyclic
  hu₁ : D₁.u = F.xF * F.yF
  hu₂ : D₂.u = S.z * F.yF

namespace BData

variable (A : BData S F T₁)

@[expose] noncomputable def V₁ : ISide S F T₁ where
  yi := F.yF
  ki := F.kF
  ui := F.xF * F.yF
  hyi := isRefl_yF F
  hki := isK_kF F
  hui := rfl
  D := A.D₁
  hq := Or.inr A.hq₁
  hu := A.hu₁

@[expose] noncomputable def V₂ : ISide S F T₁ where
  yi := F.xF * F.yF
  ki := S.z * F.kF
  ui := S.z * F.yF
  hyi := isRefl_xyF F
  hki := isK_zkF F
  hui := (xF_mul_xyF F).symm
  D := A.D₂
  hq := Or.inr A.hq₂
  hu := A.hu₂

@[expose] noncomputable def P₁ : IPair S F T₁ where
  V := A.V₁
  W := A.V₂
  hyy := Or.inl rfl
  hkk := rfl
  h4 := A.h4

noncomputable def ι : MB →* X := A.P₁.ιB A.hq₁

theorem ι_w₂ : A.ι MB.w₂ = A.D₁.w₂ := (IPair.ιB_spec (P := A.P₁) A.hq₁).1
theorem ι_u : A.ι MB.u = A.D₁.u := (IPair.ιB_spec (P := A.P₁) A.hq₁).2.1
theorem ι_w₁ : A.ι MB.w₁ = A.V₁.w₁N := (IPair.ιB_spec (P := A.P₁) A.hq₁).2.2.1
theorem ι_v : A.ι MB.v = A.V₁.vN := (IPair.ιB_spec (P := A.P₁) A.hq₁).2.2.2.1
theorem ι_z : A.ι MB.z = S.z := (IPair.ιB_spec (P := A.P₁) A.hq₁).2.2.2.2.1
theorem ι_y : A.ι MB.y = F.yF := (IPair.ιB_spec (P := A.P₁) A.hq₁).2.2.2.2.2.1
theorem ι_t : A.ι MB.t = S.t := (IPair.ιB_spec (P := A.P₁) A.hq₁).2.2.2.2.2.2.1
theorem ι_k : A.ι MB.k = F.kF := (IPair.ιB_spec (P := A.P₁) A.hq₁).2.2.2.2.2.2.2

theorem ι_injective : Function.Injective A.ι := IPair.ιB_injective (P := A.P₁) A.hq₁

theorem range_ι : A.ι.range = A.D₁.S₁ := IPair.range_ιB (P := A.P₁) A.hq₁

theorem card_S₁ : Nat.card A.D₁.S₁ = 256 := by
  rw [← A.range_ι, ← Nat.card_congr (MonoidHom.ofInjective A.ι_injective).toEquiv, MB.card_eq]
  norm_num

theorem card_centralizer (x : MB) : Nat.card (centralizer ({x} : Set MB)) = MB.ccount x := by
  classical
  rw [show Nat.card (centralizer ({x} : Set MB)) = Nat.card {g : MB // g * x = x * g} from
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_centralizer_singleton_iff),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem not_conjTo_of_ccount {x : MB} (hx : 32 < MB.ccount x) : ¬ ConjTo S.t (A.ι x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine not_conjTo_of_card (Q := (centralizer ({x} : Set MB)).map A.ι)
    ((MB.isPGroup.to_subgroup _).map A.ι) ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y * x = x * y := mem_centralizer_singleton_iff.mp hy
    rw [mem_centralizer_singleton_iff, ← map_mul, hy', map_mul]
  · rwa [card_map_of_injective A.ι_injective, card_centralizer]

theorem not_conjTo_of_QC {x : MB} (hx : MB.inQC x = true) : ¬ ConjTo S.t (A.ι x) := by
  refine A.D₁.no_conj_of (Or.inr A.hq₁) _ (map_mem_of_inSpan A.ι (MB.QC_span x hx) fun g hg => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  have hE0 : ∀ e ∈ S.E0 F.yF F.kF, e ∈ S.Q0 F.yF F.kF A.D₁.w₁ A.D₁.w₂ ⊔ A.D₁.C₁ :=
    fun e he => mem_sup_left (A.V₁.E0_le_Q0 he)
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [A.ι_w₂]; exact mem_sup_left (w₂_mem_Q0 _ _ _ _)
  · rw [A.ι_w₁]; exact mem_sup_left A.V₁.w₁N_mem_Q0
  · rw [A.ι_z]; exact hE0 _ (z_mem_E0 _ _)
  · rw [A.ι_y]; exact hE0 _ (yi_mem_E0 _ _)
  · rw [A.ι_k]; exact hE0 _ (ki_mem_E0 _ _)
  · rw [map_mul, A.ι_t, A.ι_v]
    exact A.V₁.tvN_mem_Q0C1 (A.P₁.option_of_homoc A.hq₁).1

@[expose] noncomputable def M₀ : Subgroup X := MB.Mb.map A.ι

theorem M₀_le : A.M₀ ≤ A.D₁.S₁ := by
  rw [M₀, ← A.range_ι]; exact map_le_range _ _

theorem card_M₀ : Nat.card A.M₀ = 128 := by
  rw [M₀, card_map_of_injective A.ι_injective, MB.card_Mb]

theorem relIndex_M₀ : A.M₀.relIndex A.D₁.S₁ = 2 := by
  have h1 := card_mul_index (A.M₀.subgroupOf A.D₁.S₁)
  rw [show Nat.card (A.M₀.subgroupOf A.D₁.S₁) = Nat.card A.M₀ from
    Nat.card_congr (subgroupOfEquivOfLe A.M₀_le).toEquiv, A.card_M₀, A.card_S₁] at h1
  rw [relIndex]
  omega

theorem not_conjTo_M₀ {m : X} (hm : m ∈ A.M₀) : ¬ ConjTo S.t m := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx, rfl⟩ := hm
  have hx2 : x * x = 1 := by
    apply A.ι_injective
    rw [map_mul, ← hc, map_one, show c * S.t * c⁻¹ * (c * S.t * c⁻¹) = c * (S.t * S.t) * c⁻¹ by
      group, t_mul_t, mul_one, mul_inv_cancel]
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one] at hc
    exact S.t_ne_one (by
      calc S.t = c⁻¹ * (c * S.t * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; group)
  have hq : MB.inQC x = false := by
    by_contra h
    exact A.not_conjTo_of_QC (by simpa using h) ⟨c, hc⟩
  have hcc : MB.ccount x ≤ 32 := not_lt.mp fun h => A.not_conjTo_of_ccount h ⟨c, hc⟩
  have h1 := MB.cand_fact x hx2 hx1 hq hcc
  have h2 : MB.inMb x = true := hx
  rw [h2] at h1
  exact Bool.noConfusion h1

theorem false_of_maximal [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (hmax : ∀ Q : Subgroup X, IsPGroup 2 Q → A.D₁.S₁ ≤ Q → Q = A.D₁.S₁) : False :=
  false_of_transfer (S := S) hX (sylowOfMax A.D₁.isPGroup_S₁ hmax) A.M₀_le A.relIndex_M₀
    fun _ hm => A.not_conjTo_M₀ hm

end BData

end Sec8

end CFSG.ComponentClassification.HSFLit
