module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8IIota
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MAFacts
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8CaseC

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

theorem false_of_transfer [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) (P : Sylow 2 X)
    {Q : Subgroup X} (hQP : Q ≤ P) (hindex : Q.relIndex P = 2)
    (hQ : ∀ m ∈ Q, ¬ ConjTo S.t m) : False := by
  obtain ⟨N, hN, hsq, htN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal P hQP hindex
    S.data.orderOf_t (fun x hx => hQ _ hx ⟨x⁻¹, by group⟩)
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · obtain ⟨a, b, hab⟩ := hX
    have hsq' : ∀ y : X, y * y = 1 := fun y => by
      have := hsq y
      rwa [h, mem_bot, pow_two] at this
    apply hab
    calc a * b = a * (a * b * (a * b)) * b := by rw [hsq', mul_one]
      _ = (a * a) * b * (a * (b * b)) := by group
      _ = b * a := by rw [hsq', hsq', one_mul, mul_one]
  · exact htN (h ▸ mem_top _)

@[expose] noncomputable def sylowOfMax {P : Subgroup X} (hP : IsPGroup 2 P)
    (hmax : ∀ Q : Subgroup X, IsPGroup 2 Q → P ≤ Q → Q = P) : Sylow 2 X where
  toSubgroup := P
  isPGroup' := hP
  is_maximal' hQ hle := hmax _ hQ hle

structure AData (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X) where
  h4 : S.Sec4 F T₁
  D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF)
  D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)
  hq₁ : D₁.q0 = .elem
  hq₂ : D₂.q0 = .elem
  hu₁ : D₁.u = F.xF * F.yF
  hu₂ : D₂.u = S.z * F.yF

namespace AData

variable (A : AData S F T₁)

@[expose] noncomputable def V₁ : ISide S F T₁ where
  yi := F.yF
  ki := F.kF
  ui := F.xF * F.yF
  hyi := isRefl_yF F
  hki := isK_kF F
  hui := rfl
  D := A.D₁
  hq := Or.inl A.hq₁
  hu := A.hu₁

@[expose] noncomputable def V₂ : ISide S F T₁ where
  yi := F.xF * F.yF
  ki := S.z * F.kF
  ui := S.z * F.yF
  hyi := isRefl_xyF F
  hki := isK_zkF F
  hui := (xF_mul_xyF F).symm
  D := A.D₂
  hq := Or.inl A.hq₂
  hu := A.hu₂

@[expose] noncomputable def P₁ : IPair S F T₁ where
  V := A.V₁
  W := A.V₂
  hyy := Or.inl rfl
  hkk := rfl
  h4 := A.h4

@[expose] noncomputable def P₂ : IPair S F T₁ where
  V := A.V₂
  W := A.V₁
  hyy := Or.inr (by
    change F.yF = S.z * (F.xF * (F.xF * F.yF))
    rw [xF_mul_xyF, ← mul_assoc, z_mul_z, one_mul])
  hkk := by
    change F.kF = S.z * (S.z * F.kF)
    rw [← mul_assoc, z_mul_z, one_mul]
  h4 := A.h4

noncomputable def ι : MA →* X := A.P₁.ιA A.hq₁

theorem ι_w₂ : A.ι MA.w₂ = A.D₁.w₂ := (IPair.ιA_spec (P := A.P₁) A.hq₁).1
theorem ι_u : A.ι MA.u = A.D₁.u := (IPair.ιA_spec (P := A.P₁) A.hq₁).2.1
theorem ι_w₁ : A.ι MA.w₁ = A.V₁.w₁N := (IPair.ιA_spec (P := A.P₁) A.hq₁).2.2.1
theorem ι_v : A.ι MA.v = A.V₁.vN := (IPair.ιA_spec (P := A.P₁) A.hq₁).2.2.2.1
theorem ι_z : A.ι MA.z = S.z := (IPair.ιA_spec (P := A.P₁) A.hq₁).2.2.2.2.1
theorem ι_y : A.ι MA.y = F.yF := (IPair.ιA_spec (P := A.P₁) A.hq₁).2.2.2.2.2.1
theorem ι_t : A.ι MA.t = S.t := (IPair.ιA_spec (P := A.P₁) A.hq₁).2.2.2.2.2.2.1
theorem ι_k : A.ι MA.k = F.kF := (IPair.ιA_spec (P := A.P₁) A.hq₁).2.2.2.2.2.2.2

theorem ι_injective : Function.Injective A.ι := IPair.ιA_injective (P := A.P₁) A.hq₁

theorem range_ι : A.ι.range = A.D₁.S₁ := IPair.range_ιA (P := A.P₁) A.hq₁

theorem mem_range_of_mem_S₁ {g : X} (hg : g ∈ A.D₁.S₁) : ∃ x : MA, A.ι x = g := by
  rw [← A.range_ι] at hg
  exact hg

theorem ι_mem_S₁ (x : MA) : A.ι x ∈ A.D₁.S₁ := A.range_ι ▸ ⟨x, rfl⟩

theorem card_S₁ : Nat.card A.D₁.S₁ = 256 := by
  rw [← A.range_ι, ← Nat.card_congr (MonoidHom.ofInjective A.ι_injective).toEquiv, MA.card_eq]
  norm_num

theorem card_centralizer (x : MA) : Nat.card (centralizer ({x} : Set MA)) = MA.ccount x := by
  classical
  rw [show Nat.card (centralizer ({x} : Set MA)) = Nat.card {g : MA // g * x = x * g} from
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_centralizer_singleton_iff),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem not_conjTo_of_ccount {x : MA} (hx : 32 < MA.ccount x) : ¬ ConjTo S.t (A.ι x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine not_conjTo_of_card (Q := (centralizer ({x} : Set MA)).map A.ι)
    ((MA.isPGroup.to_subgroup _).map A.ι) ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y * x = x * y := mem_centralizer_singleton_iff.mp hy
    rw [mem_centralizer_singleton_iff, ← map_mul, hy', map_mul]
  · rwa [card_map_of_injective A.ι_injective, card_centralizer]

theorem vN₁_mem_Q0C1 : A.V₁.vN ∈ S.Q0 F.yF F.kF A.D₁.w₁ A.D₁.w₂ ⊔ A.D₁.C₁ :=
  A.V₁.vN_mem_Q0C1 (A.P₁.option_of_elem A.hq₁).1

theorem not_conjTo_of_QC {x : MA} (hx : MA.inQC x = true) : ¬ ConjTo S.t (A.ι x) := by
  refine A.D₁.no_conj_of (Or.inl A.hq₁) _ (map_mem_of_inSpan A.ι (MA.QC_span x hx) fun g hg => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  have hE0 : ∀ e ∈ S.E0 F.yF F.kF, e ∈ S.Q0 F.yF F.kF A.D₁.w₁ A.D₁.w₂ ⊔ A.D₁.C₁ :=
    fun e he => mem_sup_left (A.V₁.E0_le_Q0 he)
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [A.ι_w₂]; exact mem_sup_left (w₂_mem_Q0 _ _ _ _)
  · rw [A.ι_w₁]; exact mem_sup_left A.V₁.w₁N_mem_Q0
  · rw [A.ι_v]; exact A.vN₁_mem_Q0C1
  · rw [A.ι_z]; exact hE0 _ (z_mem_E0 _ _)
  · rw [A.ι_y]; exact hE0 _ (yi_mem_E0 _ _)
  · rw [A.ι_k]; exact hE0 _ (ki_mem_E0 _ _)

theorem not_conjTo_uv : ¬ ConjTo S.t (A.ι (MA.u * MA.v)) := by
  rw [map_mul, A.ι_u, A.ι_v]
  refine A.D₂.no_conj_of (Or.inl A.hq₂) _ ?_
  set H := S.Q0 (F.xF * F.yF) (S.z * F.kF) A.D₂.w₁ A.D₂.w₂ ⊔ A.D₂.C₁ with hH
  have hE0 : ∀ e ∈ S.E0 (F.xF * F.yF) (S.z * F.kF), e ∈ H :=
    fun e he => mem_sup_left (A.V₂.E0_le_Q0 he)
  have hzk : ∀ c ∈ (zpowers S.z ⊔ zpowers (S.z * F.kF) : Subgroup X), c ∈ H :=
    fun c hc => hE0 c (A.V₂.zk_le_E0 hc)
  have hu : A.D₁.u ∈ H := by rw [A.hu₁]; exact hE0 _ (yi_mem_E0 _ _)
  have hvW : A.V₂.vN ∈ H := A.V₂.vN_mem_Q0C1 (A.P₂.option_of_elem A.hq₂).1
  have hwW : A.V₂.w₁N ∈ H := mem_sup_left A.V₂.w₁N_mem_Q0
  obtain ⟨c, hc, hw⟩ := A.P₁.exists_w₁W_same (A.hq₁.trans A.hq₂.symm)
  obtain ⟨c', hc', hv⟩ := A.P₁.exists_vW_zk
  have e1 : A.P₁.V.w₁c = A.V₁.w₁N := ISide.w₁c_of_elem _ A.hq₁
  have e2 : A.P₁.W.w₁c = A.V₂.w₁N := ISide.w₁c_of_elem _ A.hq₂
  change A.V₁.w₁c = A.V₂.w₁c * c at hw
  change A.V₁.vN * A.V₁.w₁c = A.V₂.vN * c' at hv
  rw [show A.V₁.w₁c = A.V₁.w₁N from e1, show A.V₂.w₁c = A.V₂.w₁N from e2] at hw
  rw [show A.V₁.w₁c = A.V₁.w₁N from e1] at hv
  have : A.V₁.vN = A.V₂.vN * c' * (A.V₂.w₁N * c)⁻¹ := by rw [← hw, ← hv]; group
  rw [this]
  exact mul_mem hu (mul_mem (mul_mem hvW (hzk _ hc')) (inv_mem (mul_mem hwW (hzk _ hc))))

theorem mem_Kc_of_conjTo {x : MA} (hx : ConjTo S.t (A.ι x)) : x ∈ MA.KcList := by
  obtain ⟨c, hc⟩ := hx
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
  have hq : MA.inQC x = false := by
    by_contra h
    exact A.not_conjTo_of_QC (by simpa using h) ⟨c, hc⟩
  have hcc : MA.ccount x ≤ 32 := not_lt.mp fun h => A.not_conjTo_of_ccount h ⟨c, hc⟩
  rcases MA.L_fact x hx2 hx1 hq hcc with h | ⟨s, hs⟩
  · exact h
  · exfalso
    apply A.not_conjTo_uv
    rw [← hs, map_mul, map_mul, map_inv, ← hc]
    exact ⟨A.ι s * c, by group⟩

@[expose] noncomputable def M₀ : Subgroup X := MA.M.map A.ι

theorem M₀_le : A.M₀ ≤ A.D₁.S₁ := by
  rw [M₀, ← A.range_ι]; exact map_le_range _ _

theorem card_M₀ : Nat.card A.M₀ = 128 := by
  rw [M₀, card_map_of_injective A.ι_injective, MA.card_M]

theorem not_conjTo_M₀ {m : X} (hm : m ∈ A.M₀) : ¬ ConjTo S.t m := by
  rintro hc
  obtain ⟨x, hx, rfl⟩ := hm
  have h1 := MA.Kc_not_M x (A.mem_Kc_of_conjTo hc)
  have h2 : MA.inM x = true := hx
  rw [h2] at h1
  exact Bool.noConfusion h1

end AData

end Sec8

end CFSG.ComponentClassification.HSFLit
