module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapKappa
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapMB

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

open Sec7

namespace MB

theorem centralizer_QC : ∀ x : MB, (∀ y : MB, inQC y = true → x * y = y * x) →
    inQC x = true := by
  decide +kernel

end MB

theorem exists_mem_normalizer_of_lt {X : Type} [Group X] [Finite X] {P R : Subgroup X}
    (hR : IsPGroup 2 R) (hPR : P < R) : ∃ w ∈ R, w ∉ P ∧ w ∈ normalizer (P : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt : P.subgroupOf R < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    obtain ⟨w, hwR, hwP⟩ := IsConcreteLE.exists_of_lt hPR
    have : (⟨w, hwR⟩ : R) ∈ P.subgroupOf R := by rw [htop]; exact mem_top _
    exact hwP this
  have : Group.IsNilpotent R := hR.isNilpotent
  obtain ⟨w, hwN, hwP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨w, w.2, hwP, ?_⟩
  rw [mem_normalizer_iff]
  intro g
  by_cases hgR : g ∈ R
  · have := (mem_normalizer_iff.mp hwN) ⟨g, hgR⟩
    simpa only [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using this
  · constructor
    · intro hg; exact absurd (hPR.le hg) hgR
    · intro hg
      have h1 : (w : X) * g * (w : X)⁻¹ ∈ R := hPR.le hg
      have h2 := mul_mem (mul_mem (inv_mem w.2) h1) w.2
      rw [show (w : X)⁻¹ * ((w : X) * g * (w : X)⁻¹) * (w : X) = g by group] at h2
      exact absurd h2 hgR

theorem four_mul_zmod4 : ∀ x : ZMod 4, 2 * (x + x) = 0 := by decide

theorem zmod4_aux₀ : ∀ w v : ZMod 4, -w = v + v + w → 2 * v = 0 → w + w = 0 := by decide

theorem zmod4_aux₂ : ∀ w v : ZMod 4, -w = v + v + w → 2 * v ≠ 0 → w + w = 2 := by decide

theorem blk_sum₁ : ∀ a b : ZMod 2, (a, b) ≠ (0, 0) →
    (![a, b, 1] + blk 0 1 1 1 *ᵥ ![a, b, 1]) 2 = 0 ∧
      ((![a, b, 1] + blk 0 1 1 1 *ᵥ ![a, b, 1]) 0,
        (![a, b, 1] + blk 0 1 1 1 *ᵥ ![a, b, 1]) 1) ≠ (0, 0) := by
  decide +kernel

theorem blk_sum₂ : ∀ a b : ZMod 2, (a, b) ≠ (0, 0) →
    (![a, b, 1] + blk 1 1 1 0 *ᵥ ![a, b, 1]) 2 = 0 ∧
      ((![a, b, 1] + blk 1 1 1 0 *ᵥ ![a, b, 1]) 0,
        (![a, b, 1] + blk 1 1 1 0 *ᵥ ![a, b, 1]) 1) ≠ (0, 0) := by
  decide +kernel

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace BData

variable (A : BData S F T₁)

theorem t_conj_eq_iff (v : Fin 3 → ZMod 4) :
    S.t * A.Φ v * S.t⁻¹ = A.Φ v ↔ ∀ i, 2 * v i = 0 := by
  rw [A.t_conj_Φ]
  constructor
  · intro h i
    have := congrFun (A.Φ_injective h) i
    simp only [Pi.neg_apply] at this
    rw [two_mul, ← sub_eq_zero.mpr this.symm]
    ring
  · intro h
    congr 1
    funext i
    simp only [Pi.neg_apply]
    rw [neg_eq_iff_add_eq_zero, ← two_mul, h i]

theorem mem_AA_of_S₁ {g : X} (hg : g ∈ A.D₁.S₁) (hc : g ∈ centralizer (A.AA : Set X)) :
    g ∈ A.AA := by
  rw [← A.range_ι] at hg
  obtain ⟨x, rfl⟩ := hg
  refine ⟨x, MB.centralizer_QC x fun y hy => A.ι_injective ?_, rfl⟩
  rw [map_mul, map_mul]
  exact ((mem_centralizer_iff.mp hc) (A.ι y) ⟨y, hy, rfl⟩).symm

theorem map_E₁_of_centralizer {τ : X} (hτ : τ ∈ centralizer (A.AA : Set X)) {a : X}
    (ha : τ * S.t * τ⁻¹ = S.t * a) :
    F.E₁.map (MulAut.conj τ).toMonoidHom = E0t F a := by
  rw [A.E₁_eq_E0t]
  refine map_E0t ?_ (by rw [mul_one, ha])
  apply le_antisymm
  · rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(mem_centralizer_iff.mp hτ e (A.E0_le_AA he)).symm, mul_inv_cancel_right]
    exact he
  · intro e he
    refine ⟨e, he, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(mem_centralizer_iff.mp hτ e (A.E0_le_AA he)).symm, mul_inv_cancel_right]

theorem two_mul_of_conj_t (hnc : ¬ SubConj F.E₁ F.E₂) {τ : X}
    (hτ : τ ∈ centralizer (A.AA : Set X)) {v : Fin 3 → ZMod 4}
    (hv : τ * S.t * τ⁻¹ = S.t * A.Φ v) : 2 * v 0 = 0 ∧ 2 * v 1 = 0 := by
  by_contra hne
  by_cases h2 : 2 * v 2 = 0
  · exact A.not_conj_E0t hnc h2 hne (A.map_E₁_of_centralizer hτ hv)
  obtain ⟨δ, hδ, hz⟩ := A.exists_kappa
  set κ : A.NA := ⟨δ, A.D₁₁_le_NA hδ⟩ with hκ
  set K := A.mat κ with hK
  have hτ' : δ * τ * δ⁻¹ ∈ centralizer (A.AA : Set X) := by
    rw [mem_centralizer_iff]
    intro g hg
    have hg' : δ⁻¹ * g * δ ∈ A.AA := by
      have := A.D₁₁_conj_AA (inv_mem hδ) hg
      rwa [inv_inv] at this
    have := mem_centralizer_iff.mp hτ _ hg'
    calc g * (δ * τ * δ⁻¹) = δ * ((δ⁻¹ * g * δ) * τ) * δ⁻¹ := by group
      _ = δ * (τ * (δ⁻¹ * g * δ)) * δ⁻¹ := by rw [this]
      _ = δ * τ * δ⁻¹ * g := by group
  have hv' : (δ * τ * δ⁻¹) * S.t * (δ * τ * δ⁻¹)⁻¹ = S.t * A.Φ (K *ᵥ v) := by
    have hδt := A.D₁₁_comm_t hδ
    rw [← A.conj_Φ κ v]
    calc δ * τ * δ⁻¹ * S.t * (δ * τ * δ⁻¹)⁻¹ = δ * (τ * (δ⁻¹ * S.t * δ) * τ⁻¹) * δ⁻¹ := by
          group
      _ = δ * (τ * S.t * τ⁻¹) * δ⁻¹ := by
          rw [show δ⁻¹ * S.t * δ = S.t by
            rw [mul_assoc, ← hδt, ← mul_assoc, inv_mul_cancel, one_mul]]
      _ = (δ * S.t) * A.Φ v * δ⁻¹ := by rw [hv]; group
      _ = S.t * (δ * A.Φ v * δ⁻¹) := by rw [hδt]; group
  have hprod : (τ * (δ * τ * δ⁻¹)) * S.t * (τ * (δ * τ * δ⁻¹))⁻¹ =
      S.t * A.Φ (v + K *ᵥ v) := by
    rw [A.Φ_add]
    calc τ * (δ * τ * δ⁻¹) * S.t * (τ * (δ * τ * δ⁻¹))⁻¹ =
        τ * ((δ * τ * δ⁻¹) * S.t * (δ * τ * δ⁻¹)⁻¹) * τ⁻¹ := by group
      _ = (τ * S.t * τ⁻¹) * (τ * A.Φ (K *ᵥ v) * τ⁻¹) := by rw [hv']; group
      _ = S.t * A.Φ v * A.Φ (K *ᵥ v) := by
          rw [hv, ← (mem_centralizer_iff.mp hτ _ (A.Φ_mem _)), mul_inv_cancel_right]
      _ = S.t * (A.Φ v * A.Φ (K *ᵥ v)) := by group
  have hred : redV (v + K *ᵥ v) = redV v + redM K *ᵥ redV v := by
    rw [redV_add, redV_mulVec]
  have hab : (r2 (v 0), r2 (v 1)) ≠ (0, 0) := by
    intro h
    simp only [Prod.mk.injEq] at h
    exact hne ⟨(r2_eq_zero_iff _).mp h.1, (r2_eq_zero_iff _).mp h.2⟩
  have hv2 : r2 (v 2) = 1 := by
    have h := (r2_eq_zero_iff (v 2)).not.mpr h2
    revert h; generalize r2 (v 2) = x; revert x; decide
  have hvred : redV v = ![r2 (v 0), r2 (v 1), 1] := by
    funext i; fin_cases i <;> simp [redV, hv2]
  have hK2 : redM K = blk 0 1 1 1 ∨ redM K = blk 1 1 1 0 := A.kbar_cases hδ hz
  obtain ⟨k2, k01⟩ : (redV (v + K *ᵥ v)) 2 = 0 ∧
      ((redV (v + K *ᵥ v)) 0, (redV (v + K *ᵥ v)) 1) ≠ (0, 0) := by
    rw [hred, hvred]
    rcases hK2 with h | h <;> rw [h]
    · exact blk_sum₁ _ _ hab
    · exact blk_sum₂ _ _ hab
  refine A.not_conj_E0t hnc ((r2_eq_zero_iff _).mp k2) ?_
    (A.map_E₁_of_centralizer (mul_mem hτ hτ') hprod)
  rintro ⟨h0, h1⟩
  apply k01
  simp only [redV, (r2_eq_zero_iff _).mpr h0, (r2_eq_zero_iff _).mpr h1]

theorem mem_normalizer_E₁ {q : X} (hq : q ∈ centralizer (A.AA : Set X)) {v : Fin 3 → ZMod 4}
    (hv : q * S.t * q⁻¹ = S.t * A.Φ v) (hev : ∀ i, 2 * v i = 0) :
    q ∈ normalizer (F.E₁ : Set X) := by
  have h := A.map_E₁_of_centralizer hq hv
  rw [show A.Φ v = 1 * A.Φ v by rw [one_mul], E0t_mul (A.Φ_mem_E0 hev), ← A.E₁_eq_E0t] at h
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← h]; exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← h] at hg
    obtain ⟨g', hg', hgg⟩ := hg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgg
    have : g' = g := by
      have := congrArg (fun x => q⁻¹ * x * q) hgg
      simpa [mul_assoc] using this
    rwa [← this]

structure Syl (A : BData S F T₁) where
  P : Subgroup X
  isPGroup : IsPGroup 2 P
  le_NA : P ≤ A.NA
  S₁_le : A.D₁.S₁ ≤ P
  maximal : ∀ R : Subgroup X, IsPGroup 2 R → P ≤ R → R ≤ A.NA → R = P

theorem exists_syl : Nonempty A.Syl := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 (A.D₁.S₁.subgroupOf A.NA) :=
    A.D₁.isPGroup_S₁.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hS.exists_le_sylow
  refine ⟨⟨(Q : Subgroup A.NA).map A.NA.subtype, Q.isPGroup'.map _, map_subtype_le _, ?_, ?_⟩⟩
  · intro g hg
    exact ⟨⟨g, A.S₁_le_normalizer hg⟩, hQ hg, rfl⟩
  · intro R hR hle hRN
    have hR' : IsPGroup 2 (R.subgroupOf A.NA) := hR.comap_of_injective _ (subtype_injective _)
    have hQR : (Q : Subgroup A.NA) ≤ R.subgroupOf A.NA := fun g hg => hle ⟨g, hg, rfl⟩
    have := Q.is_maximal' hR' hQR
    apply le_antisymm _ hle
    intro g hg
    have : (⟨g, hRN hg⟩ : A.NA) ∈ (Q : Subgroup A.NA) := by
      rw [← this]; exact hg
    exact ⟨_, this, rfl⟩

namespace Syl

variable {A} (Y : A.Syl)

theorem mem_NA {p : X} (hp : p ∈ Y.P) : p ∈ A.NA := Y.le_NA hp

theorem t_mem : S.t ∈ Y.P := Y.S₁_le (A.ι_t ▸ A.range_ι ▸ ⟨_, rfl⟩)

theorem u_mem : A.D₁.u ∈ Y.P := Y.S₁_le (A.ι_u ▸ A.range_ι ▸ ⟨_, rfl⟩)

theorem AA_le : A.AA ≤ Y.P := A.AA_le_S₁.trans Y.S₁_le

theorem mem_T_of_comm {p : X} (hp : p ∈ Y.P) (ht : p * S.t = S.t * p) : p ∈ S.data.T := by
  have hP : IsPGroup 2 (Y.P ⊓ centralizer ({S.t} : Set X) : Subgroup X) :=
    Y.isPGroup.to_le inf_le_left
  obtain ⟨h, -, hh⟩ := S.data.exists_conj_le_T hP inf_le_right
  have hTle : S.data.T ≤ Y.P ⊓ centralizer ({S.t} : Set X) :=
    le_inf ((BData.T_le_S₁ A).trans Y.S₁_le) S.data.T_le_centralizer
  have hcard : Nat.card (Y.P ⊓ centralizer ({S.t} : Set X) : Subgroup X) ≤
      Nat.card S.data.T := by
    rw [← card_map_of_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective]
    exact card_le_of_le hh
  have heq := Subgroup.eq_of_le_of_card_ge hTle hcard
  rw [heq]
  exact ⟨hp, mem_centralizer_singleton_iff.mpr ht⟩

theorem mem_S₁_of_normalizes {p : X} (hp : p ∈ Y.P) (hN : p ∈ normalizer (F.E₁ : Set X)) :
    p ∈ A.D₁.S₁ := by
  have hR : IsPGroup 2 (A.D₁.S₁ ⊔ zpowers p : Subgroup X) :=
    Y.isPGroup.to_le (sup_le Y.S₁_le (zpowers_le.mpr hp))
  have hle : A.D₁.S₁ ⊔ zpowers p ≤ normalizer (S.E F.yF : Set X) :=
    sup_le A.D₁.S₁_le (zpowers_le.mpr hN)
  have := A.D₁.S₁_maximal _ hR le_sup_left hle
  rw [← this]
  exact mem_sup_right (mem_zpowers p)

@[expose] def Q : Subgroup X := Y.P ⊓ centralizer (A.AA : Set X)

theorem AA_le_Q : A.AA ≤ Y.Q := le_inf Y.AA_le fun _ hg =>
  mem_centralizer_iff.mpr fun _ hh => A.AA_comm hh hg

theorem mem_AA_of_Q_S₁ {q : X} (hq : q ∈ Y.Q) (hS : q ∈ A.D₁.S₁) : q ∈ A.AA :=
  A.mem_AA_of_S₁ hS hq.2

theorem mem_AA_of_Q_normalizes {q : X} (hq : q ∈ Y.Q) (hN : q ∈ normalizer (F.E₁ : Set X)) :
    q ∈ A.AA :=
  Y.mem_AA_of_Q_S₁ hq (Y.mem_S₁_of_normalizes hq.1 hN)

theorem t_inv_mem_Q : S.t ∈ normalizer (Y.Q : Set X) := by
  rw [mem_normalizer_iff]
  intro q
  have key : ∀ g : X, g ∈ Y.Q → S.t * g * S.t⁻¹ ∈ Y.Q := fun g hg => by
    rw [Q, mem_inf] at hg ⊢
    refine ⟨mul_mem (mul_mem Y.t_mem hg.1) (inv_mem Y.t_mem), ?_⟩
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨v, rfl⟩ := A.mem_AA.mp ha
    have h1 := mem_centralizer_iff.mp hg.2 _ (A.Φ_mem (-v))
    have hinv : S.t⁻¹ * A.Φ v * S.t = A.Φ (-v) := by
      have := A.t_conj_Φ v
      rw [show S.t⁻¹ = S.t by rw [inv_eq_iff_mul_eq_one, t_mul_t]] at this ⊢
      exact this
    calc A.Φ v * (S.t * g * S.t⁻¹) = S.t * ((S.t⁻¹ * A.Φ v * S.t) * g) * S.t⁻¹ := by group
      _ = S.t * (g * (S.t⁻¹ * A.Φ v * S.t)) * S.t⁻¹ := by rw [hinv, h1]
      _ = S.t * g * S.t⁻¹ * A.Φ v := by group
  refine ⟨key q, fun h => ?_⟩
  have := key _ h
  rwa [show S.t⁻¹ = S.t by rw [inv_eq_iff_mul_eq_one, t_mul_t],
    show S.t * (S.t * q * S.t) * S.t = q by rw [← mul_assoc, ← mul_assoc, t_mul_t, one_mul,
      mul_assoc, t_mul_t, mul_one]] at this

theorem pow_four (hnc : ¬ SubConj F.E₁ F.E₂) {q : X} (hq : q ∈ Y.Q) (hqA : q ∉ A.AA)
    {v : Fin 3 → ZMod 4} (hv : q * S.t * q⁻¹ = S.t * A.Φ v) :
    q ^ 2 ∈ A.AA ∧ q ^ 4 = F.kF := by
  obtain ⟨h0, h1⟩ := A.two_mul_of_conj_t hnc hq.2 hv
  have h2 : 2 * v 2 ≠ 0 := by
    intro h2
    apply hqA
    refine Y.mem_AA_of_Q_normalizes hq (A.mem_normalizer_E₁ hq.2 hv fun i => ?_)
    fin_cases i <;> assumption
  have hqΦ : q * A.Φ v * q⁻¹ = A.Φ v := by
    rw [(mem_centralizer_iff.mp hq.2 _ (A.Φ_mem v)).symm, mul_inv_cancel_right]
  have hv2 : q ^ 2 * S.t * (q ^ 2)⁻¹ = S.t * A.Φ (v + v) := by
    rw [A.Φ_add]
    calc q ^ 2 * S.t * (q ^ 2)⁻¹ = q * (q * S.t * q⁻¹) * q⁻¹ := by rw [pow_two]; group
      _ = q * (S.t * A.Φ v) * q⁻¹ := by rw [hv]
      _ = (q * S.t * q⁻¹) * (q * A.Φ v * q⁻¹) := by group
      _ = S.t * A.Φ v * A.Φ v := by rw [hv, hqΦ]
      _ = S.t * (A.Φ v * A.Φ v) := by group
  have hq2 : q ^ 2 ∈ Y.Q := pow_mem hq 2
  have hq2A : q ^ 2 ∈ A.AA := by
    refine Y.mem_AA_of_Q_normalizes hq2 (A.mem_normalizer_E₁ hq2.2 hv2 fun i => ?_)
    simp only [Pi.add_apply]
    exact four_mul_zmod4 (v i)
  refine ⟨hq2A, ?_⟩
  obtain ⟨w, hw⟩ := A.mem_AA.mp hq2A
  have htq : S.t⁻¹ * q * S.t = A.Φ v * q := by
    have : q * S.t = S.t * A.Φ v * q := by rw [← hv]; group
    calc S.t⁻¹ * q * S.t = S.t⁻¹ * (q * S.t) := by group
      _ = A.Φ v * q := by rw [this]; group
  have hcomm : A.Φ v * q = q * A.Φ v := by
    rw [mem_centralizer_iff.mp hq.2 _ (A.Φ_mem v)]
  have htq2 : S.t⁻¹ * q ^ 2 * S.t = A.Φ (v + v) * q ^ 2 := by
    rw [A.Φ_add, pow_two,
      show S.t⁻¹ * (q * q) * S.t = (S.t⁻¹ * q * S.t) * (S.t⁻¹ * q * S.t) by group, htq,
      show A.Φ v * q * (A.Φ v * q) = A.Φ v * (q * A.Φ v) * q by group, ← hcomm]
    group
  have ht' : S.t⁻¹ = S.t := by rw [inv_eq_iff_mul_eq_one, t_mul_t]
  have hinv : S.t⁻¹ * A.Φ w * S.t = A.Φ (-w) := by
    have := A.t_conj_Φ w
    rw [ht'] at this ⊢
    exact this
  rw [← hw, hinv] at htq2
  have hw2 : -w = (v + v) + w := A.Φ_injective (by rw [htq2, A.Φ_add (v + v) w])
  have hww : w + w = ![0, 0, 2] := by
    funext i
    have := congrFun hw2 i
    simp only [Pi.add_apply, Pi.neg_apply] at this
    fin_cases i
    · exact zmod4_aux₀ _ _ this h0
    · exact zmod4_aux₀ _ _ this h1
    · exact zmod4_aux₂ _ _ this h2
  rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, ← hw, ← A.Φ_add, hww, A.Φ_k]

end Syl

end BData

end Sec8

end CFSG.ComponentClassification.HSFLit
