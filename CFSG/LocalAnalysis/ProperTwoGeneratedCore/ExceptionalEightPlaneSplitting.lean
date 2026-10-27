module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneDichotomy
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

variable {Y : Type*} [Group Y]

namespace PlaneHyp

variable {U B : Subgroup Y} {b₁ b₂ u₀ c₁ c₂ : Y} [U.Normal] [IsElementaryAbelian 2 U]
  (h : PlaneHyp U B b₁ b₂ u₀) (hl : PlaneLifts B b₁ b₂ u₀ c₁ c₂)
include h hl

theorem exists_complement_of_elementary [Finite Y] (hel : ∀ d ∈ planeD B c₁ c₂, d * d = 1) :
    ∃ K : Subgroup Y, U ⊓ K = ⊥ ∧ U ⊔ K = ⊤ := by
  classical
  have hb₁U := h.b₁_mem_U
  have hb₂U := h.b₂_mem_U
  have hc₁D := c₁_mem_planeD hl
  have hc₂D := c₂_mem_planeD hl
  have hu₀1 : u₀ ≠ 1 := fun e => h.u₀_not_mem (e ▸ B.one_mem)
  have hu₀b₁ : u₀ ≠ b₁ := fun e => h.u₀_not_mem (e ▸ h.b₁_mem)
  have hu₀b₂ : b₂ ≠ u₀ := fun e => h.u₀_not_mem (e ▸ h.b₂_mem)
  have hb₂b₁u₀ : b₂ ≠ b₁ * u₀ := by
    intro e
    apply h.u₀_not_mem
    have : u₀ = b₁⁻¹ * b₂ := by rw [e]; group
    rw [this]
    exact B.mul_mem (B.inv_mem h.b₁_mem) h.b₂_mem
  let x' : Fin 3 → U := ![⟨b₁, hb₁U⟩, ⟨u₀, h.u₀_mem⟩, ⟨b₂, hb₂U⟩]
  have hval : ∀ {a b : U}, (a : Y) ≠ b → a ≠ b := fun hab e => hab (congrArg Subtype.val e)
  have hx' : Independent x' := by
    refine independent_of_ne ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hval (a := x' 0) (b := 1) h.b₁_ne_one
    · exact hval (a := x' 1) (b := 1) hu₀1
    · exact hval (a := x' 1) (b := x' 0) hu₀b₁
    · exact hval (a := x' 2) (b := 1) h.b₂_ne_one
    · exact hval (a := x' 2) (b := x' 0) h.b₂_ne_b₁
    · exact hval (a := x' 2) (b := x' 1) hu₀b₂
    · exact hval (a := x' 2) (b := x' 0 * x' 1) hb₂b₁u₀
  obtain ⟨y, hy⟩ := h.full (basisAut h.basis_independent hx' h.card_U)
  have hσ : ∀ i, ((basisAut h.basis_independent hx' h.card_U (h.basis i) : U) : Y) =
      (x' i : Y) := fun i => by rw [basisAut_apply]
  have hyb₁ : y * b₁ * y⁻¹ = b₁ := by
    have := (hy (h.basis 0)).symm.trans (hσ 0)
    simpa [basis, x'] using this
  have hyb₂ : y * b₂ * y⁻¹ = u₀ := by
    have := (hy (h.basis 1)).symm.trans (hσ 1)
    simpa [basis, x'] using this
  have hyu₀ : y * u₀ * y⁻¹ = b₂ := by
    have := (hy (h.basis 2)).symm.trans (hσ 2)
    simpa [basis, x'] using this
  have hyb₁' : y⁻¹ * b₁ * y = b₁ := by
    calc y⁻¹ * b₁ * y = y⁻¹ * (y * b₁ * y⁻¹) * y := by rw [hyb₁]
      _ = b₁ := by group
  have hyb₂' : y⁻¹ * b₂ * y = u₀ := by
    calc y⁻¹ * b₂ * y = y⁻¹ * (y * u₀ * y⁻¹) * y := by rw [hyu₀]
      _ = u₀ := by group
  obtain ⟨t, ht⟩ : ∃ t : Y, t = y * c₁ * y⁻¹ := ⟨_, rfl⟩
  have htt : t * t = 1 := by
    rw [ht, show y * c₁ * y⁻¹ * (y * c₁ * y⁻¹) = y * (c₁ * c₁) * y⁻¹ by group, hel c₁ hc₁D]
    group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hc₁b₁ : c₁ * b₁ * c₁⁻¹ = b₁ := conj_eq_of_mem_centralizer hl.c₁_mem h.b₁_mem
  have hc₁u₀ : c₁ * u₀ * c₁⁻¹ = u₀ * b₁ := by rw [h.conj_u₀ c₁, hl.tau₁]
  have htb₁ : t * b₁ * t⁻¹ = b₁ := by
    calc t * b₁ * t⁻¹ = y * (c₁ * (y⁻¹ * b₁ * y) * c₁⁻¹) * y⁻¹ := by rw [ht]; group
      _ = b₁ := by rw [hyb₁', hc₁b₁, hyb₁]
  have htb₂ : t * b₂ * t⁻¹ = b₁ * b₂ := by
    calc t * b₂ * t⁻¹ = y * (c₁ * (y⁻¹ * b₂ * y) * c₁⁻¹) * y⁻¹ := by rw [ht]; group
      _ = y * (u₀ * b₁) * y⁻¹ := by rw [hyb₂', hc₁u₀]
      _ = (y * u₀ * y⁻¹) * (y * b₁ * y⁻¹) := by group
      _ = b₁ * b₂ := by rw [hyu₀, hyb₁, mul_comm_of_mem hb₂U hb₁U]
  have htB : ∀ z ∈ B, t * z * t⁻¹ ∈ B := by
    intro z hz
    rcases h.mem_B_cases hz with rfl | rfl | rfl | rfl
    · rw [mul_one, mul_inv_cancel]; exact B.one_mem
    · rw [htb₁]; exact h.b₁_mem
    · rw [htb₂]; exact B.mul_mem h.b₁_mem h.b₂_mem
    · rw [show t * (b₁ * b₂) * t⁻¹ = (t * b₁ * t⁻¹) * (t * b₂ * t⁻¹) by group, htb₁, htb₂,
        ← mul_assoc, mul_self_eq_one_of_mem hb₁U, one_mul]
      exact h.b₂_mem
  have htN : t ∈ Subgroup.normalizer (B : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨htB z, fun hz => ?_⟩
    have := htB _ hz
    rwa [htinv, show t * (t * z * t) * t = (t * t) * z * (t * t) by group, htt, one_mul,
      mul_one] at this
  have htC : t ∉ Subgroup.centralizer (B : Set Y) := by
    intro htC'
    have := conj_eq_of_mem_centralizer htC' h.b₂_mem
    rw [htb₂] at this
    exact h.b₁_ne_one (left_eq_mul.mp
      ((mul_comm_of_mem hb₁U hb₂U).symm.trans this).symm)
  obtain ⟨d', hd'⟩ : ∃ d' : Y, d' = t * c₂ * t⁻¹ := ⟨_, rfl⟩
  have hd'D : d' ∈ planeD B c₁ c₂ := hd' ▸ h.conj_mem_planeD hl htN hc₂D
  have hτd' : planeTau u₀ d' = b₁ * b₂ := by
    rw [hd', h.planeTau_conj htN hl.c₂_mem, hl.tau₂, htb₂]
  have hc₂c₂ : c₂ * c₂ = 1 := hel c₂ hc₂D
  have hd'd' : d' * d' = 1 := hel d' hd'D
  have hc₂d' : c₂ * d' = d' * c₂ := h.planeD_comm hl hc₂D hd'D
  have hc₂inv : c₂⁻¹ = c₂ := inv_eq_of_mul_eq_one_right hc₂c₂
  have hd'eq : d' = t * c₂ * t := by rw [hd', htinv]
  obtain ⟨r, hr⟩ : ∃ r : Y, r = c₂ * t := ⟨_, rfl⟩
  have hrr : r * r = c₂ * d' := by rw [hr, hd'eq]; group
  have hr4 : r ^ 4 = 1 := by
    calc r ^ 4 = r * r * (r * r) := by rw [pow_succ, pow_succ, pow_succ, pow_one, mul_assoc]
      _ = 1 := by rw [hrr, mul_mul_self_of_commute hc₂d', hc₂c₂, hd'd', one_mul]
  have hrel : t * r * t = r⁻¹ := by
    rw [hr, mul_inv_rev, htinv, hc₂inv]
    calc t * (c₂ * t) * t = t * c₂ * (t * t) := by group
      _ = t * c₂ := by rw [htt, mul_one]
  let φ := CFSG.Semidihedral.Principal.dihedralWordHom r t 4 hr4 htt hrel
  have hφr : ∀ i : ZMod 4, φ (DihedralGroup.r i) = r ^ i.val := fun i => rfl
  have hφsr : ∀ i : ZMod 4, φ (DihedralGroup.sr i) = t * r ^ i.val := fun i => rfl
  have hUC := h.U_le_centralizer
  have hc₂C := hl.c₂_mem
  have hd'C := planeD_le_centralizer B c₁ c₂ hd'D
  have hnot₁ : ∀ x ∈ Subgroup.centralizer (B : Set Y), x * t ∉ U := by
    intro x hx hxt
    apply htC
    have : t = x⁻¹ * (x * t) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) (hUC hxt)
  have hnot₂ : ∀ x ∈ Subgroup.centralizer (B : Set Y), t * x ∉ U := by
    intro x hx htx
    apply htC
    have : t = (t * x) * x⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (hUC htx) (Subgroup.inv_mem _ hx)
  have hτne : ∀ x ∈ Subgroup.centralizer (B : Set Y), planeTau u₀ x ≠ 1 → x ∉ U := by
    intro x _ hτ hxU
    exact hτ (h.planeTau_of_mem_U hxU)
  have hb₁₂1 : b₁ * b₂ ≠ 1 := by
    intro e
    apply h.b₂_ne_b₁
    have := eq_inv_of_mul_eq_one_right e
    rwa [inv_eq_self_of_mem hb₁U] at this
  have hτc₂d' : planeTau u₀ (c₂ * d') = b₁ := by
    rw [h.planeTau_mul hc₂C hd'C, hl.tau₂, hτd', ← mul_assoc, mul_comm_of_mem hb₂U hb₁U,
      mul_assoc, mul_self_eq_one_of_mem hb₂U, mul_one]
  have hc₂d'C : c₂ * d' ∈ Subgroup.centralizer (B : Set Y) := Subgroup.mul_mem _ hc₂C hd'C
  have hz4 : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  have hr2 : r ^ 2 = c₂ * d' := by rw [pow_two, hrr]
  have hr3 : r ^ 3 = c₂ * d' * c₂ * t := by
    rw [pow_succ, hr2, hr]
    group
  have hφU : ∀ g : DihedralGroup 4, φ g ∈ U → g = 1 := by
    intro g hg
    cases g with
    | r i =>
      rw [hφr] at hg
      rcases hz4 i with rfl | rfl | rfl | rfl
      · rfl
      · rw [show (1 : ZMod 4).val = 1 from rfl, pow_one, hr] at hg
        exact absurd hg (hnot₁ c₂ hc₂C)
      · rw [show (2 : ZMod 4).val = 2 from rfl, hr2] at hg
        exact absurd hg (hτne _ hc₂d'C (by rw [hτc₂d']; exact h.b₁_ne_one))
      · rw [show (3 : ZMod 4).val = 3 from rfl, hr3] at hg
        exact absurd hg (hnot₁ _ (Subgroup.mul_mem _ hc₂d'C hc₂C))
    | sr i =>
      exfalso
      rw [hφsr] at hg
      rcases hz4 i with rfl | rfl | rfl | rfl
      · rw [show (0 : ZMod 4).val = 0 from rfl, pow_zero, mul_one] at hg
        exact hnot₂ 1 (Subgroup.one_mem _) (by rwa [mul_one])
      · rw [show (1 : ZMod 4).val = 1 from rfl, pow_one, hr,
          show t * (c₂ * t) = t * c₂ * t by group, ← hd'eq] at hg
        exact hτne _ hd'C (by rw [hτd']; exact hb₁₂1) hg
      · rw [show (2 : ZMod 4).val = 2 from rfl, hr2] at hg
        exact hnot₂ _ hc₂d'C hg
      · rw [show (3 : ZMod 4).val = 3 from rfl, hr3] at hg
        have heq : t * (c₂ * d' * c₂ * t) = c₂ := by
          calc t * (c₂ * d' * c₂ * t) = t * (d' * (c₂ * c₂)) * t := by
                rw [hc₂d']; group
            _ = t * (t * c₂ * t) * t := by rw [hc₂c₂, mul_one, hd'eq]
            _ = (t * t) * c₂ * (t * t) := by group
            _ = c₂ := by rw [htt, one_mul, mul_one]
        rw [heq] at hg
        exact hτne _ hc₂C (by rw [hl.tau₂]; exact h.b₂_ne_one) hg
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact hφU g (by rw [hg]; exact U.one_mem)
  set K := φ.range with hK
  have hUK : U ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, g, rfl⟩
    rw [hφU g hxU, map_one]
    exact Subgroup.one_mem _
  have hKcard : Nat.card K = 8 := by
    rw [hK, ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, DihedralGroup.nat_card]
  have hTcard : Nat.card (U ⊔ K : Subgroup Y) = 64 := by
    rw [card_sup_of_normal_of_inf_eq_bot U K hUK, h.card_U, hKcard]
  have hTindex : (U ⊔ K).index = 21 := by
    have := (U ⊔ K).card_mul_index
    rw [hTcard, h.card_Y] at this
    omega
  have hcop : Nat.Coprime (U ⊔ K).index (Nat.card U) := by
    rw [hTindex, h.card_U]
    norm_num
  obtain ⟨D', -, hUD', hUD'sup⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting U (U ⊔ K) K hcop hUK rfl
  exact ⟨D', hUD', hUD'sup⟩

end PlaneHyp

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
