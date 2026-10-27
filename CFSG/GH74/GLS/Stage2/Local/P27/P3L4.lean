module

public import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg
public import CFSG.GH74.GLS.Stage2.Local.P27.P3Transfer
public import CFSG.GH74.GLS.Stage2.Local.P27.P3Extremal

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Basic

omit [Finite G] in
theorem isCentralInvolution_of_isConj_P27 {z y : G} (hz : IsCentralInvolution z) (h : IsConj z y) :
    IsCentralInvolution y := by
  obtain ⟨hord, S₀, hzS, hzc⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, c • S₀, ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hord
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z, hzS, by rw [← hc]; rfl⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hzc s' hs'
    rw [← hc]
    show (c * s' * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * s' * c⁻¹)
    calc (c * s' * c⁻¹) * (c * z * c⁻¹) = c * (s' * z) * c⁻¹ := by group
      _ = c * (z * s') * c⁻¹ := by rw [this]
      _ = (c * z * c⁻¹) * (c * s' * c⁻¹) := by group

end Basic

section Main

theorem fusion_of_extremal {z x t' : G} {T D₁ D₂ U : Subgroup G} {q n : ℕ}
    (hcfg : Cfg z x T q) (hsyl : Syl z x T D₁ D₂ U n t')
    (hD₂cl : ∀ s ∈ D₂, orderOf s = 2 → IsConj x s)
    (hxD : x ∈ ⁅D₁, D₁⁆)
    (hΩ : ∀ y ∈ ⁅T, T⁆, y * y = 1 → y = 1 ∨ y = x ∨ y = t' ∨ y = x * t') :
    ∀ s ∈ D₂, orderOf s = 2 → ∃ c ∈ centralizer ({x} : Set G), c * t' * c⁻¹ = s := by
  have hx2 : orderOf x = 2 := hcfg.x_nc.1
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  have ht'c : ∀ y ∈ T, t' * y = y * t' := by
    have hmem : t' ∈ (center ↥T).map T.subtype := by
      rw [hsyl.center_T]
      exact Subgroup.mem_sup_right (mem_zpowers t')
    obtain ⟨c, hc, hct⟩ := hmem
    intro y hy
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at this
    have hct' : (c : G) = t' := hct
    rw [hct'] at this
    exact this.symm
  have hnc : ¬ IsConj x (x * t') := by
    intro h
    exact hcfg.x_nc.2 (isCentralInvolution_of_isConj_P27 hcfg.z_central (hsyl.xt'_conj.trans h.symm))
  intro s hs hs2
  have hxs : x ≠ s := by
    intro h
    have hm : x ∈ D₁ ⊓ D₂ := ⟨hsyl.x_mem, h ▸ hs⟩
    rw [hsyl.inter] at hm
    exact hx1 (Subgroup.mem_bot.1 hm)
  exact exists_conj_centralizer_of_extremal hcfg.T_syl hsyl.t'_conj ht'c
    hsyl.D₁_le hxD hx1 hxx ((hD₂cl s hs hs2).symm.trans hsyl.t'_conj)
    (fun a ha => (hsyl.comm a ha s hs).symm) hxs hΩ hnc

theorem tr_of_l4 {z x t' : G} {T D₁ D₂ U T₁ : Subgroup G} {q n : ℕ}
    (hcfg : Cfg z x T q) (hsyl : Syl z x T D₁ D₂ U n t')
    (hT : T ≤ D₁ ⊔ D₂)
    (hT₁le : T₁ ≤ D₁) (hT₁cyc : IsCyclic ↥T₁) (hx₁ : x ∈ T₁) (hT₁idx : T₁.relIndex D₁ = 2)
    (hT₁card : Nat.card ↥T₁ * 2 = Nat.card ↥D₂)
    (hrefl : ∀ a ∈ D₁, a ∉ T₁ → a * a = 1)
    (hsepc : ∀ a ∈ D₁, a ∉ T₁ → ∀ m ∈ T₁ ⊔ D₂, m * m = 1 → m ≠ 1 → m ≠ x →
      ¬ ((IsConj z a ↔ IsConj z m) ∧ (IsConj z (x * a) ↔ IsConj z (x * m))))
    (hD₂cl : ∀ s ∈ D₂, orderOf s = 2 → IsConj x s)
    (hD₂gen : D₂ ≤ closure {s | s ∈ D₂ ∧ orderOf s = 2})
    (hxD : x ∈ ⁅D₁, D₁⁆)
    (hΩ : ∀ y ∈ ⁅T, T⁆, y * y = 1 → y = 1 ∨ y = x ∨ y = t' ∨ y = x * t')
    (hI : Ixz z x ≤ Jx x) (hJ : ⁅Jx x, Jx x⁆ = Jx x) (hJX : Jx x ≤ centralizer ({x} : Set G)) :
    Tr z x T D₁ D₂ U T₁ := by
  have hx2 : orderOf x = 2 := hcfg.x_nc.1
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  have hTX : T ≤ centralizer ({x} : Set G) := hcfg.T_syl.le
  have ht'c : ∀ y ∈ T, t' * y = y * t' := by
    have hmem : t' ∈ (center ↥T).map T.subtype := by
      rw [hsyl.center_T]
      exact Subgroup.mem_sup_right (mem_zpowers t')
    obtain ⟨c, hc, hct⟩ := hmem
    intro y hy
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at this
    have hct' : (c : G) = t' := hct
    rw [hct'] at this
    exact this.symm
  have hnc : ¬ IsConj x (x * t') := by
    intro h
    exact hcfg.x_nc.2 (isCentralInvolution_of_isConj_P27 hcfg.z_central (hsyl.xt'_conj.trans h.symm))
  have ht'J : t' ∈ Jx x := hI (hsyl.U_syl.le hsyl.t'_U)
  have hJc : Jx x ≤ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆ := by
    calc Jx x = ⁅Jx x, Jx x⁆ := hJ.symm
      _ ≤ _ := Subgroup.commutator_mono hJX hJX
  have ht'X : t' ∈ centralizer ({x} : Set G) := hTX (hsyl.D₂_le hsyl.t'_mem)
  have hinvol : ∀ s ∈ D₂, orderOf s = 2 → s ∈ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆ := by
    intro s hs hs2
    obtain ⟨c, hcX, hc⟩ := fusion_of_extremal hcfg hsyl hD₂cl hxD hΩ s hs hs2
    rw [← hc]
    have hct' : c * t' * c⁻¹ = ⁅c, t'⁆ * t' := by
      simp only [commutatorElement_def]
      group
    rw [hct']
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hcX ht'X) (hJc ht'J)
  have hD₂c : D₂ ≤ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆ := fun d hd =>
    (Subgroup.closure_le _).2 (fun s hs => hinvol s hs.1 hs.2) (hD₂gen hd)
  have hTeq : T = D₁ ⊔ D₂ := le_antisymm hT (sup_le hsyl.D₁_le hsyl.D₂_le)
  have hM : (T₁ ⊔ D₂).relIndex T = 2 := by
    rw [hTeq]
    exact relIndex_sup_comm_eq_two hsyl.comm hsyl.inter hT₁le hT₁idx
  have hMP : T₁ ⊔ D₂ ≤ T := sup_le (hT₁le.trans hsyl.D₁_le) hsyl.D₂_le
  have hsep : ∀ a ∈ D₁, a ∉ T₁ → ∀ g ∈ centralizer ({x} : Set G), g⁻¹ * a * g ∈ T →
      g⁻¹ * a * g ∉ T₁ ⊔ D₂ := by
    intro a ha haT g hg _ hgM
    have hg' : x * g = g * x := mem_centralizer_iff.1 hg x rfl
    have hgx : g⁻¹ * x * g = x := by
      rw [mul_assoc, hg', ← mul_assoc]
      simp
    have hconj : IsConj a (g⁻¹ * a * g) := isConj_iff.2 ⟨g⁻¹, by simp⟩
    have e : x * (g⁻¹ * a * g) = g⁻¹ * (x * a) * g := by
      calc x * (g⁻¹ * a * g) = (g⁻¹ * x * g) * (g⁻¹ * a * g) := by rw [hgx]
        _ = g⁻¹ * (x * a) * g := by group
    have hconj' : IsConj (x * a) (x * (g⁻¹ * a * g)) := isConj_iff.2 ⟨g⁻¹, by rw [e]; simp⟩
    have hmm : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
      calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [hrefl a ha haT]; group
    have hm1 : g⁻¹ * a * g ≠ 1 := by
      intro h
      apply haT
      have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      rw [this, h]
      simp
    have hmx : g⁻¹ * a * g ≠ x := by
      intro h
      apply haT
      have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      rw [this, h]
      have : g * x * g⁻¹ = x := by
        calc g * x * g⁻¹ = (g * x) * g⁻¹ := rfl
          _ = (x * g) * g⁻¹ := by rw [← hg']
          _ = x := by group
      rw [this]
      exact hx₁
    refine hsepc a ha haT _ hgM hmm hm1 hmx ⟨?_, ?_⟩
    · exact ⟨fun h => h.trans hconj, fun h => h.trans hconj.symm⟩
    · exact ⟨fun h => h.trans hconj', fun h => h.trans hconj'.symm⟩
  have hS1 := inter_le_of_transfer_amb hcfg.T_syl hJX hsyl.D₁_le hsyl.D₂_le hT hsyl.comm
    le_sup_left le_sup_right hrefl hM hMP hJ hD₂c hsep
  exact ⟨hI, hT₁cyc, hT₁le, hx₁, hT₁card, fun g hg => hS1 hg⟩

end Main

end CFSG.GH74.GLS.Stage2.Local.P27
