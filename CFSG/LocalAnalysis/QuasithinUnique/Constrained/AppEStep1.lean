module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEKFacts
public import CFSG.Quasithin.Background.C2Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppERed

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {n : ℕ} {t : G}

omit [Finite G] in
theorem iSup_fin_two_eq' (f : Fin 2 → Subgroup G) : (⨆ i, f i) = f 0 ⊔ f 1 :=
  le_antisymm (iSup_le fun i => by fin_cases i <;> simp) (sup_le (le_iSup f 0) (le_iSup f 1))

namespace Dbl

variable (D : Dbl T M H S L n t)
include D

theorem t_normalizer_baum : t ∈ normalizer (baum S : Set G) :=
  normalizer_le_normalizer_baum S (Subgroup.le_normalizer D.ht)

theorem U_cases {g : G} (hg : g ∈ S) :
    conjSubgroup (blockU L) g = blockU L ∨
      conjSubgroup (blockU L) g = conjSubgroup (blockU L) t := by
  rcases D.conjR_cases hg with h | h
  · left
    have := blockU_conjR L g
    rw [h] at this
    exact this.symm
  · right
    have h1 := blockU_conjR L g
    have h2 := blockU_conjR L t
    rw [h] at h1
    exact h1.symm.trans h2

theorem conj_t_Q : conjSubgroup (conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t) t =
    baum S ⊓ centralizer (blockU L : Set G) := by
  rw [conjSubgroup_conjSubgroup]
  have hS : t * t ∈ normalizer (S : Set G) := Subgroup.le_normalizer (S.mul_mem D.ht D.ht)
  have hB : t * t ∈ normalizer (baum S : Set G) := normalizer_le_normalizer_baum S hS
  have hU : t * t ∈ normalizer (blockU L : Set G) :=
    C1.mem_normalizer_blockU (R1_le_normalizer_L D.t_sq_mem)
  exact C5.conjSubgroup_eq_self (C5.mem_normalizer_inf hB (C5.mem_normalizer_centralizer hU))

theorem CS_U_eq : S ⊓ centralizer ((blockU L ⊔ conjSubgroup (blockU L) t : Subgroup G) : Set G) =
    pCoreOf 2 H := by
  have hLb : IsBlock2 H L := D.hcs.block.1
  have hL : ∀ i : Fin 2, IsBlock2 H (![L, conjR L t] i) := by
    intro i
    fin_cases i
    · exact hLb
    · exact CFSG.Quasithin.IsBlock2.conjByElt_of_mem hLb (H.inv_mem (D.hcs.sylow.le D.ht))
  have hcomm : ∀ i j : Fin 2, i ≠ j → ⁅(![L, conjR L t] i), (![L, conjR L t] j)⁆ = ⊥ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact D.hcomm
    · rw [Subgroup.commutator_comm]; exact D.hcomm
    · exact absurd rfl hij
  have hperm : ∀ g ∈ S, ∀ i : Fin 2, ∃ j : Fin 2,
      conjSubgroup (![L, conjR L t] i) g = ![L, conjR L t] j := by
    intro g hg i
    fin_cases i
    · rcases D.conjR_cases hg with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · rcases D.conjR_L₂_cases hg with h | h
      · exact ⟨1, h.2⟩
      · exact ⟨0, h.2⟩
  have hKT : (⨆ i : Fin 2, ![L, conjR L t] i) ⊔ S = H := by
    rw [iSup_fin_two_eq']
    show L ⊔ conjR L t ⊔ S = H
    rw [← D.hjoin, ← D.hcs.eq_join]
  have := Setup.Campbell.commuting_short_product_core_centralizer D.hcs.sylow (s := 2)
    (by norm_num) ![L, conjR L t] hL hcomm hperm hKT
  have hU : (⨆ i : Fin 2, blockU (![L, conjR L t] i)) =
      blockU L ⊔ conjSubgroup (blockU L) t := by
    rw [iSup_fin_two_eq']
    show blockU L ⊔ blockU (conjR L t) = _
    rw [blockU_conjR]
    rfl
  have h6 := this.2.2.2.2.2.1
  rw [hU] at h6
  exact h6

theorem exists_good {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2)
    {q : ℕ} {W : Subgroup G}
    (hl : Loc (baum S) L (blockU L) (baum S ⊓ centralizer (blockU L : Set G)) W q) :
    ∃ x ∈ M₀, x ∉ S ∧
      ¬ conjSubgroup (blockU L) x ≤ baum S ⊓ centralizer (blockU L : Set G) := by
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  by_cases h : conjSubgroup (blockU L) x₀ ≤ baum S ⊓ centralizer (blockU L : Set G)
  swap
  · exact ⟨x₀, hx₀, hx₀S, h⟩
  refine ⟨x₀ * t⁻¹, M₀.mul_mem hx₀ (M₀.inv_mem (hSM D.ht)), ?_, ?_⟩
  · intro hS
    apply hx₀S
    have := S.mul_mem hS D.ht
    simpa using this
  · intro hle
    have hl₂ := hl.conj D.t_normalizer_baum
    rw [← conjSubgroup_conjSubgroup] at hle
    have h3 := conjSubgroup_mono hle t
    rw [C5.conjSubgroup_inv_conjSubgroup] at h3
    have h4 : conjSubgroup (blockU L) x₀ ≤ pCoreOf 2 H := by
      intro a ha
      have ha₁ := h ha
      have ha₂ : a ∈ baum S ⊓ centralizer (conjSubgroup (blockU L) t : Set G) := by
        have := h3 ha
        rwa [hl₂.rk.Q_eq] at this
      rw [← D.CS_U_eq]
      exact ⟨(inf_le_left : baum S ≤ S) ha₁.1,
        C56.mem_centralizer_sup (fun v hv => Subgroup.mem_centralizer_iff.1 ha₁.2 v hv)
          (fun v hv => Subgroup.mem_centralizer_iff.1 ha₂.2 v hv)⟩
    exact C56.not_conj_le_of_mem_diff D.hcs hSM hMT h2 hx₀ hx₀S h4

end Dbl

structure Setup (T M H S L : Subgroup G) (n : ℕ) (t : G) (M₀ : Subgroup G) (x : G) (q : ℕ)
    (W : Subgroup G) : Prop where
  D : Dbl T M H S L n t
  hSM : S ≤ M₀
  hMT : M₀ ≤ T
  h2 : S.relIndex M₀ = 2
  hx : x ∈ M₀
  hxS : x ∉ S
  loc : Loc (baum S) L (blockU L) (baum S ⊓ centralizer (blockU L : Set G)) W q
  good : ¬ conjSubgroup (blockU L) x ≤ baum S ⊓ centralizer (blockU L : Set G)

namespace Setup

variable {M₀ : Subgroup G} {x : G} {q : ℕ} {W : Subgroup G}
  (P : Setup T M H S L n t M₀ x q W)
include P

theorem hxN : x ∈ normalizer (S : Set G) := normalizer_of_relIndex_two P.hSM P.h2 P.hx

theorem hxB : x ∈ normalizer (baum S : Set G) := normalizer_le_normalizer_baum S P.hxN

theorem hxsq : x * x ∈ S := mul_self_mem_of_relIndex_two P.h2 P.hx P.hxS

theorem loc₂ : Loc (baum S) (conjSubgroup L t) (conjSubgroup (blockU L) t)
    (conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t) (conjSubgroup W t) q :=
  P.loc.conj P.D.t_normalizer_baum

theorem kf₁ : KFacts (baum S) L (blockU L) (baum S ⊓ centralizer (blockU L : Set G)) W x :=
  P.loc.kfacts P.hxB P.good

theorem U₁_le_L : blockU L ≤ L := P.loc.hUL

theorem U₂_le_L₂ : conjSubgroup (blockU L) t ≤ conjSubgroup L t :=
  conjSubgroup_mono P.loc.hUL t

theorem U₂_le_Q₁ : conjSubgroup (blockU L) t ≤ baum S ⊓ centralizer (blockU L : Set G) := by
  intro u hu
  refine ⟨P.loc₂.rk.U_le_B hu, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact P.D.comm_elem v (P.U₁_le_L hv) u (P.U₂_le_L₂ hu)

theorem Ux_le_Q₂ : conjSubgroup (blockU L) x ≤
    conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t := by
  have hl2 := P.loc₂
  have kf := P.kf₁
  intro a ha
  by_contra haQ
  have haB : a ∈ baum S := kf.Ux_le_B ha
  have hnorm : a ∈ normalizer (conjSubgroup (blockU L) t : Set G) := hl2.rk.B_le_normU haB
  have hcomm : ∀ u ∈ conjSubgroup (blockU L) t, u * a = a * u := by
    intro u hu
    have hmemU₂ : ⁅u, a⁆ ∈ conjSubgroup (blockU L) t := by
      have h1 : a * u⁻¹ * a⁻¹ ∈ conjSubgroup (blockU L) t :=
        (Subgroup.mem_normalizer_iff.1 hnorm u⁻¹).1 (Subgroup.inv_mem _ hu)
      have : ⁅u, a⁆ = u * (a * u⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact Subgroup.mul_mem _ hu h1
    have hxnorm : u ∈ normalizer (conjSubgroup (blockU L) x : Set G) :=
      P.loc.rk.B_le_normU_conj P.hxB (hl2.rk.U_le_B hu)
    have hmemX : ⁅u, a⁆ ∈ conjSubgroup (blockU L) x := by
      have h1 : u * a * u⁻¹ ∈ conjSubgroup (blockU L) x :=
        (Subgroup.mem_normalizer_iff.1 hxnorm a).1 ha
      have : ⁅u, a⁆ = (u * a * u⁻¹) * a⁻¹ := commutatorElement_def u a
      rw [this]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ha)
    have hW : ⁅u, a⁆ ∈ W := by
      have : ⁅u, a⁆ ∈ conjSubgroup (blockU L) x ⊓ (baum S ⊓ centralizer (blockU L : Set G)) :=
        ⟨hmemX, P.U₂_le_Q₁ hmemU₂⟩
      rwa [kf.infQ] at this
    have hU₁ : ⁅u, a⁆ ∈ blockU L := P.loc.rk.W_le_U hW
    have hCL₂ : ⁅u, a⁆ ∈ centralizer ((conjSubgroup L t : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (P.D.comm_elem _ (P.U₁_le_L hU₁) v hv).symm
    have h1 := hl2.hcommZ a haB haQ u hu ⟨hmemU₂, hCL₂⟩
    have h2 := commutatorElement_eq_one_iff_mul_comm.1 h1
    exact h2
  exact haQ (by
    rw [hl2.rk.Q_eq]
    exact ⟨haB, Subgroup.mem_centralizer_iff.mpr hcomm⟩)

theorem Ux_t : conjSubgroup (conjSubgroup (blockU L) x) t =
    conjSubgroup (conjSubgroup (blockU L) t) x := by
  have hs' : x * t * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 P.hxN t).1 P.D.ht
  have e1 : conjSubgroup (conjSubgroup (blockU L) x) t =
      conjSubgroup (conjSubgroup (blockU L) (x * t * x⁻¹)) x := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, inv_mul_cancel_right]
  rw [e1]
  rcases P.D.U_cases hs' with h | h
  · exfalso
    rw [h] at e1
    have h3 := conjSubgroup_mono P.Ux_le_Q₂ t
    rw [e1, P.D.conj_t_Q] at h3
    exact P.good h3
  · rw [h]

theorem good₂ : ¬ conjSubgroup (conjSubgroup (blockU L) t) x ≤
    conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t := by
  intro h
  rw [← P.Ux_t] at h
  exact P.good (conjSubgroup_le_iff.1 h)

theorem kf₂ : KFacts (baum S) (conjSubgroup L t) (conjSubgroup (blockU L) t)
    (conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t) (conjSubgroup W t) x :=
  P.loc₂.kfacts P.hxB P.good₂

theorem U₂x_le_Q₁ : conjSubgroup (conjSubgroup (blockU L) t) x ≤
    baum S ⊓ centralizer (blockU L : Set G) := by
  rw [← P.Ux_t]
  have h3 := conjSubgroup_mono P.Ux_le_Q₂ t
  rwa [P.D.conj_t_Q] at h3

end Setup

end CFSG.QuasithinUnique.AppE
