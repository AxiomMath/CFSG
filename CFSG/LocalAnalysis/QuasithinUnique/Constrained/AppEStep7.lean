module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEStep6

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {n : ℕ} {t : G}

omit [Finite G] in
theorem sc_conj {R B P : Subgroup G} {g : G}
    (hSC : ∀ r ∈ R, (∀ b ∈ B, ⁅r, b⁆ ∈ P) → r ∈ B ⊔ P)
    (hgR : g ∈ normalizer (R : Set G)) (hgB : g ∈ normalizer (B : Set G))
    (hBP : B ≤ normalizer (P : Set G)) :
    ∀ r ∈ R, (∀ b ∈ B, ⁅r, b⁆ ∈ conjSubgroup P g) → r ∈ B ⊔ conjSubgroup P g := by
  intro r hr h
  have hr' : g * r * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hgR r).1 hr
  have key : ∀ b ∈ B, ⁅g * r * g⁻¹, b⁆ ∈ P := by
    intro b hb
    have hb' : g⁻¹ * b * g ∈ B := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgB) b).1 hb
      simpa using this
    have e : ⁅g * r * g⁻¹, b⁆ = g * ⁅r, g⁻¹ * b * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mem_conjSubgroup_iff.1 (h _ hb')
  obtain ⟨b₂, hb₂, p₂, hp₂, hrr⟩ := C5.mem_sup_of_le_normalizer hBP (hSC _ hr' key)
  have hb₃ : g⁻¹ * b₂ * g ∈ B := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgB) b₂).1 hb₂
    simpa using this
  have hp₃ : g⁻¹ * p₂ * g ∈ conjSubgroup P g := by
    rw [mem_conjSubgroup_iff]; simpa [mul_assoc] using hp₂
  have hpeq : r = (g⁻¹ * b₂ * g) * (g⁻¹ * p₂ * g) := by
    calc r = g⁻¹ * (g * r * g⁻¹) * g := by group
      _ = g⁻¹ * (b₂ * p₂) * g := by rw [hrr]
      _ = (g⁻¹ * b₂ * g) * (g⁻¹ * p₂ * g) := by group
  rw [hpeq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb₃) (Subgroup.mem_sup_right hp₃)

namespace Dbl

variable (D : Dbl T M H S L n t)
include D

theorem S_le_normalizer_R1 : S ≤ normalizer ((R1 S L : Subgroup G) : Set G) := fun _ hg =>
  normalizer_of_relIndex_two R1_le_S D.relIndex_R1 hg

theorem H1_inf_centralizer : H1 S L ⊓ centralizer (blockU L : Set G) = pCoreOf 2 (H1 S L) := by
  have hR2 : IsPGroup 2 (R1 S L) := D.hcs.sylow.isPGroup.to_le R1_le_S
  exact C1.inf_centralizer_blockU_eq D.hL L_le_H1 H1_le_normalizer_L fun _ hg =>
    C1.exists_pow_mem_of_mem_sup hR2 R1_le_normalizer_L hg

theorem SC₁ : ∀ r ∈ R1 S L, (∀ b ∈ baum S, ⁅r, b⁆ ∈ R1 S L ⊓ centralizer (blockU L : Set G)) →
    r ∈ baum S ⊔ (R1 S L ⊓ centralizer (blockU L : Set G)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hSC⟩ := D.naturalConcl
  rw [D.baum_R1_eq] at hSC
  intro r hr h
  have hP₁ : R1 S L ⊓ centralizer (blockU L : Set G) ≤ pCoreOf 2 (H1 S L) := by
    rw [← D.H1_inf_centralizer]
    exact inf_le_inf_right _ R1_le_H1
  have hr' := hSC r hr (fun b hb => hP₁ (h b hb))
  have hBN : baum S ≤ normalizer ((pCoreOf 2 (H1 S L) : Subgroup G) : Set G) := fun g hg =>
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (H1 S L)
      (R1_le_H1 (D.baum_le_R1 hg))
  obtain ⟨b', hb', p', hp', hrbp⟩ := C5.mem_sup_of_le_normalizer hBN hr'
  have hb'R : b' ∈ R1 S L := D.baum_le_R1 hb'
  have hp'R : p' ∈ R1 S L := by
    have : p' = b'⁻¹ * r := by rw [hrbp]; group
    rw [this]
    exact (R1 S L).mul_mem ((R1 S L).inv_mem hb'R) hr
  have hp'C : p' ∈ centralizer (blockU L : Set G) := by
    have : p' ∈ H1 S L ⊓ centralizer (blockU L : Set G) := by
      rw [D.H1_inf_centralizer]; exact hp'
    exact this.2
  rw [hrbp]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb') (Subgroup.mem_sup_right ⟨hp'R, hp'C⟩)

theorem conj_P₁_t : conjSubgroup (R1 S L ⊓ centralizer (blockU L : Set G)) t =
    R1 S L ⊓ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) := by
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_eq_self (D.S_le_normalizer_R1 D.ht),
    C5.conjSubgroup_centralizer]

theorem SC₂ : ∀ r ∈ R1 S L, (∀ b ∈ baum S, ⁅r, b⁆ ∈ R1 S L ⊓
      centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G)) →
    r ∈ baum S ⊔ (R1 S L ⊓ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G)) := by
  have hBP : baum S ≤ normalizer ((R1 S L ⊓ centralizer (blockU L : Set G) : Subgroup G) : Set G) :=
    fun g hg => C5.mem_normalizer_inf (Subgroup.le_normalizer (D.baum_le_R1 hg))
      (C5.mem_normalizer_centralizer (C1.mem_normalizer_blockU (D.baum_le_normalizer hg)))
  have := sc_conj D.SC₁ (D.S_le_normalizer_R1 D.ht) D.t_normalizer_baum hBP
  rwa [D.conj_P₁_t] at this

end Dbl

namespace Setup

variable {M₀ : Subgroup G} {x : G} {q : ℕ} {W : Subgroup G}
  (P : Setup T M H S L n t M₀ x q W)
include P

theorem conj_P₁ : conjSubgroup (R1 S L ⊓ centralizer (blockU L : Set G)) x =
    R1 S L ⊓ centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) := by
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_eq_self P.x_normalizes_R1, C5.conjSubgroup_centralizer]

theorem conj_P₂ : conjSubgroup (R1 S L ⊓
      centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G)) x =
    R1 S L ⊓ centralizer ((conjSubgroup (conjSubgroup (blockU L) t) x : Subgroup G) : Set G) := by
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_eq_self P.x_normalizes_R1, C5.conjSubgroup_centralizer]

theorem R1_le_normalizer_U₂ : R1 S L ≤ normalizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) := by
  intro g hg
  have h := C1.mem_normalizer_blockU (P.D.R1_le_normalizer_L₂ hg)
  rw [blockU_conjR] at h
  exact h

theorem P₁_le : R1 S L ⊓ centralizer (blockU L : Set G) ≤
    blockU L ⊔ (R1 S L ⊓ centralizer (blockU L : Set G) ⊓
      conjSubgroup (R1 S L ⊓ centralizer (blockU L : Set G)) x) := by
  have hkf := P.kf₁
  refine P.loc.rk.P_le_sup_inf_conj
    (D := baum S ⊓ centralizer (blockU L : Set G) ⊓ centralizer (L : Set G))
    inf_le_left P.x_normalizes_R1 P.hxB (not_conj_inv_le P.loc.rk P.hxB P.good) hkf.Q_eq
    (fun u hu a ha => Subgroup.mem_centralizer_iff.1 ha.2 u (P.U₁_le_L hu)) hkf.D_le
    (fun g hg => C1.mem_normalizer_blockU (R1_le_normalizer_L hg))
    (fun g hg => C5.mem_normalizer_inf (Subgroup.le_normalizer hg)
      (C5.mem_normalizer_centralizer (C1.mem_normalizer_blockU (R1_le_normalizer_L hg))))
    (fun u hu => ⟨P.D.baum_le_R1 (P.U₁_le_B hu),
      Subgroup.mem_centralizer_iff.mpr fun v hv => P.loc.rk.U_comm v hv u hu⟩)
    (fun b hb => ⟨P.D.baum_le_R1 hb.1, hb.2⟩) P.D.baum_le_R1
    (fun p hp u hu => Subgroup.mem_centralizer_iff.1 hp.2 u hu) P.D.SC₁

theorem P₂_le : R1 S L ⊓ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) ≤
    conjSubgroup (blockU L) t ⊔ (R1 S L ⊓
      centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) ⊓
      conjSubgroup (R1 S L ⊓ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G)) x) := by
  have hkf := P.kf₂
  refine P.loc₂.rk.P_le_sup_inf_conj
    (D := conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t ⊓
      centralizer ((conjSubgroup L t : Subgroup G) : Set G))
    inf_le_left P.x_normalizes_R1 P.hxB (not_conj_inv_le P.loc₂.rk P.hxB P.good₂) hkf.Q_eq
    (fun u hu a ha => Subgroup.mem_centralizer_iff.1 ha.2 u (P.U₂_le_L₂ hu)) hkf.D_le
    (fun g hg => P.R1_le_normalizer_U₂ hg)
    (fun g hg => C5.mem_normalizer_inf (Subgroup.le_normalizer hg)
      (C5.mem_normalizer_centralizer (P.R1_le_normalizer_U₂ hg)))
    (fun u hu => ⟨P.D.baum_le_R1 (P.U₂_le_B hu),
      Subgroup.mem_centralizer_iff.mpr fun v hv => P.loc₂.rk.U_comm v hv u hu⟩)
    (fun b hb => by
      have hb' : b ∈ baum S ⊓ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) := by
        rw [← P.loc₂.rk.Q_eq]; exact hb
      exact ⟨P.D.baum_le_R1 hb'.1, hb'.2⟩) P.D.baum_le_R1
    (fun p hp u hu => Subgroup.mem_centralizer_iff.1 hp.2 u hu) P.D.SC₂

theorem conj_O : conjSubgroup (pCoreOf 2 H) x =
    S ⊓ centralizer ((conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x : Subgroup G) : Set G) := by
  rw [← P.D.CS_U_eq, C5.conjSubgroup_inf, C5.conjSubgroup_eq_self P.hxN,
    C5.conjSubgroup_centralizer]

theorem O_comm_U : ∀ a ∈ pCoreOf 2 H, ∀ u ∈ blockU L ⊔ conjSubgroup (blockU L) t, u * a = a * u := by
  intro a ha u hu
  rw [← P.D.CS_U_eq] at ha
  exact Subgroup.mem_centralizer_iff.1 ha.2 u hu

theorem U_le_O : blockU L ⊔ conjSubgroup (blockU L) t ≤ pCoreOf 2 H := by
  rw [← P.D.CS_U_eq]
  refine le_inf (sup_le (P.U₁_le_B.trans inf_le_left) (P.U₂_le_B.trans inf_le_left)) ?_
  intro u hu
  exact Subgroup.mem_centralizer_iff.mpr fun v hv => P.elemAb_U.1 v hv u hu

theorem O_le_sup : pCoreOf 2 H ≤ (blockU L ⊔ conjSubgroup (blockU L) t) ⊔
    (pCoreOf 2 H ⊓ conjSubgroup (pCoreOf 2 H) x) := by
  intro p hp
  have hpR : p ∈ R1 S L := P.D.pCoreOf_le_R1 hp
  rw [← P.D.CS_U_eq] at hp
  have hpC₁ : ∀ v ∈ blockU L, v * p = p * v := fun v hv =>
    Subgroup.mem_centralizer_iff.1 hp.2 v (Subgroup.mem_sup_left hv)
  have hpC₂ : ∀ v ∈ conjSubgroup (blockU L) t, v * p = p * v := fun v hv =>
    Subgroup.mem_centralizer_iff.1 hp.2 v (Subgroup.mem_sup_right hv)
  have hp₁ : p ∈ R1 S L ⊓ centralizer (blockU L : Set G) := ⟨hpR, Subgroup.mem_centralizer_iff.mpr hpC₁⟩
  have hcomm₁ : ∀ u ∈ blockU L, ∀ c ∈ R1 S L ⊓ centralizer (blockU L : Set G) ⊓
      conjSubgroup (R1 S L ⊓ centralizer (blockU L : Set G)) x, u * c = c * u :=
    fun u hu c hc => Subgroup.mem_centralizer_iff.1 hc.1.2 u hu
  obtain ⟨u₁, hu₁, c, hc, rfl⟩ := mem_sup_of_commute hcomm₁ (P.P₁_le hp₁)
  have hcR : c ∈ R1 S L := hc.1.1
  have hcC₁ : c ∈ centralizer (blockU L : Set G) := hc.1.2
  have hcX₁ : c ∈ centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) := by
    have := hc.2
    rw [P.conj_P₁] at this
    exact this.2
  have hcC₂ : c ∈ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h := hpC₂ v hv
    have hvu : v * u₁ = u₁ * v := (P.D.comm_elem u₁ (P.U₁_le_L hu₁) v (P.U₂_le_L₂ hv)).symm
    have : u₁ * (v * c) = u₁ * (c * v) := by
      calc u₁ * (v * c) = (u₁ * v) * c := by rw [mul_assoc]
        _ = (v * u₁) * c := by rw [hvu]
        _ = v * (u₁ * c) := by rw [mul_assoc]
        _ = u₁ * c * v := h
        _ = u₁ * (c * v) := by rw [mul_assoc]
    exact mul_left_cancel this
  have hcomm₂ : ∀ u ∈ conjSubgroup (blockU L) t, ∀ c ∈ R1 S L ⊓
      centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) ⊓
      conjSubgroup (R1 S L ⊓ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G)) x,
      u * c = c * u := fun u hu c hc => Subgroup.mem_centralizer_iff.1 hc.1.2 u hu
  obtain ⟨u₂, hu₂, c', hc', rfl⟩ := mem_sup_of_commute hcomm₂ (P.P₂_le ⟨hcR, hcC₂⟩)
  have hc'R : c' ∈ R1 S L := hc'.1.1
  have hc'C₂ : c' ∈ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) := hc'.1.2
  have hc'X₂ : c' ∈ centralizer ((conjSubgroup (conjSubgroup (blockU L) t) x : Subgroup G) : Set G) := by
    have := hc'.2
    rw [P.conj_P₂] at this
    exact this.2
  have hc'C₁ : c' ∈ centralizer (blockU L : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h := Subgroup.mem_centralizer_iff.1 hcC₁ v hv
    have hvu : v * u₂ = u₂ * v := P.D.comm_elem v (P.U₁_le_L hv) u₂ (P.U₂_le_L₂ hu₂)
    have : u₂ * (v * c') = u₂ * (c' * v) := by
      calc u₂ * (v * c') = (u₂ * v) * c' := by rw [mul_assoc]
        _ = (v * u₂) * c' := by rw [hvu]
        _ = v * (u₂ * c') := by rw [mul_assoc]
        _ = u₂ * c' * v := h
        _ = u₂ * (c' * v) := by rw [mul_assoc]
    exact mul_left_cancel this
  have hc'X₁ : c' ∈ centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h := Subgroup.mem_centralizer_iff.1 hcX₁ v hv
    have hvu : v * u₂ = u₂ * v := (P.x_comm_U₂ hv u₂ hu₂).symm
    have : u₂ * (v * c') = u₂ * (c' * v) := by
      calc u₂ * (v * c') = (u₂ * v) * c' := by rw [mul_assoc]
        _ = (v * u₂) * c' := by rw [hvu]
        _ = v * (u₂ * c') := by rw [mul_assoc]
        _ = u₂ * c' * v := h
        _ = u₂ * (c' * v) := by rw [mul_assoc]
    exact mul_left_cancel this
  have hc'S : c' ∈ S := R1_le_S hc'R
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu₁))
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right hu₂))
      (Subgroup.mem_sup_right ⟨?_, ?_⟩))
  · rw [← P.D.CS_U_eq]
    exact ⟨hc'S, C56.mem_centralizer_sup (fun a ha => (Subgroup.mem_centralizer_iff.1 hc'C₁ a ha))
      (fun a ha => (Subgroup.mem_centralizer_iff.1 hc'C₂ a ha))⟩
  · rw [P.conj_O, C5.conjSubgroup_sup]
    exact ⟨hc'S, C56.mem_centralizer_sup (fun a ha => (Subgroup.mem_centralizer_iff.1 hc'X₁ a ha))
      (fun a ha => (Subgroup.mem_centralizer_iff.1 hc'X₂ a ha))⟩

theorem O_elemAb : ElemAb2 (pCoreOf 2 H) := by
  have hU2 : ∀ u ∈ blockU L ⊔ conjSubgroup (blockU L) t, u ^ 2 = 1 := fun u hu => P.elemAb_U.2 u hu
  have hcomm : ∀ A : Subgroup G, A ≤ pCoreOf 2 H → ∀ u ∈ blockU L ⊔ conjSubgroup (blockU L) t,
      ∀ a ∈ A, u * a = a * u := fun A hA u hu a ha => P.O_comm_U a (hA ha) u hu
  have e1 : sqSub (pCoreOf 2 H) = sqSub (pCoreOf 2 H ⊓ conjSubgroup (pCoreOf 2 H) x) := by
    have heq : pCoreOf 2 H = (blockU L ⊔ conjSubgroup (blockU L) t) ⊔
        (pCoreOf 2 H ⊓ conjSubgroup (pCoreOf 2 H) x) :=
      le_antisymm P.O_le_sup (sup_le P.U_le_O inf_le_left)
    conv_lhs => rw [heq]
    exact sqSub_sup_eq hU2 (hcomm _ inf_le_left)
  have e2 : sqSub (pCoreOf 2 H) = sqSub (pCoreOf 2 H ⊓ conjSubgroup (pCoreOf 2 H) x⁻¹) := by
    have heq : pCoreOf 2 H = (blockU L ⊔ conjSubgroup (blockU L) t) ⊔
        (pCoreOf 2 H ⊓ conjSubgroup (pCoreOf 2 H) x⁻¹) :=
      le_antisymm P.inv.O_le_sup (sup_le P.U_le_O inf_le_left)
    conv_lhs => rw [heq]
    exact sqSub_sup_eq hU2 (hcomm _ inf_le_left)
  have hxsq : conjSubgroup (sqSub (pCoreOf 2 H)) x = sqSub (pCoreOf 2 H) := by
    calc conjSubgroup (sqSub (pCoreOf 2 H)) x =
          conjSubgroup (sqSub (pCoreOf 2 H ⊓ conjSubgroup (pCoreOf 2 H) x⁻¹)) x := by rw [← e2]
      _ = sqSub (conjSubgroup (pCoreOf 2 H ⊓ conjSubgroup (pCoreOf 2 H) x⁻¹) x) :=
          C5.conjSubgroup_sqSub _ _
      _ = sqSub (pCoreOf 2 H ⊓ conjSubgroup (pCoreOf 2 H) x) := by
          rw [C5.conjSubgroup_inf, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
            inf_comm]
      _ = sqSub (pCoreOf 2 H) := e1.symm
  have hOH : H ≤ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hbot : sqSub (pCoreOf 2 H) = ⊥ := by
    refine C5.eq_bot_of_noCommonNormal' (C56.noCommonNormal P.D.hcs P.hSM P.hMT P.hne)
      (sqSub_le_self.trans (C56.pCoreOf_le_S P.D.hcs)) (fun g hg => ?_) (fun g hg => ?_)
      (conjSubgroup_eq_iff_mem_normalizer.mp hxsq)
      (le_sup_zpowers_of_relIndex_two P.h2 P.hx P.hxS)
    · exact conjSubgroup_eq_iff_mem_normalizer.mp
        (C5.conjSubgroup_sqSub_of_mem_normalizer (hOH hg))
    · exact conjSubgroup_eq_iff_mem_normalizer.mp
        (C5.conjSubgroup_sqSub_of_mem_normalizer (hOH (P.D.hcs.sylow.le hg)))
  have hP2 : ∀ p ∈ pCoreOf 2 H, p ^ 2 = 1 := sqSub_eq_bot_iff.mp hbot
  exact ⟨comm_of_sq_eq_one hP2, hP2⟩

theorem DU_le_O : baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) ≤ pCoreOf 2 H := by
  rw [← P.Y₁₁_eq]
  intro b hb
  obtain ⟨hb1, hb2⟩ := hb
  rw [← P.D.CS_U_eq]
  exact ⟨(mem_cB.1 hb1).1.1, C56.mem_centralizer_sup (fun a ha => (mem_cB.1 hb1).2 a ha)
    (fun a ha => (mem_cB.1 hb2).2 a ha)⟩

theorem O_le_baum : pCoreOf 2 H ≤ baum S := by
  have hOe := P.O_elemAb
  have hZ : omegaOneCenterOf (thompsonJ S) ≤ baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) := by
    rw [(omegaOne_centralizer_thompsonJ S).2]
    exact iInf₂_le _ P.isMax_DU
  intro p hp
  exact ⟨C56.pCoreOf_le_S P.D.hcs hp, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    hOe.1 z (P.DU_le_O (hZ hz)) p hp⟩

theorem O_eq_DU : pCoreOf 2 H = baumD S L ⊔ (blockU L ⊔ conjSubgroup (blockU L) t) := by
  refine le_antisymm ?_ P.DU_le_O
  intro p hp
  rw [← P.Y₁₁_eq]
  have hp' := hp
  rw [← P.D.CS_U_eq] at hp'
  exact ⟨mem_cB.2 ⟨P.O_le_baum hp, fun v hv =>
      Subgroup.mem_centralizer_iff.1 hp'.2 v (Subgroup.mem_sup_left hv)⟩,
    mem_cB.2 ⟨P.O_le_baum hp, fun v hv =>
      Subgroup.mem_centralizer_iff.1 hp'.2 v (Subgroup.mem_sup_right hv)⟩⟩

theorem blockD_eq : blockD S L = baumD S L := by
  refine le_antisymm ?_ (inf_le_inf_right _ (inf_le_left : baum S ≤ S))
  intro g hg
  have hUK : (blockU L ⊔ conjSubgroup (blockU L) t : Subgroup G) ≤ conjJoin S L :=
    sup_le (P.U₁_le_L.trans (Dbl.L_le_K (S := S) (L := L))) (P.U₂_le_L₂.trans P.D.L₂_le_K)
  have hgC : g ∈ centralizer ((blockU L ⊔ conjSubgroup (blockU L) t : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (fun u hu => hUK hu) hg.2
  have hgO : g ∈ pCoreOf 2 H := by
    rw [← P.D.CS_U_eq]; exact ⟨hg.1, hgC⟩
  exact ⟨P.O_le_baum hgO, hg.2⟩

end Setup

end CFSG.QuasithinUnique.AppE
