module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Cls2

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace Two

variable {t x : G} (X : Two T M H S L t x)
include X

theorem V₂_le_baum : conjR (blockU2 L t) x ≤ baum S := by
  have h := X.C'.V_le_baum X.hx
  rwa [blockU_L₂] at h

theorem V₁_sup_V₂_le_S : conjR (blockU L) x ⊔ conjR (blockU2 L t) x ≤ S :=
  sup_le (fun _ hv => (X.C.V_le_baum X.hx hv).1) (fun _ hv => (X.V₂_le_baum hv).1)

theorem conjR_pCoreOf_eq : conjR (pCoreOf 2 H) x = baumD S L ⊔ conjR (blockU0 S L) x := by
  have hD := X.C.D
  have hU0 : blockU0 S L = U0 L t := hD.blockU0_eq
  rw [X.conjR_pCoreOf, X.baumD_eq_blockD, hU0, conjR_U0_eq L t x]
  apply le_antisymm
  · intro r hr
    have h1 : ∀ v ∈ conjR (blockU L) x, r * v = v * r := fun v hv =>
      (Subgroup.mem_centralizer_iff.1 hr.2 v (Subgroup.mem_sup_left hv)).symm
    have h2 : ∀ v ∈ conjR (blockU2 L t) x, r * v = v * r := fun v hv =>
      (Subgroup.mem_centralizer_iff.1 hr.2 v (Subgroup.mem_sup_right hv)).symm
    obtain ⟨w, hw, c, hc, rfl⟩ := X.centralizer_U0x_le hr.1 h1 h2
    exact (blockD S L ⊔ (conjR (blockU L) x ⊔ conjR (blockU2 L t) x)).mul_mem
      (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left hc)
  · refine sup_le (fun c hc => ?_) (fun w hw => ?_)
    · refine Subgroup.mem_inf.2 ⟨hc.1, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
      exact comm_sup_left (A₁ := conjR (blockU L) x) (A₂ := conjR (blockU2 L t) x)
        (B := blockD S L) (fun a ha b hb => (X.blockD_comm_V₁ hb ha).symm)
        (fun a ha b hb => (X.blockD_comm_V₂ hb ha).symm) w hw c hc
    · refine Subgroup.mem_inf.2 ⟨X.V₁_sup_V₂_le_S hw, Subgroup.mem_centralizer_iff.2 fun w' hw' => ?_⟩
      exact comm_sup_sup (A₁ := conjR (blockU L) x) (A₂ := conjR (blockU2 L t) x)
        (B₁ := conjR (blockU L) x) (B₂ := conjR (blockU2 L t) x)
        (fun a ha b hb => X.V₁_ab ha hb) (fun a ha b hb => X.V₁_comm_V₂ ha hb)
        (fun a ha b hb => (X.V₁_comm_V₂ hb ha).symm) (fun a ha b hb => X.V₂_ab ha hb)
        w' hw' w hw

theorem invariant_isMax_iff {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    (∀ s ∈ S, conjR A s = A) ↔
      (A = baumD S L ⊔ blockU0 S L ∨ A = baumD S L ⊔ conjR (blockU0 S L) x) := by
  have hD := X.C.D
  have hP : pCoreOf 2 H = baumD S L ⊔ blockU0 S L := X.pCoreOf_eq
  have hPx := X.conjR_pCoreOf_eq
  have hPS : ∀ s ∈ S, conjR (pCoreOf 2 H) s = pCoreOf 2 H := fun s hs =>
    C5.conjSubgroup_eq_self
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
        (hD.hcs.sylow.le hs))
  constructor
  · intro hinv
    rcases X.im_eq_bot_or hA hinv with hbot | hE
    · left
      rw [← hP]
      exact X.eq_pCoreOf_of_im_bot hA hinv hbot
    · right
      rw [← hPx]
      have hAB := X.le_baum_of_isMax hA
      have hV₁ := X.A_comm_V₁ hA hE
      have hV₂ : ∀ a ∈ A, ∀ v ∈ conjR (blockU2 L t) x, a * v = v * a := by
        intro a ha v hv
        have hta : t * a * t⁻¹ ∈ A := by
          have : a ∈ conjR A t := by rw [hinv t hD.ht]; exact ha
          exact mem_conjSubgroup_iff.1 this
        have hv₁ : t * v * t⁻¹ ∈ conjR (blockU L) x := by
          have : v ∈ conjR (conjR (blockU L) x) t := by rw [X.conjR_V₁_t]; exact hv
          exact mem_conjSubgroup_iff.1 this
        have h2 := hV₁ _ hta _ hv₁
        have e1 : (t * a * t⁻¹) * (t * v * t⁻¹) = t * (a * v) * t⁻¹ := by group
        have e2 : (t * v * t⁻¹) * (t * a * t⁻¹) = t * (v * a) * t⁻¹ := by group
        rw [e1, e2] at h2
        exact mul_left_cancel (mul_right_cancel h2)
      have hV : IsMaxElemAbelian S (conjR (pCoreOf 2 H) x) :=
        C56.isMaxElemAbelian_conjSubgroup X.pCoreOf_isMax X.hx
      have hcomm' : ∀ w ∈ baumD S L ⊔ conjR (blockU0 S L) x, ∀ a ∈ A, w * a = a * w := by
        have hU0x : conjR (blockU0 S L) x = conjR (blockU L) x ⊔ conjR (blockU2 L t) x := by
          rw [hD.blockU0_eq]; exact conjR_U0_eq L t x
        refine comm_sup_left (A₁ := baumD S L) (A₂ := conjR (blockU0 S L) x) (B := A)
          (fun d hd a ha => ?_) (fun w hw a ha => ?_)
        · rw [X.baumD_eq_blockD] at hd
          exact X.blockD_comm_baum hd (hAB ha)
        · rw [hU0x] at hw
          exact comm_sup_left (A₁ := conjR (blockU L) x) (A₂ := conjR (blockU2 L t) x) (B := A)
            (fun v hv a ha => (hV₁ a ha v hv).symm) (fun v hv a ha => (hV₂ a ha v hv).symm)
            w hw a ha
      have hcomm : ∀ a ∈ A, ∀ w ∈ conjR (pCoreOf 2 H) x, a * w = w * a := by
        intro a ha w hw
        rw [hPx] at hw
        exact (hcomm' w hw a ha).symm
      have hel := B2F.isElemAbelian_sup_of_commute hA.2.1 hV.2.1 hcomm
      have hle : A ⊔ conjR (pCoreOf 2 H) x ≤ S := sup_le hA.1 hV.1
      have hcard := hA.2.2 _ hle hel
      have heq : A = A ⊔ conjR (pCoreOf 2 H) x := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
      have hVA : conjR (pCoreOf 2 H) x ≤ A := le_sup_right.trans heq.ge
      have hcardV : Nat.card A ≤ Nat.card ↥(conjR (pCoreOf 2 H) x) := by
        rw [Lin2.card_conjR, X.card_eq_pCoreOf hA]
      exact (Subgroup.eq_of_le_of_card_ge hVA hcardV).symm
  · rintro (h | h)
    · intro s hs
      rw [h, ← hP]
      exact hPS s hs
    · intro s hs
      rw [h, ← hPx]
      have hxs : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 X.hx s).1 hs
      rw [Dbl.conjR_conjR]
      have e : x * s = (x * s * x⁻¹) * x := by group
      rw [e, ← Dbl.conjR_conjR, hPS _ hxs]

end Two

end CFSG.QuasithinUnique.AppCS2
