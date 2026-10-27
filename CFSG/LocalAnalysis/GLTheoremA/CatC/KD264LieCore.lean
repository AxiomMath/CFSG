module

public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevToolsK
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.GroupTheory.PLayer.Transfer
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAComponentSelf
public import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem glaPLayer_inf_centralizer_anti {p : ℕ} (hp : p.Prime) (hLB : LBalanceAt Y p)
    {K : Subgroup Y} (hK : CFSG.Open.IsKGroup ↥K) {F F' : Subgroup Y} (hF'F : F' ≤ F)
    (hFF' : F ≤ Subgroup.centralizer (F' : Set Y)) (hFp : IsPGroup p F)
    (hFK : F ≤ Subgroup.normalizer (K : Set Y)) :
    GLAPLayer p (K ⊓ Subgroup.centralizer (F : Set Y)) ≤
      GLAPLayer p (K ⊓ Subgroup.centralizer (F' : Set Y)) := by
  have hC : Subgroup.centralizer (F : Set Y) ≤ Subgroup.centralizer (F' : Set Y) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hF'F)
  have hXK : CFSG.Open.IsKGroup ↥(K ⊓ Subgroup.centralizer (F' : Set Y)) :=
    hK.of_injective (Subgroup.inclusion (inf_le_left : K ⊓ Subgroup.centralizer (F' : Set Y) ≤ K))
      (Subgroup.inclusion_injective _)
  have hXN : F ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (F' : Set Y)) : Set Y) :=
    (le_inf hFK (hFF'.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hsupK : CFSG.Open.IsKGroup ↥((K ⊓ Subgroup.centralizer (F' : Set Y)) ⊔ F) :=
    CFSG.LocalAnalysis.GLTheoremA.chevTools_isKGroup_sup hp hXK hXN hFp
  have h := CFSG.LocalAnalysis.GLTheoremA.glaPLayer_inf_centralizer_le hp hLB hsupK hFp hXN
  rwa [inf_assoc, inf_eq_right.2 hC] at h

theorem kd264_goal_of_good {p : ℕ} (hp : p.Prime) (hLB : LBalanceAt Y p)
    {K B : Subgroup Y} (hK : CFSG.Open.IsKGroup ↥K) (hKn : K.Normal)
    (hB : IsElemAbelian p B) {F : Subgroup Y} (hFB : F ≤ B)
    (hFcard : p ^ 3 ≤ Nat.card F)
    (hgood : GLAPLayer p (K ⊓ Subgroup.centralizer (F : Set Y)) ≠ ⊥) :
    (∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥) ∧
      K ⊓ Subgroup.centralizer
          ((F ⊔ (B ⊓ Subgroup.centralizer (K : Set Y)) : Subgroup Y) : Set Y) =
        K ⊓ Subgroup.centralizer (F : Set Y) := by
  have hFel : IsElemAbelian p F := isElemAbelian_mono hB hFB
  have hFp : IsPGroup p F := isPGroup_of_isElemAbelian hFel
  haveI := hKn
  have hFBn : F ≤ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (G := ↥F) hp hFp
    (by simpa using hFcard)
  set E : Subgroup Y := H.map F.subtype with hEdef
  have hEF : E ≤ F := Subgroup.map_subtype_le _
  have hEcard : Nat.card E = p ^ 3 := by
    rw [hEdef, Subgroup.card_map_of_injective F.subtype_injective, hHcard]
  have hEel : IsElemAbelian p E := isElemAbelian_mono hFel hEF
  have hFE : F ≤ Subgroup.centralizer (E : Set Y) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact isElemAbelian_commute hFel (hEF he) hf
  have hanti := glaPLayer_inf_centralizer_anti hp hLB hK hEF hFE hFp hFBn
  have hgoodE : GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥ := by
    intro hbot
    exact hgood (le_bot_iff.1 (hbot ▸ hanti))
  refine ⟨⟨E, hEF.trans hFB, hEel, hEcard, hgoodE⟩, ?_⟩
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hCK : C ≤ Subgroup.centralizer (K : Set Y) := inf_le_right
  have hKC : K ≤ Subgroup.centralizer (C : Set Y) := by
    rw [Subgroup.le_centralizer_iff]
    exact hCK
  rw [centralizer_sup_eq, ← inf_assoc]
  exact inf_eq_left.2 (inf_le_left.trans hKC)

theorem kd264_of_card_centralizer {p : ℕ} (hp : p.Prime) {K B : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hcore : GLAPPrimeCore p ↥K = ⊥)
    (hB : IsElemAbelian p B)
    (hC : p ^ 3 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y))) :
    ∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥ := by
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hCel : IsElemAbelian p C := isElemAbelian_mono hB inf_le_left
  have hCp : IsPGroup p C := isPGroup_of_isElemAbelian hCel
  obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (G := ↥C) hp hCp
    (by simpa using hC)
  set E : Subgroup Y := H.map C.subtype with hEdef
  have hEC : E ≤ C := Subgroup.map_subtype_le _
  have hEcard : Nat.card E = p ^ 3 := by
    rw [hEdef, Subgroup.card_map_of_injective C.subtype_injective, hHcard]
  have hEel : IsElemAbelian p E := isElemAbelian_mono hCel hEC
  have hEK : E ≤ Subgroup.centralizer (K : Set Y) := hEC.trans inf_le_right
  have hKE : K ≤ Subgroup.centralizer (E : Set Y) := by
    rw [Subgroup.le_centralizer_iff]
    exact hEK
  have hself : GLAPComponent p K K :=
    CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hq hcore
  have hLne : GLAPLayer p K ≠ ⊥ := fun hbot =>
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hself
      (le_bot_iff.1 (hbot ▸ le_sSup hself))
  refine ⟨E, hEC.trans inf_le_left, hEel, hEcard, ?_⟩
  rwa [inf_eq_left.2 hKE]

theorem kd264_rank_ineq {p : ℕ} (hp : p.Prime) {K B : Subgroup Y}
    (hB : IsElemAbelian p B) (hmax : IsMaxRankIn p B ⊤)
    {b : Y} (hbB : b ∈ B) {A : Subgroup Y} (hAel : IsElemAbelian p A)
    (hAK : A ≤ K) (hAb : A ≤ Subgroup.centralizer ({b} : Set Y))
    (hb : b = 1 ∨ b ∉ K ⊔ (B ⊓ Subgroup.centralizer (K : Set Y))) :
    Nat.card A * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) *
        Nat.card (Subgroup.zpowers b) ≤
      Nat.card B * Nat.card ↥(A ⊓ (B ⊓ Subgroup.centralizer (K : Set Y))) := by
  classical
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hCel : IsElemAbelian p C := isElemAbelian_mono hB inf_le_left
  have hCB : C ≤ B := inf_le_left
  have hCK : C ≤ Subgroup.centralizer (K : Set Y) := inf_le_right
  have hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a := fun a ha c hc =>
    (Subgroup.mem_centralizer_iff.1 (hCK hc)) a (hAK ha)
  have hbA : ∀ a ∈ A, b * a = a * b := fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (hAb ha)) b (Set.mem_singleton b)
  have hbC : ∀ c ∈ C, b * c = c * b := fun c hc =>
    isElemAbelian_commute hB hbB (hCB hc)
  have hbAC : Subgroup.zpowers b ≤ Subgroup.centralizer ((A ⊔ C : Subgroup Y) : Set Y) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hba : b ∈ Subgroup.centralizer ({a} : Set Y) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hbA a ha
      exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.zpowers_le.2 hba hy)
    · intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hbc : b ∈ Subgroup.centralizer ({c} : Set Y) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hbC c hc
      exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.zpowers_le.2 hbc hy)
  have hHC : ∀ x ∈ (A ⊔ C : Subgroup Y), ∀ y ∈ Subgroup.zpowers b, x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.1 (hbAC hy)) x hx
  have hACel : IsElemAbelian p (A ⊔ C) := IsElemAbelian.sup_of_commute hAel hCel hAC
  have hbel : IsElemAbelian p (Subgroup.zpowers b) :=
    isElemAbelian_mono hB (Subgroup.zpowers_le.2 hbB)
  have hHel : IsElemAbelian p (A ⊔ C ⊔ Subgroup.zpowers b) :=
    IsElemAbelian.sup_of_commute hACel hbel hHC
  have hHle : Nat.card ↥(A ⊔ C ⊔ Subgroup.zpowers b) ≤ Nat.card B := hmax _ le_top hHel
  have hdisj : (A ⊔ C : Subgroup Y) ⊓ Subgroup.zpowers b = ⊥ := by
    rcases hb with rfl | hbnot
    · rw [Subgroup.zpowers_one_eq_bot, inf_bot_eq]
    · have hb1 : b ≠ 1 := by
        rintro rfl
        exact hbnot (Subgroup.one_mem _)
      have hbp : b ^ p = 1 := hB.2 b hbB
      have hbH : b ∉ (A ⊔ C : Subgroup Y) := fun hbAC =>
        hbnot ((sup_le_sup hAK le_rfl) hbAC)
      have h := zpowers_inf_eq_bot_of_not_mem hp hbp hb1 hbH
      rwa [inf_comm] at h
  have hCNA : C ≤ Subgroup.normalizer (A : Set Y) := by
    have hCA : C ≤ Subgroup.centralizer (A : Set Y) := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hAC a ha c hc
    exact hCA.trans (Subgroup.centralizer_le_normalizer (A : Set Y))
  have hbNAC : Subgroup.zpowers b ≤
      Subgroup.normalizer ((A ⊔ C : Subgroup Y) : Set Y) :=
    hbAC.trans (Subgroup.centralizer_le_normalizer _)
  have hmain : Nat.card ↥(A ⊔ C ⊔ Subgroup.zpowers b) * Nat.card ↥(A ⊓ C) =
      Nat.card A * Nat.card C * Nat.card (Subgroup.zpowers b) :=
    card_sup_sup_mul_card_inf_eq hCNA hbNAC hdisj
  calc Nat.card A * Nat.card C * Nat.card (Subgroup.zpowers b)
      = Nat.card ↥(A ⊔ C ⊔ Subgroup.zpowers b) * Nat.card ↥(A ⊓ C) := hmain.symm
    _ ≤ Nat.card B * Nat.card ↥(A ⊓ C) := Nat.mul_le_mul_right _ hHle

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
