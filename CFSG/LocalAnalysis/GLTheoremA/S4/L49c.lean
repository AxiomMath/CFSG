module

public import CFSG.LocalAnalysis.GLTheoremA.S4.StepTools
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem l49c_mem_normalizer_inf {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH h, hK h]

private theorem l49c_le_sup_inf {A C N : Subgroup G} (hAC : A ≤ C) (hCAN : C ≤ A ⊔ N)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) : C ≤ A ⊔ (C ⊓ N) := by
  intro c hc
  have hc' : c ∈ (A ⊔ N : Subgroup G) := hCAN hc
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A N hAN] at hc'
  obtain ⟨x, hx, n, hn, rfl⟩ := Set.mem_mul.mp hc'
  have hnC : n ∈ C := by
    have : x⁻¹ * (x * n) ∈ C := C.mul_mem (C.inv_mem (hAC hx)) hc
    simpa using this
  exact Subgroup.mul_mem_sup hx ⟨hnC, hn⟩

private theorem l49c_le_glaPPrimeCoreOf {p : ℕ} {N K : Subgroup G} (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p K := by
  haveI hn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hcard : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hle : N.subgroupOf K ≤ GLAPPrimeCore p ↥K := le_sSup ⟨hn, hcard ▸ hcop⟩
  intro n hn'
  exact ⟨⟨n, hNK hn'⟩, hle hn', rfl⟩

private theorem l49c_closureIn_le {I A D : Subgroup G} (hID : I ≤ D)
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) : closureIn I A ≤ D := by
  rw [closureIn_eq_iSup_gLBConj]
  refine iSup₂_le fun a ha => ?_
  rw [← mem_normalizer_iff_gLBConj_eq.1 (hAD ha)]
  exact gLBConj_mono (g := a) hID

private theorem l49c_gLBConj_le_closureIn (I A : Subgroup G) {a : G} (ha : a ∈ A) :
    GLBConj a I ≤ closureIn I A := by
  rw [closureIn_eq_iSup_gLBConj]
  exact le_biSup (fun g => GLBConj g I) ha

private theorem l49c_le_layer {p : ℕ} {X K : Subgroup G} (h : GLAPComponent p X K) :
    K ≤ GLAPLayer p X :=
  le_sSup h

theorem glaPLayer_inf_centralizer_ne_bot_of_pumpRel {p : ℕ} (hp : p.Prime) (h183 : Input18_3_4)
    (hLB : LBalanceAt G p) (hKP : CFSG.Open.IsKProper G) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t t' : Triple G} (hrel : PumpRel p t t')
    {E : Subgroup G} (hEB' : E ≤ t'.1) (hx'E : t'.2.1 ∈ E)
    (hne : GLAPLayer p (closureIn t.2.2 (t.1 ⊓ t'.1) ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥) :
    GLAPLayer p (closureIn t'.2.2 t'.1 ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hIDC, hIK'x, -⟩ := pumpRel_facts hp h183 hKP hsimple hnonab hrel
  obtain ⟨⟨hB, hx, hL⟩, ⟨hB', hx', hL'c⟩, hxB', hdec, hx'B', hx'L, -⟩ := hrel
  set B := t.1 with hBdef
  set x := t.2.1 with hxdef
  set L := t.2.2 with hLdef
  set B' := t'.1 with hB'def
  set x' := t'.2.1 with hx'def
  set L' := t'.2.2 with hL'def
  set C := Subgroup.centralizer ({x} : Set G) with hCdef
  set C' := Subgroup.centralizer ({x'} : Set G) with hC'def
  set D := C ⊓ C' with hDdef
  set A := B ⊓ B' with hAdef
  set O := GLAPPrimeCoreOf p C with hOdef
  set I := GLAPLayer p (L ⊓ C') with hIdef
  set Ce := Subgroup.centralizer (E : Set G) with hCedef
  set H := closureIn L A with hHdef
  set H' := closureIn I A with hH'def
  set K' := closureIn L' B' with hK'def
  have hBC : B ≤ C := isElemAbelian_le_centralizer hB.1 hx.1
  have hB'C : B' ≤ C := isElemAbelian_le_centralizer hB'.1 hxB'
  have hB'C' : B' ≤ C' := isElemAbelian_le_centralizer hB'.1 hx'B'
  have hAC : A ≤ C := inf_le_left.trans hBC
  have hAD : A ≤ D := le_inf hAC (inf_le_right.trans hB'C')
  have hAB' : A ≤ B' := inf_le_right
  have hEC' : E ≤ C' := hEB'.trans hB'C'
  have hCe : Ce ≤ C' := Subgroup.centralizer_le (Set.singleton_subset_iff.2 hx'E)
  have hC'top : C' ≠ ⊤ := centralizer_ne_top_of_ne_one hsimple hnonab hx'.2.1
  have hO : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp C
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p C
  have hB'p : IsPGroup p B' := isPGroup_of_isElemAbelian hB'.1
  have hxC' : Subgroup.zpowers x ≤ C' := Subgroup.zpowers_le.2 (hB'C' hxB')
  have hK'C' : K' ≤ C' :=
    l49c_closureIn_le hL'c.1 (fun b hb => Subgroup.le_normalizer (hB'C' hb))
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hB'.1 hx'B'
  obtain ⟨hIc, -, -, -, hIsup, -⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  have hIL : I ≤ L := hIc.1.trans inf_le_left
  have hcomm : ∀ c ∈ B', CentMod p L c → c ∈ Subgroup.normalizer (H : Set G) := fun c hc hcL =>
    (commutator_mem_of_centMod_closureIn hp hL (hB'C hc) hAC
      (fun a ha => isElemAbelian_commute hB'.1 ha.2 hc) hcL).1
  have hB'H : B' ≤ Subgroup.normalizer (H : Set G) := by
    intro b hb
    obtain ⟨u, hu, v, hv, hvL, rfl⟩ := hdec b hb
    exact Subgroup.mul_mem _ (le_normalizer_closureIn L A hu) (hcomm v hv hvL)
  have hEN : E ≤ Subgroup.normalizer ((H ⊓ C' : Subgroup G) : Set G) := by
    intro e he
    exact l49c_mem_normalizer_inf (hB'H (hEB' he)) (Subgroup.le_normalizer (hEC' he))
  obtain ⟨D₁, hD₁Y, hD₁⟩ : ∃ D₁ : Subgroup G, GLAPComponent p (H ⊓ Ce) D₁ ∧ D₁ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hne
    refine le_antisymm (sSup_le fun K hK => ?_) bot_le
    exact (hcon K hK).le
  have hD₁H : D₁ ≤ H ⊓ Ce := hD₁Y.1
  have hHC'e : H ⊓ Ce = (H ⊓ C') ⊓ Ce := by
    rw [inf_assoc, inf_eq_right.2 hCe]
  have hD₁Y' : GLAPComponent p ((H ⊓ C') ⊓ Ce) D₁ := by
    rw [← hHC'e]
    exact hD₁Y
  have hP1 : IsPGroup p E := hB'p.to_le hEB'
  have hK1 : CFSG.Open.IsKGroup ↥((H ⊓ C') ⊔ E) :=
    isKGroup_of_isKProper hKP (ne_top_of_le_ne_top hC'top (sup_le inf_le_right hEC'))
  have hle1 : D₁ ≤ GLAPLayer p (H ⊓ C') :=
    (l49c_le_layer hD₁Y').trans (glaPLayer_inf_centralizer_le hp hLB hK1 hP1 hEN)
  have hH'D : H' ≤ D := l49c_closureIn_le hIDC.1 (fun a ha => Subgroup.le_normalizer (hAD ha))
  have hH'C : H' ≤ C := hH'D.trans inf_le_left
  have hH'H : H' ≤ H :=
    l49c_closureIn_le (hIL.trans (le_closureIn_self L A)) (le_normalizer_closureIn L A)
  have hHsup : H ≤ H' ⊔ O := closureIn_le_closureIn_sup hp hL hIsup hAC
  have hID : ∀ a ∈ A, GLAPComponent p D (GLBConj a I) := fun a ha => by
    have := glaPComponent_gLBConj hIDC a
    rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hAD ha))] at this
  set 𝓘 : Set (Subgroup G) := {X | ∃ a ∈ A, GLBConj a I = X}
  have hS : ∀ X ∈ 𝓘, GLAPComponent p D X := by
    intro X hX
    obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, GLBConj a I = X := hX
    exact hID a ha
  have hsup𝓘 : sSup 𝓘 = H' := by
    refine le_antisymm (sSup_le fun X hX => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, GLBConj a I = X := hX
      exact l49c_gLBConj_le_closureIn I A ha
    · rw [hH'def, closureIn_eq_iSup_gLBConj]
      exact iSup₂_le fun a ha => le_sSup ⟨a, ha, rfl⟩
  set 𝓛 : Set (Subgroup G) := {X | ∃ a ∈ A, GLBConj a L = X}
  have hLC : ∀ X ∈ 𝓛, GLAPComponent p C X := by
    intro X hX
    obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, GLBConj a L = X := hX
    have := glaPComponent_gLBConj hL a
    rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hAC ha))] at this
  have hsup𝓛 : sSup 𝓛 = H := by
    refine le_antisymm (sSup_le fun X hX => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, GLBConj a L = X := hX
      exact l49c_gLBConj_le_closureIn L A ha
    · rw [hHdef, closureIn_eq_iSup_gLBConj]
      exact iSup₂_le fun a ha => le_sSup ⟨a, ha, rfl⟩
  have hHsn : IsSubnormal H C := by
    rw [← hsup𝓛]
    exact isSubnormal_sSup_glaPComponent hp 𝓛 hLC
  have hLayer : GLAPLayer p (H ⊓ C') ≤ H' := by
    refine sSup_le fun W hW => ?_
    have hW' : GLAPComponent p (H ⊓ C') W := hW
    have hW'D : GLAPComponent p D W := glaPComponent_of_isSubnormal' hp (hHsn.inf C') hW'
    have h1 : W ≤ (H' ⊔ O) ⊓ D :=
      le_inf ((hW'.1.trans inf_le_left).trans hHsup) hW'D.1
    have h2 : (H' ⊔ O) ⊓ D ≤ H' ⊔ (D ⊓ O) := by
      have h := l49c_le_sup_inf (A := H') (C := (H' ⊔ O) ⊓ D) (N := O)
        (le_inf le_sup_left hH'D) inf_le_left (fun h hh => hCO (hH'C hh))
      exact h.trans (sup_le_sup_left (inf_le_inf_right O inf_le_right) H')
    have h3 : D ⊓ O ≤ GLAPPrimeCoreOf p D := by
      refine l49c_le_glaPPrimeCoreOf inf_le_left ?_ ?_
      · intro d hd
        exact l49c_mem_normalizer_inf (Subgroup.le_normalizer hd)
          (hCO (Subgroup.mem_inf.1 hd).1)
      · exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
          hO (h.trans (Subgroup.card_dvd_of_le inf_le_right))
    have hW𝓘 : W ≤ sSup 𝓘 ⊔ GLAPPrimeCoreOf p D :=
      h1.trans (h2.trans (sup_le (le_sup_of_le_left hsup𝓘.ge) (le_sup_of_le_right h3)))
    obtain ⟨a, ha, hae⟩ : ∃ a ∈ A, GLBConj a I = W :=
      mem_of_le_sSup_sup_glaPComponent hp 𝓘 hS hW'D hW𝓘
    rw [← hae]
    exact l49c_gLBConj_le_closureIn I A ha
  have hD₁H'E : D₁ ≤ H' ⊓ Ce := le_inf (hle1.trans hLayer) (hD₁H.trans inf_le_right)
  have hD₁H'comp : GLAPComponent p (H' ⊓ Ce) D₁ :=
    glaPComponent_of_le hp hD₁Y hD₁H'E (inf_le_inf_right _ hH'H)
  have hK'Cp : ∀ a ∈ A, GLBConj a (K' ⊓ C) = K' ⊓ C := fun a ha =>
    mem_normalizer_iff_gLBConj_eq.1
      (l49c_mem_normalizer_inf (le_normalizer_closureIn L' B' (hAB' ha))
        (Subgroup.le_normalizer (hAC ha)))
  have hIK'C : ∀ a ∈ A, GLAPComponent p (K' ⊓ C) (GLBConj a I) := fun a ha => by
    have := glaPComponent_gLBConj hIK'x a
    rwa [hK'Cp a ha] at this
  have hIK'C' : ∀ X ∈ 𝓘, GLAPComponent p (K' ⊓ C) X := by
    intro X hX
    obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, GLBConj a I = X := hX
    exact hIK'C a ha
  have hH'sub : IsSubnormal H' (K' ⊓ C) := by
    rw [← hsup𝓘]
    exact isSubnormal_sSup_glaPComponent hp 𝓘 hIK'C'
  have hD₁K : GLAPComponent p ((K' ⊓ C) ⊓ Ce) D₁ :=
    glaPComponent_of_isSubnormal' hp (hH'sub.inf Ce) hD₁H'comp
  have hxCe : x ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun e he => isElemAbelian_commute hB'.1 (hEB' he) hxB'
  have hPX6 : Subgroup.zpowers x ≤ Subgroup.normalizer ((K' ⊓ Ce : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2
      (l49c_mem_normalizer_inf (le_normalizer_closureIn L' B' hxB') (Subgroup.le_normalizer hxCe))
  have hK6 : CFSG.Open.IsKGroup ↥((K' ⊓ Ce) ⊔ Subgroup.zpowers x) :=
    isKGroup_of_isKProper hKP (ne_top_of_le_ne_top hC'top (sup_le (inf_le_left.trans hK'C') hxC'))
  have hP6 : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_mem hB'.1 hxB'
  have hCzx : Subgroup.centralizer (Subgroup.zpowers x : Set G) = C := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hD₁Z : D₁ ≤ GLAPLayer p ((K' ⊓ Ce) ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
    rw [hCzx, inf_right_comm]
    exact l49c_le_layer hD₁K
  have hD₁K' : D₁ ≤ GLAPLayer p (K' ⊓ Ce) :=
    hD₁Z.trans (glaPLayer_inf_centralizer_le hp hLB hK6 hP6 hPX6)
  intro hbot
  exact hD₁ (le_bot_iff.1 (hD₁K'.trans hbot.le))

end CFSG.LocalAnalysis.GLTheoremA
