module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Proj
public import CFSG.LocalAnalysis.GLTheoremA.S4.StepTools
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem le_glaPPrimeCoreOf_of_le_normalizer' {p : ℕ} {N K : Subgroup G} (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p K := by
  haveI hn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hcard : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hle : N.subgroupOf K ≤ GLAPPrimeCore p ↥K := le_sSup ⟨hn, hcard ▸ hcop⟩
  intro n hn'
  exact ⟨⟨n, hNK hn'⟩, hle hn', rfl⟩

theorem nGen_le_iff {B K X : Subgroup G} :
    nGen B K ≤ X ↔ ∀ T : Subgroup G, T ≤ K → IsPGroup 2 T →
      B ≤ Subgroup.normalizer (T : Set G) → T ≤ X := by
  unfold nGen
  refine ⟨fun h T h1 h2 h3 => le_trans ?_ h, fun h => iSup₂_le fun T hT => h T hT.1 hT.2.1 hT.2.2⟩
  exact le_iSup₂_of_le (f := fun (T : Subgroup G)
    (_ : T ≤ K ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)) => T) T ⟨h1, h2, h3⟩ le_rfl

theorem closureIn_le_of_le {I A D : Subgroup G} (hID : I ≤ D)
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) : closureIn I A ≤ D := by
  rw [closureIn_eq_iSup_gLBConj]
  refine iSup₂_le fun a ha => ?_
  rw [← mem_normalizer_iff_gLBConj_eq.1 (hAD ha)]
  exact gLBConj_mono (g := a) hID

theorem le_glaPPrimeCoreOf_of_le_closureIn {p : ℕ} (hp : p.Prime) {C D L I A N : Subgroup G}
    (hL : GLAPComponent p C L) (hIL : I ≤ L) (hIsup : I ⊔ GLAPPrimeCoreOf p L = L)
    (hAC : A ≤ C) (hID : ∀ a ∈ A, GLAPComponent p D (GLBConj a I))
    (hN : ¬ p ∣ Nat.card N) (hNI : N ≤ closureIn I A)
    (hIN : closureIn I A ≤ Subgroup.normalizer (N : Set G)) : N ≤ GLAPPrimeCoreOf p C := by
  classical
  have hH'C : closureIn I A ≤ C :=
    closureIn_le_of_le (hIL.trans hL.1) (fun a ha => Subgroup.le_normalizer (hAC ha))
  have hNC : N ≤ C := hNI.trans hH'C
  have hIa_le : ∀ a ∈ A, GLBConj a I ≤ closureIn I A := fun a ha => by
    rw [closureIn_eq_iSup_gLBConj]
    exact le_biSup (fun g => GLBConj g I) ha
  have hIaN : ∀ a ∈ A, GLBConj a I ≤ Subgroup.normalizer (N : Set G) :=
    fun a ha => (hIa_le a ha).trans hIN
  have hNIa : ∀ a ∈ A, N ≤ Subgroup.normalizer (GLBConj a I : Set G) := by
    intro a ha
    refine hNI.trans ?_
    rw [closureIn_eq_iSup_gLBConj]
    refine iSup₂_le fun b hb => ?_
    by_cases hab : GLBConj b I = GLBConj a I
    · rw [hab]
      exact Subgroup.le_normalizer
    · intro g hg
      exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp (hID a ha)
        (hID b hb) (fun h => hab h.symm) hg
  have hPI : GLAPPrimeCoreOf p I ≤ GLAPPrimeCoreOf p C := by
    have hLO : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p C := by
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1]
      exact inf_le_right
    rw [(cover_facts hp hIL hIsup).1]
    exact inf_le_right.trans hLO
  have key : ∀ a ∈ A, ∀ n ∈ N, ∀ y ∈ GLBConj a I, ⁅n, y⁆ ∈ GLAPPrimeCoreOf p C := by
    intro a ha n hn y hy
    have hyN : y ∈ Subgroup.normalizer (N : Set G) := hIaN a ha hy
    have hnI : n ∈ Subgroup.normalizer (GLBConj a I : Set G) := hNIa a ha hn
    have h1 : ⁅n, y⁆ ∈ N := by
      have hyn : y * n⁻¹ * y⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.1 hyN n⁻¹).1 (N.inv_mem hn)
      have e : ⁅n, y⁆ = n * (y * n⁻¹ * y⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem hn hyn
    have h2 : ⁅n, y⁆ ∈ GLBConj a I := by
      have hnyn : n * y * n⁻¹ ∈ GLBConj a I := (Subgroup.mem_normalizer_iff.1 hnI y).1 hy
      rw [commutatorElement_def]
      exact (GLBConj a I).mul_mem hnyn ((GLBConj a I).inv_mem hy)
    have hcop : Nat.Coprime p (Nat.card (N ⊓ GLBConj a I : Subgroup G)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
        hN (h.trans (Subgroup.card_dvd_of_le (inf_le_left : N ⊓ GLBConj a I ≤ N)))
    have hnorm : GLBConj a I ≤ Subgroup.normalizer ((N ⊓ GLBConj a I : Subgroup G) : Set G) :=
      fun x hx => Prop53.mem_normalizer_inf_of_mem (hIaN a ha hx) (Subgroup.le_normalizer hx)
    have hsub : N ⊓ GLBConj a I ≤ GLAPPrimeCoreOf p (GLBConj a I) :=
      le_glaPPrimeCoreOf_of_le_normalizer' inf_le_right hnorm hcop
    have hPa : GLAPPrimeCoreOf p (GLBConj a I) ≤ GLAPPrimeCoreOf p C := by
      rw [glaPPrimeCoreOf_gLBConj]
      have hOa : GLBConj a (GLAPPrimeCoreOf p C) = GLAPPrimeCoreOf p C :=
        mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_glaPPrimeCoreOf p C (hAC ha))
      exact (gLBConj_mono (g := a) hPI).trans hOa.le
    exact hPa (hsub (Subgroup.mem_inf.2 ⟨h1, h2⟩))
  let Z : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (GLAPPrimeCoreOf p C : Set G) ∧
        ∀ n ∈ N, ⁅n, g⁆ ∈ GLAPPrimeCoreOf p C}
      one_mem' := by
        show _ ∧ _
        refine ⟨Subgroup.one_mem _, fun n _ => ?_⟩
        rw [commutatorElement_one_right]
        exact (GLAPPrimeCoreOf p C).one_mem
      mul_mem' := by
        intro g₁ g₂ h₁ h₂
        obtain ⟨n₁, k₁⟩ := h₁
        obtain ⟨n₂, k₂⟩ := h₂
        show _ ∧ _
        refine ⟨Subgroup.mul_mem _ n₁ n₂, fun n hn => ?_⟩
        have e : ⁅n, g₁ * g₂⁆ = ⁅n, g₁⁆ * (g₁ * ⁅n, g₂⁆ * g₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (GLAPPrimeCoreOf p C).mul_mem (k₁ n hn)
          ((Subgroup.mem_normalizer_iff.1 n₁ _).1 (k₂ n hn))
      inv_mem' := by
        intro g hg
        obtain ⟨n, k⟩ := hg
        show _ ∧ _
        refine ⟨Subgroup.inv_mem _ n, fun m hm => ?_⟩
        have e : ⁅m, g⁻¹⁆ = g⁻¹ * ⁅m, g⁆⁻¹ * g := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ n) ⁅m, g⁆⁻¹).1
          ((GLAPPrimeCoreOf p C).inv_mem (k m hm))
        rwa [inv_inv] at h }
  have hH'Z : closureIn I A ≤ Z := by
    rw [closureIn_eq_iSup_gLBConj]
    refine iSup₂_le fun a ha => ?_
    intro y hy
    show y ∈ Subgroup.normalizer (GLAPPrimeCoreOf p C : Set G) ∧
      ∀ n ∈ N, ⁅n, y⁆ ∈ GLAPPrimeCoreOf p C
    exact ⟨le_normalizer_glaPPrimeCoreOf p C (hH'C (hIa_le a ha hy)),
      fun n hn => key a ha n hn y hy⟩
  have hOZ : GLAPPrimeCoreOf p C ≤ Z := by
    intro o ho
    show o ∈ Subgroup.normalizer (GLAPPrimeCoreOf p C : Set G) ∧
      ∀ n ∈ N, ⁅n, o⁆ ∈ GLAPPrimeCoreOf p C
    refine ⟨Subgroup.le_normalizer ho, fun n hn => ?_⟩
    have hno : n * o * n⁻¹ ∈ GLAPPrimeCoreOf p C :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p C (hNC hn)) o).1 ho
    rw [commutatorElement_def]
    exact (GLAPPrimeCoreOf p C).mul_mem hno ((GLAPPrimeCoreOf p C).inv_mem ho)
  have hZs : closureIn I A ⊔ GLAPPrimeCoreOf p C ≤ Z := sup_le hH'Z hOZ
  have hIH : closureIn I A ≤ closureIn L A := by
    rw [closureIn_eq_iSup_gLBConj I A, closureIn_eq_iSup_gLBConj L A]
    exact iSup₂_le fun a ha =>
      (gLBConj_mono (g := a) hIL).trans (le_biSup (fun g => GLBConj g L) ha)
  have hsup : sSup ((fun a => GLBConj a L) '' (A : Set G)) = closureIn L A := by
    rw [closureIn_eq_iSup_gLBConj L A]
    exact sSup_image
  have hc : (⁅N, closureIn L A⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p C := by
    refine Subgroup.commutator_le.2 fun n hn k hk => ?_
    have hk' : k ∈ closureIn I A ⊔ GLAPPrimeCoreOf p C :=
      closureIn_le_closureIn_sup hp hL hIsup hAC hk
    have hkZ : k ∈ Subgroup.normalizer (GLAPPrimeCoreOf p C : Set G) ∧
        ∀ n ∈ N, ⁅n, k⁆ ∈ GLAPPrimeCoreOf p C := hZs hk'
    exact hkZ.2 n hn
  have h𝓛 : ∀ X ∈ (fun a => GLBConj a L) '' (A : Set G), GLAPComponent p C X := by
    rintro X ⟨a, ha, rfl⟩
    have haA : a ∈ A := ha
    show GLAPComponent p C (GLBConj a L)
    have h := glaPComponent_gLBConj hL a
    rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hAC haA))] at h
  have hNK : N ≤ sSup ((fun a => GLBConj a L) '' (A : Set G)) ⊔ GLAPPrimeCoreOf p C := by
    rw [hsup]
    exact hNI.trans (hIH.trans le_sup_left)
  have hc' : (⁅N, sSup ((fun a => GLBConj a L) '' (A : Set G))⁆ : Subgroup G) ≤
      GLAPPrimeCoreOf p C := by
    rw [hsup]
    exact hc
  exact le_glaPPrimeCoreOf_of_commutator_le hp _ h𝓛 hN hNK hc'

theorem lemma47 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h183 : Input18_3_4)
    (hKP : CFSG.Open.IsKProper G) (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Lemma47At G p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro t t' hrel hT
  obtain ⟨hIDC, -, hIK'⟩ := pumpRel_facts hp h183 hKP hsimple hnonab hrel
  obtain ⟨⟨hB, hx, hL⟩, ⟨hB', -, -⟩, hxB', hdec, hx'B', hx'L, -⟩ := hrel
  set B := t.1
  set x := t.2.1
  set L := t.2.2
  set B' := t'.1
  set x' := t'.2.1
  set L' := t'.2.2
  set C := Subgroup.centralizer ({x} : Set G)
  set C' := Subgroup.centralizer ({x'} : Set G)
  set O := GLAPPrimeCoreOf p C
  set A := B ⊓ B'
  have hBC : B ≤ C := isElemAbelian_le_centralizer hB.1 hx.1
  have hB'C : B' ≤ C := isElemAbelian_le_centralizer hB'.1 hxB'
  have hB'C' : B' ≤ C' := isElemAbelian_le_centralizer hB'.1 hx'B'
  have hAC : A ≤ C := inf_le_left.trans hBC
  have hAD : A ≤ C ⊓ C' := le_inf hAC (inf_le_right.trans hB'C')
  have hB'p : IsPGroup p B' := isPGroup_of_isElemAbelian hB'.1
  have hAp : IsPGroup p A := hB'p.to_le inf_le_right
  have hO : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp C
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p C
  rw [nGen_le_iff] at hT ⊢
  push Not at hT ⊢
  obtain ⟨T, hTK, hT2, hBT, hTO⟩ := hT
  obtain ⟨S, hSHO, hS2, hAS, hSO⟩ :=
    exists_two_subgroup_le_closureIn_sup hp hp2 hL hBC inf_le_left hAp hTK hT2 hBT hTO
  set H := closureIn L A
  have hHC : H ≤ C := closureIn_le_of_le hL.1 (fun a ha => Subgroup.le_normalizer (hAC ha))
  have hOC : O ≤ C := Subgroup.map_subtype_le _
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hB'.1 hx'B'
  obtain ⟨hIc, -, -, -, hIsup, -⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  set I := GLAPLayer p (L ⊓ C')
  have hIL : I ≤ L := hIc.1.trans inf_le_left
  set H' := closureIn I A
  have hH'D : H' ≤ C ⊓ C' := closureIn_le_of_le hIDC.1 (fun a ha => Subgroup.le_normalizer (hAD ha))
  have hcomm : ∀ c ∈ B', CentMod p L c → c ∈ Subgroup.normalizer (H : Set G) ∧
      ∀ h ∈ H ⊔ O, ⁅h, c⁆ ∈ O := fun c hc hcL =>
    commutator_mem_of_centMod_closureIn hp hL (hB'C hc) hAC
      (fun a ha => isElemAbelian_commute hB'.1 ha.2 hc) hcL
  have hB'SO : B' ≤ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := by
    intro b hb
    obtain ⟨u, hu, v, hv, hvL, rfl⟩ := hdec b hb
    refine Subgroup.mul_mem _ (mem_normalizer_sup (hAS hu) (hCO (hAC hu))) ?_
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    have hyHO : y ∈ H ⊔ O := sup_le hSHO le_sup_right hy
    have h1 : ⁅y⁻¹, v⁆ ∈ O := (hcomm v hv hvL).2 _ ((H ⊔ O).inv_mem hyHO)
    have e : v * y * v⁻¹ = y * ⁅y⁻¹, v⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ hy (Subgroup.mem_sup_right h1)
  have hB'H' : B' ≤ Subgroup.normalizer (H' : Set G) := by
    intro b hb
    obtain ⟨u, hu, v, hv, hvL, rfl⟩ := hdec b hb
    refine Subgroup.mul_mem _ (le_normalizer_closureIn I A hu) ?_
    have hvLC' : v ∈ Subgroup.normalizer ((L ⊓ C' : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, mem_normalizer_iff_gLBConj_eq.1 hvL.1,
        mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hB'C' hv))]
    have hvA : v ∈ Subgroup.normalizer (A : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun a ha =>
        isElemAbelian_commute hB'.1 ha.2 hv)
    exact mem_normalizer_closureIn (mem_normalizer_glaPLayer hvLC') hvA
  obtain ⟨T', hT'H', hT'2, hB'T', hT'O⟩ := exists_le_of_le_sup hp hp2 hS2
    (hSHO.trans (sup_le (closureIn_le_closureIn_sup hp hL hIsup hAC) le_sup_right)) hSO hO
    (hH'D.trans (inf_le_left.trans hCO)) (hSHO.trans (sup_le hHC hOC |>.trans hCO)) hB'p hB'SO
    hB'H' (hB'C.trans hCO)
  have hH'K' : H' ≤ closureIn L' B' :=
    closureIn_le_of_le hIK' (inf_le_right.trans (le_normalizer_closureIn L' B'))
  refine ⟨T', hT'H'.trans hH'K', hT'2, hB'T', fun hT'O' => hT'O ?_⟩
  have hID : ∀ a ∈ A, GLAPComponent p (C ⊓ C') (GLBConj a I) := fun a ha => by
    have := glaPComponent_gLBConj hIDC a
    rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hAD ha))] at this
  have hN : ¬ p ∣ Nat.card (H' ⊓ GLAPPrimeCoreOf p C' : Subgroup G) := fun h =>
    not_dvd_card_glaPPrimeCoreOf hp C' (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hIN : H' ≤ Subgroup.normalizer ((H' ⊓ GLAPPrimeCoreOf p C' : Subgroup G) : Set G) :=
    fun h hh => Prop53.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hh)
      (le_normalizer_glaPPrimeCoreOf p C' (hH'D.trans inf_le_right hh))
  exact (le_inf hT'H' hT'O').trans
    (le_glaPPrimeCoreOf_of_le_closureIn hp hL hIL hIsup hAC hID hN inf_le_left hIN)

end CFSG.LocalAnalysis.GLTheoremA
