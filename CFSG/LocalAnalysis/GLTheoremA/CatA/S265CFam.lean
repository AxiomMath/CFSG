module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallHolds
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open scoped commutatorElement

section Cfg

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem qsCfg_inf_centMod_eq {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSCfg p S B T x D K) : B ⊓ centModSubgroup p S = Subgroup.zpowers x := by
  ext c
  constructor
  · rintro ⟨hcB, hc⟩
    exact (h.centB c hcB).1 (centMod_iff.2 hc)
  · intro hc
    have hcB : c ∈ B := (Subgroup.zpowers_le.2 h.xB) hc
    exact ⟨hcB, centMod_iff.1 ((h.centB c hcB).2 hc)⟩

theorem qsCfg_card_zpowers {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSCfg p S B T x D K) : Nat.card (Subgroup.zpowers x) = p := by
  haveI := Fact.mk h.prime
  rw [Nat.card_zpowers, orderOf_eq_prime (h.elem.2 x h.xB) h.x1]

theorem qsCfg_rank {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSCfg p S B T x D K) : p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p S) ≤ Nat.card B := by
  rw [qsCfg_inf_centMod_eq h, qsCfg_card_zpowers h, ← pow_succ]
  exact h.big

theorem qsCfg_exists_gen {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSCfg p S B T x D K) :
    ∃ y ∈ D, y ∉ Subgroup.zpowers x ∧ D = Dgrp y x ∧
      S ⊓ Subgroup.centralizer (D : Set Ω) = S ⊓ cx y := by
  obtain ⟨hDB, -, hDcard, hxD, -, -, -⟩ := h.std
  have hp := h.prime
  have hzx : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.2 hxD
  obtain ⟨y, hyD, hyx⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ Subgroup.zpowers x := fun y hy => hcon y hy
    have h1 : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    rw [hDcard, qsCfg_card_zpowers h] at h1
    have h2 : p < p ^ 2 := by
      have := hp.two_le
      nlinarith
    omega
  have hyB : y ∈ B := hDB hyD
  have hordy : Nat.card (Subgroup.zpowers y) = p := by
    haveI := Fact.mk hp
    have hy1 : y ≠ 1 := fun h1 => hyx (h1 ▸ (Subgroup.zpowers x).one_mem)
    rw [Nat.card_zpowers, orderOf_eq_prime (h.elem.2 y hyB) hy1]
  have hcardD' : Nat.card ↥(Dgrp y x) = p ^ 2 := by
    rw [dgrp_eq]
    exact s265_card_sup hp h.elem (Subgroup.zpowers_le.2 h.xB)
      (by rw [qsCfg_card_zpowers h, pow_one]) hyB hyx hordy
  have hle : Dgrp y x ≤ D := by
    rw [dgrp_eq]
    exact sup_le hzx (Subgroup.zpowers_le.2 hyD)
  have hDeq : D = Dgrp y x :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardD', hDcard])).symm
  refine ⟨y, hyD, hyx, hDeq, ?_⟩
  have hSx : S ≤ Subgroup.centralizer ({x} : Set Ω) := fun s _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (h.xcen s)
  rw [hDeq]
  exact inf_cs_dgrp hSx

theorem qsCfg_isComponentOf {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSCfg p S B T x D K) {y : Ω} (hy : S ⊓ Subgroup.centralizer (D : Set Ω) = S ⊓ cx y) :
    IsComponentOf K (S ⊓ cx y) := by
  obtain ⟨-, -, -, -, -, hKcomp, -⟩ := h.std
  rw [← hy]
  exact hKcomp

theorem card_pSimple_dvd (p : ℕ) (K : Subgroup Ω) : Nat.card (PSimple p K) ∣ Nat.card K :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

theorem qsCfg_le_normalizer {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSCfg p S B T x D K) : B ≤ Subgroup.normalizer (S : Set Ω) := by
  rw [Subgroup.normalizer_eq_top_iff.2 h.normal]
  exact le_top

@[expose] def isTitsIdx : TauCeti.CFSGIndex → Prop :=
  onLie fun | .tits => True | _ => False

@[expose] def isE7TwoIdx : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E7 q => q.card = 2 | _ => False

@[expose] def isE8TwoIdx : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E8 q => q.card = 2 | _ => False

theorem catalogIs_tyC_cases {X : Type} [Group X] (h : catalogIs X tyC) :
    catalogIs X S9.isTD4two ∨ catalogIs X S9.isF4two ∨ catalogIs X S9.isTE6two ∨ catalogIs X isTitsIdx ∨
      catalogIs X isG2der := by
  obtain ⟨i, hi, he⟩ := h
  rcases hi with h1 | h1 | h1 | h1 | h1
  · exact Or.inl ⟨i, h1, he⟩
  · exact Or.inr (Or.inl ⟨i, h1, he⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, h1, he⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, h1, he⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, h1, he⟩)))

theorem qsCfg_dynkin_data {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSCfg 3 S B T x D K)
    (h3 : 3 ∣ Nat.card K) :
    ∃ y ∈ B, ¬ CentMod 3 S y ∧ GLAPComponent 3 (S ⊓ Subgroup.centralizer ({y} : Set Ω)) K := by
  obtain ⟨y, hyD, hyx, -, hSy⟩ := qsCfg_exists_gen h
  obtain ⟨hDB, -, -, -, -, -, -⟩ := h.std
  have hyB : y ∈ B := hDB hyD
  exact ⟨y, hyB, fun hc => hyx ((h.centB y hyB).1 hc),
    CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_of_isComponentOf
      (qsCfg_isComponentOf h hSy) h3⟩

end Cfg

@[expose] def DynkinItemCThree : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L K A : Subgroup Γ) (y : Γ),
    catalogIs (PSimple 3 L) I141F.isLie2NoTits → IsElemAbelian 3 A → A ≤ Subgroup.normalizer (L : Set Γ) →
    S10.InnDiagOn 3 A L → y ∈ A → ¬ CentMod 3 L y →
    GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set Γ)) K →
    ¬ catalogIs (PSimple 3 K) S9.isF4two ∧ ¬ catalogIs (PSimple 3 K) isTitsIdx ∧
      (catalogIs (PSimple 3 K) S9.isTE6two → catalogIs (PSimple 3 L) (fun i => isE7TwoIdx i ∨ isE8TwoIdx i)) ∧
      (catalogIs (PSimple 3 K) S9.isTD4two → catalogIs (PSimple 3 L) S9.isTE6two)

@[expose] def QSFamCTE6 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL 3 S B T x D K →
    catalogIs (PSimple 3 K) S9.isTE6two → catalogIs (PSimple 3 S) (fun i => isE7TwoIdx i ∨ isE8TwoIdx i) →
    QSConcl 3 S B D K

@[expose] def QSFamCTD4 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL 3 S B T x D K →
    catalogIs (PSimple 3 K) S9.isTD4two → catalogIs (PSimple 3 S) S9.isTE6two → QSConcl 3 S B D K

section Orders

theorem three_dvd_card_of_tyC {X : Type} [Group X] [Finite X] (h : catalogIs X tyC) : 3 ∣ Nat.card X := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie idx =>
    rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds idx X ⟨e⟩]
    obtain ⟨d, hv⟩ := idx
    rcases hi with h1 | h1 | h1 | h1 | h1 <;>
      (cases d <;> simp only [S9.isTD4two, S9.isF4two, S9.isTE6two, onLie] at h1 <;>
        first
          | exact h1.elim
          | (simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula, h1]; decide)
          | (rename_i r q; simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula]
             rcases r with _ | _ | _ | r <;> simp_all <;> decide))
  | cyclic _ _ => rcases hi with h1 | h1 | h1 | h1 | h1 <;> simp [S9.isTD4two, S9.isF4two, S9.isTE6two, onLie] at h1
  | alternating _ _ => rcases hi with h1 | h1 | h1 | h1 | h1 <;> simp [S9.isTD4two, S9.isF4two, S9.isTE6two, onLie] at h1
  | sporadic _ => rcases hi with h1 | h1 | h1 | h1 | h1 <;> simp [S9.isTD4two, S9.isF4two, S9.isTE6two, onLie] at h1


end Orders

section Small

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem qsCfg_lie2NoTits
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSCfg 3 S B T x D K) :
    catalogIs (PSimple 3 S) I141F.isLie2NoTits := by
  by_contra ht
  have hsmall : catalogIs (PSimple 3 S) I141F.isRankSmall := by
    rcases h.chev with hc | hc
    · exact I141F.catalogIs_rankSmall_of_char2 hc ht
    · exact S10.catalogIs_imp (fun i hi => Or.inr (Or.inl hi)) hc
  exact I141F.i141RankSmall_holds 3 Nat.prime_three (by norm_num) Ω S B hsmall h.elem h.inn (qsCfg_rank h)

end Small

section Dyn

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem qsCfg_not_isG2der
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSCfg 3 S B T x D K) :
    ¬ catalogIs (PSimple 3 K) isG2der := by
  intro hK
  obtain ⟨y, hyD, hyx, -, hSy⟩ := qsCfg_exists_gen h
  obtain ⟨hDB, -, -, -, -, -, -⟩ := h.std
  have hyB : y ∈ B := hDB hyD
  have h3 : 3 ∣ Nat.card K := by
    have hd := card_pSimple_dvd 3 K
    rw [I141F.card_eq_6048_of_isG2der hK] at hd
    exact (show 3 ∣ 6048 by norm_num).trans hd
  have hKp : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({y} : Set Ω)) K :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_of_isComponentOf
      (qsCfg_isComponentOf h hSy) h3
  have hyC : ¬ CentMod 3 S y := fun hc => hyx ((h.centB y hyB).1 hc)
  exact I141F.i141DynkinAt_of_facts I141F.i141DynkinLie_holds I141F.i141RankSmall_holds Ω 3 ⊤ S K B y
    Nat.prime_three (by norm_num) h.comp h.chev h.elem (qsCfg_le_normalizer h) h.inn (qsCfg_rank h) hyB hyC hKp hK

theorem qSFamC_of_facts
    (hDyn : DynkinItemCThree) (hTE6 : QSFamCTE6) (hTD4 : QSFamCTD4) : S265.QSFamC := by
  intro p Ω _ _ S B T x D K hN hp3 hC
  subst hp3
  have h := hN.cfg
  have h3 : 3 ∣ Nat.card K := (three_dvd_card_of_tyC hC).trans (card_pSimple_dvd 3 K)
  obtain ⟨y, hyB, hyC, hKp⟩ := qsCfg_dynkin_data h h3
  obtain ⟨hF4, hTits, hE, hT⟩ :=
    hDyn Ω S K B y (qsCfg_lie2NoTits h) h.elem (qsCfg_le_normalizer h) h.inn hyB hyC hKp
  rcases catalogIs_tyC_cases hC with hc | hc | hc | hc | hc
  · exact hTD4 Ω S B T x D K hN hc (hT hc)
  · exact (hF4 hc).elim
  · exact hTE6 Ω S B T x D K hN hc (hE hc)
  · exact (hTits hc).elim
  · exact (qsCfg_not_isG2der h hc).elim

end Dyn

end CFSG.LocalAnalysis.GLTheoremA.S265C

end
