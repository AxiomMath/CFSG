module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSDiagD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSSeed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GVac

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Bridge

variable {Ω : Type} [Group Ω]

theorem t263_inf_centralizer_sup (S D : Subgroup Ω) (x : Ω) :
    S ⊓ Subgroup.centralizer ((D ⊔ Subgroup.zpowers x : Subgroup Ω) : Set Ω) =
      (S ⊓ Subgroup.centralizer ({x} : Set Ω)) ⊓ Subgroup.centralizer (D : Set Ω) := by
  ext g
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgS, hg⟩
    have hx : x ∈ D ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    refine ⟨⟨hgS, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
    · exact (Subgroup.mem_centralizer_iff.1 hg x hx).symm
    · exact Subgroup.mem_centralizer_iff.2 fun h hh => Subgroup.mem_centralizer_iff.1 hg h
        (Subgroup.mem_sup_left hh)
  · rintro ⟨⟨hgS, hgx⟩, hgD⟩
    refine ⟨hgS, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have hle : D ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({g} : Set Ω) := by
      refine sup_le (fun d hd => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hgD d hd)
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hgx).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

end Bridge

theorem t263DiagStep_holds : T263DiagStep := by
  intro p hp hp2 Ω _ _ S B x J W hSn hSq hSp hBel hxB hxC hJ hJq hWJ hW2 hWB hWnc
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup Ω := S ⊓ Subgroup.centralizer ({x} : Set Ω) with hX
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => isElemAbelian_commute hBel ha hb
  have hBX : B ≤ Subgroup.normalizer (X : Set Ω) := by
    intro b hb
    refine mem_normalizer_inf (t263_normalizer_of_normal hSn) (Subgroup.le_normalizer ?_)
    exact Subgroup.mem_centralizer_singleton_iff.2 (hBc x hxB b hb).symm
  set H : Subgroup Ω := X ⊔ B with hH
  have hXH : X ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hJX : J ≤ X := hJ.1
  have hker0 : ¬ p ∣ Nat.card H.subtype.ker := by
    rw [Subgroup.ker_subtype, Subgroup.card_bot]
    exact hp.not_dvd_one
  have hcopι : ∀ Y₀ : Subgroup ↥H, Nat.Coprime p (Nat.card ↥(Y₀ ⊓ H.subtype.ker)) :=
    CFSG.LocalAnalysis.GLTheoremA.S267.coprime_inf_ker hp H.subtype hker0
  set M : Subgroup ↥H := X.subgroupOf H with hM
  set B' : Subgroup ↥H := B.subgroupOf H with hB'
  have hMmap : M.map H.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXH
  have hBmap : B'.map H.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBH
  have hJ' : GLAPComponent p (M.map H.subtype) J := by
    rw [hMmap]
    exact hJ
  obtain ⟨JH, hJH, hJHmap⟩ := exists_glaPComponent_map_eq hp H.subtype (hcopι M) hJ'
  have hMB : M ⊔ B' = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, hMmap, hBmap, Subgroup.map_top, Subgroup.range_subtype]
  have hB'el : IsElemAbelian p B' := CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_subgroupOf hBel H
  have hB'M : B' ≤ Subgroup.normalizer (M : Set ↥H) := by
    rw [hM, normalizer_subgroupOf_eq hXH]
    intro b hb
    exact Subgroup.mem_subgroupOf.2 (hBX (Subgroup.mem_subgroupOf.1 hb))
  have hWH : W ≤ H := hWJ.trans (hJX.trans hXH)
  set WH : Subgroup ↥H := W.subgroupOf H with hWHdef
  have hWHmap : WH.map H.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWH
  have hWHJ : WH ≤ JH := by
    intro w hw
    have hwW : (w : Ω) ∈ W := Subgroup.mem_subgroupOf.1 hw
    have hwJ : (w : Ω) ∈ JH.map H.subtype := by
      rw [hJHmap]
      exact hWJ hwW
    obtain ⟨j, hj, hjw⟩ := hwJ
    have hjw' : j = w := Subtype.ext hjw
    rwa [hjw'] at hj
  have hWH2 : IsPGroup 2 ↥WH := hW2.comap_subtype
  have hWHB : B' ⊓ Subgroup.normalizer (JH : Set ↥H) ≤ Subgroup.normalizer (WH : Set ↥H) := by
    rintro b ⟨hbB, hbJ⟩
    have hbB' : (b : Ω) ∈ B := Subgroup.mem_subgroupOf.1 hbB
    have hbJ' : (b : Ω) ∈ Subgroup.normalizer (J : Set Ω) := by
      rw [← hJHmap]
      exact Subgroup.le_normalizer_map H.subtype ⟨b, hbJ, rfl⟩
    have hbW : (b : Ω) ∈ Subgroup.normalizer (W : Set Ω) := hWB ⟨hbB', hbJ'⟩
    rw [hWHdef, normalizer_subgroupOf_eq hWH]
    exact Subgroup.mem_subgroupOf.2 hbW
  have hWHnc : ¬ WH ≤ GLAPPrimeCoreOf p JH := by
    intro h
    apply hWnc
    have h1 := Subgroup.map_mono (f := H.subtype) h
    rw [hWHmap, CFSG.LocalAnalysis.GLTheoremA.S267.map_glaPPrimeCoreOf hp H.subtype hker0 JH,
      hJHmap] at h1
    exact h1
  obtain ⟨DH, IH, hDH, hIH, hBIH, -, ⟨e⟩, TH, hTHI, hTH2, hBTH, hTHnc⟩ :=
    t263_diag_abstract hp hp2 hMB hB'el hB'M hJH hWHJ hWH2 hWHB hWHnc
  set I : Subgroup Ω := IH.map H.subtype with hIdef
  set D : Subgroup Ω := DH.map H.subtype ⊔ Subgroup.zpowers x with hDdef
  have hDB : D ≤ B := by
    refine sup_le ?_ (Subgroup.zpowers_le.2 hxB)
    rw [← hBmap]
    exact Subgroup.map_mono hDH
  have hcentmap : (M ⊓ Subgroup.centralizer (DH : Set ↥H)).map H.subtype =
      X ⊓ Subgroup.centralizer ((DH.map H.subtype : Subgroup Ω) : Set Ω) := by
    ext y
    constructor
    · rintro ⟨m, ⟨hm, hmc⟩, rfl⟩
      refine ⟨Subgroup.mem_subgroupOf.1 hm, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hmc d hd)
    · rintro ⟨hyX, hyc⟩
      refine ⟨⟨y, hXH hyX⟩, ⟨Subgroup.mem_subgroupOf.2 hyX, Subgroup.mem_centralizer_iff.2 ?_⟩, rfl⟩
      intro d hd
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hyc (d : Ω) ⟨d, hd, rfl⟩)
  have hIcomp : GLAPComponent p (X ⊓ Subgroup.centralizer ((DH.map H.subtype : Subgroup Ω) : Set Ω)) I := by
    have h1 := glaPComponent_map hp H.subtype (hcopι _) hIH
    rwa [hcentmap] at h1
  have hIcomp' : GLAPComponent p (S ⊓ Subgroup.centralizer (D : Set Ω)) I := by
    rw [hDdef, t263_inf_centralizer_sup]
    exact hIcomp
  have hBN : ∀ Z : Subgroup ↥H, B' ≤ Subgroup.normalizer (Z : Set ↥H) →
      B ≤ Subgroup.normalizer ((Z.map H.subtype : Subgroup Ω) : Set Ω) := by
    intro Z hZ b hb
    exact Subgroup.le_normalizer_map H.subtype ⟨⟨b, hBH hb⟩, hZ (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hXlt : Nat.card ↥X < Nat.card ↥S := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => hxC ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : s ∈ X := by rw [h]; exact hs
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h1).2
  have hlt : Nat.card (PQuot p I) < Nat.card ↥S := by
    have h1 : Nat.card (PQuot p I) ≤ Nat.card ↥I :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card ↥I ≤ Nat.card ↥X := Subgroup.card_le_of_le (hIcomp.1.trans inf_le_left)
    omega
  have hiso : Nonempty (PSimple p I ≃* PSimple p J) := by
    have h1 : Nonempty (PSimple p IH ≃* PSimple p (IH.map H.subtype)) :=
      t263_pSimple_map_nonempty hp H.subtype IH (hcopι IH)
    have h2 : Nonempty (PSimple p JH ≃* PSimple p (JH.map H.subtype)) :=
      t263_pSimple_map_nonempty hp H.subtype JH (hcopι JH)
    rw [hJHmap] at h2
    obtain ⟨e1⟩ := h1
    obtain ⟨e2⟩ := h2
    exact ⟨e1.symm.trans (e.trans e2)⟩
  refine ⟨D, I, hDB, hIcomp', hBN IH hBIH,
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hIcomp', hiso, hlt,
    TH.map H.subtype, Subgroup.map_mono hTHI, hTH2.map _, hBN TH hBTH, ?_⟩
  intro h
  apply hTHnc
  rw [hIdef, ← CFSG.LocalAnalysis.GLTheoremA.S267.map_glaPPrimeCoreOf hp H.subtype hker0 IH] at h
  exact (Subgroup.map_le_map_iff_of_injective H.subtype_injective).1 h

theorem t263Desc_of_seed_proved {Q : TauCeti.CFSGIndex → Prop} (hS : T263DescSeed Q) : T263Desc Q :=
  t263Desc_of_seed t263DiagStep_holds hS

end CFSG.LocalAnalysis.GLTheoremA.T263

end
