module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs103
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinctDefs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95B
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cAut
public import CFSG.CharacterTheory.Burnside
public import CFSG.Holt.General.OrbitCountBasic
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Glue
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

theorem lemma103_rawDatum_mono {lab : CFSG.Assembly.LargeEvenLabel}
    {Q Q' : CFSG.Assembly.LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → Q' R I F)
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) : CFSG.Assembly.LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact ⟨K, i1, i2, hK, b, c, hbc, hQQ' _ _ _ hq⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact ⟨K, i1, i2, hK, hQQ' _ _ _ hq⟩)

theorem lemma103_rawDatum_or {lab : CFSG.Assembly.LargeEvenLabel}
    {A B : CFSG.Assembly.LargeEvenRawCont}
    (h : CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F => A R I F ∨ B R I F) :
    CFSG.Assembly.LargeEvenRawDatum lab A ∨ CFSG.Assembly.LargeEvenRawDatum lab B := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       rcases hq with hq | hq
       · exact Or.inl ⟨K, i1, i2, hK, b, c, hbc, hq⟩
       · exact Or.inr ⟨K, i1, i2, hK, b, c, hbc, hq⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       rcases hq with hq | hq
       · exact Or.inl ⟨K, i1, i2, hK, hq⟩
       · exact Or.inr ⟨K, i1, i2, hK, hq⟩)

theorem lemma103_rawDatum_exists {lab : CFSG.Assembly.LargeEvenLabel} {Q : CFSG.Assembly.LargeEvenRawCont}
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, _, _, -, b, c, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)
    | (obtain ⟨K, _, _, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)

theorem lemma103_marking_mono {X : Type} [Group X] {P P' : CFSG.Assembly.LargeEvenMarkProp X}
    (hPP' : ∀ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → P' lab R I F θ)
    (h : CFSG.Assembly.LargeEvenMarking X P) : CFSG.Assembly.LargeEvenMarking X P' := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, lemma103_rawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hPP' lab R I F θ hθ⟩

theorem lemma103_marking_or {X : Type} [Group X] {P P' : CFSG.Assembly.LargeEvenMarkProp X}
    (h : CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∨ P' lab R I F θ) :
    CFSG.Assembly.LargeEvenMarking X P ∨ CFSG.Assembly.LargeEvenMarking X P' := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hraw' := lemma103_rawDatum_mono (Q' := fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ : X ⧸ Subgroup.center X ≃* R, P lab R I F θ) ∨
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ : X ⧸ Subgroup.center X ≃* R, P' lab R I F θ))
    (fun R _ I F hq => by
      obtain ⟨hs, hna, θ, hθ⟩ := hq
      rcases hθ with h1 | h2
      · exact Or.inl ⟨hs, hna, θ, h1⟩
      · exact Or.inr ⟨hs, hna, θ, h2⟩) hraw
  rcases lemma103_rawDatum_or hraw' with hA | hB
  · exact Or.inl ⟨hX, lab, hlab, hA⟩
  · exact Or.inr ⟨hX, lab, hlab, hB⟩

theorem lemma103_marking_witness {X : Type} [Group X] {P : CFSG.Assembly.LargeEvenMarkProp X}
    (h : CFSG.Assembly.LargeEvenMarking X P) :
    ∃ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ := by
  obtain ⟨-, lab, -, hraw⟩ := h
  obtain ⟨R, inst, I, F, hcont⟩ := lemma103_rawDatum_exists hraw
  obtain ⟨-, -, θ, hθ⟩ := hcont
  exact ⟨lab, R, inst, I, F, θ, hθ⟩

structure Lemma103Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  aut : AutCalcAt G p
  lemma102 : Lemma102Inputs G p
  i264 : I264At G p
  i263 : I263UsedAt G p
  i131 : I131TD4At G
  i265 : I265UsedAt G p
  i712 : I712At G p
  i91 : I91At G
  i147 : I147At G
  k3 : K3NotChev2At
  mult : MultU48At G
  i91u : I91U48At G
  i1024 : I1024aU42At G
  i1015 : I1015U42At G
  i8 : I8U48At G
  i2018 : I2018At G
  i91part : I91CentPartAt G p
  lbal : LBalanceAt G 3
  i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4
  i183x : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_12
  aut48 : AutU48At G
  field_n : FieldNAt G p
  g2 : TD4G2At G
  single38 : I112SingleU38At G
  more : Lemma105MoreInputs G
  dist : CatDistinctAt

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

@[expose] def isTwistedA : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA _ _ => True | _ => False

theorem isSimple_of_catalogIs_twistedA {S : Type} [Group S] (h : catalogIs S isTwistedA) : IsSimpleGroup S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [isTwistedA, onLie] at hi
  | alternating n hn => simp [isTwistedA, onLie] at hi
  | sporadic s => simp [isTwistedA, onLie] at hi
  | lie j =>
    obtain ⟨d, hv⟩ := j
    simp only [isTwistedA, onLie] at hi
    split at hi
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity S _ _ _
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA _ _ hv e)).2
    · exact absurd hi id

theorem isTwistedA_of_isU4eight {i : TauCeti.CFSGIndex} (h : S9.isU4eight i) : isTwistedA i := by
  cases i with
  | cyclic p hp => simp [S9.isU4eight, onLie] at h
  | alternating n hn => simp [S9.isU4eight, onLie] at h
  | sporadic s => simp [S9.isU4eight, onLie] at h
  | lie j =>
    obtain ⟨d, hv⟩ := j
    simp only [S9.isU4eight, isTwistedA, onLie] at h ⊢
    split at h
    · simp only
    · exact absurd h id

theorem isTwistedA_of_isU4two {i : TauCeti.CFSGIndex} (h : S9.isU4two i) : isTwistedA i := by
  cases i with
  | cyclic p hp => simp [S9.isU4two, onLie] at h
  | alternating n hn => simp [S9.isU4two, onLie] at h
  | sporadic s => simp [S9.isU4two, onLie] at h
  | lie j =>
    obtain ⟨d, hv⟩ := j
    simp only [S9.isU4two, isTwistedA, onLie] at h ⊢
    split at h
    · simp only
    · exact absurd h id

theorem isTwistedA_of_isU3eight {i : TauCeti.CFSGIndex} (h : S9.isU3eight i) : isTwistedA i := by
  cases i with
  | cyclic p hp => simp [S9.isU3eight, onLie] at h
  | alternating n hn => simp [S9.isU3eight, onLie] at h
  | sporadic s => simp [S9.isU3eight, onLie] at h
  | lie j =>
    obtain ⟨d, hv⟩ := j
    simp only [S9.isU3eight, isTwistedA, onLie] at h ⊢
    split at h
    · simp only
    · exact absurd h id

theorem isSimple_of_isU4eight {S : Type} [Group S] (h : catalogIs S S9.isU4eight) : IsSimpleGroup S :=
  isSimple_of_catalogIs_twistedA (catalogIs_imp (fun _ hi => isTwistedA_of_isU4eight hi) h)

theorem isSimple_of_isU4two {S : Type} [Group S] (h : catalogIs S S9.isU4two) : IsSimpleGroup S :=
  isSimple_of_catalogIs_twistedA (catalogIs_imp (fun _ hi => isTwistedA_of_isU4two hi) h)

theorem isSimple_of_isU3eight {S : Type} [Group S] (h : catalogIs S S9.isU3eight) : IsSimpleGroup S :=
  isSimple_of_catalogIs_twistedA (catalogIs_imp (fun _ hi => isTwistedA_of_isU3eight hi) h)

private theorem lemma103_le_glaPPrimeCoreOf_self {p : ℕ} {H : Subgroup G}
    (hcop : Nat.Coprime p (Nat.card H)) : H ≤ GLAPPrimeCoreOf p H := by
  have htop : (⊤ : Subgroup ↥H) ≤ GLAPPrimeCore p ↥H :=
    le_sSup (show (⊤ : Subgroup ↥H).Normal ∧ Nat.Coprime p (Nat.card (⊤ : Subgroup ↥H)) from
      ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  intro h hh
  exact Subgroup.mem_map.2 ⟨⟨h, hh⟩, htop (Subgroup.mem_top _), rfl⟩

private theorem lemma103_closureIn_le_of_normalizer {I H K : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (K : Set G)) (hIK : I ≤ K) : closureIn I H ≤ K := by
  refine iSup₂_le fun a ha => ?_
  rintro _ ⟨i, hi, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (hH ha) i).1 (hIK hi)

private theorem lemma103_layer_le_normalizer {p : ℕ} (hp : p.Prime) {X K' : Subgroup G}
    (hK' : GLAPComponent p X K') : GLAPLayer p X ≤ Subgroup.normalizer (K' : Set G) := by
  refine sSup_le fun K'' hK'' => ?_
  by_cases hKK : K'' = K'
  · rw [hKK]
    exact Subgroup.le_normalizer
  · intro k hk
    exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp hK' hK''
      (Ne.symm hKK) hk

private theorem lemma103_closureIn_self_of_component {p : ℕ} (hp : p.Prime) {X Y J K' : Subgroup G}
    (hK' : GLAPComponent p X K') (hJ : GLAPComponent p Y J) (hJK : J ≤ K') :
    closureIn J K' = K' := by
  classical
  have hK'K' : K' ≤ Subgroup.normalizer (K' : Set G) := Subgroup.le_normalizer
  set N : Subgroup G := closureIn J K' with hNdef
  have hNK : N ≤ K' := lemma103_closureIn_le_of_normalizer hK'K' hJK
  have hKN : K' ≤ Subgroup.normalizer (N : Set G) := le_normalizer_closureIn J K'
  have hJN : J ≤ N := le_closureIn_self J K'
  have hNX : N ≤ X := hNK.trans hK'.1
  have hNsub : IsSubnormal N X :=
    IsSubnormal.step hNK ((Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN) hK'.2.1
  have hO : GLAPPrimeCoreOf p K' ≤ GLAPPrimeCoreOf p X :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hK'.2.1
  have hJnot : ¬ J ≤ GLAPPrimeCoreOf p K' := by
    intro hJO
    have hcopX : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p X)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp X)
    have hcop : Nat.Coprime p (Nat.card J) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (hJO.trans hO)) hcopX
    have hJY : J ≤ GLAPPrimeCoreOf p Y := by
      have hinf := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hJ.2.1
      intro j hj
      have hjJ : j ∈ J ⊓ GLAPPrimeCoreOf p Y := by
        rw [hinf]
        exact lemma103_le_glaPPrimeCoreOf_self hcop hj
      exact hjJ.2
    have hbot : barX p Y J = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨y, hy, rfl⟩
      have hyO : (y : G) ∈ GLAPPrimeCoreOf p Y := hJY ((Subgroup.mem_subgroupOf).1 hy)
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.1 hyO
      have hwy' : w = y := Subtype.ext hwy
      rw [Subgroup.mem_bot]
      rw [← hwy'] at hy ⊢
      exact (QuotientGroup.eq_one_iff w).2 hw
    have hsub : Subsingleton ↥(barX p Y J) := by
      rw [hbot]
      infer_instance
    have hnt : Nontrivial ↥(barX p Y J) := isQuasisimple_nontrivial hJ.2.2.1.2.2
    exact not_subsingleton _ hsub
  have hQq : CFSG.Open.IsQuasisimple (PQuot p K') := isQuasisimple_pQuot_of_glaPComponent hp hK'
  haveI hNn : (N.subgroupOf K').Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  let π : ↥K' →* PQuot p K' := QuotientGroup.mk' (GLAPPrimeCore p ↥K')
  let M : Subgroup (PQuot p K') := (N.subgroupOf K').map π
  have hMn : M.Normal := hNn.map π (QuotientGroup.mk'_surjective _)
  let Jbar : Subgroup (PQuot p K') := (J.subgroupOf K').map π
  have hJM : Jbar ≤ M :=
    Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2 (hJN ((Subgroup.mem_subgroupOf).1 hx)))
  have hJc : ¬ Jbar ≤ Subgroup.center (PQuot p K') := by
    intro hc
    apply hJnot
    have hcomm : ⁅J, J⁆ ≤ GLAPPrimeCoreOf p K' := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      have ha' : a ∈ K' := hJK ha
      have hb' : b ∈ K' := hJK hb
      have hcen : π ⟨a, ha'⟩ ∈ Subgroup.center (PQuot p K') :=
        hc ⟨⟨a, ha'⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
      have key : π ⟨a, ha'⟩ * π ⟨b, hb'⟩ = π ⟨b, hb'⟩ * π ⟨a, ha'⟩ :=
        (Subgroup.mem_center_iff.1 hcen (π ⟨b, hb'⟩)).symm
      have hw1 : π (⟨a, ha'⟩ * ⟨b, hb'⟩ * ⟨a, ha'⟩⁻¹ * ⟨b, hb'⟩⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [key]
        group
      have hw2 : (⟨a, ha'⟩ * ⟨b, hb'⟩ * ⟨a, ha'⟩⁻¹ * ⟨b, hb'⟩⁻¹ : ↥K') ∈
          GLAPPrimeCore p ↥K' := (QuotientGroup.eq_one_iff _).1 hw1
      have hw3 : a * b * a⁻¹ * b⁻¹ ∈ GLAPPrimeCoreOf p K' :=
        Subgroup.mem_map.2 ⟨_, hw2, by simp⟩
      rw [commutatorElement_def]
      exact hw3
    rw [glaPComponent_perfect hJ] at hcomm
    exact hcomm
  have hMtop : M = ⊤ := by
    by_contra hne
    exact hJc (hJM.trans (le_center_of_normal_of_isQuasisimple hQq hMn hne))
  have hcover : ∀ k ∈ K', ∃ n ∈ N, n⁻¹ * k ∈ GLAPPrimeCoreOf p X := by
    intro k hk
    have hmem : π ⟨k, hk⟩ ∈ M := by
      rw [hMtop]
      exact Subgroup.mem_top _
    obtain ⟨z, hz, hzk⟩ := hmem
    have hzN : (z : G) ∈ N := Subgroup.mem_subgroupOf.1 hz
    have hrel : z⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore p ↥K' := (QuotientGroup.eq).1 hzk
    have hrelG : (z : G)⁻¹ * k ∈ GLAPPrimeCoreOf p K' :=
      Subgroup.mem_map.2 ⟨_, hrel, by simp⟩
    exact ⟨z, hzN, hO hrelG⟩
  have hbar : barX p X K' ≤ barX p X N := barX_le_of_forall hNX hcover
  by_contra hne
  have hlt : N < K' := lt_of_le_of_ne hNK hne
  exact hK'.2.2.2 N hlt hNsub (le_antisymm (barX_mono p hNK) hbar)

theorem closureIn_layer_eq_of_component {p : ℕ} (hp : p.Prime) {X Y J K' : Subgroup G}
    (hK' : GLAPComponent p X K') (hJ : GLAPComponent p Y J) (hJK : J ≤ K') :
    closureIn J (GLAPLayer p X) = K' := by
  apply le_antisymm
  · exact lemma103_closureIn_le_of_normalizer (lemma103_layer_le_normalizer hp hK') hJK
  · have h := lemma103_closureIn_self_of_component hp hK' hJ hJK
    calc K' = closureIn J K' := h.symm
      _ ≤ closureIn J (GLAPLayer p X) :=
        iSup₂_le fun a ha => le_iSup₂_of_le a ((le_sSup hK' : K' ≤ GLAPLayer p X) ha) le_rfl

@[expose] def CaseA (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b : G) : Prop :=
  ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ Dgrp b x ≤ E ∧
    GLAPLayer p (L ⊓ cs E) ≠ ⊥

@[expose] def HasTL (p : ℕ) (B L : Subgroup G) : Prop :=
  ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
    ¬ T ≤ GLAPPrimeCoreOf p L

structure CaseU (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b : G) :
    Prop where
  p3 : p = 3
  rank : GLATwoLocalRank 3 G = 4
  centRank : ∃ A : Subgroup G, IsElemAbelian 3 A ∧ A ≤ cs B ∧ 3 ^ 5 ≤ Nat.card A
  L_iso : catalogIs ↥L S9.isU4eight
  I_iso : catalogIs (PSimple p (Ipart p L b)) S9.isU4two
  decomp : ∃ E₂ : Subgroup G, E₂ ≤ Ipart p L b ∧ IsElemAbelian p E₂ ∧ Nat.card E₂ = p ^ 2 ∧
    B = Dgrp b x ⊔ E₂ ∧ Dgrp b x ⊓ E₂ = ⊥
  field : FieldOn p b L
  I_grp : catalogIs ↥(L ⊓ cx b) S9.isU4two
  I_eq : Ipart p L b = L ⊓ cx b
  I_core : GLAPPrimeCoreOf p (Ipart p L b) = ⊥

theorem dLevel_le_five (G : Type) [Group G] [Finite G] (p : ℕ) : dLevel G p ≤ 5 := by
  unfold dLevel
  refine csSup_le' ?_
  rintro j ⟨B, x, L, -, rfl⟩
  unfold tripleLevel
  split_ifs <;> omega

theorem dLevel_eq_five_of_gstar {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsS0 p B x L)
    (hG : IsGStar p B L) : dLevel G p = 5 := by
  have h2 := h.2
  unfold tripleLevel at h2
  rw [if_pos hG] at h2
  exact h2.symm

theorem isGStar_of_dLevel_eq_five {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsS0 p B x L)
    (hd : dLevel G p = 5) : IsGStar p B L := by
  classical
  by_contra hG
  have h2 := h.2
  unfold tripleLevel at h2
  rw [if_neg hG] at h2
  omega

theorem isGStar_of_caseA {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (h : CaseA p B x L b) : IsGStar p B L := by
  obtain ⟨E, hEB, hE, hcard, -, hne⟩ := h
  exact ⟨E, hEB, hE, hcard, by rwa [closureIn_eq_self hBN]⟩

theorem td4_gives_GStar (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hp3 : p = 3)
    (hbig : catalogIs (PSimple 3 L) (onLie isTrialityD4Big)) : IsGStar p B L := by
  subst hp3
  have hS := sstar_triple h.star
  have htd : IsTD4 3 L := catalogIs_imp (fun i hi => by
    cases i with
    | cyclic p hp => simp [onLie] at hi
    | alternating n hn => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie j =>
      obtain ⟨d, hv⟩ := j
      simp only [onLie, isTrialityD4Big] at hi ⊢
      split at hi
      · simp only
      · exact absurd hi id) hbig
  have hnb : NonInner 3 b L := by
    rcases h.prop with hf | ⟨-, -, hn⟩
    · exact absurd hf (hin.aut.td4_not_field _ L b hS.2.2 rfl htd)
    · exact hn
  exact isGStar_of_td4_big hc hin.g2 hS (sstar_norm h.star) h.mem hnb (h.td4_g2 rfl htd) hbig
    (sstar_chev2 hc h.star)

theorem dLevel_le_two_of_even (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hnG : ¬ IsGStar p B L)
    (hev : Even (Nat.card (GLAPPrimeCoreOf p (cx x)))) : dLevel G p ≤ 2 := by
  classical
  have hS := sstar_triple h.star
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := sstar_norm h.star
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hLc : L ≤ cx x := hS.2.2.1
  have hBc : B ≤ cx x := isElemAbelian_le_centralizer hS.1.1 hxB
  have hd : dLevel G p = fullCoverLevel p (PQuot p L) :=
    (fullCoverLevel_eq_dLevel (sstar_s0 h.star) hnG).symm
  have hne4 : fullCoverLevel p (PQuot p L) ≠ 4 := by
    intro h4
    have hrank : p ^ 4 ≤ Nat.card B := by
      rw [hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos hc.ctx.rank_ge
    have hNp : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p (cx x))) :=
      CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp (cx x)
    have hYN : L ⊔ B ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p (cx x) : Subgroup G) : Set G) :=
      sup_le (hLc.trans (le_normalizer_glaPPrimeCoreOf p (cx x)))
        (hBc.trans (le_normalizer_glaPPrimeCoreOf p (cx x)))
    have hMR : IsMaxRankIn p B (L ⊔ B) := isMaxRankIn_of_even hp hp2 hS.1 hev hNp hYN
    have hLne : L ≠ ⊤ := fun e => (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1)
      (top_le_iff.1 (by rw [← e]; exact hLc))
    have hKL : CFSG.Open.IsKGroup ↥L := isKGroup_of_isKProper hc.ctx.kProper hLne
    rcases hin.i264 hp hp2 B x L hS.1.1 hxB hx1 hS.2.2 hKL hBN hrank hMR h4 with
      ⟨E, hEB, hE, hcard, -, hEL⟩ | ⟨hp3, -, -, hbig, -⟩
    · apply hnG
      refine ⟨E, hEB, hE, hcard, ?_⟩
      rw [closureIn_eq_self hBN]
      exact hEL
    · exact hnG (td4_gives_GStar hc hin h hp3 hbig)
  have hne3 : fullCoverLevel p (PQuot p L) ≠ 3 := by
    intro h3
    have hK3 : K3Cover p (PQuot p L) := by
      unfold fullCoverLevel at h3
      by_cases h1 : K1Cover p (PQuot p L)
      · rw [if_pos h1] at h3
        omega
      · by_cases h2 : K2Cover p (PQuot p L)
        · rw [if_neg h1, if_pos h2] at h3
          omega
        · by_cases h3' : K3Cover p (PQuot p L)
          · exact h3'
          · rw [if_neg h1, if_neg h2, if_neg h3'] at h3
            omega
    exact hin.k3 p (PQuot p L) hK3 (sstar_chev2 hc h.star)
  have hle : fullCoverLevel p (PQuot p L) ≤ 2 := by
    have := fullCoverLevel_le_four p (PQuot p L)
    omega
  rw [hd]
  exact hle

theorem exists_T_Cx (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    (hcentral : ∀ T : Subgroup G, T ≤ GLAPPrimeCoreOf p (cx x) → IsPGroup 2 T →
      B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = ⊥) :
    ∃ T : Subgroup G, T ≤ cx x ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) = T ∧ T ≠ ⊥ ∧ ¬ T ≤ GLAPPrimeCoreOf p (cx x) := by
  classical
  have hp := hc.ctx.prime
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian p B := hS.1.1
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hBel
  obtain ⟨hxB, -, T₀, hT₀C, hT₀2, hT₀B, hT₀ne, -⟩ := hS.2.1
  have hBC : B ≤ cx x := isElemAbelian_le_centralizer hBel hxB
  have hT₀sub : (⁅T₀, B⁆ : Subgroup G) ≤ T₀ := by
    refine Subgroup.commutator_le.2 fun t ht g hg => ?_
    have h1 : g * t⁻¹ * g⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp (hT₀B hg) t⁻¹).1 (T₀.inv_mem ht)
    have h2 : ⁅t, g⁆ = t * (g * t⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact T₀.mul_mem ht h1
  have hTC : (⁅T₀, B⁆ : Subgroup G) ≤ cx x := by
    refine Subgroup.commutator_le.2 fun t ht g hg => ?_
    rw [commutatorElement_def]
    exact (cx x).mul_mem ((cx x).mul_mem ((cx x).mul_mem (hT₀C ht) (hBC hg))
      ((cx x).inv_mem (hT₀C ht))) ((cx x).inv_mem (hBC hg))
  have hTp2 : IsPGroup 2 (⁅T₀, B⁆ : Subgroup G) := IsPGroup.to_le hT₀2 hT₀sub
  have hTN : B ≤ Subgroup.normalizer ((⁅T₀, B⁆ : Subgroup G) : Set G) :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.tools_le_normalizer fun g hg y hy =>
      CFSG.HardMathSupport.Solomon.Coordinator.Generation228.tools_conj_comm_mem
        (fun t ht => (Subgroup.mem_normalizer_iff.mp (hT₀B hg) t).1 ht)
        (fun d hd => B.mul_mem (B.mul_mem hg hd) (B.inv_mem hg)) y hy
  have hT₀card : ¬ p ∣ Nat.card T₀ := by
    obtain ⟨k, hk⟩ := hT₀2.exists_card_eq
    rw [hk]
    intro hd
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hd
    exact hc.ctx.odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hTT : (⁅(⁅T₀, B⁆ : Subgroup G), B⁆ : Subgroup G) = ⁅T₀, B⁆ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq hp hBp hT₀B hT₀card
  refine ⟨⁅T₀, B⁆, hTC, hTp2, hTN, hTT, hT₀ne, fun hle => ?_⟩
  have h0 := hcentral _ hle hTp2 hTN
  rw [hTT] at h0
  exact hT₀ne h0

private theorem lemma103_bender {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hO : GLAPPrimeCore p H = ⊥) (hE : CFSG.ComponentClassification.Layer.subgroup H = ⊥)
    (r : H) (hr : ∀ s ∈ CFSG.pCore p H, r * s = s * r) : r ∈ CFSG.pCore p H := by
  have hF : CFSG.ComponentClassification.Fitting.subgroup H = CFSG.pCore p H := by
    unfold CFSG.ComponentClassification.Fitting.subgroup
    exact CFSG.Fitting_eq_pcore H p hO
  have hsub : CFSG.ComponentClassification.GeneralizedFitting.subgroup H = CFSG.pCore p H := by
    rw [CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup, hE, sup_bot_eq, hF]
  have h1 := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting H
  have hr' : r ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.GeneralizedFitting.subgroup H : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [hsub] at hs
    exact (hr s hs).symm
  have h2 := h1 hr'
  rw [hF] at h2
  exact h2

private theorem lemma103_top_core_eq_bot {p : ℕ} {Z : Type} [Group Z] [Finite Z]
    (hZ : GLAPPrimeCore p Z = ⊥) : GLAPPrimeCoreOf p (⊤ : Subgroup Z) = ⊥ := by
  unfold GLAPPrimeCore at hZ
  have h1 := CFSG.pPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup Z) ≃* Z)
  rw [hZ] at h1
  have h2 : CFSG.pPrimeCore p ↥(⊤ : Subgroup Z) = ⊥ := by
    apply Subgroup.map_injective (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup Z) ≃* Z).toMonoidHom)
      (Subgroup.topEquiv : ↥(⊤ : Subgroup Z) ≃* Z).injective
    rw [h1, Subgroup.map_bot]
  unfold GLAPPrimeCoreOf GLAPPrimeCore
  rw [h2, Subgroup.map_bot]

private theorem lemma103_normal_core_eq_bot {p : ℕ} (hp : p.Prime) {Z : Type} [Group Z] [Finite Z]
    (hZ : GLAPPrimeCore p Z = ⊥) (N : Subgroup Z) [N.Normal] : GLAPPrimeCore p ↥N = ⊥ := by
  have h1 : GLAPPrimeCoreOf p N ≤ GLAPPrimeCoreOf p (⊤ : Subgroup Z) :=
    glaPPrimeCoreOf_le_of_normal hp le_top inferInstance
  rw [lemma103_top_core_eq_bot hZ, le_bot_iff] at h1
  have h2 : (GLAPPrimeCore p ↥N).map N.subtype = ⊥ := by
    unfold GLAPPrimeCoreOf at h1
    exact h1
  rw [← Subgroup.map_bot N.subtype] at h2
  exact (Subgroup.map_injective N.subtype_injective) h2

private theorem lemma103_mk_comm_of_commutator_mem {X : Subgroup G} {w w' : ↥X}
    (h : ⁅(w : G), (w' : G)⁆ ∈ GLAPPrimeCoreOf p X) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) w * QuotientGroup.mk' (GLAPPrimeCore p ↥X) w' =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) w' * QuotientGroup.mk' (GLAPPrimeCore p ↥X) w := by
  obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 h
  have hcw : c = ⁅w, w'⁆ := Subtype.ext (by simpa [commutatorElement_def] using hce)
  have hc1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) c = 1 := (QuotientGroup.eq_one_iff c).2 hc
  rw [hcw, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at hc1
  calc _ = (QuotientGroup.mk' (GLAPPrimeCore p ↥X) w * QuotientGroup.mk' (GLAPPrimeCore p ↥X) w' *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥X) w)⁻¹ * (QuotientGroup.mk' (GLAPPrimeCore p ↥X) w')⁻¹) *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥X) w' * QuotientGroup.mk' (GLAPPrimeCore p ↥X) w) := by
        group
    _ = _ := by rw [hc1, one_mul]

private theorem lemma103_barX_layer_eq_bot {p : ℕ} (hp : p.Prime) {X L Yc : Subgroup G}
    (hL : GLAPComponent p X L) (hLX : GLAPLayer p X = L) (hYcX : Yc ≤ X)
    (hYcN : X ≤ Subgroup.normalizer (Yc : Set G))
    (hcen : ∀ y ∈ Yc, ∀ l ∈ L, ⁅l, y⁆ ∈ GLAPPrimeCoreOf p X) :
    CFSG.ComponentClassification.Layer.subgroup ↥(barX p X Yc) = ⊥ := by
  classical
  set Hb := barX p X Yc with hHb
  have hYcn : (Yc.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYcX).2 hYcN
  haveI hHbn : (barX p X Yc).Normal :=
    Subgroup.Normal.map hYcn _ (QuotientGroup.mk'_surjective _)
  rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
  refine le_antisymm (sSup_le ?_) bot_le
  intro Kc hKc
  have hKsn : CFSG.Open.IsSubnormal Kc ⊤ := hKc.2.1
  have hKq : CFSG.Open.IsQuasisimple ↥Kc := hKc.2.2
  have hKb_q : CFSG.Open.IsQuasisimple ↥(Kc.map Hb.subtype) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective Kc Hb.subtype Hb.subtype_injective) hKq
  have hKb_sn : CFSG.Open.IsSubnormal (Kc.map Hb.subtype) Hb := by
    have h1 := CFSG.Open.IsSubnormal.map Hb.subtype hKsn
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1
  have hHb_sn : CFSG.Open.IsSubnormal Hb ⊤ :=
    CFSG.Open.IsSubnormal.step le_top
      (by unfold Hb; exact Subgroup.Normal.subgroupOf inferInstance _)
      (CFSG.Open.IsSubnormal.refl _)
  have hKb_top : CFSG.Open.IsComponentOf (Kc.map Hb.subtype) ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.trans hKb_sn hHb_sn, hKb_q⟩
  obtain ⟨Lk, hLk, hLkb⟩ := exists_glaPComponent_barX_eq X hKb_top
  have hLkL : Lk ≤ L := by
    have h1 : Lk ≤ GLAPLayer p X := le_sSup hLk
    rwa [hLX] at h1
  have hKbL : Kc.map Hb.subtype ≤ barX p X L := by
    rw [← hLkb]
    exact barX_mono p hLkL
  have hcomm : ∀ a ∈ Kc.map Hb.subtype, ∀ b ∈ Kc.map Hb.subtype, a * b = b * a := by
    intro a ha b hb
    obtain ⟨w, hw, hwa⟩ := Subgroup.mem_map.1 (hKbL ha)
    have hb' : b ∈ barX p X Yc := (Subgroup.map_subtype_le Kc) hb
    obtain ⟨w', hw', hwb⟩ := Subgroup.mem_map.1 hb'
    rw [← hwa, ← hwb]
    exact lemma103_mk_comm_of_commutator_mem
      (hcen (w' : G) (Subgroup.mem_subgroupOf.1 hw') (w : G) (Subgroup.mem_subgroupOf.1 hw))
  have hbot : ⁅(⊤ : Subgroup ↥(Kc.map Hb.subtype)), (⊤ : Subgroup ↥(Kc.map Hb.subtype))⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro k _
    rw [Subgroup.mem_centralizer_iff]
    intro k' _
    exact Subtype.ext (hcomm _ k'.2 _ k.2)
  have hsub : Subsingleton ↥(Kc.map Hb.subtype) := by
    have h1 : (⊤ : Subgroup ↥(Kc.map Hb.subtype)) = ⊥ := by
      have h2 := hKb_q.1
      rw [commutator_def, hbot] at h2
      exact h2.symm
    constructor
    intro a b
    have ha : a ∈ (⊥ : Subgroup ↥(Kc.map Hb.subtype)) := h1 ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup ↥(Kc.map Hb.subtype)) := h1 ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  intro k hk
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Subgroup.coe_one]
  have hkb : Hb.subtype k ∈ Kc.map Hb.subtype := Subgroup.mem_map_of_mem _ hk
  exact congrArg Subtype.val (Subsingleton.elim (⟨Hb.subtype k, hkb⟩ : ↥(Kc.map Hb.subtype)) 1)

private theorem lemma103_core_le_centMod {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) (hN : X ≤ Subgroup.normalizer (L : Set G)) :
    GLAPPrimeCoreOf p X ≤ centModSubgroup p L := by
  intro o ho
  have hoX : o ∈ X := Subgroup.map_subtype_le _ ho
  refine ⟨hN hoX, fun l hl => ?_⟩
  have hlX : l ∈ X := hL.1 hl
  have h1 : ⁅l, o⁆ ∈ L := by
    have h2 : o * l⁻¹ * o⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hN hoX) l⁻¹).1 (L.inv_mem hl)
    have e : ⁅l, o⁆ = l * (o * l⁻¹ * o⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact L.mul_mem hl h2
  have h3 : ⁅l, o⁆ ∈ GLAPPrimeCoreOf p X := by
    have h4 : l * o * l⁻¹ ∈ GLAPPrimeCoreOf p X :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p X hlX) o).1 ho
    have e : ⁅l, o⁆ = (l * o * l⁻¹) * o⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact (GLAPPrimeCoreOf p X).mul_mem h4 ((GLAPPrimeCoreOf p X).inv_mem ho)
  have h5 := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1
  rw [← h5]
  exact ⟨h1, h3⟩

private theorem lemma103_isCyclic_of_isPGroup {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) (hN : X ≤ Subgroup.normalizer (L : Set G)) (hC : CycModSylow p L)
    (Q : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) (hQ : IsPGroup p Q)
    (hQY : Q ≤ barX p X (X ⊓ centModSubgroup p L)) : IsCyclic ↥Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set π : ↥X →* (↥X ⧸ GLAPPrimeCore p ↥X) := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set M : Subgroup ↥X := Q.comap π with hM
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥X)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥X
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hQ
  have hWcard : Nat.card M = Nat.card Q * Nat.card (GLAPPrimeCore p ↥X) := by
    have hidx : M.index = Q.index := Subgroup.index_comap_of_surjective Q hπsurj
    have h1 := Subgroup.card_mul_index M
    have h2 := Subgroup.card_mul_index Q
    have h3 := Subgroup.card_mul_index (GLAPPrimeCore p ↥X)
    have hi : Q.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hO : (GLAPPrimeCore p ↥X).index = Nat.card (↥X ⧸ GLAPPrimeCore p ↥X) := rfl
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
    calc Nat.card M * Q.index = Nat.card M * M.index := by rw [hidx]
      _ = Nat.card ↥X := h1
      _ = Nat.card (GLAPPrimeCore p ↥X) * (GLAPPrimeCore p ↥X).index := h3.symm
      _ = Nat.card (GLAPPrimeCore p ↥X) * (Nat.card Q * Q.index) := by rw [hO, ← h2]
      _ = Nat.card Q * Nat.card (GLAPPrimeCore p ↥X) * Q.index := by ring
  have hdvd : p ^ a ∣ Nat.card M := ⟨Nat.card (GLAPPrimeCore p ↥X), by rw [hWcard, ha]⟩
  obtain ⟨S₀, hS₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥M) p hdvd
  set ψ : ↥S₀ →* ↥X := M.subtype.comp S₀.subtype with hψ
  have hψinj : Function.Injective ψ := M.subtype_injective.comp S₀.subtype_injective
  set f : ↥S₀ →* (↥X ⧸ GLAPPrimeCore p ↥X) := π.comp ψ with hf
  have hfQ : ∀ w : ↥S₀, f w ∈ Q := fun w => (w : ↥M).2
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hwO : ψ w ∈ GLAPPrimeCore p ↥X := (QuotientGroup.eq_one_iff _).1 hw
    have hord1 : orderOf w ∣ p ^ a := by
      have := orderOf_dvd_natCard w
      rwa [hS₀] at this
    have hord2 : orderOf w ∣ Nat.card (GLAPPrimeCore p ↥X) :=
      calc orderOf w = orderOf (ψ w) := (orderOf_injective ψ hψinj w).symm
        _ = orderOf (⟨ψ w, hwO⟩ : ↥(GLAPPrimeCore p ↥X)) := by
          rw [← Subgroup.orderOf_coe (⟨ψ w, hwO⟩ : ↥(GLAPPrimeCore p ↥X))]
        _ ∣ Nat.card (GLAPPrimeCore p ↥X) := orderOf_dvd_natCard _
    have hcop2 : Nat.Coprime (orderOf w) (p ^ a) :=
      Nat.Coprime.pow_right a (Nat.Coprime.coprime_dvd_left hord2 hcop.symm)
    have h1 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd hcop2 hord1
    exact orderOf_eq_one_iff.1 h1
  have hmap_top : (⊤ : Subgroup ↥S₀).map f = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨w, -, rfl⟩
      exact hfQ w
    · rw [Subgroup.card_map_of_injective hfinj, Subgroup.card_top, hS₀, ha]
  set φ : ↥M →* G := X.subtype.comp M.subtype with hφ
  have hφinj : Function.Injective φ := X.subtype_injective.comp M.subtype_injective
  set S' : Subgroup G := S₀.map φ with hS'
  have hS'card : Nat.card S' = p ^ a := by
    rw [hS', Subgroup.card_map_of_injective hφinj, hS₀]
  have hS'cent : ∀ g ∈ S', CentMod p L g := by
    intro g hg
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.1 hg
    have hu : π ((w : ↥M) : ↥X) ∈ barX p X (X ⊓ centModSubgroup p L) := hQY w.2
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 hu
    have hyY : (y : G) ∈ X ⊓ centModSubgroup p L := Subgroup.mem_subgroupOf.1 hy
    have hkO : (y : G)⁻¹ * ((w : ↥M) : G) ∈ GLAPPrimeCoreOf p X := by
      have h5 : (y⁻¹ * ((w : ↥M) : ↥X)) ∈ GLAPPrimeCore p ↥X := (QuotientGroup.eq).1 hyu
      exact Subgroup.mem_map.2 ⟨_, h5, by simp⟩
    have hkc : CentMod p L ((y : G)⁻¹ * ((w : ↥M) : G)) :=
      centMod_iff.2 (lemma103_core_le_centMod hp hL hN hkO)
    have hyc : CentMod p L (y : G) := centMod_iff.2 hyY.2
    have := centMod_mul hyc hkc
    simpa [hφ] using this
  have hS'p : IsPGroup p S' := (IsPGroup.iff_card).2 ⟨a, hS'card⟩
  have hcycS' : IsCyclic ↥S' := hC S' hS'cent hS'p
  have hcycS₀ : IsCyclic ↥S₀ := by
    let e : ↥S₀ ≃* ↥S' := Subgroup.equivMapOfInjective S₀ φ hφinj
    exact isCyclic_of_surjective (e.symm : ↥S' →* ↥S₀) e.symm.surjective
  have hsurj : Function.Surjective (f.codRestrict Q hfQ) := by
    intro q
    have hq : (q : ↥X ⧸ GLAPPrimeCore p ↥X) ∈ (⊤ : Subgroup ↥S₀).map f := by
      rw [hmap_top]
      exact q.2
    obtain ⟨w, -, hw⟩ := Subgroup.mem_map.1 hq
    exact ⟨w, Subtype.ext hw⟩
  exact isCyclic_of_surjective _ hsurj

private theorem lemma103_eq_one_of_pow_coprime {M : Type*} [Monoid M] {U : M} {m N : ℕ}
    (hm : U ^ m = 1) (hN : U ^ N = 1) (hcop : Nat.Coprime m N) : U = 1 := by
  have h := pow_gcd_eq_one.2 ⟨hm, hN⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

private theorem lemma103_centralizes_of_cyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [Group H] [Finite H] {P : Subgroup H} [P.Normal] (hP : IsPGroup p P)
    [IsCyclic P] {z h : H} (hz : z ∈ P) (hzo : orderOf z = p) (hzh : h * z * h⁻¹ = z)
    (hh : Nat.Coprime (orderOf h) p) : ∀ g ∈ P, h * g * h⁻¹ = g := by
  classical
  have _hp2 := hp2
  obtain ⟨g₀', hg₀'⟩ := (IsCyclic.exists_generator : ∃ g : P, ∀ x, x ∈ Subgroup.zpowers g)
  set g₀ : H := (g₀' : H) with hg₀
  have hgen : ∀ x ∈ P, ∃ s : ℤ, g₀ ^ s = x := by
    intro x hx
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.1 (hg₀' ⟨x, hx⟩)
    refine ⟨s, ?_⟩
    rw [hg₀, ← Subgroup.coe_zpow, hs]
  have hordg : orderOf g₀ = Nat.card P := by
    rw [hg₀, Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg₀'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK⟩ := (IsPGroup.iff_card).1 hP
  have hzP : orderOf z ∣ Nat.card P := by
    have h' := orderOf_dvd_natCard (⟨z, hz⟩ : P)
    rw [← Subgroup.orderOf_coe] at h'
    exact h'
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hK
      rw [hK, hzo] at hzP
      exact hp.one_lt.ne' (Nat.dvd_one.1 hzP)
    · exact h0
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hNZ : ((Nat.card P : ℕ) : ℤ) = (p : ℤ) ^ (K' + 1) := by
    rw [hK]; push_cast; ring
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨u, hu⟩ : ∃ u : ℤ, h * g₀ * h⁻¹ = g₀ ^ u := by
    have hmem : h * g₀ * h⁻¹ ∈ P := (inferInstance : P.Normal).conj_mem g₀ g₀'.2 h
    obtain ⟨u, hu⟩ := hgen _ hmem
    exact ⟨u, hu.symm⟩
  have hconj : ∀ e : ℤ, h * g₀ ^ e * h⁻¹ = g₀ ^ (u * e) := by
    intro e
    rw [← conj_zpow, hu, ← zpow_mul]
  have hpow : ∀ j : ℕ, h ^ j * g₀ * (h ^ j)⁻¹ = g₀ ^ (u ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : h ^ (j + 1) * g₀ * (h ^ (j + 1))⁻¹ = h * (h ^ j * g₀ * (h ^ j)⁻¹) * h⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [e, ih, hconj (u ^ j), ← pow_succ']
  set m := orderOf h with hm
  have hhm : h ^ m = 1 := pow_orderOf_eq_one h
  have hgm : g₀ ^ (u ^ m) = g₀ := by
    have := hpow m
    rw [hhm, inv_one, mul_one, one_mul] at this
    exact this.symm
  have h1 : ((p : ℤ) ^ (K' + 1)) ∣ u ^ m - 1 := by
    rw [← hNZ, ← hordg]
    refine orderOf_dvd_iff_zpow_eq_one.2 ?_
    rw [zpow_sub, zpow_one, hgm, mul_inv_cancel]
  obtain ⟨s, hs⟩ := hgen z hz
  have h2 : ((p : ℤ) ^ (K' + 1)) ∣ u * s - s := by
    rw [← hNZ, ← hordg]
    refine orderOf_dvd_iff_zpow_eq_one.2 ?_
    have hzs : g₀ ^ (u * s) = g₀ ^ s := by
      rw [← hconj s, hs, hzh]
    rw [zpow_sub, hzs, mul_inv_cancel]
  have hz1 : z ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hzo
    exact hp.one_lt.ne' hzo.symm
  have hzp : z ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzo] at this
  have h3 : ((p : ℤ) ^ (K' + 1)) ∣ s * p := by
    rw [← hNZ, ← hordg]
    refine orderOf_dvd_iff_zpow_eq_one.2 ?_
    rw [zpow_mul, hs, zpow_natCast, hzp]
  have hns : ¬ ((p : ℤ) ^ (K' + 1)) ∣ s := by
    intro hd
    apply hz1
    rw [← hs]
    refine orderOf_dvd_iff_zpow_eq_one.1 ?_
    rw [hordg, hNZ]
    exact hd
  obtain ⟨c, hc⟩ := h3
  have hsc : s = (p : ℤ) ^ K' * c := by
    apply mul_right_cancel₀ hp0
    rw [pow_succ] at hc
    rw [hc]
    ring
  have hpc : ¬ (p : ℤ) ∣ c := by
    rintro ⟨d, hd⟩
    apply hns
    refine ⟨d, ?_⟩
    rw [hsc, hd]
    ring
  have hdu : (p : ℤ) ∣ u - 1 := by
    have h4 := h2
    have e : u * s - s = (p : ℤ) ^ K' * ((u - 1) * c) := by
      rw [hsc]; ring
    rw [e, pow_succ', mul_comm ((p : ℤ) ^ K')] at h4
    have h6 : (p : ℤ) ∣ (u - 1) * c :=
      (mul_dvd_mul_iff_right (pow_ne_zero K' hp0)).1 h4
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact (hpr.dvd_or_dvd h6).resolve_right hpc
  have hdu5 : ((p : ℤ) ^ (K' + 1)) ∣ u ^ (p ^ K') - 1 := by
    have := dvd_sub_pow_of_dvd_sub hdu K'
    simpa using this
  have hNcast : ((p ^ (K' + 1) : ℕ) : ℤ) = (p : ℤ) ^ (K' + 1) := by push_cast; ring
  have hU1 : ((u : ZMod (p ^ (K' + 1))) ^ m) = 1 := by
    have h7 : ((u ^ m - 1 : ℤ) : ZMod (p ^ (K' + 1))) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hNcast]
      exact h1
    push_cast at h7
    exact sub_eq_zero.1 h7
  have hU2 : ((u : ZMod (p ^ (K' + 1))) ^ (p ^ K')) = 1 := by
    have h7 : ((u ^ (p ^ K') - 1 : ℤ) : ZMod (p ^ (K' + 1))) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hNcast]
      exact hdu5
    push_cast at h7
    exact sub_eq_zero.1 h7
  have hcop : Nat.Coprime m (p ^ K') := Nat.Coprime.pow_right K' hh
  have hUone : (u : ZMod (p ^ (K' + 1))) = 1 := lemma103_eq_one_of_pow_coprime hU1 hU2 hcop
  have hdu1 : ((p : ℤ) ^ (K' + 1)) ∣ u - 1 := by
    have h8 : ((u - 1 : ℤ) : ZMod (p ^ (K' + 1))) = 0 := by
      push_cast
      rw [hUone, sub_self]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h8
    rwa [hNcast] at this
  have hgu : g₀ ^ u = g₀ := by
    have h9 : (orderOf g₀ : ℤ) ∣ u - 1 := by
      rw [hordg, hNZ]
      exact hdu1
    have h8 : g₀ ^ (u - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 h9
    rw [zpow_sub, zpow_one] at h8
    exact mul_inv_eq_one.1 h8
  intro g hg
  obtain ⟨t, ht⟩ := hgen g hg
  rw [← ht, hconj t, zpow_mul, hgu]

theorem lemma103_pow_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X L : Subgroup G} {x : G}
    (hL : GLAPComponent p X L) (hLX : GLAPLayer p X = L) (hN : X ≤ Subgroup.normalizer (L : Set G))
    (hC : CycModSylow p L) (hxX : x ∈ X) (hxo : orderOf x = p) (hxc : ∀ g ∈ X, g * x = x * g) :
    ∀ y ∈ X ⊓ centModSubgroup p L, ∃ n : ℕ, y ^ (p ^ n) ∈ GLAPPrimeCoreOf p X := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Y : Subgroup G := X ⊓ centModSubgroup p L with hY
  have hYX : Y ≤ X := inf_le_left
  have hYN : X ≤ Subgroup.normalizer (Y : Set G) := by
    intro g hg
    have hgc : g ∈ Subgroup.normalizer (centModSubgroup p L : Set G) :=
      normalizer_le_normalizer_centModSubgroup p L (hN hg)
    rw [Subgroup.mem_normalizer_iff] at hgc ⊢
    intro h
    rw [hY, Subgroup.mem_inf, Subgroup.mem_inf, ← hgc h]
    constructor
    · rintro ⟨hhX, hhc⟩
      exact ⟨X.mul_mem (X.mul_mem hg hhX) (X.inv_mem hg), hhc⟩
    · rintro ⟨hhX, hhc⟩
      refine ⟨?_, hhc⟩
      have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
      have := X.mul_mem (X.mul_mem (X.inv_mem hg) hhX) hg
      rwa [e] at this
  have hYn : (Y.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hYN
  haveI hHbn : (barX p X Y).Normal := Subgroup.Normal.map hYn _ (QuotientGroup.mk'_surjective _)
  have hcen : ∀ y ∈ Y, ∀ l ∈ L, ⁅l, y⁆ ∈ GLAPPrimeCoreOf p X := fun y hy l hl =>
    (glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1) ((mem_centModSubgroup.1 hy.2).2 l hl)
  have hZ : GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hHcore : GLAPPrimeCore p ↥(barX p X Y) = ⊥ :=
    lemma103_normal_core_eq_bot hp hZ (barX p X Y)
  have hHlayer : CFSG.ComponentClassification.Layer.subgroup ↥(barX p X Y) = ⊥ :=
    lemma103_barX_layer_eq_bot hp hL hLX hYX hYN hcen
  have hxY : x ∈ Y := by
    refine ⟨hxX, mem_centModSubgroup.2 ⟨hN hxX, fun l hl => ?_⟩⟩
    have h1 : ⁅l, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hxc l (hL.1 hl))
    rw [h1]
    exact (GLAPPrimeCoreOf p L).one_mem
  set z : ↥(barX p X Y) :=
    ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hxX⟩,
      Subgroup.mem_map.2 ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.2 hxY, rfl⟩⟩ with hzdef
  have hzcen : ∀ h : ↥(barX p X Y), h * z = z * h := by
    intro h
    obtain ⟨w, hw, hwh⟩ := Subgroup.mem_map.1 h.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hzdef]
    rw [← hwh, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hxc _ w.2)
  have hzpow : z ^ p = 1 := by
    have hx1 : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
    apply Subtype.ext
    simp only [hzdef, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow]
    have : (⟨x, hxX⟩ : ↥X) ^ p = 1 := Subtype.ext (by simpa using hx1)
    rw [this, map_one]
  have hzne : z ≠ 1 := by
    intro h1
    have hw : (⟨x, hxX⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := by
      have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨x, hxX⟩ : ↥X) = 1 :=
        congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).1 h2
    have hcop := CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥X
    have hord : orderOf (⟨x, hxX⟩ : ↥X) ∣ Nat.card (GLAPPrimeCore p ↥X) := by
      have h4 := orderOf_dvd_natCard (⟨⟨x, hxX⟩, hw⟩ : ↥(GLAPPrimeCore p ↥X))
      rw [← Subgroup.orderOf_coe] at h4
      exact h4
    have hxo' : orderOf (⟨x, hxX⟩ : ↥X) = p := by
      rw [← hxo]
      exact (orderOf_injective X.subtype X.subtype_injective _).symm
    have h5 := Nat.Coprime.coprime_dvd_left hord hcop.symm
    rw [hxo'] at h5
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h5.symm dvd_rfl)
  have hzo : orderOf z = p := orderOf_eq_prime hzpow hzne
  have hzN : (Subgroup.zpowers z).Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g z := hzcen g
    rw [show g * z ^ k * g⁻¹ = z ^ k by rw [(hc.zpow_right k).eq]; group]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  have hzpg : IsPGroup p (Subgroup.zpowers z) :=
    (IsPGroup.iff_card).2 ⟨1, by rw [Nat.card_zpowers, hzo, pow_one]⟩
  have hzP0 : Subgroup.zpowers z ≤ CFSG.pCore p ↥(barX p X Y) := le_sSup ⟨hzN, hzpg⟩
  set P : Subgroup ↥(barX p X Y) := CFSG.pCore p ↥(barX p X Y) with hP
  have hzP : z ∈ P := hzP0 (Subgroup.mem_zpowers z)
  have hPp : IsPGroup p P := CFSG.pCore_isPGroup
  have hPn : P.Normal := CFSG.pCore_normal
  have hPcyc : IsCyclic ↥P := by
    set Q : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := P.map (barX p X Y).subtype with hQ
    have hQp : IsPGroup p Q := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hPp
      exact (IsPGroup.iff_card).2 ⟨k, by rw [hQ, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hk]⟩
    have hQY : Q ≤ barX p X (X ⊓ centModSubgroup p L) := by
      rintro _ ⟨h, -, rfl⟩
      exact h.2
    have hcycQ : IsCyclic ↥Q := lemma103_isCyclic_of_isPGroup hp hL hN hC Q hQp hQY
    let e : ↥P ≃* ↥Q := Subgroup.equivMapOfInjective P (barX p X Y).subtype (Subgroup.subtype_injective _)
    exact isCyclic_of_surjective (e.symm : ↥Q →* ↥P) e.symm.surjective
  have hpprime : ∀ g : ↥(barX p X Y), Nat.Coprime (orderOf g) p → g = 1 := by
    intro g hg
    have hgz : g * z * g⁻¹ = z := by rw [hzcen g]; group
    have hcent := lemma103_centralizes_of_cyclic hp hp2 hPp hzP hzo hgz hg
    have hgP : g ∈ P := lemma103_bender hHcore hHlayer g (fun s hs => by
      have hs' := hcent s hs
      calc g * s = g * s * g⁻¹ * g := by group
        _ = s * g := by rw [hs'])
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hPp
    have hdvd : orderOf g ∣ p ^ k := by
      have h6 := orderOf_dvd_natCard (⟨g, hgP⟩ : ↥P)
      rw [← Subgroup.orderOf_coe, hk] at h6
      exact h6
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hg) hdvd)
  have hG : ∀ h : ↥(barX p X Y), ∃ e : ℕ, h ^ (p ^ e) = 1 := by
    intro h
    obtain ⟨e, n, hn, hon⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos h).ne' p hp.one_lt.ne'
    refine ⟨e, ?_⟩
    apply hpprime
    have hdvd : orderOf (h ^ (p ^ e)) ∣ n := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, ← hon, pow_orderOf_eq_one]
    exact Nat.Coprime.coprime_dvd_left hdvd ((Nat.Prime.coprime_iff_not_dvd hp).2 hn).symm
  intro y hy
  have hyX : y ∈ X := hy.1
  obtain ⟨e, he⟩ := hG ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩,
    Subgroup.mem_map.2 ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩⟩
  refine ⟨e, ?_⟩
  have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ ^ (p ^ e) = 1 := by
    have h4 := congrArg Subtype.val he
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h4
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨y, hyX⟩ ^ (p ^ e)) = 1 := by
    rw [map_pow]
    exact h2
  have h3 : (⟨y, hyX⟩ : ↥X) ^ (p ^ e) ∈ GLAPPrimeCore p ↥X := (QuotientGroup.eq_one_iff _).1 h1
  exact Subgroup.mem_map.2 ⟨_, h3, by simp⟩

private theorem lemma103_mem_sup_of_le_normalizer {W N : Subgroup G}
    (hWN : W ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ W ⊔ N) :
    ∃ w ∈ W, ∃ n ∈ N, w * n = x := by
  let P : Subgroup G :=
    { carrier := {x | ∃ w ∈ W, ∃ n ∈ N, w * n = x}
      mul_mem' := by
        rintro _ _ ⟨w1, hw1, n1, hn1, rfl⟩ ⟨w2, hw2, n2, hn2, rfl⟩
        have h1 : w2⁻¹ * n1 * w2 ∈ N := by
          have h := (Subgroup.mem_normalizer_iff.1 (hWN (W.inv_mem hw2)) n1).1 hn1
          simpa using h
        exact ⟨w1 * w2, W.mul_mem hw1 hw2, w2⁻¹ * n1 * w2 * n2, N.mul_mem h1 hn2, by group⟩
      one_mem' := ⟨1, W.one_mem, 1, N.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨w, hw, n, hn, rfl⟩
        have h1 : w * n⁻¹ * w⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.1 (hWN hw) n⁻¹).1 (N.inv_mem hn)
        exact ⟨w⁻¹, W.inv_mem hw, w * n⁻¹ * w⁻¹, h1, by group⟩ }
  have hle : W ⊔ N ≤ P := sup_le
    (fun w hw => ⟨w, hw, 1, N.one_mem, mul_one w⟩)
    (fun n hn => ⟨1, W.one_mem, n, hn, one_mul n⟩)
  obtain ⟨w, hw, n, hn, h⟩ := hle hx
  exact ⟨w, hw, n, hn, h⟩

private theorem lemma103_centMod_mul_of_inner {p : ℕ} {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) (h : InducesInnerMod p J g) :
    ∃ c ∈ centModSubgroup p J, ∃ l ∈ J, g = c * l := by
  obtain ⟨l, hl, hy⟩ := h
  refine ⟨g * l⁻¹, ⟨?_, fun x hx => ?_⟩, l, hl, by group⟩
  · exact Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (Subgroup.le_normalizer hl))
  · have h1 := hy x⁻¹ (J.inv_mem hx)
    have h2 : g * ((l⁻¹ * x⁻¹ * l)⁻¹ * (g⁻¹ * x⁻¹ * g)) * g⁻¹ ∈ GLAPPrimeCoreOf p J :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p J hg) _).1 h1
    have h3 : ⁅x, g * l⁻¹⁆ = (g * ((l⁻¹ * x⁻¹ * l)⁻¹ * (g⁻¹ * x⁻¹ * g)) * g⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h3]; exact Subgroup.inv_mem _ h2

theorem T_le_LO (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) {T : Subgroup G} (hTC : T ≤ cx x) (hT2 : IsPGroup 2 T)
    (hTB : B ≤ Subgroup.normalizer (T : Set G)) (hTT : (⁅T, B⁆ : Subgroup G) = T) :
    T ≤ L ⊔ GLAPPrimeCoreOf p (cx x) := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hS := sstar_triple h.star
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hL : GLAPComponent p (cx x) L := hS.2.2
  have hLX : GLAPLayer p (cx x) = L := sstar_layer hc h.star
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := sstar_norm h.star
  have hcyc : CycModSylow p L := sstar_cyc h.star
  have hchev : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc h.star
  have hN : cx x ≤ Subgroup.normalizer (L : Set G) := fun g hg => by
    rw [← hLX]
    exact mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := fun t ht => hN (hTC ht)
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxX : x ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxc : ∀ g ∈ cx x, g * x = x * g := fun g hg => Subgroup.mem_centralizer_singleton_iff.1 hg
  have hKgrp : CFSG.Open.IsKGroup ↥(cx x) :=
    isKGroup_of_isKProper hc.ctx.kProper (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1)
  have hcomm : ∀ a ∈ B, ∀ t ∈ T, ⁅a, t⁆ ∈ centModSubgroup p L ⊔ L := by
    intro a ha t ht
    have hI := hin.i712 hp hp2 (cx x) L B T hKgrp hL hchev (isPGroup_of_isElemAbelian hS.1.1) hT2
      hBN hTN hTB a ha t ht
    have hg : ⁅a, t⁆ ∈ Subgroup.normalizer (L : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hBN ha) (hTN ht))
        (Subgroup.inv_mem _ (hBN ha))) (Subgroup.inv_mem _ (hTN ht))
    obtain ⟨c, hc', l, hl, hcl⟩ := lemma103_centMod_mul_of_inner hg hI
    rw [hcl]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right hl)
  have hTle : T ≤ centModSubgroup p L ⊔ L := by
    have e : T = ⁅B, T⁆ := by rw [Subgroup.commutator_comm, hTT]
    rw [e]
    exact Subgroup.commutator_le.2 hcomm
  have hdec : ∀ t ∈ T, ∃ y ∈ cx x ⊓ centModSubgroup p L, ∃ l ∈ L, t = y * l := by
    intro t ht
    obtain ⟨w, hw, n, hn, hwn⟩ := lemma103_mem_sup_of_le_normalizer
      (fun g hg => (mem_centModSubgroup.1 hg).1) (hTle ht)
    have hwX : w ∈ cx x := by
      have e : w = t * n⁻¹ := by rw [← hwn]; group
      rw [e]
      exact (cx x).mul_mem (hTC ht) ((cx x).inv_mem (hL.1 hn))
    exact ⟨w, ⟨hwX, hw⟩, n, hn, hwn.symm⟩
  have hpow := lemma103_pow_core hp hp2 hL hLX hN hcyc hxX hxo hxc
  have hLn : (L.subgroupOf (cx x)).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1).2 hN
  have hOn : ((GLAPPrimeCoreOf p (cx x)).subgroupOf (cx x)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).2
      (le_normalizer_glaPPrimeCoreOf p (cx x))
  set Mq : Subgroup ↥(cx x) := L.subgroupOf (cx x) ⊔ (GLAPPrimeCoreOf p (cx x)).subgroupOf (cx x) with hMq
  have hMq_le : Mq ≤ (L ⊔ GLAPPrimeCoreOf p (cx x)).subgroupOf (cx x) :=
    sup_le (fun u hu => Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hu)))
      (fun u hu => Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hu)))
  intro t ht
  obtain ⟨y, hy, l, hl, hyl⟩ := hdec t ht
  obtain ⟨n, hn⟩ := hpow y hy
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  set u : ↥(cx x) := ⟨t, hTC ht⟩ with hu
  set v : ↥(cx x) := ⟨y, hy.1⟩ with hv
  have hl1 : QuotientGroup.mk' Mq (⟨l, hL.1 hl⟩ : ↥(cx x)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hl))
  have huv : QuotientGroup.mk' Mq u = QuotientGroup.mk' Mq v := by
    have e : u = v * ⟨l, hL.1 hl⟩ := Subtype.ext hyl
    rw [e, map_mul, hl1, mul_one]
  have hu_pow : (QuotientGroup.mk' Mq u) ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have e : u ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk')
    rw [e, map_one]
  have hv_pow : (QuotientGroup.mk' Mq u) ^ (p ^ n) = 1 := by
    rw [huv, ← map_pow]
    have hvn : v ^ (p ^ n) ∈ Mq := by
      refine Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 ?_)
      show ((v ^ (p ^ n) : ↥(cx x)) : G) ∈ GLAPPrimeCoreOf p (cx x)
      rw [Subgroup.coe_pow]
      exact hn
    exact (QuotientGroup.eq_one_iff _).2 hvn
  have hcop : Nat.Coprime (2 ^ k) (p ^ n) :=
    Nat.Coprime.pow k n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h1 : QuotientGroup.mk' Mq u = 1 := lemma103_eq_one_of_pow_coprime hu_pow hv_pow hcop
  exact Subgroup.mem_subgroupOf.1 (hMq_le ((QuotientGroup.eq_one_iff _).1 h1))

theorem exists_T1_of_le_LO (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) {T : Subgroup G} (hTC : T ≤ cx x) (hT2 : IsPGroup 2 T)
    (hTB : B ≤ Subgroup.normalizer (T : Set G)) (hTO : ¬ T ≤ GLAPPrimeCoreOf p (cx x))
    (hTLO : T ≤ L ⊔ GLAPPrimeCoreOf p (cx x)) : HasTL p B L := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian p B := hS.1.1
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hBel
  have hLC : L ≤ cx x := hS.2.2.1
  have hBC : B ≤ cx x := isElemAbelian_le_centralizer hBel hS.2.1.1
  have hON : cx x ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p (cx x) : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf p (cx x)
  set O : Subgroup G := GLAPPrimeCoreOf p (cx x) with hOdef
  have hTN : T ≤ Subgroup.normalizer (O : Set G) := hTC.trans hON
  have hLN : L ≤ Subgroup.normalizer (O : Set G) := hLC.trans hON
  have hopos : 0 < Nat.card O := Nat.card_pos
  have hcopO : Nat.Coprime p (Nat.card O) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp (cx x)
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hcopT : Nat.Coprime p (Nat.card T) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hprodOT : Nat.card (O ⊔ T : Subgroup G) * Nat.card (O ⊓ T : Subgroup G) =
      Nat.card O * Nat.card T :=
    card_sup_mul_card_inf_of_le_normalizer hTN
  have hcopOT : Nat.Coprime p (Nat.card (O ⊔ T : Subgroup G)) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro _ hprodOT) (Nat.Coprime.mul_right hcopO hcopT)
  set M : Subgroup G := (O ⊔ T) ⊓ L with hMdef
  have hBOT : B ≤ Subgroup.normalizer ((O ⊔ T : Subgroup G) : Set G) :=
    (le_inf (hBC.trans hON) hTB).trans (Subgroup.inf_normalizer_le_normalizer_sup O T)
  have hBM : B ≤ Subgroup.normalizer (M : Set G) :=
    (le_inf hBOT (sstar_norm h.star)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := O ⊔ T) (K := L))
  have hcopM : Nat.Coprime p (Nat.card M) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcopOT
  obtain ⟨R, hRM, hR2, hRidx, hBR⟩ := exists_invariant_sylow_two hp hp2 hBp hBM hcopM
  refine ⟨R, hRM.trans inf_le_right, hR2, hBR, fun hRN => ?_⟩
  have hsubL : IsSubnormal L (cx x) := hS.2.2.2.1
  have hNL : GLAPPrimeCoreOf p L = L ⊓ O :=
    (glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsubL).symm
  rw [hNL] at hRN
  have hMO : M ⊓ O = L ⊓ O := by
    apply le_antisymm (inf_le_inf_right O inf_le_right)
    exact le_inf (le_inf ((inf_le_right : L ⊓ O ≤ O).trans le_sup_left) inf_le_left) inf_le_right
  have hOM : O ⊔ M = O ⊔ T := by
    apply le_antisymm
    · exact sup_le le_sup_left inf_le_left
    · refine sup_le le_sup_left (fun t ht => ?_)
      obtain ⟨w, hw, n, hn, hwn⟩ := lemma103_mem_sup_of_le_normalizer hLN (hTLO ht)
      have htOT : t ∈ O ⊔ T := Subgroup.mem_sup_right ht
      have hwOT : w ∈ O ⊔ T := by
        have h1 : w = t * n⁻¹ := by rw [← hwn]; group
        rw [h1]
        exact (O ⊔ T).mul_mem htOT (Subgroup.mem_sup_left (O.inv_mem hn))
      have hwM : w ∈ M := ⟨hwOT, hw⟩
      rw [← hwn]
      exact (O ⊔ M).mul_mem (Subgroup.mem_sup_right hwM) (Subgroup.mem_sup_left hn)
  have hMN : M ≤ Subgroup.normalizer (O : Set G) := (inf_le_right.trans hLC).trans hON
  have hprodM : Nat.card (O ⊔ M : Subgroup G) * Nat.card (O ⊓ M : Subgroup G) =
      Nat.card O * Nat.card M :=
    card_sup_mul_card_inf_of_le_normalizer hMN
  rw [hOM, inf_comm O M, hMO] at hprodM
  have hAw : Nat.card M * Nat.card (O ⊓ T : Subgroup G) =
      Nat.card T * Nat.card (L ⊓ O : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_left hopos
    calc Nat.card O * (Nat.card M * Nat.card (O ⊓ T : Subgroup G))
        = (Nat.card O * Nat.card M) * Nat.card (O ⊓ T : Subgroup G) := by ring
      _ = (Nat.card (O ⊔ T : Subgroup G) * Nat.card (L ⊓ O : Subgroup G)) *
            Nat.card (O ⊓ T : Subgroup G) := by rw [hprodM]
      _ = (Nat.card (O ⊔ T : Subgroup G) * Nat.card (O ⊓ T : Subgroup G)) *
            Nat.card (L ⊓ O : Subgroup G) := by ring
      _ = (Nat.card O * Nat.card T) * Nat.card (L ⊓ O : Subgroup G) := by rw [hprodOT]
      _ = Nat.card O * (Nat.card T * Nat.card (L ⊓ O : Subgroup G)) := by ring
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le (inf_le_right : O ⊓ T ≤ T)
  have hc1 : c ≠ 1 := by
    intro hc1
    rw [hc1, mul_one] at hc
    apply hTO
    have heq : O ⊓ T = T := Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq hc)
    rw [← heq]
    exact inf_le_left
  have hcdvd : c ∣ 2 ^ k := Dvd.intro_left (Nat.card (O ⊓ T : Subgroup G)) (hc.symm.trans hk)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hcdvd
  have h2c : 2 ∣ c := by
    rw [hi]
    apply dvd_pow_self
    intro h0
    apply hc1
    rw [hi, h0, pow_zero]
  have hriM : R.relIndex M * Nat.card R = Nat.card M := by
    have := Subgroup.relIndex_mul_card (H := R) (K := M)
    rwa [inf_eq_left.2 hRM] at this
  have hriN : R.relIndex (L ⊓ O) * Nat.card R = Nat.card (L ⊓ O : Subgroup G) := by
    have := Subgroup.relIndex_mul_card (H := R) (K := L ⊓ O)
    rwa [inf_eq_left.2 hRN] at this
  have hr : 0 < Nat.card R := Nat.card_pos
  have hw : 0 < Nat.card (O ⊓ T : Subgroup G) := Nat.card_pos
  have key : R.relIndex M = c * R.relIndex (L ⊓ O) := by
    have h1 : Nat.card R * (R.relIndex M * Nat.card (O ⊓ T : Subgroup G)) =
        Nat.card R * (c * R.relIndex (L ⊓ O) * Nat.card (O ⊓ T : Subgroup G)) := by
      calc Nat.card R * (R.relIndex M * Nat.card (O ⊓ T : Subgroup G))
          = (R.relIndex M * Nat.card R) * Nat.card (O ⊓ T : Subgroup G) := by ring
        _ = Nat.card M * Nat.card (O ⊓ T : Subgroup G) := by rw [hriM]
        _ = Nat.card T * Nat.card (L ⊓ O : Subgroup G) := hAw
        _ = (Nat.card (O ⊓ T : Subgroup G) * c) * Nat.card (L ⊓ O : Subgroup G) := by rw [hc]
        _ = (Nat.card (O ⊓ T : Subgroup G) * c) *
              (R.relIndex (L ⊓ O) * Nat.card R) := by rw [hriN]
        _ = Nat.card R * (c * R.relIndex (L ⊓ O) * Nat.card (O ⊓ T : Subgroup G)) := by ring
    exact Nat.eq_of_mul_eq_mul_right hw (Nat.eq_of_mul_eq_mul_left hr h1)
  exact hRidx (by rw [key]; exact Dvd.dvd.mul_right h2c _)


theorem T_in_L (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) {T : Subgroup G} (hTC : T ≤ cx x) (hT2 : IsPGroup 2 T)
    (hTB : B ≤ Subgroup.normalizer (T : Set G)) (hTT : (⁅T, B⁆ : Subgroup G) = T) (hTne : T ≠ ⊥)
    (hTO : ¬ T ≤ GLAPPrimeCoreOf p (cx x)) : HasTL p B L :=
  exists_T1_of_le_LO hc h hTC hT2 hTB hTO (T_le_LO hc hin h hTC hT2 hTB hTT)

theorem exists_T_in_L (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    (hcentral : ∀ T : Subgroup G, T ≤ GLAPPrimeCoreOf p (cx x) → IsPGroup 2 T →
      B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = ⊥) : HasTL p B L := by
  obtain ⟨T, hTC, hT2, hTB, hTT, hTne, hTO⟩ := exists_T_Cx hc h hcentral
  exact T_in_L hc hin h hTC hT2 hTB hTT hTne hTO

theorem tD42_of_notG (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hnG : ¬ IsGStar p B L) (hT : HasTL p B L) :
    p = 3 ∧ IsTD4 3 L ∧ GLAMarking (PQuot 3 L) (fun lab _ _ _ _ _ => lab.n = 1) := by
  have hL : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  rcases hin.i263 B x L h.star (sstar_chev2 hc h.star) hT with hG | ⟨hp3, hM⟩
  · exact absurd hG hnG
  · subst hp3
    rcases h.prop with hf | ⟨-, htd, -⟩
    · exact absurd hM (hin.field_n Nat.prime_three (by norm_num) (cx x) L b hL hf).2.1
    · exact ⟨rfl, htd, hM⟩

theorem contra_tD42 (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hp3 : p = 3) (htd : IsTD4 3 L)
    (hmark : GLAMarking (PQuot 3 L) (fun lab _ _ _ _ _ => lab.n = 1)) (hT : HasTL p B L) : False := by
  subst hp3
  obtain ⟨T, hTL, hT2, hBT, hTO⟩ := hT
  have hS := sstar_triple h.star
  have h9 := hin.i131 (cx x) L B T hS.2.2 htd hmark (sstar_norm h.star) hS.1.1 hTL hT2 hBT hTO
  have h27 := p3_mul_cent_le hc h.star
  have hpos : 0 < Nat.card ↥(B ⊓ centModSubgroup 3 L) := Nat.card_pos
  omega

theorem contra_not_G (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hnG : ¬ IsGStar p B L) (hT : HasTL p B L) : False := by
  obtain ⟨hp3, htd, hmark⟩ := tD42_of_notG hc hin h hnG hT
  exact contra_tD42 hc hin h hp3 htd hmark hT

theorem d_eq_five (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) : dLevel G p = 5 := by
  classical
  by_contra hne
  have hlt : dLevel G p < 5 := lt_of_le_of_ne (dLevel_le_five G p) hne
  have hnG : ¬ IsGStar p B L := fun hG => hne (dLevel_eq_five_of_gstar (sstar_s0 h.star) hG)
  have hcentral : ∀ T : Subgroup G, T ≤ GLAPPrimeCoreOf p (cx x) → IsPGroup 2 T →
      B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = ⊥ := by
    intro T hTO hT2 hBT
    by_cases hev : Even (Nat.card (GLAPPrimeCoreOf p (cx x)))
    · have hd2 := dLevel_le_two_of_even hc hin h hnG hev
      have hS := sstar_triple h.star
      exact hc.stage4.2.2 hd2 B x T hS.1 hS.2.1.1 hS.2.1.2.1 hTO hT2 hBT
    · have hodd : Odd (Nat.card (GLAPPrimeCoreOf p (cx x))) := Nat.not_even_iff_odd.1 hev
      have hTcard : Nat.card T = 1 := by
        obtain ⟨k, hk⟩ := hT2.exists_card_eq
        have hdvd : Nat.card T ∣ Nat.card (GLAPPrimeCoreOf p (cx x)) := Subgroup.card_dvd_of_le hTO
        rw [hk] at hdvd ⊢
        have : ¬ 2 ∣ Nat.card (GLAPPrimeCoreOf p (cx x)) := by
          rw [← even_iff_two_dvd]
          exact Nat.not_even_iff_odd.2 hodd
        rcases k with _ | k
        · simp
        · exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) hdvd) this
      have hTbot : T = ⊥ := Subgroup.card_eq_one.1 hTcard
      rw [hTbot]
      simp
  exact contra_not_G hc hin h hnG (exists_T_in_L hc hin h hcentral)

structure UCore (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G)
    (b : G) : Prop where
  p3 : p = 3
  L_iso : catalogIs ↥L S9.isU4eight
  field : FieldOn p b L
  I_grp : catalogIs ↥(L ⊓ cx b) S9.isU4two
  I_eq : Ipart p L b = L ⊓ cx b
  I_comp : GLAPComponent p (L ⊓ cx b) (Ipart p L b)
  I_core : GLAPPrimeCoreOf p (Ipart p L b) = ⊥
  I_iso : catalogIs (PSimple p (Ipart p L b)) S9.isU4two
  cent : centCard2 p L b = 2 ^ 6

theorem layer_eq_of_isU4two {C : Subgroup G} (hC : catalogIs ↥C S9.isU4two) (hne : GLAPLayer 3 C ≠ ⊥) :
    GLAPLayer 3 C = C ∧ GLAPComponent 3 C C ∧ GLAPPrimeCoreOf 3 C = ⊥ ∧
      catalogIs (PSimple 3 C) S9.isU4two := by
  have hsimple : IsSimpleGroup ↥C := isSimple_of_isU4two hC
  obtain ⟨J, hJ, hJne⟩ : ∃ J : Subgroup G, GLAPComponent 3 C J ∧ J ≠ ⊥ := by
    by_contra hno
    push Not at hno
    apply hne
    unfold GLAPLayer
    exact sSup_eq_bot.2 fun J hJ => hno J hJ
  have hJC : J = C := by
    by_contra hJC
    obtain ⟨M, hJM, hMC, hMne, hMn, -⟩ := isSubnormal_exists_normal hJ.2.1 hJC
    haveI : (M.subgroupOf C).Normal := hMn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf C) with h1 | h1
    · apply hJne
      have hM : M = ⊥ := by
        rw [eq_bot_iff]
        intro m hm
        have h2 : (⟨m, hMC hm⟩ : ↥C) ∈ M.subgroupOf C := Subgroup.mem_subgroupOf.2 hm
        rw [h1, Subgroup.mem_bot] at h2
        exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
      exact le_bot_iff.1 (hJM.trans hM.le)
    · apply hMne
      refine le_antisymm hMC fun c hc => ?_
      have h2 : (⟨c, hc⟩ : ↥C) ∈ M.subgroupOf C := by
        rw [h1]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 h2
  rw [hJC] at hJ
  have hlayer : GLAPLayer 3 C = C := by
    unfold GLAPLayer
    exact le_antisymm (sSup_le fun K hK => hK.1) (le_sSup hJ)
  have hPQ : CFSG.Open.IsQuasisimple (PQuot 3 C) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hPS : IsSimpleGroup (PSimple 3 C) := hPQ.2
  haveI := hPS.toNontrivial
  have hne_top : GLAPPrimeCore 3 ↥C ≠ ⊤ := by
    intro htop
    have hq : Subsingleton (PQuot 3 C) := by
      unfold PQuot
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have hsub : Subsingleton (PSimple 3 C) :=
      ⟨fun a b => by
        obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
        rw [Subsingleton.elim u v]⟩
    exact not_subsingleton (PSimple 3 C) hsub
  have hO : GLAPPrimeCore 3 ↥C = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥C)).resolve_right hne_top
  have eQ : PQuot 3 C ≃* ↥C := (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hsQ : IsSimpleGroup (PQuot 3 C) := eQ.isSimpleGroup
  have hZ : Subgroup.center (PQuot 3 C) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PQuot 3 C)) with h1 | h1
    · exact h1
    · exfalso
      have hsub : Subsingleton (PSimple 3 C) := by
        unfold PSimple
        rw [h1]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton (PSimple 3 C) hsub
  have ePS : PSimple 3 C ≃* ↥C :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eQ
  have hO' : GLAPPrimeCoreOf 3 C = ⊥ := by
    show (GLAPPrimeCore 3 ↥C).map C.subtype = ⊥
    rw [hO, Subgroup.map_bot]
  exact ⟨hlayer, hJ, hO', (catalogIs_congr ePS).2 hC⟩

theorem nonInnDiag_of_r2Prop (hin : AutCalcAt G p) {X L : Subgroup G} {g : G} (hL : GLAPComponent p X L)
    (hch : IsChevSimple 2 (PSimple p L)) (h : R2Prop p g L) : NonInnDiag p g L := by
  rcases h with hf | ⟨hp3, htd, hn⟩
  · exact hin.field_nonInnDiag X L g hL hch hf
  · subst hp3
    exact hin.td4_nonInnDiag X L g hL htd hn

theorem not_innDiagOn_of_r2Prop (hin : AutCalcAt G p) {X L B : Subgroup G} {b : G}
    (hL : GLAPComponent p X L) (hch : IsChevSimple 2 (PSimple p L)) (hbB : b ∈ B) (h : R2Prop p b L) :
    ¬ InnDiagOn p B L := fun hB =>
  (nonInnDiag_of_r2Prop hin hL hch h).2 (innDiagOn_mono hB (Subgroup.zpowers_le.2 hbB))

theorem ucore (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hnA : ¬ CaseA p B x L b) :
    UCore G p B x L b := by
  have hS := sstar_triple h.star
  have hL := hS.2.2
  have hch : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc h.star
  have hq : CFSG.Open.IsQuasisimple ↥L := (hc.stage9.1 B x L h.star).1
  have hG : IsGStar p B L := isGStar_of_dLevel_eq_five (sstar_s0 h.star) hd5
  have hnI : ¬ InnDiagOn p B L := not_innDiagOn_of_r2Prop hin.aut hL hch h.mem h.prop
  rcases hin.i265 B x L b h.star hch hG h.mem h.not_mem h.prop h.td4_g2 h.I_ne hnI with hE | ⟨hp3, hU, hF⟩
  · exact absurd hE hnA
  · subst hp3
    obtain ⟨e⟩ := S9.nonempty_pSimple_equiv hc.ctx.prime hL hq
    have hLU : catalogIs (↥L ⧸ Subgroup.center ↥L) S9.isU4eight := by
      rw [← catalogIs_congr e]; exact hU
    have hLiso : catalogIs ↥L S9.isU4eight := hin.mult L hq hLU
    obtain ⟨hI, hc6⟩ := hin.i91u _ L b hL hLiso hF
    obtain ⟨hIeq, hIcomp, hIcore, hIiso⟩ := layer_eq_of_isU4two hI h.I_ne
    have hIeq' : Ipart 3 L b = L ⊓ cx b := hIeq
    refine ⟨rfl, hLiso, hF, hI, hIeq', ?_, ?_, ?_, hc6⟩
    · rw [hIeq']; exact hIcomp
    · rw [hIeq']; exact hIcore
    · rw [hIeq']; exact hIiso

private theorem lemma103_le_normalizer_of_comm {B A : Subgroup G} (hB : IsElemAbelian p B)
    (hA : A ≤ B) : B ≤ Subgroup.normalizer (A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have hfix : ∀ z ∈ A, g * z * g⁻¹ = z := fun z hz => by
    rw [isElemAbelian_commute hB hg (hA hz)]
    group
  have hgi : g⁻¹ ∈ B := B.inv_mem hg
  have hfix' : ∀ z ∈ A, g⁻¹ * z * g⁻¹⁻¹ = z := fun z hz => by
    rw [isElemAbelian_commute hB hgi (hA hz)]
    group
  intro y
  constructor
  · intro hy
    rw [hfix y hy]
    exact hy
  · intro hy
    have h3 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    have h4 := hfix' (g * y * g⁻¹) hy
    rw [h4] at h3
    rw [← h3]
    exact hy

private theorem lemma103_eq_one_of_central {L : Subgroup G} (hZ : Subgroup.center ↥L = ⊥) {u : G}
    (hu : u ∈ L) (hc : ∀ y ∈ L, y * u = u * y) : u = 1 := by
  have hmem : (⟨u, hu⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  simpa using congrArg Subtype.val hmem

theorem B_decomp_U48_core (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b) :
    B = Dgrp b x ⊔ (B ⊓ L) ∧ Dgrp b x ⊓ (B ⊓ L) = ⊥ := by
  classical
  have hp3 := hU.p3
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian 3 B := hS.1.1
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hLc : GLAPComponent 3 (cx x) L := hS.2.2
  have hLC : L ≤ cx x := hLc.1
  have hBC : B ≤ cx x := isElemAbelian_le_centralizer hBel hxB
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := sstar_norm h.star
  have hbB : b ∈ B := h.mem
  have hq : CFSG.Open.IsQuasisimple ↥L := (hc.stage9.1 B x L h.star).1
  have hch : IsChevSimple 2 (PSimple 3 L) := sstar_chev2 hc h.star
  have hLsimple : IsSimpleGroup ↥L := isSimple_of_isU4eight hU.L_iso
  have hPS : IsSimpleGroup (PSimple 3 L) := (isQuasisimple_pQuot_of_glaPComponent hp hLc).2
  haveI := hPS.toNontrivial
  have hne_top : GLAPPrimeCore 3 ↥L ≠ ⊤ := by
    intro htop
    have hq' : Subsingleton (PQuot 3 L) := by
      unfold PQuot
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    haveI := hq'
    have hsub : Subsingleton (PSimple 3 L) :=
      ⟨fun a b => by
        obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
        rw [Subsingleton.elim u v]⟩
    exact not_subsingleton (PSimple 3 L) hsub
  have hOL : GLAPPrimeCore 3 ↥L = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥L)).resolve_right hne_top
  have hOLof : GLAPPrimeCoreOf 3 L = ⊥ := by
    show (GLAPPrimeCore 3 ↥L).map L.subtype = ⊥
    rw [hOL, Subgroup.map_bot]
  have hZ : Subgroup.center ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h1 | h1
    · exact h1
    · exfalso
      have hsub : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
        rw [h1]
        exact QuotientGroup.subsingleton_quotient_top
      haveI := hq.2.toNontrivial
      exact not_subsingleton _ hsub
  have hinn : ∀ g, InducesInnerMod 3 L g → ∃ l ∈ L, ∀ y ∈ L, g⁻¹ * y * g = l⁻¹ * y * l := by
    rintro g ⟨l, hl, hy⟩
    refine ⟨l, hl, fun y hy' => ?_⟩
    have h1 := hy y hy'
    rw [hOLof, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  have hbnin : ¬ InducesInnerMod 3 L b := fun hi =>
    (hin.aut.field_nonInnDiag (cx x) L b hLc hch hU.field).2
      (hin.aut.inner_innDiag (cx x) L b hLc hch (hBN hbB) hi)
  obtain ⟨A₀, hA₀B, hcardA, hA₀in⟩ := hin.aut48 (cx x) L B hLc hU.L_iso hBN hBel
  have hbA₀ : b ∉ A₀ := fun hb => hbnin (hA₀in b hb)
  have hxzx : ∀ c ∈ A₀, ∃ l ∈ B ⊓ L, ∃ z ∈ Subgroup.zpowers x, c = l * z := by
    intro c hc0
    have hcB : c ∈ B := hA₀B hc0
    obtain ⟨l₀, hl₀, hconj⟩ := hinn c (hA₀in c hc0)
    set z : G := l₀⁻¹ * c with hzdef
    have hzL : ∀ y ∈ L, z * y = y * z := by
      intro y0 hy0
      have hy' : l₀ * y0 * l₀⁻¹ ∈ L := L.mul_mem (L.mul_mem hl₀ hy0) (L.inv_mem hl₀)
      have key := hconj (l₀ * y0 * l₀⁻¹) hy'
      have hr : l₀⁻¹ * (l₀ * y0 * l₀⁻¹) * l₀ = y0 := by group
      rw [hr] at key
      have h1 : (l₀ * y0 * l₀⁻¹) * c = c * y0 := by
        calc (l₀ * y0 * l₀⁻¹) * c = c * (c⁻¹ * (l₀ * y0 * l₀⁻¹) * c) := by group
          _ = c * y0 := by rw [key]
      calc z * y0 = l₀⁻¹ * (c * y0) := by rw [hzdef]; group
        _ = l₀⁻¹ * ((l₀ * y0 * l₀⁻¹) * c) := by rw [h1]
        _ = y0 * (l₀⁻¹ * c) := by group
    have hzC : z ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun y hy => (hzL y hy).symm
    have hzCM : CentMod 3 L z := centMod_of_mem_centralizer hzC
    have hxl₀ : Commute x l₀ := (Subgroup.mem_centralizer_singleton_iff.1 (hLC hl₀)).symm
    have hxc : Commute x c := isElemAbelian_commute hBel hxB hcB
    have hxz : Commute x z := by
      rw [hzdef]
      exact (hxl₀.inv_right).mul_right hxc
    have hcz : c = l₀ * z := by rw [hzdef]; group
    have hc3 : c ^ 3 = 1 := hBel.2 c hcB
    have hl₀z : Commute l₀ z := (hzL l₀ hl₀).symm
    have hmul : (l₀ * z) ^ 3 = l₀ ^ 3 * z ^ 3 := hl₀z.mul_pow 3
    have hprod : l₀ ^ 3 * z ^ 3 = 1 := by rw [← hmul, ← hcz, hc3]
    have hl3L : l₀ ^ 3 ∈ L := L.pow_mem hl₀ 3
    have hz3C : ∀ y ∈ L, y * l₀ ^ 3 = l₀ ^ 3 * y := by
      intro y hy
      have hcy : Commute (z ^ 3) y := Commute.pow_left (show Commute z y from hzL y hy) 3
      have hl3 : l₀ ^ 3 = (z ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hprod
      rw [hl3]
      exact (hcy.symm.inv_right).eq
    have hl3one : l₀ ^ 3 = 1 := lemma103_eq_one_of_central hZ hl3L hz3C
    have hz3one : z ^ 3 = 1 := by
      rw [hl3one, one_mul] at hprod
      exact hprod
    have hzx : z ∈ Subgroup.zpowers x := by
      by_contra hzx
      have hxx3 : x ^ 3 = 1 := hBel.2 x hxB
      obtain ⟨hE, hEcard⟩ :=
        Prop53.isElemAbelian_card_sup_zpowers hp hxz.symm.eq hz3one hxx3 hx1 hzx
      have hzcm : z ∈ centModSubgroup 3 L := centMod_iff.1 hzCM
      have hxcm : x ∈ centModSubgroup 3 L :=
        centMod_iff.1 (centMod_zpowers_of_le hLC (Subgroup.mem_zpowers x))
      have hSle : Subgroup.zpowers z ⊔ Subgroup.zpowers x ≤ centModSubgroup 3 L :=
        sup_le (Subgroup.zpowers_le.2 hzcm) (Subgroup.zpowers_le.2 hxcm)
      have hcyc := (sstar_cyc h.star) (Subgroup.zpowers z ⊔ Subgroup.zpowers x)
        (fun g hg => centMod_iff.2 (hSle hg)) (isPGroup_of_isElemAbelian hE)
      have hle3 := card_le_of_isCyclic_of_pow hp hcyc (fun d hd => hE.2 d hd)
      rw [hEcard] at hle3
      norm_num at hle3
    have hzB : z ∈ B := (Subgroup.zpowers_le.2 hxB) hzx
    have hl₀B : l₀ ∈ B := by
      have : l₀ = c * z⁻¹ := by rw [hcz]; group
      rw [this]
      exact B.mul_mem hcB (B.inv_mem hzB)
    exact ⟨l₀, ⟨hl₀B, hl₀⟩, z, hzx, hcz⟩
  have hxD : Subgroup.zpowers x ≤ Dgrp b x :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert_of_mem b (Set.mem_singleton x)))
  have hbD : Subgroup.zpowers b ≤ Dgrp b x :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert b {x}))
  have hA₀le : A₀ ≤ Dgrp b x ⊔ (B ⊓ L) := by
    intro c hc0
    obtain ⟨l, hl, z, hz, rfl⟩ := hxzx c hc0
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hl) (Subgroup.mem_sup_left (hxD hz))
  have hBN0 : B ≤ Subgroup.normalizer (A₀ : Set G) := lemma103_le_normalizer_of_comm hBel hA₀B
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hb1 : b ≠ 1 := fun e => hbA₀ (by rw [e]; exact A₀.one_mem)
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hcardzb : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hord]
  have hzbB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.2 hbB
  have hint : Nat.card (A₀ ⊓ Subgroup.zpowers b : Subgroup G) = 1 := by
    have hdvd : Nat.card (A₀ ⊓ Subgroup.zpowers b : Subgroup G) ∣ 3 := by
      rw [← hcardzb]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exact h1
    · exfalso
      have heq : A₀ ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hcardzb, h1]))
      have hbmem : b ∈ A₀ ⊓ Subgroup.zpowers b := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact hbA₀ (Subgroup.mem_inf.1 hbmem).1
  have hprodK := card_sup_mul_card_inf_of_le_normalizer (A := A₀) (B := Subgroup.zpowers b)
    (hzbB.trans hBN0)
  rw [hint, hcardzb, mul_one] at hprodK
  have hKB : A₀ ⊔ Subgroup.zpowers b = B :=
    Subgroup.eq_of_le_of_card_ge (sup_le hA₀B hzbB) (by rw [hprodK]; omega)
  have hDB : Dgrp b x ≤ B :=
    (Subgroup.closure_le B).2 (Set.insert_subset_iff.2 ⟨hbB, Set.singleton_subset_iff.2 hxB⟩)
  have hB_le : B ≤ Dgrp b x ⊔ (B ⊓ L) := by
    have h := sup_le hA₀le ((Subgroup.zpowers_le.2 (Subgroup.subset_closure
      (Set.mem_insert b {x}))).trans le_sup_left)
    rw [hKB] at h
    exact h
  refine ⟨le_antisymm hB_le (sup_le hDB inf_le_left), ?_⟩
  rw [eq_bot_iff]
  rintro d ⟨hdD, hdBL⟩
  have hdL : d ∈ L := hdBL.2
  rw [dgrp_eq_sup] at hdD
  have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    (Subgroup.zpowers_le.2 hbB).trans
      (lemma103_le_normalizer_of_comm hBel (Subgroup.zpowers_le.2 hxB))
  obtain ⟨w, hw, n, hn, hwn⟩ := lemma103_mem_sup_of_le_normalizer hbN hdD
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hw
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hn
  rw [← hi, ← hj] at hwn
  have hxl : ∀ y ∈ L, Commute x y := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hLC hy)).symm
  have hxjL : ∀ y ∈ L, Commute (x ^ j) y := fun y hy => (hxl y hy).zpow_left j
  have hbpow : ∀ k : ℤ, b ^ k = b ^ (k % 3) := fun k => by
    have := zpow_mod_orderOf b k
    rw [hord] at this
    simpa using this.symm
  have hbi_eq : b ^ i = d * (x ^ j)⁻¹ := by
    rw [← hwn]
    group
  have hi3 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hi3 with h0 | h12
  ·
    have hbi1 : b ^ i = 1 := by
      rw [hbpow i, h0, zpow_zero]
    have hdx : d = x ^ j := by
      have h1 : d * (x ^ j)⁻¹ = 1 := by rw [← hbi_eq, hbi1]
      calc d = d * (x ^ j)⁻¹ * x ^ j := by group
        _ = x ^ j := by rw [h1, one_mul]
    have hxjL' : x ^ j ∈ L := by
      rw [← hdx]
      exact hdL
    have hxj1 : x ^ j = 1 :=
      lemma103_eq_one_of_central hZ hxjL' (fun y hy => ((hxjL y hy).symm).eq)
    rw [Subgroup.mem_bot, hdx, hxj1]
  ·
    exfalso
    have hii : (i * i) % 3 = 1 := by
      rw [Int.mul_emod]
      rcases h12 with h | h <;> simp [h]
    have hbii : b ^ (i * i) = b := by
      rw [hbpow (i * i), hii, zpow_one]
    have hcomm : Commute (b ^ i) (x ^ j) := by
      have hxb : Commute x b := isElemAbelian_commute hBel hxB hbB
      exact ((hxb.zpow_left j).zpow_right i).symm
    have hcommd : Commute d (x ^ j)⁻¹ := by
      rw [← hwn]
      exact hcomm.inv_right.mul_left (Commute.refl _).inv_right
    set v : G := ((x ^ j)⁻¹) ^ i with hvdef
    set l : G := d ^ i with hldef
    have hbl : b = l * v := by
      calc b = b ^ (i * i) := hbii.symm
        _ = (b ^ i) ^ i := zpow_mul b i i
        _ = (d * (x ^ j)⁻¹) ^ i := by rw [hbi_eq]
        _ = d ^ i * ((x ^ j)⁻¹) ^ i := hcommd.mul_zpow i
    have hvL : ∀ y ∈ L, Commute v y := fun y hy => ((hxjL y hy).inv_left).zpow_left i
    have hdi : l ∈ L := L.zpow_mem hdL i
    apply hbnin
    refine ⟨l, hdi, fun y hy => ?_⟩
    rw [hOLof, Subgroup.mem_bot]
    have hm : l⁻¹ * y * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hdi) hy) hdi
    have hcm : Commute v (l⁻¹ * y * l) := hvL _ hm
    have hfix : v⁻¹ * (l⁻¹ * y * l) * v = l⁻¹ * y * l := by
      calc v⁻¹ * (l⁻¹ * y * l) * v = v⁻¹ * ((l⁻¹ * y * l) * v) := by group
        _ = v⁻¹ * (v * (l⁻¹ * y * l)) := by rw [← hcm.eq]
        _ = l⁻¹ * y * l := by group
    have hsw : (l * v)⁻¹ * y * (l * v) = v⁻¹ * (l⁻¹ * y * l) * v := by group
    rw [hbl, hsw, hfix, inv_mul_cancel]

theorem B_inf_L_le_I (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b) : B ⊓ L ≤ Ipart p L b := by
  intro g hg
  rw [hU.I_eq]
  have hBel : IsElemAbelian p B := (sstar_triple h.star).1.1
  exact ⟨hg.2, Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hg.1 h.mem)⟩

theorem B_decomp_U48 (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b) :
    B = Dgrp b x ⊔ (B ⊓ L) ∧ Dgrp b x ⊓ (B ⊓ L) = ⊥ ∧ B ⊓ L ≤ Ipart p L b :=
  ⟨(B_decomp_U48_core hc hin h hU).1, (B_decomp_U48_core hc hin h hU).2, B_inf_L_le_I hc hin h hU⟩

theorem centRank_U48 (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b)
    (hdec : B = Dgrp b x ⊔ (B ⊓ L) ∧ Dgrp b x ⊓ (B ⊓ L) = ⊥ ∧ B ⊓ L ≤ Ipart p L b) :
    ∃ A : Subgroup G, IsElemAbelian p A ∧ A ≤ cs B ∧ p ^ 5 ≤ Nat.card A := by
  have hp3 := hU.p3
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian 3 B := hS.1.1
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hLC : L ≤ cx x := hS.2.2.1
  have hbB : b ∈ B := h.mem
  have hbx : b ∉ Subgroup.zpowers x := h.not_mem
  have hBLel : IsElemAbelian 3 (B ⊓ L) := isElemAbelian_mono hBel inf_le_left
  obtain ⟨E', hEBL, hE'J, hE'el, hE'card⟩ :=
    hin.i1024 (L ⊓ cx b) (Ipart 3 L b) (B ⊓ L) hU.I_comp hU.I_iso hdec.2.2 hBLel
  have hE'Ic : E' ≤ L ⊓ cx b := by
    rw [← hU.I_eq]
    exact hE'J
  have hE'L : E' ≤ L := hE'Ic.trans inf_le_left
  obtain ⟨hDB, hDel, hDcard⟩ := card_Dgrp hBel hp hbB hxB hx1 hbx
  have hbE : b ∈ Subgroup.centralizer (E' : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun e he => (Subgroup.mem_centralizer_singleton_iff.1 (hE'Ic he).2)
  have hxE : x ∈ Subgroup.centralizer (E' : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun e he => (Subgroup.mem_centralizer_singleton_iff.1 (hLC (hE'L he)))
  have hDE : Dgrp b x ≤ Subgroup.centralizer (E' : Set G) :=
    (Subgroup.closure_le (Subgroup.centralizer (E' : Set G))).2
      (Set.insert_subset_iff.2 ⟨hbE, Set.singleton_subset_iff.2 hxE⟩)
  have hBE : B ≤ Subgroup.centralizer (E' : Set G) := by
    calc B = Dgrp b x ⊔ (B ⊓ L) := hdec.1
      _ ≤ Subgroup.centralizer (E' : Set G) := by
        refine sup_le hDE (fun c hc => Subgroup.mem_centralizer_iff.2 fun e he => ?_)
        exact (isElemAbelian_commute hE'el (hEBL hc) he).symm
  have hA_el : IsElemAbelian 3 (Dgrp b x ⊔ E') :=
    Prop53.isElemAbelian_sup_of_commute hDel hE'el
      (fun d hd c hc => ((Subgroup.mem_centralizer_iff.1 (hDE hd)) c hc).symm)
  have hA_cs : Dgrp b x ⊔ E' ≤ cs B := by
    refine sup_le (fun d hd => Subgroup.mem_centralizer_iff.2 fun c hc => ?_)
      (fun e he => Subgroup.mem_centralizer_iff.2 fun c hc => ?_)
    · exact isElemAbelian_commute hBel hc (hDB hd)
    · exact ((Subgroup.mem_centralizer_iff.1 (hBE hc)) e he).symm
  have hENorm : E' ≤ Subgroup.normalizer ((Dgrp b x : Subgroup G) : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
      ((Subgroup.mem_centralizer_iff.1 (hDE hd)) e he).symm)
  have hprod := card_sup_mul_card_inf_of_le_normalizer (A := Dgrp b x) (B := E') hENorm
  have hDE_bot : Dgrp b x ⊓ E' = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hg' : g ∈ Dgrp b x ⊓ (B ⊓ L) := ⟨hg.1, hDB hg.1, hE'L hg.2⟩
    rw [hdec.2.1] at hg'
    exact hg'
  have hcardA : Nat.card (Dgrp b x ⊔ E' : Subgroup G) = 3 ^ 5 := by
    rw [hDE_bot, Subgroup.card_bot, mul_one, hDcard, hE'card] at hprod
    rw [hprod]
    norm_num
  exact ⟨Dgrp b x ⊔ E', hA_el, hA_cs, hcardA.ge⟩


theorem E1_of_even (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b)
    (hdec : B = Dgrp b x ⊔ (B ⊓ L) ∧ Dgrp b x ⊓ (B ⊓ L) = ⊥ ∧ B ⊓ L ≤ Ipart p L b)
    (hev : Even (Nat.card (GLAPPrimeCoreOf p (cx x)))) :
    ∃ E₁ : Subgroup G, E₁ ≤ B ⊓ L ∧ IsElemAbelian p E₁ ∧ Nat.card E₁ = p ^ 3 := by
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hT := sstar_triple h.star
  have hBmax : GLAIsBmax p B := hT.1
  have hBel : IsElemAbelian p B := hT.1.1
  have hxB : x ∈ B := hT.2.1.1
  have hx1 : x ≠ 1 := hT.2.1.2.1
  have hLx : L ≤ cx x := hT.2.2.1
  have hbB : b ∈ B := h.mem
  have hbx : b ∉ Subgroup.zpowers x := h.not_mem
  obtain ⟨hDB, hDel, hDcard⟩ := card_Dgrp hBel hp hbB hxB hx1 hbx
  have hp3 : p = 3 := hU.p3
  subst hp3
  have hIcomp : GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) := hU.I_comp
  have hIiso : catalogIs (PSimple 3 (Ipart 3 L b)) S9.isU4two := hU.I_iso
  have hE0 : IsElemAbelian 3 (⊥ : Subgroup G) := isElemAbelian_mono hBel bot_le
  obtain ⟨E', -, hE'I, hE'el, hE'card⟩ :=
    hin.i1024 (L ⊓ cx b) (Ipart 3 L b) ⊥ hIcomp hIiso bot_le hE0
  have hE'L : E' ≤ L := hE'I.trans (hIcomp.1.trans inf_le_left)
  have hE'cb : E' ≤ cx b := hE'I.trans (hIcomp.1.trans inf_le_right)
  have hbC : b ∈ Subgroup.centralizer (E' : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun e he => Subgroup.mem_centralizer_singleton_iff.1 (hE'cb he)
  have hxC : x ∈ Subgroup.centralizer (E' : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun e he =>
      Subgroup.mem_centralizer_singleton_iff.1 (hLx (hE'L he))
  have hDC : Dgrp b x ≤ Subgroup.centralizer (E' : Set G) := by
    rw [dgrp_eq_sup]
    exact sup_le (Subgroup.zpowers_le.2 hbC) (Subgroup.zpowers_le.2 hxC)
  have hE'C : E' ≤ Subgroup.centralizer (Dgrp b x : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun d hd =>
      ((Subgroup.mem_centralizer_iff.1 (hDC hd)) e he).symm
  have hE'N : E' ≤ Subgroup.normalizer (Dgrp b x : Set G) :=
    hE'C.trans (Subgroup.centralizer_le_normalizer _)
  have hA : IsElemAbelian 3 (Dgrp b x ⊔ E') := isElemAbelian_sup_of_commute hDel hE'el hDC
  have hDE'inf : Dgrp b x ⊓ E' = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hmem : g ∈ Dgrp b x ⊓ (B ⊓ L) := ⟨hg.1, hDB hg.1, hE'L hg.2⟩
    rw [hdec.2.1] at hmem
    exact hmem
  have hcard1 := card_sup_mul_card_inf_of_le_normalizer hE'N
  rw [hDE'inf, Subgroup.card_bot, mul_one, hDcard, hE'card] at hcard1
  have hsub : Dgrp b x ⊔ E' ≤ L ⊔ B := sup_le (hDB.trans le_sup_right) (hE'L.trans le_sup_left)
  have hBC : B ≤ cx x := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hg hxB)
  have hYN : L ⊔ B ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 (cx x) : Set G) :=
    sup_le (hLx.trans (le_normalizer_glaPPrimeCoreOf 3 (cx x)))
      (hBC.trans (le_normalizer_glaPPrimeCoreOf 3 (cx x)))
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 (cx x))) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf (by norm_num) (cx x)
  have hmax : IsMaxRankIn 3 B (L ⊔ B) := isMaxRankIn_of_even hp hp2 hBmax hev hcop hYN
  have hBig : Nat.card ↥(Dgrp b x ⊔ E') ≤ Nat.card B := hmax _ hsub hA
  have hBLC : B ⊓ L ≤ Subgroup.centralizer (Dgrp b x : Set G) := fun k hk =>
    Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hBel (hDB hd) hk.1
  have hBLN : B ⊓ L ≤ Subgroup.normalizer (Dgrp b x : Set G) :=
    hBLC.trans (Subgroup.centralizer_le_normalizer _)
  have hcard2 := card_sup_mul_card_inf_of_le_normalizer hBLN
  rw [← hdec.1, hdec.2.1, Subgroup.card_bot, mul_one, hDcard] at hcard2
  have h27 : 3 ^ 3 ≤ Nat.card ↥(B ⊓ L) := by
    have h5 : Nat.card ↥(Dgrp b x ⊔ E') = 3 ^ 5 := by rw [hcard1]; norm_num
    rw [h5, hcard2] at hBig
    norm_num at hBig ⊢
    omega
  have hBLel : IsElemAbelian 3 (B ⊓ L) := isElemAbelian_mono hBel inf_le_left
  obtain ⟨H, hH⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 3) hp (isPGroup_of_isElemAbelian hBLel) h27
  refine ⟨H.map (B ⊓ L).subtype, (Subgroup.map_subtype_le _), ?_, ?_⟩
  · exact isElemAbelian_mono hBel ((Subgroup.map_subtype_le _).trans inf_le_left)
  · rw [Subgroup.card_map_of_injective (f := (B ⊓ L).subtype) Subtype.val_injective]
    exact hH

private theorem y9x_commutator_self {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L) :
    ⁅L, L⁆ = L := by
  have h := Subgroup.map_commutator (⊤ : Subgroup ↥L) (⊤ : Subgroup ↥L) L.subtype
  have hc : (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ : Subgroup ↥L) = ⊤ := hq.1
  have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype L
  rw [hc, htop] at h
  exact h.symm

private theorem y9x_inf_central {L O : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hLO : ¬ L ≤ O) (hON : L ≤ Subgroup.normalizer (O : Set G)) :
    ∀ n ∈ L ⊓ O, ∀ l ∈ L, l * n = n * l := by
  have hMn : ((L ⊓ O).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (hON g.2) (n : G)).1 hn.2
  have hMne : (L ⊓ O).subgroupOf L ≠ ⊤ := by
    intro htop
    apply hLO
    intro l hl
    have hmem : (⟨l, hl⟩ : ↥L) ∈ (L ⊓ O).subgroupOf L := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.1 hmem).2
  have hc := le_center_of_normal_of_isQuasisimple hq hMn hMne
  intro n hn l hl
  have hnM : (⟨n, hn.1⟩ : ↥L) ∈ (L ⊓ O).subgroupOf L := Subgroup.mem_subgroupOf.2 hn
  have hz := Subgroup.mem_center_iff.1 (hc hnM) ⟨l, hl⟩
  exact congrArg Subtype.val hz

private theorem y9x_commutator_eq_bot {L O : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hLN : O ≤ Subgroup.normalizer (L : Set G)) (hON : L ≤ Subgroup.normalizer (O : Set G))
    (hLO : ¬ L ≤ O) : ⁅L, O⁆ = ⊥ := by
  have hcen := y9x_inf_central hq hLO hON
  have hsub : ⁅L, O⁆ ≤ L ⊓ O := by
    refine Subgroup.commutator_le.2 fun h hh k hk => ?_
    rw [commutatorElement_def]
    constructor
    · have h1 : k * h⁻¹ * k⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hLN hk) h⁻¹).1 (L.inv_mem hh)
      have h2 : h * k * h⁻¹ * k⁻¹ = h * (k * h⁻¹ * k⁻¹) := by group
      rw [h2]
      exact L.mul_mem hh h1
    · have h1 : h * k * h⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hON hh) k).1 hk
      have h2 : h * k * h⁻¹ * k⁻¹ = (h * k * h⁻¹) * k⁻¹ := by group
      rw [h2]
      exact O.mul_mem h1 (O.inv_mem hk)
  have hcentral : ⁅L, O⁆ ≤ Subgroup.centralizer (L : Set G) := by
    refine hsub.trans ?_
    intro n hn
    exact Subgroup.mem_centralizer_iff.2 fun l hl => hcen n hn l hl
  have h1 : ⁅⁅L, O⁆, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcentral
  have h2 : ⁅⁅O, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm O L]
    exact h1
  have h3 : ⁅⁅L, L⁆, O⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [y9x_commutator_self hq] at h3
  exact h3

private theorem y9x_le_centralizer_core {Y L : Subgroup G} (hp : p.Prime) (hLc : GLAPComponent p Y L)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hLY : GLAPLayer p Y = L)
    (hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p Y))) :
    L ≤ Subgroup.centralizer ((GLAPPrimeCoreOf p Y : Subgroup G) : Set G) := by
  have hOY : GLAPPrimeCoreOf p Y ≤ Y := Subgroup.map_subtype_le _
  have hLN : GLAPPrimeCoreOf p Y ≤ Subgroup.normalizer (L : Set G) := fun o ho => by
    rw [← hLY]
    exact mem_normalizer_glaPLayer (Subgroup.le_normalizer (hOY ho))
  have hON : L ≤ Subgroup.normalizer (GLAPPrimeCoreOf p Y : Set G) :=
    hLc.1.trans (le_normalizer_glaPPrimeCoreOf p Y)
  have hLO : ¬ L ≤ GLAPPrimeCoreOf p Y := by
    intro hLO
    have hdvd : Nat.card ↥L ∣ Nat.card ↥(GLAPPrimeCoreOf p Y) := Subgroup.card_dvd_of_le hLO
    have hcopL : Nat.Coprime p (Nat.card ↥L) := Nat.Coprime.coprime_dvd_right hdvd hcop
    have htop : GLAPPrimeCore p ↥L = ⊤ := by
      refine top_le_iff.1 (le_sSup ⟨Subgroup.normal_top, ?_⟩)
      rw [Subgroup.card_top]
      exact hcopL
    have hnt := isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hLc)
    have hsub : Subsingleton (↥L ⧸ GLAPPrimeCore p ↥L) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_nontrivial_iff_subsingleton.2 hsub) hnt
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (y9x_commutator_eq_bot hq hLN hON hLO)

theorem exists_S_inv (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hev : Even (Nat.card (GLAPPrimeCoreOf p (cx x)))) :
    ∃ S : Subgroup G, S ≤ GLAPPrimeCoreOf p (cx x) ∧ IsPGroup 2 S ∧ S ≠ ⊥ ∧
      B ≤ Subgroup.normalizer (S : Set G) ∧ L ≤ Subgroup.normalizer (S : Set G) := by
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hT := sstar_triple h.star
  have hBel : IsElemAbelian p B := hT.1.1
  have hxB : x ∈ B := hT.2.1.1
  have hLc : GLAPComponent p (cx x) L := hT.2.2
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p (cx x))) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp (cx x)
  have hBC : B ≤ cx x := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hg hxB)
  have hBN : B ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p (cx x) : Subgroup G) : Set G) :=
    hBC.trans (le_normalizer_glaPPrimeCoreOf p (cx x))
  have hLC := y9x_le_centralizer_core hp hLc ((hc.stage9.1 B x L h.star).1) (sstar_layer hc h.star) hcop
  obtain ⟨R, hRO, hR2, hRidx, hBR⟩ :=
    exists_invariant_sylow_two hp hp2 (isPGroup_of_isElemAbelian hBel) hBN hcop
  have hR : R ≠ ⊥ := by
    rintro rfl
    apply hRidx
    have hmul := Subgroup.relIndex_mul_card (H := (⊥ : Subgroup G)) (K := GLAPPrimeCoreOf p (cx x))
    rw [bot_inf_eq, Subgroup.card_bot, mul_one] at hmul
    rw [hmul]
    exact even_iff_two_dvd.1 hev
  refine ⟨R, hRO, hR2, hR, hBR, ?_⟩
  exact (hLC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hRO))).trans
    (Subgroup.centralizer_le_normalizer _)

private theorem y9x_dgrp_le_centralizer {a c j : G} (ha : a * j = j * a) (hc : c * j = j * c) :
    Dgrp a c ≤ Subgroup.centralizer ({j} : Set G) := by
  refine (Subgroup.closure_le _).2 ?_
  intro z hz
  rcases hz with rfl | hz
  · exact Subgroup.mem_centralizer_singleton_iff.2 ha
  · rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Subgroup.mem_centralizer_singleton_iff.2 hc

private theorem y9x_inf_le_cs_D0_aux {x y : G} {L : Subgroup G} (hLx : L ≤ cx x) :
    L ⊓ cx y ≤ cs (Dgrp x y) := by
  intro f hf
  have hfx : x * f = f * x := (Subgroup.mem_centralizer_singleton_iff.1 (hLx hf.1)).symm
  have hfy : y * f = f * y := (Subgroup.mem_centralizer_singleton_iff.1 hf.2).symm
  exact Subgroup.mem_centralizer_iff.2 fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 (y9x_dgrp_le_centralizer hfx hfy hg)

private theorem y9x_center_bot {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hs : IsSimpleGroup ↥L) : Subgroup.center ↥L = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with hb | ht
  · exact hb
  · exfalso
    have hcomm : commutator ↥L = ⊥ := (commutator_eq_bot_iff_center_eq_top ↥L).2 ht
    have htop : commutator ↥L = ⊤ := hq.1
    have hbot : (⊤ : Subgroup ↥L) = ⊥ := htop.symm.trans hcomm
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial ↥L).exists_pair_ne
    have ha : a ∈ (⊥ : Subgroup ↥L) := hbot ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup ↥L) := hbot ▸ Subgroup.mem_top b
    exact hab ((Subgroup.mem_bot.1 ha).trans (Subgroup.mem_bot.1 hb).symm)

private theorem y9x_pQuot_subsingleton {p : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hcop : Nat.Coprime p (Nat.card J)) : Subsingleton (↥J ⧸ GLAPPrimeCore p ↥J) := by
  have htop : GLAPPrimeCore p ↥J = ⊤ := by
    refine top_le_iff.1 (le_sSup ⟨Subgroup.normal_top, ?_⟩)
    rw [Subgroup.card_top]
    exact hcop
  rw [htop]
  exact QuotientGroup.subsingleton_quotient_top

theorem exists_S0_of_N (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hU : UCore G p B x L b) {S : Subgroup G} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hSB : B ≤ Subgroup.normalizer (S : Set G)) (hSL : L ≤ Subgroup.normalizer (S : Set G))
    {y : G} {J : Subgroup G} (hyB : y ∈ B ⊓ L) (hy1 : y ≠ 1) (hJlay : J = GLAPLayer p (L ⊓ cx y))
    (hJ : GLAPComponent p (L ⊓ cx y) J) (hJU : catalogIs (PSimple 3 J) S9.isU3eight) :
    ∃ d ∈ Dgrp x y, d ≠ 1 ∧ ∃ S₀ : Subgroup G, IsPGroup 2 S₀ ∧ S₀ ≠ ⊥ ∧ S₀ ≤ cx d ∧
      B ≤ Subgroup.normalizer (S₀ : Set G) ∧ (⁅S₀, J⁆ : Subgroup G) = S₀ := by
  have hp3 : p = 3 := hU.p3
  subst hp3
  have hp : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hT := sstar_triple h.star
  have hBel : IsElemAbelian 3 B := hT.1.1
  have hxB : x ∈ B := hT.2.1.1
  have hx1 : x ≠ 1 := hT.2.1.2.1
  have hLc : GLAPComponent 3 (cx x) L := hT.2.2
  have hLx : L ≤ cx x := hLc.1
  have hyB' : y ∈ B := hyB.1
  have hyL : y ∈ L := hyB.2
  have hq : CFSG.Open.IsQuasisimple ↥L := (hc.stage9.1 B x L h.star).1
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hyx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyx
    have hzc : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hgx : Commute (g : G) x := Subgroup.mem_centralizer_singleton_iff.1 (hLx g.2)
      have hgy : Commute (g : G) y := hk ▸ hgx.zpow_right k
      exact hgy.eq
    have hz1 := y9x_center_bot hq (isSimple_of_isU4eight hU.L_iso)
    rw [hz1] at hzc
    exact hy1 (congrArg Subtype.val (Subgroup.mem_bot.1 hzc))
  obtain ⟨hD0B, hD0el, hD0card⟩ := card_Dgrp hBel hp hyB' hxB hx1 hyx
  have hcomm : Dgrp x y = Dgrp y x := by
    show Subgroup.closure {x, y} = Subgroup.closure {y, x}
    rw [Set.pair_comm]
  have hD0B' : Dgrp x y ≤ B := by rw [hcomm]; exact hD0B
  have hD0card' : Nat.card (Dgrp x y) = 3 ^ 2 := by rw [hcomm]; exact hD0card
  have hD0el' : IsElemAbelian 3 (Dgrp x y) := by rw [hcomm]; exact hD0el
  have hJD0 : J ≤ cs (Dgrp x y) := fun j hj => y9x_inf_le_cs_D0_aux hLx (hJ.1 hj)
  have hJN : J ≤ Subgroup.normalizer (S : Set G) := fun j hj => hSL (hJ.1 hj).1
  have hJa : ∀ a ∈ Dgrp x y, ∀ j ∈ J, a * j = j * a := fun a ha j hj =>
    Subgroup.mem_centralizer_iff.1 (hJD0 hj) a ha
  set N : Subgroup G := Subgroup.normalizer (S : Set G) with hNdef
  set O : Subgroup G := pCoreOf 2 N with hOdef
  have hNO : N ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 N
  have hO2 : IsPGroup 2 O := isPGroup_pCoreOf 2 N
  have hcopO : Nat.Coprime 3 (Nat.card O) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hO2
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hcharTwo : ∀ g ∈ N, (∀ o ∈ O, o * g = g * o) → g ∈ O := by
    intro g hg hcg
    have hmem : g ∈ N ⊓ Subgroup.centralizer (O : Set G) :=
      Subgroup.mem_inf.2 ⟨hg, Subgroup.mem_centralizer_iff.2 hcg⟩
    exact hc.ctx.charTwo N ⟨S, hS1, hS2, rfl⟩ hmem
  have hEA : IsElementaryAbelian 3 ↥(Dgrp x y) :=
    { toIsMulCommutative := hD0el'.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one
        (fun g => Subtype.ext (by simpa using hD0el'.2 g.1 g.2)) }
  have hNact : ∀ a : ↥(Dgrp x y), ∀ o ∈ O, (a : G) * o * (a : G)⁻¹ ∈ O := fun a o ho =>
    (Subgroup.mem_normalizer_iff.1 (hNO (hSB (hD0B' a.2))) o).1 ho
  letI : MulDistribMulAction ↥(Dgrp x y) ↥O :=
    { smul := fun a o => ⟨(a : G) * o * (a : G)⁻¹, hNact a o o.2⟩
      one_smul := fun o => Subtype.ext (by
        show (1 : G) * (o : G) * (1 : G)⁻¹ = (o : G)
        group)
      mul_smul := fun a b o => Subtype.ext (by
        show (a : G) * (b : G) * (o : G) * ((a : G) * (b : G))⁻¹ =
          (a : G) * ((b : G) * (o : G) * (b : G)⁻¹) * (a : G)⁻¹
        group)
      smul_one := fun a => Subtype.ext (by
        show (a : G) * (1 : G) * (a : G)⁻¹ = (1 : G)
        group)
      smul_mul := fun a o1 o2 => Subtype.ext (by
        show (a : G) * ((o1 : G) * (o2 : G)) * (a : G)⁻¹ =
          ((a : G) * (o1 : G) * (a : G)⁻¹) * ((a : G) * (o2 : G) * (a : G)⁻¹)
        group) }
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 3) (A := ↥(Dgrp x y)) (H := ↥O)
    (le_of_eq hD0card'.symm) ((Nat.Prime.coprime_iff_not_dvd hp).1 hcopO)
  have hex : ∃ a ∈ Dgrp x y, a ≠ 1 ∧ ∃ c ∈ O, c ∈ Subgroup.centralizer ({a} : Set G) ∧
      ∃ j ∈ J, c * j ≠ j * c := by
    by_contra hno
    have hno' : ∀ a ∈ Dgrp x y, a ≠ 1 → ∀ c ∈ O, c ∈ Subgroup.centralizer ({a} : Set G) →
        ∀ j ∈ J, c * j = j * c := by
      intro a ha ha1 c hcO hca j hj
      by_contra hne
      exact hno ⟨a, ha, ha1, c, hcO, hca, j, hj, hne⟩
    have hle : (⨆ (a : ↥(Dgrp x y)) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) ↥O) ≤
        (Subgroup.centralizer (J : Set G)).subgroupOf O := by
      refine iSup_le fun a => iSup_le fun ha1 => ?_
      intro o ho
      have hao := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a o).1 ho
      have hao' : (a : G) * (o : G) * (a : G)⁻¹ = (o : G) := congrArg Subtype.val hao
      have hcomm' : (a : G) * (o : G) = (o : G) * (a : G) := by
        rw [mul_inv_eq_iff_eq_mul] at hao'
        exact hao'
      have hoC : (o : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 hcomm'.symm
      have hJc := hno' (a : G) a.2 (fun h1 => ha1 (Subtype.ext h1)) (o : G) o.2 hoC
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro j hj
      exact (hJc j hj).symm
    rw [hgen] at hle
    have hJO : ∀ o ∈ O, ∀ j ∈ J, o * j = j * o := by
      intro o ho j hj
      have hmem := hle (Subgroup.mem_top (⟨o, ho⟩ : ↥O))
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hmem
      exact (hmem j hj).symm
    have hJO2 : J ≤ O := fun j hj => hcharTwo j (hJN hj) (fun o ho => hJO o ho j hj)
    have hnt := isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hJ)
    have hcopJ : Nat.Coprime 3 (Nat.card ↥J) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hJO2) hcopO
    exact (not_nontrivial_iff_subsingleton.2 (y9x_pQuot_subsingleton hp hcopJ)) hnt
  obtain ⟨a, ha, ha1, c, hcO, hca, j, hj, hcj⟩ := hex
  set A : Subgroup G := O ⊓ Subgroup.centralizer ({a} : Set G) with hAdef
  have hAO : A ≤ O := inf_le_left
  have hcA : c ∈ A := Subgroup.mem_inf.2 ⟨hcO, hca⟩
  have hnormA : ∀ u ∈ N, Commute u a → u ∈ Subgroup.normalizer (A : Set G) := by
    intro u hu hua
    have fwd : ∀ v ∈ N, Commute v a → ∀ g ∈ A, v * g * v⁻¹ ∈ A := by
      intro v hv hva g hg
      have hga : Commute g a := Subgroup.mem_centralizer_singleton_iff.1 hg.2
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hNO hv) g).1 hg.1, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 ((hva.mul_left hga).mul_left hva.inv_left)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact fwd u hu hua g
    · intro hg
      have h1 := fwd u⁻¹ (N.inv_mem hu) hua.inv_left (u * g * u⁻¹) hg
      have e : u⁻¹ * (u * g * u⁻¹) * u⁻¹⁻¹ = g := by group
      rw [e] at h1
      exact h1
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := fun b' hb' =>
    hnormA b' (hSB hb') (isElemAbelian_commute hBel hb' (hD0B' ha))
  have hJA : J ≤ Subgroup.normalizer (A : Set G) := fun j' hj' =>
    hnormA j' (hJN hj') (hJa a ha j' hj').symm
  have hnormLy : ∀ u ∈ B, u ∈ Subgroup.normalizer ((L ⊓ cx y : Subgroup G) : Set G) := by
    intro u hu
    have hcomm' : Commute u y := isElemAbelian_commute hBel hu hyB'
    have key : ∀ v ∈ B, Commute v y → ∀ l ∈ L ⊓ cx y, v * l * v⁻¹ ∈ L ⊓ cx y := by
      intro v hv hvy l hl
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (sstar_norm h.star hv) l).1 hl.1, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2
        ((hvy.mul_left (Subgroup.mem_centralizer_singleton_iff.1 hl.2)).mul_left hvy.inv_left)
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      exact key u hu hcomm' l hl
    · intro hl
      have h1 := key u⁻¹ (B.inv_mem hu) hcomm'.inv_left _ hl
      have e : u⁻¹ * (u * l * u⁻¹) * u⁻¹⁻¹ = l := by group
      rw [e] at h1
      exact h1
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := fun b' hb' => by
    rw [hJlay]
    exact mem_normalizer_glaPLayer (hnormLy b' hb')
  have hS0O : (⁅A, J⁆ : Subgroup G) ≤ O := by
    refine Subgroup.commutator_le.2 fun g hg j' hj' => ?_
    rw [commutatorElement_def]
    have e : g * j' * g⁻¹ * j'⁻¹ = g * (j' * g⁻¹ * j'⁻¹) := by group
    rw [e]
    exact O.mul_mem (hAO hg)
      ((Subgroup.mem_normalizer_iff.1 (hNO (hJN hj')) g⁻¹).1 (O.inv_mem (hAO hg)))
  have hS0ne : (⁅A, J⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    have hmem : ⁅c, j⁆ ∈ (⁅A, J⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hcA hj
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hcj hmem
  have hS0cx : (⁅A, J⁆ : Subgroup G) ≤ cx a := by
    refine Subgroup.commutator_le.2 fun g hg j' hj' => ?_
    have hga : Commute g a := Subgroup.mem_centralizer_singleton_iff.1 hg.2
    have hja : Commute j' a := (hJa a ha j' hj').symm
    have hcomm'' : Commute (⁅g, j'⁆) a := by
      rw [commutatorElement_def]
      exact (((hga.mul_left hja).mul_left hga.inv_left).mul_left hja.inv_left)
    exact Subgroup.mem_centralizer_singleton_iff.2 hcomm''
  have hcopA : Nat.Coprime 3 (Nat.card A) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hAO) hcopO
  have hI321 : (⁅⁅A, J⁆, J⁆ : Subgroup G) = ⁅A, J⁆ :=
    (i321UsedAt_holds 3) hp A J hcopA hJA (S9.residual_of_component hp hJ)
  exact ⟨a, ha, ha1, ⁅A, J⁆, hO2.to_le hS0O, hS0ne, hS0cx,
    le_normalizer_commutator hBA hBJ, hI321⟩

theorem exists_S0 (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hU : UCore G p B x L b)
    (hev : Even (Nat.card (GLAPPrimeCoreOf p (cx x)))) {y : G} {J : Subgroup G} (hyB : y ∈ B ⊓ L)
    (hy1 : y ≠ 1) (hJlay : J = GLAPLayer p (L ⊓ cx y)) (hJ : GLAPComponent p (L ⊓ cx y) J)
    (hJU : catalogIs (PSimple 3 J) S9.isU3eight) :
    ∃ d ∈ Dgrp x y, d ≠ 1 ∧ ∃ S₀ : Subgroup G, IsPGroup 2 S₀ ∧ S₀ ≠ ⊥ ∧ S₀ ≤ cx d ∧
      B ≤ Subgroup.normalizer (S₀ : Set G) ∧ (⁅S₀, J⁆ : Subgroup G) = S₀ := by
  obtain ⟨S, -, hS2, hS1, hSB, hSL⟩ := exists_S_inv hc h hev
  exact exists_S0_of_N hc h hU hS2 hS1 hSB hSL hyB hy1 hJlay hJ hJU

private theorem y9x_B_normalizes_layer (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hBel : IsElemAbelian p B) {y : G} (hyB : y ∈ B) {J : Subgroup G}
    (hJlay : J = GLAPLayer p (L ⊓ cx y)) : B ≤ Subgroup.normalizer (J : Set G) := by
  intro u hu
  rw [hJlay]
  refine mem_normalizer_glaPLayer ?_
  have hcomm' : Commute u y := isElemAbelian_commute hBel hu hyB
  have key : ∀ v ∈ B, Commute v y → ∀ l ∈ L ⊓ cx y, v * l * v⁻¹ ∈ L ⊓ cx y := by
    intro v hv hvy l hl
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (sstar_norm h.star hv) l).1 hl.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((hvy.mul_left (Subgroup.mem_centralizer_singleton_iff.1 hl.2)).mul_left hvy.inv_left)
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    exact key u hu hcomm' l hl
  · intro hl
    have h1 := key u⁻¹ (B.inv_mem hu) hcomm'.inv_left _ hl
    have e : u⁻¹ * (u * l * u⁻¹) * u⁻¹⁻¹ = l := by group
    rw [e] at h1
    exact h1

theorem K_single_comp (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b)
    {y d : G} {J : Subgroup G} (hyB : y ∈ B ⊓ L) (hy1 : y ≠ 1) (hd : d ∈ Dgrp x y) (hd1 : d ≠ 1)
    (hJlay : J = GLAPLayer p (L ⊓ cx y)) (hJ : GLAPComponent p (L ⊓ cx y) J)
    (hJU : catalogIs (PSimple 3 J) S9.isU3eight) :
    GLAPComponent p (cx d) (closureIn J (GLAPLayer p (cx d))) ∧
      B ≤ Subgroup.normalizer ((closureIn J (GLAPLayer p (cx d)) : Subgroup G) : Set G) := by
  have hp3 : p = 3 := hU.p3
  subst hp3
  have hp : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hT := sstar_triple h.star
  have hBel : IsElemAbelian 3 B := hT.1.1
  have hxB : x ∈ B := hT.2.1.1
  have hx1 : x ≠ 1 := hT.2.1.2.1
  have hLc : GLAPComponent 3 (cx x) L := hT.2.2
  have hLx : L ≤ cx x := hLc.1
  have hyB' : y ∈ B := hyB.1
  have hyL : y ∈ L := hyB.2
  have hq : CFSG.Open.IsQuasisimple ↥L := (hc.stage9.1 B x L h.star).1
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hyx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyx
    have hzc : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hgx : Commute (g : G) x := Subgroup.mem_centralizer_singleton_iff.1 (hLx g.2)
      have hgy : Commute (g : G) y := hk ▸ hgx.zpow_right k
      exact hgy.eq
    have hz1 := y9x_center_bot hq (isSimple_of_isU4eight hU.L_iso)
    rw [hz1] at hzc
    exact hy1 (congrArg Subtype.val (Subgroup.mem_bot.1 hzc))
  obtain ⟨hD0B, hD0el, hD0card⟩ := card_Dgrp hBel hp hyB' hxB hx1 hyx
  have hcomm : Dgrp x y = Dgrp y x := by
    show Subgroup.closure {x, y} = Subgroup.closure {y, x}
    rw [Set.pair_comm]
  have hD0B' : Dgrp x y ≤ B := by rw [hcomm]; exact hD0B
  have hD0card' : Nat.card (Dgrp x y) = 3 ^ 2 := by rw [hcomm]; exact hD0card
  have hxD : x ∈ Dgrp x y := Subgroup.subset_closure (Set.mem_insert x _)
  have hyD : y ∈ Dgrp x y := Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))
  have hdB : d ∈ B := hD0B' hd
  have hFle : L ⊓ cx y ≤ cs (Dgrp x y) := y9x_inf_le_cs_D0_aux hLx
  have hFsub : IsSubnormal (L ⊓ cx y) (cs (Dgrp x y)) := by
    refine IsSubnormal.step hFle ⟨fun n hn g => ?_⟩ (IsSubnormal.refl _)
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgx : (g : G) ∈ cx x :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 g.2 x hxD).symm
    have hgN : (g : G) ∈ Subgroup.normalizer (L : Set G) := by
      rw [← sstar_layer hc h.star]
      exact mem_normalizer_glaPLayer (Subgroup.le_normalizer hgx)
    have hcgy : Commute (g : G) y := (Subgroup.mem_centralizer_iff.1 g.2 y hyD).symm
    have hnY : Commute (n : G) y := Subgroup.mem_centralizer_singleton_iff.1 hn.2
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ L ⊓ cx y
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hgN (n : G)).1 hn.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.mul_left (Commute.mul_left hcgy hnY) hcgy.inv_left
  have hJD : GLAPComponent 3 (cs (Dgrp x y)) J := glaPComponent_of_isSubnormal' hp hFsub hJ
  have hdp : d ^ 3 = 1 := hBel.2 d hdB
  have hcardd : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hdp hd1]
  obtain ⟨e, heD, hed⟩ : ∃ e ∈ Dgrp x y, e ∉ Subgroup.zpowers d := by
    by_contra hcon
    push Not at hcon
    have hle : Dgrp x y ≤ Subgroup.zpowers d := fun z hz => hcon z hz
    have h1 := Subgroup.card_le_of_le hle
    rw [hD0card', hcardd] at h1
    norm_num at h1
  have heB : e ∈ B := hD0B' heD
  obtain ⟨-, -, hDecard⟩ := card_Dgrp hBel hp heB hdB hd1 hed
  have hDe : Dgrp e d = Dgrp x y := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hD0card', hDecard])
    refine (Subgroup.closure_le _).2 ?_
    intro z hz
    rcases hz with rfl | hz
    · exact heD
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hd
  have hcs_eq : cs (Dgrp x y) = cx d ⊓ cs (Subgroup.zpowers e) := by
    apply le_antisymm
    · intro g hg
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hg d hd).symm
      · exact Subgroup.mem_centralizer_iff.2 fun z hz =>
          Subgroup.mem_centralizer_iff.1 hg z (Subgroup.zpowers_le.2 heD hz)
    · intro g hg
      obtain ⟨hgd, hge⟩ := Subgroup.mem_inf.1 hg
      have hege : e * g = g * e := Subgroup.mem_centralizer_iff.1 hge e (Subgroup.mem_zpowers e)
      have hdg : d * g = g * d := (Subgroup.mem_centralizer_singleton_iff.1 hgd).symm
      have hcent := y9x_dgrp_le_centralizer hege hdg
      refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      have hz' : z ∈ Dgrp e d := by
        rw [hDe]
        exact hz
      exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hz')
  have hJcomp : GLAPComponent 3 (cx d ⊓ cs (Subgroup.zpowers e)) J := by
    rw [← hcs_eq]
    exact hJD
  have hBC : B ≤ cx d := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hg hdB)
  have hrank : 3 ^ GLATwoLocalRank 3 ↥(cx d) ≤ Nat.card ↥B := by
    rw [hT.1.2.1]
    exact Nat.pow_le_pow_right (by norm_num) (glaTwoLocalRank_subgroup_le (by norm_num) (cx d))
  obtain ⟨K', hK'comp, hJK', hBK'⟩ := hin.single38 (cx d) e B J
    (isKGroup_of_isKProper hc.ctx.kProper (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hd1))
    heB hBC hBel hrank hJcomp
    (y9x_B_normalizes_layer hc h hBel hyB' hJlay) hJU
  have hKeq := closureIn_layer_eq_of_component hp hK'comp hJ hJK'
  rw [hKeq]
  exact ⟨hK'comp, hBK'⟩

private theorem y9x_le_closureIn (J H : Subgroup G) : J ≤ closureIn J H := by
  refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem H) ?_
  intro j hj
  exact Subgroup.mem_map.2 ⟨j, hj, by simp⟩

theorem K_single_cen (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hU : UCore G p B x L b)
    {y d : G} {J : Subgroup G} (hyB : y ∈ B ⊓ L) (hy1 : y ≠ 1) (hd : d ∈ Dgrp x y) (hd1 : d ≠ 1)
    (hJlay : J = GLAPLayer p (L ⊓ cx y)) (hJ : GLAPComponent p (L ⊓ cx y) J)
    (hKcomp : GLAPComponent p (cx d) (closureIn J (GLAPLayer p (cx d)))) :
    GLAPComponent p (closureIn J (GLAPLayer p (cx d)) ⊓ cs (Dgrp x y)) J ∧
      ∃ x' ∈ Dgrp x y, x' ∉ Subgroup.zpowers d ∧
        GLAPComponent p (closureIn J (GLAPLayer p (cx d)) ⊓ cx x') J := by
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hT := sstar_triple h.star
  have hBel : IsElemAbelian p B := hT.1.1
  have hxB : x ∈ B := hT.2.1.1
  have hx1 : x ≠ 1 := hT.2.1.2.1
  have hLc : GLAPComponent p (cx x) L := hT.2.2
  have hLx : L ≤ cx x := hLc.1
  have hyB' : y ∈ B := hyB.1
  have hyL : y ∈ L := hyB.2
  have hq : CFSG.Open.IsQuasisimple ↥L := (hc.stage9.1 B x L h.star).1
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hyx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyx
    have hzc : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hgx : Commute (g : G) x := Subgroup.mem_centralizer_singleton_iff.1 (hLx g.2)
      have hgy : Commute (g : G) y := hk ▸ hgx.zpow_right k
      exact hgy.eq
    have hz1 := y9x_center_bot hq (isSimple_of_isU4eight hU.L_iso)
    rw [hz1] at hzc
    exact hy1 (congrArg Subtype.val (Subgroup.mem_bot.1 hzc))
  obtain ⟨hD0B, hD0el, hD0card⟩ := card_Dgrp hBel hp hyB' hxB hx1 hyx
  have hcomm : Dgrp x y = Dgrp y x := by
    show Subgroup.closure {x, y} = Subgroup.closure {y, x}
    rw [Set.pair_comm]
  have hD0B' : Dgrp x y ≤ B := by rw [hcomm]; exact hD0B
  have hD0card' : Nat.card (Dgrp x y) = p ^ 2 := by rw [hcomm]; exact hD0card
  have hxD : x ∈ Dgrp x y := Subgroup.subset_closure (Set.mem_insert x _)
  have hyD : y ∈ Dgrp x y := Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))
  have hdB : d ∈ B := hD0B' hd
  have hFle : L ⊓ cx y ≤ cs (Dgrp x y) := y9x_inf_le_cs_D0_aux hLx
  have hFsub : IsSubnormal (L ⊓ cx y) (cs (Dgrp x y)) := by
    refine IsSubnormal.step hFle ⟨fun n hn g => ?_⟩ (IsSubnormal.refl _)
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgx : (g : G) ∈ cx x :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 g.2 x hxD).symm
    have hgN : (g : G) ∈ Subgroup.normalizer (L : Set G) := by
      rw [← sstar_layer hc h.star]
      exact mem_normalizer_glaPLayer (Subgroup.le_normalizer hgx)
    have hcgy : Commute (g : G) y := (Subgroup.mem_centralizer_iff.1 g.2 y hyD).symm
    have hnY : Commute (n : G) y := Subgroup.mem_centralizer_singleton_iff.1 hn.2
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ L ⊓ cx y
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hgN (n : G)).1 hn.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.mul_left (Commute.mul_left hcgy hnY) hcgy.inv_left
  have hJD : GLAPComponent p (cs (Dgrp x y)) J := glaPComponent_of_isSubnormal' hp hFsub hJ
  have hJK : J ≤ closureIn J (GLAPLayer p (cx d)) := y9x_le_closureIn J _
  have hJcs : J ≤ cs (Dgrp x y) := hJ.1.trans hFle
  have hpart1 : GLAPComponent p (closureIn J (GLAPLayer p (cx d)) ⊓ cs (Dgrp x y)) J :=
    glaPComponent_of_le hp hJD (le_inf hJK hJcs) inf_le_right
  have hdp : d ^ p = 1 := hBel.2 d hdB
  have hcardd : Nat.card (Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hdp hd1]
  obtain ⟨x', hx'D, hx'd⟩ : ∃ x' ∈ Dgrp x y, x' ∉ Subgroup.zpowers d := by
    by_contra hcon
    push Not at hcon
    have hle : Dgrp x y ≤ Subgroup.zpowers d := fun z hz => hcon z hz
    have h1 := Subgroup.card_le_of_le hle
    rw [hD0card', hcardd] at h1
    nlinarith [hp.two_le]
  have hx'B : x' ∈ B := hD0B' hx'D
  obtain ⟨hD'B, -, hD'card⟩ := card_Dgrp hBel hp hx'B hdB hd1 hx'd
  have hD'le : Dgrp x' d ≤ Dgrp x y := by
    refine (Subgroup.closure_le _).2 ?_
    intro z hz
    rcases hz with rfl | hz
    · exact hx'D
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hd
  have hDgen : Dgrp x' d = Dgrp x y :=
    Subgroup.eq_of_le_of_card_ge hD'le (by rw [hD0card', hD'card])
  have hKx' : closureIn J (GLAPLayer p (cx d)) ⊓ cx x' =
      closureIn J (GLAPLayer p (cx d)) ⊓ cs (Dgrp x y) := by
    apply le_antisymm
    · intro k hk
      have hkK := (Subgroup.mem_inf.1 hk).1
      have hkx : k ∈ cx x' := (Subgroup.mem_inf.1 hk).2
      refine Subgroup.mem_inf.2 ⟨hkK, ?_⟩
      have hkd : d * k = k * d := (Subgroup.mem_centralizer_singleton_iff.1 (hKcomp.1 hkK)).symm
      have hkx' : x' * k = k * x' := (Subgroup.mem_centralizer_singleton_iff.1 hkx).symm
      have hcent : Dgrp x' d ≤ Subgroup.centralizer ({k} : Set G) :=
        y9x_dgrp_le_centralizer hkx' hkd
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [← hDgen] at hz
      exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hz)
    · intro k hk
      have hkK := (Subgroup.mem_inf.1 hk).1
      have hkD := (Subgroup.mem_inf.1 hk).2
      refine Subgroup.mem_inf.2 ⟨hkK, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hkD x' hx'D).symm
  refine ⟨hpart1, x', hx'D, hx'd, ?_⟩
  rw [hKx']
  exact hpart1

private theorem y9x_mem_normalizer_cx {d g : G} (hg : g ∈ Subgroup.centralizer ({d} : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) := by
  have hgd : Commute g d := Subgroup.mem_centralizer_singleton_iff.1 hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhd : Commute h d := Subgroup.mem_centralizer_singleton_iff.1 hh
    exact Subgroup.mem_centralizer_singleton_iff.2 ((hgd.mul_left hhd).mul_left hgd.inv_left)
  · intro hh
    have hhd : Commute (g * h * g⁻¹) d := Subgroup.mem_centralizer_singleton_iff.1 hh
    have h1 : Commute (g⁻¹ * (g * h * g⁻¹) * g) d := (hgd.inv_left.mul_left hhd).mul_left hgd
    have h2 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rw [h2] at h1
    exact Subgroup.mem_centralizer_singleton_iff.2 h1

theorem S0_le_K (hc : S10Ctx G p) {d : G} {J S₀ : Subgroup G} (hd1 : d ≠ 1)
    (hKcomp : GLAPComponent p (cx d) (closureIn J (GLAPLayer p (cx d)))) (hS₀ : S₀ ≤ cx d)
    (hS₀J : (⁅S₀, J⁆ : Subgroup G) = S₀) (hS₀2 : IsPGroup 2 S₀) :
    S₀ ≤ closureIn J (GLAPLayer p (cx d)) := by
  have hp : p.Prime := hc.ctx.prime
  set K := closureIn J (GLAPLayer p (cx d)) with hKdef
  have hJK : J ≤ K := y9x_le_closureIn J _
  have hcompN : ∀ M : Subgroup G, GLAPComponent p (cx d) M → M ≤ Subgroup.normalizer (K : Set G) := by
    intro M hM
    by_cases hMK : M = K
    · rw [hMK]
      exact Subgroup.le_normalizer
    · intro m hm
      exact (mem_centModSubgroup.1 (le_centModSubgroup_of_ne hp hM hKcomp hMK hm)).1
  have hconjN : ∀ g ∈ cx d, ∀ k ∈ K, g * k * g⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
    intro g hg k hk
    have hg' : g⁻¹ ∈ cx d := (cx d).inv_mem hg
    have hgN : g⁻¹ ∈ Subgroup.normalizer ((cx d : Subgroup G) : Set G) :=
      y9x_mem_normalizer_cx hg'
    have hcomp : GLAPComponent p (cx d) (GLBConj g⁻¹ K) := by
      have h := glaPComponent_gLBConj hKcomp g⁻¹
      rwa [gLBConj_eq_of_mem_normalizer hgN] at h
    apply hcompN _ hcomp
    rw [mem_gLBConj]
    have h2 : g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k := by group
    rw [h2]
    exact hk
  have hcomm_N : ∀ s ∈ S₀, ∀ j ∈ J, ⁅s, j⁆ ∈ Subgroup.normalizer (K : Set G) := by
    intro s hs j hj
    rw [commutatorElement_def]
    exact (Subgroup.normalizer (K : Set G)).mul_mem (hconjN s (hS₀ hs) j (hJK hj))
      (Subgroup.le_normalizer (K.inv_mem (hJK hj)))
  have hSN : S₀ ≤ Subgroup.normalizer (K : Set G) := by
    have h := Subgroup.commutator_le.2 hcomm_N
    rwa [hS₀J] at h
  have hcomm_K : ∀ s ∈ S₀, ∀ j ∈ J, ⁅s, j⁆ ∈ K := by
    intro s hs j hj
    rw [commutatorElement_def]
    have h1 : s * j * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hSN hs) j).1 (hJK hj)
    exact K.mul_mem h1 (K.inv_mem (hJK hj))
  have hfin : ⁅S₀, J⁆ ≤ K := Subgroup.commutator_le.2 hcomm_K
  rwa [hS₀J] at hfin

theorem K_single (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b)
    {y d : G} {J S₀ : Subgroup G} (hyB : y ∈ B ⊓ L) (hy1 : y ≠ 1) (hd : d ∈ Dgrp x y) (hd1 : d ≠ 1)
    (hJlay : J = GLAPLayer p (L ⊓ cx y)) (hJ : GLAPComponent p (L ⊓ cx y) J)
    (hJU : catalogIs (PSimple 3 J) S9.isU3eight)
    (hS₀ : S₀ ≤ cx d) (hS₀J : (⁅S₀, J⁆ : Subgroup G) = S₀) (hS₀2 : IsPGroup 2 S₀) :
    GLAPComponent p (cx d) (closureIn J (GLAPLayer p (cx d))) ∧
      B ≤ Subgroup.normalizer ((closureIn J (GLAPLayer p (cx d)) : Subgroup G) : Set G) ∧
      GLAPComponent p (closureIn J (GLAPLayer p (cx d)) ⊓ cs (Dgrp x y)) J ∧
      S₀ ≤ closureIn J (GLAPLayer p (cx d)) ∧
      ∃ x' ∈ Dgrp x y, x' ∉ Subgroup.zpowers d ∧
        GLAPComponent p (closureIn J (GLAPLayer p (cx d)) ⊓ cx x') J := by
  obtain ⟨hKcomp, hKB⟩ := K_single_comp hc hin h hU hyB hy1 hd hd1 hJlay hJ hJU
  obtain ⟨hcen, hx'⟩ := K_single_cen hc h hU hyB hy1 hd hd1 hJlay hJ hKcomp
  exact ⟨hKcomp, hKB, hcen, S0_le_K hc hd1 hKcomp hS₀ hS₀J hS₀2, hx'⟩

private theorem lemma103_prime_eq_two_of_card_eight (q : TauCeti.PrimePower) (h : q.card = 8) :
    q.p = 2 := by
  have hdvd : q.p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  rw [h] at hdvd
  have h2 : q.p ∣ 2 := q.prime_p.dvd_of_dvd_pow (n := 3) (by norm_num; exact hdvd)
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h2

private theorem lemma103_chev2_of_isU3eight {S : Type} [Group S] (h : catalogIs S S9.isU3eight) :
    IsChevSimple 2 S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  refine Or.inl ⟨i, ?_, ⟨e⟩⟩
  cases i with
  | cyclic p hp => simp [S9.isU3eight, onLie] at hi
  | alternating n hn => simp [S9.isU3eight, onLie] at hi
  | sporadic s => simp [S9.isU3eight, onLie] at hi
  | lie j =>
    obtain ⟨d, hv⟩ := j
    simp only [S9.isU3eight, onLie] at hi
    simp only [onLie]
    change d.characteristic = 2
    split at hi
    · rename_i q
      rw [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact lemma103_prime_eq_two_of_card_eight q hi
    · exact absurd hi id

private theorem lemma103_B_normalizes_inf {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hBel : IsElemAbelian p B) {y : G} (hyB : y ∈ B) :
    B ≤ Subgroup.normalizer ((L ⊓ cx y : Subgroup G) : Set G) := by
  intro u hu
  have hcomm' : Commute u y := isElemAbelian_commute hBel hu hyB
  have key : ∀ v ∈ B, Commute v y → ∀ l ∈ L ⊓ cx y, v * l * v⁻¹ ∈ L ⊓ cx y := by
    intro v hv hvy l hl
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (sstar_norm h.star hv) l).1 hl.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((hvy.mul_left (Subgroup.mem_centralizer_singleton_iff.1 hl.2)).mul_left hvy.inv_left)
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    exact key u hu hcomm' l hl
  · intro hl
    have h1 := key u⁻¹ (B.inv_mem hu) hcomm'.inv_left _ hl
    have e : u⁻¹ * (u * l * u⁻¹) * u⁻¹⁻¹ = l := by group
    rw [e] at h1
    exact h1

theorem BdK_isS0 (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b) (hd5 : dLevel G p = 5)
    {y d : G} {J S₀ E₀ : Subgroup G} (hyB : y ∈ B ⊓ L) (hy1 : y ≠ 1) (hd : d ∈ Dgrp x y) (hd1 : d ≠ 1)
    (hE₀ : E₀ ≤ B ⊓ L ∧ IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2 ∧ y ∈ E₀)
    (hJlay : J = GLAPLayer p (L ⊓ cx y)) (hJ : GLAPComponent p (L ⊓ cx y) J)
    (hJU : catalogIs (PSimple 3 J) S9.isU3eight)
    (hJE : GLAPLayer p (J ⊓ cs E₀) ≠ ⊥) (hS₀ : S₀ ≤ cx d) (hS₀J : (⁅S₀, J⁆ : Subgroup G) = S₀)
    (hS₀2 : IsPGroup 2 S₀) (hS₀1 : S₀ ≠ ⊥) (hS₀B : B ≤ Subgroup.normalizer (S₀ : Set G))
    (hKcomp : GLAPComponent p (cx d) (closureIn J (GLAPLayer p (cx d))))
    (hKB : B ≤ Subgroup.normalizer ((closureIn J (GLAPLayer p (cx d)) : Subgroup G) : Set G))
    (hS₀K : S₀ ≤ closureIn J (GLAPLayer p (cx d)))
    (hJK : GLAPComponent p (closureIn J (GLAPLayer p (cx d)) ⊓ cs (Dgrp x y)) J) :
    IsS0 p B d (closureIn J (GLAPLayer p (cx d))) := by
  have hp3 : p = 3 := hU.p3
  subst hp3
  have hp : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set K := closureIn J (GLAPLayer 3 (cx d)) with hKdef
  have hT := sstar_triple h.star
  have hBel : IsElemAbelian 3 B := hT.1.1
  have hxB : x ∈ B := hT.2.1.1
  have hx1 : x ≠ 1 := hT.2.1.2.1
  have hLc : GLAPComponent 3 (cx x) L := hT.2.2
  have hLx : L ≤ cx x := hLc.1
  have hq : CFSG.Open.IsQuasisimple ↥L := (hc.stage9.1 B x L h.star).1
  have hsL : IsSimpleGroup ↥L := isSimple_of_isU4eight hU.L_iso
  have hchevL : IsChevSimple 2 (PSimple 3 L) := sstar_chev2 hc h.star
  have hyB' : y ∈ B := hyB.1
  have hyL : y ∈ L := hyB.2
  have hbB : b ∈ B := h.mem
  have hxp : x ^ 3 = 1 := hBel.2 x hxB
  have hyp : y ^ 3 = 1 := hBel.2 y hyB'
  have hbp : b ^ 3 = 1 := hBel.2 b hbB
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := sstar_norm h.star hbB
  have hzL : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.1 (hLx hl))
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hyx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyx
    have hzc : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hgx : Commute (g : G) x := Subgroup.mem_centralizer_singleton_iff.1 (hLx g.2)
      have hgy : Commute (g : G) y := hk ▸ hgx.zpow_right k
      exact hgy.eq
    rw [y9x_center_bot hq hsL] at hzc
    exact hy1 (congrArg Subtype.val (Subgroup.mem_bot.1 hzc))
  obtain ⟨hD0B, -, -⟩ := card_Dgrp hBel hp hyB' hxB hx1 hyx
  have hcomm : Dgrp x y = Dgrp y x := by
    show Subgroup.closure {x, y} = Subgroup.closure {y, x}
    rw [Set.pair_comm]
  have hD0B' : Dgrp x y ≤ B := by rw [hcomm]; exact hD0B
  have hdB : d ∈ B := hD0B' hd
  have hxD : x ∈ Dgrp x y := Subgroup.subset_closure (Set.mem_insert x _)
  have hE₀B : E₀ ≤ B := hE₀.1.trans inf_le_left
  have hE₀L : E₀ ≤ L := hE₀.1.trans inf_le_right
  have hE₀el : IsElemAbelian 3 E₀ := hE₀.2.1
  have hE₀card : Nat.card E₀ = 3 ^ 2 := hE₀.2.2.1
  have hyE₀ : y ∈ E₀ := hE₀.2.2.2
  have hJ1 : J ≤ L ⊓ cx y := hJ.1
  have hBA : B ≤ Subgroup.normalizer ((L ⊓ cx y : Subgroup G) : Set G) :=
    lemma103_B_normalizes_inf h hBel hyB'
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := by
    intro u hu
    rw [hJlay]
    exact mem_normalizer_glaPLayer (hBA hu)
  have hchevJ : IsChevSimple 2 (PSimple 3 J) := lemma103_chev2_of_isU3eight hJU
  have hbyL : b ∉ Subgroup.zpowers y := by
    intro hbz
    have hbL : b ∈ L := (Subgroup.zpowers_le.2 hyL) hbz
    have hInn : InducesInnerMod 3 L b :=
      ⟨b, hbL, fun z _ => by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
    have h1 := hin.aut.inner_innDiag (cx x) L b hLc hchevL hbN hInn
    have h2 := hin.aut.field_nonInnDiag (cx x) L b hLc hchevL hU.field
    exact h2.2 h1
  have hyDiag : InnDiagOn 3 (Subgroup.zpowers y) L :=
    hin.aut.inner_innDiag (cx x) L y hLc hchevL hyN
      ⟨y, hyL, fun z _ => by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  have hcopO : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 L)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp L
  have hLO : ¬ L ≤ GLAPPrimeCoreOf 3 L := by
    intro hLO
    have h1 : Nat.card E₀ ∣ Nat.card L := Subgroup.card_dvd_of_le hE₀L
    have h2 : Nat.card L ∣ Nat.card (GLAPPrimeCoreOf 3 L) := Subgroup.card_dvd_of_le hLO
    have h3 : 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L) := by
      have h9 : 3 ∣ Nat.card E₀ := by rw [hE₀card]; exact dvd_pow_self 3 two_ne_zero
      exact h9.trans (h1.trans h2)
    exact ((Nat.Prime.coprime_iff_not_dvd hp).1 hcopO) h3
  have hnotCM : ¬ CentMod 3 L y := by
    intro hC
    have hcenter : ∀ g ∈ L, ⁅g, y⁆ ∈ GLAPPrimeCoreOf 3 L := fun g hg =>
      (mem_centModSubgroup.1 (centMod_iff.1 hC)).2 g hg
    have hON : L ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) :=
      le_normalizer_glaPPrimeCoreOf 3 L
    have hcenO := y9x_inf_central hq hLO hON
    have hcomm_all : ∀ g ∈ L, g * y = y * g := by
      intro g hg
      have hzL' : ⁅g, y⁆ ∈ L := by
        rw [commutatorElement_def]
        exact L.mul_mem (L.mul_mem (L.mul_mem hg hyL) (L.inv_mem hg)) (L.inv_mem hyL)
      have hz : ⁅g, y⁆ ∈ L ⊓ GLAPPrimeCoreOf 3 L := Subgroup.mem_inf.2 ⟨hzL', hcenter g hg⟩
      have hzc : (⟨⁅g, y⁆, hz.1⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        exact hcenO _ hz k k.2
      rw [y9x_center_bot hq hsL] at hzc
      have h1 : ⁅g, y⁆ = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hzc)
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    have hyc : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact hcomm_all g g.2
    rw [y9x_center_bot hq hsL] at hyc
    exact hy1 (congrArg Subtype.val (Subgroup.mem_bot.1 hyc))
  have hJ' : GLAPComponent 3 (closureIn L (Subgroup.zpowers y) ⊓ Subgroup.centralizer ({y} : Set G)) J := by
    have hcl : closureIn L (Subgroup.zpowers y) = L :=
      le_antisymm (lemma103_closureIn_le_of_normalizer (Subgroup.zpowers_le.2 hyN) le_rfl)
        (le_closureIn_self L _)
    rw [hcl]
    exact hJ
  have hXk : CFSG.Open.IsKGroup ↥(cx x) :=
    isKGroup_of_isKProper hc.ctx.kProper
      (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1)
  have hI := hin.lemma102.i155 hp hc.ctx.odd (cx x) L y b hXk hLc hchevL (hLx hyL) hyp hbp
    (isElemAbelian_commute hBel hyB' hbB) hbyL hbN (fun _ => ⟨hyDiag, hU.field⟩) J hJ'
    (hBJ hbB)
  have hnid : NonInnDiag 3 b J := by
    rcases hI with h1 | h2
    · exact h1.1
    · exact absurd ⟨hyN, hnotCM⟩ h2.1
  have hAM : L ⊓ cx y ≤ (L ⊓ cx y) ⊔ B := le_sup_left
  have hMN : (L ⊓ cx y) ⊔ B ≤ Subgroup.normalizer ((L ⊓ cx y : Subgroup G) : Set G) :=
    sup_le (fun g hg => Subgroup.le_normalizer hg) hBA
  have hsnA : IsSubnormal (L ⊓ cx y) ((L ⊓ cx y) ⊔ B) :=
    IsSubnormal.step le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hMN)
      (IsSubnormal.refl _)
  have hJM : J ≤ (L ⊓ cx y) ⊔ B := hJ1.trans le_sup_left
  have hsnJ : IsSubnormal J ((L ⊓ cx y) ⊔ B) := isSubnormal_trans' hJ.2.1 hsnA
  have hKq : CFSG.Open.IsQuasisimple ↥(barX 3 ((L ⊓ cx y) ⊔ B) J) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX hp hJM hsnJ) (isQuasisimple_pQuot_of_glaPComponent hp hJ)
  have hBJcomm : (⁅B, J⁆ : Subgroup G) = J := by
    refine commutator_eq_of_glaPComponent hp hAM hJ le_sup_right hBJ hKq ?_
    intro hle
    have hkey : ∀ c ∈ B, ∀ k ∈ J, (k * c)⁻¹ * (c * k) ∈ GLAPPrimeCoreOf 3 J := by
      intro c hc' k hk
      have hcM : c ∈ (L ⊓ cx y) ⊔ B := Subgroup.mem_sup_right hc'
      have hkM : k ∈ (L ⊓ cx y) ⊔ B := hJM hk
      have hx : (QuotientGroup.mk (⟨c, hcM⟩ : ↥((L ⊓ cx y) ⊔ B)) :
          ↥((L ⊓ cx y) ⊔ B) ⧸ GLAPPrimeCore 3 ↥((L ⊓ cx y) ⊔ B)) ∈ barX 3 ((L ⊓ cx y) ⊔ B) B :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hc')
      have hy : (QuotientGroup.mk (⟨k, hkM⟩ : ↥((L ⊓ cx y) ⊔ B)) :
          ↥((L ⊓ cx y) ⊔ B) ⧸ GLAPPrimeCore 3 ↥((L ⊓ cx y) ⊔ B)) ∈ barX 3 ((L ⊓ cx y) ⊔ B) J :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hk)
      have hcomm' := Subgroup.mem_centralizer_iff.1 (hle hx) _ hy
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm'
      have hG : (k * c)⁻¹ * (c * k) ∈ GLAPPrimeCoreOf 3 ((L ⊓ cx y) ⊔ B) :=
        Subgroup.mem_map_of_mem _ hcomm'
      have hI' : (k * c)⁻¹ * (c * k) ∈ J := by
        have e : (k * c)⁻¹ * (c * k) = (c⁻¹ * k⁻¹ * c⁻¹⁻¹) * k := by group
        rw [e]
        exact J.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBJ (B.inv_mem hc')) k⁻¹).1
          (J.inv_mem hk)) hk
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnJ]
      exact ⟨hI', hG⟩
    have hcomm_k : ∀ k ∈ J, ⁅k, b⁆ ∈ GLAPPrimeCoreOf 3 J := by
      intro k hk
      have h1 := hkey b⁻¹ (B.inv_mem hbB) k⁻¹ (J.inv_mem hk)
      have e : ⁅k, b⁆ = ((k⁻¹ * b⁻¹)⁻¹ * (b⁻¹ * k⁻¹))⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact (GLAPPrimeCoreOf 3 J).inv_mem h1
    have hcentb : CentMod 3 J b := centMod_iff.2 (mem_centModSubgroup.2 ⟨hBJ hbB, hcomm_k⟩)
    exact hnid.2 (hin.aut.inner_innDiag (L ⊓ cx y) J b hJ hchevJ (hBJ hbB)
      (inducesInnerMod_of_centMod hcentb))
  have hSB : (⁅S₀, B⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    have h1 : (⁅⁅B, S₀⁆, J⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_comm B S₀, hbot, Subgroup.commutator_bot_left]
    have h2 : (⁅⁅S₀, J⁆, B⁆ : Subgroup G) = ⊥ := by
      rw [hS₀J, hbot]
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [Subgroup.commutator_comm J B, hBJcomm] at h3
    apply hS₀1
    rw [← hS₀J, Subgroup.commutator_comm S₀ J, h3]
  have hJperf : (⁅J, J⁆ : Subgroup G) = J := glaPComponent_perfect hJ
  have hcomm_mem : ∀ j ∈ J, ∀ s ∈ S₀, j * s * j⁻¹ ∈ S₀ := by
    intro j hj s hs
    have hmem : ⁅j, s⁆ ∈ S₀ := by
      have h1 : ⁅j, s⁆ ∈ (⁅J, S₀⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hj hs
      rwa [Subgroup.commutator_comm, hS₀J] at h1
    have e : j * s * j⁻¹ = ⁅j, s⁆ * s := by
      rw [commutatorElement_def]; group
    rw [e]
    exact S₀.mul_mem hmem hs
  have hJN : J ≤ Subgroup.normalizer (S₀ : Set G) := fun j hj =>
    Subgroup.mem_normalizer_iff.2 fun s => ⟨fun hs => hcomm_mem j hj s hs, fun hs => by
      have h1 := hcomm_mem j⁻¹ (J.inv_mem hj) _ hs
      have e : j⁻¹ * (j * s * j⁻¹) * j⁻¹⁻¹ = s := by group
      rwa [e] at h1⟩
  have hS0Q8 : IsEmpty (S₀ ≃* QuaternionGroup 2) := by
    refine ⟨fun e => ?_⟩
    have h24 : Nat.card (MulAut ↥S₀) = 24 :=
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.natCard_mulAut_of_quaternion e
    haveI : Finite (MulAut ↥S₀) := Nat.finite_of_card_ne_zero (by rw [h24]; norm_num)
    haveI : Fintype (MulAut ↥S₀) := Fintype.ofFinite _
    haveI hsolv : Group.IsSolvable (MulAut ↥S₀) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) (a := 3) (b := 1)
        (by rw [← Nat.card_eq_fintype_card, h24]; norm_num)
    let φ : ↥J →* MulAut ↥S₀ := (Subgroup.normalizerMonoidHom S₀).comp (Subgroup.inclusion hJN)
    haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJperf
    have hφ : φ = 1 := CFSG.Holt.General.eq_one_of_isPerfect_of_isSolvable_range φ inferInstance
    have hcent : J ≤ Subgroup.centralizer ((S₀ : Subgroup G) : Set G) := by
      intro i hi
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have h1 : φ ⟨i, hi⟩ = 1 := by rw [hφ]; rfl
      have h2 := congrArg (fun α : MulAut ↥S₀ => ((α ⟨s, hs⟩ : ↥S₀) : G)) h1
      have e1 : ((φ ⟨i, hi⟩ ⟨s, hs⟩ : ↥S₀) : G) = i * s * i⁻¹ := rfl
      simp only [MulAut.one_apply] at h2
      rw [e1] at h2
      calc s * i = (i * s * i⁻¹) * i := by rw [h2]
        _ = i * s := by group
    have hbot : (⁅S₀, J⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
    exact hS₀1 (by rw [← hS₀J, hbot])
  have hess : IsEssential 3 B d := by
    unfold IsEssential
    exact ⟨hdB, hd1, S₀, hS₀, hS₀2, hS₀B, hSB, fun _ => hS0Q8⟩
  have hTriple : IsSTriple 3 B d K := ⟨hT.1, hess, hKcomp⟩
  have hKB' : closureIn K B = K :=
    le_antisymm (lemma103_closureIn_le_of_normalizer hKB le_rfl) (le_closureIn_self K B)
  have hxE : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 hxB
  have hEB : E₀ ⊔ Subgroup.zpowers x ≤ B := sup_le hE₀B hxE
  have hxC : x ∈ Subgroup.centralizer (E₀ : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun e he =>
      Subgroup.mem_centralizer_singleton_iff.1 (hLx (hE₀L he))
  have hzC : Subgroup.zpowers x ≤ Subgroup.centralizer (E₀ : Set G) := Subgroup.zpowers_le.2 hxC
  have hxel : IsElemAbelian 3 (Subgroup.zpowers x) := isElemAbelian_zpowers hxp
  have hE₀C : E₀ ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    fun e he => Subgroup.mem_centralizer_iff.2 fun z hz =>
      ((Subgroup.mem_centralizer_iff.1 (hzC hz)) e he).symm
  have hEel : IsElemAbelian 3 (E₀ ⊔ Subgroup.zpowers x) :=
    isElemAbelian_sup_of_commute hE₀el hxel hE₀C
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (E₀ : Set G) :=
    hzC.trans (Subgroup.centralizer_le_normalizer _)
  have hcard1 := card_sup_mul_card_inf_of_le_normalizer hzN
  have hinf : E₀ ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgE, hgx⟩ := Subgroup.mem_inf.1 hg
    have hgC : g ∈ Subgroup.centralizer (L : Set G) := hzL hgx
    have hgz : (⟨g, hE₀L hgE⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hgC k k.2
    rw [y9x_center_bot hq hsL] at hgz
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 hgz))
  have hEcard : Nat.card ↥(E₀ ⊔ Subgroup.zpowers x) = 3 ^ 3 := by
    rw [hinf, Subgroup.card_bot, mul_one, hE₀card, Nat.card_zpowers, orderOf_eq_prime hxp hx1]
      at hcard1
    rw [hcard1]
    norm_num
  have hEK : (K ⊓ cs (Dgrp x y)) ⊓ cs E₀ = K ⊓ cs (E₀ ⊔ Subgroup.zpowers x) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hg1, hgE₀⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨hgK, hgD⟩ := Subgroup.mem_inf.1 hg1
      have hgx : x * g = g * x := Subgroup.mem_centralizer_iff.1 hgD x hxD
      have hEg : E₀ ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({g} : Set G) :=
        sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 hgE₀ e he))
          (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hgx))
      exact Subgroup.mem_inf.2 ⟨hgK, Subgroup.mem_centralizer_iff.2 fun e he =>
        Subgroup.mem_centralizer_singleton_iff.1 (hEg he)⟩
    · intro g hg
      obtain ⟨hgK, hgE⟩ := Subgroup.mem_inf.1 hg
      have hD0E : Dgrp x y ≤ E₀ ⊔ Subgroup.zpowers x := by
        refine (Subgroup.closure_le _).2 ?_
        intro z hz
        rcases hz with hz | hz
        · rw [hz]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]; exact Subgroup.mem_sup_left hyE₀
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgK,
        Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hD0E) hgE⟩,
        Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hgE⟩
  have hsub : IsSubnormal (J ⊓ cs E₀) (K ⊓ cs (E₀ ⊔ Subgroup.zpowers x)) := by
    have h1 := isSubnormal_inf hJK.2.1 (cs E₀)
    rwa [hEK] at h1
  have hlayer : GLAPLayer 3 (K ⊓ cs (E₀ ⊔ Subgroup.zpowers x)) ≠ ⊥ := by
    obtain ⟨M, hMc, hM1⟩ : ∃ M : Subgroup G, GLAPComponent 3 (J ⊓ cs E₀) M ∧ M ≠ ⊥ := by
      by_contra hcon
      simp only [not_exists, not_and, ne_eq, not_not] at hcon
      apply hJE
      exact le_bot_iff.1 (sSup_le fun M hM => (hcon M hM).le)
    have hMK : GLAPComponent 3 (K ⊓ cs (E₀ ⊔ Subgroup.zpowers x)) M :=
      glaPComponent_of_isSubnormal' hp hsub hMc
    have hML : M ≤ GLAPLayer 3 (K ⊓ cs (E₀ ⊔ Subgroup.zpowers x)) := le_sSup hMK
    intro h0
    rw [h0] at hML
    exact hM1 (le_bot_iff.1 hML)
  have hGS : IsGStar 3 B K := by
    unfold IsGStar
    refine ⟨E₀ ⊔ Subgroup.zpowers x, hEB, hEel, hEcard, ?_⟩
    rw [hKB']
    exact hlayer
  have hTL : tripleLevel 3 B K = 5 := by
    rw [tripleLevel, if_pos hGS]
  unfold IsS0
  exact ⟨hTriple, hTL.trans hd5.symm⟩

theorem BdK_notcore (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {d : G}
    {J S₀ : Subgroup G} (hd5 : dLevel G p = 5) (hd1 : d ≠ 1)
    (hS₀J : (⁅S₀, J⁆ : Subgroup G) = S₀) (hS₀2 : IsPGroup 2 S₀) (hS₀1 : S₀ ≠ ⊥)
    (hS₀K : S₀ ≤ closureIn J (GLAPLayer p (cx d)))
    (hKcomp : GLAPComponent p (cx d) (closureIn J (GLAPLayer p (cx d))))
    (hJK : J ≤ closureIn J (GLAPLayer p (cx d)))
    (hS0 : IsS0 p B d (closureIn J (GLAPLayer p (cx d)))) :
    ¬ S₀ ≤ GLAPPrimeCoreOf p (closureIn J (GLAPLayer p (cx d))) := by
  classical
  intro hle
  set K := closureIn J (GLAPLayer p (cx d)) with hKdef
  have hp := hc.ctx.prime
  have hOK : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p (cx d) := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hKcomp.2.1]
    exact inf_le_right
  have hS0O : S₀ ≤ GLAPPrimeCoreOf p (cx d) := hle.trans hOK
  have hGs : IsGStar p B K := isGStar_of_dLevel_eq_five hS0 hd5
  have hdB : d ∈ B := hS0.1.2.1.1
  have hodd := hc.stage4.2.1 B d K hS0.1.1 hdB hd1 hKcomp hGs
  have hsub : S₀ ≤ ⁅closureIn K B, GLAPPrimeCoreOf p (cx d)⁆ := by
    calc S₀ = ⁅S₀, J⁆ := hS₀J.symm
      _ ≤ ⁅GLAPPrimeCoreOf p (cx d), K⁆ := Subgroup.commutator_mono hS0O hJK
      _ = ⁅K, GLAPPrimeCoreOf p (cx d)⁆ := Subgroup.commutator_comm _ _
      _ ≤ ⁅closureIn K B, GLAPPrimeCoreOf p (cx d)⁆ :=
          Subgroup.commutator_mono (le_closureIn_self K B) le_rfl
  have hdvd : Nat.card S₀ ∣ Nat.card (⁅closureIn K B, GLAPPrimeCoreOf p (cx d)⁆ : Subgroup G) :=
    Subgroup.card_dvd_of_le hsub
  have hoddS : Odd (Nat.card S₀) := Odd.of_dvd_nat hodd hdvd
  obtain ⟨k, hk⟩ := hS₀2.exists_card_eq
  rw [hk] at hoddS
  have hk0 : k = 0 := by
    rcases k with _ | k
    · rfl
    · exact absurd hoddS (Nat.not_odd_iff_even.2
        (even_iff_two_dvd.2 (dvd_pow_self 2 (Nat.succ_ne_zero k))))
  exact hS₀1 (Subgroup.card_eq_one.1 (by rw [hk, hk0, pow_zero]))

theorem BdK_S0 (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b) (hd5 : dLevel G p = 5)
    {y d : G} {J S₀ E₀ : Subgroup G} (hyB : y ∈ B ⊓ L) (hy1 : y ≠ 1) (hd : d ∈ Dgrp x y) (hd1 : d ≠ 1)
    (hE₀ : E₀ ≤ B ⊓ L ∧ IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2 ∧ y ∈ E₀)
    (hJlay : J = GLAPLayer p (L ⊓ cx y)) (hJ : GLAPComponent p (L ⊓ cx y) J)
    (hJU : catalogIs (PSimple 3 J) S9.isU3eight)
    (hJE : GLAPLayer p (J ⊓ cs E₀) ≠ ⊥) (hS₀ : S₀ ≤ cx d) (hS₀J : (⁅S₀, J⁆ : Subgroup G) = S₀)
    (hS₀2 : IsPGroup 2 S₀) (hS₀1 : S₀ ≠ ⊥) (hS₀B : B ≤ Subgroup.normalizer (S₀ : Set G))
    (hKcomp : GLAPComponent p (cx d) (closureIn J (GLAPLayer p (cx d))))
    (hKB : B ≤ Subgroup.normalizer ((closureIn J (GLAPLayer p (cx d)) : Subgroup G) : Set G))
    (hS₀K : S₀ ≤ closureIn J (GLAPLayer p (cx d)))
    (hJK : GLAPComponent p (closureIn J (GLAPLayer p (cx d)) ⊓ cs (Dgrp x y)) J) :
    IsS0 p B d (closureIn J (GLAPLayer p (cx d))) ∧
      ¬ S₀ ≤ GLAPPrimeCoreOf p (closureIn J (GLAPLayer p (cx d))) := by
  have hS0 := BdK_isS0 hc hin h hU hd5 hyB hy1 hd hd1 hE₀ hJlay hJ hJU hJE hS₀ hS₀J hS₀2 hS₀1 hS₀B hKcomp hKB
    hS₀K hJK
  exact ⟨hS0, BdK_notcore hc hin hd5 hd1 hS₀J hS₀2 hS₀1 hS₀K hKcomp (le_closureIn_self _ _) hS0⟩

theorem r2_BdK_gt (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b)
    {y d : G} {J S₀ : Subgroup G} (hd : d ∈ Dgrp x y) (hd1 : d ≠ 1) (hyB : y ∈ B ⊓ L) (hy1 : y ≠ 1)
    (hJ : GLAPComponent p (L ⊓ cx y) J) (hJU : catalogIs (PSimple 3 J) S9.isU3eight)
    (hS₀ : S₀ ≤ cx d) (hS₀J : (⁅S₀, J⁆ : Subgroup G) = S₀) (hS₀2 : IsPGroup 2 S₀)
    (hS₀O : ¬ S₀ ≤ GLAPPrimeCoreOf p (closureIn J (GLAPLayer p (cx d))))
    (hKcomp : GLAPComponent p (cx d) (closureIn J (GLAPLayer p (cx d))))
    (hKB : B ≤ Subgroup.normalizer ((closureIn J (GLAPLayer p (cx d)) : Subgroup G) : Set G))
    (hS₀K : S₀ ≤ closureIn J (GLAPLayer p (cx d)))
    (hKx' : ∃ x' ∈ Dgrp x y, x' ∉ Subgroup.zpowers d ∧
      GLAPComponent p (closureIn J (GLAPLayer p (cx d)) ⊓ cx x') J) :
    2 ^ 6 < r2 p B (closureIn J (GLAPLayer p (cx d))) := by
  have hp3 := hU.p3
  subst hp3
  set K := closureIn J (GLAPLayer 3 (cx d)) with hKdef
  have hBel : IsElemAbelian 3 B := (sstar_triple h.star).1.1
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hyB' : y ∈ B := hyB.1
  have hDB : Dgrp x y ≤ B := by
    show Subgroup.closure ({x, y} : Set G) ≤ B
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxB
    · exact hyB'
  obtain ⟨x', hx'D, hx'd, hJ'⟩ := hKx'
  have hx'B : x' ∈ B := hDB hx'D
  have hdB : d ∈ B := hDB hd
  have hx'c : x' ∈ cx d :=
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hx'B hdB)
  have hx'3 : x' ^ 3 = 1 := hBel.2 x' hx'B
  have hx'N : x' ∈ Subgroup.normalizer (K : Set G) := hKB hx'B
  obtain ⟨hch, hnotTD, hM⟩ :=
    hin.i2018 d x' K J S₀ hKcomp
      (isKGroup_of_isKProper hc.ctx.kProper (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hd1))
      hx'c hx'3 hx'd hJ' hJU hS₀K hS₀2 hS₀J hS₀O hx'N
  have hsplit := lemma103_marking_or (P := fun lab _ _ _ _ _ => lab.n = 1 ∧ 2 ^ 6 < card2 3 K)
    (P' := fun lab _ _ _ _ _ => lab.n = 3 ∧ 2 ^ 18 < card2 3 K) hM
  unfold r2
  split_ifs with hR hF
  · exact absurd hR.2.1 hnotTD
  · have hb₁ := hF.choose_spec
    have hpow : centCard2 3 K hF.choose ^ 3 = card2 3 K :=
      hin.i91part (cx d) K hF.choose hKcomp hch (hBel.2 _ hb₁.1) hb₁.2
    rcases hsplit with hA | hB3
    · exfalso
      exact (hin.field_n Nat.prime_three (by norm_num) (cx d) K hF.choose hKcomp hb₁.2).2.1
        (lemma103_marking_mono (fun _ _ _ _ _ _ h => h.1) hA)
    · obtain ⟨labW, RW, instW, IW, FW, θW, hP⟩ := lemma103_marking_witness hB3
      have hgt : 2 ^ 18 < card2 3 K := hP.2
      by_contra hle
      push Not at hle
      have h1 : centCard2 3 K hF.choose ^ 3 ≤ (2 ^ 6) ^ 3 := Nat.pow_le_pow_left hle 3
      have h2 : card2 3 K ≤ 2 ^ 18 := by
        rw [← hpow]
        calc centCard2 3 K hF.choose ^ 3 ≤ (2 ^ 6) ^ 3 := h1
          _ = 2 ^ 18 := by norm_num
      exact absurd hgt (not_lt.2 h2)
  · rcases hsplit with hA | hB3
    · obtain ⟨labW, RW, instW, IW, FW, θW, hP⟩ := lemma103_marking_witness hA
      exact hP.2
    · obtain ⟨labW, RW, instW, IW, FW, θW, hP⟩ := lemma103_marking_witness hB3
      exact lt_trans (by norm_num) hP.2

theorem exists_sstar_above (hc : S10Ctx G p) {B : Subgroup G} {a : G} {J : Subgroup G}
    (h0 : IsS0 p B a J)
    (hT : ∃ T : Subgroup G, T ≤ J ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p (cx a)) :
    ∃ (B' : Subgroup G) (x' : G) (L' : Subgroup G), IsSStarMax p B' x' L' ∧
      PumpLe p (B, a, J) (B', x', L') := by
  obtain ⟨B', x', L', hmax, hpump⟩ := hc.stage4o.2.2.1 B a J h0
  refine ⟨B', x', L', ⟨hmax, ?_⟩, hpump⟩
  have hn : ¬ nGen B (closureIn J B) ≤ GLAPPrimeCoreOf p (cx a) := by
    obtain ⟨T, hTJ, hT2, hTB, hTO⟩ := hT
    intro hle
    refine hTO (le_trans ?_ hle)
    exact le_iSup₂_of_le T ⟨hTJ.trans (le_closureIn_self J B), hT2, hTB⟩ le_rfl
  have hn' := hc.stage4o.2.2.2.2.2.1 (B, a, J) (B', x', L') hpump hn
  have hBN' : B' ≤ Subgroup.normalizer (L' : Set G) := hmax.2.2
  have hex : ∃ T : Subgroup G, T ≤ L' ⊔ GLAPPrimeCoreOf p (cx x') ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      B' ≤ Subgroup.normalizer (T : Set G) := by
    by_contra hno
    apply hn'
    unfold nGen
    refine iSup₂_le fun T hT' => ?_
    obtain ⟨hTK, hT2, hTB⟩ := hT'
    by_contra hTO
    exact hno ⟨T, le_sup_of_le_left (by simpa [closureIn_eq_self hBN'] using hTK),
      fun hbot => hTO (hbot ▸ bot_le), hT2, hTB⟩
  exact hc.stage5.2.2 B' x' L' hmax hex

theorem oddCore_U48 (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hU : UCore G p B x L b)
    (hdec : B = Dgrp b x ⊔ (B ⊓ L) ∧ Dgrp b x ⊓ (B ⊓ L) = ⊥ ∧ B ⊓ L ≤ Ipart p L b) :
    Odd (Nat.card (GLAPPrimeCoreOf p (cx x))) := by
  by_contra hodd
  have hev : Even (Nat.card (GLAPPrimeCoreOf p (cx x))) := Nat.not_odd_iff_even.1 hodd
  have hp := hc.ctx.prime
  have hL := (sstar_triple h.star).2.2
  obtain ⟨E₁, hE₁, hE₁a, hE₁c⟩ := E1_of_even hc hin h hU hdec hev
  have hp3 := hU.p3
  have hE₁L : E₁ ≤ L := hE₁.trans inf_le_right
  obtain ⟨y, hyE, hy1, E₀, hE₀E, hE₀a, hE₀c, hyE₀, hJ, hJU, hJE⟩ :=
    hin.i8 (cx x) L E₁ (hp3 ▸ hL) hU.L_iso hE₁L (hp3 ▸ hE₁a) (hp3 ▸ hE₁c)
  have hyBL : y ∈ B ⊓ L := hE₁ hyE
  have hE₀BL : E₀ ≤ B ⊓ L := hE₀E.trans hE₁
  subst hp3
  obtain ⟨d, hd, hd1, S₀, hS2, hS1, hS₀d, hS₀B, hS₀J⟩ :=
    exists_S0 hc h hU hev hyBL hy1 rfl hJ hJU
  obtain ⟨hKcomp, hKB, hKJ, hS₀K, hKx'⟩ :=
    K_single hc hin h hU hyBL hy1 hd hd1 rfl hJ hJU hS₀d hS₀J hS2
  obtain ⟨hS0, hS0O⟩ := BdK_S0 hc hin h hU hd5 hyBL hy1 hd hd1 ⟨hE₀BL, hE₀a, hE₀c, hyE₀⟩ rfl hJ hJU hJE
    hS₀d hS₀J hS2 hS1 hS₀B hKcomp hKB hS₀K hKJ
  have hgt := r2_BdK_gt hc hin h hU hd hd1 hyBL hy1 hJ hJU hS₀d hS₀J hS2 hS0O hKcomp hKB hS₀K hKx'
  have hSO : ¬ S₀ ≤ GLAPPrimeCoreOf 3 (cx d) := fun hle => hS0O (by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hKcomp.2.1]
    exact le_inf hS₀K hle)
  obtain ⟨B', x', L', hstar', hpump⟩ :=
    exists_sstar_above hc hS0 ⟨S₀, hS₀K, hS2, hS₀B, hSO⟩
  have ht2 : IsS2 3 (B', x', L').1 (B', x', L').2.1 (B', x', L').2.2 :=
    ⟨sstar_triple hstar', hc.stage8.1 B' x' L' hstar'⟩
  have hl := (lemma102 hc hin.lemma102 ht2 hpump).2
  have hm := h.maximal B' x' L' hstar'
  rw [h.r2_eq, hU.cent] at hm
  exact absurd (lt_of_lt_of_le hgt (hl.trans hm)) (lt_irrefl _)

theorem rank_eq_four (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : UCore G p B x L b)
    (hdec : B = Dgrp b x ⊔ (B ⊓ L) ∧ Dgrp b x ⊓ (B ⊓ L) = ⊥ ∧ B ⊓ L ≤ Ipart p L b)
    (hT : HasTL p B L) : GLATwoLocalRank 3 G = 4 := by
  have hp := hc.ctx.prime
  have hS := sstar_triple h.star
  have hp3 := hU.p3
  obtain ⟨T, hTL, hT2, hBT, hTO⟩ := hT
  have hBL : IsElemAbelian p (B ⊓ L) := isElemAbelian_mono hS.1.1 inf_le_left
  have h9 : Nat.card (B ⊓ L : Subgroup G) ≤ 3 ^ 2 :=
    hin.i1015 (cx x) L (B ⊓ L) T (hp3 ▸ hS.2.2) hU.L_iso inf_le_right (hp3 ▸ hBL) hTL hT2
      (fun g hg => hBT hg.1) (hp3 ▸ hTO)
  obtain ⟨hDB, hDel, hD9⟩ := card_Dgrp hS.1.1 hp h.mem hS.2.1.1 hS.2.1.2.1 h.not_mem
  have hnorm : B ⊓ L ≤ Subgroup.normalizer ((Dgrp b x : Subgroup G) : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
      isElemAbelian_commute hS.1.1 (hDB hd) hg.1)
  have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [← hdec.1, hdec.2.1, Subgroup.card_bot, mul_one, hS.1.2.1, hD9] at hcard
  subst hp3
  have hle : 3 ^ GLATwoLocalRank 3 G ≤ 3 ^ 2 * 3 ^ 2 := by
    rw [hcard]
    exact Nat.mul_le_mul_left _ h9
  have hm : GLATwoLocalRank 3 G ≤ 4 := by
    by_contra hgt
    push Not at hgt
    have : 3 ^ 5 ≤ 3 ^ GLATwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hgt
    omega
  exact le_antisymm hm hc.ctx.rank_ge

theorem lemma103 (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    dLevel G p = 5 ∧ (CaseA p B x L b ∨ CaseU G p B x L b) := by
  have hd5 := d_eq_five hc hin h
  refine ⟨hd5, ?_⟩
  by_cases hA : CaseA p B x L b
  · exact Or.inl hA
  right
  have hU := ucore hc hin h hd5 hA
  have hdec := B_decomp_U48 hc hin h hU
  have hodd := oddCore_U48 hc hin h hd5 hU hdec
  have hcentral : ∀ T : Subgroup G, T ≤ GLAPPrimeCoreOf p (cx x) → IsPGroup 2 T →
      B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = ⊥ := by
    intro T hTO hT2 hBT
    have hTcard : Nat.card T = 1 := by
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      have hdvd : Nat.card T ∣ Nat.card (GLAPPrimeCoreOf p (cx x)) := Subgroup.card_dvd_of_le hTO
      rw [hk] at hdvd ⊢
      have : ¬ 2 ∣ Nat.card (GLAPPrimeCoreOf p (cx x)) := by
        rw [← even_iff_two_dvd]
        exact Nat.not_even_iff_odd.2 hodd
      rcases k with _ | k
      · simp
      · exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) hdvd) this
    rw [Subgroup.card_eq_one.1 hTcard]
    simp
  have hT := exists_T_in_L hc hin h hcentral
  have hrank := rank_eq_four hc hin h hU hdec hT
  have hS := sstar_triple h.star
  have hp3 := hU.p3
  have hBL : Nat.card (B ⊓ L : Subgroup G) = p ^ 2 := by
    obtain ⟨hDB, -, hD9⟩ := card_Dgrp hS.1.1 hc.ctx.prime h.mem hS.2.1.1 hS.2.1.2.1 h.not_mem
    have hnorm : B ⊓ L ≤ Subgroup.normalizer ((Dgrp b x : Subgroup G) : Set G) := fun g hg =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
        isElemAbelian_commute hS.1.1 (hDB hd) hg.1)
    have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [← hdec.1, hdec.2.1, Subgroup.card_bot, mul_one, hS.1.2.1, hD9] at hcard
    have hrank' : GLATwoLocalRank p G = 4 := by rw [hp3]; exact hrank
    rw [hrank'] at hcard
    have h2 : p ^ 2 * Nat.card (B ⊓ L : Subgroup G) = p ^ 2 * p ^ 2 := by rw [← hcard]; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hc.ctx.prime.pos 2) h2
  exact ⟨hU.p3, hrank, hp3 ▸ centRank_U48 hc hin h hU hdec, hU.L_iso, hU.I_iso,
    ⟨B ⊓ L, hdec.2.2, isElemAbelian_mono hS.1.1 inf_le_left, hBL, hdec.1, hdec.2.1⟩,
    hU.field, hU.I_grp, hU.I_eq, hU.I_core⟩

end S10

end CFSG.LocalAnalysis.GLTheoremA
