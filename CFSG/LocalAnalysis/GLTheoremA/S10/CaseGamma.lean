module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseU
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.InnerPGroup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma105More

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure GammaInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l105 : Lemma105Inputs G p
  u48 : U48CentInvAt G
  u48z : U48CentInvFieldAt G
  i2811t : I2811TAt G
  ys08 : YS08
  labels : LabelDictAt
  i1015four : I1015fourAt G
  substable : StdSubTableAt G
  i171 : I171At G
  u6d0 : U6D0RankAt G
  i14chev : I1431Chev2At G
  i144one : I144oneAt G
  dist : CatDistinctAt
  single_std : I112SingleStdAt G
  norm113 : I113NormAt G
  stdf : StdSubFAt G

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem exists_a_gamma (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) (hU : CaseU G p B x L b)
    (hγ : ¬ ∀ a ∈ Dgrp b x, a ≠ 1 →
      catalogIs (PSimple p (Jpart p (Ipart p L b) a)) (fun i => S9.isU4two i ∨ S9.isU4eight i)) :
    ∃ a ∈ Dgrp b x, a ∉ Subgroup.zpowers x ∧
      ¬ catalogIs (PSimple p (Jpart p (Ipart p L b) a)) (fun i => S9.isU4two i ∨ S9.isU4eight i) := by
  classical
  push Not at hγ
  obtain ⟨a, haD, ha1, hna⟩ := hγ
  refine ⟨a, haD, fun hax => hna ?_, hna⟩
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian p B := B_el h
  obtain ⟨hDB, -, -⟩ := dgrp_facts hc h
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hx3 : x ^ p = 1 := hBel.2 x hxB
  have ha3 : a ^ p = 1 := hBel.2 a (hDB haD)
  have hzeq : Subgroup.zpowers a = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hax)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha3 ha1, orderOf_eq_prime hx3 hx1])
  have hcx : cx a = cx x := by
    have h1 : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
        Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by rw [hzeq]
    rw [S3.centralizer_zpowers a, S3.centralizer_zpowers x] at h1
    exact h1
  have hLc : GLAPComponent p (cx x) L := hS.2.2
  have hIc : GLAPComponent p (L ⊓ cx b) (Ipart p L b) := (Icomp_of_cfg hc hin h).1
  have hIL : Ipart p L b ≤ L := (layer_le p _).trans inf_le_left
  have hJ : Jpart p (Ipart p L b) a = L := by
    show closureIn (Ipart p L b) (GLAPLayer p (cx a)) = L
    rw [hcx]
    exact closureIn_layer_eq_of_component hp hLc hIc hIL
  rw [hJ]
  exact catalogIs_imp (fun i hi => Or.inr hi) (psimple_L_isU48 hc h hU)

private theorem gamma_cs_zpowers_sup (u v : G) :
    cs (Subgroup.zpowers u ⊔ Subgroup.zpowers v) = cx u ⊓ cx v := by
  ext g
  rw [Subgroup.mem_inf]
  change g ∈ Subgroup.centralizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) ↔ _
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    exact ⟨(hg u (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))).symm,
      (hg v (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))).symm⟩
  · rintro ⟨hu, hv⟩ k hk
    have hle : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ cx g :=
      sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hu.symm))
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hv.symm))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)

private theorem casegamma_eq_of_barX_top {p : ℕ} {K J : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥K)
    (hOZ : GLAPPrimeCore p ↥K ≤ Subgroup.center ↥K) (hJK : J ≤ K) (hbar : barX p K J = ⊤) : J = K := by
  classical
  have hdec : ∀ g : ↥K, ∃ j : ↥K, j ∈ J.subgroupOf K ∧ ∃ u : ↥K, u ∈ Subgroup.center ↥K ∧ g = j * u := by
    intro g
    have hle : barX p K K ≤ barX p K J := by rw [barX_self, hbar]
    obtain ⟨j, hjJ, hjz⟩ := exists_of_barX_le hle g.2 g.2
    unfold GLAPPrimeCoreOf at hjz
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hjz
    refine ⟨⟨j, hJK hjJ⟩, Subgroup.mem_subgroupOf.2 hjJ, u, hOZ hu, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [show (u : G) = j⁻¹ * g from hue, mul_inv_cancel_left]
  have hcomm : commutator ↥K ≤ J.subgroupOf K := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    obtain ⟨j₁, hj₁, u₁, hu₁, rfl⟩ := hdec g
    obtain ⟨j₂, hj₂, u₂, hu₂, rfl⟩ := hdec h
    rw [commutatorElement_mul_center_left hu₁, commutatorElement_mul_center_right hu₂,
      commutatorElement_def]
    exact (J.subgroupOf K).mul_mem ((J.subgroupOf K).mul_mem ((J.subgroupOf K).mul_mem hj₁ hj₂)
      ((J.subgroupOf K).inv_mem hj₁)) ((J.subgroupOf K).inv_mem hj₂)
  rw [hq.1, top_le_iff] at hcomm
  apply le_antisymm hJK
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥K) ∈ J.subgroupOf K := by
    rw [hcomm]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 hmem

theorem glaPComponent_of_quasisimple {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hKX : IsSubnormal K X)
    (hq : CFSG.Open.IsQuasisimple ↥K) (hdvd : p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) :
    GLAPComponent p X K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : p ∣ Nat.card ↥K := hdvd.trans (Subgroup.card_quotient_dvd_card _)
  have hOp : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥K) := by
    have h := not_dvd_card_glaPPrimeCoreOf hp K
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
  have hOne : GLAPPrimeCore p ↥K ≠ ⊤ := by
    intro h
    apply hOp
    rw [h, Subgroup.card_top]
    exact hpK
  have hOZ : GLAPPrimeCore p ↥K ≤ Subgroup.center ↥K :=
    le_center_of_normal_of_isQuasisimple hq (GLAPPrimeCore.normal p ↥K) hOne
  have hQ : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore p ↥K) :=
    CFSG.ComponentClassification.Quasisimple.central_quotient hq _ hOZ
  obtain ⟨I, hI, hIbar⟩ := exists_glaPComponent_of_isQuasisimple hQ
  have hIK : I = K := casegamma_eq_of_barX_top hq hOZ hI.1 hIbar
  have hKK : GLAPComponent p K K := hIK ▸ hI
  exact glaPComponent_of_isSubnormal' hp hKX hKK

theorem gamma_single (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G}
    (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a) := by
  classical
  have hp : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian 3 B := B_el h
  obtain ⟨hDB, -, -⟩ := dgrp_facts hc h
  obtain ⟨x', hx'D, hx'a, hDeq⟩ := exists_complement hc h ha ha1
  have hLc : GLAPComponent 3 (cx x) L := hS.2.2
  obtain ⟨hIc, -⟩ := Icomp_of_cfg hc hin.l105 h
  have hcsD : cx a ⊓ cx x' = cx x ⊓ cx b := by
    have h1 : cs (Dgrp b x) = cx b ⊓ cx x := by
      rw [dgrp_eq_sup]; exact gamma_cs_zpowers_sup b x
    have h2 : cs (Dgrp b x) = cx a ⊓ cx x' := by
      rw [hDeq]; exact gamma_cs_zpowers_sup a x'
    rw [← h2, h1, inf_comm]
  have hIcD : GLAPComponent 3 (cx a ⊓ cx x') (Ipart 3 L b) := by
    rw [hcsD]
    exact glaPComponent_of_isSubnormal' hp (isSubnormal_inf hLc.2.1 (cx b)) hIc
  have haB : a ∈ B := hDB ha
  have hx'B : x' ∈ B := hDB hx'D
  have hBa : B ≤ cx a := isElemAbelian_le_centralizer hBel haB
  have hrank : 3 ^ GLATwoLocalRank 3 ↥(cx a) ≤ Nat.card B := by
    rw [hS.1.2.1]
    exact Nat.pow_le_pow_right (by norm_num)
      (glaTwoLocalRank_subgroup_le (by norm_num : 1 < 3) (cx a))
  obtain ⟨K', hK'c, hIK', -⟩ := hin.single_std (cx a) x' B (Ipart 3 L b)
    (S8.isKGroup_cx hc.ctx ha1) hx'B hBa hBel hrank
    (by rw [S3.centralizer_zpowers x']; exact hIcD) (B_le_N_J hc h ha).1
    (catalogIs_imp (fun i hi => Or.inl hi) hU.I_iso)
  show GLAPComponent 3 (cx a) (closureIn (Ipart 3 L b) (GLAPLayer 3 (cx a)))
  rw [closureIn_layer_eq_of_component hp hK'c hIcD hIK']
  exact hK'c

theorem psimple_equiv_of_sup {p : ℕ} (hp : p.Prime) {I J : Subgroup G} (hIJ : I ≤ J)
    (hsup : I ⊔ GLAPPrimeCoreOf p J = J) : Nonempty (PSimple p I ≃* PSimple p J) := by
  obtain ⟨-, ⟨e⟩⟩ := cover_facts hp hIJ hsup
  exact ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

theorem not_isTD4_of_isYs09Type (hd : CatDistinctAt) {J : Subgroup G}
    (h : catalogIs (PSimple 3 J) isYs09Type) : ¬ IsTD4 3 J :=
  fun htd => hd.td4_ys09 _ htd h

theorem split_of_ys09 {lab : GLALabel} (h : Ys09Label lab) : GLASplit 3 lab := by
  have hn : lab.n = 1 := by
    rcases h with ⟨-, -, hn⟩ | ⟨-, -, hn⟩ | ⟨-, -, hn⟩ <;> exact hn
  exact Or.inr (Or.inr (Or.inr ⟨hn, rfl⟩))

theorem gamma_cent_B (hc : S10Ctx G 3) (hin : Lemma105Inputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hsingle : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a))
    (hlt : ¬ (Ipart 3 L b ⊔ GLAPPrimeCoreOf 3 (Jpart 3 (Ipart 3 L b) a) = Jpart 3 (Ipart 3 L b) a)) :
    ∀ c ∈ B, CentMod 3 (Jpart 3 (Ipart 3 L b) a) c ↔ c ∈ Subgroup.zpowers a := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  intro c hcB
  constructor
  · intro hCM
    have hBel : IsElemAbelian 3 B := B_el h
    have hcN : c ∈ Subgroup.normalizer ((Ipart 3 L b : Subgroup G) : Set G) :=
      (B_le_N_J hc h ha).1 hcB
    have hIJ : Ipart 3 L b ≤ Jpart 3 (Ipart 3 L b) a := le_closureIn_self _ _
    have hcentI : CentMod 3 (Ipart 3 L b) c := by
      refine centMod_iff.2 ⟨hcN, fun l hl => ?_⟩
      have h1 : ⁅l, c⁆ ∈ GLAPPrimeCoreOf 3 (Jpart 3 (Ipart 3 L b) a) :=
        (centMod_iff.1 hCM).2 l (hIJ hl)
      have h2 : ⁅l, c⁆ ∈ Ipart 3 L b := by
        have h3 : c * l⁻¹ * c⁻¹ ∈ Ipart 3 L b :=
          (Subgroup.mem_normalizer_iff.1 hcN l⁻¹).1 ((Ipart 3 L b).inv_mem hl)
        rw [commutatorElement_def, show l * c * l⁻¹ * c⁻¹ = l * (c * l⁻¹ * c⁻¹) by group]
        exact (Ipart 3 L b).mul_mem hl h3
      exact inf_le_glaPPrimeCoreOf (p := 3) (hIJ.trans (le_normalizer_glaPPrimeCoreOf 3 _))
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
          (not_dvd_card_glaPPrimeCoreOf hp _))) (Subgroup.mem_inf.2 ⟨h2, h1⟩)
    have hcD : c ∈ Dgrp b x := (h.cent_I c hcB).1 hcentI
    by_contra hcz
    have hPc : IsPGroup 3 (Subgroup.zpowers c) :=
      isPGroup_of_isElemAbelian (isElemAbelian_mono hBel (Subgroup.zpowers_le.2 hcB))
    obtain ⟨-, huniq, -, -, hsup, -⟩ := glaPLayer_inf_centralizer hp hsingle hPc hCM
    have hIc := I_comp_in_J hc hin.l104 h ha ha1 hcD hcz hsingle
    have hIeq : Ipart 3 L b = GLAPLayer 3 (Jpart 3 (Ipart 3 L b) a ⊓ Subgroup.centralizer ({c} : Set G)) :=
      huniq _ hIc
    exact hlt ((congrArg (fun X => X ⊔ GLAPPrimeCoreOf 3 (Jpart 3 (Ipart 3 L b) a)) hIeq).trans hsup)
  · intro hc'
    exact centMod_zpowers_of_le (Jpart_le_cx h ha) hc'

theorem gamma_cent_S (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hq : CFSG.Open.IsQuasisimple ↥(Jpart 3 (Ipart 3 L b) a))
    (hy09 : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) isYs09Type) :
    ∀ S : Subgroup G, S ≤ Subgroup.centralizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) →
      IsPGroup 3 S → IsCyclic S := by
  classical
  intro S hSC hS3
  by_contra hncyc
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨E, hES, hEel, hEc⟩ :=
    GL83.I243.Inner.exists_isElemAbelian_card_sq_of_not_isCyclic hp2 hS3 hncyc
  have hEJ : ∀ e ∈ E, e ∈ Subgroup.centralizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) :=
    fun e he => hSC (hES he)
  obtain ⟨ePS⟩ := S9.nonempty_pSimple_equiv hc.ctx.prime (gamma_single hc hin h hU ha ha1) hq
  obtain ⟨F, T, hFJ, hFel, hTJ, hT2, hTne, hFN, hFb⟩ :=
    hin.i1015four (Jpart 3 (Ipart 3 L b) a) hq ((catalogIs_congr ePS).1 hy09)
  have hFc : F ≤ Subgroup.centralizer (E : Set G) := fun f hf =>
    Subgroup.mem_centralizer_iff.2 fun e he =>
      (Subgroup.mem_centralizer_iff.1 (hEJ e he) f (hFJ hf)).symm
  have hEC : E ≤ Subgroup.centralizer (F : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun f hf => Subgroup.mem_centralizer_iff.1 (hEJ e he) f (hFJ hf)
  have hEN : E ≤ Subgroup.normalizer (F : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (hEC he)
  have hET : E ≤ Subgroup.normalizer (T : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun t ht => Subgroup.mem_centralizer_iff.1 (hEJ e he) t (hTJ ht))
  have hFE : IsElemAbelian 3 (F ⊔ E) := CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_sup_of_commute hFel hEel hFc
  have hFEN : F ⊔ E ≤ Subgroup.normalizer (T : Set G) := sup_le hFN hET
  have hcard := card_sup_mul_card_inf_of_le_normalizer (A := F) (B := E) hEN
  have hinf : Nat.card (F ⊓ E : Subgroup G) ≤
      Nat.card (F ⊓ Subgroup.centralizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le (inf_le_inf_left _ fun e he => hEJ e he)
  have hFEb : Nat.card (F ⊔ E : Subgroup G) ≤ 3 ^ GLATwoLocalRank 3 G :=
    card_le_pow_glaTwoLocalRank hp hFE hTne hT2 hFEN
  rw [hEc] at hcard
  rw [hU.rank] at hFEb
  have hpos : 0 < Nat.card (F ⊓ E : Subgroup G) := Nat.card_pos
  rw [show (3 : ℕ) ^ 3 = 27 by norm_num] at hFb
  rw [show (3 : ℕ) ^ 4 = 81 by norm_num] at hFEb
  have hmul : Nat.card (F ⊔ E : Subgroup G) * Nat.card (F ⊓ E : Subgroup G) ≤
      81 * Nat.card (F ⊓ E : Subgroup G) := Nat.mul_le_mul_right _ hFEb
  linarith

theorem gamma_inndiag (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hsingle : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a))
    (hy09 : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) isYs09Type)
    (hess : IsEssential 3 B a) : InnDiagOn 3 B (Jpart 3 (Ipart 3 L b) a) := by
  have hS : IsSTriple 3 B a (Jpart 3 (Ipart 3 L b) a) := ⟨(sstar_triple h.star).1, hess, hsingle⟩
  have hchev : IsChevSimple 2 (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) := by
    refine isChevTwo_of_isListGamma (catalogIs_imp (fun i hi => ?_) hy09)
    rcases hi with h1 | h2 | h3 | h4
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
  have haut := hin.l105.l104.lemma102.aut
  have hBN : B ≤ Subgroup.normalizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h ha).2
  refine haut.innDiag_unif _ _ B hsingle hchev hBN (fun c hcB => ?_)
  by_contra hnon
  have hnid : NonInnDiag 3 c (Jpart 3 (Ipart 3 L b) a) := ⟨hBN hcB, hnon⟩
  rcases hin.l105.l104.lemma102.dich B a _ hS (S8.isKGroup_cx hc.ctx ha1) hchev c hcB hnid with hf | ⟨-, htd⟩
  ·
    have hFN := hin.l105.l103.field_n hc.ctx.prime (by norm_num) _ _ c hsingle hf
    have hq : CFSG.Open.IsQuasisimple (PQuot 3 (Jpart 3 (Ipart 3 L b) a)) :=
      isQuasisimple_pQuot_of_glaPComponent hc.ctx.prime hsingle
    have hys : GLAMarking (PQuot 3 (Jpart 3 (Ipart 3 L b) a)) (fun lab _ _ _ _ _ => lab.n = 1) := by
      refine CFSG.StandardType.Canonical.largeEvenMarking_mono (fun lab R _ I F θ hP => ?_)
        (hin.labels (PQuot 3 (Jpart 3 (Ipart 3 L b) a)) hq hy09 _
          (hin.ys08 (PQuot 3 (Jpart 3 (Ipart 3 L b) a)) hq hchev))
      rcases hP.1 with ⟨-, -, hn⟩ | ⟨-, -, hn⟩ | ⟨-, -, hn⟩ <;> exact hn
    exact hFN.2.1 hys
  · exact not_isTD4_of_isYs09Type hin.dist hy09 htd

theorem claimK_not_A6 (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hTa : ∃ T : Subgroup G, T ≤ Jpart 3 (Ipart 3 L b) a ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) ≠ ⊥)
    (hsingle : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a))
    (hq : CFSG.Open.IsQuasisimple ↥(Jpart 3 (Ipart 3 L b) a))
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hy09 : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) isYs09Type)
    (hchev : IsChevSimple 2 (PSimple 3 (Jpart 3 (Ipart 3 L b) a)))
    (hcentEq : CentModEqZpowers 3 B (Jpart 3 (Ipart 3 L b) a) a)
    (hInn : InnDiagOn 3 B (Jpart 3 (Ipart 3 L b) a)) :
    ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      ¬ catalogIs (↥K ⧸ Subgroup.center ↥K) isA6 := by
  intro D₀ K hstd hA6
  obtain ⟨-, hA6K, -⟩ := hin.substable B a _ D₀ K hSStar hy09 hInn hstd.1
  have hKA6 : catalogIs ↥K isA6 := hA6K hA6
  have hsmall : GLASmall K := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hKA6
    right
    cases i with
    | cyclic q hq => simp [isA6] at hi
    | alternating n hn =>
      simp only [isA6] at hi
      subst hi
      exact ⟨e⟩
    | sporadic s => simp [isA6] at hi
    | lie k => simp [isA6] at hi
  have hall : ∀ D₁ K₁ : Subgroup G, GLAStdSubPre 3 B a (Jpart 3 (Ipart 3 L b) a) D₁ K₁ → GLASmall K₁ := by
    intro D₁ K₁ hP
    by_contra hns
    exact hstd.2 ⟨rfl, D₁, K₁, hP, hns⟩ hsmall
  have hB4 : 3 ^ 4 ≤ Nat.card B := le_of_eq (by rw [(sstar_triple h.star).1.2.1, hU.rank])
  have hInnM : InnerDiagMarking B (Jpart 3 (Ipart 3 L b) a) := (innDiagOn_iff hsingle hq).2 hInn
  have hi171 := hin.i171 B a _ hSStar hB4 hchev (S8.isKGroup_cx hc.ctx ha1) hInnM hcentEq hTa
    ⟨D₀, K, hstd.1⟩ hall
  exact hin.dist.u42_a6 ↥K (hi171.2 D₀ K hstd.1) hKA6

private theorem casegamma_yS_normalizer_inf {A C : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hC ⊢
  intro k
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA k, hC k]

private theorem casegamma_isComponentOf_gLBConj {H K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (hK : IsComponentOf K H) :
    IsComponentOf (GLBConj g K) H := by
  have hH : GLBConj g H = H := mem_normalizer_iff_gLBConj_eq.1 hg
  refine ⟨?_, ?_, ?_⟩
  · have := CFSG.LocalAnalysis.GLTheoremA.gLBConj_mono (g := g) hK.1
    rwa [hH] at this
  · have := isSubnormal_gLBConj hK.2.1 g
    rwa [hH] at this
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective K (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)
      hK.2.2

private theorem casegamma_layer_gLBConj_le {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : GLBConj g (GLALayer H) ≤ GLALayer H := by
  show (sSup {K | IsComponentOf K H}).map (MulAut.conj g⁻¹).toMonoidHom ≤ sSup {K | IsComponentOf K H}
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (casegamma_isComponentOf_gLBConj hg hK)

private theorem casegamma_three_dvd_quot (hin : StdSubFAt G) {K : Subgroup G}
    (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hK : catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i)) :
    3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨F, T, E, -, -, -, -, -, -, -, -, -, -, hEK, -, hEc, hZ⟩ := hin K hKq hK
  have h3K : 3 ∣ Nat.card ↥K := by
    have h := Subgroup.card_dvd_of_le hEK
    rw [hEc] at h
    exact (dvd_pow_self 3 (by norm_num : (3 : ℕ) ≠ 0)).trans h
  have hZn : ¬ 3 ∣ Nat.card (Subgroup.center ↥K) := by
    intro hd
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hd
    have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hzK : ((z : ↥K) : G) ^ 3 = 1 := by
      have := congrArg (fun w : ↥(Subgroup.center ↥K) => ((w : ↥K) : G)) hz3
      simpa using this
    have hzK1 : ((z : ↥K) : G) = 1 := by
      apply hZ
      · refine Subgroup.mem_inf.2 ⟨(z : ↥K).2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hck := Subgroup.mem_center_iff.1 z.2 ⟨k, hk⟩
        simpa using congrArg Subtype.val hck
      · exact hzK
    have hzK' : (z : ↥K) = 1 := Subtype.ext hzK1
    have hz1 : z = 1 := Subtype.ext hzK'
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
  rw [hsplit] at h3K
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3K with h | h
  · exact h
  · exact absurd h hZn

theorem std_single (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {D₀ K : Subgroup G} (hstd : GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K) {y : G} (hy : y ∈ D₀)
    (hya : y ∉ Subgroup.zpowers a) :
    GLAPComponent 3 (cx y) (closureIn K (GLAPLayer 3 (cx y))) ∧
      B ≤ Subgroup.normalizer ((closureIn K (GLAPLayer 3 (cx y)) : Subgroup G) : Set G) ∧
      GLAPComponent 3 (closureIn K (GLAPLayer 3 (cx y)) ⊓ cx a) K := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hD₀B, hD₀el, hD₀c, haD₀, hKdef, hKcomp, hDeq⟩ := hstd.1
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hBel : IsElemAbelian 3 B := B_el h
  have hy1 : y ≠ 1 := fun h1 => hya (h1 ▸ Subgroup.one_mem _)
  have hyB : y ∈ B := hD₀B hy
  have hay3 : a ^ 3 = 1 := hD₀el.2 a haD₀
  have hyy3 : y ^ 3 = 1 := hD₀el.2 y hy
  have hBC : B ≤ cx y := isElemAbelian_le_centralizer hBel hyB
  have hay' : a ∉ Subgroup.zpowers y := fun hm => by
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers y := Subgroup.zpowers_le.2 hm
    have hcard : Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers a) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hyy3 hy1, orderOf_eq_prime hay3 ha1]
    exact hya (Subgroup.eq_of_le_of_card_ge hle hcard ▸ Subgroup.mem_zpowers y)
  have hcsD : cs D₀ = cx a ⊓ cx y := by
    obtain ⟨hDle, -, hDcard⟩ := card_Dgrp hD₀el hp haD₀ hy hy1 hay'
    have hDeq' : Dgrp a y = D₀ := Subgroup.eq_of_le_of_card_ge hDle (by rw [hD₀c, hDcard])
    rw [← hDeq', dgrp_eq_sup, gamma_cs_zpowers_sup]
  have hcsA : cx a ⊓ cs D₀ = cx a ⊓ cx y := by
    rw [hcsD, ← inf_assoc, inf_idem]
  have hJsub : IsSubnormal (Jpart 3 (Ipart 3 L b) a) (cx a) := Jpart_subnormal hc hin.l105 h ha ha1
  have hKa0 : GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ Subgroup.centralizer (D₀ : Set G)) K :=
    glaPComponent_of_quasisimple hp hKcomp.2.1 hKq (casegamma_three_dvd_quot hin.stdf hKq (hclaim D₀ K hstd))
  have hKa : GLAPComponent 3 (cx y ⊓ cx a) K := by
    have h1 := glaPComponent_of_isSubnormal' hp (isSubnormal_inf hJsub (cs D₀)) hKa0
    rw [hcsA] at h1
    rw [inf_comm]
    exact h1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := by
    intro β hβ
    have hβH : ∀ γ ∈ B, γ ∈ Subgroup.normalizer
        ((Jpart 3 (Ipart 3 L b) a ⊓ Subgroup.centralizer (D₀ : Set G) : Subgroup G) : Set G) :=
      fun γ hγ => casegamma_yS_normalizer_inf ((B_le_N_J hc h ha).2 hγ)
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_iff.2 fun d hd =>
          isElemAbelian_commute hBel (hD₀B hd) hγ))
    have h1 := casegamma_layer_gLBConj_le (hβH β hβ)
    have h2 := casegamma_layer_gLBConj_le (hβH β⁻¹ (B.inv_mem hβ))
    rw [mem_normalizer_iff_gLBConj_eq, hKdef]
    apply le_antisymm h1
    calc GLALayer (Jpart 3 (Ipart 3 L b) a ⊓ Subgroup.centralizer (D₀ : Set G))
        = GLBConj β (GLBConj β⁻¹ (GLALayer (Jpart 3 (Ipart 3 L b) a ⊓
            Subgroup.centralizer (D₀ : Set G)))) := (gLBConj_gLBConj_inv β _).symm
      _ ≤ GLBConj β (GLALayer (Jpart 3 (Ipart 3 L b) a ⊓ Subgroup.centralizer (D₀ : Set G))) :=
        CFSG.LocalAnalysis.GLTheoremA.gLBConj_mono (g := β) h2
  have hX : CFSG.Open.IsKGroup ↥(cx y) := S8.isKGroup_cx hc.ctx hy1
  have hrank : 3 ^ GLATwoLocalRank 3 ↥(cx y) ≤ Nat.card B := by
    rw [(sstar_triple h.star).1.2.1]
    exact Nat.pow_le_pow_right (by norm_num) (glaTwoLocalRank_subgroup_le (by norm_num : 1 < 3) (cx y))
  obtain ⟨eK⟩ := S9.nonempty_pSimple_equiv hp hKa hKq
  have hcat : catalogIs (PSimple 3 K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) :=
    (catalogIs_congr eK).2 (hclaim D₀ K hstd)
  obtain ⟨K', hK'c, hKK', hBK'⟩ := hin.single_std (cx y) a B K hX
    (hD₀B haD₀) hBC hBel hrank
    (by rw [S3.centralizer_zpowers a]; exact hKa) hBN hcat
  have hKeq : closureIn K (GLAPLayer 3 (cx y)) = K' := closureIn_layer_eq_of_component hp hK'c hKa hKK'
  have hKa_le : K ≤ cx a := (hKcomp.1.trans inf_le_left).trans (Jpart_le_cx h ha)
  rw [hKeq]
  refine ⟨hK'c, hBK', ?_⟩
  exact glaPComponent_of_le hp hKa (le_inf hKK' hKa_le) (inf_le_inf_right _ hK'c.1)

private theorem casegamma_centralizes_of_perfect {K : Subgroup G} (hperf : commutator ↥K = ⊤) {t : G}
    (htN : t ∈ Subgroup.normalizer (K : Set G))
    (hcen : ∀ k ∈ K, ∀ k' ∈ K, (t * k * t⁻¹ * k⁻¹) * k' = k' * (t * k * t⁻¹ * k⁻¹)) :
    t ∈ Subgroup.centralizer (K : Set G) := by
  let tk : ↥K → ↥K := fun k => ⟨t * (k : G) * t⁻¹, (Subgroup.mem_normalizer_iff.1 htN k).1 k.2⟩
  have htk_mul : ∀ k k' : ↥K, tk (k * k') = tk k * tk k' := fun k k' =>
    Subtype.ext (by simp only [tk, Subgroup.coe_mul]; group)
  let u : ↥K → ↥K := fun k => tk k * k⁻¹
  have hucen : ∀ k k' : ↥K, u k * k' = k' * u k := fun k k' =>
    Subtype.ext (hcen k k.2 k' k'.2)
  have hu_mul : ∀ k k' : ↥K, u (k * k') = u k * u k' := by
    intro k k'
    calc u (k * k') = tk k * (tk k' * k'⁻¹) * k⁻¹ := by simp only [u, htk_mul]; group
      _ = (tk k * k⁻¹) * (k * (tk k' * k'⁻¹) * k⁻¹) := by group
      _ = (tk k * k⁻¹) * (tk k' * k'⁻¹) := by
        congr 1
        have := hucen k' k
        calc k * (tk k' * k'⁻¹) * k⁻¹ = (k * u k') * k⁻¹ := rfl
          _ = (u k' * k) * k⁻¹ := by rw [← this]
          _ = u k' := mul_inv_cancel_right _ _
          _ = tk k' * k'⁻¹ := rfl
  let ψ : ↥K →* ↥K :=
    { toFun := u
      map_one' := by simp [u, tk]
      map_mul' := hu_mul }
  have hψ : ∀ k, ψ k = 1 := by
    have hle : commutator ↥K ≤ ψ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hucen a (ψ b)
    intro k
    have hk : k ∈ commutator ↥K := by rw [hperf]; exact Subgroup.mem_top k
    exact MonoidHom.mem_ker.1 (hle hk)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : tk ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹ = 1 := hψ ⟨k, hk⟩
  have h2 : tk ⟨k, hk⟩ = ⟨k, hk⟩ := mul_inv_eq_one.1 h1
  have h3 : t * k * t⁻¹ = k := congrArg Subtype.val h2
  calc k * t = (t * k * t⁻¹) * t := by rw [h3]
    _ = t * k := by group

private theorem casegamma_centMod_centralizes {X J : Subgroup G} (hJ : GLAPComponent 3 X J)
    (hq : CFSG.Open.IsQuasisimple ↥J) {t : G} (ht : CentMod 3 J t) :
    t ∈ Subgroup.centralizer (J : Set G) := by
  classical
  have hPQ : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hOne : GLAPPrimeCore 3 ↥J ≠ ⊤ := by
    intro h
    have hnt := isQuasisimple_nontrivial hPQ
    rw [h] at hnt
    exact not_nontrivial_iff_subsingleton.2 QuotientGroup.subsingleton_quotient_top hnt
  have hOZ : GLAPPrimeCore 3 ↥J ≤ Subgroup.center ↥J :=
    le_center_of_normal_of_isQuasisimple hq (GLAPPrimeCore.normal 3 ↥J) hOne
  have hcen : ∀ z ∈ GLAPPrimeCoreOf 3 J, ∀ k ∈ J, k * z = z * k := by
    intro z hz k hk
    unfold GLAPPrimeCoreOf at hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hz
    have hck := Subgroup.mem_center_iff.1 (hOZ hu) ⟨k, hk⟩
    simpa using congrArg Subtype.val hck
  have htN : t ∈ Subgroup.normalizer (J : Set G) := (centMod_iff.1 ht).1
  have hcomm : ∀ k ∈ J, t * k * t⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 J := by
    intro k hk
    have h2 := (GLAPPrimeCoreOf 3 J).inv_mem ((centMod_iff.1 ht).2 k hk)
    rw [commutatorElement_def] at h2
    have heq : t * k * t⁻¹ * k⁻¹ = (k * t * k⁻¹ * t⁻¹)⁻¹ := by group
    rw [heq]
    exact h2
  apply casegamma_centralizes_of_perfect hq.1 htN
  intro k hk k' hk'
  exact (hcen _ (hcomm k hk) k' hk').symm

private theorem casegamma_card_le_three_of_cyclic {C : Subgroup G} (hC : IsCyclic C)
    (hel : ∀ x ∈ C, x ^ 3 = 1) : Nat.card C ≤ 3 := by
  have hexp : Monoid.exponent C ∣ 3 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    apply Subtype.ext
    simpa using hel g.1 g.2
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

theorem claimK_not_L28 (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hy09 : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) isYs09Type)
    (hInn : InnDiagOn 3 B (Jpart 3 (Ipart 3 L b) a)) :
    ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      ¬ catalogIs (↥K ⧸ Subgroup.center ↥K) isL2eight := by
  classical
  intro D₀ K hstd hL2
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hD₀B, hD₀el, hD₀c, -, hKdef, -, -⟩ := hstd.1
  have hsingle := gamma_single hc hin h hU ha ha1
  have hq : CFSG.Open.IsQuasisimple ↥(Jpart 3 (Ipart 3 L b) a) := hSStar.2.2.2.1.2.2
  have hU6 : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) S9.isU6two :=
    (hin.substable B a _ D₀ K hSStar hy09 hInn hstd.1).2.2 hL2
  have hBN : B ≤ Subgroup.normalizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h ha).2
  have hinnD : InnDiagOn 3 D₀ (Jpart 3 (Ipart 3 L b) a) := innDiagOn_mono hInn hD₀B
  have hbound := hin.u6d0 (Jpart 3 (Ipart 3 L b) a) D₀ K ⟨cx a, hsingle⟩ hU6
    (fun d hd => hBN (hD₀B hd)) hD₀el hD₀c hinnD hKdef hL2
  obtain ⟨A, hAel, hAB, hAcard⟩ := hU.centRank
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have haB : a ∈ B := (dgrp_facts hc h).1 ha
  have hbB : b ∈ B := h.mem
  have hAN : A ≤ Subgroup.normalizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) := by
    intro g hg
    have hgx : g ∈ cx x :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hAB hg) x hxB).symm
    have hga : g ∈ cx a :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hAB hg) a haB).symm
    have hgb : g ∈ cx b :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hAB hg) b hbB).symm
    have hgL : g ∈ Subgroup.normalizer (L : Set G) := by
      have := mem_normalizer_glaPLayer (p := 3) (Subgroup.le_normalizer hgx)
      rwa [sstar_layer hc h.star] at this
    have hgI : g ∈ Subgroup.normalizer ((L ⊓ cx b : Subgroup G) : Set G) :=
      casegamma_yS_normalizer_inf hgL (Subgroup.le_normalizer hgb)
    exact mem_normalizer_closureIn (mem_normalizer_glaPLayer hgI)
      (mem_normalizer_glaPLayer (Subgroup.le_normalizer hga))
  have hAC : A ≤ Subgroup.centralizer (D₀ : Set G) := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun d hd => Subgroup.mem_centralizer_iff.1 (hAB hg) d (hD₀B hd)
  have hbound' := hbound A hAN hAC hAel
  have hCcent : A ⊓ centModSubgroup 3 (Jpart 3 (Ipart 3 L b) a) ≤
      Subgroup.centralizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) :=
    fun g hg => casegamma_centMod_centralizes hsingle hq (centMod_iff.2 (Subgroup.mem_inf.1 hg).2)
  have hCyc := hSStar.2.2.2.2 _ hCcent (isPGroup_of_isElemAbelian (isElemAbelian_mono hAel inf_le_left))
  have hCcard : Nat.card ↥(A ⊓ centModSubgroup 3 (Jpart 3 (Ipart 3 L b) a)) ≤ 3 :=
    casegamma_card_le_three_of_cyclic hCyc (fun g hg => hAel.2 g (Subgroup.mem_inf.1 hg).1)
  rw [show (3 : ℕ) ^ 5 = 243 by norm_num] at hAcard
  rw [show (3 : ℕ) ^ 3 = 27 by norm_num] at hbound'
  omega

theorem gamma_claimK (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hTa : ∃ T : Subgroup G, T ≤ Jpart 3 (Ipart 3 L b) a ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) ≠ ⊥)
    (hsingle : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a))
    (hq : CFSG.Open.IsQuasisimple ↥(Jpart 3 (Ipart 3 L b) a))
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hy09 : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) isYs09Type)
    (hchev : IsChevSimple 2 (PSimple 3 (Jpart 3 (Ipart 3 L b) a)))
    (hcentEq : CentModEqZpowers 3 B (Jpart 3 (Ipart 3 L b) a) a)
    (hInn : InnDiagOn 3 B (Jpart 3 (Ipart 3 L b) a)) :
    ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) := by
  intro D₀ K hstd
  obtain ⟨⟨i, hi, e⟩, -, -⟩ := hin.substable B a _ D₀ K hSStar hy09 hInn hstd.1
  rcases hi with h1 | h2 | h3 | h4 | h5
  · exact ⟨i, Or.inl h1, e⟩
  · exact ⟨i, Or.inr (Or.inl h2), e⟩
  · exact ⟨i, Or.inr (Or.inr h3), e⟩
  · exact absurd ⟨i, h4, e⟩ (claimK_not_A6 hc hin h hU ha ha1 hTa hsingle hq hSStar hy09 hchev hcentEq hInn D₀ K hstd)
  · exact absurd ⟨i, h5, e⟩ (claimK_not_L28 hc hin h hU ha ha1 hSStar hy09 hInn D₀ K hstd)

private theorem casegamma_yS_not_isCyclic {p : ℕ} {D : Subgroup G} (hp : p.Prime) (hDel : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) : ¬ IsCyclic D := by
  intro hcyc
  have hexp : Monoid.exponent D ∣ p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    apply Subtype.ext
    simpa using hDel.2 g.1 g.2
  rw [IsCyclic.exponent_eq_card, hDc] at hexp
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hexp
  nlinarith [hp.two_le]

theorem gamma_yS (hc : S10Ctx G 3) {B : Subgroup G} {a : G} (hB : GLAIsBmax 3 B) {D₀ : Subgroup G}
    (hD₀B : D₀ ≤ B) (hD₀el : IsElemAbelian 3 D₀) (hD₀c : Nat.card D₀ = 3 ^ 2) (haD₀ : a ∈ D₀) (ha1 : a ≠ 1) :
    ∃ y ∈ D₀, y ∉ Subgroup.zpowers a ∧ ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≠ ⊥ ∧
      (⁅S, D₀⁆ : Subgroup G) = S ∧ S ≤ cx y ∧ B ≤ Subgroup.normalizer (S : Set G) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hBel, -, U, hU1, hU2, hUN⟩ := hB
  have hD₀ne : D₀ ≠ ⊥ := fun e => by
    rw [e, Subgroup.card_bot] at hD₀c
    norm_num at hD₀c
  have hBbot : B ≠ ⊥ := fun e => hD₀ne (le_bot_iff.1 (e ▸ hD₀B))
  obtain ⟨T, hUT, hTmax⟩ := Set.Finite.exists_le_maximal
    (Set.toFinite {T : Subgroup G | IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)})
    (show U ∈ {T : Subgroup G | IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)} from ⟨hU2, hUN⟩)
  obtain ⟨⟨hT2, hTN⟩, hTmax'⟩ := hTmax
  have hTne : T ≠ ⊥ := fun e => hU1 (le_bot_iff.1 (e ▸ hUT))
  have hmax : ∀ T' : Subgroup G, IsPGroup 2 T' → B ≤ Subgroup.normalizer (T' : Set G) →
      T ≤ T' → T' = T := fun T' h2 hN hle =>
    le_antisymm (hTmax' (show T' ∈ {T : Subgroup G | IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G)} from ⟨h2, hN⟩) hle) hle
  obtain ⟨-, hD⟩ := GL83.I_33_1_proved G hc.ctx.charTwo 3 hp hp2 B T hBbot hBel hT2 hTN
    (Or.inl ⟨hTne, hmax⟩)
  obtain ⟨-, d₁, d₂, hd₁, hd₂, hd₁1, hd₂d₁, hc₁, hc₂⟩ :=
    hD D₀ hD₀ne hD₀B (casegamma_yS_not_isCyclic hp hD₀el hD₀c)
  have hpow : ∀ g ∈ B, g ^ 3 = 1 := fun g hg => hBel.2 g hg
  obtain ⟨y, hyD, hya, hcy⟩ : ∃ y ∈ D₀, y ∉ Subgroup.zpowers a ∧
      (⁅D₀, T ⊓ cx y⁆ : Subgroup G) ≠ ⊥ := by
    by_cases hd₁x : d₁ ∈ Subgroup.zpowers a
    · refine ⟨d₂, hd₂, fun hd₂x => ?_, hc₂⟩
      have hao : orderOf a = 3 := orderOf_eq_prime (hpow a (hD₀B haD₀)) ha1
      have hd1o : orderOf d₁ = 3 := orderOf_eq_prime (hpow d₁ (hD₀B hd₁)) hd₁1
      have hdx : Subgroup.zpowers d₁ = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hd₁x)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hao, hd1o])
      rw [← hdx] at hd₂x
      exact hd₂d₁ hd₂x
    · exact ⟨d₁, hd₁, hd₁x, hc₁⟩
  refine ⟨y, hyD, hya, ?_⟩
  have hDC : D₀ ≤ cx y := isElemAbelian_le_centralizer hD₀el hyD
  have hBC : B ≤ cx y := isElemAbelian_le_centralizer hBel (hD₀B hyD)
  have hDN : D₀ ≤ Subgroup.normalizer ((T ⊓ cx y : Subgroup G) : Set G) := fun d hd =>
    casegamma_yS_normalizer_inf (hTN (hD₀B hd)) (Subgroup.le_normalizer (hDC hd))
  have hX2 : IsPGroup 2 (T ⊓ cx y : Subgroup G) := hT2.to_le inf_le_left
  have hDp : IsPGroup 3 D₀ := isPGroup_of_isElemAbelian hD₀el
  have hXp : ¬ 3 ∣ Nat.card (T ⊓ cx y : Subgroup G) := by
    intro hdvd
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hS_le : (⁅T ⊓ cx y, D₀⁆ : Subgroup G) ≤ T ⊓ cx y := comm_le_left_of_normalizes hDN
  have hS_eq : (⁅⁅T ⊓ cx y, D₀⁆, D₀⁆ : Subgroup G) = ⁅T ⊓ cx y, D₀⁆ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq hp hDp hDN hXp
  refine ⟨⁅T ⊓ cx y, D₀⁆, hT2.to_le (hS_le.trans inf_le_left), ?_, hS_eq,
    commutator_le_of_le' inf_le_right hDC, ?_⟩
  · rw [Subgroup.commutator_comm]
    exact hcy
  · intro β hβ
    rw [mem_normalizer_iff_gLBConj_eq]
    have hβX : β ∈ Subgroup.normalizer ((T ⊓ cx y : Subgroup G) : Set G) :=
      casegamma_yS_normalizer_inf (hTN hβ) (Subgroup.le_normalizer (hBC hβ))
    have hβD : β ∈ Subgroup.normalizer ((D₀ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hBel (hD₀B hd) hβ)
    have e : GLBConj β ⁅T ⊓ cx y, D₀⁆ = ⁅GLBConj β (T ⊓ cx y), GLBConj β D₀⁆ :=
      Subgroup.map_commutator _ _ (MulAut.conj β⁻¹).toMonoidHom
    show GLBConj β ⁅T ⊓ cx y, D₀⁆ = ⁅T ⊓ cx y, D₀⁆
    rw [e, mem_normalizer_iff_gLBConj_eq.1 hβX, mem_normalizer_iff_gLBConj_eq.1 hβD]

theorem gamma_S_norm (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {D₀ K : Subgroup G} (hstd : GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K) {y : G} (hy : y ∈ D₀)
    (hya : y ∉ Subgroup.zpowers a) {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hSD : (⁅S, D₀⁆ : Subgroup G) = S) (hSy : S ≤ cx y) (hSB : B ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ Subgroup.normalizer ((closureIn K (GLAPLayer 3 (cx y)) : Subgroup G) : Set G) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hD₀B, hD₀el, hD₀c, haD₀, hKdef, hKcomp, hDeq⟩ := hstd.1
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hy1 : y ≠ 1 := fun h1 => hya (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hMc, hBM, -⟩ := std_single hc hin h hU ha ha1 hSStar hclaim hstd hy hya
  obtain ⟨F, T', E, -, -, -, -, -, -, -, -, -, -, hEK, hEel, hEc, -⟩ :=
    hin.stdf K hKq (hclaim D₀ K hstd)
  have hEM : E ≤ closureIn K (GLAPLayer 3 (cx y)) := hEK.trans (le_closureIn_self _ _)
  have hBel : IsElemAbelian 3 B := B_el h
  have hBcy : B ≤ cx y := isElemAbelian_le_centralizer hBel (hD₀B hy)
  have hX : CFSG.Open.IsKGroup ↥(cx y) := S8.isKGroup_cx hc.ctx hy1
  have hrank : 3 ^ GLATwoLocalRank 3 ↥(cx y) ≤ Nat.card B := by
    rw [(sstar_triple h.star).1.2.1]
    exact Nat.pow_le_pow_right (by norm_num) (glaTwoLocalRank_subgroup_le (by norm_num : 1 < 3) (cx y))
  have hBs : ∀ s ∈ S, B ≤ Subgroup.normalizer ((GLBConj s (closureIn K (GLAPLayer 3 (cx y))) : Subgroup G) : Set G) := by
    intro s hs
    have hsN : GLBConj s (cx y) = cx y :=
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hSy hs))
    have hcomp : GLAPComponent 3 (cx y) (GLBConj s (closureIn K (GLAPLayer 3 (cx y)))) := by
      have := glaPComponent_gLBConj hMc s
      rwa [hsN] at this
    have hEs : IsElemAbelian 3 (GLBConj s E) :=
      CFSG.SectionRank.isElemAbelian_map hEel (MulAut.conj s⁻¹).toMonoidHom
    have hEcard : Nat.card (GLBConj s E) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective
    exact hin.norm113 (cx y) B (GLBConj s (closureIn K (GLAPLayer 3 (cx y)))) hX hBcy hBel hrank
      ⟨S, hSy, hSne, hS2, hSB⟩ hcomp
      ⟨GLBConj s E, CFSG.LocalAnalysis.GLTheoremA.gLBConj_mono (g := s) hEM, hEs, hEcard.trans hEc⟩
  have hkey : ∀ g ∈ S, ∀ k ∈ B,
      g * k * g⁻¹ ∈ Subgroup.normalizer ((closureIn K (GLAPLayer 3 (cx y)) : Subgroup G) : Set G) := by
    intro g hg k hk
    have hkN := hBs g hg hk
    rw [mem_normalizer_iff_gLBConj_eq] at hkN
    rw [mem_normalizer_iff_gLBConj_eq]
    calc GLBConj (g * k * g⁻¹) (closureIn K (GLAPLayer 3 (cx y)))
        = GLBConj (k * g⁻¹) (GLBConj g (closureIn K (GLAPLayer 3 (cx y)))) := by
          rw [gLBConj_gLBConj, mul_assoc]
      _ = GLBConj g⁻¹ (GLBConj k (GLBConj g (closureIn K (GLAPLayer 3 (cx y))))) :=
          (gLBConj_gLBConj g⁻¹ k _).symm
      _ = GLBConj g⁻¹ (GLBConj g (closureIn K (GLAPLayer 3 (cx y)))) := by rw [hkN]
      _ = GLBConj (g * g⁻¹) (closureIn K (GLAPLayer 3 (cx y))) := gLBConj_gLBConj g⁻¹ g _
      _ = closureIn K (GLAPLayer 3 (cx y)) := by rw [mul_inv_cancel, gLBConj_one]
  calc S = ⁅S, D₀⁆ := hSD.symm
    _ ≤ Subgroup.normalizer ((closureIn K (GLAPLayer 3 (cx y)) : Subgroup G) : Set G) := by
      refine Subgroup.commutator_le.2 fun g hg k hk => ?_
      rw [commutatorElement_def]
      exact mul_mem (hkey g hg k (hD₀B hk)) (inv_mem (hBM (hD₀B hk)))


private theorem y9x_normal_central {K N : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥K)
    (hNK : N ≤ K) (hN : ∀ n ∈ N, ∀ k ∈ K, k * n * k⁻¹ ∈ N)
    (hpK : p ∣ Nat.card ↥K) (hpN : ¬ p ∣ Nat.card ↥N) :
    ∀ n ∈ N, ∀ k ∈ K, k * n = n * k := by
  classical
  set N' : Subgroup ↥K := N.subgroupOf K with hN'def
  have hN'norm : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN'def, Subgroup.mem_subgroupOf] at hn ⊢
    have := hN (n : G) hn (g : G) g.2
    simpa [Subgroup.mem_subgroupOf] using this
  rcases normal_le_center_or_eq_top' hq N' with hcen | htop
  · intro n hn k hk
    have hmem : (⟨n, hNK hn⟩ : ↥K) ∈ N' := by
      rw [hN'def, Subgroup.mem_subgroupOf]
      exact hn
    have hc := Subgroup.mem_center_iff.1 (hcen hmem) ⟨k, hk⟩
    have hc' := congrArg Subtype.val hc
    simpa using hc'
  · exfalso
    apply hpN
    have hcardN : Nat.card N' = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
    have hcardK : Nat.card N' = Nat.card ↥K := by
      rw [htop, Subgroup.card_top]
    rw [← hcardN, hcardK]
    exact hpK

private theorem y9x_centralizes_of_comm {K : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥K) {c : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hz : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, c⁆ * k' = k' * ⁅k, c⁆) :
    ∀ k ∈ K, k * c = c * k := by
  classical
  have hcK : ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun k hk => (Subgroup.mem_normalizer_iff.1 hcN k).1 hk
  have hmul : ∀ a ∈ K, ∀ b ∈ K, ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
    intro a ha b hb
    have h1 : ⁅b, c⁆ * a = a * ⁅b, c⁆ := hz b hb a ha
    have e1 : b * c * b⁻¹ = ⁅b, c⁆ * c := by
      rw [commutatorElement_def]; group
    have e2 : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by
      rw [← h1]; group
    calc ⁅a * b, c⁆ = a * (b * c * b⁻¹) * a⁻¹ * c⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = a * (⁅b, c⁆ * c) * a⁻¹ * c⁻¹ := by rw [e1]
      _ = (a * ⁅b, c⁆ * a⁻¹) * (a * c * a⁻¹ * c⁻¹) := by group
      _ = ⁅b, c⁆ * (a * c * a⁻¹ * c⁻¹) := by rw [e2]
      _ = ⁅b, c⁆ * ⁅a, c⁆ := by simp only [commutatorElement_def]
  have hone : ∀ x : G, ⁅(1 : G), x⁆ = 1 := fun x => by simp [commutatorElement_def]
  have hinv : ∀ a ∈ K, ⁅a⁻¹, c⁆ = ⁅a, c⁆⁻¹ := by
    intro a ha
    have h := hmul a ha a⁻¹ (K.inv_mem ha)
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hval : ∀ k ∈ K, ⁅k, c⁆ ∈ K := by
    intro k hk
    have h1 : k * (c * k⁻¹ * c⁻¹) ∈ K := K.mul_mem hk (hcK _ (K.inv_mem hk))
    have e : ⁅k, c⁆ = k * (c * k⁻¹ * c⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]; exact h1
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, Commute ⁅a, c⁆ ⁅b, c⁆ := by
    intro a ha b hb
    exact (hz b hb _ (hval a ha)).symm
  set Sc : Subgroup ↥K := (Subgroup.centralizer ({c} : Set G)).subgroupOf K with hScdef
  have hcomm' : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ ≤ Sc := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    have hx : (x : G) ∈ K := x.2
    have hy : (y : G) ∈ K := y.2
    have hpt : ((⁅x, y⁆ : ↥K) : G) = ⁅(x : G), (y : G)⁆ := by
      simp [commutatorElement_def]
    have hz0 : ⁅⁅(x : G), (y : G)⁆, c⁆ = 1 := by
      have hPQ : ⁅(y : G), c⁆ * ⁅(x : G), c⁆ = ⁅(x : G), c⁆ * ⁅(y : G), c⁆ :=
        (hcomm (x : G) hx (y : G) hy).eq.symm
      have h2 := hmul (x : G) hx (y : G) hy
      have h1 := hmul ((x : G) * (y : G)) (K.mul_mem hx hy) (x : G)⁻¹ (K.inv_mem hx)
      have h3 := hmul ((x : G) * (y : G) * (x : G)⁻¹)
        (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (y : G)⁻¹ (K.inv_mem hy)
      rw [commutatorElement_def (x : G) (y : G), h3, h1, h2, hinv (x : G) hx, hinv (y : G) hy,
        hPQ, inv_mul_cancel_left, inv_mul_cancel]
    rw [hScdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, hpt]
    exact commutatorElement_eq_one_iff_mul_comm.1 hz0
  have htop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := hq.1
  rw [htop] at hcomm'
  intro k hk
  have hkS : (⟨k, hk⟩ : ↥K) ∈ Sc := hcomm' (Subgroup.mem_top _)
  rw [hScdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hkS
  exact hkS

private theorem y9x_eq_of_subnormal_cover {X J : Subgroup G} (hperf : ⁅X, X⁆ = X)
    (hJX : IsSubnormal J X)
    (hcov : ∀ x ∈ X, ∃ j ∈ J, ∃ z ∈ X, (∀ w ∈ X, z * w = w * z) ∧ x = j * z) : J = X := by
  revert hperf hcov
  induction hJX with
  | refl => intro _ _; rfl
  | @step H M X hHM hHn hMX ih =>
    intro hperf hcov
    have hcovM : ∀ x ∈ X, ∃ j ∈ M, ∃ z ∈ X, (∀ w ∈ X, z * w = w * z) ∧ x = j * z := by
      intro x hx
      obtain ⟨j, hj, z, hz, hcz, hxz⟩ := hcov x hx
      exact ⟨j, hHM hj, z, hz, hcz, hxz⟩
    have hMeq : M = X := ih hperf hcovM
    rw [hMeq] at hHn hHM
    have hHX : H ≤ X := hHM
    have hcomm_le : ⁅X, X⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨j1, hj1, z1, hz1, hc1, hx1⟩ := hcov x hx
      obtain ⟨j2, hj2, z2, hz2, hc2, hy1⟩ := hcov y hy
      have hcen1 : ∀ a ∈ X, ∀ b ∈ X, ⁅a * z1, b⁆ = ⁅a, b⁆ := by
        intro a ha b hb
        have hzb : z1 * b = b * z1 := hc1 b hb
        calc ⁅a * z1, b⁆ = a * (z1 * b * z1⁻¹) * a⁻¹ * b⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = a * b * a⁻¹ * b⁻¹ := by
              rw [hzb]; group
          _ = ⁅a, b⁆ := by simp only [commutatorElement_def]
      have hcen2 : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b * z2⁆ = ⁅a, b⁆ := by
        intro a ha b hb
        have hza : z2 * a⁻¹ * z2⁻¹ = a⁻¹ := by
          rw [hc2 a⁻¹ (X.inv_mem ha)]; group
        calc ⁅a, b * z2⁆ = a * b * (z2 * a⁻¹ * z2⁻¹) * b⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = ⁅a, b⁆ := by
              rw [hza, commutatorElement_def]
      have hnorm : j2 * j1⁻¹ * j2⁻¹ ∈ H := by
        have hmem : (⟨j1⁻¹, X.inv_mem (hHX hj1)⟩ : ↥X) ∈ H.subgroupOf X :=
          Subgroup.mem_subgroupOf.2 (H.inv_mem hj1)
        have h := Subgroup.mem_subgroupOf.1 (hHn.conj_mem _ hmem ⟨j2, hHX hj2⟩)
        simpa using h
      have e : ⁅j1, j2⁆ = j1 * (j2 * j1⁻¹ * j2⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [hx1, hy1, hcen1 j1 (hHX hj1) (j2 * z2) (X.mul_mem (hHX hj2) hz2),
        hcen2 j1 (hHX hj1) j2 (hHX hj2), e]
      exact H.mul_mem hj1 hnorm
    have hXH : X ≤ H := by
      calc X = ⁅X, X⁆ := hperf.symm
        _ ≤ H := hcomm_le
    exact le_antisymm hHX hXH


private theorem y9x_glaPComponent {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (hKX : IsSubnormal K X) (hq : CFSG.Open.IsQuasisimple ↥K) (hpK : p ∣ Nat.card ↥K) :
    GLAPComponent p X K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hKle : K ≤ X := isSubnormal_le' hKX
  have h0 : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := hq.1
  have htopK : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hperf : ⁅K, K⁆ = K := by
    have h := congrArg (Subgroup.map K.subtype) h0
    rw [Subgroup.map_commutator, htopK] at h
    exact h
  set N : Subgroup G := K ⊓ GLAPPrimeCoreOf p X with hNdef
  have hNK : N ≤ K := inf_le_left
  have hNO : N ≤ GLAPPrimeCoreOf p X := inf_le_right
  have hNnorm : ∀ n ∈ N, ∀ k ∈ K, k * n * k⁻¹ ∈ N := by
    intro n hn k hk
    refine ⟨K.mul_mem (K.mul_mem hk hn.1) (K.inv_mem hk), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p X (hKle hk)) n).1 hn.2
  have hcopO : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p X)) := by
    have e : Nat.card ↥(GLAPPrimeCoreOf p X) = Nat.card ↥(GLAPPrimeCore p ↥X) :=
      Nat.card_congr (Subgroup.equivMapOfInjective (GLAPPrimeCore p ↥X) X.subtype
        Subtype.val_injective).toEquiv.symm
    rw [e]
    exact CFSG.pPrimeCore_coprime_card
  have hNcop : ¬ p ∣ Nat.card ↥N := fun hdvd => by
    have hd : Nat.card ↥N ∣ Nat.card ↥(GLAPPrimeCoreOf p X) := Subgroup.card_dvd_of_le hNO
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcopO (hdvd.trans hd)
  have hcomm : ∀ n ∈ N, ∀ k ∈ K, k * n = n * k := y9x_normal_central hq hNK hNnorm hpK hNcop
  have hKnotO : ∃ k ∈ K, k ∉ GLAPPrimeCoreOf p X := by
    by_contra hcon
    push Not at hcon
    have hd : Nat.card ↥K ∣ Nat.card ↥(GLAPPrimeCoreOf p X) := Subgroup.card_dvd_of_le hcon
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcopO (hpK.trans hd)
  refine ⟨hKle, hKX, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX p (C := X) hKX
    rwa [barX_self] at this
  ·
    set g : ↥K →* (↥X ⧸ GLAPPrimeCore p ↥X) :=
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (Subgroup.inclusion hKle) with hgdef
    have hBeq : (K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = g.range := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
        exact ⟨⟨x.1, (Subgroup.mem_subgroupOf).1 hx⟩, rfl⟩
      · rintro ⟨k, rfl⟩
        exact Subgroup.mem_map.2 ⟨⟨k.1, hKle k.2⟩, (Subgroup.mem_subgroupOf).2 k.2, rfl⟩
    rw [hBeq]
    have hsurj : Function.Surjective g.rangeRestrict := MonoidHom.rangeRestrict_surjective g
    have hsurj : Function.Surjective g.rangeRestrict := MonoidHom.rangeRestrict_surjective g
    have hcomm_top : ⁅(⊤ : Subgroup ↥g.range), (⊤ : Subgroup ↥g.range)⁆ = ⊤ := by
      have h1 := congrArg (Subgroup.map g.rangeRestrict) h0
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj] at h1
      exact h1
    refine ⟨hcomm_top, ?_⟩
    haveI := hq.2
    have hnotc : ∃ x : ↥g.range, x ∉ Subgroup.center ↥g.range := by
      by_contra hcon
      push Not at hcon
      have hbot : ⁅(⊤ : Subgroup ↥g.range), (⊤ : Subgroup ↥g.range)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact (Subgroup.mem_center_iff.1 (hcon x)) y
      have htt : (⊤ : Subgroup ↥g.range) = ⊥ := by rw [← hcomm_top, hbot]
      obtain ⟨k, hkK, hkO⟩ := hKnotO
      have hk1 : g.rangeRestrict ⟨k, hkK⟩ = 1 := by
        have hmem : g.rangeRestrict ⟨k, hkK⟩ ∈ (⊥ : Subgroup ↥g.range) := by
          rw [← htt]; exact Subgroup.mem_top _
        exact Subgroup.mem_bot.1 hmem
      apply hkO
      have hk2 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨k, hKle hkK⟩ : ↥X) = 1 :=
        congrArg Subtype.val hk1
      have hmem0 : (⟨k, hKle hkK⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := (QuotientGroup.eq_one_iff _).1 hk2
      exact Subgroup.mem_map.2 ⟨⟨k, hKle hkK⟩, hmem0, rfl⟩
    obtain ⟨x, hx⟩ := hnotc
    haveI : Nontrivial (↥g.range ⧸ Subgroup.center ↥g.range) :=
      ⟨⟨(1 : ↥g.range ⧸ Subgroup.center ↥g.range), QuotientGroup.mk x, fun h => hx (by
        have := QuotientGroup.eq.1 h
        simpa using this)⟩⟩
    have hz : Subgroup.center ↥K ≤ (Subgroup.center ↥g.range).comap g.rangeRestrict := by
      intro z hz
      rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
      intro y
      obtain ⟨k, rfl⟩ := hsurj y
      have hzk := Subgroup.mem_center_iff.1 hz k
      have := congrArg (fun t => (g.rangeRestrict t : ↥g.range)) hzk
      simpa using this
    let φ : (↥K ⧸ Subgroup.center ↥K) →* (↥g.range ⧸ Subgroup.center ↥g.range) :=
      QuotientGroup.map (Subgroup.center ↥K) (Subgroup.center ↥g.range) g.rangeRestrict hz
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥g.range) y
      obtain ⟨k, rfl⟩ := hsurj y'
      exact ⟨QuotientGroup.mk k, rfl⟩
    exact IsSimpleGroup.isSimpleGroup_of_surjective φ hφ
  ·
    intro J hJK hJX heq
    have hJle : J ≤ K := hJK.le
    have hcov : ∀ x ∈ K, ∃ j ∈ J, ∃ z ∈ K, (∀ w ∈ K, z * w = w * z) ∧ x = j * z := by
      intro x hx
      have hle : barX p X K ≤ barX p X J := le_of_eq heq.symm
      obtain ⟨j, hj, hjx⟩ := exists_of_barX_le hle hx (hKle hx)
      have hzN : j⁻¹ * x ∈ N := ⟨K.mul_mem (K.inv_mem (hJle hj)) hx, hjx⟩
      refine ⟨j, hj, j⁻¹ * x, hNK hzN, fun w hw => (hcomm _ hzN w hw).symm, ?_⟩
      group
    have hJK' : IsSubnormal J K := isSubnormal_of_le_of_le hJX hJle hKle
    exact hJK.ne (y9x_eq_of_subnormal_cover hperf hJK' hcov)


private theorem y9x_isComponentOf_gLBConj {L H : Subgroup G} (h : IsComponentOf L H) (g : G) :
    IsComponentOf (GLBConj g L) (GLBConj g H) := by
  obtain ⟨hLH, hsn, hq⟩ := h
  refine ⟨gLBConj_mono (g := g) hLH, isSubnormal_gLBConj hsn g, ?_⟩
  have e : ↥L ≃* ↥(GLBConj g L) :=
    Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom (MulEquiv.injective _)
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hq

private theorem y9x_normalizer_layer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((GLALayer H : Subgroup G) : Set G) := by
  have hle : ∀ h : G, h ∈ Subgroup.normalizer (H : Set G) → GLBConj h (GLALayer H) ≤ GLALayer H := by
    intro h hh
    have hHh : GLBConj h H = H := mem_normalizer_iff_gLBConj_eq.1 hh
    unfold GLALayer
    rw [sSup_eq_iSup, GLBConj, Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    have hc0 := y9x_isComponentOf_gLBConj ha h
    rw [hHh] at hc0
    exact le_iSup_of_le (GLBConj h a) (le_iSup_of_le hc0 le_rfl)
  have hgi : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := Subgroup.inv_mem _ hg
  have h1 : GLBConj g (GLALayer H) ≤ GLALayer H := hle g hg
  have h2 : GLBConj g⁻¹ (GLALayer H) ≤ GLALayer H := hle g⁻¹ hgi
  have h3 : GLALayer H ≤ GLBConj g (GLALayer H) := by
    have := gLBConj_mono (g := g) h2
    rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at this
  exact mem_normalizer_iff_gLBConj_eq.2 (le_antisymm h1 h3)

private theorem y9x_three_dvd_of_stdf (hin : StdSubFAt G) {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥K)
    (hc : catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i)) :
    3 ∣ Nat.card ↥K := by
  obtain ⟨F, T, E, -, -, -, -, -, -, -, -, -, -, hEK, -, hEc, -⟩ := hin K hq hc
  have h27 : Nat.card E ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hEK
  rw [hEc] at h27
  exact (Dvd.intro_left _ rfl).trans h27


private theorem y9x_cs_pair (a y : G) :
    Subgroup.centralizer ((Dgrp a y : Subgroup G) : Set G) = cx a ⊓ cx y := by
  ext g
  constructor
  · intro hg
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · exact (Subgroup.mem_centralizer_iff.1 hg a (Subgroup.subset_closure (by simp))).symm
    · exact (Subgroup.mem_centralizer_iff.1 hg y (Subgroup.subset_closure (by simp))).symm
  · intro hg
    obtain ⟨ha, hy⟩ := Subgroup.mem_inf.1 hg
    have hle : Dgrp a y ≤ Subgroup.centralizer ({g} : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      intro d hd
      rcases hd with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 ha).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 hy).symm
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)

private theorem y9x_glaPComponent_eq_of_le {p : ℕ} {X J K' : Subgroup G}
    (hJ : GLAPComponent p X J) (hK' : GLAPComponent p X K') (hle : J ≤ K') : J = K' :=
  glaPComponent_unique hJ hK'
    (CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hJ.2.2.1 hK'.2.2.1 (barX_mono p hle))

private theorem y9x_std_core {B Ja D K : Subgroup G} {a y : G} (hc : S10Ctx G 3)
    (hin : GammaInputs G 3) (hBmax : GLAIsBmax 3 B) (hJa : IsComponentOf Ja (cx a))
    (hBJ : B ≤ Subgroup.normalizer (Ja : Set G)) (haB : a ∈ B) (ha1 : a ≠ 1) (hyB : y ∈ B)
    (hy1 : y ≠ 1) (hDB : D ≤ B) (hD : D = Dgrp a y)
    (hKdef : K = GLALayer (Ja ⊓ Subgroup.centralizer (D : Set G)))
    (hKcomp : IsComponentOf K (Ja ⊓ Subgroup.centralizer (D : Set G)))
    (hK3 : 3 ∣ Nat.card ↥K)
    (hKcl : catalogIs (↥K ⧸ Subgroup.center ↥K)
      (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i)) :
    GLAPComponent 3 (cx y) (closureIn K (GLAPLayer 3 (cx y))) ∧
      B ≤ Subgroup.normalizer ((closureIn K (GLAPLayer 3 (cx y)) : Subgroup G) : Set G) ∧
      GLAPComponent 3 (closureIn K (GLAPLayer 3 (cx y)) ⊓ cx a) K := by
  have hp : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hBel : IsElemAbelian 3 B := hBmax.1
  have hcsD : Subgroup.centralizer (D : Set G) = cx a ⊓ cx y := by
    rw [hD]; exact y9x_cs_pair a y
  have haD : a ∈ D := by
    rw [hD]; exact Subgroup.subset_closure (by simp)
  have hcsa : Subgroup.centralizer (D : Set G) ≤ cx a := by
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hg a haD).symm
  have hsub1 : IsSubnormal (Ja ⊓ Subgroup.centralizer (D : Set G))
      (cx a ⊓ Subgroup.centralizer (D : Set G)) :=
    isSubnormal_inf hJa.2.1 _
  rw [inf_eq_right.2 hcsa] at hsub1
  have hKsub : IsSubnormal K (Subgroup.centralizer (D : Set G)) :=
    isSubnormal_trans' hKcomp.2.1 hsub1
  have hKc0 : GLAPComponent 3 (Subgroup.centralizer (D : Set G)) K :=
    y9x_glaPComponent hp hKsub hKcomp.2.2 hK3
  have hKc : GLAPComponent 3 (cx y ⊓ cx a) K := by
    rw [inf_comm, ← hcsD]
    exact hKc0
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    have hconj : ∀ g' ∈ B, ∀ x ∈ Subgroup.centralizer (D : Set G),
        g' * x * g'⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
      intro g' hg' x hx
      refine Subgroup.mem_centralizer_iff.2 fun d hd => ?_
      have h1 : d * g' = g' * d := isElemAbelian_commute hBel (hDB hd) hg'
      have h2 : d * g'⁻¹ = g'⁻¹ * d := isElemAbelian_commute hBel (hDB hd) (B.inv_mem hg')
      have h3 : d * x = x * d := Subgroup.mem_centralizer_iff.1 hx d hd
      calc d * (g' * x * g'⁻¹) = (d * g') * x * g'⁻¹ := by group
        _ = g' * (x * d) * g'⁻¹ := by rw [h1, ← h3]; group
        _ = g' * x * (d * g'⁻¹) := by group
        _ = g' * x * g'⁻¹ * d := by rw [h2]; group
    have hgC : g ∈ Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hconj g hg x hx
      · intro hx
        have h := hconj g⁻¹ (B.inv_mem hg) _ hx
        have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
        rwa [e] at h
    have hgJ : g ∈ Subgroup.normalizer (Ja : Set G) := hBJ hg
    have hgN : g ∈ Subgroup.normalizer ((Ja ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff] at hgJ hgC ⊢
      intro x
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hgJ x, hgC x]
    rw [hKdef]
    exact y9x_normalizer_layer hgN
  have hKcy : CFSG.Open.IsKGroup ↥(cx y) := S8.isKGroup_cx hc.ctx hy1
  have hBcy : B ≤ cx y := isElemAbelian_le_centralizer hBel hyB
  have hrank : 3 ^ GLATwoLocalRank 3 ↥(cx y) ≤ Nat.card B := by
    rw [hBmax.2.1]
    exact Nat.pow_le_pow_right (by norm_num) (glaTwoLocalRank_subgroup_le (by norm_num : 1 < 3) (cx y))
  have hKclP : catalogIs (PSimple 3 K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) := by
    obtain ⟨eP⟩ := S9.nonempty_pSimple_equiv hp hKc hKcomp.2.2
    exact (catalogIs_congr eP.symm).1 hKcl
  obtain ⟨K', hK'c, hKK', hBK'⟩ := hin.single_std (cx y) a B K hKcy haB hBcy hBel
    hrank (by rw [S3.centralizer_zpowers]; exact hKc) hBK hKclP
  have hcl : closureIn K (GLAPLayer 3 (cx y)) = K' := closureIn_layer_eq_of_component hp hK'c hKc hKK'
  refine ⟨?_, ?_, ?_⟩
  · rw [hcl]; exact hK'c
  · rw [hcl]; exact hBK'
  · rw [hcl]
    have hK'le : K' ≤ cx y := hK'c.1
    have hKa : K ≤ cx a := (hKcomp.1.trans inf_le_right).trans hcsa
    exact glaPComponent_of_le hp hKc (le_inf hKK' hKa) (inf_le_inf_right _ hK'le)


private theorem y9x_comm_le_of_le_sup {p : ℕ} {J K : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (J : Set G)) (hKa : K ≤ cx a) (hKJ : K ≤ J)
    (hJ : J ≤ K ⊔ GLAPPrimeCoreOf p J) :
    (⁅J, Subgroup.zpowers a⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p J := by
  set O := GLAPPrimeCoreOf p J with hOdef
  have hJO : J ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p J
  have hconjO : ∀ g ∈ Subgroup.normalizer (O : Set G), ∀ o ∈ O, g * o * g⁻¹ ∈ O :=
    fun g hg o ho => (Subgroup.mem_normalizer_iff.1 hg o).1 ho
  have haNO : a ∈ Subgroup.normalizer (O : Set G) := normalizer_le_normalizer_glaPPrimeCoreOf p J haN
  let T : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (O : Set G) ∧ ⁅g, a⁆ ∈ O}
      mul_mem' := fun {g h} hg hh => ⟨Subgroup.mul_mem _ hg.1 hh.1, by
        have e : ⁅g * h, a⁆ = (g * ⁅h, a⁆ * g⁻¹) * ⁅g, a⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact O.mul_mem (hconjO g hg.1 _ hh.2) hg.2⟩
      one_mem' := ⟨Subgroup.one_mem _, by
        rw [show ⁅(1 : G), a⁆ = 1 by simp [commutatorElement_def]]
        exact O.one_mem⟩
      inv_mem' := fun {g} hg => ⟨Subgroup.inv_mem _ hg.1, by
        have e : ⁅g⁻¹, a⁆ = g⁻¹ * (⁅g, a⁆)⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hconjO g⁻¹ (Subgroup.inv_mem _ hg.1) _ (O.inv_mem hg.2)⟩ }
  have hKT : K ≤ T := fun k hk => by
    refine ⟨hJO (hKJ hk), ?_⟩
    have hka : k * a = a * k := Subgroup.mem_centralizer_singleton_iff.1 (hKa hk)
    rw [show ⁅k, a⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.2 hka]
    exact O.one_mem
  have hOT : O ≤ T := fun o ho => by
    refine ⟨Subgroup.le_normalizer ho, ?_⟩
    have e : ⁅o, a⁆ = o * (a * o⁻¹ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact O.mul_mem ho (hconjO a haNO _ (O.inv_mem ho))
  have hJT : J ≤ T := hJ.trans (sup_le hKT hOT)
  let U : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (O : Set G) ∧ ∀ j ∈ J, ⁅j, g⁆ ∈ O}
      mul_mem' := fun {g h} hg hh => ⟨Subgroup.mul_mem _ hg.1 hh.1, fun j hj => by
        have e : ⁅j, g * h⁆ = ⁅j, g⁆ * (g * ⁅j, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact O.mul_mem (hg.2 j hj) (hconjO g hg.1 _ (hh.2 j hj))⟩
      one_mem' := ⟨Subgroup.one_mem _, fun j _ => by
        rw [show ⁅j, (1 : G)⁆ = 1 by simp [commutatorElement_def]]
        exact O.one_mem⟩
      inv_mem' := fun {g} hg => ⟨Subgroup.inv_mem _ hg.1, fun j hj => by
        have e : ⁅j, g⁻¹⁆ = g⁻¹ * (⁅j, g⁆)⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hconjO g⁻¹ (Subgroup.inv_mem _ hg.1) _ (O.inv_mem (hg.2 j hj))⟩ }
  have haU : a ∈ U := ⟨haNO, fun j hj => (hJT hj).2⟩
  rw [Subgroup.commutator_le]
  intro j hj g hg
  exact (Subgroup.zpowers_le.2 haU hg).2 j hj


private theorem y9x_not_dvd_card_core {p : ℕ} (hp : p.Prime) (H : Subgroup G) {N : Subgroup G}
    (hN : N ≤ GLAPPrimeCoreOf p H) : ¬ p ∣ Nat.card ↥N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcopO : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p H)) := by
    have e : Nat.card ↥(GLAPPrimeCoreOf p H) = Nat.card ↥(GLAPPrimeCore p ↥H) :=
      Nat.card_congr (Subgroup.equivMapOfInjective (GLAPPrimeCore p ↥H) H.subtype
        Subtype.val_injective).toEquiv.symm
    rw [e]
    exact CFSG.pPrimeCore_coprime_card
  intro hdvd
  have hd : Nat.card ↥N ∣ Nat.card ↥(GLAPPrimeCoreOf p H) := Subgroup.card_dvd_of_le hN
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcopO (hdvd.trans hd)

private theorem y9x_B_le_normalizer_K {B Ja D K : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hDB : D ≤ B) (hBJ : B ≤ Subgroup.normalizer (Ja : Set G))
    (hKdef : K = GLALayer (Ja ⊓ Subgroup.centralizer (D : Set G))) :
    B ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  have hconj : ∀ g' ∈ B, ∀ x ∈ Subgroup.centralizer (D : Set G),
      g' * x * g'⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    intro g' hg' x hx
    refine Subgroup.mem_centralizer_iff.2 fun d hd => ?_
    have h1 : d * g' = g' * d := isElemAbelian_commute hBel (hDB hd) hg'
    have h2 : d * g'⁻¹ = g'⁻¹ * d := isElemAbelian_commute hBel (hDB hd) (B.inv_mem hg')
    have h3 : d * x = x * d := Subgroup.mem_centralizer_iff.1 hx d hd
    calc d * (g' * x * g'⁻¹) = (d * g') * x * g'⁻¹ := by group
      _ = g' * (x * d) * g'⁻¹ := by rw [h1, ← h3]; group
      _ = g' * x * (d * g'⁻¹) := by group
      _ = g' * x * g'⁻¹ * d := by rw [h2]; group
  have hgC : g ∈ Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj g hg x hx
    · intro hx
      have h := hconj g⁻¹ (B.inv_mem hg) _ hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at h
  have hgJ : g ∈ Subgroup.normalizer (Ja : Set G) := hBJ hg
  have hgN : g ∈ Subgroup.normalizer ((Ja ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hgJ hgC ⊢
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hgJ x, hgC x]
  rw [hKdef]
  exact y9x_normalizer_layer hgN


private theorem y9x_mem_sup_of_comm {A C : Subgroup G} (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) :
    ∀ x ∈ A ⊔ C, ∃ a ∈ A, ∃ c ∈ C, x = a * c := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ c ∈ C, x = a * c}
      mul_mem' := fun {x y} hx hy => by
        obtain ⟨a1, ha1, c1, hc1, rfl⟩ := hx
        obtain ⟨a2, ha2, c2, hc2, rfl⟩ := hy
        refine ⟨a1 * a2, A.mul_mem ha1 ha2, c1 * c2, C.mul_mem hc1 hc2, ?_⟩
        have e : c1 * a2 = a2 * c1 := (hAC a2 ha2 c1 hc1).symm
        calc a1 * c1 * (a2 * c2) = a1 * (c1 * a2) * c2 := by group
          _ = a1 * (a2 * c1) * c2 := by rw [e]
          _ = a1 * a2 * (c1 * c2) := by group
      one_mem' := ⟨1, A.one_mem, 1, C.one_mem, by group⟩
      inv_mem' := fun {x} hx => by
        obtain ⟨a, ha, c, hc, rfl⟩ := hx
        refine ⟨a⁻¹, A.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
        have e := congrArg (fun t => t⁻¹) (hAC a ha c hc)
        simp only [mul_inv_rev] at e
        rw [mul_inv_rev]
        exact e }
  have hle : A ⊔ C ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, C.one_mem, by group⟩) (fun c hc => ⟨1, A.one_mem, c, hc, by group⟩)
  intro x hx
  exact hle hx

private theorem y9x_normalizes_of_comm {D K : Subgroup G}
    (h : ∀ d ∈ D, ∀ k ∈ K, k * d = d * k) : D ≤ Subgroup.normalizer (K : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hfix : ∀ e ∈ D, ∀ k ∈ K, e * k * e⁻¹ = k := fun e he k hk => by
    rw [← h e he k hk]; group
  constructor
  · intro hx
    rw [hfix d hd x hx]
    exact hx
  · intro hx
    have h1 := hfix d⁻¹ (D.inv_mem hd) (d * x * d⁻¹) hx
    have e : d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x := by group
    rw [e] at h1
    rw [h1]
    exact hx

private theorem y9x_centralizes_of_cover {p : ℕ} (hp : p.Prime) {K J : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hpK : p ∣ Nat.card ↥K) (hKJ : K ≤ J) {c : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hcc : (⁅J, Subgroup.zpowers c⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p J) :
    ∀ k ∈ K, k * c = c * k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm_mem : ∀ k ∈ K, ⁅k, c⁆ ∈ K ⊓ GLAPPrimeCoreOf p J := by
    intro k hk
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : c * k⁻¹ * c⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hcN k⁻¹).1 (K.inv_mem hk)
      have h2 := K.mul_mem hk h1
      have e : ⁅k, c⁆ = k * (c * k⁻¹ * c⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e]
      exact h2
    · exact hcc (Subgroup.commutator_mem_commutator (hKJ hk) (Subgroup.mem_zpowers c))
  have hNnorm : ∀ n ∈ K ⊓ GLAPPrimeCoreOf p J, ∀ k ∈ K,
      k * n * k⁻¹ ∈ K ⊓ GLAPPrimeCoreOf p J := by
    intro n hn k hk
    refine Subgroup.mem_inf.2 ⟨K.mul_mem (K.mul_mem hk hn.1) (K.inv_mem hk), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p J (hKJ hk)) n).1 hn.2
  have hcentN := y9x_normal_central hq inf_le_left hNnorm hpK
    (y9x_not_dvd_card_core hp J inf_le_right)
  have hz : ∀ k1 ∈ K, ∀ k' ∈ K, ⁅k1, c⁆ * k' = k' * ⁅k1, c⁆ := by
    intro k1 hk1 k' hk'
    exact (hcentN _ (hcomm_mem k1 hk1) k' hk').symm
  exact y9x_centralizes_of_comm hq hcN hz

section SylowPointwise

open scoped Pointwise

private def y9x_basic_sylowOf {p : ℕ} {H R : Subgroup G} (hR : IsPGroup p R) (hRH : R ≤ H)
    (hmax : ∀ Y : Subgroup G, Y ≤ H → IsPGroup p Y → R ≤ Y → Y = R) : Sylow p ↥H where
  toSubgroup := R.subgroupOf H
  isPGroup' := hR.comap_subtype
  is_maximal' := fun {Y} hY hle => by
    have hYmap : Y.map H.subtype = R := hmax _ (Subgroup.map_subtype_le Y) (hY.map H.subtype) (by
      intro x hx
      rw [Subgroup.mem_map]
      exact ⟨⟨x, hRH hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩)
    ext z
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      rw [← hYmap]
      exact Subgroup.mem_map.2 ⟨z, hz, rfl⟩
    · intro hz
      rw [← hYmap] at hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz
      have hwz' : w = z := Subtype.ext hwz
      rwa [hwz'] at hw

private theorem y9x_basic_maximal_of_card {p : ℕ} (hp : p.Prime) {H P : Subgroup G}
    (hP : IsPGroup p P) (hPH : P ≤ H) {m : ℕ} (hm : Nat.card H = Nat.card P * m)
    (hpm : Nat.Coprime p m) : ∀ Y : Subgroup G, Y ≤ H → IsPGroup p Y → P ≤ Y → Y = P := by
  intro Y hYH hY hPY
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hY.exists_card_eq
  obtain ⟨b, hb⟩ := hP.exists_card_eq
  have h1 : p ^ a ∣ p ^ b * m := by
    have := Subgroup.card_dvd_of_le hYH
    rwa [ha, hm, hb] at this
  have h2 : p ^ a ∣ p ^ b := Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left a hpm) h1
  have h3 : p ^ b ∣ p ^ a := by
    have := Subgroup.card_dvd_of_le hPY
    rwa [ha, hb] at this
  have hab : a = b :=
    le_antisymm ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h2)
      ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h3)
  exact (Subgroup.eq_of_le_of_card_ge hPY (le_of_eq (by rw [ha, hb, hab]))).symm

private theorem y9x_basic_exists_conj_le {p : ℕ} (hp : p.Prime) {H P Q : Subgroup G}
    (hP : IsPGroup p P) (hPH : P ≤ H) (hQ : IsPGroup p Q) (hQH : Q ≤ H) {m : ℕ}
    (hm : Nat.card H = Nat.card P * m) (hQc : Nat.card Q = Nat.card P) (hpm : Nat.Coprime p m) :
    ∃ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hmP := y9x_basic_maximal_of_card hp hP hPH hm hpm
  have hmQ := y9x_basic_maximal_of_card hp hQ hQH (by rw [hQc]; exact hm) hpm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H (y9x_basic_sylowOf hP hPH hmP) (y9x_basic_sylowOf hQ hQH hmQ)
  have hQ0 : ((y9x_basic_sylowOf hQ hQH hmQ : Sylow p ↥H) : Subgroup ↥H) =
      MulAut.conj g • ((y9x_basic_sylowOf hP hPH hmP : Sylow p ↥H) : Subgroup ↥H) := by
    rw [← hg]
    rfl
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  have hx' : (⟨x, hPH hx⟩ : ↥H) ∈ ((y9x_basic_sylowOf hP hPH hmP : Sylow p ↥H) : Subgroup ↥H) :=
    Subgroup.mem_subgroupOf.2 hx
  have hmem : MulAut.conj g (⟨x, hPH hx⟩ : ↥H) ∈
      ((y9x_basic_sylowOf hQ hQH hmQ : Sylow p ↥H) : Subgroup ↥H) := by
    rw [hQ0]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hx'
  have := Subgroup.mem_subgroupOf.1 hmem
  simpa [MulAut.conj_apply, mul_assoc] using this

private theorem y9x_basic_mem_normalizer_of_map_le {T : Subgroup G} {g : G}
    (h : T.map (MulAut.conj g).toMonoidHom ≤ T) : g ∈ Subgroup.normalizer (T : Set G) := by
  have hfin : T.map (MulAut.conj g).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge h (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : g * y * g⁻¹ ∈ T.map (MulAut.conj g).toMonoidHom := Subgroup.mem_map.2 ⟨y, hy, rfl⟩
    rwa [hfin] at this
  · intro hy
    rw [← hfin] at hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
    have : z = y := by simpa [MulAut.conj_apply] using hzy
    rwa [← this]



private theorem y9x_basic_covers_of_sylow {C O T : Subgroup G} (hOC : O ≤ C)
    (hCO : C ≤ Subgroup.normalizer (O : Set G)) (hT2 : IsPGroup 2 T) (hTO : T ≤ O)
    {m : ℕ} (hm : Nat.card O = Nat.card T * m) (hcop : Nat.Coprime 2 m) :
    (Subgroup.normalizer (T : Set G) ⊓ C) ⊔ O = C := by
  apply le_antisymm (sup_le inf_le_right hOC)
  intro c hc
  have hcO : c ∈ Subgroup.normalizer (O : Set G) := hCO hc
  have hTc : T.map (MulAut.conj c).toMonoidHom ≤ O := by
    rintro _ ⟨t, ht, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hcO t).1 (hTO ht)
  have hTc2 : IsPGroup 2 (T.map (MulAut.conj c).toMonoidHom) := hT2.map _
  have hTcc : Nat.card (T.map (MulAut.conj c).toMonoidHom) = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  obtain ⟨h, hhO, hconj⟩ := y9x_basic_exists_conj_le Nat.prime_two hT2 hTO hTc2 hTc hm hTcc hcop
  have hgC : c⁻¹ * h ∈ C := C.mul_mem (C.inv_mem hc) (hOC hhO)
  have hgT : T.map (MulAut.conj (c⁻¹ * h)).toMonoidHom ≤ T := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hs'⟩ := Subgroup.mem_map.1 (hconj t ht)
    have e : (MulAut.conj (c⁻¹ * h)) t = s := by
      have hs2 : c * s * c⁻¹ = h * t * h⁻¹ := hs'
      calc (MulAut.conj (c⁻¹ * h)) t = c⁻¹ * (h * t * h⁻¹) * c := by
            simp only [MulAut.conj_apply]; group
        _ = c⁻¹ * (c * s * c⁻¹) * c := by rw [hs2]
        _ = s := by group
    show (MulAut.conj (c⁻¹ * h)) t ∈ T
    rw [e]
    exact hs
  have hgN : c⁻¹ * h ∈ Subgroup.normalizer (T : Set G) := y9x_basic_mem_normalizer_of_map_le hgT
  have hc' : c = h * (c⁻¹ * h)⁻¹ := by group
  rw [hc']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hhO)
    (Subgroup.mem_sup_left ⟨Subgroup.inv_mem _ hgN, C.inv_mem hgC⟩)

end SylowPointwise

private theorem y9x_mem_sup_of_normalizes {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    ∀ x ∈ H ⊔ K, ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let T : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      mul_mem' := fun {x y} hx hy => by
        obtain ⟨h1, hh1, k1, hk1, rfl⟩ := hx
        obtain ⟨h2, hh2, k2, hk2, rfl⟩ := hy
        have hconj : h2⁻¹ * k1 * h2⁻¹⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.1 (hHK (H.inv_mem hh2)) k1).1 hk1
        refine ⟨h1 * h2, H.mul_mem hh1 hh2, (h2⁻¹ * k1 * h2⁻¹⁻¹) * k2, K.mul_mem hconj hk2, ?_⟩
        group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by group⟩
      inv_mem' := fun {x} hx => by
        obtain ⟨h, hh, k, hk, rfl⟩ := hx
        have hconjK : h * k⁻¹ * h⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.1 (hHK hh) k⁻¹).1 (K.inv_mem hk)
        refine ⟨h⁻¹, H.inv_mem hh, h * k⁻¹ * h⁻¹, hconjK, ?_⟩
        group }
  have hle : H ⊔ K ≤ T :=
    sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by group⟩) (fun k hk => ⟨1, H.one_mem, k, hk, by group⟩)
  intro x hx
  exact hle hx

private theorem y9x_inf_eq_bot_of_pow {H O : Subgroup G} {p n : ℕ} (hp : p.Prime)
    (hH : Nat.card ↥H = p ^ n) (hO : ¬ p ∣ Nat.card ↥O) : H ⊓ O = ⊥ := by
  have hd : Nat.card ↥(H ⊓ O) ∣ Nat.card ↥H := Subgroup.card_dvd_of_le inf_le_left
  have hd2 : Nat.card ↥(H ⊓ O) ∣ Nat.card ↥O := Subgroup.card_dvd_of_le inf_le_right
  rw [hH] at hd
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hj0 : j = 0 := by
    by_contra hne
    apply hO
    have hpj : p ∣ Nat.card ↥(H ⊓ O) := by
      rw [hjeq]
      exact dvd_pow_self p hne
    exact hpj.trans hd2
  rw [hj0, pow_zero] at hjeq
  exact Subgroup.eq_bot_of_card_eq _ hjeq


private theorem y9x_mem_normalizer_sup {S O : Subgroup G} {g : G}
    (hgO : g ∈ Subgroup.normalizer (O : Set G)) (hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S ⊔ O) :
    g ∈ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := by
  apply y9x_basic_mem_normalizer_of_map_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact hgS s hs
  · rintro _ ⟨o, ho, rfl⟩
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hgO o).1 ho)

theorem gamma_not_cent (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {D₀ K : Subgroup G} (hstd : GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K) {y : G} (hy : y ∈ D₀)
    (hya : y ∉ Subgroup.zpowers a) {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hSD : (⁅S, D₀⁆ : Subgroup G) = S) (hSy : S ≤ cx y) (hSB : B ≤ Subgroup.normalizer (S : Set G))
    (hSN : S ≤ Subgroup.normalizer ((closureIn K (GLAPLayer 3 (cx y)) : Subgroup G) : Set G)) :
    ¬ (⁅closureIn K (GLAPLayer 3 (cx y)), Subgroup.zpowers a⁆ : Subgroup G) ≤
      GLAPPrimeCoreOf 3 (closureIn K (GLAPLayer 3 (cx y))) := by
  intro hcc
  have hstd' := hstd
  obtain ⟨⟨hD₀B, hD₀el, hD₀c, haD₀, hKdef, hKcomp, hDeq⟩, -⟩ := hstd
  have hBmax : GLAIsBmax 3 B := hSStar.1
  have hBel : IsElemAbelian 3 B := hBmax.1
  have haB : a ∈ B := hSStar.2.1
  have hyB : y ∈ B := hD₀B hy
  have hy1 : y ≠ 1 := fun h1 => hya (h1 ▸ Subgroup.one_mem _)
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hclK := hclaim D₀ K hstd'
  have hK3 : 3 ∣ Nat.card ↥K := y9x_three_dvd_of_stdf hin.stdf hq hclK
  have hJa : IsComponentOf (Jpart 3 (Ipart 3 L b) a) (cx a) := hSStar.2.2.2.1
  have hBJ : B ≤ Subgroup.normalizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h ha).2
  have hD₀eqa : D₀ = Dgrp a y := by
    obtain ⟨hDle, -, hDcard⟩ := card_Dgrp hBel hp3 hyB haB ha1 hya
    have hDy : Dgrp y a ≤ D₀ := (Subgroup.closure_le D₀).2 (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hy
      · exact haD₀)
    have h1 : Dgrp y a = D₀ := Subgroup.eq_of_le_of_card_ge hDy (by rw [hD₀c, hDcard])
    rw [← h1]
    unfold Dgrp
    rw [Set.pair_comm]
  obtain ⟨hA, hBN, hC⟩ := y9x_std_core hc hin hBmax hJa hBJ haB ha1 hyB hy1 hD₀B hD₀eqa
    hKdef hKcomp hK3 hclK
  obtain ⟨F, T, E, -, -, -, -, -, -, -, -, -, -, hEK, hEel, hEc, hZ⟩ := hin.stdf K hq hclK
  set Ks := closureIn K (GLAPLayer 3 (cx y)) with hKs
  have hKK : K ≤ Ks := le_closureIn_self K (GLAPLayer 3 (cx y))
  have hKsC : Ks ≤ cx y := hA.1
  have hKsSub : IsSubnormal Ks (cx y) := hA.2.1
  have hDK : ∀ d ∈ D₀, ∀ k ∈ K, k * d = d * k := by
    intro d hd k hk
    have hdC : d ∈ Subgroup.centralizer (K : Set G) := by
      rw [hDeq] at hd
      exact (Subgroup.mem_inf.1 hd).2
    exact Subgroup.mem_centralizer_iff.1 hdC k hk
  have hBcy : B ≤ cx y := isElemAbelian_le_centralizer hBel hyB
  have hDC : D₀ ≤ cx y := fun d hd => hBcy (hD₀B hd)
  have hOodd : Odd (Nat.card ↥(GLAPPrimeCoreOf 3 (cx y))) := odd_core_of_caseU hc h hU hyB
  have hO3 : ¬ 3 ∣ Nat.card ↥(GLAPPrimeCoreOf 3 (cx y)) :=
    y9x_not_dvd_card_core hp3 (cx y) le_rfl
  have hOC : GLAPPrimeCoreOf 3 (cx y) ≤ cx y := Subgroup.map_subtype_le _
  have hCO : cx y ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 (cx y) : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf 3 (cx y)
  have hNO : GLAPPrimeCoreOf 3 Ks ≤ GLAPPrimeCoreOf 3 (cx y) := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp3 hKsSub]
    exact inf_le_right
  have hcc' : ∀ k ∈ Ks, ⁅k, a⁆ ∈ GLAPPrimeCoreOf 3 (cx y) := fun k hk =>
    hNO (hcc (Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers a)))
  set O := GLAPPrimeCoreOf 3 (cx y) with hOdef
  set M : Subgroup G := Subgroup.normalizer (Ks : Set G) ⊓ cx y with hMdef
  have hMN : ∀ m ∈ M, m ∈ Subgroup.normalizer (Ks : Set G) := fun m hm => (Subgroup.mem_inf.1 hm).1
  have hMC : ∀ m ∈ M, m ∈ cx y := fun m hm => (Subgroup.mem_inf.1 hm).2
  have hMK : ∀ m ∈ M, ∀ k ∈ Ks, m * k * m⁻¹ ∈ Ks := fun m hm k hk =>
    (Subgroup.mem_normalizer_iff.1 (hMN m hm) k).1 hk
  have hCon : ∀ c ∈ cx y, ∀ o ∈ O, c * o * c⁻¹ ∈ O := fun c hc o ho =>
    (Subgroup.mem_normalizer_iff.1 (hCO hc) o).1 ho
  let W : Subgroup G :=
    { carrier := {g | g ∈ M ∧ ∀ k ∈ Ks, ⁅k, g⁆ ∈ O}
      mul_mem' := fun {g h} hg hh => ⟨M.mul_mem hg.1 hh.1, fun k hk => by
        have e : ⁅k, g * h⁆ = ⁅k, g⁆ * (g * ⁅k, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact O.mul_mem (hg.2 k hk) (hCon g (hMC g hg.1) _ (hh.2 k hk))⟩
      one_mem' := ⟨M.one_mem, fun k _ => by
        rw [show ⁅k, (1 : G)⁆ = 1 by simp [commutatorElement_def]]
        exact O.one_mem⟩
      inv_mem' := fun {g} hg => ⟨M.inv_mem hg.1, fun k hk => by
        have e : ⁅k, g⁻¹⁆ = g⁻¹ * (⁅k, g⁆)⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hCon g⁻¹ ((cx y).inv_mem (hMC g hg.1)) _ (O.inv_mem (hg.2 k hk))⟩ }
  have hWconj : ∀ c ∈ M, ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    refine ⟨M.mul_mem (M.mul_mem hc hw.1) (M.inv_mem hc), fun k hk => ?_⟩
    have hck : c⁻¹ * k * c⁻¹⁻¹ ∈ Ks := hMK c⁻¹ (M.inv_mem hc) k hk
    have e : ⁅k, c * w * c⁻¹⁆ = c * ⁅c⁻¹ * k * c⁻¹⁻¹, w⁆ * c⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hCon c (hMC c hc) _ (hw.2 _ hck)
  let V : Subgroup G :=
    { carrier := {d | d ∈ M ∧ ∀ s ∈ S, ⁅s, d⁆ ∈ W}
      mul_mem' := fun {d e} hd he => ⟨M.mul_mem hd.1 he.1, fun s hs => by
        have ee : ⁅s, d * e⁆ = ⁅s, d⁆ * (d * ⁅s, e⁆ * d⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [ee]
        exact W.mul_mem (hd.2 s hs) (hWconj d hd.1 _ (he.2 s hs))⟩
      one_mem' := ⟨M.one_mem, fun s _ => by
        rw [show ⁅s, (1 : G)⁆ = 1 by simp [commutatorElement_def]]
        exact W.one_mem⟩
      inv_mem' := fun {d} hd => ⟨M.inv_mem hd.1, fun s hs => by
        have ee : ⁅s, d⁻¹⁆ = d⁻¹ * (⁅s, d⁆)⁻¹ * d⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [ee]
        exact hWconj d⁻¹ (M.inv_mem hd.1) _ (W.inv_mem (hd.2 s hs))⟩ }
  have hSM : ∀ s ∈ S, s ∈ M := fun s hs => ⟨hSN hs, hSy hs⟩
  have haM : a ∈ M := ⟨hBN haB, Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel haB hyB)⟩
  have hyM : y ∈ M := ⟨hBN hyB, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have haW : a ∈ W := ⟨haM, fun k hk => hcc' k hk⟩
  have hyV : y ∈ V := ⟨hyM, fun s hs => by
    have h1 : ⁅s, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 (hSy hs))
    rw [h1]
    exact W.one_mem⟩
  have haV : a ∈ V := ⟨haM, fun s hs => by
    rw [commutatorElement_def s a]
    exact W.mul_mem (hWconj s (hSM s hs) a haW) (W.inv_mem haW)⟩
  have hDV : D₀ ≤ V := by
    rw [hD₀eqa]
    exact (Subgroup.closure_le V).2 (Set.insert_subset_iff.2 ⟨haV, Set.singleton_subset_iff.2 hyV⟩)
  have hSW : S ≤ W := by
    have h1 : ⁅S, D₀⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro s hs d hd
      exact (hDV hd).2 s hs
    rw [hSD] at h1
    exact h1
  have hSK : ∀ s ∈ S, ∀ k ∈ Ks, ⁅k, s⁆ ∈ O := fun s hs k hk => (hSW hs).2 k hk
  have hKsSO : ∀ k ∈ Ks, k ∈ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := fun k hk =>
    y9x_mem_normalizer_sup (hCO (hKsC hk)) (fun s hs => by
      have e : k * s * k⁻¹ = ⁅k, s⁆ * s := by simp only [commutatorElement_def]; group
      rw [e]
      exact (S ⊔ O).mul_mem (Subgroup.mem_sup_right (hSK s hs k hk)) (Subgroup.mem_sup_left hs))
  have hD₀SO : ∀ d ∈ D₀, d ∈ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := fun d hd =>
    y9x_mem_normalizer_sup (hCO (hDC hd)) (fun s hs =>
      Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hSB (hD₀B hd)) s).1 hs))
  have hOSO : ∀ o ∈ O, o ∈ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := fun o ho =>
    y9x_mem_normalizer_sup (Subgroup.le_normalizer ho) (fun s hs => by
      have hsoO : s * o⁻¹ * s⁻¹ ∈ O := hCon s (hSy hs) o⁻¹ (O.inv_mem ho)
      have e : o * s * o⁻¹ = (o * (s * o⁻¹ * s⁻¹)) * s := by group
      rw [e]
      exact (S ⊔ O).mul_mem (Subgroup.mem_sup_right (O.mul_mem ho hsoO)) (Subgroup.mem_sup_left hs))
  have hDEcomm : ∀ d ∈ D₀, ∀ e ∈ E, d * e = e * d := fun d hd e he => (hDK d hd e (hEK he)).symm
  have hEnorm : E ≤ Subgroup.normalizer (D₀ : Set G) :=
    y9x_normalizes_of_comm (fun e he d hd => hDEcomm d hd e he)
  have hD₀E : D₀ ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxD, hxE⟩ := Subgroup.mem_inf.1 hx
    have hx3 : x ^ 3 = 1 := hBel.2 x (hD₀B hxD)
    have hxZ : x ∈ K ⊓ Subgroup.centralizer (K : Set G) :=
      Subgroup.mem_inf.2 ⟨hEK hxE, Subgroup.mem_centralizer_iff.2 fun k hk => hDK x hxD k hk⟩
    rw [Subgroup.mem_bot]
    exact hZ x hxZ hx3
  have hAel : IsElemAbelian 3 (D₀ ⊔ E) :=
    CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_sup_of_commute hD₀el hEel
      (fun d hd => Subgroup.mem_centralizer_iff.2 fun e he => (hDEcomm d hd e he).symm)
  have hAcard : Nat.card ↥(D₀ ⊔ E) = 3 ^ 5 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hEnorm
    rw [hD₀E, Subgroup.card_bot, hD₀c, hEc] at h
    rw [mul_one] at h
    rw [h]
    norm_num
  have hAC : D₀ ⊔ E ≤ cx y := sup_le hDC (fun e he => hKsC (hKK (hEK he)))
  have hAN : D₀ ⊔ E ≤ Subgroup.normalizer (O : Set G) := fun x hx => hCO (hAC hx)
  have hAO : (D₀ ⊔ E) ⊓ O = ⊥ := y9x_inf_eq_bot_of_pow hp3 hAcard hO3
  set X : Subgroup G := (D₀ ⊔ E) ⊔ O with hXdef
  have hXC : X ≤ cx y := sup_le hAC hOC
  have hX_card : Nat.card ↥X = Nat.card ↥O * 3 ^ 5 := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := O) (B := D₀ ⊔ E) hAN
    rw [inf_comm, hAO, Subgroup.card_bot, hAcard, mul_one, sup_comm] at h
    rw [hXdef]
    exact h
  have hSC : S ≤ cx y := hSy
  have hSNO : S ≤ Subgroup.normalizer (O : Set G) := fun s hs => hCO (hSC hs)
  have hSO_card : Nat.card ↥(S ⊔ O) = Nat.card ↥S * Nat.card ↥O := by
    have hSOinf : O ⊓ S = ⊥ := by
      rw [inf_comm]
      obtain ⟨k, hk⟩ := hS2.exists_card_eq
      exact y9x_inf_eq_bot_of_pow Nat.prime_two hk hOodd.not_two_dvd_nat
    have h := card_sup_mul_card_inf_of_le_normalizer (A := O) (B := S) hSNO
    rw [hSOinf, Subgroup.card_bot, mul_one] at h
    rw [sup_comm, h]
    ring
  have hcop2 : Nat.Coprime 2 (Nat.card ↥O) := Nat.coprime_two_left.2 hOodd
  set Lam : Subgroup G := (D₀ ⊔ E) ⊔ (S ⊔ O) with hLamdef
  have hLamN : Lam ≤ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) :=
    sup_le (sup_le (fun d hd => hD₀SO d hd) (fun e he => hKsSO e (hKK (hEK he))))
      (Subgroup.le_normalizer)
  have hSOLam : S ⊔ O ≤ Lam := le_sup_right
  have hcov := y9x_basic_covers_of_sylow hSOLam hLamN hS2 le_sup_left hSO_card hcop2
  have hXLam : X ≤ Lam := sup_le (le_sup_left) (le_sup_right.trans le_sup_right)
  have hXQ : X ≤ (X ⊓ Subgroup.normalizer (S : Set G)) ⊔ O := by
    intro x hx
    have hx' : x ∈ Lam := hXLam hx
    rw [← hcov] at hx'
    obtain ⟨h, hh, n, hn, hxhn⟩ := y9x_mem_sup_of_normalizes
      (H := Subgroup.normalizer (S : Set G) ⊓ Lam) (K := S ⊔ O)
      (fun h' hh' => hLamN (Subgroup.mem_inf.1 hh').2) x hx'
    obtain ⟨s, hs, o, ho, hno⟩ := y9x_mem_sup_of_normalizes hSNO n hn
    have hm : h * s ∈ X ⊓ Subgroup.normalizer (S : Set G) := by
      refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mul_mem _ hh.1 (Subgroup.le_normalizer hs)⟩
      have hxo : x * o⁻¹ = h * s := by
        rw [hxhn, hno]
        group
      rw [← hxo]
      exact X.mul_mem hx (X.inv_mem (Subgroup.mem_sup_right ho))
    have hxeq : x = (h * s) * o := by
      rw [hxhn, hno]
      group
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right ho)
  set Q : Subgroup G := X ⊓ Subgroup.normalizer (S : Set G) with hQdef
  have hQN : Q ≤ Subgroup.normalizer (O : Set G) := fun q hq => hCO (hXC hq.1)
  have hQO : O ⊔ Q = X := by
    apply le_antisymm
    · exact sup_le (le_sup_right) inf_le_left
    · intro x hx
      rw [← sup_comm]
      exact hXQ hx
  have hQcard : Nat.card ↥Q = 3 ^ 5 * Nat.card ↥(O ⊓ Q) := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := O) (B := Q) hQN
    rw [hQO, hX_card] at h
    have hOpos : 0 < Nat.card ↥O := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hOpos
    rw [← h]
    ring
  have h3Q : 3 ^ 5 ∣ Nat.card ↥Q := ⟨Nat.card ↥(O ⊓ Q), hQcard⟩
  obtain ⟨P', hP'⟩ := Sylow.exists_subgroup_card_pow_prime 3 h3Q
  set P : Subgroup G := P'.map Q.subtype with hPdef
  have hPcard : Nat.card ↥P = 3 ^ 5 := by
    rw [hPdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective Q), hP']
  have hPQ : P ≤ Q := Subgroup.map_subtype_le _
  have hPX : P ≤ X := hPQ.trans inf_le_left
  have hPN : P ≤ Subgroup.normalizer (S : Set G) := hPQ.trans inf_le_right
  have hPO : P ⊓ O = ⊥ := y9x_inf_eq_bot_of_pow hp3 hPcard hO3
  have hPdec : ∀ p ∈ P, ∃ a' ∈ D₀ ⊔ E, ∃ o ∈ O, p = a' * o := by
    intro p hp'
    obtain ⟨a', ha', o, ho, hpo⟩ := y9x_mem_sup_of_normalizes hAN p (hPX hp')
    exact ⟨a', ha', o, ho, hpo⟩
  have hdecomp : ∀ a1 ∈ D₀ ⊔ E, ∀ o1 ∈ O, ∀ a2 ∈ D₀ ⊔ E, ∀ o2 ∈ O,
      ∃ o' ∈ O, a1 * o1 * (a2 * o2) = a1 * a2 * o' := by
    intro a1 _ o1 ho1 a2 ha2 o2 ho2
    refine ⟨(a2⁻¹ * o1 * a2⁻¹⁻¹) * o2,
      O.mul_mem (hCon a2⁻¹ ((cx y).inv_mem (hAC ha2)) o1 ho1) ho2, ?_⟩
    group
  have hPcomm : ∀ p1 ∈ P, ∀ p2 ∈ P, p1 * p2 = p2 * p1 := by
    intro p1 hp1 p2 hp2
    obtain ⟨a1, ha1, o1, ho1, rfl⟩ := hPdec p1 hp1
    obtain ⟨a2, ha2, o2, ho2, rfl⟩ := hPdec p2 hp2
    obtain ⟨o', ho', hu⟩ := hdecomp a1 ha1 o1 ho1 a2 ha2 o2 ho2
    obtain ⟨o'', ho'', hv⟩ := hdecomp a2 ha2 o2 ho2 a1 ha1 o1 ho1
    have hc12 : a1 * a2 = a2 * a1 := isElemAbelian_commute hAel ha1 ha2
    have hinv : (a1 * o1 * (a2 * o2))⁻¹ * (a2 * o2 * (a1 * o1)) ∈ O := by
      rw [hu, hv, ← hc12]
      have e : (a1 * a2 * o')⁻¹ * (a1 * a2 * o'') = o'⁻¹ * o'' := by group
      rw [e]
      exact O.mul_mem (O.inv_mem ho') ho''
    have hmemP : (a1 * o1 * (a2 * o2))⁻¹ * (a2 * o2 * (a1 * o1)) ∈ P :=
      P.mul_mem (P.inv_mem (P.mul_mem hp1 hp2)) (P.mul_mem hp2 hp1)
    have hmem : (a1 * o1 * (a2 * o2))⁻¹ * (a2 * o2 * (a1 * o1)) ∈ P ⊓ O :=
      Subgroup.mem_inf.2 ⟨hmemP, hinv⟩
    rw [hPO, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.1 hmem
  have hPexp : ∀ p ∈ P, p ^ 3 = 1 := by
    intro p hp'
    obtain ⟨a', ha', o, ho, rfl⟩ := hPdec p hp'
    obtain ⟨o1, ho1, h2⟩ := hdecomp a' ha' o ho a' ha' o ho
    have hA3 : a' ^ 3 = 1 := hAel.2 a' ha'
    have hconj : a'⁻¹ * o1 * a' ∈ O := by
      have := hCon a'⁻¹ ((cx y).inv_mem (hAC ha')) o1 ho1
      rwa [inv_inv] at this
    have h3 : (a' * o) ^ 3 = a' ^ 3 * ((a'⁻¹ * o1 * a') * o) := by
      have e1 : (a' * o) ^ 3 = (a' * a' * o1) * (a' * o) := by
        rw [pow_three', ← h2]
      have e2 : (a' * a' * o1) * (a' * o) = a' ^ 3 * ((a'⁻¹ * o1 * a') * o) := by
        rw [pow_three']
        simp only [mul_assoc, mul_inv_cancel_left]
      exact e1.trans e2
    have hmemO : (a' * o) ^ 3 ∈ O := by
      rw [h3, hA3, one_mul]
      exact O.mul_mem hconj ho
    have hmem : (a' * o) ^ 3 ∈ P ⊓ O := Subgroup.mem_inf.2 ⟨P.pow_mem hp' 3, hmemO⟩
    rw [hPO, Subgroup.mem_bot] at hmem
    exact hmem
  have hPel : IsElemAbelian 3 P :=
    ⟨⟨⟨fun x y => Subtype.ext (hPcomm x.1 x.2 y.1 y.2)⟩⟩, fun x hx => hPexp x hx⟩
  have hbound := card_le_pow_glaTwoLocalRank hp3 hPel hSne hS2 hPN
  rw [hPcard, hU.rank] at hbound
  norm_num at hbound

theorem gamma_cent_Kstar (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {D₀ K : Subgroup G} (hstd : GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K) {y : G} (hy : y ∈ D₀)
    (hya : y ∉ Subgroup.zpowers a) {c : G} (hcB : c ∈ B)
    (hcN : c ∈ Subgroup.normalizer ((closureIn K (GLAPLayer 3 (cx y)) : Subgroup G) : Set G))
    (hcc : (⁅closureIn K (GLAPLayer 3 (cx y)), Subgroup.zpowers c⁆ : Subgroup G) ≤
      GLAPPrimeCoreOf 3 (closureIn K (GLAPLayer 3 (cx y)))) : c ∈ D₀ := by
  have hstd' := hstd
  obtain ⟨⟨hD₀B, -, -, -, hKdef, hKcomp, hDeq⟩, -⟩ := hstd
  have hq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hBel : IsElemAbelian 3 B := hSStar.1.1
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hK3 : 3 ∣ Nat.card ↥K := y9x_three_dvd_of_stdf hin.stdf hq (hclaim D₀ K hstd')
  have hBJ : B ≤ Subgroup.normalizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h ha).2
  have hcN' : c ∈ Subgroup.normalizer (K : Set G) :=
    y9x_B_le_normalizer_K hBel hD₀B hBJ hKdef hcB
  have hKK : K ≤ closureIn K (GLAPLayer 3 (cx y)) := le_closureIn_self K (GLAPLayer 3 (cx y))
  have hcomm_mem : ∀ k ∈ K,
      ⁅k, c⁆ ∈ K ⊓ GLAPPrimeCoreOf 3 (closureIn K (GLAPLayer 3 (cx y))) := by
    intro k hk
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : c * k⁻¹ * c⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hcN' k⁻¹).1 (K.inv_mem hk)
      have h2 := K.mul_mem hk h1
      have e : ⁅k, c⁆ = k * (c * k⁻¹ * c⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e]
      exact h2
    · exact hcc (Subgroup.commutator_mem_commutator (hKK hk) (Subgroup.mem_zpowers c))
  have hNnorm : ∀ n ∈ K ⊓ GLAPPrimeCoreOf 3 (closureIn K (GLAPLayer 3 (cx y))),
      ∀ k ∈ K, k * n * k⁻¹ ∈ K ⊓ GLAPPrimeCoreOf 3 (closureIn K (GLAPLayer 3 (cx y))) := by
    intro n hn k hk
    refine Subgroup.mem_inf.2 ⟨K.mul_mem (K.mul_mem hk hn.1) (K.inv_mem hk), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf 3 (closureIn K (GLAPLayer 3 (cx y))) (hKK hk)) n).1 hn.2
  have hcentN := y9x_normal_central hq inf_le_left hNnorm hK3
    (y9x_not_dvd_card_core hp3 _ inf_le_right)
  have hz : ∀ k1 ∈ K, ∀ k' ∈ K, ⁅k1, c⁆ * k' = k' * ⁅k1, c⁆ := by
    intro k1 hk1 k' hk'
    exact (hcentN _ (hcomm_mem k1 hk1) k' hk').symm
  have hcent : ∀ k ∈ K, k * c = c * k := y9x_centralizes_of_comm hq hcN' hz
  rw [hDeq]
  exact Subgroup.mem_inf.2 ⟨hcB, Subgroup.mem_centralizer_iff.2 fun k hk => hcent k hk⟩

theorem gamma_neighbor_exists (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x)
    (ha1 : a ≠ 1) (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i)) :
    ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      ∃ (y : G) (J : Subgroup G), GLASHat 3 B y J ∧ GLANeighbor 3 a y J D₀ K := by
  intro D₀ K hstd
  have hp : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hD₀B, hD₀el, hD₀c, haD₀, -, -, -⟩ := hstd.1
  obtain ⟨y, hyD₀, hya, S, hS2, hSne, hSD, hSy, hSB⟩ := gamma_yS hc hSStar.1 hD₀B hD₀el hD₀c haD₀ ha1
  obtain ⟨hKs, hKB, hKcomp⟩ := std_single hc hin h hU ha ha1 hSStar hclaim hstd hyD₀ hya
  have hSN := gamma_S_norm hc hin h hU ha ha1 hSStar hclaim hstd hyD₀ hya hS2 hSne hSD hSy hSB
  have hnc := gamma_not_cent hc hin h hU ha ha1 hSStar hclaim hstd hyD₀ hya hS2 hSne hSD hSy hSB hSN
  have hy1 : y ≠ 1 := fun h1 => hya (h1 ▸ Subgroup.one_mem _)
  have hyB : y ∈ B := hD₀B hyD₀
  have hBel : IsElemAbelian 3 B := hSStar.1.1
  have hKcx : closureIn K (GLAPLayer 3 (cx y)) ≤ cx y := hKs.1
  have hay3 : a ^ 3 = 1 := hBel.2 a (hD₀B haD₀)
  have hyy3 : y ^ 3 = 1 := hBel.2 y hyB
  have hay' : a ∉ Subgroup.zpowers y := fun hm => by
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers y := Subgroup.zpowers_le.2 hm
    have hcard : Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers a) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hyy3 hy1, orderOf_eq_prime hay3 ha1]
    exact hya (Subgroup.eq_of_le_of_card_ge hle hcard ▸ Subgroup.mem_zpowers y)
  refine ⟨y, closureIn K (GLAPLayer 3 (cx y)), ⟨hSStar.1, hyB, hy1, hKcx, hKs, fun b' => ⟨?_, ?_⟩⟩,
    ⟨?_, ?_, hnc⟩⟩
  · rintro ⟨hb'B, hb'N, hb'c⟩
    have hb'D₀ : b' ∈ D₀ :=
      gamma_cent_Kstar hc hin h hU ha ha1 hSStar hclaim hstd hyD₀ hya hb'B hb'N hb'c
    by_contra hb'y
    have hb'1 : b' ≠ 1 := fun h1 => hb'y (h1 ▸ Subgroup.one_mem _)
    have hb'3 : b' ^ 3 = 1 := hBel.2 b' hb'B
    have hyb' : y ∉ Subgroup.zpowers b' := fun hm => hb'y (by
      have hle : Subgroup.zpowers y ≤ Subgroup.zpowers b' := Subgroup.zpowers_le.2 hm
      have hcard : Nat.card (Subgroup.zpowers b') ≤ Nat.card (Subgroup.zpowers y) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hyy3 hy1, orderOf_eq_prime hb'3 hb'1]
      exact Subgroup.eq_of_le_of_card_ge hle hcard ▸ Subgroup.mem_zpowers b')
    obtain ⟨hDle, -, hDcard⟩ := card_Dgrp hD₀el hp hyD₀ hb'D₀ hb'1 hyb'
    have hDeq : Dgrp y b' = D₀ := Subgroup.eq_of_le_of_card_ge hDle (by rw [hD₀c, hDcard])
    have hyc : y ∈ centModSubgroup 3 (closureIn K (GLAPLayer 3 (cx y))) :=
      centMod_iff.1 (centMod_zpowers_of_le hKcx (Subgroup.mem_zpowers y))
    have hb'c' : b' ∈ centModSubgroup 3 (closureIn K (GLAPLayer 3 (cx y))) := centMod_iff.1 ⟨hb'N, hb'c⟩
    have haC : a ∈ centModSubgroup 3 (closureIn K (GLAPLayer 3 (cx y))) := by
      have : Dgrp y b' ≤ centModSubgroup 3 (closureIn K (GLAPLayer 3 (cx y))) :=
        (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hyc, Set.singleton_subset_iff.2 hb'c'⟩)
      exact this (hDeq ▸ haD₀)
    exact hnc (centMod_iff.2 haC).2
  · intro hb'
    exact centMod_zpowers_of_le hKcx hb' |> fun hc' => ⟨Subgroup.zpowers_le.2 hyB hb', hc'.1, hc'.2⟩
  · have hDle : Dgrp a y ≤ D₀ := (Subgroup.closure_le _).2 (Set.insert_subset_iff.2
      ⟨haD₀, Set.singleton_subset_iff.2 hyD₀⟩)
    obtain ⟨-, -, hDcard⟩ := card_Dgrp hD₀el hp haD₀ hyD₀ hy1 hay'
    exact (Subgroup.eq_of_le_of_card_ge hDle (by rw [hD₀c, hDcard])).symm
  · exact le_of_eq (closureIn_eq_iSup_gLBConj K (GLAPLayer 3 (cx y)))

theorem neighbor_data (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {y : G} {J : Subgroup G} (hnb : GLAIsNeighborOf 3 B a (Jpart 3 (Ipart 3 L b) a) y J) :
    ∃ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K ∧ y ∈ D₀ ∧
      y ∉ Subgroup.zpowers a ∧ J = closureIn K (GLAPLayer 3 (cx y)) ∧ K ≤ J ∧
      GLAPComponent 3 (J ⊓ cx a) K ∧ B ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨hSHat, D, K, hstd, hnbr⟩ := hnb
  have hstd' := hstd
  obtain ⟨hDcl, hJsup, -⟩ := hnbr
  obtain ⟨hBmax, hyB, hy1, -, hJc, -⟩ := hSHat
  have hBel : IsElemAbelian 3 B := hBmax.1
  have hJa : IsComponentOf (Jpart 3 (Ipart 3 L b) a) (cx a) := hSStar.2.2.2.1
  have hBJ : B ≤ Subgroup.normalizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h ha).2
  obtain ⟨⟨hDB, hDel, hDc, haD, hKdef, hKcomp, hDeq⟩, -⟩ := hstd
  have haB : a ∈ B := hDB haD
  have hclK := hclaim D K hstd'
  have hK3 : 3 ∣ Nat.card ↥K := y9x_three_dvd_of_stdf hin.stdf hKcomp.2.2 hclK
  obtain ⟨hA, hB', hC⟩ :=
    y9x_std_core hc hin hBmax hJa hBJ haB ha1 hyB hy1 hDB hDcl hKdef hKcomp hK3 hclK
  have hJK2 : J ≤ closureIn K (GLAPLayer 3 (cx y)) := by
    refine hJsup.trans ?_
    refine iSup₂_le fun g hg => ?_
    unfold closureIn
    exact le_iSup₂_of_le g⁻¹ (Subgroup.inv_mem _ hg) le_rfl
  have hJeq : J = closureIn K (GLAPLayer 3 (cx y)) := y9x_glaPComponent_eq_of_le hJc hA hJK2
  have hya : y ∉ Subgroup.zpowers a := by
    intro hm
    have hle : D ≤ Subgroup.zpowers a := by
      rw [hDcl]
      exact (Subgroup.closure_le _).2
        (Set.insert_subset_iff.2 ⟨Subgroup.mem_zpowers a, Set.singleton_subset_iff.2 hm⟩)
    have hcard := Subgroup.card_le_of_le hle
    have ha3 : a ^ 3 = 1 := hBel.2 a haB
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [hDc, Nat.card_zpowers, orderOf_eq_prime ha3 ha1] at hcard
    norm_num at hcard
  have hyD : y ∈ D := by
    rw [hDcl]
    exact Subgroup.subset_closure (by simp)
  refine ⟨D, K, hstd', hyD, hya, hJeq, ?_, ?_, ?_⟩
  · rw [hJeq]
    exact le_closureIn_self _ _
  · rw [hJeq]
    exact hC
  · rw [hJeq]
    exact hB'

theorem neighbor_norm (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {y : G} {J : Subgroup G} (hnb : GLAIsNeighborOf 3 B a (Jpart 3 (Ipart 3 L b) a) y J) :
    B ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, hN⟩ := neighbor_data hc hin h hU ha ha1 hSStar hclaim hnb
  exact hN

theorem neighbor_chev2 (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {y : G} {J : Subgroup G} (hnb : GLAIsNeighborOf 3 B a (Jpart 3 (Ipart 3 L b) a) y J) :
    IsChevSimple 2 (PSimple 3 J) := by
  obtain ⟨D₀, K₀, hstd₀, hyD₀, hya₀, hJeq, hKJ, hKa, hBJ⟩ :=
    neighbor_data hc hin h hU ha ha1 hSStar hclaim hnb
  obtain ⟨hBmax, hyB, hy1, -, hJc, -⟩ := hnb.1
  have hBel : IsElemAbelian 3 B := hBmax.1
  have hcatK := hclaim D₀ K₀ hstd₀
  obtain ⟨⟨hDB₀, -, -, haD₀, -, hKcomp₀, -⟩, -⟩ := hstd₀
  have haB : a ∈ B := hDB₀ haD₀
  have hKC : K₀ ≤ cx a := by
    intro k hk
    have hk' := hKcomp₀.1 hk
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk').2 a haD₀).symm)
  have haN : a ∈ Subgroup.normalizer ((J : Subgroup G) : Set G) := hBJ haB
  obtain ⟨-, D', K', -, hnbr⟩ := hnb
  obtain ⟨-, -, hnot⟩ := hnbr
  have hnotle : ¬ J ≤ K₀ ⊔ GLAPPrimeCoreOf 3 J := fun hle =>
    hnot (y9x_comm_le_of_le_sup haN hKC hKJ hle)
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hcaty : a ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel haB hyB)
  have ha3 : a ^ 3 = 1 := hBel.2 a haB
  have hqK : CFSG.Open.IsQuasisimple ↥K₀ := hKcomp₀.2.2
  have hcatKP : catalogIs (PSimple 3 K₀) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) := by
    obtain ⟨eP⟩ := S9.nonempty_pSimple_equiv hp3 hKa hqK
    exact (catalogIs_congr eP.symm).1 hcatK
  have hord : orderOf y = 3 := orderOf_eq_prime (hBel.2 y hyB) hy1
  exact hin.i14chev y a J K₀ (S8.isKGroup_cx hc.ctx hy1) hcaty ha3 hJc haN hKa hcatKP hnotle
    hU.rank.le (hc.stage8.2 rfl hU.rank y J hord hJc)

theorem neighbor_Bstar (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {y : G} {J : Subgroup G} (hnb : GLAIsNeighborOf 3 B a (Jpart 3 (Ipart 3 L b) a) y J)
    (hchev : IsChevSimple 2 (PSimple 3 J)) :
    ∃ B' : Subgroup G, GLAIsBmax 3 B' ∧ y ∈ B' ∧ B' ≤ Subgroup.normalizer (J : Set G) ∧
      CentModEqZpowers 3 B' J y ∧ ¬ IsSC 3 B' ∧ IsEssential 3 B' y := by
  obtain ⟨D₀, K₀, hstd₀, hyD₀, -, hJeq, hKJ, hKa, hBJ⟩ :=
    neighbor_data hc hin h hU ha ha1 hSStar hclaim hnb
  obtain ⟨hBmax, hyB, hy1, hJy, hJc, hGH⟩ := hnb.1
  have hBel : IsElemAbelian 3 B := hBmax.1
  have hcatK := hclaim D₀ K₀ hstd₀
  obtain ⟨⟨hD₀B, hD₀el, hD₀c, haD₀, hKdef₀, hKcomp₀, hDeq₀⟩, -⟩ := hstd₀
  have hqK : CFSG.Open.IsQuasisimple ↥K₀ := hKcomp₀.2.2
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hK3 : 3 ∣ Nat.card ↥K₀ := y9x_three_dvd_of_stdf hin.stdf hqK hcatK
  obtain ⟨F, T, E, hFK, hFel, hFc, hTK, hTp, hFN, hTF, hTQ8, -, hgex, -, -, -, hZ⟩ :=
    hin.stdf K₀ hqK hcatK
  obtain ⟨g, hgKC, hg3, hgF⟩ := hgex
  have hgK : g ∈ K₀ := (Subgroup.mem_inf.1 hgKC).1
  have hgC : g ∈ Subgroup.centralizer (F : Set G) := (Subgroup.mem_inf.1 hgKC).2
  have hDK : ∀ d ∈ D₀, ∀ k ∈ K₀, k * d = d * k := by
    intro d hd k hk
    have hdC : d ∈ Subgroup.centralizer (K₀ : Set G) := by
      rw [hDeq₀] at hd
      exact (Subgroup.mem_inf.1 hd).2
    exact Subgroup.mem_centralizer_iff.1 hdC k hk
  have hDF : ∀ d ∈ D₀, ∀ f ∈ F, d * f = f * d := fun d hd f hf => (hDK d hd f (hFK hf)).symm
  have hD₀F : D₀ ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxD, hxF⟩ := Subgroup.mem_inf.1 hx
    have hx3 : x ^ 3 = 1 := hBel.2 x (hD₀B hxD)
    have hxZ : x ∈ K₀ ⊓ Subgroup.centralizer (K₀ : Set G) :=
      Subgroup.mem_inf.2 ⟨hFK hxF, Subgroup.mem_centralizer_iff.2 fun k hk => hDK x hxD k hk⟩
    rw [Subgroup.mem_bot]
    exact hZ x hxZ hx3
  have hDNF : D₀ ≤ Subgroup.normalizer (F : Set G) :=
    y9x_normalizes_of_comm (fun d hd f hf => (hDF d hd f hf).symm)
  have hDNK : D₀ ≤ Subgroup.normalizer (K₀ : Set G) := y9x_normalizes_of_comm hDK
  have hDNT : D₀ ≤ Subgroup.normalizer (T : Set G) :=
    y9x_normalizes_of_comm (fun d hd t ht => hDK d hd t (hTK ht))
  have hB'card : Nat.card ↥(D₀ ⊔ F) = 3 ^ 4 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hDNF
    rw [inf_comm, hD₀F, Subgroup.card_bot, sup_comm, hFc, hD₀c] at h
    rw [mul_one] at h
    rw [h]
    norm_num
  have hel : IsElemAbelian 3 (D₀ ⊔ F) :=
    CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_sup_of_commute hD₀el hFel
      (fun d hd => Subgroup.mem_centralizer_iff.2 fun f hf => (hDF d hd f hf).symm)
  have hTne : T ≠ ⊥ := by
    intro h0
    apply hTF
    subst h0
    simp
  have hB'N : D₀ ⊔ F ≤ Subgroup.normalizer (T : Set G) := sup_le hDNT hFN
  have hBmax' : GLAIsBmax 3 (D₀ ⊔ F) :=
    ⟨hel, by rw [hB'card, hU.rank], T, hTne, hTp, hB'N⟩
  have hB'J : D₀ ⊔ F ≤ Subgroup.normalizer (J : Set G) :=
    sup_le (fun d hd => hBJ (hD₀B hd)) (fun f hf => Subgroup.le_normalizer (hKJ (hFK hf)))
  have hcent : CentModEqZpowers 3 (D₀ ⊔ F) J y := by
    intro c hc'
    constructor
    · intro hcCM
      obtain ⟨d, hd, f, hf, rfl⟩ := y9x_mem_sup_of_comm hDF c hc'
      have hcN : d * f ∈ Subgroup.normalizer (K₀ : Set G) :=
        Subgroup.mul_mem _ (hDNK hd) (Subgroup.le_normalizer (hFK hf))
      have hcentK : ∀ k ∈ K₀, k * (d * f) = (d * f) * k :=
        y9x_centralizes_of_cover hp3 hqK hK3 hKJ hcN hcCM.2
      have hfk : ∀ k ∈ K₀, k * f = f * k := by
        intro k hk
        have h1 := hcentK k hk
        rw [← mul_assoc, hDK d hd k hk, mul_assoc, mul_assoc] at h1
        exact mul_left_cancel h1
      have hf1 : f = 1 :=
        hZ f (Subgroup.mem_inf.2 ⟨hFK hf, Subgroup.mem_centralizer_iff.2 fun k hk => hfk k hk⟩)
          (hFel.2 f hf)
      rw [hf1, mul_one] at hcCM ⊢
      exact (hGH d).1 ⟨hD₀B hd, hcCM.1, hcCM.2⟩
    · intro hcy
      exact centMod_zpowers_of_le hJy hcy
  have hnsc : ¬ IsSC 3 (D₀ ⊔ F) := by
    rintro ⟨-, hcont⟩
    have hg1 : g ≠ 1 := fun h1 => hgF (h1 ▸ F.one_mem)
    have hgC' : g ∈ Subgroup.centralizer ((D₀ ⊔ F : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨d, hd, f, hf, rfl⟩ := y9x_mem_sup_of_comm hDF x hx
      have key : g * (d * f) = d * f * g := by
        calc g * (d * f) = (g * d) * f := by group
          _ = (d * g) * f := by rw [hDK d hd g hgK]
          _ = d * (g * f) := by group
          _ = d * (f * g) := by rw [Subgroup.mem_centralizer_iff.1 hgC f hf]
          _ = (d * f) * g := by group
      exact key.symm
    have hg3' : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    obtain ⟨d, hd, f, hf, hgdf⟩ := y9x_mem_sup_of_comm hDF g (hcont g hgC' hg3')
    have hdK : d ∈ K₀ := by
      have e : d = g * f⁻¹ := by
        rw [hgdf]; group
      rw [e]
      exact K₀.mul_mem hgK (K₀.inv_mem (hFK hf))
    have hdZ : d ∈ K₀ ⊓ Subgroup.centralizer (K₀ : Set G) :=
      Subgroup.mem_inf.2 ⟨hdK, Subgroup.mem_centralizer_iff.2 fun k hk => hDK d hd k hk⟩
    have hd1 : d = 1 := hZ d hdZ (hBel.2 d (hD₀B hd))
    apply hgF
    rw [hgdf, hd1, one_mul]
    exact hf
  have hess : IsEssential 3 (D₀ ⊔ F) y := by
    refine ⟨Subgroup.mem_sup_left hyD₀, hy1, T, fun t ht => hJy (hKJ (hTK ht)), hTp, hB'N,
      ?_, fun _ => hTQ8⟩
    intro h0
    exact hTF (eq_bot_iff.2 ((Subgroup.commutator_mono (le_refl T) le_sup_right).trans (le_of_eq h0)))
  exact ⟨D₀ ⊔ F, hBmax', Subgroup.mem_sup_left hyD₀, hB'J, hcent, hnsc, hess⟩

theorem neighbor_quasisimple (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x)
    (ha1 : a ≠ 1) (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {y : G} {J : Subgroup G} (hnb : GLAIsNeighborOf 3 B a (Jpart 3 (Ipart 3 L b) a) y J)
    (hchev : IsChevSimple 2 (PSimple 3 J)) : CFSG.Open.IsQuasisimple ↥J := by
  obtain ⟨B', hB', hyB', hN, hcent, hnsc, hess⟩ :=
    neighbor_Bstar hc hin h hU ha ha1 hSStar hclaim hnb hchev
  exact hc.stage9.2 B' y J hB' hyB' hnb.1.2.2.1 hnb.1.2.2.2.2.1 hN hcent hchev
    (Or.inr (Or.inr ⟨hnsc, hess⟩))

theorem neighbor_marking (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a))
    (hclaim : ∀ D₀ K : Subgroup G, GLAStdSub 3 B a (Jpart 3 (Ipart 3 L b) a) D₀ K →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i))
    {y : G} {J : Subgroup G} (hnb : GLAIsNeighborOf 3 B a (Jpart 3 (Ipart 3 L b) a) y J)
    (hchev : IsChevSimple 2 (PSimple 3 J)) (hq : CFSG.Open.IsQuasisimple ↥J) :
    GLAMarking ↥J (fun lab _ _ I F θ => GLAHalfSplit 3 lab (Subgroup.center ↥J = ⊥) ∨
      GLAPrimeField 3 lab I F (GLAInduces θ fun j j' => (j' : G) = a⁻¹ * j * a)) := by
  obtain ⟨D₀, K₀, hstd₀, hyD₀, hya₀, hJeq, hKJ, hKa, hBJ⟩ :=
    neighbor_data hc hin h hU ha ha1 hSStar hclaim hnb
  obtain ⟨hBmax, hyB, hy1, -, hJc, -⟩ := hnb.1
  have hBel : IsElemAbelian 3 B := hBmax.1
  have hcatK := hclaim D₀ K₀ hstd₀
  obtain ⟨⟨hDB₀, -, -, haD₀, -, hKcomp₀, -⟩, -⟩ := hstd₀
  have haB : a ∈ B := hDB₀ haD₀
  have hqK : CFSG.Open.IsQuasisimple ↥K₀ := hKcomp₀.2.2
  have hKC : K₀ ≤ cx a := by
    intro k hk
    have hk' := hKcomp₀.1 hk
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk').2 a haD₀).symm)
  have haN : a ∈ Subgroup.normalizer ((J : Subgroup G) : Set G) := hBJ haB
  obtain ⟨-, D', K', -, hnbr⟩ := hnb
  obtain ⟨-, -, hnot⟩ := hnbr
  have hnotle : ¬ J ≤ K₀ ⊔ GLAPPrimeCoreOf 3 J := fun hle =>
    hnot (y9x_comm_le_of_le_sup haN hKC hKJ hle)
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hcaty : a ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel haB hyB)
  have ha3 : a ^ 3 = 1 := hBel.2 a haB
  have hcatKP : catalogIs (PSimple 3 K₀) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) := by
    obtain ⟨eP⟩ := S9.nonempty_pSimple_equiv hp3 hKa hqK
    exact (catalogIs_congr eP.symm).1 hcatK
  rcases hin.i144one y a J K₀ hcaty ha3 hJc hq hchev haN hKa hcatKP hnotle with hcase | hcase
  · refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ hcase
    intro lab R _ I F θ hP
    exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨hP, rfl⟩))))
  · exact CFSG.StandardType.Canonical.largeEvenMarking_mono (fun lab R _ I F θ hP => Or.inr hP) hcase

theorem gamma_odd (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    (hU : CaseU G p B x L b) {a : G} {J D₀ K : Subgroup G} (hstd : GLAStdSub p B a J D₀ K) {d : G}
    (hd : d ∈ D₀) : Odd (Nat.card (⁅K, GLAPPrimeCoreOf p (cx d)⁆ : Subgroup G)) := by
  have hdB : d ∈ B := hstd.1.1 hd
  have hodd := odd_core_of_caseU hc h hU hdB
  have hKle : K ≤ J ⊓ cs D₀ := by
    rw [hstd.1.2.2.2.2.1]
    exact sSup_le fun K' hK' => hK'.1
  have hK : K ≤ cx d := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 (hKle hg).2 d hd).symm)
  have hle : (⁅K, GLAPPrimeCoreOf p (cx d)⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (cx d) := by
    rw [Subgroup.commutator_comm]
    exact comm_le_left_of_normalizes (hK.trans (le_normalizer_glaPPrimeCoreOf p (cx d)))
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)

theorem gamma_T (hc : S10Ctx G 3) (hin : GammaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) :
    ∃ T : Subgroup G, T ≤ Ipart 3 L b ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧ ¬ T ≤ GLAPPrimeCoreOf 3 (Ipart 3 L b) ∧
      IsEmpty (T ≃* QuaternionGroup 2) := by
  obtain ⟨z, -, hz2, hz1, hzc, hBz⟩ := exists_z hc hin.l105 hin.u48 hin.u48z h hU
  obtain ⟨E₂, hE₂I, hE₂el, hE₂card, hBE, -⟩ := hU.decomp
  have hE₂B : E₂ ≤ B := by
    rw [hBE]
    exact le_sup_right
  obtain ⟨hIcomp, -⟩ := Icomp_of_cfg hc hin.l105 h
  obtain ⟨T, hTI, hT2, hTN, hTcomm, hTO, hTQ⟩ := hin.i2811t (L ⊓ cx b) (Ipart 3 L b) E₂ z hIcomp hU.I_iso
    (odd_core_I hc hin.l105.l103 h hU) hzc hz2 hz1 (le_inf hE₂I (fun g hg => hBz (hE₂B hg))) hE₂el hE₂card
  have hDT : Dgrp b x ≤ Subgroup.normalizer (T : Set G) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun t ht =>
      (Subgroup.mem_centralizer_iff.1 (Ipart_le_cs h (hTI ht)) d hd).symm)
  refine ⟨T, hTI, hT2, ?_, ?_, hTO, hTQ⟩
  · rw [hBE]
    exact sup_le hDT hTN
  · intro hbot
    apply hTcomm
    have hle : (⁅T, E₂⁆ : Subgroup G) ≤ ⁅T, B⁆ := Subgroup.commutator_mono le_rfl hE₂B
    rw [hbot] at hle
    exact le_bot_iff.1 hle

theorem caseGamma (hc : S10Ctx G p) (hin : GammaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hγ : CaseGamma G p B x L b) : Alt2 G p := by
  have hU := hγ.1
  obtain ⟨a, haD, hax, hnot⟩ := exists_a_gamma hc hin.l105 h hU hγ.2
  have hp3 := hU.p3
  subst hp3
  refine ⟨rfl, B, a, Jpart 3 (Ipart 3 L b) a, ?_⟩
  have hS := sstar_triple h.star
  obtain ⟨hDB, -, -⟩ := dgrp_facts hc h
  have haB : a ∈ B := hDB haD
  have ha1 : a ≠ 1 := fun h1 => hax (h1 ▸ Subgroup.one_mem _)
  have hsingle := gamma_single hc hin h hU haD ha1
  obtain ⟨T, hTI, hT2, hTB, hTne, hTO, hTQ⟩ := gamma_T hc hin h hU
  have hess : ∀ d ∈ Dgrp b x, d ≠ 1 → IsEssential 3 B d := fun d hd hd1 =>
    ⟨hDB hd, hd1, T, hTI.trans (Ipart_le_cx h hd), hT2, hTB, hTne, fun _ => hTQ⟩
  have hIJ : Ipart 3 L b ≤ Jpart 3 (Ipart 3 L b) a := le_closureIn_self _ _
  have hlt : ¬ (Ipart 3 L b ⊔ GLAPPrimeCoreOf 3 (Jpart 3 (Ipart 3 L b) a) = Jpart 3 (Ipart 3 L b) a) := by
    intro hsup
    obtain ⟨e⟩ := psimple_equiv_of_sup Nat.prime_three hIJ hsup
    exact hnot ((catalogIs_congr e).1 (catalogIs_imp (fun i hi => Or.inl hi) hU.I_iso))
  have hH : H104 3 B x L b a := ⟨haD, ha1, hess a haD ha1, hsingle, hlt,
    ⟨T, hTI.trans hIJ, hT2, hTB, fun hle => hTO ((le_inf hTI hle).trans (core_inf_le hIJ))⟩⟩
  have hlist := lemma104_gamma hc hin.l105.l104 h hU hH
  have hchev : IsChevSimple 2 (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) := isChevTwo_of_isListGamma hlist
  have hy09 : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) isYs09Type := by
    obtain ⟨i, hi, e⟩ := hlist
    rcases hi with h1 | h2 | h3 | h4 | h5
    · exact absurd ⟨i, Or.inr h1, e⟩ hnot
    · exact ⟨i, Or.inl h2, e⟩
    · exact ⟨i, Or.inr (Or.inl h3), e⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inl h4)), e⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inr h5)), e⟩
  have hcentEq := gamma_cent_B hc hin.l105 h hU haD ha1 hsingle hlt
  have hnotSC : ¬ IsSC 3 B := by
    intro hsc
    obtain ⟨A, hAel, hAB, hAcard⟩ := hU.centRank
    have hAle : A ≤ B := fun g hg => by
      by_cases hg1 : g = 1
      · rw [hg1]
        exact B.one_mem
      · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact hsc.2 g (hAB hg) (orderOf_eq_prime (hAel.2 g hg) hg1)
    have h1 := Subgroup.card_le_of_le hAle
    have h2 : Nat.card B = 3 ^ 4 := by rw [hS.1.2.1, hU.rank]
    have h3 : 3 ^ 4 < 3 ^ 5 := by norm_num
    omega
  have hBN : B ≤ Subgroup.normalizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h haD).2
  have hq : CFSG.Open.IsQuasisimple ↥(Jpart 3 (Ipart 3 L b) a) :=
    hc.stage9.2 B a _ hS.1 haB ha1 hsingle hBN hcentEq hchev
      (Or.inr (Or.inr ⟨hnotSC, hess a haD ha1⟩))
  have hcyc := gamma_cent_S hc hin h hU haD ha1 hq hy09
  have hSStar : GLASStar 3 B a (Jpart 3 (Ipart 3 L b) a) :=
    ⟨hS.1, haB, ha1, ⟨hsingle.1, hsingle.2.1, hq⟩, hcyc⟩
  have hInn : InnDiagOn 3 B (Jpart 3 (Ipart 3 L b) a) :=
    gamma_inndiag hc hin h haD ha1 hsingle hy09 (hess a haD ha1)
  have hInnM : InnerDiagMarking B (Jpart 3 (Ipart 3 L b) a) := (innDiagOn_iff hsingle hq).2 hInn
  obtain ⟨ePS⟩ := S9.nonempty_pSimple_equiv hc.ctx.prime hsingle hq
  have hcatJ : catalogIs (↥(Jpart 3 (Ipart 3 L b) a) ⧸ Subgroup.center ↥(Jpart 3 (Ipart 3 L b) a))
      isYs09Type := (catalogIs_congr ePS).1 hy09
  have hchevJ : IsChevSimple 2 (↥(Jpart 3 (Ipart 3 L b) a) ⧸ Subgroup.center ↥(Jpart 3 (Ipart 3 L b) a)) :=
    (S9.isChevSimple_congr ePS).1 hchev
  have hmark : GLAMarking ↥(Jpart 3 (Ipart 3 L b) a)
      (fun lab _ _ I _ θ => GLASplit 3 lab ∧ B ≤ Subgroup.normalizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) ∧
        ∀ b' ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : G) = b'⁻¹ * l * b') φ) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨split_of_ys09 hP.1, hP.2⟩)
      (hin.labels _ hq hcatJ _ hInnM)
  have hys : GLAMarking ↥(Jpart 3 (Ipart 3 L b) a) (fun lab _ _ _ _ _ => Ys09Label lab) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun lab R _ I F θ hP => hP.1)
      (hin.labels _ hq hcatJ (fun _ _ _ _ _ _ => True) (hin.ys08 _ hq hchevJ))
  have hclaim := gamma_claimK hc hin h hU haD ha1 ⟨T, hTI.trans hIJ, hT2, hTB, hTne⟩ hsingle hq hSStar hy09 hchev
    hcentEq hInn
  refine ⟨hSStar, ?_, hys⟩
  unfold GLAStandardType CFSG.Assembly.LargeEvenStandardTypeOf
  refine ⟨hmark, ⟨T, hTI.trans (Ipart_le_cx h haD), hT2, hTB, hTne⟩, ?_, ?_⟩
  · intro y J hnb
    have hchevJ := neighbor_chev2 hc hin h hU haD ha1 hSStar hclaim hnb
    have hqJ := neighbor_quasisimple hc hin h hU haD ha1 hSStar hclaim hnb hchevJ
    exact ⟨neighbor_norm hc hin h hU haD ha1 hSStar hclaim hnb,
      neighbor_marking hc hin h hU haD ha1 hSStar hclaim hnb hchevJ hqJ⟩
  · intro D₀ K hstd
    exact ⟨gamma_neighbor_exists hc hin h hU haD ha1 hSStar hclaim D₀ K hstd,
      fun d hd _ => gamma_odd hc h hU hstd hd⟩

end S10

end CFSG.LocalAnalysis.GLTheoremA
