module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma104
public import CFSG.LocalAnalysis.GLTheoremA.S8.Common
public import CFSG.LocalAnalysis.GLTheoremA.I32One
public import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Lemma105Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l103 : Lemma103Inputs G p
  l104 : Lemma104Inputs G p
  i2015 : I2015At G p
  i1312 : I1312At G p
  i114 : I114At G
  i1015 : I1015oneAt G
  i1131 : I1131At G p
  i1122 : I1122IsoAt G p
  lbal : LBalanceAt G p
  i91comp : I91CompAt G p

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem B_el {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b) : IsElemAbelian p B :=
  (sstar_triple h.star).1.1

theorem dgrp_facts (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    Dgrp b x ≤ B ∧ IsElemAbelian p (Dgrp b x) ∧ Nat.card (Dgrp b x) = p ^ 2 :=
  card_Dgrp (B_el h) hc.ctx.prime h.mem (sstar_triple h.star).2.1.1 (sstar_triple h.star).2.1.2.1 h.not_mem

theorem layer_le (p : ℕ) (X : Subgroup G) : GLAPLayer p X ≤ X := sSup_le fun _ hK => hK.1

theorem Ipart_le_cs {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    Ipart p L b ≤ cs (Dgrp b x) := by
  have hI : Ipart p L b ≤ L ⊓ cx b := layer_le p _
  have hLx : L ≤ cx x := (sstar_triple h.star).2.2.1
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hDg : Dgrp b x ≤ cx g := (Subgroup.closure_le _).2 (by
    rintro k (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 (hI hg).2).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 (hLx (hI hg).1)).symm)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hDg hd)

theorem Ipart_le_cx {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G} (h : Cfg p B x L b)
    (ha : a ∈ Dgrp b x) : Ipart p L b ≤ cx a :=
  (Ipart_le_cs h).trans (Subgroup.centralizer_le (by simpa using ha))

theorem closureIn_le_of_le {I H X : Subgroup G} (hI : I ≤ X) (hH : H ≤ X) : closureIn I H ≤ X := by
  unfold closureIn
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨i, hi, rfl⟩
  exact X.mul_mem (X.mul_mem (hH hg) (hI hi)) (X.inv_mem (hH hg))

theorem Jpart_le_cx {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G} (h : Cfg p B x L b)
    (ha : a ∈ Dgrp b x) : Jpart p (Ipart p L b) a ≤ cx a :=
  closureIn_le_of_le (Ipart_le_cx h ha) (layer_le p _)

theorem comm_le_left_of_normalizes {A J : Subgroup G} (hJ : J ≤ Subgroup.normalizer (A : Set G)) :
    (⁅A, J⁆ : Subgroup G) ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha j hj
  rw [commutatorElement_def]
  have h1 : j * a⁻¹ * j⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hJ hj) a⁻¹).1 (A.inv_mem ha)
  simpa [mul_assoc] using A.mul_mem ha h1

theorem eq_bot_of_le_odd {T M : Subgroup G} (hT : IsPGroup 2 T) (hM : Odd (Nat.card M)) (hle : T ≤ M) :
    T = ⊥ := by
  have hTcard : Nat.card T = 1 := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    have hdvd : Nat.card T ∣ Nat.card M := Subgroup.card_dvd_of_le hle
    rw [hk] at hdvd ⊢
    have : ¬ 2 ∣ Nat.card M := by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.2 hM
    rcases k with _ | k
    · simp
    · exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) hdvd) this
  exact Subgroup.card_eq_one.1 hTcard

private theorem lemma102_mem_normalizer_inf {A C : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hC ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hC h]

private theorem lemma102_commutator_le {Q I : Subgroup G}
    (h : I ≤ Subgroup.normalizer (Q : Set G)) : (⁅Q, I⁆ : Subgroup G) ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq i hi
  rw [commutatorElement_def]
  have h1 : i * q⁻¹ * i⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (h hi) q⁻¹).1 (Q.inv_mem hq)
  simpa [mul_assoc] using Q.mul_mem hq h1

private theorem lemma102_mem_normalizer_commutator {Q I : Subgroup G} {g : G}
    (hQ : g ∈ Subgroup.normalizer (Q : Set G)) (hI : g ∈ Subgroup.normalizer (I : Set G)) :
    g ∈ Subgroup.normalizer ((⁅Q, I⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hQ hI ⊢
  unfold GLBConj at hQ hI ⊢
  rw [Subgroup.map_commutator, hQ, hI]

private theorem lemma102_le_of_isSubnormal {S I K X : Subgroup G} (hK : IsSubnormal K X)
    (hSX : S ≤ X) (hIK : I ≤ K) (hS : (⁅S, I⁆ : Subgroup G) = S) : S ≤ K := by
  induction hK with
  | refl => exact hSX
  | @step H M X' hHM hn _ ih =>
    have hSM : S ≤ M := ih hSX (hIK.trans hHM)
    have hMN : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn
    rw [← hS, Subgroup.commutator_le]
    intro s hs i hi
    rw [commutatorElement_def]
    have h1 : s * i * s⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 (hMN (hSM hs)) i).1 (hIK hi)
    exact H.mul_mem h1 (H.inv_mem (hIK hi))

private theorem lemma102_mem_cs_of {S : Subgroup G} {g : G} (h : S ≤ cx g) : g ∈ cs S :=
  Subgroup.mem_centralizer_iff.2 fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (h hs)

private theorem lemma102_inf_cent_le {D E : Subgroup G} {a : G} (hD : D ≤ Subgroup.zpowers a ⊔ E) :
    cx a ⊓ Subgroup.centralizer (E : Set G) ≤ cs D := by
  intro g hg
  have hza : Subgroup.zpowers a ≤ cx g :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).1).symm)
  have hEg : E ≤ cx g := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2 e he)
  exact lemma102_mem_cs_of (hD.trans (sup_le hza hEg))

private theorem lemma105_cs_eq {D E : Subgroup G} {a : G} (hD : D ≤ Subgroup.zpowers a ⊔ E)
    (haD : a ∈ D) (hED : E ≤ D) :
    cx a ⊓ Subgroup.centralizer (E : Set G) = cs D :=
  le_antisymm (lemma102_inf_cent_le hD) (le_inf (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD))
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hED)))

private theorem lemma102_layer_normal (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (GLAPLayer p X : Set G) :=
  fun g hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)

private theorem lemma102_closureIn_le {K J B : Subgroup G} (hKJ : K ≤ J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) : closureIn K B ≤ J := by
  unfold closureIn
  refine iSup₂_le fun b' hb' => ?_
  rintro _ ⟨k, hk, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (hBJ hb') k).1 (hKJ hk)

private theorem lemma102_isSubnormal_closureIn {I H : Subgroup G} (hI : I ≤ H) :
    IsSubnormal (closureIn I H) H :=
  IsSubnormal.step (closureIn_le_of_le hI le_rfl)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (closureIn_le_of_le hI le_rfl)).2
      (le_normalizer_closureIn I H))
    (IsSubnormal.refl H)

private theorem lemma102_layer_perfect (p : ℕ) (X : Subgroup G) :
    (⁅GLAPLayer p X, GLAPLayer p X⁆ : Subgroup G) = GLAPLayer p X := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (GLAPLayer p X).mul_mem ((GLAPLayer p X).mul_mem ((GLAPLayer p X).mul_mem ha hb)
      ((GLAPLayer p X).inv_mem ha)) ((GLAPLayer p X).inv_mem hb)
  · unfold GLAPLayer
    refine sSup_le fun K hK => ?_
    have hKL : K ≤ sSup {L | GLAPComponent p X L} := le_sSup hK
    calc K = ⁅K, K⁆ := (glaPComponent_perfect hK).symm
      _ ≤ ⁅sSup {L | GLAPComponent p X L}, sSup {L | GLAPComponent p X L}⁆ :=
          Subgroup.commutator_mono hKL hKL

private theorem lemma102_gen_of_index {p : ℕ} (hp : p.Prime) {A D : Subgroup G}
    (hD : Nat.card D = p ^ 2) (hAD : A ≤ D) (hi : (A.subgroupOf D).index = p) :
    ∃ a : G, a ∈ A ∧ a ≠ 1 ∧ A = Subgroup.zpowers a := by
  have hA : Nat.card A = p := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf D)
    have h2 : Nat.card (A.subgroupOf D) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv
    rw [h2, hi, hD] at h1
    have h3 : Nat.card A * p = p * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h3
  have hAne : A ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hA
    have := hp.two_le
    omega
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hdvd : orderOf a ∣ p := hA ▸ Subgroup.orderOf_dvd_natCard A haA
  have hord : orderOf a = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1'
    · exact h
  refine ⟨a, haA, ha1', ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haA)
    (by rw [hA, Nat.card_zpowers, hord])).symm

private theorem lemma105_ipart_comp (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    GLAPComponent p (cs (Dgrp b x)) (Ipart p L b) := by
  have hp := hc.ctx.prime
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hLeq : GLAPLayer p (cx x) = L := sstar_layer hc h.star
  have hxn : cx x ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hLeq]
    exact lemma102_layer_normal p (cx x)
  have hbp : b ^ p = 1 := (B_el h).2 b h.mem
  obtain ⟨hI, -⟩ := hin.i91comp (cx x) L b hLc (sstar_chev2 hc h.star) hbp h.prop h.I_ne
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hLb : L ⊓ cx b ≤ cs (Dgrp b x) := by
    intro g hg
    refine lemma102_mem_cs_of ?_
    have hgx : g ∈ cx x := hLc.1 (Subgroup.mem_inf.1 hg).1
    have hgb : g ∈ cx b := (Subgroup.mem_inf.1 hg).2
    refine (Subgroup.closure_le _).2 ?_
    rintro k (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hgb).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hgx).symm
  have hnorm : cs (Dgrp b x) ≤ Subgroup.normalizer ((L ⊓ cx b : Subgroup G) : Set G) := by
    intro g hg
    have hgx : g ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hg x hxD).symm
    have hgb : g ∈ cx b := Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hg b hbD).symm
    exact lemma102_mem_normalizer_inf (hxn hgx) (Subgroup.le_normalizer hgb)
  have hsub : IsSubnormal (L ⊓ cx b) (cs (Dgrp b x)) :=
    IsSubnormal.step hLb ((Subgroup.normal_subgroupOf_iff_le_normalizer hLb).2 hnorm) (IsSubnormal.refl _)
  exact glaPComponent_of_isSubnormal' hp hsub hI

@[expose] def CaseAB (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G)
    (b : G) : Prop := CaseA p B x L b ∨ CaseBeta G p B x L b

structure Concl105 (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G)
    (b : G) : Prop where
  odd_comm : ∀ a ∈ Dgrp b x, a ≠ 1 →
    Odd (Nat.card (⁅Jpart p (Ipart p L b) a, GLAPPrimeCoreOf p (cx a)⁆ : Subgroup G))
  no_two_local : ¬ ∃ N : Subgroup G, IsTwoLocal N ∧ B ≤ N ∧ S9.Covers p N (Ipart p L b)
  odd_core : ∀ a ∈ Dgrp b x, a ≠ 1 → Odd (Nat.card (GLAPPrimeCoreOf p (cx a)))
  T_exists : ∃ T : Subgroup G, T ≤ Ipart p L b ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
    ¬ T ≤ GLAPPrimeCoreOf p (Ipart p L b) ∧ (⁅B, T⁆ : Subgroup G) = T ∧ T ≠ ⊥
  single : ∀ a ∈ Dgrp b x, a ≠ 1 → GLAPComponent p (cx a) (Jpart p (Ipart p L b) a) ∧
    ∀ K : Subgroup G, GLAPComponent p (cx a) K →
      Nonempty (PQuot p K ≃* PQuot p (Jpart p (Ipart p L b) a)) → B ≤ Subgroup.normalizer (K : Set G)
  essential : ∀ a ∈ Dgrp b x, a ≠ 1 → IsEssential p B a

theorem lemma104_ab (hc : S10Ctx G p) (hin : Lemma104Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5)
    (hcase : CaseAB G p B x L b) (hH : H104 p B x L b a) : Concl104 p B x L b a := by
  rcases hcase with hA | ⟨hU, hβ⟩
  · exact lemma104_alpha hc hin h hd5 hA hH
  · exact lemma104_beta hc hin h hU hH (hβ a hH.mem hH.ne)

theorem Jpart_gen_K (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) :
    ∃ K : Subgroup G, GLAPComponent p (cx a) K ∧ closureIn K B = Jpart p (Ipart p L b) a := by
  have hp := hc.ctx.prime
  obtain ⟨x', hx'D, -, hDeq⟩ := exists_complement hc h ha ha1
  have hDB := (dgrp_facts hc h).1
  have hDel := (dgrp_facts hc h).2.1
  have hED : Subgroup.zpowers x' ≤ Dgrp b x := Subgroup.zpowers_le.2 hx'D
  have hEB : Subgroup.zpowers x' ≤ B := hED.trans hDB
  have hEel : IsElemAbelian p (Subgroup.zpowers x') := isElemAbelian_mono hDel hED
  have hEX : Subgroup.zpowers x' ≤ cx a := hED.trans (isElemAbelian_le_centralizer hDel ha)
  have hIcomp := lemma105_ipart_comp hc hin h
  have hcs := lemma105_cs_eq hDeq.le ha hED
  have hJcomp : GLAPComponent p (cx a ⊓ Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G))
      (Ipart p L b) := by
    refine glaPComponent_of_le hp hIcomp ?_ hcs.le
    rw [hcs]
    exact Ipart_le_cs h
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ := hin.l104.i183 G (cx a) (S8.isKGroup_cx hc.ctx ha1) p hp
    (Subgroup.zpowers x') hEX hEel (Ipart p L b) hJcomp
  have hJeq : Jpart p (Ipart p L b) a = ⨆ L' ∈ 𝒞, L' := by
    show closureIn (Ipart p L b) (GLAPLayer p (cx a)) = _
    rw [closureIn_eq_iSup_gLBConj, h𝒞sup]
  have hBJ := (B_le_N_J hc h ha).2
  have hI0 : Ipart p L b ≤ ⨆ L' ∈ 𝒞, L' := by
    rw [← hJeq]
    exact le_closureIn_self _ _
  have hne𝒞 : 𝒞.Nonempty := by
    rcases Set.eq_empty_or_nonempty 𝒞 with hempty | hne
    · exfalso
      have h0 : (⨆ L' ∈ 𝒞, L') = ⊥ := by simp [hempty]
      rw [h0] at hI0
      exact h.I_ne (eq_bot_iff.2 hI0)
    · exact hne
  obtain ⟨K, hK⟩ := hne𝒞
  have hKJ : K ≤ Jpart p (Ipart p L b) a := by
    rw [hJeq]
    exact le_iSup₂ (f := fun L' (_ : L' ∈ 𝒞) => L') K hK
  refine ⟨K, h𝒞c K hK, le_antisymm (lemma102_closureIn_le hKJ hBJ) ?_⟩
  rw [hJeq]
  refine iSup₂_le fun L' hL' => ?_
  obtain ⟨e, he, hLe⟩ := h𝒞tr K hK L' hL'
  rw [← hLe]
  exact le_iSup₂ (f := fun g (_ : g ∈ B) => K.map (MulAut.conj g).toMonoidHom) e⁻¹
    (B.inv_mem (hEB he))

theorem odd_comm_alpha (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (hA : CaseA p B x L b) (ha : a ∈ Dgrp b x)
    (ha1 : a ≠ 1) :
    Odd (Nat.card (⁅Jpart p (Ipart p L b) a, GLAPPrimeCoreOf p (cx a)⁆ : Subgroup G)) := by
  obtain ⟨K, hK, hKB⟩ := Jpart_gen_K hc hin h ha ha1
  have hBN := (B_le_N_J hc h ha).2
  have hG : IsGStar p B K := by
    obtain ⟨E, hEB, hE, hcard, hne⟩ := JGB_of_E hc hin.l104 h ha hA
    refine ⟨E, hEB, hE, hcard, ?_⟩
    rw [hKB]
    rwa [closureIn_eq_self hBN] at hne
  have := hc.stage4.2.1 B a K (sstar_triple h.star).1 ((dgrp_facts hc h).1 ha) ha1 hK hG
  rwa [hKB] at this

theorem odd_comm_beta (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G}
    (h : Cfg p B x L b) (hU : CaseU G p B x L b) (ha : a ∈ Dgrp b x) :
    Odd (Nat.card (GLAPPrimeCoreOf p (cx a))) ∧
      Odd (Nat.card (⁅Jpart p (Ipart p L b) a, GLAPPrimeCoreOf p (cx a)⁆ : Subgroup G)) := by
  have hS := sstar_triple h.star
  have hp := hc.ctx.prime
  have hp3 := hU.p3
  have hrk := hU.rank
  subst hp3
  obtain ⟨A, hAel, hAB, hAcard⟩ := hU.centRank
  have haB : a ∈ B := (dgrp_facts hc h).1 ha
  have hAa : A ≤ cx a := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hAB hg) a haB).symm
  have hBcard : Nat.card B = 3 ^ 4 := by
    rw [hS.1.2.1, hrk]
  have hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 (cx a))) := by
    refine S8.odd_core_of_big_rank hp hS.1 hAa hAel ?_
    rw [hBcard]
    calc 3 ^ 4 < 3 ^ 5 := by norm_num
      _ ≤ Nat.card A := hAcard
  refine ⟨hodd, ?_⟩
  have hle : (⁅Jpart 3 (Ipart 3 L b) a, GLAPPrimeCoreOf 3 (cx a)⁆ : Subgroup G) ≤ GLAPPrimeCoreOf 3 (cx a) := by
    rw [Subgroup.commutator_comm]
    exact comm_le_left_of_normalizes
      ((Jpart_le_cx h ha).trans (le_normalizer_glaPPrimeCoreOf 3 (cx a)))
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)

theorem odd_comm (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hcase : CaseAB G p B x L b) :
    ∀ a ∈ Dgrp b x, a ≠ 1 →
      Odd (Nat.card (⁅Jpart p (Ipart p L b) a, GLAPPrimeCoreOf p (cx a)⁆ : Subgroup G)) := by
  intro a ha ha1
  rcases hcase with hA | ⟨hU, -⟩
  · exact odd_comm_alpha hc hin h hA ha ha1
  · exact (odd_comm_beta hc h hU ha).2

abbrev I0part (p : ℕ) (L : Subgroup G) (b : G) (N : Subgroup G) : Subgroup G :=
  GLAPLayer p (Ipart p L b ⊓ N)

abbrev Spart (p : ℕ) (L : Subgroup G) (b : G) (N : Subgroup G) (a : G) : Subgroup G :=
  ⁅I0part p L b N, pCoreOf 2 N ⊓ cx a⁆

structure Sdata (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b : G) (N : Subgroup G) (a : G) : Prop where
  mem : a ∈ Dgrp b x
  ne : a ≠ 1
  I0_le : I0part p L b N ≤ Ipart p L b
  I0_cov : I0part p L b N ⊔ GLAPPrimeCoreOf p (Ipart p L b) = Ipart p L b
  S_le : Spart p L b N a ≤ Jpart p (Ipart p L b) a
  S_two : IsPGroup 2 (Spart p L b N a)
  S_ne : Spart p L b N a ≠ ⊥
  S_comm : (⁅Spart p L b N a, I0part p L b N⁆ : Subgroup G) = Spart p L b N a
  I0_norm : I0part p L b N ≤ Subgroup.normalizer ((Spart p L b N a : Subgroup G) : Set G)
  B_norm : B ≤ Subgroup.normalizer ((Spart p L b N a : Subgroup G) : Set G)
  ess : IsEssential p B a

private theorem lemma102_I0_normQ {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {N : Subgroup G} {a : G} (ha : a ∈ Dgrp b x) :
    I0part p L b N ≤ Subgroup.normalizer ((pCoreOf 2 N ⊓ cx a : Subgroup G) : Set G) := by
  have hI0N : I0part p L b N ≤ N := (layer_le p _).trans inf_le_right
  have hI0cx : I0part p L b N ≤ cx a := ((layer_le p _).trans inf_le_left).trans (Ipart_le_cx h ha)
  intro g hg
  exact lemma102_mem_normalizer_inf (le_normalizer_pCoreOf 2 N (hI0N hg)) (Subgroup.le_normalizer (hI0cx hg))

private theorem lemma102_spart_le {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {N : Subgroup G} {a : G} (ha : a ∈ Dgrp b x) :
    (⁅I0part p L b N, pCoreOf 2 N ⊓ cx a⁆ : Subgroup G) ≤ pCoreOf 2 N ⊓ cx a := by
  rw [Subgroup.commutator_comm]
  exact lemma102_commutator_le (lemma102_I0_normQ h ha)

private theorem lemma102_rawDatum_exists (lab : CFSG.Assembly.LargeEvenLabel)
    (Q : CFSG.Assembly.LargeEvenRawCont) (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h <;> (try split_ifs at h) <;>
    first
    | (obtain ⟨K, x, fin, hc, hQ⟩ := h; exact ⟨_, _, _, _, hQ⟩)
    | (obtain ⟨K, x, fin, hc, b, c, hs, hQ⟩ := h; exact ⟨_, _, _, _, hQ⟩)

private theorem lemma102_isQuasisimple_of_marking {Q : Type} [Group Q]
    {P : CFSG.Assembly.LargeEvenMarkProp Q} (hM : CFSG.Assembly.LargeEvenMarking Q P) :
    CFSG.Open.IsQuasisimple Q := by
  obtain ⟨hcomm, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, hR⟩ := lemma102_rawDatum_exists lab _ hraw
  obtain ⟨hsimp, -, θ, -⟩ := hR
  haveI := hsimp
  exact ⟨hcomm, θ.isSimpleGroup⟩

private theorem lemma102_quasisimple_Ipart {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) : CFSG.Open.IsQuasisimple (PQuot p (Ipart p L b)) :=
  lemma102_isQuasisimple_of_marking h.inner_I.2

theorem I0_cov (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {N : Subgroup G} (hcov : S9.Covers p N (Ipart p L b)) :
    I0part p L b N ⊔ GLAPPrimeCoreOf p (Ipart p L b) = Ipart p L b := by
  have hp := hc.ctx.prime
  have hq := lemma102_quasisimple_Ipart h
  set I : Subgroup G := Ipart p L b with hI
  have hcov' : (I ⊓ N) ⊔ GLAPPrimeCoreOf p I = I := by
    have h0 : (N ⊓ I) ⊔ GLAPPrimeCoreOf p I = I := hcov
    rwa [inf_comm] at h0
  obtain ⟨hcore, ⟨e⟩⟩ := cover_facts hp (inf_le_left : I ⊓ N ≤ I) hcov'
  have hHq : CFSG.Open.IsQuasisimple (PQuot p (I ⊓ N)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq
  obtain ⟨-, -, hbar⟩ := glaPLayer_of_isQuasisimple hHq
  have h1 : GLAPLayer p (I ⊓ N) ⊔ GLAPPrimeCoreOf p (I ⊓ N) = I ⊓ N :=
    sup_glaPPrimeCoreOf_eq_of_barX_eq_top (layer_le p _) hbar
  have hOH : GLAPPrimeCoreOf p (I ⊓ N) ≤ GLAPPrimeCoreOf p I := by
    rw [hcore]
    exact inf_le_right
  refine le_antisymm (sup_le ((layer_le p _).trans inf_le_left) (Subgroup.map_subtype_le _)) ?_
  calc I = (I ⊓ N) ⊔ GLAPPrimeCoreOf p I := hcov'.symm
    _ = (GLAPLayer p (I ⊓ N) ⊔ GLAPPrimeCoreOf p (I ⊓ N)) ⊔ GLAPPrimeCoreOf p I := by rw [h1]
    _ ≤ GLAPLayer p (I ⊓ N) ⊔ GLAPPrimeCoreOf p I :=
        sup_le (sup_le le_sup_left (hOH.trans le_sup_right)) le_sup_right

theorem I0_not_two (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {N : Subgroup G} (hcov : S9.Covers p N (Ipart p L b)) : ¬ IsPGroup 2 (I0part p L b N) := by
  intro h2
  have hp := hc.ctx.prime
  have hq := lemma102_quasisimple_Ipart h
  have hcov' : I0part p L b N ⊔ GLAPPrimeCoreOf p (Ipart p L b) = Ipart p L b := I0_cov hc h hcov
  have hI0J : I0part p L b N ≤ Ipart p L b := (layer_le p _).trans inf_le_left
  let f : ↥(I0part p L b N) →* PQuot p (Ipart p L b) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥(Ipart p L b))).comp (Subgroup.inclusion hI0J)
  have hfs : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      have hy : (y : G) ∈ I0part p L b N ⊔ GLAPPrimeCoreOf p (Ipart p L b) := by
        rw [hcov']
        exact y.2
      have hJO : I0part p L b N ≤ Subgroup.normalizer (GLAPPrimeCoreOf p (Ipart p L b) : Set G) :=
        hI0J.trans (le_normalizer_glaPPrimeCoreOf p (Ipart p L b))
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hJO] at hy
      obtain ⟨j, hj, o, ho, hjo⟩ := Set.mem_mul.mp hy
      refine ⟨⟨j, hj⟩, ?_⟩
      show QuotientGroup.mk (Subgroup.inclusion hI0J ⟨j, hj⟩) = QuotientGroup.mk y
      rw [QuotientGroup.eq]
      obtain ⟨o', ho', ho'eq⟩ := ho
      have : (Subgroup.inclusion hI0J ⟨j, hj⟩)⁻¹ * y = o' := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        calc j⁻¹ * (y : G) = j⁻¹ * (j * o) := by rw [hjo]
          _ = o := by group
          _ = (o' : G) := ho'eq.symm
      rw [this]
      exact ho'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (PQuot p (Ipart p L b)) := IsPGroup.of_surjective h2 f hfs
  haveI : Group.IsNilpotent (PQuot p (Ipart p L b)) := hQ2.isNilpotent
  haveI : Nontrivial (PQuot p (Ipart p L b)) := isQuasisimple_nontrivial hq
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (PQuot p (Ipart p L b))).ne hq.1

theorem I0_facts (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {N : Subgroup G} (hcov : S9.Covers p N (Ipart p L b)) :
    I0part p L b N ≤ Ipart p L b ∧
      I0part p L b N ⊔ GLAPPrimeCoreOf p (Ipart p L b) = Ipart p L b ∧ ¬ IsPGroup 2 (I0part p L b N) :=
  ⟨(layer_le p _).trans inf_le_left, I0_cov hc h hcov, I0_not_two hc h hcov⟩

theorem exists_a_of_I33 (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {N : Subgroup G} (hN : IsTwoLocal N) (hBN : B ≤ N) (hnot : ¬ IsPGroup 2 (I0part p L b N)) :
    ∃ a ∈ Dgrp b x, a ≠ 1 ∧ Spart p L b N a ≠ ⊥ := by
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  obtain ⟨hDB, hDel, hD2⟩ := dgrp_facts hc h
  have hD1 : Dgrp b x ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hD2
    have h2 := hp.two_le
    have h4 : 4 ≤ p ^ 2 := by nlinarith
    omega
  have hI0 : I0part p L b N ≤ N ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) :=
    le_inf ((layer_le p _).trans inf_le_right)
      (((layer_le p _).trans inf_le_left).trans (Ipart_le_cs h))
  obtain ⟨A, hAD, hAi, hne⟩ := GL83.I_33_3_proved G hc.ctx.charTwo p hp hp2 N (Dgrp b x)
    (I0part p L b N) hN hD1 hDel (hDB.trans hBN) hI0 hnot
  obtain ⟨a, haA, ha1, rfl⟩ := lemma102_gen_of_index hp hD2 hAD hAi
  have hcz : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) = cx a := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  refine ⟨a, hAD haA, ha1, ?_⟩
  rw [hcz] at hne
  exact hne

theorem S_basic (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {N : Subgroup G} (hN : IsTwoLocal N) (hBN : B ≤ N) {a : G} (ha : a ∈ Dgrp b x) :
    IsPGroup 2 (Spart p L b N a) ∧ (⁅Spart p L b N a, I0part p L b N⁆ : Subgroup G) = Spart p L b N a ∧
      I0part p L b N ≤ Subgroup.normalizer ((Spart p L b N a : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer ((Spart p L b N a : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 N ⊓ cx a) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le inf_le_left
  have hI0Q := lemma102_I0_normQ (N := N) h ha
  have hperf := lemma102_layer_perfect p (Ipart p L b ⊓ N)
  have hS2 : IsPGroup 2 (Spart p L b N a) := hQ2.to_le (lemma102_spart_le (N := N) h ha)
  have e : (Spart p L b N a : Subgroup G) = ⁅pCoreOf 2 N ⊓ cx a, I0part p L b N⁆ :=
    Subgroup.commutator_comm _ _
  have hcomm : (⁅Spart p L b N a, I0part p L b N⁆ : Subgroup G) = Spart p L b N a := by
    rw [e]
    exact commutator_commutator_eq_of_perfect hQ2 hperf hI0Q
  have hI0S : I0part p L b N ≤ Subgroup.normalizer ((Spart p L b N a : Subgroup G) : Set G) := by
    rw [e]
    exact Subgroup.normalizer_commutator_ge_right _ _
  have hBQ : B ≤ Subgroup.normalizer ((pCoreOf 2 N ⊓ cx a : Subgroup G) : Set G) := fun g hg =>
    lemma102_mem_normalizer_inf (le_normalizer_pCoreOf 2 N (hBN hg))
      (Subgroup.le_normalizer (isElemAbelian_le_centralizer (B_el h) ((dgrp_facts hc h).1 ha) hg))
  have hBI0 : B ≤ Subgroup.normalizer ((I0part p L b N : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_glaPLayer (lemma102_mem_normalizer_inf ((B_le_N_J hc h ha).1 hg)
      (Subgroup.le_normalizer (hBN hg)))
  have hBS : B ≤ Subgroup.normalizer ((Spart p L b N a : Subgroup G) : Set G) := fun g hg => by
    rw [e]
    exact lemma102_mem_normalizer_commutator (hBQ hg) (hBI0 hg)
  exact ⟨hS2, hcomm, hI0S, hBS⟩

theorem Jpart_subnormal (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) :
    IsSubnormal (Jpart p (Ipart p L b) a) (cx a) := by
  have hp := hc.ctx.prime
  obtain ⟨x', hx'D, -, hDeq⟩ := exists_complement hc h ha ha1
  have hDel := (dgrp_facts hc h).2.1
  have hED : Subgroup.zpowers x' ≤ Dgrp b x := Subgroup.zpowers_le.2 hx'D
  have hEel : IsElemAbelian p (Subgroup.zpowers x') := isElemAbelian_mono hDel hED
  have hEp : IsPGroup p (Subgroup.zpowers x') := by
    have hdvd : orderOf x' ∣ p := orderOf_dvd_of_pow_eq_one (hDel.2 x' hx'D)
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hEX : Subgroup.zpowers x' ≤ cx a := hED.trans (isElemAbelian_le_centralizer hDel ha)
  have hcs := lemma105_cs_eq hDeq.le ha hED
  have hIcomp := lemma105_ipart_comp hc hin h
  have hLe : GLAPLayer p (cs (Dgrp b x)) ≤ GLAPLayer p (cx a) := by
    rw [← hcs]
    exact hin.lbal (cx a) (Subgroup.zpowers x') (S8.isKGroup_cx hc.ctx ha1) hEX hEp
  have hIL : Ipart p L b ≤ GLAPLayer p (cx a) := by
    have h1 : Ipart p L b ≤ GLAPLayer p (cs (Dgrp b x)) := le_sSup hIcomp
    exact h1.trans hLe
  have hLsub : IsSubnormal (GLAPLayer p (cx a)) (cx a) :=
    IsSubnormal.step (layer_le p _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (layer_le p _)).2 (lemma102_layer_normal p (cx a)))
      (IsSubnormal.refl _)
  exact (lemma102_isSubnormal_closureIn hIL).trans hLsub

theorem S_le_J (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {N : Subgroup G} (hN : IsTwoLocal N) (hBN : B ≤ N)
    (hcov : S9.Covers p N (Ipart p L b)) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) :
    Spart p L b N a ≤ Jpart p (Ipart p L b) a := by
  obtain ⟨-, hcomm, -, -⟩ := S_basic hc h hN hBN ha
  have hSC : Spart p L b N a ≤ cx a := (lemma102_spart_le (N := N) h ha).trans inf_le_right
  have hI0J : I0part p L b N ≤ Jpart p (Ipart p L b) a :=
    ((layer_le p _).trans inf_le_left).trans (le_closureIn_self _ _)
  exact lemma102_le_of_isSubnormal (Jpart_subnormal hc hin h ha ha1) hSC hI0J hcomm

private theorem lemma102_comp_self (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) {N : Subgroup G} (hcov : S9.Covers p N (Ipart p L b)) :
    GLAPComponent p (I0part p L b N) (I0part p L b N) := by
  have hp := hc.ctx.prime
  have hI0I : I0part p L b N ≤ Ipart p L b := (layer_le p _).trans inf_le_left
  have hq : CFSG.Open.IsQuasisimple (PQuot p (I0part p L b N)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (cover_facts hp hI0I (I0_cov hc h hcov)).2.some.symm (lemma102_quasisimple_Ipart h)
  obtain ⟨hcomp, huniq, -⟩ := glaPLayer_of_isQuasisimple hq
  have hle : I0part p L b N ≤ GLAPLayer p (I0part p L b N) :=
    sSup_le fun K hK => by
      have hKc : GLAPComponent p (I0part p L b N) K :=
        glaPComponent_of_le hp hK (le_sSup hK) (layer_le p _)
      exact (huniq K hKc).le
  have heq : GLAPLayer p (I0part p L b N) = I0part p L b N :=
    le_antisymm (layer_le p _) hle
  rw [heq] at hcomp
  exact hcomp

private theorem lemma102_comm_B_I0 (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) {N : Subgroup G} (hBN : B ≤ N) (hcov : S9.Covers p N (Ipart p L b)) :
    (⁅B, I0part p L b N⁆ : Subgroup G) = I0part p L b N := by
  have hp := hc.ctx.prime
  have hcomp := lemma102_comp_self hc h hcov
  have hcov' := I0_cov hc h hcov
  have hI0I : I0part p L b N ≤ Ipart p L b := (layer_le p _).trans inf_le_left
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hBI0 : B ≤ Subgroup.normalizer ((I0part p L b N : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_glaPLayer (lemma102_mem_normalizer_inf ((B_le_N_J hc h hxD).1 hg)
      (Subgroup.le_normalizer (hBN hg)))
  have hMN : I0part p L b N ⊔ B ≤ Subgroup.normalizer ((I0part p L b N : Subgroup G) : Set G) :=
    sup_le (fun g hg => Subgroup.le_normalizer hg) hBI0
  have hsn : IsSubnormal (I0part p L b N) (I0part p L b N ⊔ B) :=
    IsSubnormal.step le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hMN)
      (IsSubnormal.refl _)
  have hKq : CFSG.Open.IsQuasisimple ↥(barX p (I0part p L b N ⊔ B) (I0part p L b N)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX hp le_sup_left hsn) (isQuasisimple_pQuot_of_glaPComponent hp hcomp)
  have hO0 : GLAPPrimeCoreOf p (I0part p L b N) ≤ GLAPPrimeCoreOf p (Ipart p L b) := by
    rw [(cover_facts hp hI0I hcov').1]
    exact inf_le_right
  have hnc : ¬ barX p (I0part p L b N ⊔ B) B ≤ Subgroup.centralizer
      ((barX p (I0part p L b N ⊔ B) (I0part p L b N) : Subgroup _) : Set _) := by
    intro hle
    have key : ∀ c ∈ B, ∀ k ∈ I0part p L b N,
        (k * c)⁻¹ * (c * k) ∈ GLAPPrimeCoreOf p (I0part p L b N) := by
      intro c hc' k hk
      have hcM : c ∈ I0part p L b N ⊔ B := Subgroup.mem_sup_right hc'
      have hkM : k ∈ I0part p L b N ⊔ B := Subgroup.mem_sup_left hk
      have hx : (QuotientGroup.mk (⟨c, hcM⟩ : ↥(I0part p L b N ⊔ B)) :
          ↥(I0part p L b N ⊔ B) ⧸ GLAPPrimeCore p ↥(I0part p L b N ⊔ B)) ∈
          barX p (I0part p L b N ⊔ B) B :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hc')
      have hy : (QuotientGroup.mk (⟨k, hkM⟩ : ↥(I0part p L b N ⊔ B)) :
          ↥(I0part p L b N ⊔ B) ⧸ GLAPPrimeCore p ↥(I0part p L b N ⊔ B)) ∈
          barX p (I0part p L b N ⊔ B) (I0part p L b N) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hk)
      have hcomm := Subgroup.mem_centralizer_iff.1 (hle hx) _ hy
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
      have hG : (k * c)⁻¹ * (c * k) ∈ GLAPPrimeCoreOf p (I0part p L b N ⊔ B) :=
        Subgroup.mem_map_of_mem _ hcomm
      have hI0mem : (k * c)⁻¹ * (c * k) ∈ I0part p L b N := by
        have e : (k * c)⁻¹ * (c * k) = (c⁻¹ * k⁻¹ * c⁻¹⁻¹) * k := by group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hBI0 (B.inv_mem hc')) k⁻¹).1
          (Subgroup.inv_mem _ hk)) hk
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
      exact ⟨hI0mem, hG⟩
    have hcent : ∀ c ∈ B, CentMod p (Ipart p L b) c := by
      intro c hc'
      have hcN : c ∈ Subgroup.normalizer ((Ipart p L b : Subgroup G) : Set G) :=
        (B_le_N_J hc h hxD).1 hc'
      have hcO : c ∈ Subgroup.normalizer ((GLAPPrimeCoreOf p (Ipart p L b) : Subgroup G) : Set G) :=
        normalizer_le_normalizer_glaPPrimeCoreOf p (Ipart p L b) hcN
      have hkc : ∀ k ∈ I0part p L b N, k * c * k⁻¹ * c⁻¹ ∈ GLAPPrimeCoreOf p (I0part p L b N) := by
        intro k hk
        have h1 := key c⁻¹ (B.inv_mem hc') k⁻¹ (Subgroup.inv_mem _ hk)
        have e : k * c * k⁻¹ * c⁻¹ = ((k⁻¹ * c⁻¹)⁻¹ * (c⁻¹ * k⁻¹))⁻¹ := by group
        rw [e]
        exact (GLAPPrimeCoreOf p (I0part p L b N)).inv_mem h1
      have hall : ∀ l ∈ Ipart p L b, ⁅l, c⁆ ∈ GLAPPrimeCoreOf p (Ipart p L b) := by
        intro l hl
        have hl' : l ∈ I0part p L b N ⊔ GLAPPrimeCoreOf p (Ipart p L b) := by
          rw [hcov']
          exact hl
        have hI0N : I0part p L b N ≤ Subgroup.normalizer
            ((GLAPPrimeCoreOf p (Ipart p L b) : Subgroup G) : Set G) :=
          hI0I.trans (le_normalizer_glaPPrimeCoreOf p (Ipart p L b))
        rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hI0N] at hl'
        obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.1 hl'
        have hkI : k ∈ Ipart p L b := hI0I hk
        have e3 : ⁅k * o, c⁆ = k * (o * c * o⁻¹ * c⁻¹) * k⁻¹ * (k * c * k⁻¹ * c⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e3]
        have hA : o * c * o⁻¹ * c⁻¹ ∈ GLAPPrimeCoreOf p (Ipart p L b) := by
          have : c * o⁻¹ * c⁻¹ ∈ GLAPPrimeCoreOf p (Ipart p L b) :=
            (Subgroup.mem_normalizer_iff.1 hcO o⁻¹).1 ((GLAPPrimeCoreOf p (Ipart p L b)).inv_mem ho)
          have e4 : o * c * o⁻¹ * c⁻¹ = o * (c * o⁻¹ * c⁻¹) := by group
          rw [e4]
          exact mul_mem ho this
        have hB' : k * (o * c * o⁻¹ * c⁻¹) * k⁻¹ ∈ GLAPPrimeCoreOf p (Ipart p L b) :=
          (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p (Ipart p L b) hkI)
            (o * c * o⁻¹ * c⁻¹)).1 hA
        have hC : k * c * k⁻¹ * c⁻¹ ∈ GLAPPrimeCoreOf p (Ipart p L b) :=
          hO0 (hkc k hk)
        exact mul_mem hB' hC
      exact (centMod_iff).2 ⟨hcN, hall⟩
    have hBD : B ≤ Dgrp b x := fun c hc' => (h.cent_I c hc').1 (hcent c hc')
    have hcard := Subgroup.card_le_of_le hBD
    have hBrank : Nat.card B = p ^ GLATwoLocalRank p G := ((sstar_triple h.star).1).2.1
    have hD2 := (dgrp_facts hc h).2.2
    have h4 := hc.ctx.rank_ge
    have hp2 := hp.two_le
    rw [hBrank, hD2] at hcard
    have h5 : p ^ 4 ≤ p ^ GLATwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
    have h6 : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  exact commutator_eq_of_glaPComponent hp (le_sup_left : I0part p L b N ≤ I0part p L b N ⊔ B) hcomp
    (le_sup_right : B ≤ I0part p L b N ⊔ B) hBI0 hKq hnc

theorem S_essential (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {N : Subgroup G} (hN : IsTwoLocal N) (hBN : B ≤ N) (hcov : S9.Covers p N (Ipart p L b)) {a : G}
    (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) (hS : Spart p L b N a ≠ ⊥) (hSJ : Spart p L b N a ≤ cx a) :
    IsEssential p B a := by
  obtain ⟨hS2, hSI0, -, hBS⟩ := S_basic hc h hN hBN ha
  have hBI0 : (⁅B, I0part p L b N⁆ : Subgroup G) = I0part p L b N :=
    lemma102_comm_B_I0 hc h hBN hcov
  have hSB : (⁅Spart p L b N a, B⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    have h1 : (⁅⁅B, Spart p L b N a⁆, I0part p L b N⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_comm B (Spart p L b N a), hbot, Subgroup.commutator_bot_left]
    have h2 : (⁅⁅Spart p L b N a, I0part p L b N⁆, B⁆ : Subgroup G) = ⊥ := by
      rw [hSI0, hbot]
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [Subgroup.commutator_comm (I0part p L b N) B, hBI0] at h3
    apply hS
    rw [← hSI0, Subgroup.commutator_comm (Spart p L b N a) (I0part p L b N), h3]
  unfold IsEssential
  refine ⟨(dgrp_facts hc h).1 ha, ha1, Spart p L b N a, hSJ, hS2, hBS, hSB, ?_⟩
  intro _hp3
  refine ⟨fun e => ?_⟩
  have hperf : (⁅I0part p L b N, I0part p L b N⁆ : Subgroup G) = I0part p L b N :=
    glaPComponent_perfect (lemma102_comp_self hc h hcov)
  have h24 : Nat.card (MulAut ↥(Spart p L b N a)) = 24 :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.natCard_mulAut_of_quaternion e
  haveI : Finite (MulAut ↥(Spart p L b N a)) := Nat.finite_of_card_ne_zero (by rw [h24]; norm_num)
  haveI : Fintype (MulAut ↥(Spart p L b N a)) := Fintype.ofFinite _
  haveI hsolv : Group.IsSolvable (MulAut ↥(Spart p L b N a)) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three
      (by norm_num) (a := 3) (b := 1)
      (by rw [← Nat.card_eq_fintype_card, h24]; norm_num)
  have hIN : I0part p L b N ≤ Subgroup.normalizer ((Spart p L b N a : Subgroup G) : Set G) :=
    (S_basic hc h hN hBN ha).2.2.1
  let φ : ↥(I0part p L b N) →* MulAut ↥(Spart p L b N a) :=
    (Subgroup.normalizerMonoidHom (Spart p L b N a)).comp (Subgroup.inclusion hIN)
  haveI : Group.IsPerfect ↥(I0part p L b N) := Subgroup.isPerfect_iff.2 hperf
  have hφ : φ = 1 := CFSG.Holt.General.eq_one_of_isPerfect_of_isSolvable_range φ inferInstance
  have hcent : I0part p L b N ≤ Subgroup.centralizer ((Spart p L b N a : Subgroup G) : Set G) := by
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : φ ⟨i, hi⟩ = 1 := by rw [hφ]; rfl
    have h2 := congrArg (fun α : MulAut ↥(Spart p L b N a) => ((α ⟨s, hs⟩ : ↥(Spart p L b N a)) : G)) h1
    have e1 : ((φ ⟨i, hi⟩ ⟨s, hs⟩ : ↥(Spart p L b N a)) : G) = i * s * i⁻¹ := rfl
    simp only [MulAut.one_apply] at h2
    rw [e1] at h2
    calc s * i = (i * s * i⁻¹) * i := by rw [h2]
      _ = i * s := by group
  have hbot : (⁅Spart p L b N a, I0part p L b N⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  exact hS (by rw [← hSI0, hbot])

theorem exists_Sdata (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) {N : Subgroup G} (hN : IsTwoLocal N) (hBN : B ≤ N)
    (hcov : S9.Covers p N (Ipart p L b)) : ∃ a : G, Sdata p B x L b N a := by
  obtain ⟨hI0le, hI0cov, hnot⟩ := I0_facts hc h hcov
  obtain ⟨a, ha, ha1, hne⟩ := exists_a_of_I33 hc h hN hBN hnot
  obtain ⟨hS2, hSI, hI0S, hBS⟩ := S_basic hc h hN hBN ha
  have hSJ := S_le_J hc hin h hN hBN hcov ha ha1
  have hSC : Spart p L b N a ≤ cx a := hSJ.trans (Jpart_le_cx h ha)
  exact ⟨a, ha, ha1, hI0le, hI0cov, hSJ, hS2, hne, hSI, hI0S, hBS,
    S_essential hc h hN hBN hcov ha ha1 hne hSC⟩

theorem S_not_le_core (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {N : Subgroup G} {a : G} (hd : Sdata p B x L b N a)
    (hodd : Odd (Nat.card (⁅Jpart p (Ipart p L b) a, GLAPPrimeCoreOf p (cx a)⁆ : Subgroup G))) :
    ¬ Spart p L b N a ≤ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) := by
  intro hle
  have hsub := Jpart_subnormal hc hin h hd.mem hd.ne
  have hO : GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) ≤ GLAPPrimeCoreOf p (cx a) :=
    glaPPrimeCoreOf_le_of_isSubnormal hc.ctx.prime hsub
  have hI0J : I0part p L b N ≤ Jpart p (Ipart p L b) a :=
    hd.I0_le.trans (le_closureIn_self _ _)
  have h1 : Spart p L b N a ≤ (⁅Jpart p (Ipart p L b) a, GLAPPrimeCoreOf p (cx a)⁆ : Subgroup G) := by
    calc Spart p L b N a = ⁅Spart p L b N a, I0part p L b N⁆ := hd.S_comm.symm
      _ = ⁅I0part p L b N, Spart p L b N a⁆ := Subgroup.commutator_comm _ _
      _ ≤ ⁅Jpart p (Ipart p L b) a, GLAPPrimeCoreOf p (cx a)⁆ :=
          Subgroup.commutator_mono hI0J (hle.trans hO)
  exact hd.S_ne (eq_bot_of_le_odd hd.S_two hodd h1)

theorem single_of_S (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {N : Subgroup G} {a : G} (hd : Sdata p B x L b N a)
    (hSO : ¬ Spart p L b N a ≤ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a)) :
    GLAPComponent p (cx a) (Jpart p (Ipart p L b) a) := by
  classical
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hc.ctx.odd
  have ha := hd.mem
  have ha1 := hd.ne
  obtain ⟨x', hx'D, -, hDeq⟩ := exists_complement hc h ha ha1
  have hDel := (dgrp_facts hc h).2.1
  have hDcard := (dgrp_facts hc h).2.2
  have hDB : Dgrp b x ≤ B := (dgrp_facts hc h).1
  have hB : GLAIsBmax p B := (sstar_triple h.star).1
  have hED : Subgroup.zpowers x' ≤ Dgrp b x := Subgroup.zpowers_le.2 hx'D
  have hEel : IsElemAbelian p (Subgroup.zpowers x') := isElemAbelian_mono hDel hED
  have hEX : Subgroup.zpowers x' ≤ cx a := hED.trans (isElemAbelian_le_centralizer hDel ha)
  have hIcomp := lemma105_ipart_comp hc hin h
  have hcs := lemma105_cs_eq hDeq.le ha hED
  have hJcomp : GLAPComponent p (cx a ⊓
      Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G)) (Ipart p L b) := by
    refine glaPComponent_of_le hp hIcomp ?_ hcs.le
    rw [hcs]
    exact Ipart_le_cs h
  have hzx : Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) =
      Subgroup.centralizer ({x'} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hJcomp' : GLAPComponent p (cx a ⊓ Subgroup.centralizer ({x'} : Set G)) (Ipart p L b) := by
    rw [← hzx]; exact hJcomp
  obtain ⟨𝒞, h𝒞c, h𝒞sup, h𝒞stab, h𝒞tr⟩ := hin.l104.i183 G (cx a) (S8.isKGroup_cx hc.ctx ha1) p hp
    (Subgroup.zpowers x') hEX hEel (Ipart p L b) hJcomp
  have hJeq : Jpart p (Ipart p L b) a = ⨆ C ∈ 𝒞, C := by
    show closureIn (Ipart p L b) (GLAPLayer p (cx a)) = _
    rw [closureIn_eq_iSup_gLBConj, h𝒞sup]
  set J := Jpart p (Ipart p L b) a with hJdef
  have hIJ : Ipart p L b ≤ J := le_closureIn_self _ _
  have hJsub : IsSubnormal J (cx a) := Jpart_subnormal hc hin h ha ha1
  by_cases htwo : ∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂
  swap
  ·
    push_neg at htwo
    have hne : 𝒞.Nonempty := by
      rcases Set.eq_empty_or_nonempty 𝒞 with hem | hne
      · exfalso
        have hJbot : J = ⊥ := by rw [hJeq, hem]; simp
        exact h.I_ne (eq_bot_iff.2 (hJbot ▸ hIJ))
      · exact hne
    obtain ⟨K, hK⟩ := hne
    have hJK : J = K := by
      rw [hJeq]
      apply le_antisymm
      · exact iSup₂_le fun C hC => le_of_eq (htwo C hC K hK)
      · exact le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) K hK
    rw [hJK]
    exact h𝒞c K hK
  exfalso
  obtain ⟨C₁, hC₁, C₂, hC₂, hne⟩ := htwo
  have hK₁ : GLAPComponent p (cx a) C₁ := h𝒞c C₁ hC₁
  have hx'N : x' ∉ Subgroup.normalizer (C₁ : Set G) := by
    intro hN
    apply hne
    have hall : ∀ C ∈ 𝒞, C = C₁ := by
      intro C hC
      obtain ⟨e, he, he'⟩ := h𝒞tr C₁ hC₁ C hC
      have hNe : GLBConj e C₁ = C₁ :=
        mem_normalizer_iff_gLBConj_eq.1 ((Subgroup.zpowers_le.2 hN) he)
      rw [← he', hNe]
    rw [hall C₂ hC₂, hall C₁ hC₁]
  have hx'B : x' ∈ B := hDB hx'D
  have hIsubC : Ipart p L b ≤ closureIn C₁ B := by
    refine hIJ.trans ?_
    rw [hJeq]
    refine iSup₂_le fun C hC => ?_
    obtain ⟨e, he, rfl⟩ := h𝒞tr C₁ hC₁ C hC
    rw [closureIn_eq_iSup_gLBConj]
    exact le_biSup (fun g => GLBConj g C₁) (hDB (hED he))
  have hIx : Ipart p L b ≤ Subgroup.centralizer ({x'} : Set G) := fun i hi => (hJcomp'.1 hi).2
  have hCB : closureIn C₁ B ≤ cx a :=
    closureIn_le_of_le hK₁.1 (isElemAbelian_le_centralizer (B_el h) (hDB ha))
  have hI1122 : GLAPComponent p (closureIn C₁ B ⊓ Subgroup.centralizer ({x'} : Set G))
      (Ipart p L b) :=
    glaPComponent_of_le hp hJcomp' (le_inf hIsubC hIx) (inf_le_inf_right _ hCB)
  obtain ⟨eI⟩ := hin.i1122 B a C₁ x' hB hd.ess hK₁ hx'B hx'N (Ipart p L b) hI1122
  have hcard : Nat.card (PQuot p (Ipart p L b)) = Nat.card (PSimple p C₁) :=
    Nat.card_congr eI.toEquiv
  have hza : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) = cx a := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have haD : Subgroup.zpowers a ≤ Dgrp b x := Subgroup.zpowers_le.2 ha
  have hAcard : Nat.card ↥(Subgroup.zpowers a) = p := lemma102_card_zpowers_prime hp hDel ha ha1
  have hidx : ((Subgroup.zpowers a).subgroupOf (Dgrp b x)).index = p :=
    lemma102_index_eq hp haD hDcard hAcard
  have hcomm_ad : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers x', u * v = v * u := by
    intro u hu v hv
    exact idiag_commute hDel (haD hu) (hED hv)
  have hstab : ∀ C ∈ 𝒞, ∀ e ∈ Dgrp b x, GLBConj e C ∈ 𝒞 := by
    intro C hC e he
    rw [hDeq] at he
    obtain ⟨u, hu, v, hv, rfl⟩ := lemma102_mem_sup_comm hcomm_ad he
    rw [← gLBConj_gLBConj, lemma102_glbconj_zpowers_eq (h𝒞c C hC).1 hu]
    exact h𝒞stab C hC v hv
  have htr' : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ Dgrp b x, GLBConj e C = C' := by
    intro C hC C' hC'
    obtain ⟨e, he, he'⟩ := h𝒞tr C hC C' hC'
    exact ⟨e, hED he, he'⟩
  have hsup' : (⨆ C ∈ 𝒞, C) = ⨆ g ∈ GLAPLayer p
      (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)), GLBConj g (Ipart p L b) := by
    rw [hza]; exact h𝒞sup
  have hcomp' : ∀ C ∈ 𝒞, GLAPComponent p
      (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)) C := by
    intro C hC; rw [hza]; exact h𝒞c C hC
  have hKg : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)) := by
    rw [hza]; exact S8.isKGroup_cx hc.ctx ha1
  have hIdiag : GLAPComponent p (Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G))
      (Ipart p L b) := hIcomp
  have hcov_all : ∀ C ∈ 𝒞, C ≤ Ipart p L b ⊔ centModSubgroup p C :=
    i183DiagAt_holds G p hp hp2 (Subgroup.zpowers a) (Dgrp b x) (Ipart p L b) 𝒞 hDel haD hidx hKg
      hIdiag hcomp' hsup' hstab htr' ⟨C₁, hC₁, C₂, hC₂, hne⟩
  have hperm : ∀ e ∈ Subgroup.zpowers x', ∀ C ∈ 𝒞, GLBConj e C ∈ 𝒞 :=
    fun e he C hC => h𝒞stab C hC e he
  have hO : GLAPPrimeCoreOf p (Ipart p L b) ≤ GLAPPrimeCoreOf p J :=
    lemma102_O_le hp h𝒞c hJeq hperm h𝒞tr hC₁ hIJ hIx (hcov_all C₁ hC₁) hcard
  have hOnorm : GLAPPrimeCoreOf p J ≤
      Subgroup.normalizer ((Spart p L b N a ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) :=
    fun o ho => lemma102_O_normalizes_sup hd.S_le ho
  have hJS : Ipart p L b ≤
      Subgroup.normalizer ((Spart p L b N a ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) := by
    rw [← hd.I0_cov]
    refine sup_le (fun i hi => ?_) (hO.trans hOnorm)
    have hiJ : i ∈ J := hIJ (hd.I0_le hi)
    exact CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_normalizer_sup (hd.I0_norm hi)
      (le_normalizer_glaPPrimeCoreOf p J hiJ)
  have hclaim : ⁅Spart p L b N a, Ipart p L b⁆ ≤ GLAPPrimeCoreOf p J :=
    L62.claim_of_projection hp h𝒞c hJeq.symm hJsub hIJ hd.S_two hd.S_le hJS hcov_all
  apply hSO
  calc Spart p L b N a = ⁅Spart p L b N a, I0part p L b N⁆ := hd.S_comm.symm
    _ ≤ ⁅Spart p L b N a, Ipart p L b⁆ := Subgroup.commutator_mono le_rfl hd.I0_le
    _ ≤ GLAPPrimeCoreOf p J := hclaim

private theorem lemma102_mem_normalizer_of_conj {C : Subgroup G} {g : G}
    (h1 : ∀ t ∈ C, g * t * g⁻¹ ∈ C) (h2 : ∀ t ∈ C, g⁻¹ * t * g⁻¹⁻¹ ∈ C) :
    g ∈ Subgroup.normalizer (C : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => h1 h hh, fun hh => ?_⟩
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  have := h2 _ hh
  rwa [e] at this

private theorem lemma102_conj_sup_le {A B : Subgroup G} {g : G}
    (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ B) (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ A ⊔ B) :
    ∀ t ∈ A ⊔ B, g * t * g⁻¹ ∈ A ⊔ B := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  intro t ht
  exact hle ht

theorem lt_of_S (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {N : Subgroup G} {a : G} (hd : Sdata p B x L b N a)
    (hSO : ¬ Spart p L b N a ≤ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a))
    (hsingle : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a)) :
    ¬ (Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a) := by
  intro hcov
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥(Spart p L b N a) := hd.S_two
  have hIJ : Ipart p L b ≤ Jpart p (Ipart p L b) a := le_closureIn_self _ _
  set J : Subgroup G := Jpart p (Ipart p L b) a with hJ
  set O : Subgroup G := GLAPPrimeCoreOf p J with hO
  set S : Subgroup G := Spart p L b N a with hS
  set I0 : Subgroup G := I0part p L b N with hI0
  have hOI : GLAPPrimeCoreOf p (Ipart p L b) ≤ O := by
    rw [(cover_facts hp hIJ hcov).1]
    exact inf_le_right
  have hI0J : I0 ≤ J := hd.I0_le.trans hIJ
  have hJO : J ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p J
  have hOJ : O ≤ J := Subgroup.map_subtype_le _
  have hSJ : S ≤ J := hd.S_le
  have hSN : S ≤ Subgroup.normalizer (O : Set G) := hSJ.trans hJO
  have hI0O : I0 ⊔ O = J := by
    apply le_antisymm (sup_le hI0J hOJ)
    calc J = Ipart p L b ⊔ O := hcov.symm
      _ ≤ I0 ⊔ O := by
        have h1 : Ipart p L b ≤ I0 ⊔ GLAPPrimeCoreOf p (Ipart p L b) := hd.I0_cov.symm.le
        exact sup_le (h1.trans (sup_le le_sup_left (hOI.trans le_sup_right))) le_sup_right
  have hI0N : I0 ≤ Subgroup.normalizer (O : Set G) := hI0J.trans hJO
  have hJ_mul : ∀ j ∈ J, ∃ i ∈ I0, ∃ o ∈ O, i * o = j := by
    intro j hj
    have hj' : j ∈ ((I0 ⊔ O : Subgroup G) : Set G) := by
      rw [hI0O]
      exact hj
    rw [Subgroup.coe_mul_of_left_le_normalizer_right I0 O hI0N] at hj'
    obtain ⟨i, hi, o, ho, hio⟩ := Set.mem_mul.1 hj'
    exact ⟨i, hi, o, ho, hio⟩
  have hOnorm : ∀ o ∈ O, ∀ j ∈ J, j * o * j⁻¹ ∈ O := fun o ho j hj =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p J hj) o).1 ho
  have hOconj : ∀ o ∈ O, ∀ t ∈ S ⊔ O, o * t * o⁻¹ ∈ S ⊔ O := by
    intro o ho
    refine lemma102_conj_sup_le (fun s hs => ?_)
      (fun y hy => Subgroup.mem_sup_right (O.mul_mem (O.mul_mem ho hy) (O.inv_mem ho)))
    have hsJ := hSJ hs
    have hu : s⁻¹ * o * s⁻¹⁻¹ ∈ O := hOnorm o ho s⁻¹ (J.inv_mem hsJ)
    have e : o * s * o⁻¹ = s * ((s⁻¹ * o * s⁻¹⁻¹) * o⁻¹) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right (O.mul_mem hu (O.inv_mem ho)))
  have hI0conj : ∀ i ∈ I0, ∀ t ∈ S ⊔ O, i * t * i⁻¹ ∈ S ⊔ O := by
    intro i hi
    refine lemma102_conj_sup_le (fun s hs => Subgroup.mem_sup_left ?_)
      (fun y hy => Subgroup.mem_sup_right (hOnorm y hy i (hI0J hi)))
    exact (Subgroup.mem_normalizer_iff.1 (hd.I0_norm hi) s).1 hs
  have hNormO : ∀ o ∈ O, o ∈ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := fun o ho =>
    lemma102_mem_normalizer_of_conj (hOconj o ho) (hOconj o⁻¹ (O.inv_mem ho))
  have hNormI : ∀ i ∈ I0, i ∈ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := fun i hi =>
    lemma102_mem_normalizer_of_conj (hI0conj i hi) (hI0conj i⁻¹ (I0.inv_mem hi))
  have hTJ : S ⊔ O ≤ J := sup_le hSJ hOJ
  have hJN : J ≤ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G) := by
    intro j hj
    obtain ⟨i, hi, o, ho, rfl⟩ := hJ_mul j hj
    exact mul_mem (hNormI i hi) (hNormO o ho)
  have hTnorm : ((S ⊔ O).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).2 hJN
  have hOcop : Nat.Coprime p (Nat.card O) := (Nat.Prime.coprime_iff_not_dvd hp).2
    (not_dvd_card_glaPPrimeCoreOf hp J)
  have hST : S ≤ S ⊔ O := le_sup_left
  have hOT : O ≤ S ⊔ O := le_sup_right
  have hindex : Nat.Coprime p (O.subgroupOf (S ⊔ O)).index := by
    haveI : (O.subgroupOf (S ⊔ O)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOT).2 (hTJ.trans hJO)
    let f : ↥S →* (↥(S ⊔ O) ⧸ O.subgroupOf (S ⊔ O)) :=
      (QuotientGroup.mk' (O.subgroupOf (S ⊔ O))).comp (Subgroup.inclusion hST)
    have hf : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H t =>
        have ht : (t : G) ∈ ((S ⊔ O : Subgroup G) : Set G) := t.2
        rw [Subgroup.coe_mul_of_left_le_normalizer_right S O hSN] at ht
        obtain ⟨s, hs, o, ho, hso⟩ := Set.mem_mul.1 ht
        refine ⟨⟨s, hs⟩, ?_⟩
        show (QuotientGroup.mk (⟨s, hST hs⟩ : ↥(S ⊔ O)) : ↥(S ⊔ O) ⧸ O.subgroupOf (S ⊔ O)) = QuotientGroup.mk t
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have e : (((⟨s, hST hs⟩ : ↥(S ⊔ O))⁻¹ * t : ↥(S ⊔ O)) : G) = o := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hso]
          group
        rw [e]
        exact ho
    have hdvd : (O.subgroupOf (S ⊔ O)).index ∣ Nat.card ↥S := Subgroup.card_dvd_of_surjective hf
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS2
    exact Nat.Coprime.coprime_dvd_right hdvd (by
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have hTcop : Nat.Coprime p (Nat.card ((S ⊔ O).subgroupOf J)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv]
    have hmul := Subgroup.card_mul_index (O.subgroupOf (S ⊔ O))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOT).toEquiv] at hmul
    rw [← hmul]
    exact Nat.Coprime.mul_right hOcop hindex
  have hTj : (S ⊔ O).subgroupOf J ≤ GLAPPrimeCore p ↥J := by
    haveI := hTnorm
    unfold GLAPPrimeCore CFSG.pPrimeCore
    exact le_sSup ⟨inferInstance, hTcop⟩
  apply hSO
  intro s hs
  have hsJ := hSJ hs
  exact Subgroup.mem_map.2 ⟨⟨s, hsJ⟩, hTj (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hs)), rfl⟩

theorem single_lt_of_S (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {N : Subgroup G} {a : G} (hd : Sdata p B x L b N a)
    (hSO : ¬ Spart p L b N a ≤ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a)) :
    GLAPComponent p (cx a) (Jpart p (Ipart p L b) a) ∧
      ¬ (Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a) :=
  have hs := single_of_S hc hin h hd hSO
  ⟨hs, lt_of_S hc hin h hd hSO hs⟩

theorem h104_of_Sdata (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {N : Subgroup G} {a : G} (hd : Sdata p B x L b N a)
    (hodd : Odd (Nat.card (⁅Jpart p (Ipart p L b) a, GLAPPrimeCoreOf p (cx a)⁆ : Subgroup G))) :
    H104 p B x L b a := by
  have hSO := S_not_le_core hc hin h hd hodd
  obtain ⟨hsingle, hlt⟩ := single_lt_of_S hc hin h hd hSO
  exact ⟨hd.mem, hd.ne, hd.ess, hsingle, hlt, ⟨Spart p L b N a, hd.S_le, hd.S_two, hd.B_norm, hSO⟩⟩

theorem oddCore_of_noTwoLocal (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G}
    (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hno : ¬ ∃ N : Subgroup G, IsTwoLocal N ∧ B ≤ N ∧ S9.Covers p N (Ipart p L b)) :
    Odd (Nat.card (GLAPPrimeCoreOf p (cx a))) := by
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hc.ctx.odd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDB, hDel, -⟩ := dgrp_facts hc h
  set W : Subgroup G := GLAPPrimeCoreOf p (cx a) with hWdef
  have hWcop : Nat.Coprime p (Nat.card W) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp (cx a))
  have hcxW : cx a ≤ Subgroup.normalizer (W : Set G) := le_normalizer_glaPPrimeCoreOf p (cx a)
  have hWcx : W ≤ cx a := Subgroup.map_subtype_le _
  have hBel : IsElemAbelian p B := B_el h
  have haB : a ∈ B := hDB ha
  have hBcx : B ≤ cx a := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hg haB)
  have hDcx : Dgrp b x ≤ cx a := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hDel hd ha)
  have hBW : B ≤ Subgroup.normalizer (W : Set G) := hBcx.trans hcxW
  by_contra hodd
  have h2W : 2 ∣ Nat.card W := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨R, hRW, hR2, hRodd, hBR⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.exists_invariant_sylow_two hp hp2 (isPGroup_of_isElemAbelian hBel)
      hBW hWcop
  have hRne : R ≠ ⊥ := by
    intro hR
    apply hRodd
    rw [hR, Subgroup.relIndex_bot_left]
    exact h2W
  have hN2 : IsTwoLocal (Subgroup.normalizer (R : Set G)) := ⟨R, hRne, hR2, rfl⟩
  have hfrat : ∀ g ∈ cx a, ∃ n ∈ Subgroup.normalizer (R : Set G), ∃ w ∈ W, g = n * w := by
    intro g hg
    set R' : Subgroup G := R.map (MulAut.conj g).toMonoidHom with hR'def
    have hgW : ∀ r ∈ W, g * r * g⁻¹ ∈ W := fun r hr =>
      (Subgroup.mem_normalizer_iff.1 (hcxW hg) r).1 hr
    have hR'W : R' ≤ W := by
      rintro _ ⟨r, hr, rfl⟩
      exact hgW r (hRW hr)
    have hRcard : Nat.card R' = Nat.card R :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hR'2 : IsPGroup 2 R' := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR2
      exact IsPGroup.of_card (n := k) (by rw [hRcard, hk])
    have hR'odd : ¬ 2 ∣ R'.relIndex W := by
      have h1 := Subgroup.relIndex_mul_card R' W
      have h2 := Subgroup.relIndex_mul_card R W
      rw [inf_eq_left.2 hR'W] at h1
      rw [inf_eq_left.2 hRW] at h2
      have hpos : 0 < Nat.card R' := Nat.card_pos
      have hrel : R'.relIndex W = R.relIndex W := by
        apply Nat.eq_of_mul_eq_mul_right hpos
        rw [h1, hRcard, h2]
      rw [hrel]
      exact hRodd
    obtain ⟨w₀, hw₀⟩ := exists_conj_iff_of_isPGroup (Γ := W)
      (hR'2.comap_subtype) (hR2.comap_subtype)
      (by
        show ¬ 2 ∣ R'.relIndex W
        exact hR'odd)
      (by
        show ¬ 2 ∣ R.relIndex W
        exact hRodd)
    have hw₀W : (w₀ : G) ∈ W := w₀.2
    have hw₀G : ∀ z ∈ W, z ∈ R ↔ ∃ y ∈ R', z = (w₀ : G) * y * (w₀ : G)⁻¹ := by
      intro z hz
      constructor
      · intro hzR
        obtain ⟨y, hy, hzy⟩ := (hw₀ ⟨z, hz⟩).1 (Subgroup.mem_subgroupOf.2 hzR)
        refine ⟨(y : G), Subgroup.mem_subgroupOf.1 hy, ?_⟩
        have := congrArg Subtype.val hzy
        simpa using this
      · rintro ⟨y, hy, hzy⟩
        have hyW : y ∈ W := hR'W hy
        have hzeq : (⟨z, hz⟩ : ↥W) = w₀ * ⟨y, hyW⟩ * w₀⁻¹ := Subtype.ext (by simpa using hzy)
        exact Subgroup.mem_subgroupOf.1 ((hw₀ ⟨z, hz⟩).2
          ⟨⟨y, hyW⟩, Subgroup.mem_subgroupOf.2 hy, hzeq⟩)
    set n : G := (w₀ : G) * g with hn
    have hnN : n ∈ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hxR
        have e : n * x * n⁻¹ = (w₀ : G) * (g * x * g⁻¹) * (w₀ : G)⁻¹ := by
          rw [hn]
          group
        have hz : n * x * n⁻¹ ∈ W := by
          rw [e]
          exact W.mul_mem (W.mul_mem hw₀W (hgW x (hRW hxR))) (W.inv_mem hw₀W)
        exact (hw₀G _ hz).2 ⟨g * x * g⁻¹, Subgroup.mem_map.2 ⟨x, hxR, rfl⟩, e⟩
      · intro hzR
        have e : n * x * n⁻¹ = (w₀ : G) * (g * x * g⁻¹) * (w₀ : G)⁻¹ := by
          rw [hn]
          group
        have hz : n * x * n⁻¹ ∈ W := hRW hzR
        obtain ⟨y, hy, hzy⟩ := (hw₀G _ hz).1 hzR
        obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.1 hy
        have key : n * x * n⁻¹ = n * r * n⁻¹ := by
          rw [hzy, ← hry]
          show (w₀ : G) * (g * r * g⁻¹) * (w₀ : G)⁻¹ = n * r * n⁻¹
          rw [hn]
          group
        have hxr : x = r := by
          have := congrArg (fun z => n⁻¹ * z * n) key
          simpa using this
        rw [hxr]
        exact hr
    have hncx : n ∈ cx a := by
      rw [hn]
      exact (cx a).mul_mem (hWcx w₀.2) hg
    refine ⟨n, hnN, n⁻¹ * (w₀ : G)⁻¹ * n, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (hcxW ((cx a).inv_mem hncx)) (w₀ : G)⁻¹).1
        (W.inv_mem hw₀W)
      rw [inv_inv] at this
      exact this
    · rw [hn]
      group
  have hD : IsPGroup p (Dgrp b x) := isPGroup_of_isElemAbelian hDel
  have hDW : Dgrp b x ≤ Subgroup.normalizer (W : Set G) := hDcx.trans hcxW
  have hIW : Ipart p L b ≤ Subgroup.normalizer (W : Set G) := (Ipart_le_cx h ha).trans hcxW
  have hDN : Dgrp b x ≤ Subgroup.normalizer (R : Set G) := hDB.trans hBR
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hLeq : GLAPLayer p (cx x) = L := sstar_layer hc h.star
  have hxn : cx x ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hLeq]
    exact lemma102_layer_normal p (cx x)
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hLb : L ⊓ cx b ≤ cs (Dgrp b x) := by
    intro g hg
    refine lemma102_mem_cs_of ?_
    have hgx : g ∈ cx x := hLc.1 (Subgroup.mem_inf.1 hg).1
    have hgb : g ∈ cx b := (Subgroup.mem_inf.1 hg).2
    refine (Subgroup.closure_le _).2 ?_
    rintro k (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hgb).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hgx).symm
  have hnorm : cs (Dgrp b x) ≤ Subgroup.normalizer ((L ⊓ cx b : Subgroup G) : Set G) := by
    intro g hg
    have hgx : g ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hg x hxD).symm
    have hgb : g ∈ cx b := Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hg b hbD).symm
    exact lemma102_mem_normalizer_inf (hxn hgx) (Subgroup.le_normalizer hgb)
  have hLsub : IsSubnormal (L ⊓ cx b) (cs (Dgrp b x)) :=
    IsSubnormal.step hLb ((Subgroup.normal_subgroupOf_iff_le_normalizer hLb).2 hnorm)
      (IsSubnormal.refl _)
  have hsubI : IsSubnormal (Ipart p L b) (cs (Dgrp b x)) :=
    (IsSubnormal.step (layer_le p _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (layer_le p _)).2
        (lemma102_layer_normal p _))
      (IsSubnormal.refl _)).trans hLsub
  have hI : PPrimePerfect p (Ipart p L b) := pPrimePerfect_glaPLayer p (L ⊓ cx b)
  have hcov : ∀ i ∈ Ipart p L b, ∃ n ∈ Subgroup.normalizer (R : Set G), ∃ w ∈ W, i = n * w :=
    fun i hi => hfrat i (Ipart_le_cx h ha hi)
  have hcovers : S9.Covers p (Subgroup.normalizer (R : Set G)) (Ipart p L b) :=
    covers_of_weak hD (Ipart_le_cs h) hsubI hI hWcop.symm hDW hIW hDN hcov
  exact hno ⟨Subgroup.normalizer (R : Set G), hN2, hBR, hcovers⟩

theorem no_two_local (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hcase : CaseAB G p B x L b) :
    ¬ ∃ N : Subgroup G, IsTwoLocal N ∧ B ≤ N ∧ S9.Covers p N (Ipart p L b) := by
  rintro ⟨N, hN, hBN, hcov⟩
  obtain ⟨a, hd⟩ := exists_Sdata hc hin h hN hBN hcov
  have hodd := odd_comm hc hin h hcase a hd.mem hd.ne
  have hH := h104_of_Sdata hc hin h hd hodd
  have hSO := S_not_le_core hc hin h hd hodd
  obtain ⟨hS2, hdisj⟩ := lemma104_ab hc hin.l104 h hd5 hcase hH
  obtain ⟨hDB, hDel, hD2⟩ := dgrp_facts hc h
  obtain ⟨d, hdD, hdp⟩ : ∃ d ∈ Dgrp b x, R2Prop p d (Jpart p (Ipart p L b) a) := by
    rcases hdisj with ⟨d, hdD, hdf⟩ | ⟨hp3, htd, ⟨d, hdD, hdn⟩, -⟩
    · exact ⟨d, hdD, Or.inl hdf⟩
    · exact ⟨d, hdD, Or.inr ⟨hp3, htd, hdn⟩⟩
  have haut := hin.l104.lemma102.aut
  have hdN : d ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    (B_le_N_J hc h hd.mem).2 (hDB hdD)
  have hda : d ∉ Subgroup.zpowers a := by
    intro hz
    have hcm : CentMod p (Jpart p (Ipart p L b) a) d := centMod_zpowers_of_le (Jpart_le_cx h hd.mem) hz
    have hinn := inducesInnerMod_of_centMod hcm
    rcases hdp with hf | ⟨hp3, -, hn⟩
    · exact (haut.field_nonInnDiag _ _ d hH.single hS2.2 hf).2
        (haut.inner_innDiag _ _ d hH.single hS2.2 hdN hinn)
    · subst hp3
      exact hn.2 hinn
  have hcomp := I_comp_in_J hc hin.l104 h hd.mem hd.ne (hDB hdD |> fun _ => hdD) hda hH.single
  have hI2015 := hin.i2015 (cx a) _ _ _ d hH.single hS2.2 hcomp hd.I0_le hd.I0_cov
    ((B_el h).2 d (hDB hdD)) hdp (Spart p L b N a) hd.S_le hd.S_two hd.I0_norm
  exact hSO hI2015

end S10

end CFSG.LocalAnalysis.GLTheoremA
