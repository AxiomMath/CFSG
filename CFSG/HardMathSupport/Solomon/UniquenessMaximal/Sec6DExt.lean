module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DPB
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EGSideFuse
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ea_comm {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm h hx hy

omit [Finite G] in
theorem jOf_le' (L A : Subgroup G) : jLayerOf L A ≤ L ⊓ Subgroup.centralizer (A : Set G) :=
  sSup_le fun _ hL => hL.1

omit [Finite G] in
theorem jOf_le_kOf' (L A : Subgroup G) (x : G) : jLayerOf L A ≤ kOf L A x := by
  refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) ?_
  intro z hz
  exact ⟨z, hz, by simp⟩

structure ExtCtx (B : Subgroup G) (b : G) (L A : Subgroup G) : Prop where
  Bel : IsElemAbelian 3 B
  Bc : Nat.card B = 81
  SC : IsSCp 3 ⊤ B
  b_mem : b ∈ B
  b_ne : b ≠ 1
  L_comp : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L
  AB : A ≤ B
  Ael : IsElemAbelian 3 A
  Ac : Nat.card A = 9
  b_A : b ∈ A
  field : ∀ a ∈ A, InducesFieldAut 3 L a
  Fc : Nat.card ↥(B ⊓ L) = 9
  FJ : B ⊓ L ≤ jLayerOf L A
  AF : A ⊓ (B ⊓ L) = ⊥
  BAF : A ⊔ (B ⊓ L) = B
  ext_type : IsExtremalType (barOf 3 L)
  pump : ∀ x ∈ B, x ≠ 1 → InducesFieldAut 3 L x →
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) (pumpUp L x) ∧
      InducesFieldAut 3 (pumpUp L x) b ∧ Nat.card (barOf 3 (pumpUp L x)) ≤ Nat.card (barOf 3 L)

theorem exists_extCtx {m : ℕ} (hS : GLStanding G m 3) (hC : GLCaseFour G 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) {b : G} {L A : Subgroup G} (hw : IsExtremalWitness B b L A) :
    ExtCtx B b L A := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hbB, hb1, hL, -, hty, ⟨hF, hA, hbA, hfld, hJ, q8, hq8⟩, hpump⟩ := hw
  have hSC : IsSCp 3 ⊤ B := lemma23_proved G m 3 hS B hB
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hBc : Nat.card B = 81 := by
    have hcard := hB.1.2.1
    rw [hcard, hC.2.1]; norm_num
  obtain ⟨hAB, hAel, hAc⟩ := hA
  have hcommB : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc => ea_comm hBel ha hc
  have hexpB : ∀ a ∈ B, a ^ 3 = 1 := hBel.2
  have hFcomm : ∀ x ∈ B ⊓ L, ∀ y ∈ B ⊓ L, x * y = y * x := fun x hx y hy => hcommB x hx.1 y hy.1
  have hFexp : ∀ x ∈ B ⊓ L, x ^ 3 = 1 := fun x hx => hexpB x hx.1
  have hAF : A ⊓ (B ⊓ L) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Subgroup.mem_bot]
    by_contra hf1
    have hfF : f ∈ B ⊓ L := hf.2
    have hfinv : f⁻¹ ∈ B ⊓ L := (B ⊓ L).inv_mem hfF
    obtain ⟨n, hn, hnf⟩ := fuse_of_q8 (jLayerOf L A) (B ⊓ L) hFcomm hFexp hF q8 hq8 f hfF hf1 f⁻¹ hfinv
      (fun h => hf1 (inv_eq_one.1 h))
    have hnC : n ∈ Subgroup.centralizer (A : Set G) := (jOf_le' L A hn.1).2
    have hcomm : n * f = f * n := by
      have := Subgroup.mem_centralizer_iff.1 hnC f hf.1
      exact this.symm
    have h1 : f = f⁻¹ := by
      calc f = n * f * n⁻¹ := by rw [hcomm]; group
        _ = f⁻¹ := hnf
    have h2 : f * f = 1 := by
      calc f * f = f * f⁻¹ := by rw [← h1]
        _ = 1 := by group
    have h3 : f = 1 := by
      have := hexpB f (hAB hf.1)
      calc f = f ^ 3 * (f * f)⁻¹ := by group
        _ = 1 := by rw [this, h2]; group
    exact hf1 h3
  have hBAF : A ⊔ (B ⊓ L) = B := by
    have hN : B ⊓ L ≤ Subgroup.normalizer (A : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro f hf
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hcommB a (hAB ha) f hf.1)
    have h := card_sup_mul_card_inf hN
    rw [hAF, Subgroup.card_bot, hAc, hF] at h
    have hle : A ⊔ (B ⊓ L) ≤ B := sup_le hAB inf_le_left
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hBc]; omega
  exact ⟨hBel, hBc, hSC, hbB, hb1, hL, hAB, hAel, by rw [hAc]; norm_num, hbA, hfld, hF, hJ, hAF,
    hBAF, hty, hpump⟩

omit [Finite G] in
theorem center_eq_bot_of_quasisimple_simple {Q : Type*} [Group Q] (hq : CFSG.Open.IsQuasisimple Q)
    (hs : IsSimpleGroup Q) : Subgroup.center Q = ⊥ := by
  have := hs
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Q) with h0 | h0
  · exact h0
  · exfalso
    have hab : ∀ a b : Q, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b : b ∈ Subgroup.center Q) a)
    have hcomm : commutator Q ≤ ⊥ := by
      rw [commutator_eq_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a, b, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hab _ _)
    rw [hq.1] at hcomm
    obtain ⟨a, ha⟩ := exists_ne (1 : Q)
    exact ha (Subgroup.mem_bot.1 (hcomm (Subgroup.mem_top a)))

omit [Finite G] in
theorem subnormal_eq_or_le_center {A B : Subgroup G} (h : IsSubnormal A B)
    (hB : CFSG.Open.IsQuasisimple B) : A = B ∨ A ≤ (Subgroup.center B).map B.subtype := by
  induction h with
  | refl A => exact Or.inl rfl
  | step hAM hn _ ih =>
    rename_i A M
    rcases ih hB with hMB | hM
    · subst hMB
      have hB' : CFSG.IsQuasisimple _ :=
        ⟨⟨hB.1⟩, hB.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hB⟩
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hB' hn with h | h
      · exact Or.inl (le_antisymm hAM (Subgroup.subgroupOf_eq_top.mp h))
      · refine Or.inr fun x hx => ⟨⟨x, hAM hx⟩, h ?_, rfl⟩
        exact hx
    · exact Or.inr (hAM.trans hM)

theorem layer_le_normalizer' {C L : Subgroup G} (hL : GLAPComponent 3 C L) :
    GLAPLayer 3 C ≤ Subgroup.normalizer (L : Set G) := by
  refine sSup_le fun A hA => ?_
  by_cases hAL : A = L
  · subst hAL; exact Subgroup.le_normalizer
  · exact le_normalizer_of_ne hA hL hAL

theorem layer_self_of_comp {X L : Subgroup G} (hL : GLAPComponent 3 X L) : GLAPLayer 3 L = L := by
  apply le_antisymm (sSup_le fun J hJ => hJ.1)
  exact le_sSup (glaPComponent_of_le Nat.prime_three hL le_rfl hL.1)

theorem pumpUp_eq_L {a b : G} {L : Subgroup G} (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hC : Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G)) :
    pumpUp L a = L := by
  unfold pumpUp
  rw [hC]
  have hLC : L ⊓ Subgroup.centralizer ({b} : Set G) = L := inf_eq_left.2 hL.1
  rw [hLC, layer_self_of_comp hL]
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [gLBConj_eq_of_mem_normalizer (layer_le_normalizer' hL hg)]
  · exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (by rw [gLBConj_one])

theorem jOf_le_L (L A : Subgroup G) : jLayerOf L A ≤ L := (jOf_le' L A).trans inf_le_left

theorem kOf_eq_L (iL3 : InputL3U3Facts) {B : Subgroup G} {b : G} {L A : Subgroup G}
    (hx : ExtCtx B b L A) {a : G}
    (hC : Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G)) :
    kOf L A a = L := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := hx.L_comp
  set X := Subgroup.centralizer ({b} : Set G) with hX
  have hkdef : kOf L A a = bClosure (GLAPLayer 3 X) (jLayerOf L A) := by
    unfold kOf bClosure
    rw [hC]
  rw [hkdef]
  set H := bClosure (GLAPLayer 3 X) (jLayerOf L A) with hH
  have hHL : H ≤ L := by
    refine iSup₂_le fun g hg => ?_
    have := gLBConj_mono g (jOf_le_L L A)
    rwa [gLBConj_eq_of_mem_normalizer (layer_le_normalizer' hL hg)] at this
  have hLlayer : L ≤ GLAPLayer 3 X := le_sSup hL
  have hn : L ≤ Subgroup.normalizer (H : Set G) := fun g hg =>
    mem_normalizer_iff_gLBConj_eq.2 (bClosure_conj_eq (hLlayer hg))
  have hsnL : IsSubnormal H L :=
    IsSubnormal.step hHL ((Subgroup.normal_subgroupOf_iff_le_normalizer hHL).2 hn)
      (IsSubnormal.refl L)
  have hsn : IsSubnormal H X := isSubnormal_trans' hsnL hL.2.1
  by_contra hne
  have hlt : H < L := lt_of_le_of_ne hHL hne
  have hQq : CFSG.Open.IsQuasisimple ↥(barX 3 X L) := hL.2.2.1.2.2
  have hsub : IsSubnormal (barX 3 X H) (barX 3 X L) := isSubnormal_barX 3 hsnL
  rcases subnormal_eq_or_le_center hsub hQq with h | h
  · exact hL.2.2.2 H hlt hsn h
  · have hsimp : IsSimpleGroup ↥(barX 3 X L) := by
      have h1 := (iL3 (barOf 3 L) (IsExtremalType.isLThreeEps hx.ext_type)).1
        ((Lemma512Ns.isQuasisimple_barX_iff Nat.prime_three hL.2.1).1 hL.2.2.1.2.2).1
      exact ((Lemma512Ns.barXEquiv Nat.prime_three hL.2.1).isSimpleGroup_congr).1 h1
    have hcen := center_eq_bot_of_quasisimple_simple hQq hsimp
    rw [hcen, Subgroup.map_bot, le_bot_iff] at h
    have hFp : IsPGroup 3 ↥(B ⊓ L) := (isPGroup_of_isElemAbelian hx.Bel).to_inf_left
    have hFX : B ⊓ L ≤ X := inf_le_right.trans hL.1
    have hFH : B ⊓ L ≤ H := by
      refine hx.FJ.trans ?_
      exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (by rw [gLBConj_one])
    have hbar : barX 3 X (B ⊓ L) ≤ barX 3 X H :=
      Subgroup.map_mono fun z hz => Subgroup.mem_subgroupOf.2 (hFH (Subgroup.mem_subgroupOf.1 hz))
    rw [h, le_bot_iff] at hbar
    have := card_barX_of_isPGroup Nat.prime_three hFX hFp
    rw [hbar, Subgroup.card_bot, hx.Fc] at this
    omega

structure Env (m : ℕ) (B : Subgroup G) (b : G) (L A : Subgroup G) : Prop where
  S : GLStanding G m 3
  C : GLCaseFour G 3
  B1 : IsBOneMax 3 B
  w : IsExtremalWitness B b L A
  X : ExtCtx B b L A

omit [Finite G] in
theorem centralizer_le_of_mem_zpowers {x y : G} (h : x ∈ Subgroup.zpowers y) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  exact (Commute.zpow_right (show Commute g y from hg) k).eq

theorem centralizer_eq_of_mem_zpowers {a b : G} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (ha : a ∈ Subgroup.zpowers b) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have ha3 : a ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have cb : Nat.card ↥(Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have ca : Nat.card ↥(Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hab : Subgroup.zpowers a = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ha) (by rw [ca, cb])
  have hba : b ∈ Subgroup.zpowers a := by rw [hab]; exact Subgroup.mem_zpowers b
  exact le_antisymm (centralizer_le_of_mem_zpowers hba) (centralizer_le_of_mem_zpowers ha)

theorem kOf_eq_pumpUp (iL3 : InputL3U3Facts) {B : Subgroup G} {b : G} {L A : Subgroup G}
    (hx : ExtCtx B b L A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : kOf L A a = pumpUp L a := by
  by_cases hab : a ∈ Subgroup.zpowers b
  · have hC := centralizer_eq_of_mem_zpowers (hx.Bel.2 b hx.b_mem) hx.b_ne hab ha1
    rw [kOf_eq_L iL3 hx hC, pumpUp_eq_L hx.L_comp hC]
  · have haB : a ∈ B := hx.AB ha
    have ha3 : a ^ 3 = 1 := hx.Bel.2 a haB
    have hb3 : b ^ 3 = 1 := hx.Bel.2 b hx.b_mem
    have hcomm : a * b = b * a := ea_comm hx.Bel haB hx.b_mem
    have hne : Subgroup.zpowers a ≠ Subgroup.zpowers b := by
      intro h; apply hab; rw [← h]; exact Subgroup.mem_zpowers a
    have h9 := card_zpowers_sup hcomm ha3 hb3 ha1 hx.b_ne hne
    have hAeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = A :=
      Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.2 ha)
        (Subgroup.zpowers_le.2 hx.b_A)) (by rw [h9, hx.Ac])
    have hLC : L ⊓ Subgroup.centralizer ({a} : Set G) = L ⊓ Subgroup.centralizer (A : Set G) := by
      ext g
      constructor
      · rintro ⟨hgL, hga⟩
        have hgb : g * b = b * g :=
          Subgroup.mem_centralizer_singleton_iff.1 (hx.L_comp.1 hgL)
        have hga' : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 hga
        have hle : A ≤ Subgroup.centralizer ({g} : Set G) := by
          rw [← hAeq]
          exact sup_le (zpowers_le_cent hga'.symm) (zpowers_le_cent hgb.symm)
        refine ⟨hgL, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz))
      · rintro ⟨hgL, hgA⟩
        exact ⟨hgL, Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hgA a ha).symm⟩
    unfold kOf pumpUp jLayerOf
    rw [hLC]

section KaFacts

variable {m : ℕ} {B : Subgroup G} {b : G} {L A : Subgroup G}

theorem Ka_comp (iL3 : InputL3U3Facts) (hx : ExtCtx B b L A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) (kOf L A a) := by
  rw [kOf_eq_pumpUp iL3 hx ha ha1]
  exact (hx.pump a (hx.AB ha) ha1 (hx.field a ha)).1

theorem Ka_N (h515 : Lemma515) (e : Env m B b L A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ Subgroup.normalizer (kOf L A a : Set G) :=
  fun _ hg => h515 G m e.S e.C B e.B1 b L A e.w a ha ha1 hg

theorem Ka_B (h515 : Lemma515) (e : Env m B b L A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    B ≤ Subgroup.normalizer (kOf L A a : Set G) := by
  intro y hy
  have hy' : y ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_left (show Commute a y from ea_comm e.X.Bel (e.X.AB ha) hy) k).eq
  exact Ka_N h515 e ha ha1 (Subgroup.centralizer_le_normalizer _ hy')

theorem F_le_Ka (hx : ExtCtx B b L A) (a : G) : B ⊓ L ≤ kOf L A a :=
  hx.FJ.trans (jOf_le_kOf' L A a)

theorem Ka_type (iK : InputKType) (e : Env m B b L A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    IsLThreeEps (barOf 3 (kOf L A a)) :=
  iK G m e.S e.C B e.B1 b L A e.w a ha ha1

end KaFacts

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
