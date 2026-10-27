module

public import CFSG.LocalAnalysis.GLTheoremA.S11.CounterB
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95C
public import CFSG.LocalAnalysis.GLTheoremA.S8.Common
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cAut
public import CFSG.CharacterTheory.Burnside
public import CFSG.Holt.General.OrbitCountBasic
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxClaim
public import CFSG.LocalAnalysis.GLTheoremA.S6.I183Diag

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure CConf (G : Type) [Group G] [Finite G] (p q : ℕ) (B : Subgroup G) (x : G) (L M D E F J : Subgroup G) (a : G)
    (S K : Subgroup G) : Prop where
  red : RedB G p q B x L M D E F J
  a_mem : a ∈ D
  a_ne : a ≠ 1
  S_def : S = ⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆
  S_ne : S ≠ ⊥
  S_two : IsPGroup 2 S
  S_normB : B ≤ Subgroup.normalizer (S : Set G)
  S_comm : (⁅S, J⁆ : Subgroup G) = S
  S_le_T0 : S ≤ pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)
  K_comp : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K
  J_le : J ≤ K
  K_normB : B ≤ Subgroup.normalizer (K : Set G)
  K_gstar : IsGStar p B K
  S_le_K : S ≤ K

namespace S11

variable {G : Type} [Group G] [Finite G] {m p q : ℕ} {B : Subgroup G} {x : G} {L M D E F J : Subgroup G}

private theorem cfC_inv_comm {a g : G} (hg : g * a = a * g) : g⁻¹ * a = a * g⁻¹ := by
  calc g⁻¹ * a = g⁻¹ * a * (g * g⁻¹) := by group
    _ = g⁻¹ * (a * g) * g⁻¹ := by group
    _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hg]
    _ = a * g⁻¹ := by group

private theorem cfC_conj_comm {a g h : G} (hg : g * a = a * g) (hh : h * a = a * h) :
    g * h * g⁻¹ * a = a * (g * h * g⁻¹) := by
  calc g * h * g⁻¹ * a = g * h * (g⁻¹ * a) := by group
    _ = g * h * (a * g⁻¹) := by rw [cfC_inv_comm hg]
    _ = g * (h * a) * g⁻¹ := by group
    _ = g * (a * h) * g⁻¹ := by rw [hh]
    _ = g * a * h * g⁻¹ := by group
    _ = a * g * h * g⁻¹ := by rw [hg]
    _ = a * (g * h * g⁻¹) := by group

private theorem cfC_mem_normalizer_centralizer {a g : G} (hg : g * a = a * g) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  refine ⟨fun hh => cfC_conj_comm hg hh, fun hh => ?_⟩
  have key := cfC_conj_comm (cfC_inv_comm hg) hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rw [e] at key
  exact key

private theorem cfC_gLBConj_inv_eq (c : G) (I : Subgroup G) :
    GLBConj c⁻¹ I = I.map (MulAut.conj c).toMonoidHom := by
  unfold GLBConj
  rw [inv_inv]

private theorem cfC_mem_normalizer_closureIn {I H : Subgroup G} {y : G}
    (hy : ∀ c ∈ H, y ∈ Subgroup.normalizer ((I.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G)) :
    y ∈ Subgroup.normalizer ((closureIn I H : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold closureIn GLBConj
  simp only [Subgroup.map_iSup]
  refine iSup_congr fun c => iSup_congr fun hc => ?_
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (hy c hc)
  unfold GLBConj at h1
  exact h1

private theorem cfC_mem_normalizer_layer {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLAPLayer p X : Set G) := by
  have key : ∀ h ∈ Subgroup.normalizer (X : Set G), GLBConj h (GLAPLayer p X) ≤ GLAPLayer p X := by
    intro h hh
    have hX : GLBConj h X = X := gLBConj_eq_of_mem_normalizer hh
    have e : GLBConj h (GLAPLayer p X) = ⨆ Y ∈ {L : Subgroup G | GLAPComponent p X L}, GLBConj h Y := by
      show GLBConj h (sSup {L : Subgroup G | GLAPComponent p X L}) = _
      rw [sSup_eq_iSup]
      unfold GLBConj
      simp only [Subgroup.map_iSup]
    rw [e]
    refine iSup₂_le fun Y hY => le_sSup ?_
    have hY' : GLAPComponent p X Y := hY
    have h1 := glaPComponent_gLBConj hY' h
    rw [hX] at h1
    exact h1
  apply mem_normalizer_iff_gLBConj_eq.2
  apply le_antisymm (key g hg)
  have hg' : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := (Subgroup.normalizer (X : Set G)).inv_mem hg
  have h2 := gLBConj_mono (g := g) (key g⁻¹ hg')
  rw [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h2
  exact h2

private theorem cfC_card_le_of_twoLocal {p : ℕ} (hp : p.Prime) {M E : Subgroup G}
    (hM : IsTwoLocal M) (hEM : E ≤ M) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ GLATwoLocalRank p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hE).exists_card_eq
  have h1 : n ≤ CFSG.Open.pRank p M := CFSG.SectionRank.le_pRank hp1 hEM hE hn
  have hbdd : BddAbove {k : ℕ | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨F, -, -, hF⟩ := CFSG.SectionRank.exists_pRank hp1 H
    have h3 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp1
    have h4 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    rw [hF] at h4
    omega
  have h2 : CFSG.Open.pRank p M ≤ CFSG.Open.twoLocalPrimeRank p G :=
    le_csSup hbdd ⟨M, hM, rfl⟩
  rw [hn]
  exact Nat.pow_le_pow_right hp.pos (h1.trans h2)

private theorem cfC_conj_component {p : ℕ} {a : G} {B K₁ : Subgroup G}
    (hBa : ∀ c ∈ B, c * a = a * c) (hK₁ : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K₁)
    {c : G} (hc : c ∈ B) :
    GLAPComponent p (Subgroup.centralizer ({a} : Set G)) (K₁.map (MulAut.conj c).toMonoidHom) := by
  rw [← cfC_gLBConj_inv_eq]
  have hn : c⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) :=
    cfC_mem_normalizer_centralizer (cfC_inv_comm (hBa c hc))
  have h1 := glaPComponent_gLBConj hK₁ c⁻¹
  rwa [gLBConj_eq_of_mem_normalizer hn] at h1

private theorem cfC_layer_le_normalizer_closureIn {p : ℕ} (hp : p.Prime) {a : G} {B K₁ : Subgroup G}
    (hBa : ∀ c ∈ B, c * a = a * c) (hK₁ : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K₁) :
    GLAPLayer p (Subgroup.centralizer ({a} : Set G)) ≤
      Subgroup.normalizer ((closureIn K₁ B : Subgroup G) : Set G) := by
  have hKle : ∀ c ∈ B, GLBConj c⁻¹ K₁ ≤ closureIn K₁ B := fun c hc => by
    rw [cfC_gLBConj_inv_eq]
    exact le_iSup₂_of_le (f := fun a (_ : a ∈ B) => K₁.map (MulAut.conj a).toMonoidHom) c hc le_rfl
  have hnormY : ∀ Y : Subgroup G, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) Y →
      Y ≤ Subgroup.normalizer ((closureIn K₁ B : Subgroup G) : Set G) := by
    intro Y hY
    by_cases hex : ∃ c ∈ B, GLBConj c⁻¹ K₁ = Y
    · obtain ⟨c, hc, rfl⟩ := hex
      exact (hKle c hc).trans Subgroup.le_normalizer
    · simp only [not_exists, not_and] at hex
      intro y hy
      refine cfC_mem_normalizer_closureIn fun c hc => ?_
      have hcc : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) (GLBConj c⁻¹ K₁) := by
        rw [cfC_gLBConj_inv_eq]
        exact cfC_conj_component hBa hK₁ hc
      rw [← cfC_gLBConj_inv_eq]
      exact (le_centModSubgroup_of_ne hp hY hcc (Ne.symm (hex c hc)) hy).1
  show sSup {Y : Subgroup G | GLAPComponent p (Subgroup.centralizer ({a} : Set G)) Y} ≤ _
  exact sSup_le fun Y hY => hnormY Y hY

theorem B_le_M_of_redB (hH : Hyp111 G m p B x L) (hR : RedB G p q B x L M D E F J) : B ≤ M := fun b hb =>
  hR.cx_le (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hH.elem hb hH.mem))

theorem J_le_M_of_redB (hR : RedB G p q B x L M D E F J) : J ≤ M :=
  (hR.J_comp.1.trans inf_le_left).trans hR.L_le

theorem J_le_cx_of_redB (hR : RedB G p q B x L M D E F J) {a : G} (haD : a ∈ D) :
    J ≤ Subgroup.centralizer ({a} : Set G) :=
  (hR.J_comp.1.trans inf_le_right).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD))

theorem J_le_normalizer_T0_of_redB (hR : RedB G p q B x L M D E F J) {a : G} (haD : a ∈ D) :
    J ≤ Subgroup.normalizer ((pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
  fun j hj => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_pCoreOf 2 M (J_le_M_of_redB hR hj), Subgroup.le_normalizer (J_le_cx_of_redB hR haD hj)⟩

theorem B_le_normalizer_T0_of_redB (hH : Hyp111 G m p B x L) (hR : RedB G p q B x L M D E F J) {a : G} (haD : a ∈ D) :
    B ≤ Subgroup.normalizer ((pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
  fun b hb => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_pCoreOf 2 M (B_le_M_of_redB hH hR hb),
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2
        (isElemAbelian_commute hH.elem hb ((hR.D_le.trans hR.E_le) haD)))⟩

theorem S_le_T0_of_redB (hR : RedB G p q B x L M D E F J) {a : G} (haD : a ∈ D) :
    (⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆ : Subgroup G) ≤
      pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.le_normalizer_iff_commutator_le_left.1 (J_le_normalizer_T0_of_redB hR haD)

theorem exists_a (hctx : ThmACtx G m) (hH : Hyp111 G m p B x L) (hR : RedB G p q B x L M D E F J) :
    ∃ a ∈ D, a ≠ 1 ∧ (⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆ : Subgroup G) ≠ ⊥ := by
  have hp : p.Prime := hH.prime
  have hp2 : p ≠ 2 := hH.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hDB : D ≤ B := hR.D_le.trans hR.E_le
  have hDel : IsElemAbelian p D := isElemAbelian_mono hH.elem hDB
  have hDcard : Nat.card D = p ^ 2 := hR.card_D
  have hDne : D ≠ ⊥ := by
    intro hD0
    rw [hD0, Subgroup.card_bot] at hDcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hDM : D ≤ M := hDB.trans (B_le_M_of_redB hH hR)
  have hJ' : J ≤ M ⊓ Subgroup.centralizer (D : Set G) :=
    le_inf (J_le_M_of_redB hR) (hR.J_comp.1.trans inf_le_right)
  have hnot2 : ¬ IsPGroup 2 J := S9.not_isPGroup_of_component Nat.prime_two hR.J_comp
  obtain ⟨A, hAD, hAidx, hne⟩ :=
    GL83.I_33_3_proved G hctx.1.charTwo p hp hp2 M D J hR.two_local hDne hDel hDM hJ' hnot2
  have hAcard : Nat.card A = p := by
    have h1 := S9.card_mul_of_index_eq hAD hAidx
    rw [hDcard] at h1
    have hp0 : 0 < p := hp.pos
    have h2 : Nat.card A * p = p * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 h2
  have hA1 : A ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hAcard
    exact hp.one_lt.ne hAcard
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haD : a ∈ D := hAD haA
  have hord : orderOf a = p := orderOf_eq_prime (hDel.2 a haD) ha1'
  have hAz : Subgroup.zpowers a = A := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haA) ?_
    rw [Nat.card_zpowers, hord, hAcard]
  refine ⟨a, haD, ha1', ?_⟩
  rw [← hAz, S3.centralizer_zpowers] at hne
  exact hne

theorem S_facts (hH : Hyp111 G m p B x L) (hR : RedB G p q B x L M D E F J) {a : G} (haD : a ∈ D) :
    IsPGroup 2 (⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆ : Subgroup G) ∧
      B ≤ Subgroup.normalizer ((⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆ : Subgroup G) : Set G) ∧
      (⁅(⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆ : Subgroup G), J⁆ : Subgroup G) =
        ⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆ := by
  have hp : p.Prime := hH.prime
  have hp2 : p ≠ 2 := hH.ne_two
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2M : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hT₀2 : IsPGroup 2 (pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
    h2M.to_le inf_le_left
  have hJT₀ := J_le_normalizer_T0_of_redB hR haD
  refine ⟨hT₀2.to_le (S_le_T0_of_redB hR haD), le_normalizer_commutator hR.B_norm (B_le_normalizer_T0_of_redB hH hR haD), ?_⟩
  have h := i321UsedAt_holds p hp _ J (S9.coprime_card_of_two_group hp hp2 hT₀2) hJT₀
    (S9.residual_of_component hp hR.J_comp)
  rw [Subgroup.commutator_comm J (pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G))]
  exact h

theorem exists_Gstar_component' (hctx : ThmACtx G m) (h183 : Input18_3_4) (hH : Hyp111 G m p B x L)
    (hR : RedB G p q B x L M D E F J) {a : G} (haD : a ∈ D) (ha1 : a ≠ 1) :
    ∃ K₁ : Subgroup G, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K₁ ∧ J ≤ closureIn K₁ B ∧ IsGStar p B K₁ := by
  have hp : p.Prime := hH.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hKa : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    S8.isKGroup_cx (S3Ctx.of_ctx hctx hH.mu) ha1
  have hDB : D ≤ B := hR.D_le.trans hR.E_le
  have hD : IsElemAbelian p D := isElemAbelian_mono hH.elem hDB
  have hE : IsElemAbelian p E := isElemAbelian_mono hH.elem hR.E_le
  have hDa : D ≤ Subgroup.centralizer ({a} : Set G) := isElemAbelian_le_centralizer hD haD
  have hJD : GLAPComponent p (Subgroup.centralizer (D : Set G)) J :=
    S9.glaPComponent_centralizer hp hH.comp hR.x_mem hR.J_comp
  have hCD : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD)
  have hJ' : GLAPComponent p (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer (D : Set G)) J := by
    rw [inf_eq_right.2 hCD]
    exact hJD
  obtain ⟨𝒞, h𝒞comp, h𝒞sup, -, h𝒞trans⟩ :=
    h183 G (Subgroup.centralizer ({a} : Set G)) hKa p hp D hDa hD J hJ'
  have hJsup : J ≤ ⨆ L ∈ 𝒞, L := by
    rw [h𝒞sup]
    refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (le_of_eq ?_)
    exact (gLBConj_one J).symm
  rcases Set.eq_empty_or_nonempty 𝒞 with hempty | ⟨K₁, hK₁⟩
  · exfalso
    have hbot : (⨆ L ∈ 𝒞, L) = ⊥ := by
      rw [hempty]
      simp
    exact glaPComponent_ne_bot' hJD (le_bot_iff.1 (hJsup.trans hbot.le))
  · have hKc : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K₁ := h𝒞comp K₁ hK₁
    have hcl : ∀ L ∈ 𝒞, L ≤ closureIn K₁ B := by
      intro L hL
      obtain ⟨e, he, rfl⟩ := h𝒞trans K₁ hK₁ L hL
      have hconj : GLBConj e K₁ = K₁.map (MulAut.conj e⁻¹).toMonoidHom := rfl
      rw [hconj]
      exact le_iSup₂_of_le (f := fun a (_ : a ∈ B) => K₁.map (MulAut.conj a).toMonoidHom) e⁻¹
        (B.inv_mem (hDB he)) le_rfl
    have hJcl : J ≤ closureIn K₁ B := hJsup.trans (iSup₂_le fun L hL => hcl L hL)
    refine ⟨K₁, hKc, hJcl, ?_⟩
    unfold IsGStar
    refine ⟨E, hR.E_le, hE, hR.card_E, ?_⟩
    have hCED : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (D : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hR.D_le)
    have hsub1 : IsSubnormal (J ⊓ closureIn K₁ B) (Subgroup.centralizer (D : Set G) ⊓ closureIn K₁ B) :=
      isSubnormal_inf hJD.2.1 _
    rw [inf_eq_left.2 hJcl] at hsub1
    have hsub2 : IsSubnormal (J ⊓ Subgroup.centralizer (E : Set G))
        ((Subgroup.centralizer (D : Set G) ⊓ closureIn K₁ B) ⊓ Subgroup.centralizer (E : Set G)) :=
      isSubnormal_inf hsub1 _
    have hKE : (Subgroup.centralizer (D : Set G) ⊓ closureIn K₁ B) ⊓ Subgroup.centralizer (E : Set G)
        = closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G) := by
      rw [inf_comm (Subgroup.centralizer (D : Set G)) (closureIn K₁ B), inf_assoc,
        inf_eq_right.2 hCED]
    rw [hKE] at hsub2
    have hYex : ∃ Y : Subgroup G, GLAPComponent p (J ⊓ Subgroup.centralizer (E : Set G)) Y := by
      rcases Set.eq_empty_or_nonempty
          {L : Subgroup G | GLAPComponent p (J ⊓ Subgroup.centralizer (E : Set G)) L} with h0 | ⟨Y, hY⟩
      · exfalso
        apply hR.J_layer
        show sSup {L : Subgroup G | GLAPComponent p (J ⊓ Subgroup.centralizer (E : Set G)) L} = ⊥
        rw [h0, sSup_empty]
      · exact ⟨Y, hY⟩
    obtain ⟨Y, hY⟩ := hYex
    have hY' : GLAPComponent p (J ⊓ Subgroup.centralizer (E : Set G)) Y := hY
    have hYK : GLAPComponent p (closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G)) Y :=
      glaPComponent_of_isSubnormal' hp hsub2 hY'
    intro h0
    apply glaPComponent_ne_bot' hYK
    have hYmem : Y ∈ {L : Subgroup G | GLAPComponent p (closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G)) L} :=
      hYK
    exact le_bot_iff.1 ((le_sSup hYmem).trans h0.le)

theorem S_le_closure (hH : Hyp111 G m p B x L) (hR : RedB G p q B x L M D E F J) {a : G} (haD : a ∈ D) {K₁ S : Subgroup G}
    (hK₁ : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K₁) (hJK : J ≤ closureIn K₁ B)
    (hS : S = ⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆)
    (hSJ : (⁅S, J⁆ : Subgroup G) = S) : S ≤ closureIn K₁ B := by
  have hp : p.Prime := hH.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hDB : D ≤ B := hR.D_le.trans hR.E_le
  have haB : a ∈ B := hDB haD
  have hBn : ∀ c ∈ B, GLBConj c⁻¹ (Subgroup.centralizer ({a} : Set G)) = Subgroup.centralizer ({a} : Set G) :=
    fun c hc => gLBConj_eq_of_mem_normalizer
      (cfC_mem_normalizer_centralizer (cfC_inv_comm (isElemAbelian_commute hH.elem hc haB)))
  have hK1c : ∀ c ∈ B, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) (GLBConj c⁻¹ K₁) := fun c hc => by
    have h1 := glaPComponent_gLBConj hK₁ c⁻¹
    rwa [hBn c hc] at h1
  have hKle : ∀ c ∈ B, GLBConj c⁻¹ K₁ ≤ closureIn K₁ B := fun c hc => by
    rw [cfC_gLBConj_inv_eq]
    exact le_iSup₂_of_le (f := fun a (_ : a ∈ B) => K₁.map (MulAut.conj a).toMonoidHom) c hc le_rfl
  have hKlayer : closureIn K₁ B ≤ GLAPLayer p (Subgroup.centralizer ({a} : Set G)) := by
    refine (iSup₂_le fun c hc => ?_ : (⨆ c : G, ⨆ (_ : c ∈ B), K₁.map (MulAut.conj c).toMonoidHom) ≤ _)
    rw [← cfC_gLBConj_inv_eq]
    exact le_sSup (hK1c c hc)
  have hnormY : ∀ Y : Subgroup G, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) Y →
      Y ≤ Subgroup.normalizer ((closureIn K₁ B : Subgroup G) : Set G) := by
    intro Y hY
    by_cases hex : ∃ c ∈ B, GLBConj c⁻¹ K₁ = Y
    · obtain ⟨c, hc, rfl⟩ := hex
      exact (hKle c hc).trans Subgroup.le_normalizer
    · simp only [not_exists, not_and] at hex
      intro y hy
      refine cfC_mem_normalizer_closureIn fun c hc => ?_
      rw [← cfC_gLBConj_inv_eq]
      exact (le_centModSubgroup_of_ne hp hY (hK1c c hc) (Ne.symm (hex c hc)) hy).1
  have hlayN : GLAPLayer p (Subgroup.centralizer ({a} : Set G)) ≤
      Subgroup.normalizer ((closureIn K₁ B : Subgroup G) : Set G) := by
    show sSup {Y : Subgroup G | GLAPComponent p (Subgroup.centralizer ({a} : Set G)) Y} ≤ _
    exact sSup_le fun Y hY => hnormY Y hY
  have hT₀N : ∀ t ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G),
      t ∈ Subgroup.normalizer (GLAPLayer p (Subgroup.centralizer ({a} : Set G)) : Set G) := fun t ht =>
    cfC_mem_normalizer_layer (cfC_mem_normalizer_centralizer
      (Subgroup.mem_centralizer_singleton_iff.1 ht.2))
  have hSL : S ≤ GLAPLayer p (Subgroup.centralizer ({a} : Set G)) := by
    rw [hS, Subgroup.commutator_le]
    intro j hj t ht
    have hjL : j ∈ GLAPLayer p (Subgroup.centralizer ({a} : Set G)) := hKlayer (hJK hj)
    rw [commutatorElement_def]
    have h1 : t * j⁻¹ * t⁻¹ ∈ GLAPLayer p (Subgroup.centralizer ({a} : Set G)) :=
      (Subgroup.mem_normalizer_iff.1 (hT₀N t ht) j⁻¹).1
        ((GLAPLayer p (Subgroup.centralizer ({a} : Set G))).inv_mem hjL)
    have e : j * t * j⁻¹ * t⁻¹ = j * (t * j⁻¹ * t⁻¹) := by group
    rw [e]
    exact (GLAPLayer p (Subgroup.centralizer ({a} : Set G))).mul_mem hjL h1
  have hSN : S ≤ Subgroup.normalizer ((closureIn K₁ B : Subgroup G) : Set G) := hSL.trans hlayN
  have hcomm : (⁅S, J⁆ : Subgroup G) ≤ closureIn K₁ B := Subgroup.commutator_le.2 fun s hs j hj => by
    rw [commutatorElement_def]
    have h1 : s * j * s⁻¹ ∈ closureIn K₁ B := (Subgroup.mem_normalizer_iff.1 (hSN hs) j).1 (hJK hj)
    exact (closureIn K₁ B).mul_mem h1 ((closureIn K₁ B).inv_mem (hJK hj))
  rw [hSJ] at hcomm
  exact hcomm

theorem K_single (hctx : ThmACtx G m) (h183 : Input18_3_4) (hH : Hyp111 G m p B x L) (hR : RedB G p q B x L M D E F J)
    {a : G} (haD : a ∈ D) {K₁ S : Subgroup G}
    (hK₁ : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K₁) (hJK : J ≤ closureIn K₁ B)
    (hS : S = ⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆) (hSne : S ≠ ⊥) (hSJ : (⁅S, J⁆ : Subgroup G) = S)
    (hSK : S ≤ closureIn K₁ B) (hSB : B ≤ Subgroup.normalizer (S : Set G)) (hS2 : IsPGroup 2 S)
    (hSc : ¬ S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))) : closureIn K₁ B = K₁ := by
  have hp : p.Prime := hH.prime
  have hp2 : p ≠ 2 := hH.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hDB : D ≤ B := hR.D_le.trans hR.E_le
  have haB : a ∈ B := hDB haD
  have hBa : ∀ c ∈ B, c * a = a * c := fun c hc => isElemAbelian_commute hH.elem hc haB
  have hJN : J ≤ Subgroup.normalizer (S : Set G) := by
    rw [hS]
    exact le_normalizer_commutator Subgroup.le_normalizer (J_le_normalizer_T0_of_redB hR haD)
  by_cases ha1 : a = 1
  ·
    have hC1 : Subgroup.centralizer ({a} : Set G) = ⊤ := by
      rw [ha1, eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_singleton_iff, one_mul, mul_one]
    rw [hC1] at hK₁
    have hK1top : K₁ = ⊤ := by
      by_contra hne
      obtain ⟨M', hKM, -, hMne, hMn, -⟩ := isSubnormal_exists_normal hK₁.2.1 hne
      have hMnorm : M'.Normal := by
        have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : M' ≤ ⊤)).1 hMn
        exact Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 h1)
      haveI : IsSimpleGroup G := hctx.1.simple
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M' with h | h
      · exact glaPComponent_ne_bot' hK₁ (le_bot_iff.1 (h ▸ hKM))
      · exact hMne h
    rw [hK1top]
    exact eq_top_iff.2 (le_iSup₂_of_le (f := fun c (_ : c ∈ B) => (⊤ : Subgroup G).map (MulAut.conj c).toMonoidHom)
      1 B.one_mem (by simp))
  ·
    have hCA : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
        Subgroup.centralizer ({a} : Set G) := S3.centralizer_zpowers a
    have hAD : Subgroup.zpowers a ≤ D := Subgroup.zpowers_le.2 haD
    have hDel : IsElemAbelian p D := isElemAbelian_mono hH.elem hDB
    have hord : orderOf a = p := orderOf_eq_prime (hDel.2 a haD) ha1
    have hAcard : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
    have hidx : ((Subgroup.zpowers a).subgroupOf D).index = p := by
      have h1 := Subgroup.card_mul_index ((Subgroup.zpowers a).subgroupOf D)
      have h2 : Nat.card ((Subgroup.zpowers a).subgroupOf D) = p := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv, hAcard]
      rw [h2, hR.card_D, pow_two] at h1
      exact Nat.eq_of_mul_eq_mul_left hp.pos h1
    have hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)) := by
      rw [hCA]
      exact S8.isKGroup_cx (S3Ctx.of_ctx hctx hH.mu) ha1
    have hJD : GLAPComponent p (Subgroup.centralizer (D : Set G)) J :=
      S9.glaPComponent_centralizer hp hH.comp hR.x_mem hR.J_comp
    obtain ⟨𝒞, hcomp, hsup, hinv, htrans, hJK', hne⟩ :=
      L62.exists_family hp h183 hX hAD hDel hJD
    have hSC : S ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [hS]
      exact (S_le_T0_of_redB hR haD).trans inf_le_right
    have hSA : S ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
      rw [hCA]
      exact hSC
    have hSJ' : S ≤ ⁅S, J⁆ := le_of_eq hSJ.symm
    have hKsub := L62.layerClosure_isSubnormal hp hcomp hsup
    have hSK' : S ≤ layerClosure p (Subgroup.zpowers a) J :=
      L62.le_of_subnormal_comm_eq hKsub hJK' hSA hSJ'
    have hJS : J ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p (layerClosure p (Subgroup.zpowers a) J) :
        Subgroup G) : Set G) := fun j hj =>
      CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_normalizer_sup (hJN hj)
        (le_normalizer_glaPPrimeCoreOf p _ (hJK' hj))
    by_cases h2 : ∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂
    ·
      exfalso
      have hproj := i183DiagAt_holds G p hp hp2 (Subgroup.zpowers a) D J 𝒞 hDel hAD hidx hX hJD
        hcomp hsup hinv htrans h2
      have hcomm := L62.claim_of_projection hp hcomp hsup hKsub hJK' hS2 hSK' hJS hproj
      have hSO : S ≤ GLAPPrimeCoreOf p (layerClosure p (Subgroup.zpowers a) J) := by
        rw [← hSJ]
        exact hcomm
      have hO := glaPPrimeCoreOf_le_of_isSubnormal hp hKsub
      rw [hCA] at hO
      exact hSc (hSO.trans hO)
    ·
      push Not at h2
      obtain ⟨K₀, hK₀⟩ := hne
      have hLK₀ : layerClosure p (Subgroup.zpowers a) J = K₀ := by
        rw [← hsup]
        exact le_antisymm (iSup₂_le fun C hC => (h2 C hC K₀ hK₀).le) (le_iSup₂_of_le K₀ hK₀ le_rfl)
      have hBC : B ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
        rw [hCA]
        exact fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hBa b hb)
      have hLeq : layerClosure p (Subgroup.zpowers a) J =
          closureIn J (GLAPLayer p (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G))) :=
        (closureIn_eq_iSup_gLBConj J _).symm
      have hBN : B ≤ Subgroup.normalizer (layerClosure p (Subgroup.zpowers a) J : Set G) := by
        rw [hLeq]
        exact L62.le_normalizer_closureIn_of_le hR.B_norm (hBC.trans (L62.le_normalizer_glaPLayer p _))
      rw [hLK₀] at hBN
      have hK₀K : K₀ ≤ closureIn K₁ B := by
        rw [← hLK₀]
        refine iSup₂_le fun g hg => ?_
        have hg' : g ∈ GLAPLayer p (Subgroup.centralizer ({a} : Set G)) := by
          rw [hCA] at hg
          exact hg
        have hgN := cfC_layer_le_normalizer_closureIn hp hBa hK₁ hg'
        calc GLBConj g J ≤ GLBConj g (closureIn K₁ B) := gLBConj_mono hJK
          _ = closureIn K₁ B := gLBConj_eq_of_mem_normalizer hgN
      have hK₀c : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K₀ := by
        have h0 := hcomp K₀ hK₀
        rw [hCA] at h0
        exact h0
      have hsub : closureIn K₁ B ≤
          sSup {Y : Subgroup G | ∃ c ∈ B, Y = K₁.map (MulAut.conj c).toMonoidHom} := by
        unfold closureIn
        exact iSup₂_le fun c hc => le_sSup ⟨c, hc, rfl⟩
      have hmemK₀ : K₀ ∈ {Y : Subgroup G | ∃ c ∈ B, Y = K₁.map (MulAut.conj c).toMonoidHom} :=
        mem_of_le_sSup_glaPComponent hp _
          (fun Y hY => by
            obtain ⟨c, hc, rfl⟩ := hY
            exact cfC_conj_component hBa hK₁ hc)
          hK₀c (hK₀K.trans hsub)
      obtain ⟨c, hc, hKc⟩ := hmemK₀
      have hK₀eq : K₀ = GLBConj c⁻¹ K₁ := by
        rw [hKc, cfC_gLBConj_inv_eq]
      have hBK₁ : ∀ x ∈ B, x ∈ Subgroup.normalizer (K₁ : Set G) := by
        intro x hx
        have hx0 : x ∈ Subgroup.normalizer (K₀ : Set G) := hBN hx
        rw [hK₀eq] at hx0
        have e1 : GLBConj x (GLBConj c⁻¹ K₁) = GLBConj c⁻¹ K₁ := mem_normalizer_iff_gLBConj_eq.1 hx0
        rw [gLBConj_gLBConj] at e1
        have e2 := congrArg (GLBConj c) e1
        rw [gLBConj_gLBConj, gLBConj_gLBConj] at e2
        have hcx : c⁻¹ * x = x * c⁻¹ := isElemAbelian_commute hH.elem (B.inv_mem hc) hx
        have hfin : c⁻¹ * x * c = x := by
          rw [hcx, mul_assoc, inv_mul_cancel, mul_one]
        rw [hfin, inv_mul_cancel, gLBConj_one] at e2
        exact mem_normalizer_iff_gLBConj_eq.2 e2
      apply le_antisymm
      · unfold closureIn
        refine iSup₂_le fun b hb => ?_
        rw [← cfC_gLBConj_inv_eq]
        exact le_of_eq (mem_normalizer_iff_gLBConj_eq.1 (hBK₁ b⁻¹ (B.inv_mem hb)))
      · refine le_iSup₂_of_le (f := fun b (_ : b ∈ B) => K₁.map (MulAut.conj b).toMonoidHom) 1 B.one_mem
          (le_of_eq ?_)
        rw [← cfC_gLBConj_inv_eq, inv_one, gLBConj_one]

theorem S_not_le_core (hsf : StageFacts G m) (hH : Hyp111 G m p B x L) {a : G} {K₁ S : Subgroup G}
    (ha1 : a ≠ 1) (haB : a ∈ B) (hK₁ : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K₁)
    (hG : IsGStar p B K₁) (hJK : J ≤ closureIn K₁ B) (hSne : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hSJ : (⁅S, J⁆ : Subgroup G) = S) :
    ¬ S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) := by
  intro hSc
  obtain ⟨-, -, h4, -⟩ := hsf p hH.mu
  have hodd := h4.2.1 B a K₁ hH.bmax haB ha1 hK₁ hG
  have hle : S ≤ ⁅closureIn K₁ B, GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))⁆ := by
    calc S = ⁅S, J⁆ := hSJ.symm
      _ ≤ ⁅GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)), closureIn K₁ B⁆ :=
          Subgroup.commutator_mono hSc hJK
      _ = ⁅closureIn K₁ B, GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))⁆ :=
          Subgroup.commutator_comm _ _
  have hodd' : Odd (Nat.card S) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  exact hSne (S9.eq_bot_of_two_group_odd hS2 hodd')

theorem exists_conf (hctx : ThmACtx G m) (hsf : StageFacts G m) (h183 : Input18_3_4) (hH : Hyp111 G m p B x L)
    (hR : RedB G p q B x L M D E F J) :
    ∃ (a : G) (S K : Subgroup G), CConf G p q B x L M D E F J a S K := by
  obtain ⟨a, haD, ha1, hSne⟩ := exists_a hctx hH hR
  obtain ⟨hS2, hSB, hSJ⟩ := S_facts hH hR haD
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, S = ⁅J, pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G)⁆ := ⟨_, rfl⟩
  rw [← hS] at hSne hS2 hSB hSJ
  have haB : a ∈ B := (hR.D_le.trans hR.E_le) haD
  obtain ⟨K₁, hK₁, hJK, hGstar⟩ := exists_Gstar_component' hctx h183 hH hR haD ha1
  have hSc : ¬ S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) :=
    S_not_le_core hsf hH ha1 haB hK₁ hGstar hJK hSne hS2 hSJ
  have hSK : S ≤ closureIn K₁ B := S_le_closure hH hR haD hK₁ hJK hS hSJ
  have hKs : closureIn K₁ B = K₁ := K_single hctx h183 hH hR haD hK₁ hJK hS hSne hSJ hSK hSB hS2 hSc
  have hKN : B ≤ Subgroup.normalizer (K₁ : Set G) := by
    have := le_normalizer_closureIn K₁ B
    rwa [hKs] at this
  refine ⟨a, S, K₁, ⟨hR, haD, ha1, hS, hSne, hS2, hSB, hSJ, hS ▸ S_le_T0_of_redB hR haD, hK₁, hKs ▸ hJK, hKN,
    hGstar, hKs ▸ hSK⟩⟩

theorem a_essential (hH : Hyp111 G m p B x L) (hR : RedB G p q B x L M D E F J) {a : G} {S K : Subgroup G}
    (hc : CConf G p q B x L M D E F J a S K) : IsEssential p B a := by
  have hp : p.Prime := hH.prime
  have hp2 : p ≠ 2 := hH.ne_two
  have haB : a ∈ B := (hR.D_le.trans hR.E_le) hc.a_mem
  have hmax : ∀ E' : Subgroup G, IsElemAbelian p E' → B ≤ E' → E' ≤ J ⊔ B → E' = B := by
    intro E' hE' hBE' hE'JB
    have hMJB : J ⊔ B ≤ M := sup_le (J_le_M_of_redB hR) (B_le_M_of_redB hH hR)
    have hle := cfC_card_le_of_twoLocal hp hR.two_local (hE'JB.trans hMJB) hE'
    have hmB : GLATwoLocalRank p G = m := hH.mu.2.1
    rw [hmB] at hle
    exact (Subgroup.eq_of_le_of_card_ge hBE' (by rw [hH.card_B]; exact hle)).symm
  have hJB : J ≤ ⁅J, B⁆ := P51.le_commutator_of_maximal hp hp2 hR.J_comp hH.elem hR.B_norm hmax
  have hSB : (⁅S, B⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    apply hc.S_ne
    have h1 : (⁅⁅S, J⁆, B⁆ : Subgroup G) = ⊥ := by rw [hc.S_comm, hbot]
    have h2 : (⁅⁅B, S⁆, J⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_comm B S, hbot, Subgroup.commutator_bot_left]
    have h3 : (⁅⁅J, B⁆, S⁆ : Subgroup G) = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    have h4 : (⁅J, S⁆ : Subgroup G) ≤ ⊥ := by
      calc (⁅J, S⁆ : Subgroup G) ≤ ⁅⁅J, B⁆, S⁆ := Subgroup.commutator_mono hJB le_rfl
        _ = ⊥ := h3
    rw [Subgroup.commutator_comm] at h4
    rw [← hc.S_comm]
    exact le_bot_iff.1 h4
  refine ⟨haB, hc.a_ne, S, hc.S_le_T0.trans inf_le_right, hc.S_two, hc.S_normB, hSB, ?_⟩
  intro _hp3
  refine ⟨fun e => ?_⟩
  have hperf : (⁅J, J⁆ : Subgroup G) = J := glaPComponent_perfect hR.J_comp
  have h24 : Nat.card (MulAut ↥S) = 24 :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.natCard_mulAut_of_quaternion e
  haveI : Finite (MulAut ↥S) := Nat.finite_of_card_ne_zero (by rw [h24]; norm_num)
  haveI : Fintype (MulAut ↥S) := Fintype.ofFinite _
  haveI hsolv : Group.IsSolvable (MulAut ↥S) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three
      (by norm_num) (a := 3) (b := 1) (by rw [← Nat.card_eq_fintype_card, h24]; norm_num)
  have hIN : J ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [hc.S_def]
    exact le_normalizer_commutator Subgroup.le_normalizer (J_le_normalizer_T0_of_redB hR hc.a_mem)
  let φ : ↥J →* MulAut ↥S := (Subgroup.normalizerMonoidHom S).comp (Subgroup.inclusion hIN)
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hperf
  have hφ : φ = 1 := CFSG.Holt.General.eq_one_of_isPerfect_of_isSolvable_range φ inferInstance
  have hcent : J ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : φ ⟨i, hi⟩ = 1 := by rw [hφ]; rfl
    have h2 := congrArg (fun α : MulAut ↥S => ((α ⟨s, hs⟩ : ↥S) : G)) h1
    have e1 : ((φ ⟨i, hi⟩ ⟨s, hs⟩ : ↥S) : G) = i * s * i⁻¹ := rfl
    simp only [MulAut.one_apply] at h2
    rw [e1] at h2
    calc s * i = (i * s * i⁻¹) * i := by rw [h2]
      _ = i * s := by group
  have hbot : (⁅S, J⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  apply hc.S_ne
  rw [← hc.S_comm, hbot]

theorem J_lt_K (hH : Hyp111 G m p B x L) (hR : RedB G p q B x L M D E F J) {a : G} {S K : Subgroup G}
    (hc : CConf G p q B x L M D E F J a S K) (hSc : ¬ S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))) :
    ¬ K ≤ J ⊔ GLAPPrimeCoreOf p K := by
  intro hle
  have hp : p.Prime := hH.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hH.ne_two
  have hKq : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hc.K_comp
  have hJN : J ≤ Subgroup.normalizer (S : Set G) := by
    rw [hc.S_def]
    exact le_normalizer_commutator Subgroup.le_normalizer (J_le_normalizer_T0_of_redB hR hc.a_mem)
  have hmapTop : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hTop : (⊤ : Subgroup ↥K) ≤ J.subgroupOf K ⊔ GLAPPrimeCore p ↥K := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := K.subtype) (Subgroup.subtype_injective K)]
    rw [hmapTop, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hc.J_le]
    exact hle
  have hdec : ∀ k : ↥K, ∃ j ∈ J.subgroupOf K, ∃ u ∈ GLAPPrimeCore p ↥K, j * u = k := by
    intro k
    exact Subgroup.mem_sup_of_normal_right.1 (hTop (Subgroup.mem_top k))
  have hŜn : ((S.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hn
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥K) g
    obtain ⟨j, hj, u, hu, rfl⟩ := hdec k
    have hu1 : QuotientGroup.mk' (GLAPPrimeCore p ↥K) u = 1 := (QuotientGroup.eq_one_iff u).2 hu
    rw [map_mul, hu1, mul_one]
    have hjG : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
    have htG : (t : G) ∈ S := Subgroup.mem_subgroupOf.1 ht
    have hconj : (j : G) * (t : G) * (j : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.1 (hJN hjG) (t : G)).1 htG
    have hmem : j * t * j⁻¹ ∈ S.subgroupOf K := Subgroup.mem_subgroupOf.2 (by simpa using hconj)
    have hconjπ : QuotientGroup.mk' (GLAPPrimeCore p ↥K) j * QuotientGroup.mk' (GLAPPrimeCore p ↥K) t *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥K) j)⁻¹ =
          QuotientGroup.mk' (GLAPPrimeCore p ↥K) (j * t * j⁻¹) := by
      simp [map_mul, map_inv]
    rw [hconjπ]
    exact Subgroup.mem_map_of_mem _ hmem
  by_cases hŜtop : (S.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) = ⊤
  ·
    exfalso
    have h2Q : IsPGroup 2 (PQuot p K) := by
      intro g
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥K) g
      have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥K) k ∈
          (S.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) := by
        rw [hŜtop]
        exact Subgroup.mem_top _
      obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 hmem
      obtain ⟨n, hn⟩ := hc.S_two ⟨(t : G), Subgroup.mem_subgroupOf.1 ht⟩
      have ht2 : t ^ 2 ^ n = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hn
        simpa using this
      refine ⟨n, ?_⟩
      rw [← hte, ← map_pow, ht2, map_one]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent (PQuot p K) := h2Q.isNilpotent
    haveI : Nontrivial (PQuot p K) := isQuasisimple_nontrivial hKq
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (PQuot p K)).ne hKq.1
  ·
    have hcen := le_center_of_normal_of_isQuasisimple hKq hŜn hŜtop
    have hSPk : S ≤ GLAPPrimeCoreOf p K := by
      intro s hs
      have hsK : s ∈ K := hc.S_le_K hs
      have htT : (⟨s, hsK⟩ : ↥K) ∈ S.subgroupOf K := Subgroup.mem_subgroupOf.2 hs
      have hz : QuotientGroup.mk' (GLAPPrimeCore p ↥K) (⟨s, hsK⟩ : ↥K) ∈
          Subgroup.center (PQuot p K) := hcen (Subgroup.mem_map_of_mem _ htT)
      obtain ⟨k, hk⟩ := (S9.pComponent_basic hp hc.K_comp).2.2.1 _ hz
      obtain ⟨n, hn⟩ := hc.S_two ⟨s, hs⟩
      have hn' : (⟨s, hsK⟩ : ↥K) ^ 2 ^ n = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hn
        simpa using this
      have hπ2 : QuotientGroup.mk' (GLAPPrimeCore p ↥K) (⟨s, hsK⟩ : ↥K) ^ 2 ^ n = 1 := by
        rw [← map_pow, hn', map_one]
      have hcop : Nat.Coprime (p ^ k) (2 ^ n) :=
        Nat.Coprime.pow k n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
      have hone := (pow_gcd_eq_one (a := QuotientGroup.mk' (GLAPPrimeCore p ↥K) (⟨s, hsK⟩ : ↥K))).2
        ⟨hk, hπ2⟩
      rw [hcop.gcd_eq_one, pow_one] at hone
      have htN : (⟨s, hsK⟩ : ↥K) ∈ GLAPPrimeCore p ↥K := (QuotientGroup.eq_one_iff _).1 hone
      exact Subgroup.mem_map.2 ⟨⟨s, hsK⟩, htN, rfl⟩
    exact hSc (hSPk.trans (glaPPrimeCoreOf_le_of_isSubnormal hp hc.K_comp.2.1))

end S11

end CFSG.LocalAnalysis.GLTheoremA
