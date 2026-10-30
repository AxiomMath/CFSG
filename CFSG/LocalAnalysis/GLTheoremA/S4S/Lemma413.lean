module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.LocalAnalysis.GLTheoremA.S4.StepTools
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem layer_closureIn {p : ℕ} (hp : p.Prime) {Y K₁ B : Subgroup G}
    (hK₁ : GLAPComponent p Y K₁) (hBY : B ≤ Subgroup.normalizer (Y : Set G)) :
    closureIn K₁ B ≤ Y ∧ B ≤ Subgroup.normalizer (closureIn K₁ B : Set G) ∧
      GLAPPrimeCoreOf p Y ≤ Subgroup.normalizer (closureIn K₁ B : Set G) ∧
      GLAPLayer p (closureIn K₁ B) = closureIn K₁ B := by
  obtain ⟨𝓛, h𝓛def⟩ : ∃ 𝓛 : Set (Subgroup G), 𝓛 = {X | ∃ b ∈ B, GLBConj b K₁ = X} :=
    ⟨_, rfl⟩
  have hmem : ∀ X, X ∈ 𝓛 ↔ ∃ b ∈ B, GLBConj b K₁ = X := fun X => by
    rw [h𝓛def, Set.mem_setOf_eq]
  have h𝓛C : ∀ X ∈ 𝓛, GLAPComponent p Y X := by
    intro X hX
    obtain ⟨b, hb, rfl⟩ := (hmem X).1 hX
    have := glaPComponent_gLBConj hK₁ b
    rwa [mem_normalizer_iff_gLBConj_eq.1 (hBY hb)] at this
  have hsup : sSup 𝓛 = closureIn K₁ B := by
    apply le_antisymm
    · refine sSup_le fun X hX => ?_
      obtain ⟨b, hb, rfl⟩ := (hmem _).1 hX
      rw [closureIn_eq_iSup_gLBConj K₁ B]
      exact le_biSup (fun g => GLBConj g K₁) hb
    · rw [closureIn_eq_iSup_gLBConj K₁ B]
      refine iSup₂_le fun b hb => ?_
      exact le_sSup ((hmem _).2 ⟨b, hb, rfl⟩)
  have hKY : closureIn K₁ B ≤ Y := by
    rw [← hsup]
    exact sSup_le fun X hX => (h𝓛C X hX).1
  refine ⟨hKY, le_normalizer_closureIn K₁ B, ?_, ?_⟩
  · rw [← hsup]
    intro o ho
    exact mem_normalizer_sSup fun X hX =>
      CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPPrimeCoreOf_le_normalizer (h𝓛C X hX) ho
  · apply le_antisymm
    · exact sSup_le fun L hL => (show GLAPComponent p (closureIn K₁ B) L from hL).1
    · calc closureIn K₁ B = sSup 𝓛 := hsup.symm
        _ ≤ GLAPLayer p (closureIn K₁ B) := by
          refine sSup_le fun X hX => ?_
          have hXK : X ≤ closureIn K₁ B := hsup ▸ le_sSup hX
          exact le_sSup (show GLAPComponent p (closureIn K₁ B) X from
            glaPComponent_of_le hp (h𝓛C X hX) hXK hKY)

theorem commutator_oPrime_facts {p : ℕ} (hp : p.Prime) {Y K₁ B : Subgroup G}
    (hK₁ : GLAPComponent p Y K₁) (hBY : B ≤ Subgroup.normalizer (Y : Set G)) :
    (⁅closureIn K₁ B, GLAPPrimeCoreOf p Y⁆ : Subgroup G) ≤ closureIn K₁ B ∧
    (⁅closureIn K₁ B, GLAPPrimeCoreOf p Y⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p Y ∧
    closureIn K₁ B ≤
      Subgroup.normalizer ((⁅closureIn K₁ B, GLAPPrimeCoreOf p Y⁆ : Subgroup G) : Set G) ∧
    B ≤ Subgroup.normalizer ((⁅closureIn K₁ B, GLAPPrimeCoreOf p Y⁆ : Subgroup G) : Set G) ∧
    (⁅closureIn K₁ B, GLAPPrimeCoreOf p Y⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (closureIn K₁ B) ∧
    Nat.Coprime p (Nat.card (⁅closureIn K₁ B, GLAPPrimeCoreOf p Y⁆ : Subgroup G)) := by
  obtain ⟨hKY, hBK, hObK, -⟩ := layer_closureIn hp hK₁ hBY
  set K : Subgroup G := closureIn K₁ B with hK
  set Ob : Subgroup G := GLAPPrimeCoreOf p Y with hOb
  have hOnY : Y ≤ Subgroup.normalizer (Ob : Set G) := le_normalizer_glaPPrimeCoreOf p Y
  have hBnOb : B ≤ Subgroup.normalizer (Ob : Set G) :=
    hBY.trans (normalizer_le_normalizer_glaPPrimeCoreOf p Y)
  have hXK : (⁅K, Ob⁆ : Subgroup G) ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk o ho
    rw [commutatorElement_def]
    have h1 : o * k⁻¹ * o⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hObK ho) k⁻¹).1 (K.inv_mem hk)
    simpa [mul_assoc] using K.mul_mem hk h1
  have hXle : (⁅K, Ob⁆ : Subgroup G) ≤ Ob := by
    rw [Subgroup.commutator_le]
    intro k hk o ho
    rw [commutatorElement_def]
    have h1 : k * o * k⁻¹ ∈ Ob := (Subgroup.mem_normalizer_iff.1 (hOnY (hKY hk)) o).1 ho
    exact Ob.mul_mem h1 (Ob.inv_mem ho)
  have hcopOb : Nat.Coprime p (Nat.card Ob) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp Y
  have hcopX : Nat.Coprime p (Nat.card (⁅K, Ob⁆ : Subgroup G)) :=
    hcopOb.coprime_dvd_right (Subgroup.card_dvd_of_le hXle)
  have hKX : K ≤ Subgroup.normalizer ((⁅K, Ob⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer (hKY.trans hOnY)
  have hBX : B ≤ Subgroup.normalizer ((⁅K, Ob⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hBK hBnOb
  refine ⟨hXK, hXle, hKX, hBX, ?_, hcopX⟩
  refine CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal hXK ?_ hcopX
  intro g hg x hx
  exact (Subgroup.mem_normalizer_iff.1 (hKX hg) x).1 hx

private theorem barX_oPPrimeP_413 (p : ℕ) (X : Subgroup G) :
    barX p X (oPPrimeP p X) = CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := by
  have hJg : (oPPrimeP p X).subgroupOf X =
      (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  show ((oPPrimeP p X).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = _
  rw [hJg]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem J_not_le_centralizer {p : ℕ} (hp : p.Prime) {K J R : Subgroup G} (hJK : J ≤ K)
    (hJ : GLAPLayer p J = J) (hJ1 : J ≠ ⊥)
    (hC : K ⊓ Subgroup.centralizer (R : Set G) ≤ oPPrimeP p K) :
    ¬ J ≤ Subgroup.centralizer (R : Set G) := by
  intro hJC
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, GLAPComponent p J T := by
    by_contra hcon
    push Not at hcon
    apply hJ1
    refine le_bot_iff.1 ?_
    rw [← hJ]
    unfold GLAPLayer
    exact sSup_le fun T hT => absurd hT (hcon T)
  have hTJ : T ≤ J := hT.1
  have hTK : T ≤ K := hTJ.trans hJK
  have hTO : T ≤ oPPrimeP p K := fun t ht => hC ⟨hTK ht, hJC (hTJ ht)⟩
  have hperf : ⁅barX p K T, barX p K T⁆ = barX p K T := by
    rw [← barX_commutator p hTK hTK, glaPComponent_perfect hT]
  haveI : Group.IsPerfect ↥(barX p K T) := Subgroup.isPerfect_iff.2 hperf
  have hle : barX p K T ≤ CFSG.pCore p (↥K ⧸ GLAPPrimeCore p ↥K) :=
    (barX_mono p hTO).trans (barX_oPPrimeP_413 p K).le
  have hpg : IsPGroup p ↥(barX p K T) :=
    IsPGroup.to_le (CFSG.pCore_isPGroup (p := p) (G := ↥K ⧸ GLAPPrimeCore p ↥K)) hle
  have htriv : barX p K T = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(barX p K T) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isNilpotent ↥(barX p K T) (IsPGroup.isNilpotent hpg)
  have hTO' : T ≤ GLAPPrimeCoreOf p K := by
    intro t ht
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥K) (⟨t, hTK ht⟩ : ↥K) :
        ↥K ⧸ GLAPPrimeCore p ↥K) ∈ barX p K T :=
      Subgroup.mem_map.2 ⟨⟨t, hTK ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
    rw [htriv, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_map.2 ⟨⟨t, hTK ht⟩, (QuotientGroup.eq_one_iff _).1 hmem, rfl⟩
  have hd1 : p ∣ Nat.card (PQuot p T) := dvd_card_pQuot_of_component hp hT
  have hd2 : Nat.card (PQuot p T) ∣ Nat.card ↥T := Subgroup.card_quotient_dvd_card _
  have hd3 : Nat.card ↥T ∣ Nat.card ↥(GLAPPrimeCoreOf p K) := Subgroup.card_dvd_of_le hTO'
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p K)) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp K
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop ((hd1.trans hd2).trans hd3))

theorem exists_D_commutator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E R J : Subgroup G}
    (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) (hER : E ≤ Subgroup.normalizer (R : Set G)) (hR : IsPGroup 2 R)
    (hJR : J ≤ Subgroup.normalizer (R : Set G)) (hJE : J ≤ Subgroup.centralizer (E : Set G))
    (hnc : ¬ J ≤ Subgroup.centralizer (R : Set G)) :
    ∃ D : Subgroup G, D ≤ E ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧
      (⁅R ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) ≠ ⊥ := by
  classical
  by_contra hcon
  push Not at hcon
  apply hnc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpE : p ≤ Nat.card E := by
    rw [hEc]
    exact Nat.le_self_pow (by norm_num) p
  have hcop : Nat.Coprime p (Nat.card R) := by
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes hp hE hpE hER hcop
  have hle : R ≤ Subgroup.centralizer (J : Set G) := by
    rw [← hgen]
    refine iSup₂_le fun D hD => ?_
    have hDc : Nat.card D = p ^ 2 := by
      have h1 := hD.2
      rw [hEc] at h1
      have h2 : p * p ^ 2 = p * Nat.card D := by rw [← h1]; ring
      exact (Nat.eq_of_mul_eq_mul_left hp.pos h2).symm
    have hDel : IsElemAbelian p D := isElemAbelian_mono hE hD.1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcon D hD.1 hDel hDc)
  exact Subgroup.le_centralizer_iff.2 hle

theorem layer_inf_centralizer_le {p : ℕ} (hp : p.Prime) {Y K₁ B E : Subgroup G}
    (hK₁ : GLAPComponent p Y K₁) (hBY : B ≤ Subgroup.normalizer (Y : Set G)) :
    GLAPLayer p (closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G)) ≤
      GLAPLayer p (Y ⊓ Subgroup.centralizer (E : Set G)) := by
  obtain ⟨𝓛, h𝓛def⟩ : ∃ 𝓛 : Set (Subgroup G), 𝓛 = {X | ∃ b ∈ B, GLBConj b K₁ = X} :=
    ⟨_, rfl⟩
  have hmem : ∀ X, X ∈ 𝓛 ↔ ∃ b ∈ B, GLBConj b K₁ = X := fun X => by
    rw [h𝓛def, Set.mem_setOf_eq]
  have h𝓛C : ∀ X ∈ 𝓛, GLAPComponent p Y X := by
    intro X hX
    obtain ⟨b, hb, rfl⟩ := (hmem X).1 hX
    have := glaPComponent_gLBConj hK₁ b
    rwa [mem_normalizer_iff_gLBConj_eq.1 (hBY hb)] at this
  have hsup : sSup 𝓛 = closureIn K₁ B := by
    apply le_antisymm
    · refine sSup_le fun X hX => ?_
      obtain ⟨b, hb, rfl⟩ := (hmem _).1 hX
      rw [closureIn_eq_iSup_gLBConj K₁ B]
      exact le_biSup (fun g => GLBConj g K₁) hb
    · rw [closureIn_eq_iSup_gLBConj K₁ B]
      refine iSup₂_le fun b hb => ?_
      exact le_sSup ((hmem _).2 ⟨b, hb, rfl⟩)
  have hKsn : IsSubnormal (closureIn K₁ B) Y := by
    rw [← hsup]
    exact isSubnormal_sSup_glaPComponent hp 𝓛 h𝓛C
  exact glaPLayer_le_of_isSubnormal hp (hKsn.inf _)

theorem S_le_delta {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Open.IsKProper G) (hbal : LBalanceAt G p)
    (h145 : I145UsedAt G p) {B E D K₁ J R : Subgroup G} {b : G} (hB : IsElemAbelian p B)
    (hEB : E ≤ B) (hDE : D ≤ E) (hb : b ∈ B) (hb1 : b ≠ 1)
    (hK₁ : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) K₁)
    (hJ : J ≤ GLAPLayer p (closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G)))
    (hR : R ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))) :
    (⁅R ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) ≤ GLADelta p D := by
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB
  set Cb : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCb
  set D' : Subgroup G := D ⊔ Subgroup.zpowers b with hD'
  set P : Subgroup G := E ⊔ Subgroup.zpowers b with hP
  have hzB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.2 hb
  have hD'B : D' ≤ B := sup_le (hDE.trans hEB) hzB
  have hPB : P ≤ B := sup_le hEB hzB
  have hD'P : D' ≤ P := sup_le_sup_right hDE _
  have hPp : IsPGroup p P := hBp.to_le hPB
  have hD'p : IsPGroup p D' := hBp.to_le hD'B
  have hBC : ∀ H : Subgroup G, H ≤ B → B ≤ Subgroup.centralizer (H : Set G) := by
    intro H hH g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact isElemAbelian_commute hB (hH hh) hg
  have hD'Cb : Subgroup.centralizer (D' : Set G) ≤ Cb := Subgroup.centralizer_le (by
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hCbne : Cb ≠ ⊤ := centralizer_ne_top_of_ne_one hsimple hnonab hb1
  have hD'ne : Subgroup.centralizer (D' : Set G) ≠ ⊤ := fun h =>
    hCbne (top_le_iff.1 (h ▸ hD'Cb))
  have hKC : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (D' : Set G)) := hK.isKGroup _ hD'ne
  have hBnCb : B ≤ Subgroup.normalizer (Cb : Set G) :=
    (isElemAbelian_le_centralizer hB hb).trans Subgroup.le_normalizer
  have hJL : J ≤ GLAPLayer p (Cb ⊓ Subgroup.centralizer (E : Set G)) :=
    hJ.trans (layer_inf_centralizer_le hp hK₁ hBnCb)
  have hCP : Subgroup.centralizer (D' : Set G) ⊓ Subgroup.centralizer (P : Set G) =
      Cb ⊓ Subgroup.centralizer (E : Set G) := by
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hD'Cb h1, Subgroup.centralizer_le (le_sup_left : E ≤ P) h2⟩
    · rintro ⟨h1, h2⟩
      have hgb : b ∈ Subgroup.centralizer ({g} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 h1).symm
      have hPg : P ≤ Subgroup.centralizer ({g} : Set G) := by
        refine sup_le (fun e he => ?_) (Subgroup.zpowers_le.2 hgb)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 h2) e he
      have hgP : g ∈ Subgroup.centralizer (P : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact Subgroup.mem_centralizer_singleton_iff.1 (hPg hh)
      exact ⟨Subgroup.centralizer_le hD'P hgP, hgP⟩
  have hPle : P ≤ Subgroup.centralizer (D' : Set G) := hPB.trans (hBC D' hD'B)
  have hJD' : J ≤ GLAPLayer p (Subgroup.centralizer (D' : Set G)) := by
    have h1 := hbal (Subgroup.centralizer (D' : Set G)) P hKC hPle hPp
    rw [hCP] at h1
    exact hJL.trans h1
  have hRD : R ⊓ Subgroup.centralizer (D : Set G) ≤ GLAPPrimeCoreOf p (Subgroup.centralizer (D' : Set G)) := by
    intro g hg
    have hgR : g ∈ GLAPPrimeCoreOf p Cb := hR hg.1
    have hgCb : g ∈ Cb := Subgroup.map_subtype_le _ hgR
    have hgb : b ∈ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hgCb).symm
    have hD'g : D' ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (fun d hd => ?_) (Subgroup.zpowers_le.2 hgb)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hg.2) d hd
    have hgD' : g ∈ Subgroup.centralizer (D' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.1 (hD'g hh)
    have h1 : g ∈ GLAPPrimeCoreOf p (Cb ⊓ Subgroup.centralizer (D' : Set G)) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp Cb _ ⟨hgR, hgD'⟩
    rwa [inf_eq_right.2 hD'Cb] at h1
  refine le_iInf fun a => le_iInf fun haD => le_iInf fun ha1 => ?_
  have hCa : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    hK.isKGroup _ (centralizer_ne_top_of_ne_one hsimple hnonab ha1)
  have haD' : a ∈ D' := Subgroup.mem_sup_left haD
  have hD'Ca : D' ≤ Subgroup.centralizer ({a} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hB (hD'B hg) (hD'B haD')
  have hC'a : Subgroup.centralizer (D' : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (by
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact haD')
  have key := h145 hp hp2 (Subgroup.centralizer ({a} : Set G)) D' hCa hD'Ca hD'p
  rw [inf_eq_right.2 hC'a] at key
  calc (⁅R ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G)
      = ⁅J, R ⊓ Subgroup.centralizer (D : Set G)⁆ := Subgroup.commutator_comm _ _
    _ ≤ ⁅GLAPLayer p (Subgroup.centralizer (D' : Set G)),
          GLAPPrimeCoreOf p (Subgroup.centralizer (D' : Set G))⁆ :=
        Subgroup.commutator_mono hJD' hRD
    _ ≤ _ := key

theorem lemma413 {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) (hbal : LBalanceAt G p)
    (h1810 : I1810UsedAt G p) (h145 : I145UsedAt G p) : Lemma413At G p := by
  intro B b K₁ hB hb hb1 hK₁ hGS
  have hpp : p.Prime := hp.1.1
  have hp2 : p ≠ 2 := hp.1.2.1
  have hΔ : GLADeltaZero G p := hp.2.2
  have hBel : IsElemAbelian p B := hB.1
  by_contra hodd
  set Y : Subgroup G := Subgroup.centralizer ({b} : Set G) with hY
  set K : Subgroup G := closureIn K₁ B with hKdef
  set Ob : Subgroup G := GLAPPrimeCoreOf p Y with hOb
  have hX2 : Even (Nat.card (⁅K, Ob⁆ : Subgroup G)) := Nat.not_odd_iff_even.1 hodd
  have hBY : B ≤ Y := isElemAbelian_le_centralizer hBel hb
  have hBnY : B ≤ Subgroup.normalizer (Y : Set G) := hBY.trans (Subgroup.le_normalizer)
  obtain ⟨hKY, hBK, hObK, hKL⟩ := layer_closureIn hpp hK₁ hBnY
  obtain ⟨hXK, hXle, hKX, hBnX, hXO, hcopX⟩ := commutator_oPrime_facts hpp hK₁ hBnY
  obtain ⟨R, hRX, hR2, hRidx, hBR⟩ := exists_invariant_sylow_two hpp hp2 (GLAIsBmax.isPGroup hB) hBnX hcopX
  have hR1 : R ≠ ⊥ := ne_bot_of_even hRidx hX2
  have hsimple := hctx.1.simple
  have hnonab := hctx.1.nonabelian
  have hkp := hctx.1.kProper
  have hYne : Y ≠ ⊤ := centralizer_ne_top_of_ne_one hsimple hnonab hb1
  have hYK : CFSG.Open.IsKGroup ↥Y := hkp.isKGroup Y hYne
  have hEvenOb : Even (Nat.card Ob) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 hX2).trans (Subgroup.card_dvd_of_le hXle))
  have hCz : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) = Y := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hSC : IsSC p B := by
    refine i326UsedAt_holds p hpp hp2 B (Subgroup.zpowers b) hB (Subgroup.zpowers_le.2 hb)
      (mt Subgroup.zpowers_eq_bot.1 hb1) ?_
    rw [hCz]
    exact hEvenOb
  have hC : K ⊓ Subgroup.centralizer (R : Set G) ≤ oPPrimeP p K :=
    h1810 hpp hp2 Y K₁ B R hYK hK₁ (GLAIsBmax.isPGroup hB) hBnY hR1 hR2 hRX hRidx hBR
  unfold IsGStar at hGS
  obtain ⟨E, hEB, hEel, hEc, hZ⟩ := hGS
  obtain ⟨J, hJK, hJR, hJE, hBJ, hJ1, hJL, hJZ, -⟩ :=
    exists_J_data hpp hp2 hKL hBK hBel hEB hXK hKX hXO hR2 hRX hRidx hBR hZ
  have hnc : ¬ J ≤ Subgroup.centralizer (R : Set G) := J_not_le_centralizer hpp hJK hJL hJ1 hC
  obtain ⟨D, hDE, hDel, hDc, hS⟩ :=
    exists_D_commutator hpp hp2 hEel hEc (hEB.trans hBR) hR2 hJR hJE hnc
  set C₀ : Subgroup G := R ⊓ Subgroup.centralizer (D : Set G) with hC₀
  have hJCD : J ≤ Subgroup.centralizer (D : Set G) :=
    hJE.trans (Subgroup.centralizer_le hDE)
  have hJNC : J ≤ Subgroup.normalizer (C₀ : Set G) :=
    le_normalizer_inf hJR (hJCD.trans Subgroup.le_normalizer)
  have hBCD : B ≤ Subgroup.centralizer (D : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact isElemAbelian_commute hBel (hEB (hDE hd)) hg
  have hBNC : B ≤ Subgroup.normalizer (C₀ : Set G) :=
    le_normalizer_inf hBR (hBCD.trans Subgroup.le_normalizer)
  have hC2 : IsPGroup 2 C₀ := hR2.to_le inf_le_left
  have hCΔ : (⁅C₀, J⁆ : Subgroup G) ≤ GLADelta p D :=
    S_le_delta hpp hp2 hsimple hnonab hkp hbal h145 hBel hEB hDE hb hb1 hK₁ hJZ
      (hRX.trans hXle)
  have h0 : (⁅C₀, J⁆ : Subgroup G) = ⊥ :=
    layer_commutator_eq_bot hpp hp2 hΔ hB hSC (hDE.trans hEB) hDel hDc hBJ hJL hC2 hBNC hJNC hCΔ
  exact hS h0

end CFSG.LocalAnalysis.GLTheoremA
