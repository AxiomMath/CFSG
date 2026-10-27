module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Used

theorem factU_of_factUQ (hQ : QFactU) : FactU := by
  intro p A _ _ S B T x b cfg
  classical
  have hp := cfg.prime
  have hp2 := cfg.odd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hSn : S.Normal := cfg.normal
  haveI hNn : (GLAPPrimeCoreOf p S).Normal := normal_glaPPrimeCoreOf hSn
  set N : Subgroup A := GLAPPrimeCoreOf p S with hNdef
  have hNp : ¬ p ∣ Nat.card N := not_dvd_card_glaPPrimeCoreOf hp S
  set π : A →* A ⧸ N := QuotientGroup.mk' N with hπ
  have hkerπ : π.ker = N := by rw [hπ, QuotientGroup.ker_mk']
  have hker : ¬ p ∣ Nat.card π.ker := by rw [hkerπ]; exact hNp
  have hNS : N ≤ S := Subgroup.map_subtype_le _
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian cfg.elem
  have hSN : ∀ g : A, g ∈ Subgroup.normalizer (S : Set A) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]; exact Subgroup.mem_top g
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hbN : b ∈ Subgroup.normalizer (S : Set A) := hSN b
  obtain ⟨e, he⟩ : ∃ e : PQuot p S ≃* PQuot p (S.map π), ∀ (g : A), g ∈ Subgroup.normalizer (S : Set A) →
      ∀ q q' : PQuot p S, indRel p (S.map π) (π g) (e q) (e q') ↔ indRel p S g q q' :=
    ⟨T156.pquotMap hp π hker S, fun g hg q q' => T156.indRel_pquotMap hp π hker hg q q'⟩
  obtain ⟨e₃⟩ := nonempty_pQuot_equiv_map_self (p := p) (ψ := π) (K := S)
    (by rw [hkerπ, inf_eq_left.2 hNS])
  have hq0 : CFSG.Open.IsQuasisimple (PQuot p S) := isQuasisimple_pQuot_of_glaPComponent hp cfg.comp
  have hSp : GLAPPrimeCore p ↥(S.map π) = ⊥ := by
    have h1 : (GLAPPrimeCoreOf p S).map π = GLAPPrimeCoreOf p (S.map π) :=
      S267.map_glaPPrimeCoreOf hp π hker S
    have h2 : (GLAPPrimeCoreOf p S).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hkerπ]
    have h3 : GLAPPrimeCoreOf p (S.map π) = ⊥ := by rw [← h1, h2]
    exact (Subgroup.map_eq_bot_iff_of_injective _ (S.map π).subtype_injective).1 h3
  have hcomp₂ : GLAPComponent p (⊤ : Subgroup (A ⧸ N)) (S.map π) := by
    have h := glaPComponent_map hp π (S267.coprime_inf_ker hp π hker ⊤) cfg.comp
    rwa [Subgroup.map_top_of_surjective π hπs] at h
  have hrank₂ : p ^ GLATwoLocalRank p (A ⧸ N) ≤ Nat.card (B.map π) := by
    refine (Nat.pow_le_pow_right hp.pos (twoLocalRank_quot_le hp hp2 N hNp)).trans ?_
    rw [S267.card_map_of_isPGroup hp π hker hBp]
    exact cfg.rank
  have hcm : ∀ c₂ ∈ B.map π, CentMod p (S.map π) c₂ ↔ c₂ ∈ Subgroup.zpowers (π x) := by
    intro c₂ hc₂
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hc₂
    rw [centMod_iff, ← S267.mem_centModSubgroup_map_iff hp π hker (hSN c), ← centMod_iff, cfg.centB c hc]
    have := T156.mem_map_iff_of_injOn hp π hker hBp (T := Subgroup.zpowers x)
      (Subgroup.zpowers_le.2 cfg.xB) hc
    rw [MonoidHom.map_zpowers] at this
    exact this.symm
  have hR₂ : R2Prop p (π b) (S.map π) := by
    rcases cfg.prop with hF | ⟨hp3, hT3, hNI⟩
    · exact Or.inl (T156.fieldOn_to_Omega e (T156.map_normalizer_mem π hbN)
        (fun q q' => (he b hbN q q').symm) hF)
    · subst hp3
      exact Or.inr ⟨rfl, (T156.isTD4_congr rfl e).1 hT3, T156.map_normalizer_mem π hbN,
        fun hI => hNI.2 (T156.inducesInnerMod_of_map hp π hker hbN hI)⟩
  have hg2 : p = 3 → IsTD4 3 (S.map π) → centCard2 3 (S.map π) (π b) = Nat.sqrt (card2 3 (S.map π)) := by
    intro h3 hT'
    have hT3 : IsTD4 3 S := (T156.isTD4_congr h3 e).2 hT'
    have key := cfg.g2 h3 hT3
    subst h3
    rw [centCard2_map hp π hker hbN, card2_map hp π hker]
    exact key
  have hip : Ipart p (S.map π) (π b) ≠ ⊥ := by
    have hE : IsPGroup p (Subgroup.zpowers b) := hBp.to_le (Subgroup.zpowers_le.2 cfg.hb)
    have hEM : Subgroup.zpowers b ≤ Subgroup.normalizer (S : Set A) := fun g _ => hSN g
    have hY := T156.map_centralizer_omega (M := S) π hker hp hE hEM
    have h := (S267.glaPLayer_map_ne_bot_iff hp π hker (S ⊓ Subgroup.centralizer ({b} : Set A))).2 cfg.ipart
    rw [hY] at h
    exact h
  have hnn : ¬ InnDiagOn p (B.map π) (S.map π) := by
    intro h
    refine cfg.noninn (T156.innDiagOn_of_Omega e (fun a ha => hSN a) (fun a ha => ?_) h)
    exact ⟨π a, Subgroup.mem_map_of_mem π ha, fun q q' => (he a (hSN a) q q').symm⟩
  have hgs : ∃ E : Subgroup (A ⧸ N), E ≤ B.map π ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      GLAPLayer p (S.map π ⊓ Subgroup.centralizer (E : Set (A ⧸ N))) ≠ ⊥ := by
    obtain ⟨E, hEB, hEel, hEcard, hElay⟩ := cfg.gstar
    have hEp : IsPGroup p E := isPGroup_of_isElemAbelian hEel
    refine ⟨E.map π, Subgroup.map_mono hEB, CFSG.Open.IsElemAbelian.map hEel π, ?_, ?_⟩
    · rw [S267.card_map_of_isPGroup hp π hker hEp, hEcard]
    · have h := (S267.glaPLayer_map_ne_bot_iff hp π hker (S ⊓ Subgroup.centralizer (E : Set A))).2 hElay
      rwa [S267.map_inf_centralizer hp π hker hEp (fun g _ => hSN g)] at h
  have hcfg : QUCfg p (S.map π) (B.map π) (T.map π) (π x) (π b) :=
    { prime := hp
      odd := hp2
      kgroup := cfg.kgroup.quotient N
      comp := hcomp₂
      normal := hSn.map π hπs
      quasi := hq0.of_mulEquiv e₃.symm
      core := hSp
      chev := T156.isChevSimple_congr (T156.psimpleIso e) cfg.chev
      gen := by
        rw [← Subgroup.map_sup, ← Subgroup.map_sup, cfg.gen, Subgroup.map_top_of_surjective π hπs]
      elem := CFSG.Open.IsElemAbelian.map cfg.elem π
      two := cfg.two.map π
      bnorm := (Subgroup.map_mono cfg.bnorm).trans (Subgroup.le_normalizer_map π)
      maxc := (maxc_of_cases hp hp2 hNp cfg.elem cfg.rank cfg.two cfg.bnorm cfg.ne).imp_right And.right
      rank := hrank₂
      big := by rw [S267.card_map_of_isPGroup hp π hker hBp]; exact cfg.big
      cyc := cycModSylow_map hp hSn N rfl cfg.cyc
      xB := Subgroup.mem_map_of_mem π cfg.xB
      x1 := fun h => cfg.x1 (T156.injOn_of_pgroup hp π hker hBp cfg.xB B.one_mem (by rw [h, map_one]))
      xcen := fun g₂ => by
        obtain ⟨g, rfl⟩ := hπs g₂
        rw [← map_mul, ← map_mul, cfg.xcen g]
      centB := hcm
      hb := Subgroup.mem_map_of_mem π cfg.hb
      hbx := fun h => cfg.hbx (by
        have := (T156.mem_map_iff_of_injOn hp π hker hBp (T := Subgroup.zpowers x)
          (Subgroup.zpowers_le.2 cfg.xB) cfg.hb).1
        rw [MonoidHom.map_zpowers] at this
        exact this h)
      prop := hR₂
      g2 := hg2
      ipart := hip
      noninn := hnn
      gstar := hgs }
  rcases hQ p (A ⧸ N) (S.map π) (B.map π) (T.map π) (π x) (π b) hcfg with
    ⟨E₂, hE₂B, hE₂el, hE₂card, hDE, hE₂lay⟩ | ⟨hp3, hU, hFi⟩
  · left
    set E : Subgroup A := B ⊓ E₂.comap π with hE
    have hEB : E ≤ B := inf_le_left
    have hEel : IsElemAbelian p E := isElemAbelian_mono cfg.elem hEB
    have hEp : IsPGroup p E := isPGroup_of_isElemAbelian hEel
    have hEmap : E.map π = E₂ := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact hy.2
      · intro y hy
        obtain ⟨c, hc, rfl⟩ := hE₂B hy
        exact ⟨c, ⟨hc, hy⟩, rfl⟩
    refine ⟨E, hEB, hEel, ?_, ?_, ?_⟩
    · rw [← hE₂card, ← hEmap, S267.card_map_of_isPGroup hp π hker hEp]
    · refine (Subgroup.closure_le _).2 ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨cfg.hb, hDE (Subgroup.subset_closure (by simp))⟩
      · exact ⟨cfg.xB, hDE (Subgroup.subset_closure (by simp))⟩
    · refine (S267.glaPLayer_map_ne_bot_iff hp π hker (S ⊓ Subgroup.centralizer (E : Set A))).1 ?_
      rw [S267.map_inf_centralizer hp π hker hEp (fun g _ => hSN g), hEmap]
      exact hE₂lay
  · right
    subst hp3
    refine ⟨rfl, (T156.psimple3_congr rfl e _).2 hU, ?_⟩
    exact T156.fieldOn_to_Omega e.symm hbN (fun q q' => by
      have := he b hbN (e.symm q) (e.symm q')
      simpa using this) hFi

end Used

end CFSG.LocalAnalysis.GLTheoremA.S265

end
