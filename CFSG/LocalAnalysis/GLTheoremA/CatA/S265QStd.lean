module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Omega268
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Std

theorem factS_of_factSQ (hQ : QFactS) : FactS := by
  intro p A _ _ S B T x D K cfg
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
  have hq0 : CFSG.Open.IsQuasisimple (PQuot p S) := isQuasisimple_pQuot_of_glaPComponent hp cfg.comp
  have hZ : ∀ n ∈ N, ∀ s ∈ S, s * n = n * s := glaPPrimeCoreOf_central cfg.quasi hq0
  obtain ⟨e, he⟩ : ∃ e : PQuot p S ≃* PQuot p (S.map π), ∀ (g : A), g ∈ Subgroup.normalizer (S : Set A) →
      ∀ q q' : PQuot p S, indRel p (S.map π) (π g) (e q) (e q') ↔ indRel p S g q q' :=
    ⟨T156.pquotMap hp π hker S, fun g hg q q' => T156.indRel_pquotMap hp π hker hg q q'⟩
  obtain ⟨e₃⟩ := nonempty_pQuot_equiv_map_self (p := p) (ψ := π) (K := S)
    (by rw [hkerπ, inf_eq_left.2 hNS])
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
  obtain ⟨hDB, hDel, hDcard, hxD, hKlay, hKcomp, hDK⟩ := cfg.std
  have hDp : IsPGroup p D := hBp.to_le hDB
  have hDN : D ≤ Subgroup.normalizer (S : Set A) := fun g _ => hSN g
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hKY : K ≤ S ⊓ Subgroup.centralizer (D : Set A) := hKcomp.1
  have hKS : K ≤ S := hKY.trans inf_le_left
  have hBK : B ≤ Subgroup.normalizer (K : Set A) := S171.B_norm_K cfg.elem (fun g _ => hSN g) cfg.std
  have hYmap : (S ⊓ Subgroup.centralizer (D : Set A)).map π =
      S.map π ⊓ Subgroup.centralizer ((D.map π : Subgroup (A ⧸ N)) : Set (A ⧸ N)) :=
    S267.map_inf_centralizer hp π hker hDp hDN
  have hKnot : ¬ K ≤ π.ker := by
    intro hle
    rw [hkerπ] at hle
    exact not_le_of_isQuasisimple_central hKq (hle.trans le_rfl) (fun z hz k hk => hZ z hz k (hKS hk))
  have hcomp₂K : IsComponentOf (K.map π) (S.map π ⊓ Subgroup.centralizer ((D.map π : Subgroup (A ⧸ N)) : Set (A ⧸ N))) := by
    rw [← hYmap]
    exact S12.isComponentOf_map_of_not_le_ker π hKcomp hKnot
  have hstd : GLAStdSubPre p (B.map π) (π x) (S.map π) (D.map π) (K.map π) := by
    refine ⟨Subgroup.map_mono hDB, CFSG.Open.IsElemAbelian.map hDel π, ?_, Subgroup.mem_map_of_mem π hxD, ?_,
      hcomp₂K, ?_⟩
    · rw [S267.card_map_of_isPGroup hp π hker hDp, hDcard]
    · apply le_antisymm
      · exact I142N.le_GLALayer hcomp₂K
      · have h := glaLayer_map_le_central π (Y := S ⊓ Subgroup.centralizer (D : Set A))
          (fun n hn hn1 y hy => hZ n (by rw [← hkerπ]; exact MonoidHom.mem_ker.2 hn1) y hy.1)
        rw [hYmap, ← hKlay] at h
        exact h
    · apply le_antisymm
      · intro y hy
        have hyD : y ∈ D.map π := hy
        rw [hDK] at hyD
        obtain ⟨d, hd, rfl⟩ := hyD
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem π hd.1, Subgroup.mem_centralizer_iff.2 ?_⟩
        rintro _ ⟨k, hk, rfl⟩
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hd.2 k hk]
      · rintro _ ⟨hc₂, hc₂K⟩
        obtain ⟨c, hcB, rfl⟩ := Subgroup.mem_map.1 hc₂
        have hcD : c ∈ D := by
          refine S171.faithful_quot hBK hKq cfg.std hcB ?_
          rw [Subgroup.commutator_le]
          intro k hk y hy
          rw [Subgroup.mem_centralizer_iff]
          intro k' hk'
          have hyB : y ∈ B := (Subgroup.zpowers_le.2 hcB) hy
          have hπy : π y ∈ Subgroup.centralizer ((K.map π : Subgroup (A ⧸ N)) : Set (A ⧸ N)) := by
            obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
            rw [map_zpow]
            exact Subgroup.zpow_mem _ hc₂K m
          have hcommk : ⁅k, y⁆ ∈ N := by
            rw [← hkerπ, MonoidHom.mem_ker, map_commutatorElement,
              commutatorElement_eq_one_iff_mul_comm]
            exact Subgroup.mem_centralizer_iff.1 hπy (π k) (Subgroup.mem_map_of_mem π hk)
          exact hZ _ hcommk k' (hKS hk')
        exact Subgroup.mem_map_of_mem π hcD
  have hmaxc : (⁅T.map π, B.map π⁆ : Subgroup (A ⧸ N)) ≠ ⊥ ∨
      ((∀ E : Subgroup (A ⧸ N), IsElemAbelian p E → Nat.card E ≤ Nat.card (B.map π)) ∧
        B.map π ≠ (B.map π ⊓ S.map π) ⊔ (B.map π ⊓ centModSubgroup p (S.map π))) := by
    rcases maxc_of_cases hp hp2 hNp cfg.elem cfg.rank cfg.two cfg.bnorm cfg.ne with h | ⟨hle, hE⟩
    · exact Or.inl h
    · refine Or.inr ⟨hE, fun hsplit => ?_⟩
      have hcomm : ∀ h ∈ B.map π ⊓ S.map π, ∀ k ∈ B.map π ⊓ centModSubgroup p (S.map π), h * k = k * h :=
        fun h hh k hk => isElemAbelian_commute (CFSG.Open.IsElemAbelian.map cfg.elem π) hh.1 hk.1
      have hcc : ∀ c ∈ Subgroup.zpowers x, ∀ g : A, g * c = c * g := by
        intro c hc g
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
        exact (Commute.zpow_right (show Commute g x from cfg.xcen g) k).eq
      have hdec : ∀ b ∈ B, ∃ s ∈ S, ∃ c ∈ Subgroup.zpowers x, b = s * c := by
        intro b hb
        have hbmem : π b ∈ (B.map π ⊓ S.map π) ⊔ (B.map π ⊓ centModSubgroup p (S.map π)) := by
          rw [← hsplit]; exact Subgroup.mem_map_of_mem π hb
        obtain ⟨u, hu, v, hv, huv⟩ := S267.exists_mul_of_comm_sup hcomm hbmem
        obtain ⟨s, hsB, rfl⟩ := Subgroup.mem_map.1 hu.1
        obtain ⟨c, hcB, rfl⟩ := Subgroup.mem_map.1 hv.1
        obtain ⟨s', hs'S, hs'⟩ := Subgroup.mem_map.1 hu.2
        have hsS : s ∈ S := by
          have h1 : s'⁻¹ * s ∈ N := by
            rw [← hkerπ, MonoidHom.mem_ker, map_mul, map_inv, hs']
            exact inv_mul_cancel _
          have h2 : s = s' * (s'⁻¹ * s) := by group
          rw [h2]
          exact S.mul_mem hs'S (hNS h1)
        have hcx : c ∈ Subgroup.zpowers x := by
          refine (cfg.centB c hcB).1 (centMod_iff.2 ?_)
          exact (S267.mem_centModSubgroup_map_iff hp π hker (hSN c)).2 hv.2
        refine ⟨s, hsS, c, hcx, ?_⟩
        refine T156.injOn_of_pgroup hp π hker hBp hb (B.mul_mem hsB hcB) ?_
        rw [map_mul]
        exact huv
      have hNB : (⁅N, B⁆ : Subgroup A) = ⊥ := by
        refine le_bot_iff.1 ((Subgroup.commutator_le).2 fun n hn b hb => ?_)
        obtain ⟨s, hsS, c, hcx, rfl⟩ := hdec b hb
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        calc n * (s * c) = (n * s) * c := by group
          _ = (s * n) * c := by rw [hZ n hn s hsS]
          _ = s * (n * c) := by group
          _ = s * (c * n) := by rw [hcc c hcx n]
          _ = (s * c) * n := by group
      have h1 : (⁅⁅T, B⁆, B⁆ : Subgroup A) = ⁅T, B⁆ :=
        commutator_commutator_eq_of_isPGroup hp hBp cfg.two hp2 cfg.bnorm
      have h2 : (⁅⁅T, B⁆, B⁆ : Subgroup A) ≤ ⁅N, B⁆ := Subgroup.commutator_mono hle le_rfl
      apply cfg.ne
      rw [← h1]
      exact le_bot_iff.1 (h2.trans hNB.le)
  have hcfg : QSCfg p (S.map π) (B.map π) (T.map π) (π x) (D.map π) (K.map π) :=
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
      maxc := hmaxc
      rank := hrank₂
      big := by rw [S267.card_map_of_isPGroup hp π hker hBp]; exact cfg.big
      cyc := cycModSylow_map hp hSn N rfl cfg.cyc
      xB := Subgroup.mem_map_of_mem π cfg.xB
      x1 := fun h => cfg.x1 (T156.injOn_of_pgroup hp π hker hBp cfg.xB B.one_mem (by rw [h, map_one]))
      xcen := fun g₂ => by
        obtain ⟨g, rfl⟩ := hπs g₂
        rw [← map_mul, ← map_mul, cfg.xcen g]
      centB := hcm
      inn := T156.innDiagOn_to_Omega e (fun a ha => by
          obtain ⟨g, rfl⟩ := hπs a
          exact T156.map_normalizer_mem π (hSN g) |> fun h => h)
        (fun a' ha' => by
          obtain ⟨a, haB, rfl⟩ := Subgroup.mem_map.1 ha'
          exact ⟨a, haB, fun q q' => (he a (hSN a) q q').symm⟩) cfg.inn
      std := hstd }
  rcases hQ p (A ⧸ N) (S.map π) (B.map π) (T.map π) (π x) (D.map π) (K.map π) hcfg with
    ⟨E₂, ⟨hE₂B, hE₂el, hE₂card⟩, hDE, hE₂lay⟩ | ⟨hp3, hsm⟩
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
    refine ⟨E, ⟨hEB, hEel, ?_⟩, ?_, ?_⟩
    · rw [← hE₂card, ← hEmap, S267.card_map_of_isPGroup hp π hker hEp]
    · intro d hd
      exact ⟨hDB hd, hDE (Subgroup.mem_map_of_mem π hd)⟩
    · refine (S267.glaPLayer_map_ne_bot_iff hp π hker (S ⊓ Subgroup.centralizer (E : Set A))).1 ?_
      rw [S267.map_inf_centralizer hp π hker hEp (fun g _ => hSN g), hEmap]
      exact hE₂lay
  · right
    subst hp3
    refine ⟨rfl, ?_⟩
    have e₄ := T156.pquotMap hp π hker K
    rcases hsm with hU | hA
    · exact Or.inl ((T156.psimple3_congr rfl e₄ _).2 hU)
    · exact Or.inr ((T156.psimple3_congr rfl e₄ _).2 hA)

end Std

end CFSG.LocalAnalysis.GLTheoremA.S265

end
