module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1115
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1114
public import CFSG.LocalAnalysis.GL83PartI.I_22_5
public import CFSG.HardMathSupport.Dickson.Sec6.Residuals
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1112b
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.InnDiagRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.InnDiag
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

section Unique

variable {G : Type} [Group G] [Finite G] {M E A K : Subgroup G} {a : G}

theorem isSimpleGroup_barX_K (c : Inputs1114.Cfg M E A K a) :
    IsSimpleGroup ↥(barX 3 (Cg a) K) := by
  have hiso : barOf 3 K ≃* ↥(barX 3 (Cg a) K) := quotEquivBarX Nat.prime_three c.hK.1 c.hK.2.1
  haveI := (CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour c.hL).1
  exact MulEquiv.isSimpleGroup hiso.symm

theorem card_barX_K (c : Inputs1114.Cfg M E A K a) : Nat.card ↥(barX 3 (Cg a) K) = 20160 := by
  rw [← Nat.card_congr (quotEquivBarX Nat.prime_three c.hK.1 c.hK.2.1).toEquiv]
  exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour c.hL

theorem eq_bot_of_le_barX_K (c : Inputs1114.Cfg M E A K a)
    {N : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a))} (hNK : N ≤ barX 3 (Cg a) K)
    (hKN : barX 3 (Cg a) K ≤ Subgroup.normalizer (N : Set _)) (hN : Nat.Coprime 3 (Nat.card N)) :
    N = ⊥ := by
  haveI := isSimpleGroup_barX_K c
  haveI : (N.subgroupOf (barX 3 (Cg a) K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (barX 3 (Cg a) K)) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    rw [← inf_eq_left.2 hNK]
    exact disjoint_iff.1 h
  · exfalso
    have hle : barX 3 (Cg a) K ≤ N := (Subgroup.subgroupOf_eq_top.1 h)
    have hdvd : Nat.card ↥(barX 3 (Cg a) K) ∣ Nat.card N := Subgroup.card_dvd_of_le hle
    rw [card_barX_K c] at hdvd
    have h3 : 3 ∣ Nat.card N := (by norm_num : 3 ∣ 20160).trans hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hN h3

theorem coprime_card_barX {X U : Subgroup G} (hUX : U ≤ X) (hU : Nat.Coprime 3 (Nat.card U)) :
    Nat.Coprime 3 (Nat.card (barX 3 X U)) := by
  have h1 : Nat.card (barX 3 X U) ∣ Nat.card (U.subgroupOf X) := Subgroup.card_map_dvd _ _
  have h2 : Nat.card (U.subgroupOf X) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv
  exact Nat.Coprime.coprime_dvd_right (h2 ▸ h1) hU

theorem eq_of_glaPComponent_inf (c : Inputs1114.Cfg M E A K a) {H K' K'' : Subgroup G}
    (hK' : GLAPComponent 3 (H ⊓ Cg a) K') (hbar : barX 3 (Cg a) K' = barX 3 (Cg a) K)
    (hKK' : ∀ k ∈ K, ∃ k' ∈ K', k'⁻¹ * k ∈ GLAPPrimeCoreOf 3 (Cg a))
    (hK'' : GLAPComponent 3 (H ⊓ Cg a) K'') : K'' = K' := by
  by_contra hne
  set Y := H ⊓ Cg a with hY
  set O := GLAPPrimeCoreOf 3 (Cg a) with hO
  have hYC : Y ≤ Cg a := inf_le_right
  set U := GLAPPrimeCoreOf 3 Y with hU
  have hUY : U ≤ Y := Subgroup.map_subtype_le _
  have hUC : U ≤ Cg a := hUY.trans hYC
  have hcomm : ⁅K'', K'⁆ ≤ U :=
    CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne Nat.prime_three
      hK'' hK' hne
  have hK'NU : K' ≤ Subgroup.normalizer (U : Set G) :=
    hK'.1.trans (le_normalizer_glaPPrimeCoreOf 3 Y)
  have hKNU : barX 3 (Cg a) K ≤ Subgroup.normalizer (barX 3 (Cg a) U : Set _) := by
    rw [← hbar]
    exact barX_le_normalizer hK'NU
  have hUK : barX 3 (Cg a) U ⊓ barX 3 (Cg a) K = ⊥ := by
    refine eq_bot_of_le_barX_K c inf_le_right ?_ ?_
    · intro x hx
      exact Inputs1115.mem_normalizer_inf (hKNU hx) (Subgroup.le_normalizer hx)
    · refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) ?_
      exact coprime_card_barX hUC
        (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 Y)
  have hcent : K'' ≤ centBar 3 (Cg a) K := by
    intro x hx
    have hxC : x ∈ Cg a := (hK''.1.trans hYC) hx
    have hxN : x ∈ Subgroup.normalizer (K : Set G) := c.cg_le_normalizer hxC
    refine Inputs1114.mem_centBar_iff_forall.2 ⟨hxC, hxN, fun k hk => ?_⟩
    have hkC : k ∈ Cg a := c.hK.1 hk
    obtain ⟨k', hk', hkk'⟩ := hKK' k hk
    have hk'C : k' ∈ Cg a := (hK'.1.trans hYC) hk'
    set u := x * k * x⁻¹ * k⁻¹ with hu
    set v := x * k' * x⁻¹ * k'⁻¹ with hv
    have huK : u ∈ K := K.mul_mem ((Subgroup.mem_normalizer_iff.1 hxN k).1 hk) (K.inv_mem hk)
    have huC : u ∈ Cg a := c.hK.1 huK
    have hvU : v ∈ U := hcomm (Subgroup.commutator_mem_commutator hx hk')
    have hvC : v ∈ Cg a := hUC hvU
    have huv : u⁻¹ * v ∈ O := by
      set o := k'⁻¹ * k with ho
      have hoO : o ∈ O := hkk'
      have hON : ∀ g ∈ Cg a, ∀ y ∈ O, g * y * g⁻¹ ∈ O := fun g hg y hy =>
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 (Cg a) hg) y).1 hy
      have e : u⁻¹ * v = k' * (o * (x * o⁻¹ * x⁻¹)) * k'⁻¹ := by
        have hk : k = k' * o := by rw [ho]; group
        rw [hu, hv, hk]; group
      rw [e]
      exact hON k' hk'C _ (O.mul_mem hoO (hON x hxC _ (O.inv_mem hoO)))
    have hmk : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨u, huC⟩ ∈
        barX 3 (Cg a) U ⊓ barX 3 (Cg a) K := by
      refine ⟨?_, Inputs1115.mk_mem_barX huC huK⟩
      rw [Inputs1115.mk_eq_mk huC hvC huv]
      exact Inputs1115.mk_mem_barX hvC hvU
    rw [hUK, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmk
    have huO : u ∈ O := ⟨_, hmk, rfl⟩
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three c.hK.2.1]
    exact ⟨huK, huO⟩
  have hK''O : K'' ≤ O :=
    Inputs1114.perfect_le_core_of_le_sup (glaPComponent_perfect hK'') (hcent.trans c.centBar_le)
  apply CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.A2_barX_ne_bot hK''
  rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_eq_bot_iff hK''.1]
  intro x hx
  have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le Nat.prime_three
    (Cg a) H
  rw [inf_comm (Cg a) H] at h1
  exact h1 ⟨hK''O hx, (hK''.1 hx).1⟩

theorem isLThreeFour_barOf_K' (c : Inputs1114.Cfg M E A K a) {H K' : Subgroup G}
    (hK' : GLAPComponent 3 (H ⊓ Cg a) K') (hbar : barX 3 (Cg a) K' = barX 3 (Cg a) K) :
    IsLThreeFour (barOf 3 K') := by
  have hK'C : K' ≤ Cg a := hK'.1.trans inf_le_right
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) with hπ
  set ψ : ↥K' →* (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)) := π.comp (Subgroup.inclusion hK'C) with hψ
  have hrange : ψ.range = barX 3 (Cg a) K := by
    rw [← hbar]
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hK'C y, Subgroup.mem_subgroupOf.2 y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  set W : Subgroup G := GLAPPrimeCoreOf 3 K' with hW
  have hWK' : W ≤ K' := Subgroup.map_subtype_le _
  have hWbar : barX 3 (Cg a) W = ⊥ := by
    refine eq_bot_of_le_barX_K c ?_ ?_ ?_
    · rw [← hbar]
      exact Inputs1115.barX_le_barX hWK'
    · rw [← hbar]
      exact barX_le_normalizer (le_normalizer_glaPPrimeCoreOf 3 K')
    · exact coprime_card_barX (hWK'.trans hK'C)
        (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 K')
  have hker : ψ.ker = GLAPPrimeCore 3 ↥K' := by
    ext y
    rw [MonoidHom.mem_ker]
    constructor
    · intro hy
      have hyO : (y : G) ∈ GLAPPrimeCoreOf 3 (Cg a) := by
        have : π (Subgroup.inclusion hK'C y) = 1 := hy
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
        exact ⟨_, this, rfl⟩
      have hle : K' ⊓ GLAPPrimeCoreOf 3 (Cg a) ≤ GLAPPrimeCoreOf 3 K' := by
        refine Inputs1115.le_glaPPrimeCoreOf_of_le_normalizer inf_le_left ?_ ?_
        · intro g hg
          exact Inputs1115.mem_normalizer_inf (Subgroup.le_normalizer hg)
            (le_normalizer_glaPPrimeCoreOf 3 (Cg a) (hK'C hg))
        · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
            (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3
              (Cg a))
      obtain ⟨z, hz, hzy⟩ := hle ⟨y.2, hyO⟩
      have : z = y := Subtype.ext hzy
      rw [← this]
      exact hz
    · intro hy
      have hyW : (y : G) ∈ W := ⟨y, hy, rfl⟩
      have h1 : π (Subgroup.inclusion hK'C y) ∈ barX 3 (Cg a) W :=
        Inputs1115.mk_mem_barX (hK'C y.2) hyW
      rw [hWbar, Subgroup.mem_bot] at h1
      exact h1
  have e1 : barOf 3 K' ≃* ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  have e2 : barOf 3 K' ≃* barOf 3 K :=
    (e1.trans (MulEquiv.subgroupCongr hrange)).trans
      (quotEquivBarX Nat.prime_three c.hK.1 c.hK.2.1).symm
  obtain ⟨F, hF, hFf, hc, ⟨f⟩⟩ := c.hL
  exact ⟨F, hF, hFf, hc, ⟨e2.trans f⟩⟩

end Unique

section Situation

variable {G : Type} [Group G] [Finite G]

structure Sit (M E A K H : Subgroup G) (a : G) (K' : Subgroup G) : Prop where
  cfg : Inputs1114.Cfg M E A K a
  hH : InHFamily A K a H
  hK' : GLAPComponent 3 (H ⊓ Cg a) K'
  hbar : barX 3 (Cg a) K' = barX 3 (Cg a) K
  hKK' : ∀ k ∈ K, ∃ k' ∈ K', k'⁻¹ * k ∈ GLAPPrimeCoreOf 3 (Cg a)
  hK'L : K' ≤ GLAPLayer 3 H
  hrank : CFSG.Open.pRank 3 (Cg a) = 3
  hKH : CFSG.Open.IsKGroup ↥H

theorem exists_sit (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h1111 : Lemma1111Statement) (h119 : Lemma119Statement) (h1112 : Lemma1112Statement)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 3 B M E A a K)
    {H : Subgroup G} (hH : InHFamily A K a H) : ∃ K' : Subgroup G, Sit M E A K H a K' := by
  have c := Inputs1114.cfg_of h1111 h119 h1112 h
  obtain ⟨K', hK', hbar, hKK'⟩ := Inputs1115.exists_cover_K h hH
  have hsec : Sec11 G m 3 B M E A := h.toCex117Base.toSec11
  have hHtop : H ≠ ⊤ := Inputs1115.twoLocal_ne_top hsec.standing hH.1
  have hKH : CFSG.Open.IsKGroup ↥H := isKGroup_of_isKProper hsec.standing.kProper hHtop
  have haH : a ∈ H := hH.2.1 c.ha
  have hAp : IsPGroup 3 ↥A := CFSG.Open.IsElemAbelian.isPGroup c.hAel
  have hK'L : K' ≤ GLAPLayer 3 H :=
    (le_sSup hK' : K' ≤ GLAPLayer 3 (H ⊓ Cg a)).trans
      (Inputs1115.layer_cg_le_layer hS hKH haH (hAp.to_le (Subgroup.zpowers_le.2 c.ha)))
  exact ⟨K', c, hH, hK', hbar, hKK', hK'L, (h1112 h).1.2, hKH⟩

variable {M E A K H : Subgroup G} {a : G} {K' : Subgroup G}

theorem Sit.haH (S : Sit M E A K H a K') : a ∈ H := S.hH.2.1 S.cfg.ha

theorem Sit.hAH (S : Sit M E A K H a K') : A ≤ H := S.hH.2.1

theorem Sit.ha3 (S : Sit M E A K H a K') : a ^ 3 = 1 := S.cfg.ha3

theorem Sit.unique (S : Sit M E A K H a K') {K'' : Subgroup G}
    (hK'' : GLAPComponent 3 (H ⊓ Cg a) K'') : K'' = K' :=
  eq_of_glaPComponent_inf S.cfg S.hK' S.hbar S.hKK' hK''

theorem Sit.layer_eq (S : Sit M E A K H a K') : GLAPLayer 3 (H ⊓ Cg a) = K' :=
  le_antisymm (sSup_le fun _ hL => (S.unique hL).le) (le_sSup S.hK')

theorem Sit.jLayer_eq (S : Sit M E A K H a K') :
    Lemma1115.jLayer a H = ⨆ g ∈ GLAPLayer 3 H, GLBConj g K' := by
  unfold Lemma1115.jLayer
  rw [S.layer_eq]

theorem Sit.K'_le_jLayer (S : Sit M E A K H a K') : K' ≤ Lemma1115.jLayer a H := by
  have := Inputs1115.layer_le_jLayer (a := a) H
  rwa [S.layer_eq] at this

theorem centralizer_zpowers_eq (a : G) :
    Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) = Cg a := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem Sit.A0_le (S : Sit M E A K H a K') : E ⊓ A ≤ K' := by
  have hAp : IsPGroup 3 ↥A := CFSG.Open.IsElemAbelian.isPGroup S.cfg.hAel
  have hA0p : IsPGroup 3 ↥(E ⊓ A : Subgroup G) := hAp.to_le inf_le_right
  refine Inputs1115.le_of_isPGroup_le_sup (O := GLAPPrimeCoreOf 3 (Cg a) ⊓ H) ?_ ?_ hA0p ?_
  · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 (Cg a))
  · rw [← S.layer_eq]
    refine CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPLayer 3 ?_
    intro x hx
    exact Subgroup.le_normalizer ⟨hx.2,
      CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.gLAPPrimeCoreOf_le 3 (Cg a) hx.1⟩
  · intro x hx
    obtain ⟨k', hk', hkk⟩ := S.hKK' x (S.cfg.hA0K hx)
    have hk'H : k' ∈ H := (S.hK'.1.trans inf_le_left) hk'
    have hxH : x ∈ H := S.hAH hx.2
    have e : x = k' * (k'⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk')
      (Subgroup.mem_sup_right ⟨hkk, H.mul_mem (H.inv_mem hk'H) hxH⟩)

theorem Sit.cases (S : Sit M E A K H a K') :
    (∃ L : Subgroup G, GLAPComponent 3 H L ∧ GLBConj a L = L ∧ Lemma1115.jLayer a H = L) ∨
    (∃ L : Subgroup G, CFSG.HardMathSupport.Solomon.Coordinator.I183vCyc H a L ∧
      Lemma1115.jLayer a H = L ⊔ GLBConj a L ⊔ GLBConj a (GLBConj a L)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hEX : Subgroup.zpowers a ≤ H := Subgroup.zpowers_le.2 S.haH
  have hEp : IsPGroup 3 ↥(Subgroup.zpowers a) :=
    (CFSG.Open.IsElemAbelian.isPGroup S.cfg.hAel).to_le (Subgroup.zpowers_le.2 S.cfg.ha)
  have hJ'' : GLAPComponent 3 (H ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) :
      Set G)) K' := by
    rw [centralizer_zpowers_eq]
    exact S.hK'
  have hCeq := CFSG.HardMathSupport.Solomon.Coordinator.i183_iSup_family_eq hp hJ'' S.hK'L
  rw [← S.jLayer_eq] at hCeq
  have hJE : K' ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
    hJ''.1.trans inf_le_right
  have hstab : ∀ L ∈ CFSG.HardMathSupport.Solomon.Coordinator.i183Family 3 H K', GLBConj a L ∈
      CFSG.HardMathSupport.Solomon.Coordinator.i183Family 3 H K' := fun L hL =>
    CFSG.HardMathSupport.Solomon.Coordinator.i183_gLBConj_mem_family hEX hJE hL
      (Subgroup.mem_zpowers a)
  have htrans := fun L₁ L₂ h₁ h₂ =>
    CFSG.HardMathSupport.Solomon.Coordinator.i183_transitive hp hEX hEp hJ'' S.hK'L
      (L₁ := L₁) (L₂ := L₂) h₁ h₂
  obtain ⟨L, hL⟩ : ∃ L, L ∈ CFSG.HardMathSupport.Solomon.Coordinator.i183Family 3 H K' := by
    by_contra hne
    push Not at hne
    have h0 : (⨆ L ∈ CFSG.HardMathSupport.Solomon.Coordinator.i183Family 3 H K', L) = ⊥ :=
      le_bot_iff.1 (iSup₂_le fun L hL => absurd hL (hne L))
    rw [hCeq] at h0
    have := S.K'_le_jLayer.trans h0.le
    exact CFSG.HardMathSupport.Solomon.Coordinator.i183v_not_le_core S.hK' inf_le_left
      (this.trans bot_le)
  by_cases haL : GLBConj a L = L
  · left
    have hsub : ∀ L' ∈ CFSG.HardMathSupport.Solomon.Coordinator.i183Family 3 H K', L' = L := by
      intro L' hL'
      obtain ⟨e, he, rfl⟩ := htrans L L' hL hL'
      exact gLBConj_eq_of_mem_normalizer
        (Subgroup.zpowers_le.2 (mem_normalizer_iff_gLBConj_eq.2 haL) he)
    refine ⟨L, hL.1, haL, ?_⟩
    rw [← hCeq]
    exact le_antisymm (iSup₂_le fun L' hL' => (hsub L' hL').le) (le_iSup₂_of_le L hL le_rfl)
  · right
    have ha3' : a * (a * a) = 1 := by
      rw [← pow_three]
      exact S.ha3
    have h3 : GLBConj a (GLBConj a (GLBConj a L)) = L := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj, ha3', gLBConj_one]
    have h2 : GLBConj a (GLBConj a L) ≠ L := by
      intro h
      apply haL
      exact (h3.symm.trans (congrArg (GLBConj a) h)).symm
    have hL1 := hstab L hL
    have hL2 := hstab _ hL1
    refine ⟨L, ⟨S.haH, S.ha3, hL.1, haL, h2⟩, ?_⟩
    rw [← hCeq]
    refine le_antisymm (iSup₂_le fun L' hL' => ?_) (sup_le (sup_le
      (le_iSup₂_of_le L hL le_rfl) (le_iSup₂_of_le _ hL1 le_rfl)) (le_iSup₂_of_le _ hL2 le_rfl))
    obtain ⟨e, he, rfl⟩ := htrans L L' hL hL'
    obtain ⟨r, hr, rfl⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i183v_mem_zpowers S.ha3 he
    have hcg : GLBConj (a ^ r) L = CFSG.HardMathSupport.Solomon.Coordinator.i183vM a L r := rfl
    rw [hcg]
    interval_cases r
    · rw [CFSG.HardMathSupport.Solomon.Coordinator.i183vM_zero]
      exact le_sup_of_le_left le_sup_left
    · rw [CFSG.HardMathSupport.Solomon.Coordinator.i183vM_one]
      exact le_sup_of_le_left le_sup_right
    · rw [CFSG.HardMathSupport.Solomon.Coordinator.i183vM_two]
      exact le_sup_right

end Situation

section Types

variable {G : Type} [Group G] [Finite G] {M E A K H : Subgroup G} {a : G} {K' : Subgroup G}

theorem center_eq_bot_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ∃ x y : X, x * y ≠ y * x) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hX
    have hx : x ∈ Subgroup.center X := h ▸ Subgroup.mem_top x
    exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)

theorem center_eq_bot_of_isLThreeFour {X : Type} [Group X] (h : IsLThreeFour X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨hs, hn⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour h
  exact center_eq_bot_of_simple hn

theorem Sit.isLThreeFour_of_mem_dQ (S : Sit M E A K H a K') {L : Subgroup G}
    (hL : GLAPComponent 3 H L) (hJ : Lemma1115.jLayer a H = L)
    (hdQ : a ∈ CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L) :
    IsLThreeFour (barOf 3 L) := by
  have hE : IsPGroup 3 ↥(Subgroup.zpowers a) :=
    (CFSG.Open.IsElemAbelian.isPGroup S.cfg.hAel).to_le (Subgroup.zpowers_le.2 S.cfg.ha)
  have hEd : Subgroup.zpowers a ≤ CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L :=
    Subgroup.zpowers_le.2 hdQ
  obtain ⟨J', hJ', -, huniq, -, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.ia_cover
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.coverStmt hL hE hEd
  rw [centralizer_zpowers_eq] at huniq
  have hK'L : K' ≤ L := hJ ▸ S.K'_le_jLayer
  have hK'c : GLAPComponent 3 (L ⊓ Cg a) K' :=
    glaPComponent_of_le Nat.prime_three S.hK' (le_inf hK'L (S.hK'.1.trans inf_le_right))
      (inf_le_inf_right _ hL.1)
  have hJK' : K' = J' := huniq K' hK'c
  subst hJK'
  have h34 := isLThreeFour_barOf_K' S.cfg S.hK' S.hbar
  obtain ⟨F, hF, hFf, hc, ⟨f⟩⟩ := h34
  exact ⟨F, hF, hFf, hc, ⟨e.symm.trans f⟩⟩

theorem Sit.single_types (hup34 : CFSG.HardMathSupport.Dickson.Sec6.Up34Statement)
    (S : Sit M E A K H a K') {L : Subgroup G} (hL : GLAPComponent 3 H L) (haL : GLBConj a L = L)
    (hJ : Lemma1115.jLayer a H = L) :
    (a ∈ CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L ∧ IsLThreeFour (barOf 3 L)) ∨
    (a ∉ CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L ∧
      ∃ haN : a ∈ Subgroup.normalizer (L : Set G),
      ((CFSG.HardMathSupport.Solomon.Coordinator.IsCatalogLieIso
          (barOf 3 L ⧸ Subgroup.center (barOf 3 L))
          CFSG.HardMathSupport.Solomon.Coordinator.IsL364Index ∧
        ¬ CFSG.HardMathSupport.Solomon.LocalBalance.IsInnDiagThree
          (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L ⟨a, haN⟩)) ∨
      CFSG.HardMathSupport.Solomon.Coordinator.IsCatalogLieIso
        (barOf 3 L ⧸ Subgroup.center (barOf 3 L))
        CFSG.HardMathSupport.Solomon.Coordinator.Is3D44Index ∨
      (CFSG.HardMathSupport.Solomon.Coordinator.IsCatalogLieIso (barOf 3 L)
          CFSG.HardMathSupport.Solomon.Coordinator.IsD44Index ∧
        Subgroup.center (barOf 3 L) = ⊥))) := by
  by_cases hdQ : a ∈ CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L
  · exact Or.inl ⟨hdQ, S.isLThreeFour_of_mem_dQ hL hJ hdQ⟩
  · right
    have haN : a ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 haL
    refine ⟨hdQ, haN, ?_⟩
    have hK'L : K' ≤ L := hJ ▸ S.K'_le_jLayer
    have hK'c : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({a} : Set G)) K' :=
      glaPComponent_of_le Nat.prime_three S.hK' (le_inf hK'L (S.hK'.1.trans inf_le_right))
        (inf_le_inf_right _ hL.1)
    exact hup34 G H L (CFSG.HardMathSupport.Solomon.Coordinator.isKGroup_of_openIsKGroup S.hKH)
      hL a S.haH haN S.ha3 hdQ K' hK'c (isLThreeFour_barOf_K' S.cfg S.hK' S.hbar)

theorem Sit.triple_type (S : Sit M E A K H a K') {L : Subgroup G}
    (c : CFSG.HardMathSupport.Solomon.Coordinator.I183vCyc H a L)
    (hJ : Lemma1115.jLayer a H = L ⊔ GLBConj a L ⊔ GLBConj a (GLBConj a L)) :
    IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) := by
  have hK'J : K' ≤ L ⊔ GLBConj a L ⊔ GLBConj a (GLBConj a L) := hJ ▸ S.K'_le_jLayer
  obtain ⟨Z, hZn, hZc, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i183v_diag c S.hK' hK'J
  have h34 : IsLThreeFour (barOf 3 L ⧸ Z) := by
    obtain ⟨F, hF, hFf, hc, ⟨f⟩⟩ := isLThreeFour_barOf_K' S.cfg S.hK' S.hbar
    exact ⟨F, hF, hFf, hc, ⟨φ.symm.trans f⟩⟩
  have hcen : Subgroup.center (barOf 3 L) ≤ Z := by
    intro z hz
    have hbot := center_eq_bot_of_isLThreeFour h34
    have hmem : (QuotientGroup.mk z : barOf 3 L ⧸ Z) ∈ Subgroup.center (barOf 3 L ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.1 hz y)]
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  have hZeq : Z = Subgroup.center (barOf 3 L) := le_antisymm hZc hcen
  subst hZeq
  exact h34

theorem pRank_mulAut_le_two_of_L34 {Y : Type} [Group Y] [Finite Y] (hY : commutator Y = ⊤)
    (h : IsLThreeFour (Y ⧸ Subgroup.center Y)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) ≤ 2 := by
  refine (CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_le_quot hY).trans ?_
  obtain ⟨k, hk, hk4, ⟨e⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL h
  have : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk4
  rw [CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_of_mulEquiv e]
  exact CFSG.HardMathSupport.Solomon.Coordinator.pRank_mulAut_projectiveSL_le_two (Or.inl (by
    rw [hk4]))

theorem barX_le_glbCore_of_L34 {L B1 : Subgroup G} (hL : GLAPComponent 3 H L)
    (h34 : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L)))
    (hB1H : B1 ≤ H) (hB1 : IsElemAbelian 3 B1) (hB1c : Nat.card B1 = 3 ^ 4) :
    barX 3 H L ≤ barX 3 H (GLBCore 3 2 B1) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hperf : commutator (barOf 3 L) = ⊤ := by
    exact (CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX hp hL.1 hL.2.1).symm hL.2.2.1.2.2).1
  have haut : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥(barX 3 H L))) ≤ 2 := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_of_mulEquiv
      (quotEquivBarX hp hL.1 hL.2.1)]
    exact pRank_mulAut_le_two_of_L34 hperf h34
  have hB1el : IsElemAbelian 3 (barX 3 H B1) := (hB1.subgroupOf H).map _
  have hB1card : Nat.card (barX 3 H B1) = 3 ^ 4 := by
    have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥H) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1
        (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥H)
    unfold barX
    rw [Inputs1114.card_map_mk_of_isPGroup hN (hB1.subgroupOf H).isPGroup,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB1H).toEquiv, hB1c]
  have hrk : 4 ≤ CFSG.Open.pRank 3 (barX 3 H B1) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hB1el hB1card
  have h225 := GL83.I_22_5_proved (↥H ⧸ GLAPPrimeCore 3 ↥H) 3 hp
    (glaPPrimeCore_quotient_eq_bot hp) (barX 3 H L) hL.2.2.1 (barX 3 H B1) hB1el (by omega) 2
    (by norm_num) (by omega)
  exact h225.trans (Inputs1115.glbCore_barX_le hp 2 hB1.isPGroup hB1H)

end Types

section Rank

variable {G : Type} [Group G] [Finite G]

theorem mem_of_centralizes_of_rank {A : Subgroup G} {a : G} (hA : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (haA : a ∈ A) (hrank : CFSG.Open.pRank 3 (Cg a) = 3) {c : G}
    (hc3 : c ^ 3 = 1) (hcA : ∀ x ∈ A, c * x = x * c) : c ∈ A := by
  by_contra hcA'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc1 : c ≠ 1 := fun h => hcA' (h ▸ A.one_mem)
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcomm : ∀ x ∈ A, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_right (show Commute x c from (hcA x hx).symm) n)).eq
  have hF : IsElemAbelian 3 (A ⊔ Subgroup.zpowers c) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hA (CFSG.Open.isElemAbelian_zpowers hc3) hcomm
  have hFcard : Nat.card (A ⊔ Subgroup.zpowers c : Subgroup G) = 3 ^ 4 := by
    rw [GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcomm
      (GL83.CompFam.inf_zpowers_eq_bot hord hcA'), hA27, Nat.card_zpowers, hord]
    norm_num
  have hFC : A ⊔ Subgroup.zpowers c ≤ Cg a := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg Subtype.val (hF.1.is_comm.comm ⟨y, hy⟩ ⟨a, Subgroup.mem_sup_left haA⟩)
    simpa using this
  have h4 := CFSG.SectionRank.le_pRank (by norm_num) hFC hF hFcard
  omega

variable {M E A K H : Subgroup G} {a : G} {K' : Subgroup G}

theorem card_barX_of_isPGroup {X P : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup 3 ↥P) :
    Nat.card ↥(barX 3 X P) = Nat.card P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥X)
  unfold barX
  rw [Inputs1114.card_map_mk_of_isPGroup hN (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv]

theorem Sit.mem_barX_A (S : Sit M E A K H a K') {y : ↥H ⧸ GLAPPrimeCore 3 ↥H} (hy3 : y ^ 3 = 1)
    (hy : y ∈ Subgroup.centralizer (barX 3 H A : Set (↥H ⧸ GLAPPrimeCore 3 ↥H))) :
    y ∈ barX 3 H A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 ↥A := CFSG.Open.IsElemAbelian.isPGroup S.cfg.hAel
  obtain ⟨c, hc, rfl⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_centralizer_barX_le Nat.prime_three S.hAH hAp hy
  have hcA : (c : G) ∈ Subgroup.centralizer (A : Set G) := (Subgroup.mem_subgroupOf.1 hc).2
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) with hπ
  have hc3 : c ^ 3 ∈ GLAPPrimeCore 3 ↥H := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact hy3
  set r := orderOf (c ^ 3) with hr
  have hrcop : Nat.Coprime r 3 := by
    have h1 : r ∣ Nat.card (GLAPPrimeCore 3 ↥H) := Subgroup.orderOf_dvd_natCard _ hc3
    exact (Nat.Coprime.coprime_dvd_right h1
      (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥H)).symm
  have hcr3 : (c ^ r) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hr, pow_orderOf_eq_one]
  have hcrA : ((c ^ r : ↥H) : G) ∈ A := by
    refine mem_of_centralizes_of_rank S.cfg.hAel S.cfg.hA27 S.cfg.ha S.hrank ?_ ?_
    · have := congrArg Subtype.val hcr3
      simpa using this
    · intro x hx
      have hcx : (c : G) * x = x * c := (Subgroup.mem_centralizer_iff.1 hcA x hx).symm
      simp only [Subgroup.coe_pow]
      exact ((Commute.pow_left (show Commute (c : G) x from hcx) r)).eq
  have hyr : π c ^ r ∈ barX 3 H A := by
    rw [← map_pow]
    exact ⟨c ^ r, Subgroup.mem_subgroupOf.2 hcrA, rfl⟩
  have hgcd : r.gcd (orderOf (π c)) = 1 :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hy3) hrcop
  exact (Subgroup.zpowers_le.2 hyr) (mem_zpowers_pow_iff.2 hgcd)

theorem Sit.eq_one_of_A0 (S : Sit M E A K H a K') {x : G} (hx : x ∈ E ⊓ A)
    (hxk : ∀ k ∈ K', x * k * x⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 H) : x = 1 := by
  have hxK' : x ∈ K' := S.A0_le hx
  have hK'H : K' ≤ H := S.hK'.1.trans inf_le_left
  have hle : K' ⊓ GLAPPrimeCoreOf 3 H ≤ GLAPPrimeCoreOf 3 K' := by
    refine Inputs1115.le_glaPPrimeCoreOf_of_le_normalizer inf_le_left ?_ ?_
    · intro g hg
      exact Inputs1115.mem_normalizer_inf (Subgroup.le_normalizer hg)
        (le_normalizer_glaPPrimeCoreOf 3 H (hK'H hg))
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 H)
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K') with hπ
  have hcen : π ⟨x, hxK'⟩ ∈ Subgroup.center (barOf 3 K') := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K') z
    have hc : x * k * x⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 K' :=
      hle ⟨K'.mul_mem (K'.mul_mem (K'.mul_mem hxK' k.2) (K'.inv_mem hxK')) (K'.inv_mem k.2),
        hxk k k.2⟩
    obtain ⟨w, hw, hwc⟩ := hc
    have hw' : w = ⟨x, hxK'⟩ * k * ⟨x, hxK'⟩⁻¹ * k⁻¹ := Subtype.ext (by simpa using hwc)
    rw [hw'] at hw
    have h1 : π (⟨x, hxK'⟩ * k * ⟨x, hxK'⟩⁻¹ * k⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hw
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : π ⟨x, hxK'⟩ * π k = π k * π ⟨x, hxK'⟩ := by
      have := congrArg (· * (π k * π ⟨x, hxK'⟩)) h1
      simp only [one_mul] at this
      rw [← this]
      group
    exact h2.symm
  rw [center_eq_bot_of_isLThreeFour (isLThreeFour_barOf_K' S.cfg S.hK' S.hbar), Subgroup.mem_bot,
    hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  have hx3 : x ^ 3 = 1 := S.cfg.hAel.2 x hx.2
  have hdvd : orderOf (⟨x, hxK'⟩ : ↥K') ∣ Nat.card (GLAPPrimeCore 3 ↥K') :=
    Subgroup.orderOf_dvd_natCard _ hcen
  rw [Subgroup.orderOf_mk] at hdvd
  have hcop := CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥K'
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : Nat.Coprime 3 (orderOf x) := Nat.Coprime.coprime_dvd_right hdvd hcop
  have h3 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact h
    · rw [h] at h2; norm_num at h2
  exact orderOf_eq_one_iff.1 h3

theorem barX_le_centralizer_of_ne' {X L L' : Subgroup G} (hL : GLAPComponent 3 X L)
    (hL' : GLAPComponent 3 X L') (hne : L ≠ L') :
    barX 3 X L' ≤ Subgroup.centralizer (barX 3 X L : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
  have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne
    Nat.prime_three hL' hL (Ne.symm hne)
  have h2 : barX 3 X ⁅L', L⁆ = ⊥ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_eq_bot_iff
      (commutator_le_of_le' hL'.1 hL.1)).2 h1
  rw [barX_commutator 3 hL'.1 hL.1] at h2
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2

theorem exists_central_of_normal {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]
    {S T : Subgroup Γ} (hS : IsPGroup p ↥S) (hTS : T ≤ S)
    (hTn : S ≤ Subgroup.normalizer (T : Set Γ)) (hT : T ≠ ⊥) :
    ∃ z ∈ T, orderOf z = p ∧ ∀ s ∈ S, s * z = z * s := by
  haveI : (T.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTS).2 hTn
  haveI : Group.IsNilpotent ↥S := hS.isNilpotent
  have hne : T.subgroupOf S ≠ ⊥ := by
    intro h
    apply hT
    rw [Subgroup.subgroupOf_eq_bot] at h
    rw [← inf_eq_left.2 hTS]
    exact disjoint_iff.1 h
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hp : IsPGroup p ↥(T.subgroupOf S ⊓ Subgroup.center ↥S) :=
    hS.to_subgroup (T.subgroupOf S ⊓ Subgroup.center ↥S)
  obtain ⟨w, hw⟩ : ∃ w : ↥(T.subgroupOf S ⊓ Subgroup.center ↥S), orderOf w = p := by
    have hnt : Nontrivial ↥(T.subgroupOf S ⊓ Subgroup.center ↥S) := Subgroup.nontrivial_iff_ne_bot _ |>.2 h1
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.2 hnt).ne' hk
    exact exists_prime_orderOf_dvd_card' p (hk ▸ dvd_pow_self p hk0)
  refine ⟨((w : ↥S) : Γ), Subgroup.mem_subgroupOf.1 w.2.1, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  · have := Subgroup.mem_center_iff.1 w.2.2 ⟨s, hs⟩
    exact congrArg Subtype.val this

end Rank

section Normal

variable {G : Type} [Group G] [Finite G] {M E A K H : Subgroup G} {a : G} {K' : Subgroup G}

theorem commutator_mem_core_of_commute {p : ℕ} {X : Subgroup G} {x k : G} (hx : x ∈ X) (hk : k ∈ X)
    (h : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hx⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨k, hk⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨k, hk⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hx⟩) :
    x * k * x⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf p X := by
  set c : ↥X := ⟨x, hx⟩ * ⟨k, hk⟩ * (⟨x, hx⟩ : ↥X)⁻¹ * (⟨k, hk⟩ : ↥X)⁻¹ with hc
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) c = 1 := by
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨c, h1, by simp [hc]⟩

theorem Sit.le_normalizer_single (S : Sit M E A K H a K') {L : Subgroup G}
    (hL : GLAPComponent 3 H L) (haL : GLBConj a L = L) (hJ : Lemma1115.jLayer a H = L) :
    H ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h hh
  rw [mem_normalizer_iff_gLBConj_eq]
  by_contra hne
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥H) with hπ
  set L₂ := GLBConj h L with hL₂def
  set L₃ := GLBConj a L₂ with hL₃def
  set L₄ := GLBConj a L₃ with hL₄def
  have hL₂ : GLAPComponent 3 H L₂ := Inputs1115.glaPComponent_conj_of_mem hL hh
  have hL₃ : GLAPComponent 3 H L₃ := Inputs1115.glaPComponent_conj_of_mem hL₂ S.haH
  have hL₄ : GLAPComponent 3 H L₄ := Inputs1115.glaPComponent_conj_of_mem hL₃ S.haH
  have haN : a ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 haL
  have hainvL : GLBConj a⁻¹ L = L := gLBConj_eq_of_mem_normalizer (Subgroup.inv_mem _ haN)
  have hne₂ : L ≠ L₂ := fun h' => hne h'.symm
  have hne₃ : L ≠ L₃ := by
    intro h'
    apply hne₂
    have e : L₂ = GLBConj a⁻¹ L₃ := by rw [hL₃def, gLBConj_inv_gLBConj]
    rw [e, ← h', hainvL]
  have hne₄ : L ≠ L₄ := by
    intro h'
    apply hne₃
    have e : L₃ = GLBConj a⁻¹ L₄ := by rw [hL₄def, gLBConj_inv_gLBConj]
    rw [e, ← h', hainvL]
  set V' : Subgroup G := L₂ ⊔ L₃ ⊔ L₄ with hV'def
  have hV'H : V' ≤ H := sup_le (sup_le hL₂.1 hL₃.1) hL₄.1
  have haV' : a ∈ Subgroup.normalizer (V' : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    have ha3' : a * (a * a) = 1 := by rw [← pow_three]; exact S.ha3
    have h5 : GLBConj a L₄ = L₂ := by
      rw [hL₄def, hL₃def, gLBConj_gLBConj, gLBConj_gLBConj, ha3', gLBConj_one]
    have hmap : ∀ X Y : Subgroup G, GLBConj a (X ⊔ Y) = GLBConj a X ⊔ GLBConj a Y :=
      fun X Y => Subgroup.map_sup X Y _
    rw [hV'def, hmap, hmap, ← hL₃def, ← hL₄def, h5]
    rw [sup_comm (L₃ ⊔ L₄) L₂, sup_assoc]
  set V : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H) := barX 3 H V' with hVdef
  have hVc : V ≤ Subgroup.centralizer (barX 3 H L : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := by
    rw [hVdef, hV'def, CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup
      (sup_le hL₂.1 hL₃.1) hL₄.1, CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup hL₂.1 hL₃.1]
    exact sup_le (sup_le (barX_le_centralizer_of_ne' hL hL₂ hne₂)
      (barX_le_centralizer_of_ne' hL hL₃ hne₃)) (barX_le_centralizer_of_ne' hL hL₄ hne₄)
  have hA0L : E ⊓ A ≤ L := S.A0_le.trans (hJ ▸ S.K'_le_jLayer)
  have hA0H : E ⊓ A ≤ H := inf_le_right.trans S.hAH
  have hK'L : K' ≤ L := hJ ▸ S.K'_le_jLayer
  set A0b : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H) := barX 3 H (E ⊓ A) with hA0bdef
  set Ab : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H) := barX 3 H A with hAbdef
  have hA0bL : A0b ≤ barX 3 H L := Inputs1115.barX_le_barX hA0L
  have hA0V : A0b ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨x, hx, rfl⟩, hvV⟩
    have hx' : (x : G) ∈ E ⊓ A := Subgroup.mem_subgroupOf.1 hx
    have hx1 : (x : G) = 1 := by
      refine S.eq_one_of_A0 hx' fun k hk => ?_
      have hkH : k ∈ H := (S.hK'.1.trans inf_le_left) hk
      have hcomm := Subgroup.mem_centralizer_iff.1 (hVc hvV) _
        (Inputs1115.mk_mem_barX hkH (hK'L hk))
      have e1 : (⟨(x : G), x.2⟩ : ↥H) = x := rfl
      refine commutator_mem_core_of_commute x.2 hkH ?_
      rw [e1]
      exact hcomm.symm
    have : x = 1 := Subtype.ext hx1
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hAp : IsPGroup 3 ↥A := CFSG.Open.IsElemAbelian.isPGroup S.cfg.hAel
  have hA0el : IsElemAbelian 3 (E ⊓ A : Subgroup G) := S.cfg.hAel.mono inf_le_right
  have hAbel : IsElemAbelian 3 Ab := (S.cfg.hAel.subgroupOf H).map _
  have hA0bA : A0b ≤ Ab := Inputs1115.barX_le_barX inf_le_right
  have hAbcard : Nat.card Ab = 27 := by
    rw [hAbdef, card_barX_of_isPGroup S.hAH hAp, S.cfg.hA27]
  have hA0bcard : Nat.card A0b = 9 := by
    rw [hA0bdef, card_barX_of_isPGroup hA0H (hAp.to_le inf_le_right), S.cfg.hA0card]
  have hAeq : (E ⊓ A) ⊔ Subgroup.zpowers a = A :=
    (Lemma1114.coord_setup S.cfg.hAel S.cfg.hA27 inf_le_right S.cfg.hA0card S.cfg.ha S.cfg.ha1
      S.cfg.haA0).2
  have hAV : Ab ≤ Subgroup.normalizer (V : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := by
    rw [hAbdef, ← hAeq, CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup hA0H
      (Subgroup.zpowers_le.2 S.haH)]
    refine sup_le ?_ ?_
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.1 (hVc hv) u (hA0bL hu)).symm
    · exact barX_le_normalizer (Subgroup.zpowers_le.2 haV')
  set F : Subgroup G := GLBConj h (E ⊓ A) with hFdef
  have hFL₂ : F ≤ L₂ := gLBConj_mono h hA0L
  have hFH : F ≤ H := hFL₂.trans hL₂.1
  have hFel : IsElemAbelian 3 F := isElemAbelian_GLBConj h hA0el
  have hFcard : Nat.card F = 9 := by rw [hFdef, Lemma1112b.card_glbConj, S.cfg.hA0card]
  set Fb : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H) := barX 3 H F with hFbdef
  have hFbV : Fb ≤ V := Inputs1115.barX_le_barX (le_sup_left.trans le_sup_left |>.trans' hFL₂)
  have hFbel : IsElemAbelian 3 Fb := (hFel.subgroupOf H).map _
  have hFbcard : Nat.card Fb = 9 := by
    rw [hFbdef, card_barX_of_isPGroup hFH hFel.isPGroup, hFcard]
  set Y : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H) := V ⊔ Ab with hYdef
  have hYN : Y ≤ Subgroup.normalizer (V : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) :=
    sup_le Subgroup.le_normalizer hAV
  obtain ⟨x, hxY, S₀, hS₀p, hS₀Y, hAS₀, hFS₀⟩ :=
    exists_conj_le_pGroup' (p := 3) (K := Y) (X := Ab) (Y := Fb) le_sup_right hAbel.isPGroup
      (hFbV.trans le_sup_left) hFbel.isPGroup
  have hFxV : GLBConj x Fb ≤ V := by
    have := gLBConj_mono x hFbV
    rwa [gLBConj_eq_of_mem_normalizer (hYN hxY)] at this
  set T : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H) := S₀ ⊓ V with hTdef
  have hFT : GLBConj x Fb ≤ T := le_inf hFS₀ hFxV
  have hFxcard : Nat.card (GLBConj x Fb) = 9 := by rw [Lemma1112b.card_glbConj, hFbcard]
  have hT0 : T ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (GLBConj x Fb) ≤ Nat.card T := Subgroup.card_le_of_le hFT
    rw [hbot, Subgroup.card_bot, hFxcard] at h1
    omega
  have hS₀T : S₀ ≤ Subgroup.normalizer (T : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := fun s hs =>
    Inputs1115.mem_normalizer_inf (Subgroup.le_normalizer hs) (hYN (hS₀Y hs))
  obtain ⟨z, hzT, hz3, hzc⟩ := exists_central_of_normal hS₀p inf_le_left hS₀T hT0
  have hzA : z ∈ Ab := by
    refine S.mem_barX_A (by have := pow_orderOf_eq_one z; rwa [hz3] at this) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hzc u (hAS₀ hu)
  have hzA0 : z ∉ A0b := by
    intro hz
    have h1 : z ∈ A0b ⊓ V := ⟨hz, hzT.2⟩
    rw [hA0V, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hz3
    norm_num at hz3
  have hAz : A0b ⊔ Subgroup.zpowers z = Ab := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hA0bA (Subgroup.zpowers_le.2 hzA)) ?_
    rw [GL83.CompFam.card_sup_zpowers hAbel hA0bA hzA hzA0, hA0bcard, hAbcard]
  have hTc : ∀ t ∈ T, Ab ≤ Subgroup.centralizer ({t} : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)) := by
    intro t ht
    rw [← hAz]
    refine sup_le ?_ (Subgroup.zpowers_le.2 ?_)
    · intro u hu
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (hVc ht.2) u (hA0bL hu)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hzc t ht.1).symm
  have hFxel : IsElemAbelian 3 (GLBConj x Fb) := isElemAbelian_GLBConj x hFbel
  have hFAV : GLBConj x Fb ≤ Ab ⊓ V := by
    intro e he
    refine ⟨S.mem_barX_A (hFxel.2 e he) ?_, hFxV he⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.1 (hTc e (hFT he) hu)
  have hAVcard : Nat.card (Ab ⊓ V : Subgroup _) ≤ 3 := by
    have hc : ∀ u ∈ Ab ⊓ V, ∀ w ∈ A0b, u * w = w * u := fun u hu w hw =>
      congrArg Subtype.val (hAbel.1.is_comm.comm ⟨u, hu.1⟩ ⟨w, hA0bA hw⟩)
    have hd : (Ab ⊓ V) ⊓ A0b = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have : u ∈ A0b ⊓ V := ⟨hu.2, hu.1.2⟩
      rwa [hA0V] at this
    have h1 := GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hc hd
    have h2 : Nat.card ((Ab ⊓ V) ⊔ A0b : Subgroup _) ≤ Nat.card Ab :=
      Subgroup.card_le_of_le (sup_le inf_le_left hA0bA)
    rw [h1, hA0bcard, hAbcard] at h2
    omega
  have := Subgroup.card_le_of_le hFAV
  omega

end Normal

section Transfer

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

open CFSG.HardMathSupport.Solomon.Coordinator (c25Img c25Fix c25_transfer c25Img_isElemAbelian
  IsCatalogLieIso IsL364Index Is3D44Index IsD44Index)

theorem barX_le_of_le_sup {L X N : Subgroup G} (hL : GLAPComponent 3 H L) (hXL : X ≤ L)
    (hXN : X ≤ N) (hLX : L ≤ X ⊔ GLAPPrimeCoreOf 3 L) : barX 3 H L ≤ barX 3 H N := by
  have hOL : GLAPPrimeCoreOf 3 L ≤ L := Subgroup.map_subtype_le _
  have hOH : GLAPPrimeCoreOf 3 L ≤ GLAPPrimeCoreOf 3 H :=
    glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hL.2.1
  calc barX 3 H L ≤ barX 3 H (X ⊔ GLAPPrimeCoreOf 3 L) := Inputs1115.barX_le_barX hLX
    _ = barX 3 H X ⊔ barX 3 H (GLAPPrimeCoreOf 3 L) :=
        CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup (hXL.trans hL.1) (hOL.trans hL.1)
    _ = barX 3 H X := by
        rw [(CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_eq_bot_iff (hOL.trans hL.1)).2 hOH,
          sup_bot_eq]
    _ ≤ barX 3 H N := Inputs1115.barX_le_barX hXN

theorem gammaOne_le_glbCore (L : Subgroup G) {B1 : Subgroup G} (hB1 : IsElemAbelian 3 B1) {k : ℕ}
    (hB1c : Nat.card B1 = 3 ^ k) (hk : 3 ≤ k) :
    (⨆ (E : Subgroup G) (_ : E ≤ B1 ∧ CFSG.pRank 3 ↥B1 - 1 ≤ CFSG.pRank 3 ↥E),
      L ⊓ Subgroup.centralizer (E : Set G)) ≤ GLBCore 3 2 B1 := by
  refine iSup₂_le fun E hE => ?_
  have hrk : CFSG.pRank 3 ↥B1 = k :=
    CFSG.HardMathSupport.Solomon.Coordinator.c25_pRank_eq hB1 hB1c
  have h2 : 2 ≤ CFSG.Open.pRank 3 E := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    omega
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (E : Set G)).trans
    (le_sSup ⟨E, hE.1, h2, rfl⟩))

theorem barOf_facts {L : Subgroup G} (hL : GLAPComponent 3 H L) :
    CFSG.Open.IsQuasisimple (barOf 3 L) ∧ GLAPPrimeCore 3 (barOf 3 L) = ⊥ :=
  ⟨CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX Nat.prime_three hL.1 hL.2.1).symm hL.2.2.1.2.2,
    glaPPrimeCore_quotient_eq_bot Nat.prime_three⟩

theorem barX_le_glbCore_of_gen {L B : Subgroup G} (hL : GLAPComponent 3 H L)
    (hB : IsElemAbelian 3 B) {k : ℕ} (hBc : Nat.card B = 3 ^ k) (hk : 3 ≤ k)
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hgen : ⊤ ≤ ⨆ (S : Subgroup (MulAut (barOf 3 L)))
      (_ : S ≤ c25Img L B ∧ Nat.card (c25Img L B) ≤ 3 * Nat.card S), c25Fix S) :
    barX 3 H L ≤ barX 3 H (GLBCore 3 2 B) := by
  have h := c25_transfer hB hBN (fun X => X) (fun X => X) (fun X => le_rfl) (fun E _ => le_rfl) hgen
  exact barX_le_of_le_sup hL (iSup₂_le fun E _ => inf_le_left) (gammaOne_le_glbCore L hB hBc hk) h

theorem barX_le_glbCore_of_ker {L B : Subgroup G} (hL : GLAPComponent 3 H L)
    (hB : IsElemAbelian 3 B)
    (h9 : 9 ≤ Nat.card ↥(CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L ⊓ B)) :
    barX 3 H L ≤ barX 3 H (GLBCore 3 2 B) := by
  set D := CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L ⊓ B with hD
  have hDel : IsElemAbelian 3 D := hB.mono inf_le_right
  obtain ⟨J', -, -, -, hLJ', hJ'le, -⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.ia_cover
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.coverStmt hL hDel.isPGroup inf_le_left
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hDel.isPGroup.exists_card_eq
  have hj2 : 2 ≤ j := by
    by_contra hj2
    have : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : 2 ≤ CFSG.Open.pRank 3 D :=
    hj2.trans (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hDel hj)
  refine barX_le_of_le_sup hL (X := L ⊓ Subgroup.centralizer (D : Set G)) inf_le_left ?_
    (hLJ'.trans (sup_le_sup_right hJ'le _))
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (D : Set G)).trans
    (le_sSup ⟨D, inf_le_right, h2, rfl⟩))

theorem barX_le_glbCore_of_L364 {L B1 : Subgroup G} (hL : GLAPComponent 3 H L)
    (hcat : IsCatalogLieIso (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) IsL364Index)
    (hB1 : IsElemAbelian 3 B1) (hB1c : Nat.card B1 = 3 ^ 4)
    (hBN : B1 ≤ Subgroup.normalizer (L : Set G)) :
    barX 3 H L ≤ barX 3 H (GLBCore 3 2 B1) := by
  obtain ⟨hq, hcore⟩ := barOf_facts hL
  by_cases hα : ∃ α ∈ c25Img L B1, α ≠ 1 ∧
      ¬ CFSG.HardMathSupport.Solomon.LocalBalance.IsInnDiagThree α
  · refine barX_le_glbCore_of_gen hL hB1 hB1c (by norm_num) hBN ?_
    exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.genL364Narrow_of_rank3
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.l364Rank3Gen_of_heis
        CFSG.HardMathSupport.Dickson.Sec6.l364Rank3Heis_holds) _ hq hcore hcat _
      (c25Img_isElemAbelian hB1) hα
  · push Not at hα
    obtain ⟨K₀, hK₀, hK₀f, hK₀c, ⟨e⟩⟩ :=
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.exists_model_of_catalogL364 hcat
    have hT : CFSG.HardMathSupport.Solomon.LocalBalance.IsThreeType (barOf 3 L) :=
      Or.inl ⟨K₀, hK₀, hK₀f, ⟨e⟩⟩
    have hall : ∀ α ∈ c25Img L B1, CFSG.HardMathSupport.Solomon.LocalBalance.IsInnDiagThree α := by
      intro α hαA
      by_cases h1 : α = 1
      · subst h1
        exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.isInnDiagThree_one hT
      · exact hα α hαA h1
    have heps : CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeEps
        (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) :=
      Or.inl ⟨K₀, hK₀, hK₀f, by rw [hK₀c], ⟨e⟩⟩
    have h9 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.innDiagRankTwo_holds _ hq heps
      _ (c25Img_isElemAbelian hB1) hall
    rw [CFSG.HardMathSupport.Solomon.Coordinator.card_c25Img hBN] at h9
    refine barX_le_glbCore_of_ker hL hB1 ?_
    have hmul := Subgroup.relIndex_mul_card (CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L) B1
    rw [hB1c] at hmul
    have hpos : 0 < Nat.card ↥(CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L ⊓ B1) :=
      Nat.card_pos
    nlinarith

theorem barX_le_glbCore_of_3D44 (hgen : CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Statement)
    {L B1 : Subgroup G} (hL : GLAPComponent 3 H L)
    (hcat : IsCatalogLieIso (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) Is3D44Index)
    (hB1 : IsElemAbelian 3 B1) (hB1c : Nat.card B1 = 3 ^ 4)
    (hBN : B1 ≤ Subgroup.normalizer (L : Set G)) :
    barX 3 H L ≤ barX 3 H (GLBCore 3 2 B1) := by
  obtain ⟨hq, hcore⟩ := barOf_facts hL
  exact barX_le_glbCore_of_gen hL hB1 hB1c (by norm_num) hBN
    (hgen _ hq hcore hcat _ (c25Img_isElemAbelian hB1))

end Transfer

section D44

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.Coordinator (c25Img c25Fix c25Img_isElemAbelian IsCatalogLieIso
  IsD44Index)

@[expose] def Seitz2310D44Inner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → IsCatalogLieIso Y IsD44Index →
    ∀ A : Subgroup (MulAut Y), IsElemAbelian 3 A → Nat.card A = 3 ^ 3 →
      A ≤ (MulAut.conj : Y →* MulAut Y).range → CFSG.LieType.Seitz.seitzHyperGamma 3 A = ⊤

@[expose] def Input10_2D44 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsCatalogLieIso Y IsD44Index →
    ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      ∃ F : Subgroup Y, E ≤ F ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 4

theorem subgroupOf_map_subtype_eq {L : Subgroup G} (S : Subgroup ↥L) :
    (S.map L.subtype).subgroupOf L = S := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem exists_lift {L P : Subgroup G} (hPL : P ≤ L) (hP : IsPGroup 3 ↥P) {Q : Subgroup (barOf 3 L)}
    (hQ : IsPGroup 3 ↥Q)
    (hPQ : (P.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) ≤ Q) :
    ∃ F : Subgroup G, P ≤ F ∧ F ≤ L ∧ IsPGroup 3 ↥F ∧
      (F.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) = Q ∧ Nat.card F = Nat.card Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := GLAPPrimeCore 3 ↥L with hN
  set π := QuotientGroup.mk' N with hπ
  set Qh : Subgroup ↥L := Q.comap π with hQh
  have hPQh : P.subgroupOf L ≤ Qh := fun x hx => hPQ ⟨x, hx, rfl⟩
  have hP' : IsPGroup 3 ↥((P.subgroupOf L).subgroupOf Qh) :=
    (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm).of_equiv
      (Subgroup.subgroupOfEquivOfLe hPQh).symm
  obtain ⟨T, hT⟩ := hP'.exists_le_sylow
  set S : Subgroup ↥L := (T : Subgroup ↥Qh).map Qh.subtype with hSdef
  have hcardQh : Nat.card Qh = Nat.card N * Nat.card Q :=
    QuotientGroup.card_preimage_mk N (Q : Set (↥L ⧸ N))
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : 3 ^ k ∣ Nat.card Qh := by
    rw [hcardQh, hk]
    exact dvd_mul_left _ _
  have hTcard : 3 ^ k ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card hdvd
  have hSp : IsPGroup 3 ↥S := T.isPGroup'.map _
  have hScard : Nat.card S = Nat.card T := Subgroup.card_map_of_injective Qh.subtype_injective
  have hNc : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥L)
  have hSmap : Nat.card (S.map π) = Nat.card S := Inputs1114.card_map_mk_of_isPGroup hNc hSp
  have hSQ : S.map π ≤ Q := by
    rintro _ ⟨s, ⟨t, -, rfl⟩, rfl⟩
    exact t.2
  have hle : Nat.card Q ≤ Nat.card (S.map π) := by
    rw [hSmap, hScard, hk]
    exact Nat.le_of_dvd Nat.card_pos hTcard
  have heq : S.map π = Q := Subgroup.eq_of_le_of_card_ge hSQ hle
  refine ⟨S.map L.subtype, ?_, Subgroup.map_subtype_le _, hSp.map _, ?_, ?_⟩
  · intro x hx
    have hxL := hPL hx
    have h1 : (⟨x, hxL⟩ : ↥L) ∈ P.subgroupOf L := Subgroup.mem_subgroupOf.2 hx
    have h2 : (⟨⟨x, hxL⟩, hPQh h1⟩ : ↥Qh) ∈ T := hT (Subgroup.mem_subgroupOf.2 h1)
    exact ⟨⟨x, hxL⟩, ⟨_, h2, rfl⟩, rfl⟩
  · rw [subgroupOf_map_subtype_eq, heq]
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hScard]
    exact le_antisymm (by rw [← hScard, ← hSmap]; exact Subgroup.card_le_of_le hSQ)
      (by rw [hk]; exact Nat.le_of_dvd Nat.card_pos hTcard)

theorem isElemAbelian_of_map {L F : Subgroup G} (hFL : F ≤ L) (hF : IsPGroup 3 ↥F)
    {Q : Subgroup (barOf 3 L)} (hQ : IsElemAbelian 3 Q)
    (hFQ : (F.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) = Q) :
    IsElemAbelian 3 F := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hπ
  have hNc : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥L)
  have hF' : IsPGroup 3 ↥(F.subgroupOf L) := hF.of_equiv (Subgroup.subgroupOfEquivOfLe hFL).symm
  have hmem : ∀ (x : G) (hx : x ∈ F), π ⟨x, hFL hx⟩ ∈ Q := fun x hx =>
    hFQ ▸ ⟨⟨x, hFL hx⟩, hx, rfl⟩
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have hu := hmem u u.2
    have hv := hmem v v.2
    have hc : π ⟨u, hFL u.2⟩ * π ⟨v, hFL v.2⟩ = π ⟨v, hFL v.2⟩ * π ⟨u, hFL u.2⟩ :=
      congrArg Subtype.val (hQ.1.is_comm.comm ⟨_, hu⟩ ⟨_, hv⟩)
    rw [← map_mul, ← map_mul] at hc
    have := Inputs1114.mk_injOn_of_isPGroup hNc hF'
      (Subgroup.mul_mem _ (show (⟨u, hFL u.2⟩ : ↥L) ∈ F.subgroupOf L from u.2)
        (show (⟨v, hFL v.2⟩ : ↥L) ∈ F.subgroupOf L from v.2))
      (Subgroup.mul_mem _ (show (⟨v, hFL v.2⟩ : ↥L) ∈ F.subgroupOf L from v.2)
        (show (⟨u, hFL u.2⟩ : ↥L) ∈ F.subgroupOf L from u.2)) hc
    have h2 := congrArg (fun w : ↥L => (w : G)) this
    simpa using h2
  · have hx3 : (π ⟨x, hFL hx⟩) ^ 3 = 1 := hQ.2 _ (hmem x hx)
    rw [← map_pow] at hx3
    have h1 : (⟨x, hFL hx⟩ : ↥L) ^ 3 ∈ F.subgroupOf L :=
      Subgroup.pow_mem _ (show (⟨x, hFL hx⟩ : ↥L) ∈ F.subgroupOf L from hx) 3
    have := Inputs1114.mk_injOn_of_isPGroup hNc hF' h1 (Subgroup.one_mem _)
      (by rw [QuotientGroup.mk_one]; exact hx3)
    have := congrArg Subtype.val this
    simpa using this

theorem exists_isSylowIn_le {p : ℕ} {X P : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup p ↥P) :
    ∃ R : Subgroup G, IsSylowIn p X R ∧ P ≤ R := by
  classical
  let 𝒮 : Set (Subgroup G) := {R | R ≤ X ∧ IsPGroup p ↥R ∧ P ≤ R}
  obtain ⟨R, ⟨hRX, hRp, hPR⟩, hmax⟩ := (Set.toFinite 𝒮).exists_maximal ⟨P, hPX, hP, le_rfl⟩
  refine ⟨R, ⟨hRX, hRp, fun R' hR'X hR'p hRR' => ?_⟩, hPR⟩
  exact le_antisymm (hmax ⟨hR'X, hR'p, hPR.trans hRR'⟩ hRR') hRR'

theorem dQ_inf_eq_bot {L F : Subgroup G} (hFL : F ≤ L) (hF : IsPGroup 3 ↥F)
    (hZ : Subgroup.center (barOf 3 L) = ⊥) :
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L ⊓ F = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  rintro x ⟨hxD, hxF⟩
  rw [Subgroup.mem_bot]
  have hxL : x ∈ L := hFL hxF
  obtain ⟨-, -, hcomm⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.mem_dQ.1 hxD
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hπ
  have hcen : π ⟨x, hxL⟩ ∈ Subgroup.center (barOf 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) z
    obtain ⟨w, hw, hwc⟩ := hcomm (y : G) y.2
    have hw' : w = y * ⟨x, hxL⟩ * y⁻¹ * (⟨x, hxL⟩ : ↥L)⁻¹ := Subtype.ext (by simpa using hwc)
    rw [hw'] at hw
    have h1 : π (y * ⟨x, hxL⟩ * y⁻¹ * (⟨x, hxL⟩ : ↥L)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hw
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π y * π ⟨x, hxL⟩ = (π y * π ⟨x, hxL⟩ * (π y)⁻¹ * (π ⟨x, hxL⟩)⁻¹) * (π ⟨x, hxL⟩ * π y) := by
          group
      _ = π ⟨x, hxL⟩ * π y := by rw [h1, one_mul]
  rw [hZ, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  have hdvd : orderOf (⟨x, hxL⟩ : ↥L) ∣ Nat.card (GLAPPrimeCore 3 ↥L) :=
    Subgroup.orderOf_dvd_natCard _ hcen
  rw [Subgroup.orderOf_mk] at hdvd
  have hcop := CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥L
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hF) ⟨x, hxF⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h3 : 3 ∣ 3 ^ k := dvd_pow_self 3 hk0
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop (h3.trans hdvd)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.1 hk

variable {M E A K H : Subgroup G} {a : G} {K' : Subgroup G}

theorem Sit.false_of_D44 {m : ℕ} {B : Subgroup G} (h : Cex117 G m 3 B M E A a K)
    (h1111 : Lemma1111Statement) (h104v : Lemma104_vStatement) (h111 : Prop111Statement)
    (hgen : Seitz2310D44Inner) (h102 : Input10_2D44) (S : Sit M E A K H a K') {L : Subgroup G}
    (hL : GLAPComponent 3 H L) (hJ : Lemma1115.jLayer a H = L)
    (hD4 : IsCatalogLieIso (barOf 3 L) IsD44Index) (hZ : Subgroup.center (barOf 3 L) = ⊥) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsec : Sec11 G m 3 B M E A := h.toCex117Base.toSec11
  obtain ⟨-, hA3, -⟩ := h1111 h
  have hA0L : E ⊓ A ≤ L := S.A0_le.trans (hJ ▸ S.K'_le_jLayer)
  have hA0el : IsElemAbelian 3 (E ⊓ A : Subgroup G) := S.cfg.hAel.mono inf_le_right
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hπ
  have hA0bel : IsElemAbelian 3 (((E ⊓ A).subgroupOf L).map π) := (hA0el.subgroupOf L).map _
  have hA0bc : Nat.card (((E ⊓ A).subgroupOf L).map π) = 3 ^ 2 := by
    have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥L)
    rw [Inputs1114.card_map_mk_of_isPGroup hN (hA0el.subgroupOf L).isPGroup,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0L).toEquiv, S.cfg.hA0card]
    norm_num
  obtain ⟨Fb, hA0Fb, hFbel, hFbc⟩ := h102 (barOf 3 L) hD4 _ hA0bel hA0bc
  obtain ⟨F, hA0F, hFL, hFp, hFmap, hFc⟩ := exists_lift hA0L hA0el.isPGroup hFbel.isPGroup hA0Fb
  rw [hFbc] at hFc
  have hFel : IsElemAbelian 3 F := isElemAbelian_of_map hFL hFp hFbel hFmap
  have hFM : F ≤ M := by
    intro f hf
    refine Inputs1115.normalizer_A0_le h (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (hFel.1.is_comm.comm ⟨x, hA0F hx⟩ ⟨f, hf⟩)
  obtain ⟨R, hRsyl, hFR⟩ := exists_isSylowIn_le hFM hFp
  have hFek : IsEkIn 3 4 R F := ⟨hFR, hFel, hFc⟩
  obtain ⟨hD0, -⟩ := h104v hsec.toSec10Fails hsec.pair (Or.inr hA3) hRsyl
  obtain ⟨-, -, A', hA'D, hFA'⟩ := hD0 F hFek
  obtain ⟨E', hE'c, -, hE'F⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := G) (p := 3)
    Nat.prime_three (n := 3) (H := ⊥) (L := F) (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hFc]; exact pow_dvd_pow 3 (by norm_num)) bot_le
  have hcoreE' : GLBCore 3 2 E' ≤ M := by
    refine le_trans ?_ hA'D.2.clause_d
    unfold GLBCore
    exact sSup_le_sSup (by
      rintro N ⟨Q, hQ, hk, rfl⟩
      exact ⟨Q, hQ.trans (hE'F.trans hFA'), hk, rfl⟩)
  have hE'el : IsElemAbelian 3 E' := hFel.mono hE'F
  have hE'L : E' ≤ L := hE'F.trans hFL
  have hE'N : E' ≤ Subgroup.normalizer (L : Set G) := hE'L.trans Subgroup.le_normalizer
  have hcard : Nat.card (c25Img L E') = 3 ^ 3 := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.card_c25Img hE'N]
    have hmul := Subgroup.relIndex_mul_card (CFSG.HardMathSupport.Solomon.UniquenessMaximal.dQ L) E'
    rw [dQ_inf_eq_bot hE'L hE'el.isPGroup hZ, Subgroup.card_bot, mul_one, hE'c] at hmul
    exact hmul
  have hinn : c25Img L E' ≤ (MulAut.conj : barOf 3 L →* MulAut (barOf 3 L)).range := by
    rintro _ ⟨⟨f, hfN⟩, hf, rfl⟩
    have hfE : f ∈ E' := Subgroup.mem_subgroupOf.1 hf
    refine ⟨QuotientGroup.mk ⟨f, hE'L hfE⟩, ?_⟩
    rw [← Inputs1114.barAut_of_mem (hE'L hfE)]
  have hsimple : IsSimpleGroup (barOf 3 L) := by
    obtain ⟨hq, -⟩ := barOf_facts hL
    haveI := hq.2
    exact MulEquiv.isSimpleGroup
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hseitz := hgen (barOf 3 L) hsimple hD4 (c25Img L E') (c25Img_isElemAbelian hE'el) hcard hinn
  have hgen' : ⊤ ≤ ⨆ (S : Subgroup (MulAut (barOf 3 L)))
      (_ : S ≤ c25Img L E' ∧ Nat.card (c25Img L E') ≤ 3 * Nat.card S), c25Fix S := by
    refine hseitz.ge.trans ?_
    unfold CFSG.LieType.Seitz.seitzHyperGamma
    refine iSup₂_le fun S hS => ?_
    refine le_iSup₂_of_le (f := fun (S : Subgroup (MulAut (barOf 3 L)))
      (_ : S ≤ c25Img L E' ∧ Nat.card (c25Img L E') ≤ 3 * Nat.card S) => c25Fix S) S ⟨hS.1, ?_⟩ ?_
    · have hm := Subgroup.relIndex_mul_card S (c25Img L E')
      rw [inf_eq_left.2 hS.1, hS.2] at hm
      omega
    · intro y hy
      exact hy
  have hcov := barX_le_glbCore_of_gen hL hE'el hE'c (by norm_num) hE'N hgen'
  have hcovM : Covers 3 H M (Lemma1115.jLayer a H) := by
    rw [hJ]
    exact hcov.trans (Inputs1115.barX_le_barX hcoreE')
  exact h.notM (Inputs1115.input1115Chain_of_inputs h111 h H S.hH hcovM)

end D44

section GammaMain

variable {G : Type} [Group G] [Finite G]

noncomputable def centerQuotEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem isLThreeFour_quot_center {X : Type} [Group X] (h : IsLThreeFour X) :
    IsLThreeFour (X ⧸ Subgroup.center X) := by
  have e : (X ⧸ Subgroup.center X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isLThreeFour h)).trans
      QuotientGroup.quotientBot
  obtain ⟨F, hF, hFf, hc, ⟨f⟩⟩ := h
  exact ⟨F, hF, hFf, hc, ⟨e.trans f⟩⟩

theorem isLThreeFour_quot_center_conj {L : Subgroup G} (g : G)
    (h : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L))) :
    IsLThreeFour (barOf 3 (GLBConj g L) ⧸ Subgroup.center (barOf 3 (GLBConj g L))) := by
  have e := centerQuotEquiv' (conjQuotEquiv 3 g L)
  obtain ⟨F, hF, hFf, hc, ⟨f⟩⟩ := h
  exact ⟨F, hF, hFf, hc, ⟨e.symm.trans f⟩⟩

theorem input1115Gamma_of_inputs (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h1111 : Lemma1111Statement) (h119 : Lemma119Statement) (h1112 : Lemma1112Statement)
    (h104v : Lemma104_vStatement) (h111 : Prop111Statement)
    (hup34 : CFSG.HardMathSupport.Dickson.Sec6.Up34Statement)
    (hgen3D4 : CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Statement)
    (hD44 : Seitz2310D44Inner) (h102 : Input10_2D44) : Lemma1115.Input1115Gamma := by
  intro G _ _ m B M E A a K h H hH B1 hB1 hB1H
  obtain ⟨K', S⟩ := exists_sit hS h1111 h119 h1112 h hH
  show barX 3 H (Lemma1115.jLayer a H) ≤ barX 3 H (GLBCore 3 2 B1 ⊓ H)
  rw [barX_inf_self]
  obtain ⟨-, hB1el, hB1c⟩ := hB1
  rcases S.cases with ⟨L, hL, haL, hJ⟩ | ⟨L, c, hJ⟩
  · rw [hJ]
    rcases S.single_types hup34 hL haL hJ with ⟨-, h34⟩ | ⟨-, haN, htype⟩
    · exact barX_le_glbCore_of_L34 hL (isLThreeFour_quot_center h34) hB1H hB1el hB1c
    · have hBN : B1 ≤ Subgroup.normalizer (L : Set G) :=
        hB1H.trans (S.le_normalizer_single hL haL hJ)
      rcases htype with ⟨hcat, -⟩ | hcat | ⟨hD4, hZ⟩
      · exact barX_le_glbCore_of_L364 hL hcat hB1el hB1c hBN
      · exact barX_le_glbCore_of_3D44 hgen3D4 hL hcat hB1el hB1c hBN
      · exact (S.false_of_D44 h h1111 h104v h111 hD44 h102 hL hJ hD4 hZ).elim
  · have h34 := S.triple_type c hJ
    have hL₂ : GLAPComponent 3 H (GLBConj a L) := Inputs1115.glaPComponent_conj_of_mem c.hM S.haH
    have hL₃ : GLAPComponent 3 H (GLBConj a (GLBConj a L)) :=
      Inputs1115.glaPComponent_conj_of_mem hL₂ S.haH
    rw [hJ, CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup (sup_le c.hM.1 hL₂.1) hL₃.1,
      CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup c.hM.1 hL₂.1]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact barX_le_glbCore_of_L34 c.hM h34 hB1H hB1el hB1c
    · exact barX_le_glbCore_of_L34 hL₂ (isLThreeFour_quot_center_conj a h34) hB1H hB1el hB1c
    · exact barX_le_glbCore_of_L34 hL₃
        (isLThreeFour_quot_center_conj a (isLThreeFour_quot_center_conj a h34)) hB1H hB1el hB1c

end GammaMain

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1115b

end
