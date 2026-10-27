module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBCenter
public import CFSG.LocalAnalysis.AGLEmbedding.D1CompCore
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.Quasithin.Background.A1cRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

section Reduced

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.isCyclic_of_le_sup_of_inf_eq_bot
    (h : ReducedNongeneration p Y Rb Y₀) {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L₂ : Subgroup Y)) {A : Subgroup Y}
    (hAR : A ≤ Rb) (hAL : A ≤ L₁ ⊔ L₂) (hA₁ : A ⊓ L₁ = ⊥) : IsCyclic A := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hZ := h.center_eq_bot_of_isCyclic h₂ hcyc
  have hN : A ≤ Subgroup.normalizer (L₂ : Set Y) :=
    hAR.trans (h.sylow_le_normalizer_component h₂)
  have h₁₂ : L₁ ≤ Subgroup.centralizer (L₂ : Set Y) := le_centralizer_of_component_ne h₁ h₂ hne
  have hmul : ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) = (L₁ : Set Y) * (L₂ : Set Y) :=
    Subgroup.coe_mul_of_left_le_normalizer_right L₁ L₂
      (h₁₂.trans (Subgroup.centralizer_le_normalizer _))
  have hdec : ∀ a ∈ A, ∃ l₁ ∈ L₁, ∃ l₂ ∈ L₂, a = l₁ * l₂ := by
    intro a ha
    have : a ∈ ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) := hAL ha
    rw [hmul] at this
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Set.mem_mul.mp this
    exact ⟨l₁, hl₁, l₂, hl₂, rfl⟩
  have hfa : ∀ (a : A) (n : L₂), ((conjAut hN a n : L₂) : Y) = a * n * (a : Y)⁻¹ :=
    fun a n => by rw [conjAut_apply_coe, Subgroup.coe_inv]
  have hinner : ∀ a : A, ∃ l : L₂, conjAut hN a = MulAut.conj l := by
    intro a
    obtain ⟨l₁, hl₁, l₂, hl₂, ha⟩ := hdec a a.2
    refine ⟨⟨l₂, hl₂⟩, MulEquiv.ext fun n => Subtype.ext ?_⟩
    rw [hfa, MulAut.conj_apply]
    have hc : l₁ * (l₂ * n * l₂⁻¹) = (l₂ * n * l₂⁻¹) * l₁ :=
      (Subgroup.mem_centralizer_iff.mp (h₁₂ hl₁) _
        (L₂.mul_mem (L₂.mul_mem hl₂ n.2) (L₂.inv_mem hl₂))).symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ha]
    calc l₁ * l₂ * (n : Y) * (l₁ * l₂)⁻¹ = l₁ * (l₂ * n * l₂⁻¹) * l₁⁻¹ := by group
      _ = l₂ * n * l₂⁻¹ := by rw [hc]; group
  have hinj : Function.Injective (conjAut hN) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨l₁, hl₁, l₂, hl₂, hal⟩ := hdec a a.2
    have haC : ∀ n ∈ L₂, (a : Y) * n * (a : Y)⁻¹ = n := fun n hn => by
      have := congrArg (fun g : MulAut L₂ => ((g ⟨n, hn⟩ : L₂) : Y)) ha
      simpa only [hfa, MulAut.one_apply] using this
    have hl₂Z : (⟨l₂, hl₂⟩ : L₂) ∈ Subgroup.center L₂ := by
      rw [Subgroup.mem_center_iff]
      intro n
      apply Subtype.ext
      have h2 : (n : Y) * l₁ = l₁ * n := Subgroup.mem_centralizer_iff.mp (h₁₂ hl₁) n n.2
      have key : l₂ * (n : Y) * l₂⁻¹ = n := by
        have e : l₂ * (n : Y) * l₂⁻¹ = l₁⁻¹ * ((a : Y) * n * (a : Y)⁻¹) * l₁ := by
          rw [hal]; group
        rw [e, haC n n.2]
        calc l₁⁻¹ * (n : Y) * l₁ = l₁⁻¹ * ((n : Y) * l₁) := by group
          _ = l₁⁻¹ * (l₁ * n) := by rw [h2]
          _ = n := by group
      simp only [Subgroup.coe_mul]
      calc (n : Y) * l₂ = l₂ * n * l₂⁻¹ * l₂ := by rw [key]
        _ = l₂ * n := by group
    rw [hZ, Subgroup.mem_bot] at hl₂Z
    have hl₂1 : l₂ = 1 := congrArg Subtype.val hl₂Z
    have haL : (a : Y) ∈ A ⊓ L₁ := ⟨a.2, by rw [hal, hl₂1, mul_one]; exact hl₁⟩
    rw [hA₁, Subgroup.mem_bot] at haL
    exact Subtype.ext haL
  have hconj : Function.Injective (MulAut.conj : L₂ →* MulAut L₂) := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have hlZ : l ∈ Subgroup.center L₂ := by
      rw [Subgroup.mem_center_iff]
      intro n
      have := congrArg (fun g : MulAut L₂ => g n) hl
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc n * l = l * n * l⁻¹ * l := by rw [this]
        _ = l * n := by group
    rw [hZ, Subgroup.mem_bot] at hlZ
    exact hlZ
  have hrange : (conjAut hN).range ≤ (MulAut.conj : L₂ →* MulAut L₂).range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨l, hl⟩ := hinner a
    exact ⟨l, hl.symm⟩
  set B : Subgroup L₂ := (conjAut hN).range.comap (MulAut.conj : L₂ →* MulAut L₂) with hB
  have hAp : IsPGroup p A := Rb.isPGroup'.to_le hAR
  have hfp : IsPGroup p (conjAut hN).range :=
    hAp.of_surjective (conjAut hN).rangeRestrict (conjAut hN).rangeRestrict_surjective
  have hBp : IsPGroup p B := hfp.of_injective
    (((MulAut.conj : L₂ →* MulAut L₂).comp B.subtype).codRestrict (conjAut hN).range
      fun b => b.2)
    (fun b c hbc => Subtype.ext (hconj (congrArg Subtype.val hbc)))
  obtain ⟨P₂, hP₂⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (ComponentClassification.Components.mathlib_subnormal_of_chain h₂.2.1
      Subgroup.IsSubnormal.top)
  have hP₂c : IsCyclic (P₂ : Subgroup L₂) := by
    rw [← hP₂] at hcyc
    exact isCyclic_of_surjective (Subgroup.equivMapOfInjective _ _ L₂.subtype_injective).symm
      (MulEquiv.surjective _)
  obtain ⟨Q, hBQ⟩ := hBp.exists_le_sylow
  have hQc : IsCyclic (Q : Subgroup L₂) :=
    isCyclic_of_surjective (Sylow.equiv P₂ Q).toMonoidHom (Sylow.equiv P₂ Q).surjective
  have hBc : IsCyclic B := Subgroup.isCyclic_of_le hBQ
  have hBmap : B.map (MulAut.conj : L₂ →* MulAut L₂) = (conjAut hN).range :=
    Subgroup.map_comap_eq_self hrange
  have hfc : IsCyclic (conjAut hN).range := hBmap ▸ isCyclic_of_surjective _
    ((MulAut.conj : L₂ →* MulAut L₂).subgroupMap_surjective B)
  exact isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom
    (MulEquiv.surjective _)

end Reduced

section Escape

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}

theorem D1CompCore.exists_component_le_of_escape (hd : D1CompCore p P M H R Rbar K)
    (hkP : CFSG.Open.IsKProper G) {M'' : Subgroup G} (hesc : D1Escape p P' M'' H₁ S)
    (hJH₁ : nclIn H (d1LiftX p H R K) ≤ H₁) (hXS : d1LiftX p H R K ≤ S)
    (hSch : KFactCatalogSchreier) (hcon : ¬ HasPrimeConstraint (G := H₁) p) :
    ∃ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L ⊤ ∧ L.Normal ∧
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L := by
  have hp := hesc.prime
  have : Fact p.Prime := ⟨hp⟩
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  set X := d1LiftX p H R K with hXdef
  set J := nclIn H X with hJdef
  set Jt := (J.subgroupOf H₁).map π₁ with hJt
  set Xt := (X.subgroupOf H₁).map π₁ with hXt
  set St := (S.subgroupOf H₁).map π₁ with hSt
  obtain ⟨Rb₁, hRb₁, hred₁, hX₁, -, htwo₁, -, -, K₁, hK₁, -, -⟩ :=
    hesc.exists_reducedNongeneration_of_not_hasPrimeConstraint hkP hcon
  have hRbS : (Rb₁ : Subgroup _) = St := hRb₁
  have hXH₁ : X ≤ H₁ := ((le_nclIn (d1LiftX_le_H p H R K)).trans hJH₁)
  have hXp : IsPGroup p X := hd.esc.isPGroup.to_le (d1LiftX_le p H R K)
  have hXtp : IsPGroup p Xt := hXp.comap_subtype.map _
  have hXtJt : Xt ≤ Jt := Subgroup.map_mono (Subgroup.comap_mono (le_nclIn (d1LiftX_le_H p H R K)))
  have hXtS : Xt ≤ St := Subgroup.map_mono (Subgroup.comap_mono hXS)
  have hXt1 : Xt ≠ ⊥ := map_mk_ne_bot_of_isPGroup hp hXH₁ hXp hd.d1LiftX_ne_bot
  have hXtnc : ¬ IsCyclic Xt := hd.not_isCyclic_map hXH₁
  have hncl : nclIn Jt Xt = Jt :=
    nclIn_map_eq π₁ (le_nclIn (d1LiftX_le_H p H R K)) hJH₁ hd.nclIn_nclIn
  obtain ⟨φ, hφs, hφk, -⟩ :=
    exists_competitorHom_apply_of_map_eq (hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot) hJH₁
  obtain ⟨hKs, hKnab⟩ := hd.isSimpleGroup
  have hJN : ∀ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L ⊤ →
      Jt ≤ Subgroup.normalizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) := by
    intro L hL
    rw [← hncl]
    exact nclIn_le_of_forall_conj_mem fun c _ x hx =>
      hred₁.conj_mem_normalizer_component hL (hRbS ▸ hXtS hx) c
  have hJperf := isPerfect_of_nclIn_eq hKs hKnab hXtp hncl φ hφs hφk
  have hJE := hred₁.le_layer_of_isPerfect hX₁ hSch hK₁ hJperf hJN
  have hdich : ∀ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L ⊤ →
      Jt ≤ L ∨ Xt ⊓ L = ⊥ := by
    intro L hL
    have hn : ((L ⊓ Jt).subgroupOf Jt).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
        ((le_inf (hJN L hL) Subgroup.le_normalizer).trans
          Subgroup.inf_normalizer_le_normalizer_inf)
    rcases eq_top_or_le_ker_of_nclIn_eq hKs hXtp hncl φ hφs hφk ((L ⊓ Jt).subgroupOf Jt) with
      htop | hker
    · exact Or.inl ((Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left)
    · refine Or.inr (eq_bot_iff.mpr fun x hx => ?_)
      have hbot : Xt.subgroupOf Jt ⊓ φ.ker = ⊥ :=
        inf_eq_bot_of_isPGroup hp (hXtp.comap_subtype (K := Jt)) hφk
      have hmem : (⟨x, hXtJt hx.1⟩ : Jt) ∈ Xt.subgroupOf Jt ⊓ φ.ker :=
        ⟨Subgroup.mem_subgroupOf.mpr hx.1, hker (Subgroup.mem_subgroupOf.mpr ⟨hx.2, hXtJt hx.1⟩)⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  have hex : ∃ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L ⊤ ∧
      Jt ≤ L := by
    by_contra hno
    push Not at hno
    have hXL : ∀ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L ⊤ →
        Xt ⊓ L = ⊥ := fun L hL => (hdich L hL).resolve_left (hno L hL)
    have hXE : Xt ≤ CFSG.layer (H₁ ⧸ primeComplementCore (G := H₁) p) := hXtJt.trans hJE
    by_cases h2 : ∃ L₂ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L₂ ⊤ ∧
        L₂ ≠ K₁
    · obtain ⟨L₂, hL₂, hne⟩ := h2
      have hE : CFSG.layer (H₁ ⧸ primeComplementCore (G := H₁) p) ≤ K₁ ⊔ L₂ := by
        refine sSup_le fun L' hL' => ?_
        rcases hred₁.eq_or_eq_of_isComponentOf hK₁ hL₂ hne.symm
          ((CFSG.isComponent_iff_open L').mp hL') with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      have hXR : Xt ≤ Rb₁ := hRbS ▸ hXtS
      by_cases hc₂ : IsCyclic ((Rb₁ : Subgroup _) ⊓ L₂ : Subgroup _)
      · exact hXtnc (hred₁.isCyclic_of_le_sup_of_inf_eq_bot hK₁ hL₂ hne.symm hc₂ hXR
          (hXE.trans hE) (hXL K₁ hK₁))
      · have hc₁ : IsCyclic ((Rb₁ : Subgroup _) ⊓ K₁ : Subgroup _) := by
          by_contra hc₁
          exact hne (htwo₁ L₂ K₁ hL₂ hK₁
            (two_le_pRank_of_isPGroup_not_isCyclic hp hesc.ne_two
              (Rb₁.isPGroup'.to_le inf_le_left) hc₂)
            (two_le_pRank_of_isPGroup_not_isCyclic hp hesc.ne_two
              (Rb₁.isPGroup'.to_le inf_le_left) hc₁))
        exact hXtnc (hred₁.isCyclic_of_le_sup_of_inf_eq_bot hL₂ hK₁ hne hc₁ hXR
          (hXE.trans (hE.trans (sup_comm K₁ L₂).le)) (hXL L₂ hL₂))
    · push Not at h2
      have hE : CFSG.layer (H₁ ⧸ primeComplementCore (G := H₁) p) ≤ K₁ :=
        sSup_le fun L' hL' => (h2 L' ((CFSG.isComponent_iff_open L').mp hL')).le
      apply hXt1
      rw [← inf_eq_left.mpr (hXE.trans hE)]
      exact hXL K₁ hK₁
  obtain ⟨L, hL, hJL⟩ := hex
  have hnc : ¬ IsCyclic ((Rb₁ : Subgroup _) ⊓ L : Subgroup _) := fun hcyc =>
    hXtnc (Subgroup.isCyclic_of_le (le_inf (hRbS ▸ hXtS) (hXtJt.trans hJL)))
  exact ⟨L, hL, hred₁.normal_of_rankOne hL hnc, hJL⟩

end Escape

namespace D1OneLieCompetitorData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {R₁ : Subgroup G} {P' : Sylow p G}
  {H₁ S : Subgroup G}

theorem exists_normal_component (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    (hSch : KFactCatalogSchreier) :
    ∃ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L ⊤ ∧ L.Normal ∧
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L ∧
      Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) = ⊥ ∧
      ∀ L' : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L' ⊤ → L' = L := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  set St := (S.subgroupOf H₁).map π₁ with hSt
  obtain ⟨Rb₁, hRb₁, hred₁, -⟩ :=
    hc.escape.exists_reducedNongeneration_of_not_hasPrimeConstraint hd.cfg.glob.kProper
      hc.not_hasPrimeConstraint
  have hRbS : (Rb₁ : Subgroup _) = St := hRb₁
  have hStp : IsPGroup p St := hRbS ▸ Rb₁.isPGroup'
  obtain ⟨L, hL, -, hJL⟩ := hd.toCore.exists_component_le_of_escape hd.cfg.glob.kProper hc.escape
    hc.nclIn_le (hc.liftX_le.trans hc.le_S) hSch hc.not_hasPrimeConstraint
  have hSL : St ≤ Subgroup.normalizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) :=
    hRbS ▸ hred₁.sylow_le_normalizer_component hL
  have hSC : St ⊓ Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) = ⊥ := by
    by_contra hne
    have hSA : St ≤ Subgroup.normalizer ((St ⊓ Subgroup.centralizer
        (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) : Subgroup _) : Set _) :=
      (le_inf Subgroup.le_normalizer (hSL.trans
        (RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer L))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    obtain ⟨b, ⟨hbS, hbL⟩, hbC, hbp⟩ :=
      exists_mem_inf_centralizer_orderOf_eq hStp inf_le_left hSA hne
    exact hc.false_of_mem_center hbS hbC hbp (Subgroup.centralizer_le hJL hbL)
  have hLn : L.Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun y _ =>
      mem_normalizer_of_conj_map_le ?_)
    by_contra hle
    have hL' : IsComponentOf (L.map (MulAut.conj y).toMonoidHom) ⊤ :=
      (CFSG.isComponent_iff_open _).mp (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y)
        ((CFSG.isComponent_iff_open L).mpr hL))
    have hne : L.map (MulAut.conj y).toMonoidHom ≠ L := fun h => hle h.le
    obtain ⟨t, ⟨htR, htL'⟩, htp, -⟩ :=
      exists_mem_sylow_inf_component hp hc.escape.ne_two hred₁.core_eq_bot Rb₁ hL'
    have ht : t ∈ St ⊓ Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) :=
      ⟨hRbS ▸ htR, le_centralizer_of_component_ne hL' hL hne htL'⟩
    rw [hSC, Subgroup.mem_bot] at ht
    rw [ht, orderOf_one] at htp
    exact hp.one_lt.ne htp
  have hCL : Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) = ⊥ := by
    have hcop : p.Coprime (Nat.card (Subgroup.centralizer
        (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)))) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      obtain ⟨c, hcp⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hcz : IsPGroup p (Subgroup.zpowers (c : H₁ ⧸ primeComplementCore (G := H₁) p)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hcp, pow_one])
      obtain ⟨Q, hQ⟩ := hcz.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
        (H₁ ⧸ primeComplementCore (G := H₁) p) Rb₁ Q
      have hcQ : (c : H₁ ⧸ primeComplementCore (G := H₁) p) ∈ (Q : Subgroup _) :=
        hQ (Subgroup.mem_zpowers _)
      rw [← hg, coe_smul_sylow_eq_map_conj] at hcQ
      obtain ⟨x, hxR, hxc⟩ := hcQ
      have hxC : x ∈ Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) := by
        have := (inferInstance : (Subgroup.centralizer
          (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p))).Normal).conj_mem _ c.2 g⁻¹
        have e : x = g⁻¹ * (c : H₁ ⧸ primeComplementCore (G := H₁) p) * g⁻¹⁻¹ := by
          rw [← hxc]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact this
      have hx1 : x ∈ St ⊓ Subgroup.centralizer
          (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) := ⟨hRbS ▸ hxR, hxC⟩
      rw [hSC, Subgroup.mem_bot] at hx1
      have hc1 : (c : H₁ ⧸ primeComplementCore (G := H₁) p) = 1 := by
        rw [← hxc, hx1, map_one]
      rw [show c = 1 from Subtype.ext hc1, orderOf_one] at hcp
      exact hp.one_lt.ne hcp
    exact le_bot_iff.mp (hred₁.core_eq_bot ▸
      normal_coprime_le_primeComplementCore p _ inferInstance hcop)
  refine ⟨L, hL, hLn, hJL, hCL, fun L' hL' => ?_⟩
  by_contra hne
  have hL'C := le_centralizer_of_component_ne hL' hL hne
  rw [hCL] at hL'C
  obtain ⟨t, ⟨-, htL'⟩, htp, -⟩ :=
    exists_mem_sylow_inf_component hp hc.escape.ne_two hred₁.core_eq_bot Rb₁ hL'
  rw [Subgroup.mem_bot.mp (hL'C htL'), orderOf_one] at htp
  exact hp.one_lt.ne htp

end D1OneLieCompetitorData

end CFSG.AGLEmbedding
