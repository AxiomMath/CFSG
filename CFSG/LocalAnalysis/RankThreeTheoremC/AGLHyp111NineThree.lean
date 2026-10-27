module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111DataBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ADefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAZNAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoTheoremZAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem factor_of_compCore (hd : D1CompCore p P M H R Rbar K) :
    ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H, QuotientGroup.mk' (primeComplementCore (G := H) p) k ∈ K ∧
      x = m * k := by
  have : Fact p.Prime := ⟨hd.red.prime⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hKn : K.Normal := hd.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨T₁, hT₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hd.comp.2.1
      Subgroup.IsSubnormal.top)
  have htop := Sylow.normalizer_sup_eq_top T₁
  rw [hT₁] at htop
  obtain ⟨zb, hzbR, hzbK, hzbp, hzbc⟩ := hd.z
  have hN := hd.red.normalizer_inf_le_of_rankOne hd.noncyclic hzbR hzbK hzbp hzbc
  intro x hx
  have hmem : π ⟨x, hx⟩ ∈ Subgroup.normalizer
      (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) p)) ⊔ K := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨ν, hν, k, hk, hνk⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  obtain ⟨m, hm, rfl⟩ := hN hν
  obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := H) p) k
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
  have h1 : π (m⁻¹ * ⟨x, hx⟩ * k'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, ← hνk, hπ]; group
  have hoM : ((m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : H) : G) ∈ M :=
    hd.esc.primeCore_le ((mk'_primeComplementCore_eq_one_iff p _).mp h1)
  refine ⟨(m : G) * ((m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : H) : G),
    ⟨H.mul_mem m.2 (m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : H).2, M.mul_mem hmM hoM⟩, k', hk, ?_⟩
  simp [mul_assoc]

theorem nineThree_of_compCore (hd : D1CompCore p P M H R Rbar K) : Hyp111NineThree p M H K :=
  ⟨hd.red.normal_of_rankOne hd.comp hd.noncyclic, hd.d1PlusCore_facts.1.trans inf_le_right,
    factor_of_compCore hd⟩

theorem nineThree_of_oneSmall3 (hd : D1OneSmall3Data p P M H R Rbar K) :
    Hyp111NineThree p M H K :=
  nineThree_of_compCore hd.toCore

theorem le_of_not_le_compCore (hd : D1CompCore p P M H R Rbar K)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) : L ≤ K := by
  by_contra hLK
  have hne : L ≠ K := fun h => hLK h.le
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  exact hLX ((le_centralizer_of_component_ne hL hd.comp hne).trans
    (hd.red.centralizer_le_of_rankOne hd.noncyclic hzR hzK hzp hzc))

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.normalizer_inf_le_of_pCore (h : ReducedNongeneration p Y Rb Y₀)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {z : Y} (hz : z ∈ CFSG.pCore p Y) (hzp : orderOf z = p) :
    Subgroup.normalizer (((Rb : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) ≤ Y₀ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have : IsCyclic (CFSG.pCore p Y) := h.isCyclic_pCore_of_component hL
  obtain ⟨t, ⟨htR, htL⟩, ht, -⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb hL
  have hzC : z ∈ Subgroup.centralizer (L : Set Y) := h.pCore_le_centralizer hL hz
  have hzt : z ∉ Subgroup.zpowers t := by
    intro hzt
    have hz1 := h.eq_one_of_mem_centralizer_of_isCyclic hL hcyc (Subgroup.zpowers_le.mpr htL hzt)
      hzC
    rw [hz1, orderOf_one] at hzp
    exact hp.one_lt.ne hzp
  have hzconj : ∀ g : Y, g * z * g⁻¹ ∈ Subgroup.zpowers z := fun g =>
    conj_mem_zpowers_of_isCyclic rfl hz (‹(CFSG.pCore p Y).Normal›.conj_mem z hz g)
  have hQR : Subgroup.zpowers t ⊔ Subgroup.zpowers z ≤ Rb :=
    sup_le (Subgroup.zpowers_le.mpr htR)
      (Subgroup.zpowers_le.mpr (CFSG.pCore_isPGroup.le_sylow_of_normal Rb hz))
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers t ⊔ Subgroup.zpowers z) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp ht (hzp ▸ pow_orderOf_eq_one z) hzt
      (Subgroup.mem_centralizer_iff.mp hzC t htL)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hC := h.three_le_pRank_inf_centralizer_sup_zpowers ht hzp
    (fun v hv => h.conj_mem_zpowers_of_component hL hcyc ⟨htR, htL⟩ hv) fun v _ => hzconj v
  have hNQ : Subgroup.normalizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers z : Subgroup Y) : Set Y) ≤ Y₀ :=
    (normalizer_le_weakCore p hQR hQ2 (hC.trans (pRank_mono p hp le_sup_right))).trans
      h.weakCore_le
  intro g hg
  have hgt : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
    conj_mem_zpowers_of_isCyclic (T := (Rb : Subgroup Y) ⊓ L) rfl ⟨htR, htL⟩
      ((Subgroup.mem_normalizer_iff.mp hg t).mp ⟨htR, htL⟩)
  exact hNQ (mem_normalizer_sup_zpowers (Subgroup.mem_sup_left hgt)
    (Subgroup.mem_sup_right (hzconj g)))

end CFSG.AGLEmbedding

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem plusCore_le_of_centralizer_le (he : D1Escape p P M H R)
    {J : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hC : Subgroup.centralizer (J : Set (H ⧸ primeComplementCore (G := H) p)) ≤ d1X0 p M H) :
    d1PlusCore p H J ≤ M := by
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨m, hm, hmh⟩ := hC hh
  have h1 : QuotientGroup.mk' (primeComplementCore (G := H) p) (m⁻¹ * h) = 1 := by
    rw [map_mul, map_inv, hmh, inv_mul_cancel]
  have hoM : ((m⁻¹ * h : H) : G) ∈ M :=
    he.primeCore_le ((mk'_primeComplementCore_eq_one_iff p _).mp h1)
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
  have e : (h : G) = (m : G) * ((m⁻¹ * h : H) : G) := by simp
  rw [Subgroup.coe_subtype, e]
  exact M.mul_mem hmM hoM

theorem factor_of_top_le (he : D1Escape p P M H R)
    {J : Subgroup (H ⧸ primeComplementCore (G := H) p)} [J.Normal]
    (htop : (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ d1X0 p M H ⊔ J) :
    ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H, QuotientGroup.mk' (primeComplementCore (G := H) p) k ∈ J ∧
      x = m * k := by
  intro x hx
  have hmem := htop (Subgroup.mem_top (QuotientGroup.mk' (primeComplementCore (G := H) p)
    ⟨x, hx⟩))
  obtain ⟨ν, hν, k, hk, hνk⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  obtain ⟨m, hm, rfl⟩ := hν
  obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := H) p) k
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
  have h1 : QuotientGroup.mk' (primeComplementCore (G := H) p) (m⁻¹ * ⟨x, hx⟩ * k'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, ← hνk]; group
  have hoM : ((m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : H) : G) ∈ M :=
    he.primeCore_le ((mk'_primeComplementCore_eq_one_iff p _).mp h1)
  refine ⟨(m : G) * ((m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : H) : G),
    ⟨H.mul_mem m.2 (m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : H).2, M.mul_mem hmM hoM⟩, k', hk, ?_⟩
  simp [mul_assoc]

theorem layer_le_sup_of_two (hd : D1CaseTwoData3 p P M H R Rbar)
    {L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂) :
    CFSG.layer (H ⧸ primeComplementCore (G := H) p) ≤ L₁ ⊔ L₂ := by
  refine sSup_le fun L hL => ?_
  rcases hd.cfg.red.eq_or_eq_of_isComponentOf h₁ h₂ hne ((CFSG.isComponent_iff_open L).mp hL)
    with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem nineThree_of_caseTwo_mixed (hd : D1CaseTwoData3 p P M H R Rbar)
    {L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (hL₁ : ¬ L₁ ≤ d1X0 p M H) (hL₂ : L₂ ≤ d1X0 p M H) :
    Hyp111NineThree p M H L₁ := by
  have he := hd.cfg.ext.toD1Escape
  have hne : L₁ ≠ L₂ := fun heq => hL₁ (heq ▸ hL₂)
  have hn := (hd.cfg.red.normal_of_two_components hd.cyclic h₁ h₂ hL₁ hL₂).1
  refine ⟨hn, plusCore_le_of_centralizer_le he
    (hd.cfg.red.centralizer_le_of_not_le hd.cyclic h₁ h₂ hL₁ hL₂), factor_of_top_le he ?_⟩
  refine (hd.cfg.red.top_le_sup_layer hd.cyclic h₁ h₂ hne).trans (sup_le le_sup_left ?_)
  refine (layer_le_sup_of_two hd h₁ h₂ hne).trans (sup_le le_sup_right ?_)
  exact hL₂.trans le_sup_left

theorem nineThree_of_caseTwo_unique (hd : D1CaseTwoData3 p P M H R Rbar)
    (hA : CycAutRankLeTwo p (H ⧸ primeComplementCore (G := H) p) Rbar)
    {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h₁ : IsComponentOf L₁ ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁) :
    Hyp111NineThree p M H L₁ := by
  have he := hd.cfg.ext.toD1Escape
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hO := hd.cfg.red.pCore_ne_bot_of_unique_of_aut hA hd.cyclic hd.rank h₁ huniq
  obtain ⟨z, hz, hzp⟩ : ∃ z ∈ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p),
      orderOf z = p := by
    obtain ⟨z, hz⟩ : ∃ x : CFSG.pCore p (H ⧸ primeComplementCore (G := H) p),
        orderOf x = p := by
      rcases (CFSG.pCore_isPGroup (p := p)
          (G := H ⧸ primeComplementCore (G := H) p)).card_eq_or_dvd with h1 | hdvd
      · exact absurd (Subgroup.card_eq_one.mp h1) hO
      · exact exists_prime_orderOf_dvd_card' p hdvd
    exact ⟨z, z.2, (Subgroup.orderOf_coe z).trans hz⟩
  have hn : L₁.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hL : IsComponentOf (L₁.map (MulAut.conj g).toMonoidHom) ⊤ :=
      (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L₁).mpr h₁
    rw [← huniq _ hL]
    exact ⟨n, hn, rfl⟩
  refine ⟨hn, plusCore_le_of_centralizer_le he
    (hd.cfg.red.centralizer_le_of_pCore h₁ (hd.cyclic L₁ h₁) hz hzp), factor_of_top_le he ?_⟩
  obtain ⟨T₁, hT₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (Subgroup.Normal.isSubnormal hn)
  have htop := Sylow.normalizer_sup_eq_top T₁
  rw [hT₁] at htop
  rw [← htop]
  exact sup_le_sup_right (hd.cfg.red.normalizer_inf_le_of_pCore h₁ (hd.cyclic L₁ h₁) hz hzp) _

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
