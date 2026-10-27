module

public import CFSG.ClassicalInvolution.Asc77.AscSixAEmpty
public import CFSG.ClassicalInvolution.Asc77.WP1Section18

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

noncomputable def conjSylow (g : G) (S : Sylow 2 G) : Sylow 2 G := g • S

theorem coe_conjSylow (g : G) (S : Sylow 2 G) :
    ((conjSylow g S : Sylow 2 G) : Subgroup G) = conjSub g (S : Subgroup G) := by
  unfold conjSylow
  rw [Sylow.coe_subgroup_smul]
  ext x
  simp [conjSub, Subgroup.pointwise_smul_def]

theorem conjSub_iSup₂ {ι : Type*} (g : G) (A : ι → Subgroup G) (s : Set ι) :
    conjSub g (⨆ i ∈ s, A i) = ⨆ i ∈ s, conjSub g (A i) := by
  unfold conjSub
  rw [Subgroup.map_iSup]
  congr 1
  funext i
  rw [Subgroup.map_iSup]

theorem conjSub_top_eq_top (g : G) : conjSub g (⊤ : Subgroup G) = ⊤ := by
  ext x
  rw [mem_conjSub_iff]
  simp

section Eta

variable {Ω : Set (Subgroup G)} {p f : ℕ} [Fact p.Prime]

theorem conjSub_image_mem_etaSet (hΩ : ConjInvariant Ω) {S : Subgroup G} {η : Set (Subgroup G)}
    (h : η ∈ etaSet Ω S) (g : G) : conjSub g '' η ∈ etaSet Ω (conjSub g S) := by
  have hinj : Function.Injective (conjSub g : Subgroup G → Subgroup G) := conjSub_injective g
  refine ⟨?_, inDistinctMembers_image_conj hΩ h.2.1 g, fun η' hη' hd => ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨USet.conj hΩ (h.1 hU).1 g, conjSub_mono (h.1 hU).2⟩
  · rw [Set.ncard_image_of_injective _ hinj]
    exact ncard_le_of_mem_etaSet_conj hΩ rfl h hη' hd

theorem WSet.conj (hΩ : ConjInvariant Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) (g : G) :
    conjSub g W ∈ WSet Ω := by
  obtain ⟨η, ⟨S₁, hS₁, hinv⟩, rfl⟩ := hW
  refine ⟨conjSub g '' η, ⟨conjSylow g S₁, ?_, ?_⟩, ?_⟩
  · have := conjSub_image_mem_etaSet hΩ hS₁ g
    rwa [← coe_conjSylow] at this
  · intro s hs U hU
    rw [coe_conjSylow, mem_conjSub_iff] at hs
    obtain ⟨U₀, hU₀, rfl⟩ := hU
    refine ⟨conjSub (g⁻¹ * s * g) U₀, hinv _ hs U₀ hU₀, ?_⟩
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  · rw [conjSub_iSup₂, iSup_image]

end Eta

section Transport

variable {Ω : Set (Subgroup G)} {p f : ℕ} [Fact p.Prime]

theorem KPerp_conj (hΩ : ConjInvariant Ω) {K J : Subgroup G} (h : J ∈ KPerp Ω K) (g : G) :
    conjSub g J ∈ KPerp Ω (conjSub g K) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (omegaNbr_conj hΩ h g)

theorem CentralizersTwinPerp.conj (hΩ : ConjInvariant Ω) {K H : Subgroup G}
    (h : CentralizersTwinPerp Ω K H) (g : G) :
    CentralizersTwinPerp Ω (conjSub g K) (conjSub g H) := by
  intro L hL J hJ a haJ ha1 ha2
  have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
    have := twinSet_conj hΩ hL g⁻¹
    rwa [conjSub_inv_conjSub] at this
  have hJ' : conjSub g⁻¹ J ∈ KPerp Ω (conjSub g⁻¹ L) := KPerp_conj hΩ hJ g⁻¹
  have haJ' : g⁻¹ * a * g ∈ conjSub g⁻¹ L ⊔ conjSub g⁻¹ J := by
    have := conj_mem_conjSub (n := g⁻¹) haJ
    rwa [conjSub_sup, inv_inv] at this
  have ha1' : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have ha2' : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have hc := h _ hL' _ hJ' _ haJ' ha1' ha2'
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({g⁻¹ * a * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * (g⁻¹ * a * g) = g⁻¹ * (x * a) * g := by group
      _ = g⁻¹ * (a * x) * g := by rw [hx]
      _ = g⁻¹ * a * g * (g⁻¹ * x * g) := by group
  have := hc hx'
  rw [mem_conjSub_iff]
  exact this

theorem CentralizersSylowPairs.conj (hΩ : ConjInvariant Ω) {K H : Subgroup G}
    (h : CentralizersSylowPairs Ω K H) (g : G) :
    CentralizersSylowPairs Ω (conjSub g K) (conjSub g H) := by
  intro L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hcomm a haR ha1 ha2
  have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
    have := twinSet_conj hΩ hL g⁻¹
    rwa [conjSub_inv_conjSub] at this
  have hJ' : conjSub g⁻¹ J ∈ KPerp Ω (conjSub g⁻¹ L) := KPerp_conj hΩ hJ g⁻¹
  have hcomm' : Commutes (conjSub g⁻¹ R₁) (conjSub g⁻¹ R₂) ∨
      conjSub g⁻¹ R₂ = conjSub g⁻¹ R₁ := by
    rcases hcomm with h1 | h1
    · exact Or.inl (h1.conjSub g⁻¹)
    · exact Or.inr (by rw [h1])
  have haR' : g⁻¹ * a * g ∈ conjSub g⁻¹ R₁ ⊔ conjSub g⁻¹ R₂ := by
    have := conj_mem_conjSub (n := g⁻¹) haR
    rwa [conjSub_sup, inv_inv] at this
  have ha1' : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have ha2' : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have hc := h _ hL' _ hJ' _ _ (RSet.conj hΩ hR₁ g⁻¹) (conjSub_mono hR₁L)
    (RSet.conj hΩ hR₂ g⁻¹) (conjSub_mono hR₂J) hcomm' _ haR' ha1' ha2'
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({g⁻¹ * a * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * (g⁻¹ * a * g) = g⁻¹ * (x * a) * g := by group
      _ = g⁻¹ * (a * x) * g := by rw [hx]
      _ = g⁻¹ * a * g * (g⁻¹ * x * g) := by group
  have := hc hx'
  rw [mem_conjSub_iff]
  exact this

theorem EHyp.conj (hΩ : ConjInvariant Ω) {K W H : Subgroup G} (h : EHyp Ω K W H) (g : G) :
    EHyp Ω (conjSub g K) (conjSub g W) (conjSub g H) where
  trans := by
    intro J hJ
    have hJ' : conjSub g⁻¹ J ∈ dstarComp Ω K := by
      have := dstarComp_conj hΩ hJ g⁻¹
      rwa [conjSub_inv_conjSub] at this
    obtain ⟨h₀, hh₀, hh₀K⟩ := h.trans _ hJ'
    refine ⟨g * h₀ * g⁻¹, conj_mem_conjSub hh₀, ?_⟩
    rw [show g * h₀ * g⁻¹ = g * (h₀ * g⁻¹) by group, conjSub_mul, conjSub_mul,
      conjSub_inv_conjSub, hh₀K, conjSub_conjSub_inv]
  cent := h.cent.conj hΩ g


namespace E187C

variable {Ω : Set (Subgroup G)}

theorem twin_conj (hΩ : ConjInvariant Ω) {K : Subgroup G} {S : Sylow 2 G}
    (h : ∃ K' ∈ twinSet Ω K, K' ≠ K ∧ ∃ R' ∈ RSet Ω, R' ≤ K' ∧ R' ≤ (S : Subgroup G)) (g : G) :
    ∃ K' ∈ twinSet Ω (conjSub g K), K' ≠ conjSub g K ∧ ∃ R' ∈ RSet Ω, R' ≤ K' ∧
      R' ≤ (conjSylow g S : Subgroup G) := by
  obtain ⟨K', hK', hne, R', hR', hR'K', hR'S⟩ := h
  refine ⟨conjSub g K', twinSet_conj hΩ hK' g, fun h' => hne ((conjSub_inj g).mp h'),
    conjSub g R', RSet.conj hΩ hR' g, conjSub_mono hR'K', ?_⟩
  rw [coe_conjSylow]
  exact conjSub_mono hR'S

theorem hR_conj (hΩ : ConjInvariant Ω) {K R : Subgroup G} {S : Sylow 2 G}
    (h : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)) (g : G) :
    conjSub g R ∈ RSet Ω ∧ conjSub g R ≤ conjSub g K ∧
      conjSub g R ≤ (conjSylow g S : Subgroup G) := by
  obtain ⟨hR, hRK, hRS⟩ := h
  refine ⟨RSet.conj hΩ hR g, conjSub_mono hRK, ?_⟩
  rw [coe_conjSylow]
  exact conjSub_mono hRS

theorem hW_conj (hΩ : ConjInvariant Ω) {W : Subgroup G} {S : Sylow 2 G}
    (h : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W) (g : G) :
    conjSub g W ∈ WSet Ω ∧ conjSub g W ≤ (conjSylow g S : Subgroup G) ∧
      ∀ s ∈ (conjSylow g S : Subgroup G), conjSub s (conjSub g W) = conjSub g W := by
  obtain ⟨hW, hWS, hWn⟩ := h
  refine ⟨WSet.conj hΩ hW g, ?_, ?_⟩
  · rw [coe_conjSylow]
    exact conjSub_mono hWS
  · intro s hs
    rw [coe_conjSylow, mem_conjSub_iff] at hs
    have := hWn _ hs
    calc conjSub s (conjSub g W) = conjSub g (conjSub (g⁻¹ * s * g) W) := by
          rw [← conjSub_mul, ← conjSub_mul]
          congr 1
          group
      _ = conjSub g W := by rw [this]

theorem conjSub_ne_top {H : Subgroup G} (hH : H ≠ ⊤) (g : G) : conjSub g H ≠ ⊤ := by
  intro h
  apply hH
  have := congrArg (conjSub g⁻¹) h
  rwa [conjSub_inv_conjSub, conjSub_top_eq_top] at this


theorem center_eq_bot_of_centralizer_eq_bot {F : Subgroup G}
    (hF : Subgroup.centralizer (F : Set G) = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact (Subgroup.mem_center_iff.mp hx y)
  rw [hF] at this
  exact this

theorem centralizer_singleton_ne_top (hZ : Subgroup.center G = ⊥) {x : G} (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
  intro h
  apply hx
  have hc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have : y ∈ Subgroup.centralizer ({x} : Set G) := by rw [h]; exact Subgroup.mem_top y
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rw [hZ] at hc
  exact Subgroup.mem_bot.mp hc


theorem exists_sylow_inf_centralizer [Finite G] {R R' A : Subgroup G} {S : Sylow 2 G}
    (hRS : R ≤ (S : Subgroup G)) (hR'S : R' ≤ (S : Subgroup G))
    (hRA : R ⊔ R' ≤ Subgroup.centralizer (A : Set G)) :
    ∃ S' : Sylow 2 G, R ≤ (S' : Subgroup G) ∧ R' ≤ (S' : Subgroup G) ∧
      IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer (A : Set G))
        (Subgroup.centralizer (A : Set G)) := by
  have hRR' : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  obtain ⟨P, hP, hRRP⟩ := IsSylow2In.exists_ge hRR' hRA
  obtain ⟨S', hPS'⟩ := IsPGroup.exists_le_sylow hP.2.1
  refine ⟨S', le_sup_left.trans (hRRP.trans hPS'), le_sup_right.trans (hRRP.trans hPS'), ?_⟩
  have hle : P ≤ (S' : Subgroup G) ⊓ Subgroup.centralizer (A : Set G) := le_inf hPS' hP.1
  have hp2 : IsPGroup 2 ↥((S' : Subgroup G) ⊓ Subgroup.centralizer (A : Set G)) :=
    S'.isPGroup'.to_le inf_le_left
  have heq := hP.eq_of_le hp2 inf_le_right hle
  rw [heq]
  exact hP

end E187C

end Transport

section MinCexConj

variable {Ω : Set (Subgroup G)} {p f : ℕ} [Fact p.Prime] [Finite G]

set_option linter.unusedSectionVars false in
theorem EStand.conj {K R W : Subgroup G} {S : Sylow 2 G} (h : EStand p f Ω K S R W) (g : G) :
    EStand p f Ω (conjSub g K) (conjSylow g S) (conjSub g R) (conjSub g W) where
  odd := h.odd
  five := h.five
  hyp := h.hyp
  below := h.below
  mem := h.hyp.conjInvariant g K h.mem
  aEmpty := aEmpty_conj h.hyp.conjInvariant h.aEmpty g
  twin := E187C.twin_conj h.hyp.conjInvariant h.twin g
  hR := E187C.hR_conj h.hyp.conjInvariant h.hR g
  hW := E187C.hW_conj h.hyp.conjInvariant h.hW g

theorem MinCex.conj {K R W H : Subgroup G} {S : Sylow 2 G} (c : MinCex p f Ω K S R W H)
    (g : G) : MinCex p f Ω (conjSub g K) (conjSylow g S) (conjSub g R) (conjSub g W)
      (conjSub g H) where
  stand := c.stand.conj g
  hyp := c.hyp.conj c.stand.hyp.conjInvariant g
  proper := E187C.conjSub_ne_top c.proper g
  minimal := c.minimal

end MinCexConj

end CFSG.ClassicalInvolution.Asc77
