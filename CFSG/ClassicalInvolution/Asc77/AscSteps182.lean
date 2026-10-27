module

public import CFSG.ClassicalInvolution.Asc77.AscSteps181
public import CFSG.ClassicalInvolution.Asc77.AscSteps183
public import CFSG.ClassicalInvolution.Asc77.AscSix611
public import CFSG.ClassicalInvolution.Asc77.AscSixAEmpty

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

private theorem orderOf_conj_mul_inv (g u : G) : orderOf (g * u * g⁻¹) = orderOf u := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) u
  simpa [MulAut.conj_apply] using this

theorem HypOmegaMod.isSylow2In_of_mem_RSet_of_le [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K) : IsSylow2In R K := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  have hJK : K = J := hΩ.eq_of_le_of_le hK hJ hRJ.2.1 (by omega) hRK hRJ.1
  exact hJK ▸ hRJ

theorem E187C.mem_dstarComp_of_mem_USet_le_W_of [Finite G]
    (hzK0 : ∀ {K : Subgroup G}, K ∈ Ω → ∃ z : G, IsUniqueInvolution K z)
    (h4U : ∀ {U : Subgroup G}, U ∈ USet Ω → 4 ≤ Nat.card U)
    (h2U : ∀ {U : Subgroup G}, U ∈ USet Ω → IsPGroup 2 U)
    (hnorm : ∀ {K J : Subgroup G} {z : G} {A : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J →
      IsUniqueInvolution K z → A ≤ J → IsPGroup 2 A → 3 ≤ Nat.card A →
        A ≤ Subgroup.centralizer ({z} : Set G) → A ≤ Subgroup.normalizer (K : Set G))
    {K J W V₀ V₁ : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hV₀ : V₀ ∈ USet Ω) (hV₀K : V₀ ≤ K) (hV₀W : V₀ ≤ W) (hV₁ : V₁ ∈ USet Ω) (hV₁J : V₁ ≤ J)
    (hV₁W : V₁ ≤ W) (habel : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : J ∈ dstarComp Ω K := by
  by_cases hJK : J = K
  · rw [hJK]
    exact Relation.ReflTransGen.refl
  obtain ⟨z, hz⟩ := hzK0 hK
  have h4 := h4U hV₀
  have h4' := h4U hV₁
  have hzV₀ : z ∈ V₀ :=
    mem_of_isUniqueInvolution_of_isPGroup hz hV₀K (h2U hV₀) (by omega)
  have hc : V₁ ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (habel x (hV₁W hx) z (hV₀W hzV₀))
  have hN : V₁ ≤ Subgroup.normalizer (K : Set G) :=
    hnorm hK hJ (Ne.symm hJK) hz hV₁J
      (h2U hV₁) (by omega) hc
  exact Relation.ReflTransGen.single ⟨hJ, Or.inl ⟨hJ, hJK, V₁, hV₁, hV₁J, hN⟩⟩

theorem mem_dstarComp_of_mem_USet_le_W [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J W V₀ V₁ : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hV₀ : V₀ ∈ USet Ω) (hV₀K : V₀ ≤ K) (hV₀W : V₀ ≤ W) (hV₁ : V₁ ∈ USet Ω) (hV₁J : V₁ ≤ J)
    (hV₁W : V₁ ≤ W) (habel : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : J ∈ dstarComp Ω K :=
  E187C.mem_dstarComp_of_mem_USet_le_W_of (fun hK => hΩ.exists_uniqueInvolution hp hq hK)
    (fun hU => by
      obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hU
      exact h4)
    (fun hU => hΩ.isPGroup_of_mem_USet hp hU)
    (fun hK hJ hKJ hz hAJ hA2 hA3 hAc =>
      hΩ.le_normalizer_of_le_centralizer hp hq hK hJ hKJ hz hAJ hA2 hA3 hAc)
    hK hJ hV₀ hV₀K hV₀W hV₁ hV₁J hV₁W habel

theorem exists_conj_mem_of_sylow_le [Finite G] {S : Sylow 2 G} {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) {v : G} (hvH : v ∈ H) (hv : IsPGroup 2 (Subgroup.zpowers v)) :
    ∃ h ∈ H, h⁻¹ * v * h ∈ (S : Subgroup G) := by
  have hP : IsPGroup 2 ((Subgroup.zpowers v).subgroupOf H) := hv.comap_subtype
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hP
  obtain ⟨h, hh⟩ := exists_conjSub_eq_of_sylow (G := ↥H) (S.subtype hSH) Q
  refine ⟨h, h.2, ?_⟩
  have hvQ : (⟨v, hvH⟩ : ↥H) ∈ (Q : Subgroup ↥H) :=
    hQ (by simp [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers])
  rw [← hh, mem_conjSub_iff] at hvQ
  simpa [Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hvQ

@[expose] def EtaAbelian (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Sylow 2 G, ∀ η ∈ etaSet Ω (S : Subgroup G),
    (∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) →
      ∀ x ∈ ⨆ U ∈ η, U, ∀ y ∈ ⨆ U ∈ η, U, x * y = y * x

@[expose] def EtaMeet (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
    ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (⨆ V ∈ η, V) ∈ η

theorem EtaAbelian.of_cyc66 [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hC : Cyc66 Ω) : EtaAbelian Ω :=
  fun _ _ hη hinv => (eta_abelian_of_cyc66 hp hq hΩ hC hη hinv).1

theorem EtaMeet.of_cyc66 [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hC : Cyc66 Ω) : EtaMeet Ω :=
  fun _ _ hη hηS _ hK h2 => eta_inf_mem_of_cyc66 hp hq hΩ hC hη hηS hK h2

theorem EtaAbelian.of_l6_9 [Finite G] (h : L6_9 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) : EtaAbelian Ω :=
  fun S _ hη hinv => ((h hp hq G Ω hΩ S).2 _ hη hinv).1

theorem EtaMeet.of_l6_11 [Finite G] (h : L6_11 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) : EtaMeet Ω :=
  fun S _ hη hηS _ hK h2 => h hp hq G Ω hΩ S _ hη hηS _ hK h2

section MinCex

variable [Finite G] {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.exists_eta (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω) :
    ∃ η : Set (Subgroup G), η ∈ etaG Ω ∧ W = ⨆ V ∈ η, V ∧
      (∀ V ∈ η, V ∈ USet Ω ∧ V ≤ (S : Subgroup G)) ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ ∃ V₀ ∈ η, V₀ ≤ K := by
  have hp : p ≠ 2 := c.stand.odd
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨hWW, hWS, -⟩ := c.stand.hW
  obtain ⟨η, hη, hWη⟩ := hWW
  obtain ⟨S₁, hS₁, hinv⟩ := hη
  have hAW : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂_of_le V hV le_rfl
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hAW V hV).trans hWS
  have hηS' : η ∈ etaSet Ω (S : Subgroup G) := mem_etaSet_of_le hΩ.conjInvariant hS₁ hηS
  have hRK' : IsSylow2In R K := hΩ.isSylow2In_of_mem_RSet_of_le hp hK hRR hRK
  obtain ⟨U₀, hU₀R, hcyc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hp hRR).exists_cyclic_index_two
  have hU₀ : U₀ ∈ USet Ω := mem_USet_of_natCard hK hRK' hU₀R hcyc hcard
  obtain ⟨V₀, hV₀η, hV₀K⟩ := exists_mem_of_mem_etaSet hp hΩ hηS' hK ⟨hU₀, hU₀R.trans hRS⟩
    (hU₀R.trans hRK)
  refine ⟨η, ⟨S₁, hS₁, hinv⟩, hWη, fun V hV => ⟨(hS₁.1 hV).1, hηS V hV⟩, ?_, V₀, hV₀η, hV₀K⟩
  have := hA S₁ η hS₁ hinv
  rwa [← hWη] at this

theorem MinCex.mem_of_conjSub_eq_W (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω) {n : G}
    (hn : conjSub n W = W) : n ∈ H := by
  obtain ⟨η, -, hWη, hηU, habel, V₀, hV₀η, hV₀K⟩ := c.exists_eta hA
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hV₀U : V₀ ∈ USet Ω := (hηU V₀ hV₀η).1
  have hV₀W : V₀ ≤ W := hWη ▸ le_iSup₂_of_le V₀ hV₀η le_rfl
  have hmem : conjSub n K ∈ dstarComp Ω K :=
    mem_dstarComp_of_mem_USet_le_W hp hq hΩ c.stand.mem (hΩ.conjInvariant n K c.stand.mem)
      hV₀U hV₀K hV₀W (USet.conj hΩ.conjInvariant hV₀U n) (conjSub_mono hV₀K)
      (hn ▸ conjSub_mono hV₀W) habel
  exact (e18_1 p f G Ω K S R W H c).1 n hmem

theorem MinCex.sylow_le (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω) :
    (S : Subgroup G) ≤ H :=
  fun s hs => c.mem_of_conjSub_eq_W hA (c.stand.hW.2.2 s hs)

theorem E187C.mem_of_conj_mem_of {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K W H : Subgroup G} {S : Sylow 2 G} (hc : ConjInvariant Ω) (hK : K ∈ Ω) (hM : EtaMeet Ω)
    (heta : ∃ η : Set (Subgroup G), η ∈ etaG Ω ∧ W = ⨆ V ∈ η, V ∧
      (∀ V ∈ η, V ∈ USet Ω ∧ V ≤ (S : Subgroup G)) ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ ∃ V₀ ∈ η, V₀ ≤ K)
    (hSH : (S : Subgroup G) ≤ H)
    (hdst : ∀ {J V₀ V₁ : Subgroup G}, J ∈ Ω → V₀ ∈ USet Ω → V₀ ≤ K → V₀ ≤ W → V₁ ∈ USet Ω →
      V₁ ≤ J → V₁ ≤ W → (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) → J ∈ dstarComp Ω K)
    (h181 : ∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H)
    {u : G} (hu : u ∈ K) (hu4 : orderOf u = 4) {g : G} (hg : g * u * g⁻¹ ∈ H) :
    g ∈ H := by
  obtain ⟨η, hη, hWη, hηU, habel, V₀, hV₀η, hV₀K⟩ := heta
  have hv4 : orderOf (g * u * g⁻¹) = 4 := by rw [orderOf_conj_mul_inv, hu4]
  have hv2 : IsPGroup 2 (Subgroup.zpowers (g * u * g⁻¹)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hv4]; norm_num)
  obtain ⟨h, hhH, hh⟩ := exists_conj_mem_of_sylow_le hSH hg hv2
  have hxu : (h⁻¹ * g) * u * (h⁻¹ * g)⁻¹ ∈ (S : Subgroup G) := by
    have e : (h⁻¹ * g) * u * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * u * g⁻¹) * h := by group
    rw [e]
    exact hh
  have hK₁ : conjSub (h⁻¹ * g) K ∈ Ω := hc _ K hK
  have h2 : 2 < Nat.card ↥(conjSub (h⁻¹ * g) K ⊓ (S : Subgroup G)) := by
    have hle : Subgroup.zpowers ((h⁻¹ * g) * u * (h⁻¹ * g)⁻¹) ≤
        conjSub (h⁻¹ * g) K ⊓ (S : Subgroup G) :=
      Subgroup.zpowers_le.mpr ⟨conj_mem_conjSub hu, hxu⟩
    have h4 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_conj_mul_inv, hu4] at h4
    omega
  have hmem := hM S η hη (fun V hV => (hηU V hV).2) _ hK₁ h2
  rw [← hWη] at hmem
  have hV₀W : V₀ ≤ W := hWη ▸ le_iSup₂_of_le V₀ hV₀η le_rfl
  have hSigma : conjSub (h⁻¹ * g) K ∈ dstarComp Ω K :=
    hdst hK₁ (hηU V₀ hV₀η).1 hV₀K hV₀W
      (hηU _ hmem).1 inf_le_left inf_le_right habel
  have hxH : h⁻¹ * g ∈ H := h181 _ hSigma
  have hg' : g = h * (h⁻¹ * g) := by group
  rw [hg']
  exact H.mul_mem hhH hxH

theorem MinCex.mem_of_conj_mem (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {u : G} (hu : u ∈ K) (hu4 : orderOf u = 4) {g : G} (hg : g * u * g⁻¹ ∈ H) :
    g ∈ H := by
  exact E187C.mem_of_conj_mem_of c.stand.hyp.conjInvariant c.stand.mem hM (c.exists_eta hA)
    (c.sylow_le hA)
    (fun hJ hV₀ hV₀K hV₀W hV₁ hV₁J hV₁W habel =>
      mem_dstarComp_of_mem_USet_le_W c.stand.odd c.stand.five c.stand.hyp c.stand.mem hJ hV₀ hV₀K
        hV₀W hV₁ hV₁J hV₁W habel)
    (e18_1 p f G Ω K S R W H c).1 hu hu4 hg

end MinCex

variable (p f)

theorem e18_2_of_l6_9_l6_11 (h69 : L6_9 p f) (h611 : L6_11 p f) : E18_2 p f := by
  intro G _ _ Ω K S R W H c u hu hu4 g hg
  exact c.mem_of_conj_mem (EtaAbelian.of_l6_9 h69 c.stand.odd c.stand.five c.stand.hyp)
    (EtaMeet.of_l6_11 h611 c.stand.odd c.stand.five c.stand.hyp) hu hu4 hg

theorem e18_2 (h : L6_6ii p f) : E18_2 p f :=
  e18_2_of_l6_9_l6_11 p f (l6_9_of_l6_6ii p f h) (l6_11_of_l6_6ii p f h)

theorem e18_2AEmpty (h3 : E18_3 p f) (h : L6_6iiAEmpty p f) : E18_2 p f := by
  intro G _ _ Ω K S R W H c u hu hu4 g hg
  have hA := aEmpty_forall_of_transitive c.stand.hyp.conjInvariant (h3 G Ω K S R W H c)
    c.stand.aEmpty
  have hC := h c.stand.odd c.stand.five G Ω c.stand.hyp hA
  exact c.mem_of_conj_mem (EtaAbelian.of_cyc66 c.stand.odd c.stand.five c.stand.hyp hC)
    (EtaMeet.of_cyc66 c.stand.odd c.stand.five c.stand.hyp hC) hu hu4 hg

theorem e18_2_of_l6_7 (h67 : L6_7 p f) (h : L6_6iiAEmpty p f) : E18_2 p f :=
  e18_2AEmpty p f (e18_3 p f h67) h

end CFSG.ClassicalInvolution.Asc77
