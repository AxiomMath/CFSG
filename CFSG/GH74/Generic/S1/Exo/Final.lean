module

public import CFSG.GH74.Generic.S1.Exo.Order
public import CFSG.GH74.Generic.S1.Exo.ModelOpsUni
public import CFSG.GH74.Generic.S1.TFrame

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

@[expose] def S1ExoticExcludedHigh : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → S1LargeModel K → ∀ (v : G) (hv : v ∈ centralizer ({x} : Set G)), IsConj x v →
      v ≠ x → v * v = 1 → barOf hv ∉ K → ∀ α : MulAut ↥K,
        (∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹) →
          IsExoticAut α → False

@[expose] def S1ExoticExcludedQ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ¬ S1LargeModel K → ∀ (v : G) (hv : v ∈ centralizer ({x} : Set G)), IsConj x v →
      v ≠ x → v * v = 1 → barOf hv ∉ K → ∀ α : MulAut ↥K,
        (∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹) →
          IsExoticAut α → False

theorem s1ExoticExcludedHigh_of_noPrime (hExact : S1LiftExactProp) (hno : S1LayerNoPrime) :
    S1ExoticExcludedHigh := by
  intro G _ _ x K hset hfront hbig v hv hconj hvx hv2 hvK α hα hExo
  obtain ⟨q, hq⟩ := IsExoticAut.exists_at hExo
  rcases hq with ⟨F, _, _, e, hF, h3, hβ⟩ | ⟨F, _, _, e, hF, hq4, hβ⟩
  · have hF3 : 3 < Nat.card F := three_lt_card_of_largeModel hbig (by omega) ⟨e⟩
    have hq5 : 5 ≤ q := by omega
    exact exotic_contradiction (linModelOps (by omega) hF3) hExact hno hset hfront e 1
      (Or.inl ⟨rfl, h3, F, inferInstance, inferInstance, hF, ⟨e⟩⟩) hq5 hv hconj hvx hv2 hvK α hα
      (Or.inl ⟨F, inferInstance, inferInstance, e, hF, h3, hβ⟩)
  · have hq1 : 1 < q := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hF] at h1
      by_contra hle
      have hle' : q ≤ 1 := by omega
      interval_cases q <;> simp at h1
    have hq5 : 5 ≤ q := by omega
    exact exotic_contradiction (uniModelOps hF hq4) hExact hno hset hfront e (-1)
      (Or.inr ⟨rfl, hq4, F, inferInstance, inferInstance, hF, ⟨e⟩⟩) hq5 hv hconj hvx hv2 hvK α hα
      (Or.inr ⟨F, inferInstance, inferInstance, e, hF, hq4, hβ⟩)

theorem s1ExoticExcludedExplicit_of_cases (h1 : S1ExoticExcludedHigh) (h2 : S1ExoticExcludedQ3) :
    S1ExoticExcludedExplicit := by
  intro G _ _ x K hset hfront v hv hconj hvx hv2 hvK α hα hExo
  by_cases hbig : S1LargeModel K
  · exact h1 G x K hset hfront hbig v hv hconj hvx hv2 hvK α hα hExo
  · exact h2 G x K hset hfront hbig v hv hconj hvx hv2 hvK α hα hExo

theorem s1FrameExists_of_noPrime (hExact : S1LiftExactProp) (hno : S1LayerNoPrime)
    (h3 : S1ExoticExcludedQ3) : S1FrameExists :=
  s1FrameExists_of_explicit
    (s1ExoticExcludedExplicit_of_cases (s1ExoticExcludedHigh_of_noPrime hExact hno) h3)

@[expose] def NbhdNoPrime : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (q : ℕ) (w y : H) (J₂ J₄ : Subgroup H),
    NbhdHyp H q w y J₂ J₄ → ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ q ^ 2 + 1 → ¬ r ∣ Nat.card ↥(layer H)

theorem s1LayerNoPrime_of_nbhd (hExact : S1LiftExactProp) (hNb : NbhdNoPrime) : S1LayerNoPrime := by
  intro G _ _ x K hset hfront ε q hmodel hq5 c hc hc2 hcL hcne hgrowth r hr hr2 hrq
  have hcx : c ≠ x := by
    intro h
    subst h
    exact hcne rfl
  rcases hmodel with ⟨hε, hq4, F, _, _, hF, ⟨e⟩⟩ | ⟨hε, hq4, F, _, _, hF, ⟨e⟩⟩
  · have h4 : 3 < Nat.card F := by omega
    set mo := linModelOps (F := F) (by omega) h4 with hmo
    obtain ⟨D, hDK, hDc⟩ := exists_layer_with_z0 mo hExact hset hfront e hc hc2 hcL hcne
    have hxK : xbar x ∈ D.K := hDK ▸ hset.shape.2
    have hqM : mo.qM = q := hF
    obtain ⟨y, J₂, J₄, hnb⟩ := nbhdHyp_of_classical mo D hset.simple hset.nonab hset.gen4 hset.kgh
      hset.inv hxK hDc hc2 hcx (by rw [hqM]; exact hq5) hgrowth
    have := hNb _ mo.qM _ y J₂ J₄ hnb r hr hr2 (by rw [hqM]; exact hrq)
    exact this
  · have hq5' : 5 ≤ q := hq5
    set mo := uniModelOps (F := F) hF hq4 with hmo
    obtain ⟨D, hDK, hDc⟩ := exists_layer_with_z0 mo hExact hset hfront e hc hc2 hcL hcne
    have hxK : xbar x ∈ D.K := hDK ▸ hset.shape.2
    have hqM : mo.qM = q := rfl
    obtain ⟨y, J₂, J₄, hnb⟩ := nbhdHyp_of_classical mo D hset.simple hset.nonab hset.gen4 hset.kgh
      hset.inv hxK hDc hc2 hcx (by rw [hqM]; exact hq5) hgrowth
    have := hNb _ mo.qM _ y J₂ J₄ hnb r hr hr2 (by rw [hqM]; exact hrq)
    exact this

theorem s1FrameExists_of_nbhd (hExact : S1LiftExactProp) (hNb : NbhdNoPrime)
    (h3 : S1ExoticExcludedQ3) : S1FrameExists :=
  s1FrameExists_of_noPrime hExact (s1LayerNoPrime_of_nbhd hExact hNb) h3

end CFSG.GH74.Generic.S1.Exo
