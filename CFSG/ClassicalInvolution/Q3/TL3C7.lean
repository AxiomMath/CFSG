module

public import CFSG.ClassicalInvolution.Q3.TL3C6
public import CFSG.ClassicalInvolution.Asc77.AscE187Conj
public import CFSG.ClassicalInvolution.Q3.TL3C5

public section

namespace CFSG.ClassicalInvolution.Q3.TC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def UAt (Ω : Set (Subgroup G)) (z : G) (N : Subgroup G) : Prop :=
  ∃ U ∈ USet Ω, U ≤ N ∧ ∃ P : Subgroup G, IsNormalTwoIn P z ∧ U ≤ P

theorem le_centralizer_of_reach (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {A : Subgroup G → Subgroup G → Prop}
    (hA : ∀ {M N : Subgroup G}, A M N → M ∈ Ω →
      N ∈ Ω ∧ ∀ z : G, IsUniqueInvolution M z → UAt Ω z N)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {η : Set (Subgroup G)} (hη : η ∈ etaG Ω)
    (hWz : etaSpan η ≤ Subgroup.centralizer ({z} : Set G)) {L : Subgroup G}
    (hL : Relation.ReflTransGen A K L) :
    L ∈ Ω ∧ ∃ u : G, IsUniqueInvolution L u ∧ etaSpan η ≤ Subgroup.centralizer ({u} : Set G) := by
  induction hL with
  | refl => exact ⟨hK, z, hz, hWz⟩
  | tail _ hMN ih =>
    obtain ⟨hMΩ, uM, huM, hWuM⟩ := ih
    obtain ⟨hNΩ, hU⟩ := hA hMN hMΩ
    obtain ⟨U₀, hU₀, hU₀N, P, hP, hU₀P⟩ := hU uM huM
    obtain ⟨-, uN, huN, hWuN⟩ :=
      normalizes_w_of_le_twoNormal hΩ h2 hη hWuM hNΩ hU₀ hU₀N hP hU₀P
    exact ⟨hNΩ, uN, huN, hWuN⟩

omit [Finite G] in
theorem conjSub_etaSpan_eq {η : Set (Subgroup G)} {g : G} (hg : ∀ V ∈ η, conjSub g V ∈ η)
    (hg' : ∀ V ∈ η, conjSub g⁻¹ V ∈ η) : conjSub g (etaSpan η) = etaSpan η := by
  apply le_antisymm
  · unfold etaSpan
    rw [conjSub_iSup₂]
    exact iSup₂_le fun V hV => le_etaSpan (hg V hV)
  · refine etaSpan_le fun V hV => ?_
    have h1 := conjSub_mono (n := g) (le_etaSpan (hg' V hV))
    rwa [conjSub_conjSub_inv] at h1

theorem inO2_of_reach (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {A : Subgroup G → Subgroup G → Prop}
    (hA : ∀ {M N : Subgroup G}, A M N → M ∈ Ω →
      N ∈ Ω ∧ ∀ z : G, IsUniqueInvolution M z → UAt Ω z N)
    (hself : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u → UAt Ω u L)
    {K : Subgroup G} (hK : K ∈ Ω) (hreach : ∀ L ∈ Ω, Relation.ReflTransGen A K L)
    (hgen : (⨆ L ∈ Ω, L) = ⊤) {z : G} (hz : IsUniqueInvolution K z) :
    ∃ P : Subgroup G, P.Normal ∧ IsPGroup 2 P ∧ z ∈ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hKS⟩ := (h2 K hK).exists_le_sylow
  obtain ⟨η, hηS, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hη : η ∈ etaG Ω := ⟨S, hηS, hinv⟩
  have hηS' : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηS.1 hV).2
  set W := etaSpan η with hWdef
  have hW2 : IsPGroup 2 W := etaSpan_isPGroup hη
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := etaSpan_comm hΩ hη
  obtain ⟨U₀, hU₀, hU₀K, -⟩ := hself K hK z hz
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU₀
  have hcard : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hU₀K (hU₀K.trans hKS))
    omega
  have hKW : K ⊓ W ∈ η := Sec6Gen.l6_11Gen G Ω hΩ S η hη hηS' K hK hcard
  have hKWU : K ⊓ W ∈ USet Ω := (hηS.1 hKW).1
  obtain ⟨-, -, -, -, -, -, -, -, hKW4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hKWU
  have hzW : z ∈ K ⊓ W := hz.mem_of_le inf_le_left (hW2.to_le inf_le_right) (by omega)
  have hWz : W ≤ Subgroup.centralizer ({z} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hWcomm w hw z hzW.2
  have hnorm : ∀ L ∈ Ω, L ≤ Subgroup.normalizer (W : Set G) := by
    intro L hL
    obtain ⟨hLΩ, uL, huL, hWuL⟩ := le_centralizer_of_reach hΩ h2 hA hK hz hη hWz (hreach L hL)
    obtain ⟨U₁, hU₁, hU₁L, P, hP, hU₁P⟩ := hself L hL uL huL
    have hact := (normalizes_w_of_le_twoNormal hΩ h2 hη hWuL hLΩ hU₁ hU₁L hP hU₁P).1
    intro l hl
    rw [mem_normalizer_iff_conjSub_eq]
    exact conjSub_etaSpan_eq (hact l hl) (hact l⁻¹ (L.inv_mem hl))
  have hWn : W.Normal := by
    have htop : (⊤ : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
      rw [← hgen]
      exact iSup₂_le hnorm
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)
  exact ⟨W, hWn, hW2, hzW.2⟩

theorem inO2_of_maxAdj (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (hsep : SepHyp Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (htr : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hgen : (⨆ J ∈ Ω, J) = ⊤) (hconn : Disconnected.DConnected Ω)
    (hself : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u → UAt Ω u L)
    (hmax : ∀ M N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ∀ u : G, IsUniqueInvolution M u →
      UAt Ω u N)
    {z : G} (hz : IsUniqueInvolution K z) :
    ∃ P : Subgroup G, P.Normal ∧ IsPGroup 2 P ∧ z ∈ P := by
  have hF := graphFam hΩ h2 hsep htr hgen hconn
  refine inO2_of_reach hΩ h2 (A := MaxAdj (nbrAdj Ω)) ?_ hself hK (reach_maxAdj hF hK) hgen hz
  intro M N hMN _
  exact ⟨hMN.1.2.1, hmax M N hMN⟩

end CFSG.ClassicalInvolution.Q3.TC
