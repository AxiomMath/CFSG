module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmQ8Frame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmE

namespace MinCexQ8Frame

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem mem_dstarComp_of_mem_USet_le_W [Finite G] (hΩ : HypOmegaGen Ω) {K J W V₀ V₁ : Subgroup G} (hK
    : K ∈ Ω) (hJ : J ∈ Ω)
    (hV₀ : V₀ ∈ USet Ω) (hV₀K : V₀ ≤ K) (hV₀W : V₀ ≤ W) (hV₁ : V₁ ∈ USet Ω) (hV₁J : V₁ ≤ J)
    (hV₁W : V₁ ≤ W) (habel : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : J ∈ dstarComp Ω K := by
  by_cases hJK : J = K
  · rw [hJK]
    exact Relation.ReflTransGen.refl
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hV₀
  obtain ⟨-, -, -, -, -, -, -, -, h4'⟩ := hΩ.exists_data_of_mem_USet hV₁
  have hzV₀ : z ∈ V₀ :=
    mem_of_isUniqueInvolution_of_isPGroup hz hV₀K (hΩ.isPGroup_of_mem_USet hV₀) (by omega)
  have hc : V₁ ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (habel x (hV₁W hx) z (hV₀W hzV₀))
  have hN : V₁ ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK hJ (Ne.symm hJK) hz hV₁J
      (hΩ.isPGroup_of_mem_USet hV₁) (by omega) hc
  exact Relation.ReflTransGen.single ⟨hJ, Or.inl ⟨hJ, hJK, V₁, hV₁, hV₁J, hN⟩⟩

private theorem orderOf_conj_mul_inv (g u : G) : orderOf (g * u * g⁻¹) = orderOf u := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) u
  simpa [MulAut.conj_apply] using this

section Eng

variable [Finite G] {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem exists_eta (c : MinCexQ8Frame Ω K S R W H) (hA : EtaAbelian Ω) :
    ∃ η : Set (Subgroup G), η ∈ etaG Ω ∧ W = ⨆ V ∈ η, V ∧
      (∀ V ∈ η, V ∈ USet Ω ∧ V ≤ (S : Subgroup G)) ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ ∃ V₀ ∈ η, V₀ ≤ K := by
  have hΩ : HypOmegaGen Ω := c.hyp
  have hK : K ∈ Ω := c.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.hR
  obtain ⟨hWW, hWS, -⟩ := c.hW
  obtain ⟨η, hη, hWη⟩ := hWW
  obtain ⟨S₁, hS₁, hinv⟩ := hη
  have hAW : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂_of_le V hV le_rfl
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hAW V hV).trans hWS
  have hηS' : η ∈ etaSet Ω (S : Subgroup G) := mem_etaSet_of_le hΩ.conjInvariant hS₁ hηS
  have hRK' : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRR hRK
  obtain ⟨U₀, hU₀R, hcyc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hRR).exists_cyclic_index_two
  have hU₀ : U₀ ∈ USet Ω := mem_USet_of_natCard hK hRK' hU₀R hcyc hcard
  obtain ⟨V₀, hV₀η, hV₀K⟩ :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.exists_mem_of_mem_etaSet hΩ hηS' hK
      ⟨hU₀, hU₀R.trans hRS⟩
    (hU₀R.trans hRK)
  refine ⟨η, ⟨S₁, hS₁, hinv⟩, hWη, fun V hV => ⟨(hS₁.1 hV).1, hηS V hV⟩, ?_, V₀, hV₀η, hV₀K⟩
  have := hA S₁ η hS₁ hinv
  rwa [← hWη] at this

theorem mem_of_conjSub_eq_W (c : MinCexQ8Frame Ω K S R W H)
    (h181 : ∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H) (hA : EtaAbelian Ω) {n : G}
    (hn : conjSub n W = W) : n ∈ H := by
  obtain ⟨η, -, hWη, hηU, habel, V₀, hV₀η, hV₀K⟩ := c.exists_eta hA
  have hΩ : HypOmegaGen Ω := c.hyp
  have hV₀U : V₀ ∈ USet Ω := (hηU V₀ hV₀η).1
  have hV₀W : V₀ ≤ W := hWη ▸ le_iSup₂_of_le V₀ hV₀η le_rfl
  have hmem : conjSub n K ∈ dstarComp Ω K :=
    mem_dstarComp_of_mem_USet_le_W hΩ c.mem (hΩ.conjInvariant n K c.mem)
      hV₀U hV₀K hV₀W (USet.conj hΩ.conjInvariant hV₀U n) (conjSub_mono hV₀K)
      (hn ▸ conjSub_mono hV₀W) habel
  exact h181 n hmem

theorem sylow_le (c : MinCexQ8Frame Ω K S R W H)
    (h181 : ∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H) (hA : EtaAbelian Ω) :
    (S : Subgroup G) ≤ H :=
  fun s hs => c.mem_of_conjSub_eq_W h181 hA (c.hW.2.2 s hs)

theorem mem_of_conj_mem (c : MinCexQ8Frame Ω K S R W H)
    (h181 : ∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {u : G} (hu : u ∈ K) (hu4 : orderOf u = 4) {g : G} (hg : g * u * g⁻¹ ∈ H) :
    g ∈ H := by
  obtain ⟨η, hη, hWη, hηU, habel, V₀, hV₀η, hV₀K⟩ := c.exists_eta hA
  have hΩ : HypOmegaGen Ω := c.hyp
  have hK : K ∈ Ω := c.mem
  
  have hv4 : orderOf (g * u * g⁻¹) = 4 := by rw [orderOf_conj_mul_inv, hu4]
  have hv2 : IsPGroup 2 (Subgroup.zpowers (g * u * g⁻¹)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hv4]; norm_num)
  obtain ⟨h, hhH, hh⟩ := exists_conj_mem_of_sylow_le (c.sylow_le h181 hA) hg hv2
  have hxu : (h⁻¹ * g) * u * (h⁻¹ * g)⁻¹ ∈ (S : Subgroup G) := by
    have e : (h⁻¹ * g) * u * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * u * g⁻¹) * h := by group
    rw [e]
    exact hh
  
  have hK₁ : conjSub (h⁻¹ * g) K ∈ Ω := hΩ.conjInvariant _ K hK
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
    mem_dstarComp_of_mem_USet_le_W hΩ hK hK₁ (hηU V₀ hV₀η).1 hV₀K hV₀W
      (hηU _ hmem).1 inf_le_left inf_le_right habel
  have hxH : h⁻¹ * g ∈ H := h181 _ hSigma
  have hg' : g = h * (h⁻¹ * g) := by group
  rw [hg']
  exact H.mul_mem hhH hxH

end Eng

end MinCexQ8Frame

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
