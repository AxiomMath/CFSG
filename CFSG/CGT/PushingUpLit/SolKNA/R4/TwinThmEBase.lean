module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmESteps
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf182

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW

namespace ThmE

section Base


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.exists_zW (c : MinCex r Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W :=
  exists_zW' c.stand.hyp c.stand.mem c.stand.hR.1 c.stand.hR.2.1 c.stand.hR.2.2 c.stand.hW.1
    c.stand.hW.2.1

theorem MinCex.centralizer_le (c : MinCex r Ω K S R W H) {z : G}
    (hz : IsUniqueInvolution K z) : Subgroup.centralizer ({z} : Set G) ≤ H :=
  centralizer_le_of_hyp c.stand.hyp c.stand.mem c.stand.hR.1 c.stand.hR.2.1 c.stand.hR.2.2
    c.stand.hW.1 c.stand.hW.2.1 c.hyp.cent hz

theorem MinCex.exists_centralizer_le (c : MinCex r Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution c.stand.hyp c.stand.mem
  exact ⟨z, hz, c.centralizer_le hz⟩

theorem e18_1 : E18_1 r := by
  intro G _ _ Ω K S R W H c
  obtain ⟨z, hz, hcz⟩ := c.exists_centralizer_le
  have key : ∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H := fun g hg =>
    mem_of_conjSub_mem_dstarComp c.hyp.trans hz hcz hg
  refine ⟨key, ?_⟩
  by_contra hno
  push Not at hno
  apply c.proper
  rw [eq_top_iff]
  intro g _
  exact key g (hno _ (c.stand.hyp.conjInvariant g K c.stand.mem))

theorem e18_3 : E18_3 r := by
  intro G _ _ Ω K S R W H c J hJ
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hΩc := hΩ.conjInvariant
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨RJ, hRJmem, hRJ, -⟩ :=
    exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hRJ.2.1
  obtain ⟨y, hy⟩ := exists_conjSub_eq_of_sylow S Q
  set J' : Subgroup G := conjSub y⁻¹ J with hJ'def
  set R' : Subgroup G := conjSub y⁻¹ RJ with hR'def
  have hJ'Ω : J' ∈ Ω := hΩc y⁻¹ J hJ
  have hR'mem : R' ∈ RSet Ω := RSet.conj hΩc hRJmem y⁻¹
  have hR'J : IsSylow2In R' J' := hRJ.conj y⁻¹
  have hR'S : R' ≤ (S : Subgroup G) := by
    have h1 : RJ ≤ conjSub y (S : Subgroup G) := hy ▸ hQ
    have := conjSub_mono (n := y⁻¹) h1
    rwa [conjSub_inv_conjSub] at this
  have key : J' ∈ dstarComp Ω K := by
    by_cases hJK : J' = K
    · rw [hJK]
      exact Relation.ReflTransGen.refl
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
    have hR2 : IsPGroup 2 R := by
      obtain ⟨J₀, -, -, h2, -⟩ := mem_RSet_iff.mp hRR
      exact h2
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRR
    have h8' := Sec6Gen.eight_le_of_mem_RSet hΩ hR'mem
    have hRne : R ≠ R' := by
      intro hRR'
      exact hJK (Sec6Gen.eq_of_le_of_le hΩ hJ'Ω hK hR2 (by omega) (hRR' ▸ hR'J.1) hRK)
    have hcomm : Commutes R R' := Q3CP.l67Gen G Ω hΩ S R hRR R' hR'mem hRS hR'S hRne
    have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRK hR2 (by omega)
    have hR'c : R' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzR x hx).symm
    have hR'N : R' ≤ Subgroup.normalizer (K : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJ'Ω (Ne.symm hJK) hz hR'J.1 hR'J.2.1
        (by omega) hR'c
    obtain ⟨U, hUR, hUcyc, hUcard⟩ :=
      (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR'mem).exists_cyclic_index_two
    have hU : U ∈ USet Ω := mem_USet_of_natCard hJ'Ω hR'J hUR hUcyc hUcard
    exact Relation.ReflTransGen.single ⟨hJ'Ω, Or.inl ⟨hJ'Ω, hJK, U, hU, hUR.trans hR'J.1,
      hUR.trans hR'N⟩⟩
  obtain ⟨h, -, hh⟩ := c.hyp.trans J' key
  refine ⟨y * h, ?_⟩
  rw [conjSub_mul, hh]
  exact conjSub_conjSub_inv y J

private theorem orderOf_conj_mul_inv' (g u : G) : orderOf (g * u * g⁻¹) = orderOf u := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) u
  simpa [MulAut.conj_apply] using this

theorem MinCex.exists_eta (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω) :
    ∃ η : Set (Subgroup G), η ∈ etaG Ω ∧ W = ⨆ V ∈ η, V ∧
      (∀ V ∈ η, V ∈ USet Ω ∧ V ≤ (S : Subgroup G)) ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ ∃ V₀ ∈ η, V₀ ≤ K := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨hWW, hWS, -⟩ := c.stand.hW
  obtain ⟨η, hη, hWη⟩ := hWW
  obtain ⟨S₁, hS₁, hinv⟩ := hη
  have hAW : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂_of_le V hV le_rfl
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hAW V hV).trans hWS
  have hηS' : η ∈ etaSet Ω (S : Subgroup G) := mem_etaSet_of_le hΩ.conjInvariant hS₁ hηS
  have hRK' : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRR hRK
  obtain ⟨U₀, hU₀R, hcyc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hRR).exists_cyclic_index_two
  have hU₀ : U₀ ∈ USet Ω := mem_USet_of_natCard hK hRK' hU₀R hcyc hcard
  obtain ⟨V₀, hV₀η, hV₀K⟩ :=
    Sec6Gen.exists_mem_of_mem_etaSet hΩ hηS' hK ⟨hU₀, hU₀R.trans hRS⟩ (hU₀R.trans hRK)
  refine ⟨η, ⟨S₁, hS₁, hinv⟩, hWη, fun V hV => ⟨(hS₁.1 hV).1, hηS V hV⟩, ?_, V₀, hV₀η, hV₀K⟩
  have := hA S₁ η hS₁ hinv
  rwa [← hWη] at this

theorem MinCex.mem_of_conjSub_eq_W (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω) {n : G}
    (hn : conjSub n W = W) : n ∈ H := by
  obtain ⟨η, -, hWη, hηU, habel, V₀, hV₀η, hV₀K⟩ := c.exists_eta hA
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hV₀U : V₀ ∈ USet Ω := (hηU V₀ hV₀η).1
  have hV₀W : V₀ ≤ W := hWη ▸ le_iSup₂_of_le V₀ hV₀η le_rfl
  have hmem : conjSub n K ∈ dstarComp Ω K :=
    mem_dstarComp_of_mem_USet_le_W hΩ c.stand.mem (hΩ.conjInvariant n K c.stand.mem)
      hV₀U hV₀K hV₀W (USet.conj hΩ.conjInvariant hV₀U n) (conjSub_mono hV₀K)
      (hn ▸ conjSub_mono hV₀W) habel
  exact (e18_1 G Ω K S R W H c).1 n hmem

theorem MinCex.sylow_le (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω) :
    (S : Subgroup G) ≤ H :=
  fun s hs => c.mem_of_conjSub_eq_W hA (c.stand.hW.2.2 s hs)

theorem MinCex.mem_of_conj_mem (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {u : G} (hu : u ∈ K) (hu4 : orderOf u = 4) {g : G} (hg : g * u * g⁻¹ ∈ H) :
    g ∈ H := by
  obtain ⟨η, hη, hWη, hηU, habel, V₀, hV₀η, hV₀K⟩ := c.exists_eta hA
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hv4 : orderOf (g * u * g⁻¹) = 4 := by rw [orderOf_conj_mul_inv', hu4]
  have hv2 : IsPGroup 2 (Subgroup.zpowers (g * u * g⁻¹)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hv4]; norm_num)
  obtain ⟨h, hhH, hh⟩ := exists_conj_mem_of_sylow_le (c.sylow_le hA) hg hv2
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
    rw [Nat.card_zpowers, orderOf_conj_mul_inv', hu4] at h4
    omega
  have hmem := hM S η hη (fun V hV => (hηU V hV).2) _ hK₁ h2
  rw [← hWη] at hmem
  have hV₀W : V₀ ≤ W := hWη ▸ le_iSup₂_of_le V₀ hV₀η le_rfl
  have hSigma : conjSub (h⁻¹ * g) K ∈ dstarComp Ω K :=
    mem_dstarComp_of_mem_USet_le_W hΩ hK hK₁ (hηU V₀ hV₀η).1 hV₀K hV₀W
      (hηU _ hmem).1 inf_le_left inf_le_right habel
  have hxH : h⁻¹ * g ∈ H := (e18_1 G Ω K S R W H c).1 _ hSigma
  have hg' : g = h * (h⁻¹ * g) := by group
  rw [hg']
  exact H.mul_mem hhH hxH

@[expose] def E18_2 (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      ∀ u ∈ K, orderOf u = 4 → ∀ g : G, g * u * g⁻¹ ∈ H → g ∈ H

theorem e18_2 : E18_2 r := by
  intro G _ _ Ω K S R W H c u hu hu4 g hg
  exact c.mem_of_conj_mem (etaAbelian_of_gen c.stand.hyp) (etaMeet_of_gen c.stand.hyp) hu hu4 hg

theorem e18_8z_of_e18_7 (h : E18_7 r) : E18_8z r := by
  intro G _ _ Ω K S R W H c a hz
  have ha1 : a ≠ 1 := hz.ne_one
  have ha2 : a * a = 1 := hz.sq
  have hcent : Subgroup.centralizer ({a} : Set G) ≤ H := c.centralizer_le hz
  have haH : a ∈ H := hcent (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have h7 := h G Ω K S R W H c a ha1 ha2 hcent
  refine ⟨(1 : G) , ?_, ?_⟩
  · show a • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact QuotientGroup.eq.mpr (by simpa using H.inv_mem haH)
  · intro c' hc'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c'
    have hg : g⁻¹ * a * g ∈ H := by
      have h1 : a • ((g : G) : G ⧸ H) = (g : G ⧸ H) := hc'
      rw [MulAction.Quotient.smul_mk, smul_eq_mul] at h1
      have h2 := QuotientGroup.eq.mp h1
      have : (a * g)⁻¹ * g = g⁻¹ * a⁻¹ * g := by group
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
      rw [this, ha'] at h2
      exact h2
    obtain ⟨k, hk, hka⟩ := h7 g⁻¹ (by simpa using hg)
    have hgk : g * k ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 : k * a * k⁻¹ = g⁻¹ * a * g := by simpa using hka
      calc (g * k) * a = (g * (k * a * k⁻¹)) * k := by group
        _ = a * (g * k) := by rw [h3]; group
    have : g ∈ H := by
      have h4 : g * k * k⁻¹ ∈ H := H.mul_mem (hcent hgk) (H.inv_mem hk)
      simpa using h4
    exact (QuotientGroup.eq.mpr (by simpa using H.inv_mem this)).symm

end Base

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
