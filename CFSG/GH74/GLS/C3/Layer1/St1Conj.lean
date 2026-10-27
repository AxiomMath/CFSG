module

public import CFSG.GH74.GLS.C3.Layer1.St1Prop77
public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.CentralizerConj
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.C3.Layer1.St1Thm4
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped Pointwise

section Conj

variable {G : Type} [Group G]

theorem orderOf_conj' (c y : G) : orderOf (c * y * c⁻¹) = orderOf y := by
  have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y
  simpa [MulAut.conj_apply] using this

theorem centralizer_conj_eq
    (c x : G) :
    centralizer ({c * x * c⁻¹} : Set G) = cmap c (centralizer ({x} : Set G)) :=
  (GorensteinWalter.map_centralizer_singleton_conj c x).symm

theorem mem_centralizer_conj_iff
    {c x z : G} :
    z ∈ centralizer ({c * x * c⁻¹} : Set G) ↔ c⁻¹ * z * c ∈ centralizer ({x} : Set G) := by
  rw [centralizer_conj_eq, mem_cmap]

theorem mem_normalizer_cmap_iff {c y : G} {K : Subgroup G} :
    c * y * c⁻¹ ∈ normalizer (cmap c K : Set G) ↔ y ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h k
    have := h (c * k * c⁻¹)
    rw [mem_cmap, mem_cmap] at this
    rwa [show c⁻¹ * (c * k * c⁻¹) * c = k by group,
      show c⁻¹ * (c * y * c⁻¹ * (c * k * c⁻¹) * (c * y * c⁻¹)⁻¹) * c = y * k * y⁻¹ by group] at this
  · intro h g
    rw [mem_cmap, mem_cmap]
    have := h (c⁻¹ * g * c)
    rwa [show c⁻¹ * (c * y * c⁻¹ * g * (c * y * c⁻¹)⁻¹) * c = y * (c⁻¹ * g * c) * y⁻¹ by group]

theorem mem_centralizerSection_cmap_iff {c z : G} {K M : Subgroup G} :
    c * z * c⁻¹ ∈ centralizerSection (cmap c K) (cmap c M) ↔ z ∈ centralizerSection K M := by
  constructor
  · intro h
    have h2 := cmap_mem_centralizerSection h c⁻¹
    rwa [cmap_inv_cancel, cmap_inv_cancel,
      show c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ = z by group] at h2
  · intro h
    exact cmap_mem_centralizerSection h c

theorem mem_CxK_cmap_iff
    {c x z' : G} {K : Subgroup G} :
    z' ∈ CxK (c * x * c⁻¹) (cmap c K) ↔ c⁻¹ * z' * c ∈ CxK x K := by
  unfold CxK
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_centralizer_conj_iff, pPrimeCoreOf_cmap]
  have := @mem_centralizerSection_cmap_iff G _ c (c⁻¹ * z' * c) K (pPrimeCoreOf 2 K)
  rw [show c * (c⁻¹ * z' * c) * c⁻¹ = z' by group] at this
  rw [this]

theorem CxK_cmap
    (c x : G) (K : Subgroup G) :
    CxK (c * x * c⁻¹) (cmap c K) = cmap c (CxK x K) := by
  ext z
  rw [mem_cmap]
  exact mem_CxK_cmap_iff

section Fin

variable [Finite G]

theorem isSylowOf_cmap {P X : Subgroup G} (h : IsSylowOf 2 P X) (c : G) :
    IsSylowOf 2 (cmap c P) (cmap c X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hP.map _, ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]

theorem isUnbalancingTriple_cmap
    {x y : G} {K : Subgroup G} (h : IsUnbalancingTriple x y K)
    (c : G) : IsUnbalancingTriple (c * x * c⁻¹) (c * y * c⁻¹) (cmap c K) := by
  obtain ⟨hK, hy, hyx, hyN, hnot⟩ := h
  refine ⟨⟨by rw [orderOf_conj']; exact hK.1, ?_⟩, by rw [orderOf_conj']; exact hy, ?_,
    mem_normalizer_cmap_iff.mpr hyN, ?_⟩
  · rw [centralizer_conj_eq]
    exact isPCompIn_cmap hK.2 c
  · rw [mem_centralizer_conj_iff, show c⁻¹ * (c * y * c⁻¹) * c = y by group]
    exact hyx
  · intro hle
    apply hnot
    intro w hw
    have hw1 : c * w * c⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({c * y * c⁻¹} : Set G)) := by
      rw [centralizer_conj_eq, pPrimeCoreOf_cmap, mem_cmap,
        show c⁻¹ * (c * w * c⁻¹) * c = w by group]
      exact hw.1
    have hw2 : c * w * c⁻¹ ∈ centralizer ({c * x * c⁻¹} : Set G) := by
      rw [mem_centralizer_conj_iff, show c⁻¹ * (c * w * c⁻¹) * c = w by group]
      exact hw.2
    have h3 := hle ⟨hw1, hw2⟩
    rw [pPrimeCoreOf_cmap] at h3
    exact mem_centralizerSection_cmap_iff.mp h3

theorem isTerminallyUnbalancing_cmap
    {x y : G} {K : Subgroup G} (h : IsTerminallyUnbalancing x y K)
    (c : G) : IsTerminallyUnbalancing (c * x * c⁻¹) (c * y * c⁻¹) (cmap c K) := by
  have hord : ∀ z' : G, orderOf z' = 2 → orderOf (c⁻¹ * z' * c) = 2 := by
    intro z' hz'
    have := orderOf_conj' c⁻¹ z'
    rw [inv_inv] at this
    exact this.trans hz'
  have hcomm : ∀ z' : G, z' * (c * y * c⁻¹) = (c * y * c⁻¹) * z' →
      (c⁻¹ * z' * c) * y = y * (c⁻¹ * z' * c) := by
    intro z' hz'
    calc c⁻¹ * z' * c * y = c⁻¹ * (z' * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * z') * c := by rw [hz']
      _ = y * (c⁻¹ * z' * c) := by group
  have hpump : ∀ (z' : G) (K'' : Subgroup G), PumpUpLT 2 (c * x * c⁻¹) (cmap c K) z' (cmap c K'') →
      PumpUpLT 2 x K (c⁻¹ * z' * c) K'' := by
    intro z' K'' hK
    have hK' := pumpUpLT_cmap hK c⁻¹
    rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group, cmap_inv_cancel, cmap_inv_cancel,
      show c⁻¹ * z' * c⁻¹⁻¹ = c⁻¹ * z' * c by group] at hK'
  refine ⟨isUnbalancingTriple_cmap h.unbalancing c, ?_, ?_⟩
  · intro z' hz' hzC hzy
    have htp := h.trivialPumpups _ (hord z' hz') (mem_CxK_cmap_iff.mp hzC) (hcomm z' hzy)
    intro K₁ hK₁
    obtain ⟨K'', rfl⟩ : ∃ K'', K₁ = cmap c K'' := ⟨cmap c⁻¹ K₁, (cmap_cancel c K₁).symm⟩
    obtain ⟨hxN, ⟨e⟩⟩ := htp K'' (hpump z' K'' hK₁)
    obtain ⟨eA⟩ := nonempty_quot_cmap c K''
    obtain ⟨eB⟩ := nonempty_quot_cmap c K
    exact ⟨mem_normalizer_cmap_iff.mpr hxN, ⟨(eA.trans e).trans eB.symm⟩⟩
  · intro Q' hQ' z' hz'Q' hz'ord hz'cent hz'y K₁ hK₁
    obtain ⟨K'', rfl⟩ : ∃ K'', K₁ = cmap c K'' := ⟨cmap c⁻¹ K₁, (cmap_cancel c K₁).symm⟩
    have hQ : IsSylowOf 2 (cmap c⁻¹ Q') (CxK x K) := by
      have := isSylowOf_cmap hQ' c⁻¹
      rwa [CxK_cmap, cmap_inv_cancel] at this
    have hzQ : c⁻¹ * z' * c ∈ cmap c⁻¹ Q' := by
      rw [mem_cmap, inv_inv, show c * (c⁻¹ * z' * c) * c⁻¹ = z' by group]
      exact hz'Q'
    have hcent : ∀ q ∈ cmap c⁻¹ Q', (c⁻¹ * z' * c) * q = q * (c⁻¹ * z' * c) := by
      intro q hq
      rw [mem_cmap, inv_inv] at hq
      have h1 := hz'cent _ hq
      calc c⁻¹ * z' * c * q = c⁻¹ * (z' * (c * q * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * q * c⁻¹) * z') * c := by rw [h1]
        _ = q * (c⁻¹ * z' * c) := by group
    have hres := h.sylow (cmap c⁻¹ Q') hQ _ hzQ (hord z' hz'ord) hcent (hcomm z' hz'y) K''
      (hpump z' K'' hK₁)
    have := isSylowOf_cmap hres c
    rwa [cmap_cancel, ← CxK_cmap, show c * (c⁻¹ * z' * c) * c⁻¹ = z' by group] at this

theorem exists_conj_mem_sylow_two {Q : Subgroup G} (hQ : IsPGroup 2 Q) (S : Sylow 2 G) :
    ∃ g : G, ∀ q ∈ Q, g⁻¹ * q * g ∈ (S : Subgroup G) := by
  obtain ⟨T, hQT⟩ := hQ.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S T
  refine ⟨g, fun q hq => ?_⟩
  have h := hQT hq
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
  simpa [MulAut.smul_def, mul_assoc] using h

theorem b_st1_lemma75
    : B_st1_lemma75 := by
  intro G _ _ S hS x y K h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu := h.unbalancing
  have hy2 : orderOf y = 2 := hu.2.1
  have hyC : y ∈ centralizer ({x} : Set G) := hu.2.2.1
  have hyp : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  obtain ⟨T₀, hT₀, hyT₀⟩ := exists_isSylowOf_ge (N := centralizer ({x} : Set G)) (K := zpowers y)
    (zpowers_le.mpr hyC) hyp
  obtain ⟨hSle, hSp, hSdvd⟩ := isSylowOf_iff.mp hS
  have hSdvd' : ¬ 2 ∣ S.index := by rwa [Subgroup.relIndex_top_right] at hSdvd
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_two hT₀.isPGroup (hSp.toSylow hSdvd')
  have hSsub : ((hSp.toSylow hSdvd' : Sylow 2 G) : Subgroup G) = S := IsPGroup.toSylow_coe hSp hSdvd'
  rw [hSsub] at hg
  have hxx : g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g := by rw [inv_inv]
  have hyy : g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g := by rw [inv_inv]
  have hC : centralizer ({g⁻¹ * x * g} : Set G) = cmap g⁻¹ (centralizer ({x} : Set G)) := by
    rw [← hxx]
    exact centralizer_conj_eq g⁻¹ x
  have hT₀' : IsSylowOf 2 (cmap g⁻¹ T₀) (centralizer ({g⁻¹ * x * g} : Set G)) := by
    rw [hC]
    exact isSylowOf_cmap hT₀ g⁻¹
  have hT₀S : cmap g⁻¹ T₀ ≤ S := by
    intro z hz
    rw [mem_cmap, inv_inv] at hz
    have := hg _ hz
    rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this
  refine ⟨g, ?_, ?_, hg y (hyT₀ (mem_zpowers y))⟩
  · have := isTerminallyUnbalancing_cmap h g⁻¹
    rw [hxx, hyy] at this
    exact this
  · have hle : cmap g⁻¹ T₀ ≤ S ⊓ centralizer ({g⁻¹ * x * g} : Set G) := le_inf hT₀S hT₀'.le
    have heq := hT₀'.eq_of_le hle inf_le_right (hSp.to_inf_left)
    rw [heq]
    exact hT₀'

end Fin

end Conj

end CFSG.GH74.GLS
