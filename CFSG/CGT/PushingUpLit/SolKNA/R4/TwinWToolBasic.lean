module

public import CFSG.ClassicalInvolution.Q3.TL3C2
public import CFSG.ClassicalInvolution.Asc77.AscE187Conj

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.WTool

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_mem_USet_of_isPGroup (hΩ : HypOmegaGen Ω)
    (h16 : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J → 16 ≤ Nat.card P)
    {J S U V : Subgroup G} (hJ : J ∈ Ω) (hS : IsPGroup 2 S) (hU : U ∈ USet Ω) (hV : V ∈ USet Ω)
    (hUJ : U ≤ J) (hVJ : V ≤ J) (hUS : U ≤ S) (hVS : V ≤ S) : U = V := by
  obtain ⟨T, hT, hJST⟩ := IsSylow2In.exists_ge (hS.to_le (inf_le_right : J ⊓ S ≤ S))
    (inf_le_left : J ⊓ S ≤ J)
  have key : ∀ X : Subgroup G, X ∈ USet Ω → X ≤ J → X ≤ S →
      X ≤ T ∧ IsCyclic ↥X ∧ Nat.card T = 2 * Nat.card X := by
    intro X hX hXJ hXS
    obtain ⟨R, -, J', hJ', hRJ', hXR, hcX, hRX, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hX
    have hJJ' : J' = J := Sec6Gen.eq_of_mem_USet hΩ hX hJ' hJ (hXR.trans hRJ'.1) hXJ
    subst hJJ'
    exact ⟨(le_inf hXJ hXS).trans hJST, hcX, (hT.natCard_eq hRJ').trans hRX⟩
  obtain ⟨hUT, hcU, hcardU⟩ := key U hU hUJ hUS
  obtain ⟨hVT, hcV, hcardV⟩ := key V hV hVJ hVS
  exact (Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ hT)).eq_of_cyclic hUT hVT hcU
    hcV hcardU hcardV (h16 J hJ T hT)

theorem uinS_mem_etaSet (hΩ : HypOmegaGen Ω)
    (h16 : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J → 16 ≤ Nat.card P) {S : Subgroup G}
    (hS : IsPGroup 2 S) : UinS Ω S ∈ etaSet Ω S := by
  refine Sec6Gen.mem_etaSet_of_cover hΩ subset_rfl ?_ ?_
  · intro U hU U' hU' hne J hJ hUU'
    exact hne (eq_of_mem_USet_of_isPGroup hΩ h16 hJ hS hU.1 hU'.1 hUU'.1 hUU'.2 hU.2 hU'.2)
  · rintro K - ⟨U, hU, hUK⟩
    exact ⟨U, hU, hUK⟩

theorem etaSet_eq_singleton (hΩ : HypOmegaGen Ω)
    (h16 : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J → 16 ≤ Nat.card P) {S : Subgroup G}
    (hS : IsPGroup 2 S) : etaSet Ω S = {UinS Ω S} := by
  have hmem := uinS_mem_etaSet hΩ h16 hS
  ext η
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hη
    exact Set.eq_of_subset_of_ncard_le hη.1 (hη.2.2 _ subset_rfl hmem.2.1) (Set.toFinite _)
  · rintro rfl
    exact hmem

theorem isPGroup_of_mem_wSet {W : Subgroup G} (hW : W ∈ WSet Ω) : IsPGroup 2 W := by
  obtain ⟨η, hη, rfl⟩ := hW
  exact TC.etaSpan_isPGroup hη

theorem comm_of_mem_wSet (hΩ : HypOmegaGen Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) :
    ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, hη, rfl⟩ := hW
  exact TC.etaSpan_comm hΩ hη

theorem eq_iSup_uinS_of_le (hΩ : HypOmegaGen Ω)
    (h16 : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J → 16 ≤ Nat.card P) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G)) :
    W = ⨆ U ∈ UinS Ω (S : Subgroup G), U := by
  obtain ⟨η, ⟨S₁, hη, -⟩, rfl⟩ := hW
  have hsub : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (le_iSup₂_of_le V hV le_rfl).trans hWS
  have hηS := mem_etaSet_of_le hΩ.conjInvariant hη hsub
  rw [etaSet_eq_singleton hΩ h16 S.isPGroup', Set.mem_singleton_iff] at hηS
  rw [hηS]

theorem eq_of_le_of_isPGroup (hΩ : HypOmegaGen Ω)
    (h16 : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J → 16 ≤ Nat.card P) {W W' P : Subgroup G}
    (hW : W ∈ WSet Ω) (hW' : W' ∈ WSet Ω) (hP : IsPGroup 2 P) (hWP : W ≤ P) (hW'P : W' ≤ P) :
    W = W' := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  rw [eq_iSup_uinS_of_le hΩ h16 hW (hWP.trans hPS), eq_iSup_uinS_of_le hΩ h16 hW' (hW'P.trans hPS)]

theorem conjSub_eq_of_le_isPGroup (hΩ : HypOmegaGen Ω)
    (h16 : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J → 16 ≤ Nat.card P) {W P : Subgroup G}
    (hW : W ∈ WSet Ω) (hP : IsPGroup 2 P) (hWP : W ≤ P) {g : G} (hgP : conjSub g W ≤ P) :
    conjSub g W = W :=
  eq_of_le_of_isPGroup hΩ h16 (WSet.conj hΩ.conjInvariant hW g) hW hP hgP hWP

theorem le_normalizer_of_le_isPGroup (hΩ : HypOmegaGen Ω)
    (h16 : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J → 16 ≤ Nat.card P) {W P : Subgroup G}
    (hW : W ∈ WSet Ω) (hP : IsPGroup 2 P) (hWP : W ≤ P) : P ≤ Subgroup.normalizer (W : Set G) := by
  intro p hp
  rw [mem_normalizer_iff_conjSub_eq]
  refine conjSub_eq_of_le_isPGroup hΩ h16 hW hP hWP fun x hx => ?_
  rw [mem_conjSub_iff] at hx
  have h1 : p⁻¹ * x * p ∈ P := hWP hx
  have : x = p * (p⁻¹ * x * p) * p⁻¹ := by group
  rw [this]
  exact P.mul_mem (P.mul_mem hp h1) (P.inv_mem hp)

theorem exists_conj_of_mem_mem (hΩ : HypOmegaGen Ω)
    (h16 : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J → 16 ≤ Nat.card P) {W W' : Subgroup G}
    (hW : W ∈ WSet Ω) (hW' : W' ∈ WSet Ω) {z : G} (hzW : z ∈ W) (hzW' : z ∈ W') :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c W = W' := by
  have hle : ∀ V ∈ WSet Ω, z ∈ V → V ≤ Subgroup.centralizer ({z} : Set G) := by
    intro V hV hzV v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_mem_wSet hΩ hV v hv z hzV
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge (isPGroup_of_mem_wSet hW) (hle W hW hzW)
  obtain ⟨T', hT', hW'T'⟩ := IsSylow2In.exists_ge (isPGroup_of_mem_wSet hW') (hle W' hW' hzW')
  obtain ⟨c, hcC, hc⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hT hT'
  refine ⟨c, hcC, ?_⟩
  have hW'' : conjSub c⁻¹ W' ∈ WSet Ω := WSet.conj hΩ.conjInvariant hW' c⁻¹
  have hW''T : conjSub c⁻¹ W' ≤ T := by
    have := conjSub_mono (n := c⁻¹) hW'T'
    rwa [← hc, conjSub_inv_conjSub] at this
  have heq := eq_of_le_of_isPGroup hΩ h16 hW hW'' hT.2.1 hWT hW''T
  rw [heq, conjSub_conjSub_inv]

theorem inf_mem_USet_of_card (hΩ : HypOmegaGen Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G)) {M : Subgroup G} (hM : M ∈ Ω)
    (h2 : 2 < Nat.card ↥(M ⊓ (S : Subgroup G))) : M ⊓ W ∈ USet Ω := by
  obtain ⟨η, hη, rfl⟩ := hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (le_iSup₂_of_le V hV le_rfl).trans hWS
  have hmem := Sec6Gen.l6_11Gen G Ω hΩ S η hη hηS M hM h2
  obtain ⟨S₁, hS₁, -⟩ := hη
  exact (hS₁.1 hmem).1

theorem mem_of_mem_USet_of_le (hΩ : HypOmegaGen Ω) {K U : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hU : U ∈ USet Ω) (hUK : U ≤ K) : z ∈ U := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  exact mem_of_isUniqueInvolution_of_isPGroup hz hUK (Sec6Gen.isPGroup_of_mem_USet hΩ hU)
    (by omega)

theorem sylow16_of_quat {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (hquat : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J → 16 ≤ Nat.card P := by
  intro J hJ P hP
  obtain ⟨P₀, hP₀, ⟨e⟩⟩ := hquat J hJ
  rw [← Sec6Gen.natCard_isSylow2In_eq hΩ hJ hJ hP₀ hP]
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have : 2 ^ 2 ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.CGT.PushingUpLit.SolKNA.R4.WTool
