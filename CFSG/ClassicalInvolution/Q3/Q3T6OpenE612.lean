module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI2
public import CFSG.ClassicalInvolution.AschTight.Sec7L612A

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.Gen612

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem natCard_eq_two_mul_of_mem_USet (hΩ : HypOmegaGen Ω) {U K R : Subgroup G}
    (hU : U ∈ USet Ω) (hK : K ∈ Ω) (hR : IsSylow2In R K) :
    Nat.card R = 2 * Nat.card U := by
  obtain ⟨R', -, J, hJ, hR'J, -, -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  rw [← hcard, Sec6Gen.natCard_isSylow2In_eq hΩ hK hJ hR hR'J]

theorem isSylow2In_sup_of_ne (hΩ : HypOmegaGen Ω) {K U V : Subgroup G} (hK : K ∈ Ω)
    (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K) (hne : U ≠ V)
    (h2 : IsPGroup 2 ↥(U ⊔ V)) : IsSylow2In (U ⊔ V) K := by
  obtain ⟨R, hR⟩ := Sec7.exists_isSylow2In K
  have hRU := natCard_eq_two_mul_of_mem_USet hΩ hU hK hR
  have hRV := natCard_eq_two_mul_of_mem_USet hΩ hV hK hR
  refine IsSylow2In.of_natCard_le hR h2 (sup_le hUK hVK) ?_
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : U ≤ U ⊔ V)
  have hpos : 0 < Nat.card ↥(U ⊔ V) := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    have hUe : U = U ⊔ V := Subgroup.eq_of_le_of_card_ge le_sup_left hk.le
    have hVU : V ≤ U := hUe ▸ le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge hVU (by omega)).symm
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 2 ≤ k := by omega
  calc Nat.card R = 2 * Nat.card U := hRU
    _ ≤ Nat.card U * k := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hk2
    _ = Nat.card ↥(U ⊔ V) := hk.symm

theorem le_normalizer_of_mem_etaGIn (hΩ : HypOmegaGen Ω) (habel : Sec7.EtaAbelian Ω)
    (h611 : Sec7.EtaMeets Ω) {S : Sylow 2 G} {γ : Set (Subgroup G)}
    (hγ : γ ∈ Sec7.etaGIn Ω (S : Subgroup G)) {U : Subgroup G} (hU : U ∈ γ) {K : Subgroup G}
    (hK : K ∈ Ω) (hKS : 2 < Nat.card ↥(K ⊓ (S : Subgroup G))) :
    U ≤ Subgroup.normalizer (K : Set G) := by
  have hUU := Sec7.mem_USet_of_mem_etaG hγ.1 hU
  obtain ⟨K', hK', hUK'⟩ := Sec6Gen.exists_member_of_mem_USet hΩ hUU
  by_cases hKK' : K = K'
  · subst hKK'
    exact hUK'.trans (Subgroup.le_normalizer)
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hA : K ⊓ (⨆ V ∈ γ, V) ∈ γ := h611 S γ hγ.1 hγ.2 K hK hKS
  have hAU := Sec7.mem_USet_of_mem_etaG hγ.1 hA
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hAU
  have hzA : z ∈ K ⊓ (⨆ V ∈ γ, V) :=
    hz.mem_of_le inf_le_left (Sec6Gen.isPGroup_of_mem_USet hΩ hAU) (by omega)
  have hzW : z ∈ ⨆ V ∈ γ, V := (Subgroup.mem_inf.mp hzA).2
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hUU
  refine Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hK' hKK' hz hUK'
    (Sec6Gen.isPGroup_of_mem_USet hΩ hUU) (by omega) fun u hu => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact habel γ hγ.1 u (le_iSup₂_of_le (f := fun V (_ : V ∈ γ) => V) U hU le_rfl hu) z hzW

theorem etaGenIn_le_normalizer (hΩ : HypOmegaGen Ω) (habel : Sec7.EtaAbelian Ω)
    (h611 : Sec7.EtaMeets Ω) {S : Sylow 2 G} {K : Subgroup G} (hK : K ∈ Ω)
    (hKS : 2 < Nat.card ↥(K ⊓ (S : Subgroup G))) :
    Sec7.etaGenIn Ω (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
  iSup₂_le fun _ ⟨_, hγ, hU⟩ => le_normalizer_of_mem_etaGIn hΩ habel h611 hγ hU hK hKS

theorem false_of_mem_etaGIn_of_not_mem (hΩ : HypOmegaGen Ω) (habel : Sec7.EtaAbelian Ω)
    (h611 : Sec7.EtaMeets Ω) (htr : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    {S : Sylow 2 G} {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hK₀S : 2 < Nat.card ↥(K₀ ⊓ (S : Subgroup G))) (hK₀R : K₀ ⊓ (S : Subgroup G) ∉ RSet Ω)
    {η β : Set (Subgroup G)} (hη : η ∈ Sec7.etaGIn Ω (S : Subgroup G))
    (hβ : β ∈ Sec7.etaGIn Ω (S : Subgroup G)) {X : Subgroup G} (hXη : X ∈ η) (hXβ : X ∉ β) :
    False := by
  have hXU := Sec7.mem_USet_of_mem_etaG hη.1 hXη
  obtain ⟨L, hL, hXL⟩ := Sec6Gen.exists_member_of_mem_USet hΩ hXU
  obtain ⟨-, -, -, -, -, -, -, -, hX4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hXU
  have hXS : X ≤ (S : Subgroup G) := hη.2 X hXη
  have hLS : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hXL hXS)
    omega
  have hYβ : L ⊓ (⨆ V ∈ β, V) ∈ β := h611 S β hβ.1 hβ.2 L hL hLS
  have hYU := Sec7.mem_USet_of_mem_etaG hβ.1 hYβ
  have hXY : X ≠ L ⊓ (⨆ V ∈ β, V) := fun h => hXβ (h ▸ hYβ)
  have hYS : L ⊓ (⨆ V ∈ β, V) ≤ (S : Subgroup G) := hβ.2 _ hYβ
  have h2 : IsPGroup 2 ↥(X ⊔ L ⊓ (⨆ V ∈ β, V)) := S.isPGroup'.to_le (sup_le hXS hYS)
  have hRL : IsSylow2In (X ⊔ L ⊓ (⨆ V ∈ β, V)) L :=
    isSylow2In_sup_of_ne hΩ hL hXU hYU hXL inf_le_left hXY h2
  have hRM : X ⊔ L ⊓ (⨆ V ∈ β, V) ≤ Sec7.etaGenIn Ω (S : Subgroup G) :=
    sup_le (Sec7.le_etaGenIn hη hXη) (Sec7.le_etaGenIn hβ hYβ)
  have hNK₀ := etaGenIn_le_normalizer hΩ habel h611 hK₀ hK₀S
  have hNL := etaGenIn_le_normalizer hΩ habel h611 hL hLS
  obtain ⟨g, hg⟩ := htr L hL K₀ hK₀
  have hWC := Sec7.weaklyClosedIn_etaGenIn hΩ.conjInvariant (S : Subgroup G)
  have hgM : conjSub g⁻¹ (Sec7.etaGenIn Ω (S : Subgroup G)) ≤
      Subgroup.normalizer (L : Set G) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    have h1 := hNK₀ hx
    rw [← hg, mem_normalizer_conjSub_iff] at h1
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h1
  obtain ⟨c, hc, hcM⟩ := hWC.exists_mem_mul (Sec7.isPGroup_etaGenIn S) hNL hgM
  have hnK₀ : conjSub (c * g⁻¹) K₀ = L := by
    rw [conjSub_mul, ← hg, conjSub_inv_conjSub]
    exact mem_normalizer_iff_conjSub_eq.mp hc
  have hnK₀' : conjSub (c * g⁻¹)⁻¹ L = K₀ := by
    rw [← hnK₀, conjSub_inv_conjSub]
  have hnM : conjSub (c * g⁻¹)⁻¹ (Sec7.etaGenIn Ω (S : Subgroup G)) =
      Sec7.etaGenIn Ω (S : Subgroup G) :=
    Sec7.conjSub_inv_eq hcM
  have hle : conjSub (c * g⁻¹)⁻¹ (X ⊔ L ⊓ (⨆ V ∈ β, V)) ≤ K₀ ⊓ (S : Subgroup G) := by
    refine le_inf ?_ ?_
    · rw [← hnK₀']
      exact conjSub_mono hRL.1
    · exact (conjSub_mono hRM).trans (hnM.le.trans (Sec7.etaGenIn_le _))
  have hsyl := hRL.conj (c * g⁻¹)⁻¹
  rw [hnK₀'] at hsyl
  have heq := hsyl.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left hle
  rw [← heq] at hsyl
  exact hK₀R (mem_RSet_of_isSylow2In hK₀ hsyl)

theorem eq_of_mem_etaGIn (hΩ : HypOmegaGen Ω) (habel : Sec7.EtaAbelian Ω)
    (h611 : Sec7.EtaMeets Ω) (htr : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    {S : Sylow 2 G} {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hK₀S : 2 < Nat.card ↥(K₀ ⊓ (S : Subgroup G))) (hK₀R : K₀ ⊓ (S : Subgroup G) ∉ RSet Ω)
    {η β : Set (Subgroup G)} (hη : η ∈ Sec7.etaGIn Ω (S : Subgroup G))
    (hβ : β ∈ Sec7.etaGIn Ω (S : Subgroup G)) : η = β := by
  by_contra hne
  by_cases h1 : η ⊆ β
  · obtain ⟨Y, hYβ, hYη⟩ := Set.not_subset.mp fun h2 => hne (Set.Subset.antisymm h1 h2)
    exact false_of_mem_etaGIn_of_not_mem hΩ habel h611 htr hK₀ hK₀S hK₀R hβ hη hYβ hYη
  · obtain ⟨X, hXη, hXβ⟩ := Set.not_subset.mp h1
    exact false_of_mem_etaGIn_of_not_mem hΩ habel h611 htr hK₀ hK₀S hK₀R hη hβ hXη hXβ

theorem l6_12_on (hΩ : HypOmegaGen Ω) (hex : Sec7.EtaExists Ω) (habel : Sec7.EtaAbelian Ω)
    (h611 : Sec7.EtaMeets Ω) (htr : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (S : Sylow 2 G) :
    let M : Subgroup G := ⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧
      U ≤ (S : Subgroup G)}, U
    (∃ η ∈ etaG Ω, (∀ m ∈ M, ∀ U ∈ η, conjSub m U ∈ η) ∧
      (∀ η' ∈ etaG Ω, (∀ m ∈ M, ∀ U ∈ η', conjSub m U ∈ η') → η' = η) ∧
      ∀ g : G, (∀ U ∈ η, conjSub g U ≤ (S : Subgroup G)) → ∀ U ∈ η, conjSub g U ∈ η) ∨
    ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (S : Subgroup G) ∈ RSet Ω := by
  intro M
  by_cases h2 : ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (S : Subgroup G) ∈ RSet Ω
  · exact Or.inr h2
  left
  push Not at h2
  obtain ⟨K₀, hK₀, hK₀S, hK₀R⟩ := h2
  have huniq : ∀ η ∈ Sec7.etaGIn Ω (S : Subgroup G), ∀ β ∈ Sec7.etaGIn Ω (S : Subgroup G),
      η = β :=
    fun η hη β hβ => eq_of_mem_etaGIn hΩ habel h611 htr hK₀ hK₀S hK₀R hη hβ
  have hcinv := hΩ.conjInvariant
  obtain ⟨η₀, hη₀S, hinv⟩ := hex S
  have hη₀G : η₀ ∈ etaG Ω := ⟨S, hη₀S, hinv⟩
  have hη₀ : η₀ ∈ Sec7.etaGIn Ω (S : Subgroup G) := ⟨hη₀G, fun V hV => (hη₀S.1 hV).2⟩
  have hMS : M ≤ (S : Subgroup G) := iSup₂_le fun U hU => hU.2
  have hMAM : Sec7.etaGenIn Ω (S : Subgroup G) ≤ M := iSup₂_le fun U ⟨γ, hγ, hU⟩ =>
    le_iSup₂_of_le (f := fun U (_ : U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧
      U ≤ (S : Subgroup G)}) => U) U ⟨⟨γ, hγ.1, hU⟩, hγ.2 U hU⟩ le_rfl
  have hWC := Sec7.weaklyClosedIn_etaGenIn hcinv (S : Subgroup G)
  refine ⟨η₀, hη₀G, fun m hm U hU => hinv m (hMS hm) U hU, ?_, ?_⟩
  · intro η' hη' hM'
    obtain ⟨S', hS'⟩ := Sec7.exists_sylow_of_mem_etaG hη'
    have hW'2 : IsPGroup 2 ↥(⨆ U ∈ η', U) := S'.isPGroup'.to_le (iSup₂_le hS')
    have hMN : Sec7.etaGenIn Ω (S : Subgroup G) ≤
        Subgroup.normalizer ((⨆ U ∈ η', U : Subgroup G) : Set G) := by
      intro m hm
      rw [mem_normalizer_iff_conjSub_eq]
      refine Sec7.conjSub_eq_of_le_self ?_
      rw [conjSub_le_iff]
      refine iSup₂_le fun U hU => ?_
      rw [← conjSub_le_iff]
      exact le_iSup₂_of_le (f := fun V (_ : V ∈ η') => V) _ (hM' m (hMAM hm) U hU) le_rfl
    have hP : IsPGroup 2 ↥(Sec7.etaGenIn Ω (S : Subgroup G) ⊔ ⨆ U ∈ η', U) :=
      IsPGroup.to_sup_of_normal_right' (Sec7.isPGroup_etaGenIn S) hW'2 hMN
    obtain ⟨S₁, hS₁⟩ := hP.exists_le_sylow
    obtain ⟨h, hh⟩ := exists_conjSub_eq_of_sylow S S₁
    have hMh : conjSub h⁻¹ (Sec7.etaGenIn Ω (S : Subgroup G)) =
        Sec7.etaGenIn Ω (S : Subgroup G) :=
      hWC _ (by rw [conjSub_le_iff, inv_inv, hh]; exact le_sup_left.trans hS₁)
    have hβ : conjSub h⁻¹ '' η' ∈ Sec7.etaGIn Ω (S : Subgroup G) := by
      refine ⟨Sec7.etaG_conj hcinv hη' h⁻¹, ?_⟩
      rintro _ ⟨U, hU, rfl⟩
      rw [conjSub_le_iff, inv_inv, hh]
      exact (le_iSup₂_of_le (f := fun V (_ : V ∈ η') => V) U hU le_rfl).trans
        (le_sup_right.trans hS₁)
    have h1 : conjSub h⁻¹ '' η' = η₀ := huniq _ hβ _ hη₀
    have h2 : η' = conjSub h '' η₀ := by
      rw [← h1, Set.image_image]
      simp only [conjSub_conjSub_inv, Set.image_id']
    have hMh' : conjSub h (Sec7.etaGenIn Ω (S : Subgroup G)) =
        Sec7.etaGenIn Ω (S : Subgroup G) := by
      simpa using Sec7.conjSub_inv_eq hMh
    have h3 : conjSub h '' η₀ ∈ Sec7.etaGIn Ω (S : Subgroup G) :=
      Sec7.image_conj_mem_etaGIn hcinv hη₀ fun V hV =>
        (conjSub_mono (Sec7.le_etaGenIn hη₀ hV)).trans (hMh'.le.trans (Sec7.etaGenIn_le _))
    rw [h2]
    exact huniq _ h3 _ hη₀
  · intro g hg U hU
    have h1 : conjSub g '' η₀ ∈ Sec7.etaGIn Ω (S : Subgroup G) :=
      Sec7.image_conj_mem_etaGIn hcinv hη₀ hg
    have h2 : conjSub g U ∈ conjSub g '' η₀ := ⟨U, hU, rfl⟩
    rwa [huniq _ h1 _ hη₀] at h2

end CFSG.ClassicalInvolution.Q3.Q3T6.Gen612
