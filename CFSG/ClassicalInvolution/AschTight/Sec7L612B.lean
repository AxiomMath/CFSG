module

public import CFSG.ClassicalInvolution.AschTight.Sec7L612A
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem false_of_mem_etaGIn_of_not_mem (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (habel : EtaAbelian Ω) (h611 : EtaMeets Ω)
    (htr : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) {S : Sylow 2 G} {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ Ω) (hK₀S : 2 < Nat.card ↥(K₀ ⊓ (S : Subgroup G)))
    (hK₀R : K₀ ⊓ (S : Subgroup G) ∉ RSet Ω) {η β : Set (Subgroup G)}
    (hη : η ∈ etaGIn Ω (S : Subgroup G)) (hβ : β ∈ etaGIn Ω (S : Subgroup G)) {X : Subgroup G}
    (hXη : X ∈ η) (hXβ : X ∉ β) : False := by
  have hXU := mem_USet_of_mem_etaG hη.1 hXη
  obtain ⟨L, hL, hXL⟩ := hΩ.exists_member_of_mem_USet hp hXU
  obtain ⟨-, -, -, -, -, -, -, -, hX4⟩ := hΩ.exists_data_of_mem_USet hp hXU
  have hXS : X ≤ (S : Subgroup G) := hη.2 X hXη
  have hLS : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hXL hXS)
    omega
  have hYβ : L ⊓ (⨆ V ∈ β, V) ∈ β := h611 S β hβ.1 hβ.2 L hL hLS
  have hYU := mem_USet_of_mem_etaG hβ.1 hYβ
  have hXY : X ≠ L ⊓ (⨆ V ∈ β, V) := fun h => hXβ (h ▸ hYβ)
  have hYS : L ⊓ (⨆ V ∈ β, V) ≤ (S : Subgroup G) := hβ.2 _ hYβ
  have h2 : IsPGroup 2 ↥(X ⊔ L ⊓ (⨆ V ∈ β, V)) := S.isPGroup'.to_le (sup_le hXS hYS)
  have hRL : IsSylow2In (X ⊔ L ⊓ (⨆ V ∈ β, V)) L :=
    isSylow2In_sup_of_ne hp hΩ hL hXU hYU hXL inf_le_left hXY h2
  have hRM : X ⊔ L ⊓ (⨆ V ∈ β, V) ≤ etaGenIn Ω (S : Subgroup G) :=
    sup_le (le_etaGenIn hη hXη) (le_etaGenIn hβ hYβ)
  have hNK₀ := etaGenIn_le_normalizer hp hq hΩ habel h611 hK₀ hK₀S
  have hNL := etaGenIn_le_normalizer hp hq hΩ habel h611 hL hLS
  obtain ⟨g, hg⟩ := htr L hL K₀ hK₀
  have hWC := weaklyClosedIn_etaGenIn hΩ.conjInvariant (S : Subgroup G)
  have hgM : conjSub g⁻¹ (etaGenIn Ω (S : Subgroup G)) ≤ Subgroup.normalizer (L : Set G) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    have h1 := hNK₀ hx
    rw [← hg, mem_normalizer_conjSub_iff] at h1
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h1
  obtain ⟨c, hc, hcM⟩ := hWC.exists_mem_mul (isPGroup_etaGenIn S) hNL hgM
  have hnK₀ : conjSub (c * g⁻¹) K₀ = L := by
    rw [conjSub_mul, ← hg, conjSub_inv_conjSub]
    exact mem_normalizer_iff_conjSub_eq.mp hc
  have hnK₀' : conjSub (c * g⁻¹)⁻¹ L = K₀ := by
    rw [← hnK₀, conjSub_inv_conjSub]
  have hnM : conjSub (c * g⁻¹)⁻¹ (etaGenIn Ω (S : Subgroup G)) = etaGenIn Ω (S : Subgroup G) :=
    conjSub_inv_eq hcM
  have hle : conjSub (c * g⁻¹)⁻¹ (X ⊔ L ⊓ (⨆ V ∈ β, V)) ≤ K₀ ⊓ (S : Subgroup G) := by
    refine le_inf ?_ ?_
    · rw [← hnK₀']
      exact conjSub_mono hRL.1
    · exact (conjSub_mono hRM).trans (hnM.le.trans (etaGenIn_le _))
  have hsyl := hRL.conj (c * g⁻¹)⁻¹
  rw [hnK₀'] at hsyl
  have heq := hsyl.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left hle
  rw [← heq] at hsyl
  exact hK₀R (mem_RSet_of_isSylow2In hK₀ hsyl)

theorem eq_of_mem_etaGIn (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (habel : EtaAbelian Ω) (h611 : EtaMeets Ω)
    (htr : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) {S : Sylow 2 G} {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ Ω) (hK₀S : 2 < Nat.card ↥(K₀ ⊓ (S : Subgroup G)))
    (hK₀R : K₀ ⊓ (S : Subgroup G) ∉ RSet Ω) {η β : Set (Subgroup G)}
    (hη : η ∈ etaGIn Ω (S : Subgroup G)) (hβ : β ∈ etaGIn Ω (S : Subgroup G)) : η = β := by
  by_contra hne
  by_cases h1 : η ⊆ β
  · obtain ⟨Y, hYβ, hYη⟩ := Set.not_subset.mp fun h2 => hne (Set.Subset.antisymm h1 h2)
    exact false_of_mem_etaGIn_of_not_mem hp hq hΩ habel h611 htr hK₀ hK₀S hK₀R hβ hη hYβ hYη
  · obtain ⟨X, hXη, hXβ⟩ := Set.not_subset.mp h1
    exact false_of_mem_etaGIn_of_not_mem hp hq hΩ habel h611 htr hK₀ hK₀S hK₀R hη hβ hXη hXβ

theorem l6_12_on (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (hex : EtaExists Ω)
    (habel : EtaAbelian Ω) (h611 : EtaMeets Ω)
    (htr : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (S : Sylow 2 G) :
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
  have huniq : ∀ η ∈ etaGIn Ω (S : Subgroup G), ∀ β ∈ etaGIn Ω (S : Subgroup G), η = β :=
    fun η hη β hβ => eq_of_mem_etaGIn hp hq hΩ habel h611 htr hK₀ hK₀S hK₀R hη hβ
  have hcinv := hΩ.conjInvariant
  obtain ⟨η₀, hη₀S, hinv⟩ := hex S
  have hη₀G : η₀ ∈ etaG Ω := ⟨S, hη₀S, hinv⟩
  have hη₀ : η₀ ∈ etaGIn Ω (S : Subgroup G) := ⟨hη₀G, fun V hV => (hη₀S.1 hV).2⟩
  have hMS : M ≤ (S : Subgroup G) := iSup₂_le fun U hU => hU.2
  have hMAM : etaGenIn Ω (S : Subgroup G) ≤ M := iSup₂_le fun U ⟨γ, hγ, hU⟩ =>
    le_iSup₂_of_le (f := fun U (_ : U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧
      U ≤ (S : Subgroup G)}) => U) U ⟨⟨γ, hγ.1, hU⟩, hγ.2 U hU⟩ le_rfl
  have hWC := weaklyClosedIn_etaGenIn hcinv (S : Subgroup G)
  refine ⟨η₀, hη₀G, fun m hm U hU => hinv m (hMS hm) U hU, ?_, ?_⟩
  · intro η' hη' hM'
    obtain ⟨S', hS'⟩ := exists_sylow_of_mem_etaG hη'
    have hW'2 : IsPGroup 2 ↥(⨆ U ∈ η', U) := S'.isPGroup'.to_le (iSup₂_le hS')
    have hMN : etaGenIn Ω (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η', U : Subgroup G) :
        Set G) := by
      intro m hm
      rw [mem_normalizer_iff_conjSub_eq]
      refine conjSub_eq_of_le_self ?_
      rw [conjSub_le_iff]
      refine iSup₂_le fun U hU => ?_
      rw [← conjSub_le_iff]
      exact le_iSup₂_of_le (f := fun V (_ : V ∈ η') => V) _ (hM' m (hMAM hm) U hU) le_rfl
    have hP : IsPGroup 2 ↥(etaGenIn Ω (S : Subgroup G) ⊔ ⨆ U ∈ η', U) :=
      IsPGroup.to_sup_of_normal_right' (isPGroup_etaGenIn S) hW'2 hMN
    obtain ⟨S₁, hS₁⟩ := hP.exists_le_sylow
    obtain ⟨h, hh⟩ := exists_conjSub_eq_of_sylow S S₁
    have hMh : conjSub h⁻¹ (etaGenIn Ω (S : Subgroup G)) = etaGenIn Ω (S : Subgroup G) :=
      hWC _ (by rw [conjSub_le_iff, inv_inv, hh]; exact le_sup_left.trans hS₁)
    have hβ : conjSub h⁻¹ '' η' ∈ etaGIn Ω (S : Subgroup G) := by
      refine ⟨etaG_conj hcinv hη' h⁻¹, ?_⟩
      rintro _ ⟨U, hU, rfl⟩
      rw [conjSub_le_iff, inv_inv, hh]
      exact (le_iSup₂_of_le (f := fun V (_ : V ∈ η') => V) U hU le_rfl).trans
        (le_sup_right.trans hS₁)
    have h1 : conjSub h⁻¹ '' η' = η₀ := huniq _ hβ _ hη₀
    have h2 : η' = conjSub h '' η₀ := by
      rw [← h1, Set.image_image]
      simp only [conjSub_conjSub_inv, Set.image_id']
    have hMh' : conjSub h (etaGenIn Ω (S : Subgroup G)) = etaGenIn Ω (S : Subgroup G) := by
      simpa using conjSub_inv_eq hMh
    have h3 : conjSub h '' η₀ ∈ etaGIn Ω (S : Subgroup G) :=
      image_conj_mem_etaGIn hcinv hη₀ fun V hV =>
        (conjSub_mono (le_etaGenIn hη₀ hV)).trans (hMh'.le.trans (etaGenIn_le _))
    rw [h2]
    exact huniq _ h3 _ hη₀
  · intro g hg U hU
    have h1 : conjSub g '' η₀ ∈ etaGIn Ω (S : Subgroup G) := image_conj_mem_etaGIn hcinv hη₀ hg
    have h2 : conjSub g U ∈ conjSub g '' η₀ := ⟨U, hU, rfl⟩
    rwa [huniq _ h1 _ hη₀] at h2

variable (p f) in
theorem l6_12ModTmp_of
    (hex : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
      EtaExists Ω)
    (habel : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
      EtaAbelian Ω)
    (h611 : L6_11ModTmp p f) : L6_12ModTmp p f := by
  intro G _ _ Ω hΩ htr S
  exact l6_12_on hΩ.1 hΩ.2.1 hΩ.2.2.1 (hex G Ω hΩ) (habel G Ω hΩ) (h611 G Ω hΩ) htr S

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
