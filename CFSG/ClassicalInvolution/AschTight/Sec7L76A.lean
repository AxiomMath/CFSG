module

public import CFSG.ClassicalInvolution.AschTight.Sec7L612A

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem isPGroup_of_mem_WSet {W : Subgroup G} (hW : W ∈ WSet Ω) : IsPGroup 2 W := by
  obtain ⟨η, hη, rfl⟩ := hW
  obtain ⟨S, hS⟩ := exists_sylow_of_mem_etaG hη
  exact S.isPGroup'.to_le (iSup₂_le hS)

omit [Finite G] in
theorem isPGroup_of_mem_RSet {R : Subgroup G} (hR : R ∈ RSet Ω) : IsPGroup 2 R := by
  obtain ⟨J, -, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  exact hRJ.2.1

theorem control_centralizer_of_weaklyClosed {W : Subgroup G} {S : Sylow 2 G}
    (hW2 : IsPGroup 2 W) (hWC : WeaklyClosedIn W S) {x : G}
    (hx : x ∈ Subgroup.centralizer (W : Set G)) {g : G}
    (hgx : g * x * g⁻¹ ∈ Subgroup.centralizer (W : Set G)) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), n * x * n⁻¹ = g * x * g⁻¹ := by
  have hWH : W ≤ Subgroup.centralizer ({g * x * g⁻¹} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hgx) w hw)
  have hgW : conjSub g W ≤ Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
    intro v hv
    rw [mem_conjSub_iff] at hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g⁻¹ * v * g * x = x * (g⁻¹ * v * g) := (Subgroup.mem_centralizer_iff.mp hx) _ hv
    calc v * (g * x * g⁻¹) = g * (g⁻¹ * v * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * v := by group
  obtain ⟨c, hc, hcW⟩ := hWC.exists_mem_mul hW2 hWH hgW
  refine ⟨c * g, mem_normalizer_iff_conjSub_eq.mpr hcW, ?_⟩
  have hc' : c * (g * x * g⁻¹) = g * x * g⁻¹ * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  calc c * g * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ := by group
    _ = g * x * g⁻¹ := by rw [hc']; group

theorem le_normalizer_of_mem_DSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (habel : EtaAbelian Ω) (h611 : EtaMeets Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R K : Subgroup G} (hR : R ∈ DSet Ω W) (hK : K ∈ Ω) (hRK : R ≤ K) :
    W ≤ Subgroup.normalizer (K : Set G) := by
  have hW2 := isPGroup_of_mem_WSet hW
  obtain ⟨η, hη, rfl⟩ := hW
  have hRW : IsPGroup 2 ↥(R ⊔ ⨆ U ∈ η, U) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_of_mem_RSet hR.1) hW2 hR.2
  obtain ⟨S₁, hS₁⟩ := hRW.exists_le_sylow
  have hγ : η ∈ etaGIn Ω (S₁ : Subgroup G) :=
    ⟨hη, fun V hV => (le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) V hV le_rfl).trans
      (le_sup_right.trans hS₁)⟩
  have hKS : 2 < Nat.card ↥(K ⊓ (S₁ : Subgroup G)) := by
    have h8 := hΩ.eight_le_of_mem_RSet hp hR.1
    have := Subgroup.card_le_of_le (le_inf hRK (le_sup_left.trans hS₁))
    omega
  exact iSup₂_le fun U hU => le_normalizer_of_mem_etaGIn hp hq hΩ habel h611 hγ hU hK hKS

omit [Finite G] in
theorem conjSub_le_normalizer {A K : Subgroup G} (h : A ≤ Subgroup.normalizer (K : Set G))
    (g : G) : conjSub g A ≤ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  rw [mem_normalizer_conjSub_iff]
  exact h hx

theorem control_DSet_of_weaklyClosed (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (habel : EtaAbelian Ω) (h611 : EtaMeets Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {S : Sylow 2 G} (hWC : WeaklyClosedIn W S) {R T : Subgroup G} (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) {g : G} (hg : conjSub g R = T) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), conjSub n R = T := by
  have hW2 := isPGroup_of_mem_WSet hW
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT.1
  have hT2 := hTJ.2.1
  have h8 := hΩ.eight_le_of_mem_RSet hp hT.1
  have hgK : conjSub g K = J := by
    refine hΩ.eq_of_le_of_le (hΩ.conjInvariant g K hK) hJ hT2 (by omega) ?_ hTJ.1
    rw [← hg]
    exact conjSub_mono hRK.1
  have hWK := le_normalizer_of_mem_DSet hp hq hΩ habel h611 hW hR hK hRK.1
  have hWJ := le_normalizer_of_mem_DSet hp hq hΩ habel h611 hW hT hJ hTJ.1
  have hgWJ : conjSub g W ≤ Subgroup.normalizer (J : Set G) := by
    rw [← hgK]
    exact conjSub_le_normalizer hWK g
  have hTgW : T ≤ Subgroup.normalizer ((conjSub g W : Subgroup G) : Set G) := by
    rw [← hg]
    exact conjSub_le_normalizer hR.2 g
  have h1 : IsPGroup 2 ↥(W ⊔ T) := IsPGroup.to_sup_of_normal_left' hW2 hT2 hT.2
  have h2 : IsPGroup 2 ↥(conjSub g W ⊔ T) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_conjSub g hW2) hT2 hTgW
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hTJ.1.trans Subgroup.le_normalizer
  obtain ⟨P, hP, hWTP⟩ := IsSylow2In.exists_ge h1 (sup_le hWJ hTN)
  obtain ⟨c, hc, hcP⟩ := exists_conj_le_of_isSylow2In hP h2 (sup_le hgWJ hTN)
  have hPJ : P ⊓ J = T :=
    hTJ.eq_of_le (hP.2.1.to_le inf_le_left) inf_le_right (le_inf (le_sup_right.trans hWTP) hTJ.1)
  have hcJ : conjSub c J = J := mem_normalizer_iff_conjSub_eq.mp hc
  have hTc : T ≤ conjSub c T := by
    have h3 : T ≤ conjSub c (P ⊓ J) := by
      rw [conjSub_inf, hcJ]
      exact le_inf (le_sup_right.trans hcP) hTJ.1
    rwa [hPJ] at h3
  have hcT : conjSub c T = T := conjSub_eq_of_le_self' hTc
  have hcW : conjSub (c⁻¹ * g) W = W := by
    refine hWC.eq_of_le_of_isPGroup hP.2.1 (le_sup_left.trans hWTP) ?_
    rw [conjSub_mul, conjSub_le_iff, inv_inv]
    exact le_sup_left.trans hcP
  refine ⟨c⁻¹ * g, mem_normalizer_iff_conjSub_eq.mpr hcW, ?_⟩
  rw [conjSub_mul, hg]
  exact conjSub_inv_eq hcT

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
