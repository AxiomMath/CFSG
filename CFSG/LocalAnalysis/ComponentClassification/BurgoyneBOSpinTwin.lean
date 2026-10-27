module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOOddLift
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank QuadraticMap
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL slRingEquiv
  conj_injective_of_mulEquiv)
open CFSG.LieType.Universal.Spin CliffordAlgebra
open scoped MatrixGroups

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]

theorem mem_twin_sup_of_spin {L₀ : Type} [Field L₀] [Finite L₀] (hK : ringChar L₀ ≠ 2)
    (hK5 : 5 ≤ Nat.card L₀) {d : ℕ} (hd5 : 5 ≤ d) {w : Fin d → L₀} (hw : ∀ i, w i ≠ 0)
    {α a : L₀} (hW : OSliceW (by omega : 4 ≤ d) w α a) {σ : Type} [Fintype σ] [DecidableEq σ]
    (e : σ ≃ Fin d) (Q₀ : QuadraticForm L₀ (σ → L₀)) {Q0 : (σ → L₀) → L₀} (hQ : ⇑Q₀ = Q0)
    (hRs : (spinMatrix Q₀).range = StatedOmega Q0)
    (hsurjS : Function.Surjective (spinToStatedProj Q₀ hRs)) [Finite (spinGroup Q₀)]
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* spinGroup Q₀),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : spinGroup Q₀ →* E, ∀ x, π (s x) = x)
    {Q₁ : QuadraticForm L₀ (Fin d → L₀)} (S₁ : GL (Fin d) L₀) (ν₁ : L₀ˣ)
    (hS₁ : ∀ v, Q₁ (S₁.val *ᵥ v) = ν₁ * reindexQuadraticForm e Q₀ v)
    (S₂ : GL (Fin d) L₀) (ν₂ : L₀ˣ) (hS₂ : ∀ v, oQ (diagGL hw) (S₂.val *ᵥ v) = ν₂ * Q₁ v)
    (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
    (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* StatedProj (matrixDerived (oQ (diagGL hw))))
    (hQne : Q₀ ≠ 0) {c : K ⧸ pPrimeCore 2 K}
    (hc : ∀ α' : spinGroup Q₀ →* K ⧸ pPrimeCore 2 K, Function.Surjective α' →
      c = α' (spinGroup.negOne Q₀ hQne)) :
    c ∈ ⁅((slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ)).comap (liftHom K),
        ((slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ)).comap (liftHom K)⁆ ⊔
      ⁅((slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ)).comap (liftHom K),
        ((slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ)).comap (liftHom K)⁆ := by
  have h2 : (2 : L₀) ≠ 0 := Ring.two_ne_zero hK
  have hψ := socleAction_injective hsimple hnab θ
  have hrange := liftHom_range_eq K hq hsimple hnab
  have hsocle := mem_socle_iff hsimple hnab θ
  let Θ := (statedProjectiveReindexEquiv e Q₀ hQ).trans
    ((oTransport S₁ ν₁ hS₁).trans (oTransport S₂ ν₂ hS₂))
  let fS : spinGroup Q₀ →* MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))) :=
    (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).comp
        (Θ.toMonoidHom.comp (spinToStatedProj Q₀ hRs))
  have hfS : ∀ x, fS x = MulAut.conj (Θ (spinToStatedProj Q₀ hRs x)) := fun _ => rfl
  have hfSr : ∀ x, fS x ∈ (socleAction θ).range := fun x => conj_mem_range_socleAction θ _
  let β : spinGroup Q₀ →* (rhoZ K).range := factorHom hψ fS hfSr
  have hβ : ∀ g, socleAction θ (β g) = fS g := factorHom_spec hψ fS hfSr
  have hβr : β.range = (liftHom K).range := by
    rw [hrange]
    ext x
    rw [hsocle]
    constructor
    · rintro ⟨g, rfl⟩
      rw [hβ, hfS]
      exact ⟨_, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := Θ.surjective y
      obtain ⟨g, rfl⟩ := hsurjS z
      refine ⟨g, hψ ?_⟩
      rw [hβ, hfS]
      exact hy
  obtain ⟨α', hαβ, hαs, -⟩ := exists_cover K hsplit hq hβr
  have hcα := hc α' hαs
  obtain ⟨R₁, R₂, hneg, hR₁, hR₂⟩ := spin_slices_bridge h2 (by omega) hd5 hw hW e Q₀ hQ hRs
    S₁ ν₁ hS₁ S₂ ν₂ hS₂
  have hnegmem : spinGroup.negOne Q₀ hQne ∈ R₁.range ⊔ R₂.range := by
    have : spinGroup.negOne Q₀ hQne = R₁ (-1) * R₂ (-1) :=
      Subtype.ext (by rw [hneg, spinGroup.coe_negOne])
    rw [this]
    exact mul_mem (mem_sup_left ⟨-1, rfl⟩) (mem_sup_right ⟨-1, rfl⟩)
  have hperf : Group.IsPerfect SL(2, L₀) := CatalogueBGeneralLinear.specialLinear_perfect 2 L₀
    le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have hβ₁ : ∀ g ∈ R₁.range, β g ∈ (slice (twinL hK hK5 hd5 hw hW)).comap (socleAction θ) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_comap, hβ, hfS]
    obtain ⟨x', hx'⟩ := hR₁ x
    rw [hx']
    exact ⟨_, ⟨x', rfl⟩, rfl⟩
  have hβ₂ : ∀ g ∈ R₂.range, β g ∈ (slice (twinR hK hK5 hd5 hw hW)).comap (socleAction θ) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_comap, hβ, hfS]
    obtain ⟨x', hx'⟩ := hR₂ x
    rw [hx']
    exact ⟨_, ⟨x', rfl⟩, rfl⟩
  have hcT := map_mem_sup_of_cover (liftHom K) α' hαβ (commutator_range_of_perfect hperf R₁)
    (commutator_range_of_perfect hperf R₂) hβ₁ hβ₂ hnegmem
  rwa [← hcα] at hcT

theorem propB_of_twinSliceData {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {p' f' : ℕ} [Fact p'.Prime] (hp2' : p' ≠ 2) {L₀ : Type}
    [Field L₀] [Finite L₀] (hK : ringChar L₀ ≠ 2) (hKc : Nat.card L₀ = p' ^ f') {d : ℕ}
    {R : GL (Fin d) L₀}
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* StatedProj (matrixDerived (oQ R)))
    (hT : 5 ≤ Nat.card L₀ ∧ TwinSliceData (Ring.two_ne_zero hK) θ ((rhoZ K).rangeRestrict t))
    {σ : Type} [Fintype σ] [DecidableEq σ] (e : σ ≃ Fin d) (Q₀ : QuadraticForm L₀ (σ → L₀))
    {Q0 : (σ → L₀) → L₀} (hQ : ⇑Q₀ = Q0) (hRs : (spinMatrix Q₀).range = StatedOmega Q0)
    (hsurjS : Function.Surjective (spinToStatedProj Q₀ hRs)) [Finite (spinGroup Q₀)]
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* spinGroup Q₀),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : spinGroup Q₀ →* E, ∀ x, π (s x) = x)
    (S₁ : GL (Fin d) L₀) (ν₁ : L₀ˣ)
    (hS₁ : ∀ v, oQ R (S₁.val *ᵥ v) = ν₁ * reindexQuadraticForm e Q₀ v) (hQne : Q₀ ≠ 0)
    (hc : ∀ α' : spinGroup Q₀ →* K ⧸ pPrimeCore 2 K, Function.Surjective α' →
      c = α' (spinGroup.negOne Q₀ hQne)) :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ := by
  obtain ⟨hq, hM4, -, hY1, hY2, -, -, -, -, -, -, -, -, hcZ, -, hc2, -⟩ := id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  obtain ⟨hK5, hd5, w, hw, α, a, hW, S, ν, hS, hker', hψ't, hcore'⟩ := hT
  obtain ⟨ū, hū, ⟨f₁⟩, ⟨f₂⟩, hcomm, hū₁, hū₂, hint', hs₁, hs₁s, hs₂, hs₂s, hprop₁', hprop₂'⟩ :=
    odd_twin_comap hK hK5 hd5 hw hW hker' hsimple hnab (θ.trans (oTransport S ν hS)) hψ't hcore'
      hY1 hY2 hKc
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hcT := mem_twin_sup_of_spin K hK hK5 hd5 hw hW e Q₀ hQ hRs hsurjS hsplit S₁ ν₁ hS₁
    S ν hS hq hsimple hnab (θ.trans (oTransport S ν hS)) hQne hc
  have hrange := liftHom_range_eq K hq hsimple hnab
  have hSr : ∀ {L : Subgroup (matrixDerived (oQ (diagGL hw)))},
      (slice L).comap (socleAction (θ.trans (oTransport S ν hS))) ≤ (liftHom K).range := by
    intro L g hg
    rw [hrange, mem_socle_iff hsimple hnab (θ.trans (oTransport S ν hS))]
    exact slice_le_range hg
  have h5 : 5 ≤ p' ^ f' := by rw [← hKc]; exact hK5
  exact propB_of_twin K hq hSr hSr hp2' h5 f₁ f₂ hcomm hū hū₁ hū₂ hint' hs₁ hs₁s hs₂ hs₂s
    hprop₁' hprop₂' hcZ hc1 hcT

end CFSG.ComponentClassification.Burgoyne.B
