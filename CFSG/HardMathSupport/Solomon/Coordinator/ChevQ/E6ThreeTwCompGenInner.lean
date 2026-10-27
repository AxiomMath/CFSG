module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompHatInner
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2Conj

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KD4T
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Plane

theorem twExists_inner_plane_notMem_zpowers {K : Type} [Field K] {σ : K ≃+* K}
    {E P : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hEi : E ≤ twistedE6Inn K σ) (hPE : P ≤ E) (hPc : Nat.card P = 3 ^ 2)
    {ε : MulAut (twistedE6RootGroup K σ)} (hε : ε ∈ E) :
    ∃ v : twistedE6RootGroup K σ, MulAut.conj v ∈ P ∧ MulAut.conj v ∉ Subgroup.zpowers ε := by
  by_contra hno
  push Not at hno
  have hle : P ≤ Subgroup.zpowers ε := by
    intro ε' hε'
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.1 (hEi (hPE hε'))
    exact hno v hε'
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hPc, Nat.card_zpowers] at hdvd
  have h33 := Nat.dvd_trans hdvd (orderOf_dvd_of_pow_eq_one (hE.2 ε hε))
  norm_num at h33

end Plane

section Package

variable {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K} {ℓ f : ℕ} {hU : UnitaryFieldData ℓ f K}
  {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
  {Hc : Fin 3 → SL(3, AlgebraicClosure K)}
  {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
  {A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary hU (idGram K 3)}

theorem TwCompFrames.twMem_of_comm (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    (hl : TwE6ThreeA2Line K σ h₀ L T n) (hconj : TwE6ThreeA2ConjAt K σ)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3) {P : Subgroup (MulAut (twistedE6RootGroup K σ))} (hPE : P ≤ E)
    (hAll : TwE6InnerAll24 K σ P) {s : twistedE6RootGroup K σ}
    (hs : (s : ModGL TwistTag.E6.tag K) = h₀) (hsP : MulAut.conj s ∈ P)
    {v : twistedE6RootGroup K σ} (hvP : MulAut.conj v ∈ P)
    (hvs : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj s))
    (hvM : (v : ModGL TwistTag.E6.tag K) ∈ T ⊔ ⨆ i, L i) :
    n ∈ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔ (T ⊔ ⨆ i, L i) := by
  have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
  have hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hsE : MulAut.conj s ∈ E := hPE hsP
  have hvE : MulAut.conj v ∈ E := hPE hvP
  have hcm := F.twComm_mem_layer_inner hl hconj
  obtain ⟨τ, hτT, x, hvx⟩ := twM_exists_mul_layerProd hl F.range hvM
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀, ℓ₀ = n * τ * n⁻¹ * τ⁻¹ := ⟨_, rfl⟩
  have hℓ : ℓ₀ ∈ T ⊓ ⨆ i, L i := by
    rw [hℓ₀]
    exact hcm τ hτT
  obtain ⟨hℓT, hℓL⟩ := Subgroup.mem_inf.1 hℓ
  obtain ⟨x'', hx''⟩ := twLayer_exists_layerProd hl F.range
    (mul_mem hℓL ((hl.conj_mem_iSup _).1 (twLayerProd_mem F.range x)))
  have hc : ℓ₀ * τ = τ * ℓ₀ := hl.T_comm _ hℓT _ hτT
  have hv' : n * (τ * twLayerProd ρ x) * n⁻¹ = τ * twLayerProd ρ x'' := by
    calc n * (τ * twLayerProd ρ x) * n⁻¹ = ℓ₀ * τ * (n * twLayerProd ρ x * n⁻¹) := by
          rw [hℓ₀]; group
      _ = τ * ℓ₀ * (n * twLayerProd ρ x * n⁻¹) := by rw [hc]
      _ = τ * twLayerProd ρ x'' := by rw [mul_assoc τ ℓ₀, hx'']
  have hv3 : v ^ 3 = 1 := by
    apply CFSG.Fischer.mulAutConj_injective hZ
    rw [map_pow, map_one]
    exact hE.2 _ hvE
  have h3 : (τ * twLayerProd ρ x) ^ 3 = 1 := by
    rw [← hvx]
    exact congrArg Subtype.val hv3
  have h3'' : (τ * twLayerProd ρ x'') ^ 3 = 1 := by
    rw [← hv', conj_pow, h3, mul_one, mul_inv_cancel]
  have hnh : h₀ * n = n * h₀ :=
    twComp_comm_h₀ hl (Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
  have hd : ∀ k : ℕ, Module.finrank K (LinearMap.ker (((h₀ ^ k * (τ * twLayerProd ρ x) :
      ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 := by
    intro k
    rw [← hvx, ← hs]
    exact twFinrank_pow_mul_eq hAll hsP hvP hvs k
  have hd'' : ∀ k : ℕ, Module.finrank K (LinearMap.ker (((h₀ ^ k * (τ * twLayerProd ρ x'') :
      ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 := by
    intro k
    have hk : h₀ ^ k * n = n * h₀ ^ k := (Commute.pow_left hnh k).eq
    have e : h₀ ^ k * (τ * twLayerProd ρ x'') =
        n * (h₀ ^ k * (τ * twLayerProd ρ x)) * n⁻¹ := by
      rw [← hv']
      calc h₀ ^ k * (n * (τ * twLayerProd ρ x) * n⁻¹)
          = h₀ ^ k * n * (τ * twLayerProd ρ x) * n⁻¹ := by simp only [mul_assoc]
        _ = n * h₀ ^ k * (τ * twLayerProd ρ x) * n⁻¹ := by rw [hk]
        _ = n * (h₀ ^ k * (τ * twLayerProd ρ x)) * n⁻¹ := by simp only [mul_assoc]
    rw [e, finrank_ker_conj_sub_one]
    exact hd k
  obtain ⟨y, hy⟩ := F.twExists_layer_conj hl (F.twLe_torusHat hτT) h3 h3'' hd hd''
  have hcomm := twFrames_commute hl F.range
  obtain ⟨gC, hgC⟩ : ∃ g : twistedE6RootGroup K σ,
      (g : ModGL TwistTag.E6.tag K) = n⁻¹ * twLayerProd ρ y :=
    ⟨(⟨n, hl.n_mem⟩ : twistedE6RootGroup K σ)⁻¹ * commProd3 ρ hcomm y, rfl⟩
  have hgv : (gC : ModGL TwistTag.E6.tag K) * (v : ModGL TwistTag.E6.tag K) *
      (gC : ModGL TwistTag.E6.tag K)⁻¹ = (v : ModGL TwistTag.E6.tag K) := by
    rw [hgC, hvx]
    exact twConj_inv_mul_eq (hy.trans hv'.symm)
  have hgh : h₀ * (gC : ModGL TwistTag.E6.tag K) = (gC : ModGL TwistTag.E6.tag K) * h₀ := by
    rw [hgC]
    exact twComp_comm_h₀ hl (mul_mem (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers n)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (twLayerProd_mem F.range y))))
  have hσg : MulAut.conj s gC = gC := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    show (s : ModGL TwistTag.E6.tag K) * (gC : ModGL TwistTag.E6.tag K) *
      (s : ModGL TwistTag.E6.tag K)⁻¹ = (gC : ModGL TwistTag.E6.tag K)
    rw [hs]
    exact mul_inv_eq_iff_eq_mul.2 hgh
  have hvg : MulAut.conj v gC = gC := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    show (v : ModGL TwistTag.E6.tag K) * (gC : ModGL TwistTag.E6.tag K) *
      (v : ModGL TwistTag.E6.tag K)⁻¹ = (gC : ModGL TwistTag.E6.tag K)
    exact mul_inv_eq_iff_eq_mul.2 (mul_inv_eq_iff_eq_mul.1 hgv).symm
  have hgΓ : gC ∈ seitzHyperGamma 3 E :=
    mem_seitzHyperGamma_of_fixed hE hcard27 hsE hvE (twConj_ne_one hl hs) hvs hσg hvg
  have e : n = twLayerProd ρ y * (gC : ModGL TwistTag.E6.tag K)⁻¹ := by
    rw [hgC]
    group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_right (twLayerProd_mem F.range y)))
    (Subgroup.mem_sup_left (inv_mem ⟨gC, hgΓ, rfl⟩))

end Package

section Final

theorem twE6ThreeCompGenInner_holds :
    ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
      Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
      ∀ (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
        (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K),
        TwE6ThreeA2Line K σ h₀ L T n →
      ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
        E ≤ twistedE6Inn K σ →
        ∀ P : Subgroup (MulAut (twistedE6RootGroup K σ)), P ≤ E → Nat.card P = 3 ^ 2 →
          TwE6InnerAll24 K σ P →
        (∃ s : twistedE6RootGroup K σ, (s : ModGL TwistTag.E6.tag K) = h₀ ∧ MulAut.conj s ∈ P) →
        n ∈ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔ (T ⊔ ⨆ i, L i) := by
  rintro K _ _ σ q hch hσ hK h3 hq h₀ L T n hl E hE hcard hEi P hPE hPc hAll ⟨s, hs, hsP⟩
  obtain ⟨v, hvP, hvs⟩ := twExists_inner_plane_notMem_zpowers hE hEi hPE hPc (hPE hsP)
  by_cases hvM : (v : ModGL TwistTag.E6.tag K) ∈ T ⊔ ⨆ i, L i
  · obtain ⟨ℓ, f, hU, Fr, g₀, Hc, ρ, A, -, F⟩ := exists_twCompFrames hch hK h3 hl
    exact F.twMem_of_comm hl (twE6ThreeA2ConjAt_of_stmt twE6ThreeA2Conj_holds σ hch hσ hK h3 hq)
      hE hcard hPE hAll hs hsP hvP hvs hvM
  · exact twComp_mem_of_notMem hl hE hcard hs (hPE hsP) (hPE hvP) hvs hvM

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
