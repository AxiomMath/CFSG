module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompReg
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompTypes
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompUnitary
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KD4T
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 unitarySU_le_unitaryIsom3)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Fix

variable
  {K : Type} [Field K] {σ : K ≃+* K} {E : Subgroup (MulAut (twistedE6RootGroup K σ))}

theorem twFinrank_pow_mul_eq (hAll : TwE6InnerAll24 K σ E) {s v : twistedE6RootGroup K σ}
    (hsE : MulAut.conj s ∈ E) (hvE : MulAut.conj v ∈ E)
    (hvs : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj s)) (k : ℕ) :
    Module.finrank K (LinearMap.ker ((((s : ModGL TwistTag.E6.tag K) ^ k *
      (v : ModGL TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 :=
  hAll (s ^ k * v) (by rw [map_mul, map_pow]; exact mul_mem (pow_mem hsE k) hvE) fun h =>
    hvs (by
      rw [eq_inv_of_mul_eq_one_right h, map_inv, map_pow]
      exact inv_mem (pow_mem (Subgroup.mem_zpowers _) k))

end Fix

section Package


variable {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K} {ℓ f : ℕ} {hU : UnitaryFieldData ℓ f K}
  {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
  {Hc : Fin 3 → SL(3, AlgebraicClosure K)}
  {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
  {A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary hU (idGram K 3)}

theorem TwCompFrames.twExists_layer_conj (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    (hl : TwE6ThreeA2Line K σ h₀ L T n) {τ : ModGL TwistTag.E6.tag K}
    (hτ : τ ∈ twTorusHat K σ g₀) {x x'' : Fin 3 → unitarySU ℓ f K 3}
    (h3 : (τ * twLayerProd ρ x) ^ 3 = 1) (h3'' : (τ * twLayerProd ρ x'') ^ 3 = 1)
    (hd : ∀ k : ℕ, Module.finrank K (LinearMap.ker (((h₀ ^ k * (τ * twLayerProd ρ x) :
      ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24)
    (hd'' : ∀ k : ℕ, Module.finrank K (LinearMap.ker (((h₀ ^ k * (τ * twLayerProd ρ x'') :
      ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24) :
    ∃ y : Fin 3 → unitarySU ℓ f K 3,
      twLayerProd ρ y * (τ * twLayerProd ρ x) * (twLayerProd ρ y)⁻¹ = τ * twLayerProd ρ x'' := by
  have hcomm := twFrames_commute hl F.range
  have hact : ∀ i w, τ * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * τ⁻¹ =
      ((ρ i (conjSU hU (A i τ) w) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) :=
    fun i w => F.act i τ hτ w
  have hcyc : ∀ z : Fin 3 → unitarySU ℓ f K 3, (τ * twLayerProd ρ z) ^ 3 = 1 →
      (∀ k : ℕ, Module.finrank K (LinearMap.ker (((h₀ ^ k * (τ * twLayerProd ρ z) :
        ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24) →
      ∀ i, HasCyclicVec3 ((((A i τ : GL (Fin 3) K) * (z i : GL (Fin 3) K) : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) := fun z hz3 hzd => by
    have hz0 := hzd 0
    have hz1 := hzd 1
    rw [pow_zero, one_mul] at hz0
    rw [pow_one] at hz1
    exact F.hasCyclicVec3 hl hτ z hz3 hz0 hz1 (hzd 2)
  have hiso : ∀ (z : Fin 3 → unitarySU ℓ f K 3) i,
      (A i τ : GL (Fin 3) K) * (z i : GL (Fin 3) K) ∈ unitaryIsom3 hU := fun z i =>
    mul_mem (twMem_unitaryIsom3_of_mem hU (A i τ).2)
      (unitarySU_le_unitaryIsom3 (h := hU) (z i).2)
  have hdet : ∀ (z : Fin 3 → unitarySU ℓ f K 3) i,
      ((((A i τ : GL (Fin 3) K) * (z i : GL (Fin 3) K) : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K).det =
        ((A i τ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := fun z i => by
    rw [Units.val_mul, Matrix.det_mul, ((mem_unitarySU_iff hU).1 (z i).2).1, mul_one]
  have hy : ∀ i, ∃ g : unitarySU ℓ f K 3,
      (g : GL (Fin 3) K) * ((A i τ : GL (Fin 3) K) * (x i : GL (Fin 3) K)) =
        ((A i τ : GL (Fin 3) K) * (x'' i : GL (Fin 3) K)) * g := fun i => by
    obtain ⟨α, hα⟩ := twLayerProd_pow_three (A := fun i => A i τ) F.injective hcomm hact x h3 i
    obtain ⟨β, hβ⟩ :=
      twLayerProd_pow_three (A := fun i => A i τ) F.injective hcomm hact x'' h3'' i
    obtain ⟨g, hg, hge⟩ := twExists_unitarySU_conj_of_hasCyclicVec3 hU F.twThree_dvd
      (hiso x i) (hiso x'' i) hα hβ ((hdet x i).trans (hdet x'' i).symm) (hcyc x h3 hd i)
      (hcyc x'' h3'' hd'' i)
    exact ⟨⟨g, hg⟩, hge⟩
  choose y hy using hy
  refine ⟨y, ?_⟩
  have hyx : ∀ i, conjSU hU (A i τ)⁻¹ (y i) * x i = x'' i * y i := fun i => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_conjSU, Subgroup.coe_inv, inv_inv]
    calc ((A i τ : GL (Fin 3) K))⁻¹ * (y i : GL (Fin 3) K) * (A i τ : GL (Fin 3) K) *
          (x i : GL (Fin 3) K)
        = ((A i τ : GL (Fin 3) K))⁻¹ *
          ((y i : GL (Fin 3) K) * ((A i τ : GL (Fin 3) K) * (x i : GL (Fin 3) K))) := by group
      _ = ((A i τ : GL (Fin 3) K))⁻¹ *
          (((A i τ : GL (Fin 3) K) * (x'' i : GL (Fin 3) K)) * (y i : GL (Fin 3) K)) := by
        rw [hy i]
      _ = (x'' i : GL (Fin 3) K) * (y i : GL (Fin 3) K) := by group
  have hτy : τ⁻¹ * twLayerProd ρ y * τ = twLayerProd ρ (fun i => conjSU hU (A i τ)⁻¹ (y i)) :=
    twLayerProd_conj (fun i w => inv_conj_frame (B := fun i => A i τ) hact i w) y
  have hmul : twLayerProd ρ (fun i => conjSU hU (A i τ)⁻¹ (y i)) * twLayerProd ρ x =
      twLayerProd ρ x'' * twLayerProd ρ y := by
    have h1 : commProd3 ρ hcomm (fun i => conjSU hU (A i τ)⁻¹ (y i)) * commProd3 ρ hcomm x =
        commProd3 ρ hcomm x'' * commProd3 ρ hcomm y := by
      rw [← map_mul, ← map_mul]
      exact congrArg (commProd3 ρ hcomm) (funext hyx)
    exact congrArg Subtype.val h1
  calc twLayerProd ρ y * (τ * twLayerProd ρ x) * (twLayerProd ρ y)⁻¹
      = τ * ((τ⁻¹ * twLayerProd ρ y * τ) * twLayerProd ρ x) * (twLayerProd ρ y)⁻¹ := by group
    _ = τ * (twLayerProd ρ x'' * twLayerProd ρ y) * (twLayerProd ρ y)⁻¹ := by rw [hτy, hmul]
    _ = τ * twLayerProd ρ x'' := by group


theorem TwCompFrames.twMem_of_fix (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    (hl : TwE6ThreeA2Line K σ h₀ L T n)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3) (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hEi : ¬ E ≤ twistedE6Inn K σ) (hAll : TwE6InnerAll24 K σ E)
    {s : twistedE6RootGroup K σ} (hs : (s : ModGL TwistTag.E6.tag K) = h₀)
    (hsE : MulAut.conj s ∈ E) {v : twistedE6RootGroup K σ} (hvE : MulAut.conj v ∈ E)
    (hvs : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj s))
    (hvM : (v : ModGL TwistTag.E6.tag K) ∈ T ⊔ ⨆ i, L i)
    (hfix : ∀ φ ∈ E, ∀ i, ((L i).subgroupOf (twistedE6RootGroup K σ)).map φ.toMonoidHom =
      (L i).subgroupOf (twistedE6RootGroup K σ)) :
    n ∈ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔ (T ⊔ ⨆ i, L i) := by
  have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
  have hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  obtain ⟨ε, hεE, hεi⟩ := SetLike.not_le_iff_exists.1 hEi
  obtain ⟨e, he, heT, he3⟩ := F.twExists_outer_torsion hl hs (hED hεE) hεi
    (congrArg Subtype.val (hE.1.is_comm.comm (⟨ε, hεE⟩ : E) ⟨_, hsE⟩))
    (fun i => by rw [twComp_range_eq F.range]; exact hfix ε hεE i)
  have hcm := F.twComm_mem_layer hl (F.twCard_three_le_nine he heT he3)
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
    exact twFinrank_pow_mul_eq hAll hsE hvE hvs k
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


theorem twE6ThreeCompGen_holds : TwE6ThreeCompGen := by
  rintro K _ _ σ q hch hσ hK h3 hq h₀ L T n hl E hE hcard hED hEi - hAll ⟨s, hs, hsE⟩
  obtain ⟨v, hvE, hvs⟩ := twExists_inner_notMem_zpowers hK hσ hE hcard hED hEi hsE
  by_cases hvM : (v : ModGL TwistTag.E6.tag K) ∈ T ⊔ ⨆ i, L i
  · by_cases hfix : ∀ φ ∈ E, ∀ i, ((L i).subgroupOf (twistedE6RootGroup K σ)).map
        φ.toMonoidHom = (L i).subgroupOf (twistedE6RootGroup K σ)
    · obtain ⟨ℓ, f, hU, Fr, g₀, Hc, ρ, A, -, F⟩ := exists_twCompFrames hch hK h3 hl
      exact F.twMem_of_fix hl hE hcard hED hEi hAll hs hsE hvE hvs hvM hfix
    · exact twComp_mem_of_moves σ q hch hσ hK h3 hq hl hE hcard hED hs hsE hvE hvs hvM hfix
  · exact twComp_mem_of_notMem hl hE hcard hs hsE hvE hvs hvM

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
