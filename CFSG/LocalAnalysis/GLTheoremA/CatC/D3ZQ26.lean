module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ25
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ24
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZA4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ2

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Dickson.Bal207.D4Graph
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise


section Phi

variable {K : Type} [Field K] [Finite K]

@[expose] def PhiHom (Θ : adjointGroup Tag.D4 K ≃* D4Model K) : D4Model K →* ModGL Tag.D4 K :=
  (adjointGroup Tag.D4 K).subtype.comp Θ.symm.toMonoidHom

theorem PhiHom_apply (Θ : adjointGroup Tag.D4 K ≃* D4Model K) (s : D4Model K) :
    PhiHom Θ s = ((Θ.symm s : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) := rfl

theorem PhiHom_injective (Θ : adjointGroup Tag.D4 K ≃* D4Model K) :
    Function.Injective (PhiHom Θ) := fun s s' h => Θ.symm.injective (Subtype.ext h)

theorem PhiHom_range (Θ : adjointGroup Tag.D4 K ≃* D4Model K) :
    (PhiHom Θ).range = adjointGroup Tag.D4 K := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact (Θ.symm s).2
  · intro hz
    exact ⟨Θ ⟨z, hz⟩, by simp [PhiHom_apply]⟩

theorem PhiHom_aut (Θ : adjointGroup Tag.D4 K ≃* D4Model K) (τ : MulAut (D4Model K))
    (s : D4Model K) :
    PhiHom Θ (τ s) =
      ((MulAut.congr Θ.symm τ (Θ.symm s) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) := by
  simp [PhiHom_apply, MulAut.congr_apply]

end Phi

section Main

variable {K : Type} [Field K] [Finite K]

set_option maxHeartbeats 400000 in
theorem d3A4Levi_holds : D3A4Levi := by
  intro K _ _ n hK b t₁ t₂ hb3 hbE ht₁2 ht₂2 hcomm hne₁ hne₂ hne₁₂ hbt₁ hbt₂ A hA hAbig hfb hf1 hf2
    V hAV hV1 hVp hVb hVt₁ hVt₂ hVc hVtop hVS hVsyl
  classical
  haveI := charP_three_of_card hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (D4Model K) := inferInstance
  haveI : Finite ↥(adjointGroup Tag.D4 K) := inferInstance
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hVm : ∀ τ : MulAut (D4Model K), V.map τ.toMonoidHom = V → ∀ h, τ h ∈ V ↔ h ∈ V := by
    intro τ hτ h
    constructor
    · intro hh
      rw [← hτ] at hh
      obtain ⟨v, hv, hvh⟩ := hh
      have : v = h := τ.injective hvh
      rw [← this]; exact hv
    · intro hh
      have := Subgroup.mem_map_of_mem τ.toMonoidHom hh
      rwa [hτ] at this
  have hPb : ∀ x ∈ Subgroup.normalizer (V : Set (D4Model K)),
      b x ∈ Subgroup.normalizer (V : Set (D4Model K)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro h
    obtain ⟨h', rfl⟩ := b.surjective h
    have e : b x * b h' * (b x)⁻¹ = b (x * h' * x⁻¹) := by simp
    rw [e, hVm b hVb, hVm b hVb, hx h']
  obtain ⟨S₀, hS₀⟩ := hVS
  have hS₀P : (S₀ : Subgroup (D4Model K)) ≤ Subgroup.normalizer (V : Set (D4Model K)) :=
    Subgroup.le_normalizer.trans hS₀
  obtain ⟨S₁, hS₁P, hS₁b⟩ := exists_stable_sylow_in b hb3 _ hPb S₀ hS₀P
  have hNS₁ := normalizer_le_of_sylow _ S₀ S₁ hS₀P hS₁P hS₀
  obtain ⟨Θ, g, a, σ, ε, hΘ, hε, hgB, hα'eq⟩ := exists_frame hK hb3 hbE hS₁b
  set F : MulAut (D4Model K) ≃* MulAut (adjointGroup Tag.D4 K) := MulAut.congr Θ.symm with hF
  have hFapp : ∀ (τ : MulAut (D4Model K)) (y : adjointGroup Tag.D4 K),
      F τ y = Θ.symm (τ (Θ y)) := fun τ y => by simp [hF, MulAut.congr_apply]
  have hα'3 : F b ^ 3 = 1 := by
    have := congrArg F hb3
    simpa only [map_pow, map_one] using this
  have h₁sq : F t₁ * F t₁ = 1 := by
    have := congrArg F ht₁2
    simpa only [map_pow, map_one, sq, map_mul] using this
  have h₂sq : F t₂ * F t₂ = 1 := by
    have := congrArg F ht₂2
    simpa only [map_pow, map_one, sq, map_mul] using this
  have hFcomm : F t₁ * F t₂ = F t₂ * F t₁ := by
    have := congrArg F hcomm
    simpa only [map_mul] using this
  have hFb₁ : F b * F t₁ = F t₂ * F b := by
    have := congrArg F hbt₁
    simpa only [map_mul] using this
  have hFb₂ : F b * F t₂ = F t₁ * F t₂ * F b := by
    have := congrArg F hbt₂
    simpa only [map_mul] using this
  obtain ⟨c₁, c₂, a₁, a₂, ht₁', ht₂'⟩ := a4_inndiag hε h₁sq
    (by rw [← hα'eq]; exact hFb₁) (by rw [← hα'eq]; exact hFb₂)
  set Γ₁ : ModGL Tag.D4 K := (c₁ : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a₁ with hΓ₁
  set Γ₂ : ModGL Tag.D4 K := (c₂ : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a₂ with hΓ₂
  have hT₁ : ∀ y : adjointGroup Tag.D4 K,
      ((F t₁ y : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = Γ₁ * (y : ModGL Tag.D4 K) * Γ₁⁻¹ := by
    intro y
    rw [ht₁']
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_diagAut, hΓ₁]
    group
  have hT₂ : ∀ y : adjointGroup Tag.D4 K,
      ((F t₂ y : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = Γ₂ * (y : ModGL Tag.D4 K) * Γ₂⁻¹ := by
    intro y
    rw [ht₂']
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_diagAut, hΓ₂]
    group
  have hφ : ∀ y : adjointGroup Tag.D4 K,
      ((F b y : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        phiG (g : ModGL Tag.D4 K) a σ ε (y : ModGL Tag.D4 K) := coe_alpha_eq_phiG hα'eq
  have sq₁ : ∀ x ∈ adjointGroup Tag.D4 K, Γ₁ * Γ₁ * x * (Γ₁ * Γ₁)⁻¹ = x := by
    intro x hx
    have h := congrArg (fun τ : MulAut (adjointGroup Tag.D4 K) =>
      ((τ ⟨x, hx⟩ : adjointGroup Tag.D4 K) : ModGL Tag.D4 K)) h₁sq
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    rw [hT₁, hT₁] at h
    calc Γ₁ * Γ₁ * x * (Γ₁ * Γ₁)⁻¹ = Γ₁ * (Γ₁ * x * Γ₁⁻¹) * Γ₁⁻¹ := by group
      _ = x := h
  have sq₂ : ∀ x ∈ adjointGroup Tag.D4 K, Γ₂ * Γ₂ * x * (Γ₂ * Γ₂)⁻¹ = x := by
    intro x hx
    have h := congrArg (fun τ : MulAut (adjointGroup Tag.D4 K) =>
      ((τ ⟨x, hx⟩ : adjointGroup Tag.D4 K) : ModGL Tag.D4 K)) h₂sq
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    rw [hT₂, hT₂] at h
    calc Γ₂ * Γ₂ * x * (Γ₂ * Γ₂)⁻¹ = Γ₂ * (Γ₂ * x * Γ₂⁻¹) * Γ₂⁻¹ := by group
      _ = x := h
  have comm : ∀ x ∈ adjointGroup Tag.D4 K,
      Γ₁ * (Γ₂ * x * Γ₂⁻¹) * Γ₁⁻¹ = Γ₂ * (Γ₁ * x * Γ₁⁻¹) * Γ₂⁻¹ := by
    intro x hx
    have h := congrArg (fun τ : MulAut (adjointGroup Tag.D4 K) =>
      ((τ ⟨x, hx⟩ : adjointGroup Tag.D4 K) : ModGL Tag.D4 K)) hFcomm
    simp only [MulAut.mul_apply] at h
    rw [hT₁, hT₂, hT₂, hT₁] at h
    exact h
  have rel₁ : ∀ x ∈ adjointGroup Tag.D4 K,
      phiG (g : ModGL Tag.D4 K) a σ ε (Γ₁ * x * Γ₁⁻¹) = Γ₂ * phiG (g : ModGL Tag.D4 K) a σ ε x * Γ₂⁻¹ := by
    intro x hx
    have h := congrArg (fun τ : MulAut (adjointGroup Tag.D4 K) =>
      ((τ ⟨x, hx⟩ : adjointGroup Tag.D4 K) : ModGL Tag.D4 K)) hFb₁
    simp only [MulAut.mul_apply] at h
    rw [hφ, hT₁, hT₂, hφ] at h
    exact h
  have rel₂ : ∀ x ∈ adjointGroup Tag.D4 K,
      phiG (g : ModGL Tag.D4 K) a σ ε (Γ₂ * x * Γ₂⁻¹) =
        (Γ₁ * Γ₂) * phiG (g : ModGL Tag.D4 K) a σ ε x * (Γ₁ * Γ₂)⁻¹ := by
    intro x hx
    have h := congrArg (fun τ : MulAut (adjointGroup Tag.D4 K) =>
      ((τ ⟨x, hx⟩ : adjointGroup Tag.D4 K) : ModGL Tag.D4 K)) hFb₂
    simp only [MulAut.mul_apply] at h
    rw [hφ, hT₂, hT₁, hT₂, hφ] at h
    rw [h]
    group
  have hne₁' : ∃ x ∈ adjointGroup Tag.D4 K, Γ₁ * x * Γ₁⁻¹ ≠ x := by
    by_contra hcon
    push Not at hcon
    apply hne₁
    have : F t₁ = 1 := by
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [hT₁, hcon y.1 y.2]
      rfl
    exact F.injective (this.trans (map_one F).symm)
  set Φ : D4Model K →* ModGL Tag.D4 K := PhiHom Θ with hΦ
  have hΦinj : Function.Injective Φ := PhiHom_injective Θ
  have hΦrange : Φ.range = adjointGroup Tag.D4 K := PhiHom_range Θ
  have hΦτ : ∀ (τ : MulAut (D4Model K)) (s : D4Model K),
      Φ (τ s) = ((F τ (Θ.symm s) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) :=
    fun τ s => PhiHom_aut Θ τ s
  have hΦb : ∀ s, Φ (b s) = phiG (g : ModGL Tag.D4 K) a σ ε (Φ s) := by
    intro s
    rw [hΦτ, hφ]
    rfl
  have hΦt₁ : ∀ s, Φ (t₁ s) = Γ₁ * Φ s * Γ₁⁻¹ := by
    intro s
    rw [hΦτ, hT₁]
    rfl
  have hΦt₂ : ∀ s, Φ (t₂ s) = Γ₂ * Φ s * Γ₂⁻¹ := by
    intro s
    rw [hΦτ, hT₂]
    rfl
  have hBC : borelGroup Tag.D4 K ≤ adjointGroup Tag.D4 K := by
    rw [← (borel_self_normalizers Tag.D4 K).1]; exact inf_le_left
  have hBnorm : ∀ z : ↥(adjointGroup Tag.D4 K), (z : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K →
      ∀ u : ↥(adjointGroup Tag.D4 K), u ∈ unitU K ↔ z * u * z⁻¹ ∈ unitU K := by
    intro z hz u
    have hzN : (z : ModGL Tag.D4 K) ∈
        Subgroup.normalizer (posUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) := by
      have := hz
      rw [← (borel_self_normalizers Tag.D4 K).1] at this
      exact this.2
    have hmemH : ∀ y : ↥(adjointGroup Tag.D4 K), y ∈ unitU K ↔
        (y : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K := fun y => Subgroup.mem_subgroupOf
    rw [hmemH, hmemH]
    exact Subgroup.mem_normalizer_iff.1 hzN _
  have hBN : ∀ z : ↥(adjointGroup Tag.D4 K), (z : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K →
      Θ z ∈ Subgroup.normalizer ((S₁ : Subgroup (D4Model K)) : Set (D4Model K)) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro s
    obtain ⟨y, rfl⟩ := Θ.surjective s
    rw [← map_mul, ← map_inv, ← map_mul, hΘ, hΘ]
    exact hBnorm z hz y
  set Vm : Subgroup (ModGL Tag.D4 K) := V.map Φ with hVm'
  have hPm : adjointGroup Tag.D4 K ⊓ Subgroup.normalizer (Vm : Set (ModGL Tag.D4 K)) =
      (Subgroup.normalizer (V : Set (D4Model K))).map Φ := by
    rw [← hΦrange]
    exact inf_range_normalizer_map Φ hΦinj V
  have hVC : Vm ≤ adjointGroup Tag.D4 K := hΦrange ▸ Subgroup.map_le_range Φ V
  have hVpm : IsPGroup 3 Vm := hVp.map Φ
  have hB : borelGroup Tag.D4 K ≤
      adjointGroup Tag.D4 K ⊓ Subgroup.normalizer (Vm : Set (ModGL Tag.D4 K)) := by
    intro z hz
    rw [hPm]
    refine ⟨Θ ⟨z, hBC hz⟩, hNS₁ (hBN ⟨z, hBC hz⟩ hz), ?_⟩
    simp [hΦ, PhiHom_apply]
  have hne : adjointGroup Tag.D4 K ⊓ Subgroup.normalizer (Vm : Set (ModGL Tag.D4 K)) ≠
      adjointGroup Tag.D4 K := by
    intro h
    apply hVtop
    rw [hPm, ← hΦrange, MonoidHom.range_eq_map] at h
    exact Subgroup.map_injective hΦinj h
  have hVcm : pCoreOf 3 (adjointGroup Tag.D4 K ⊓ Subgroup.normalizer (Vm : Set (ModGL Tag.D4 K))) =
      Vm := by
    rw [hPm, pCoreOf_map_of_injective Φ hΦinj, hVc]
  have hVφ : ∀ x ∈ Vm, phiG (g : ModGL Tag.D4 K) a σ ε x ∈ Vm := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← hΦb]
    exact ⟨b s, (hVm b hVb s).2 hs, rfl⟩
  have hVΓ : ∀ (τ : MulAut (D4Model K)) (Γ : ModGL Tag.D4 K), V.map τ.toMonoidHom = V →
      (∀ s, Φ (τ s) = Γ * Φ s * Γ⁻¹) →
      ∀ x ∈ adjointGroup Tag.D4 K, Γ * x * Γ⁻¹ ∈ Vm ↔ x ∈ Vm := by
    intro τ Γ hτ hΦτ' x hx
    have hxr : x ∈ Φ.range := by rw [hΦrange]; exact hx
    obtain ⟨s, rfl⟩ := hxr
    rw [← hΦτ' s, hVm', Subgroup.mem_map_iff_mem hΦinj, Subgroup.mem_map_iff_mem hΦinj]
    exact hVm τ hτ s
  have hVΓ₁ := hVΓ t₁ Γ₁ hVt₁ hΦt₁
  have hVΓ₂ := hVΓ t₂ Γ₂ hVt₂ hΦt₂
  have hS₁img : (S₁ : Subgroup (D4Model K)).map Φ = posUnipotent Tag.D4 K := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hy : Θ.symm s ∈ unitU K := by
        rw [← hΘ, MulEquiv.apply_symm_apply]; exact hs
      exact hy
    · intro hz
      have hzC : z ∈ adjointGroup Tag.D4 K := posUnipotent_le_adjointGroup hz
      have hy : (⟨z, hzC⟩ : adjointGroup Tag.D4 K) ∈ unitU K := hz
      exact ⟨Θ ⟨z, hzC⟩, (hΘ _).2 hy, by simp [hΦ, PhiHom_apply]⟩
  have hVU : Vm ≠ posUnipotent Tag.D4 K := by
    intro h
    apply hVsyl
    refine ⟨S₁, ?_⟩
    apply Subgroup.map_injective hΦinj
    rw [hS₁img, ← h]
  set Am : Subgroup (ModGL Tag.D4 K) := A.map Φ with hAm
  have hAmV : Am ≤ Vm := Subgroup.map_mono hAV
  have hAc : ∀ x ∈ Am, ∀ y ∈ Am, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, d3f_commute hA hx hy]
  have hAm₁ : ∀ x ∈ Am, Γ₁ * x * Γ₁⁻¹ = x := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hΦt₁, hf1 x hx]
  have hAm₂ : ∀ x ∈ Am, Γ₂ * x * Γ₂⁻¹ = x := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hΦt₂, hf2 x hx]
  have hcardA : Nat.card Am = Nat.card A :=
    Nat.card_congr (Subgroup.equivMapOfInjective A Φ hΦinj).toEquiv.symm
  exact levi_chev hK hgB hε (fun x hx => phiG_cube hα'eq hα'3 hx)
    (fun x hx => phiG_mem_adjoint hα'eq hx) c₁.2 c₂.2 rfl rfl sq₁ sq₂ comm rel₁ rel₂ hne₁' hVC
    hVpm hB hne hVcm hVφ hVΓ₁ hVΓ₂ hVU hAmV hAc hAm₁ hAm₂ (by rw [hcardA]; exact hAbig)

end Main

end CFSG.LocalAnalysis.GLTheoremA
