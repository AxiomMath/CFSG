module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLevel1Base
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT2Data

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

theorem sClassify_leaf
    (γ : SModel ≃* SModel) :
    ∃ s₀ : SModel, ∃ k, k < 8 ∧ ∃ m, m < (sLeaves k).length ∧
      ∀ a : SModel, γ a = s₀ * ⟨sFm k m a.code, sF_lt _ _ _⟩ * s₀⁻¹ := by
  obtain ⟨s₀, k, hk, ds, hds, hγ⟩ := sClassify SModel.codeIso γ
  obtain ⟨m, hm, hmds⟩ := mem_sLeaves hk hds
  refine ⟨s₀, k, hk, m, hm, fun a => ?_⟩
  apply SModel.ext
  have h1 := hγ a
  rw [SModel.codeIso_f, SModel.codeIso_f, SModel.codeIso_f, sConj, cconj] at h1
  rw [SModel.code_mul, SModel.code_mul, SModel.code_inv, h1]
  show sMul (sMul s₀.code (sAutData.F sMul k ds a.code)) (sInv s₀.code) =
    sMul (sMul s₀.code (sAutData.F sMul k ((sLeaves k).getD m []) a.code)) (sInv s₀.code)
  rw [hmds]

namespace CodeIso

variable {T : Type*} [Group T] {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T 131072 mul)

theorem g_mul {c d : ℕ} (hc : c < 131072) (hd : d < 131072) : Φ.g (mul c d) = Φ.g c * Φ.g d := by
  rw [← Φ.f_g hc, ← Φ.f_g hd, ← Φ.map_mul, Φ.g_f, Φ.f_g hc, Φ.f_g hd]

theorem g_zero (h0 : mul 0 0 = 0) : Φ.g 0 = 1 := by rw [← Φ.f_one h0, Φ.g_f]

end CodeIso

structure IotaFacts (mul : ℕ → ℕ → ℕ) (ι vec : Array ℕ) : Prop where
  zero : ι[0]! = 0
  lt : ∀ c, c < 65536 → ι[c]! < 131072
  ker : ∀ c, c < 65536 → ι[c]! = 0 → c = 0
  gens : ∀ g ∈ sGens, s2InSp vec ι[g]! = true
  hom : ∀ c, c < 65536 → ∀ g ∈ sGens, ι[sMul c g]! = mul ι[c]! ι[g]!

section Iota

variable {T₁ : Subgroup G}
  {mul : ℕ → ℕ → ℕ}
  (Φ : CodeIso T₁ 131072 mul) (h0 : mul 0 0 = 0) {ι vec : Array ℕ}
  (hι : IotaFacts mul ι vec)

@[expose] noncomputable def iotaF (a : SModel) : T₁ := Φ.g ι[a.code]!

include hι in
theorem f_iotaF (a : SModel) : Φ.f (iotaF Φ (ι := ι) a) = ι[a.code]! :=
  Φ.f_g (hι.lt _ a.lt)

include hι in
theorem iotaF_mul_gen (a : SModel) {g : ℕ} (hg : g ∈ sGens) :
    iotaF Φ (ι := ι) (a * SModel.codeIso.g g) =
      iotaF Φ (ι := ι) a * iotaF Φ (ι := ι) (SModel.codeIso.g g) := by
  have hgl : g < 65536 := sGens_lt g hg
  have hcode : (SModel.codeIso.g g).code = g := SModel.codeIso.f_g hgl
  unfold iotaF
  rw [SModel.code_mul, hcode, hι.hom _ a.lt g hg, Φ.g_mul (hι.lt _ a.lt) (hι.lt _ hgl)]

include h0 hι in
theorem iotaF_one : iotaF Φ (ι := ι) 1 = 1 := by
  unfold iotaF
  rw [SModel.code_one, hι.zero, Φ.g_zero h0]

include h0 hι in
theorem iotaF_mul (a b : SModel) :
    iotaF Φ (ι := ι) (a * b) = iotaF Φ (ι := ι) a * iotaF Φ (ι := ι) b := by
  revert a
  refine SModel.codeIso.induction sMul_zero_zero sGens_lt sGen (P := fun b =>
    ∀ a : SModel, iotaF Φ (ι := ι) (a * b) = iotaF Φ (ι := ι) a * iotaF Φ (ι := ι) b) ?_ ?_ b
  · intro a
    rw [mul_one, iotaF_one Φ h0 hι, mul_one]
  · intro b hb g hg a
    rw [← mul_assoc, iotaF_mul_gen Φ hι _ hg, hb, iotaF_mul_gen Φ hι _ hg, mul_assoc]

include h0 hι in
theorem iotaF_injective : Function.Injective (iotaF Φ (ι := ι)) := by
  intro a b hab
  have h1 : iotaF Φ (ι := ι) (a * b⁻¹) = 1 := by
    rw [iotaF_mul Φ h0 hι, hab, ← iotaF_mul Φ h0 hι, mul_inv_cancel, iotaF_one Φ h0 hι]
  have h2 : ι[(a * b⁻¹).code]! = 0 := by
    have := congrArg Φ.f h1
    rw [f_iotaF Φ hι, Φ.f_one h0] at this
    exact this
  have hc0 : (a * b⁻¹).code = 0 := hι.ker _ (a * b⁻¹).lt h2
  have h3 : a * b⁻¹ = 1 := SModel.ext (hc0.trans SModel.code_one.symm)
  calc a = a * b⁻¹ * b := (inv_mul_cancel_right a b).symm
    _ = b := by rw [h3, one_mul]

include Φ h0 hι in
theorem iota_code_inj {c d : ℕ} (hc : c < 65536) (hd : d < 65536) (h : ι[c]! = ι[d]!) :
    c = d := by
  have hc' : (SModel.codeIso.g c).code = c := SModel.codeIso.f_g hc
  have hd' : (SModel.codeIso.g d).code = d := SModel.codeIso.f_g hd
  have hcd : iotaF Φ (ι := ι) (SModel.codeIso.g c) = iotaF Φ (ι := ι) (SModel.codeIso.g d) := by
    unfold iotaF
    rw [hc', hd', h]
  have := congrArg SModel.code (iotaF_injective Φ h0 hι hcd)
  rwa [hc', hd'] at this

include h0 hι in
theorem conj_iotaF_mem {S : Subgroup G} {y : G}
    (hK : ∀ g : T₁, y⁻¹ * g * y ∈ S ↔ s2InSp vec (Φ.f g) = true) (a : SModel) :
    y⁻¹ * (iotaF Φ (ι := ι) a : G) * y ∈ S := by
  refine SModel.codeIso.induction sMul_zero_zero sGens_lt sGen
    (P := fun a => y⁻¹ * (iotaF Φ (ι := ι) a : G) * y ∈ S) ?_ ?_ a
  · rw [iotaF_one Φ h0 hι]
    simp
  · intro b hb g hg
    have hcode : (SModel.codeIso.g g).code = g := SModel.codeIso.f_g (sGens_lt g hg)
    have hgm : y⁻¹ * (iotaF Φ (ι := ι) (SModel.codeIso.g g) : G) * y ∈ S := by
      refine (hK _).2 ?_
      rw [f_iotaF Φ hι, hcode]
      exact hι.gens g hg
    have e : y⁻¹ * ((iotaF Φ (ι := ι) b : G) * (iotaF Φ (ι := ι) (SModel.codeIso.g g) : G)) * y =
        (y⁻¹ * (iotaF Φ (ι := ι) b : G) * y) *
          (y⁻¹ * (iotaF Φ (ι := ι) (SModel.codeIso.g g) : G) * y) := by group
    rw [iotaF_mul_gen Φ hι b hg, Subgroup.coe_mul, e]
    exact S.mul_mem hb hgm

end Iota

@[expose] noncomputable def iotaHom
    {T₁ : Subgroup G} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul) (h0 : mul 0 0 = 0)
    {ι vec : Array ℕ} (hι : IotaFacts mul ι vec) : SModel →* T₁ where
  toFun := iotaF Φ (ι := ι)
  map_one' := iotaF_one Φ h0 hι
  map_mul' := iotaF_mul Φ h0 hι

theorem iotaHom_apply
    {T₁ : Subgroup G} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul) (h0 : mul 0 0 = 0)
    {ι vec : Array ℕ} (hι : IotaFacts mul ι vec) (a : SModel) :
    iotaHom Φ h0 hι a = iotaF Φ (ι := ι) a := rfl

theorem exists_twist
    {S T₁ : Subgroup G} (e : S ≃* SModel)
    {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul) (h0 : mul 0 0 = 0) {ι vec : Array ℕ}
    (hι : IotaFacts mul ι vec) {y : G}
    (hK : ∀ g : T₁, y⁻¹ * g * y ∈ S ↔ s2InSp vec (Φ.f g) = true) :
    ∃ σ : T₁, ∃ k, k < 8 ∧ ∃ m, m < (sLeaves k).length ∧
      ∀ s : S, ∀ h : (σ : G)⁻¹ * y * s * ((σ : G)⁻¹ * y)⁻¹ ∈ T₁,
        Φ.f ⟨_, h⟩ = ι[sFm k m (e s).code]! := by
  set ιH := iotaHom Φ h0 hι
  have hmem : ∀ a : SModel, y⁻¹ * (ιH a : G) * y ∈ S := fun a =>
    conj_iotaF_mem Φ h0 hι hK a
  let φ : SModel →* S :=
    { toFun := fun a => ⟨y⁻¹ * (ιH a : G) * y, hmem a⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul]
        group }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk] at h1
    apply iotaF_injective Φ h0 hι
    apply Subtype.ext
    simpa [ιH, iotaHom_apply] using h1
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_congr e.toEquiv, SModel.codeIso.card_univ]; norm_num)
  have hcard : Nat.card SModel = Nat.card S := by
    rw [Nat.card_congr e.toEquiv]
  have hφbij : Function.Bijective φ := (Nat.bijective_iff_injective_and_card φ).2 ⟨hφinj, hcard⟩
  set γ : SModel ≃* SModel := e.symm.trans (MulEquiv.ofBijective φ hφbij).symm
  obtain ⟨s₀, k, hk, m, hm, hγ⟩ := sClassify_leaf γ
  refine ⟨ιH s₀, k, hk, m, hm, fun s h => ?_⟩
  have h1 : φ (γ (e s)) = s := by
    simp only [γ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact MulEquiv.ofBijective_apply_symm_apply φ hφbij
  have h2 : ((s : S) : G) = y⁻¹ * ((ιH s₀ : G) * (ιH ⟨sFm k m (e s).code, sF_lt _ _ _⟩ : G) *
      (ιH s₀ : G)⁻¹) * y := by
    have h1' : ((φ (γ (e s)) : S) : G) = s := congrArg Subtype.val h1
    rw [← h1', hγ (e s)]
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv]
    group
  have h3 : (⟨_, h⟩ : T₁) = ιH ⟨sFm k m (e s).code, sF_lt _ _ _⟩ := by
    apply Subtype.ext
    show (ιH s₀ : G)⁻¹ * y * s * ((ιH s₀ : G)⁻¹ * y)⁻¹ = ιH ⟨sFm k m (e s).code, sF_lt _ _ _⟩
    rw [h2]
    group
  rw [h3, iotaHom_apply, f_iotaF Φ hι]

end CFSG.EvenSmallLie.OmegaEight.SpBranch
