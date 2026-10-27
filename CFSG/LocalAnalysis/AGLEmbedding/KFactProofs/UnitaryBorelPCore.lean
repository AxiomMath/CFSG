module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutCore

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model

section BorelPCore

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hJ hK hfix

theorem eq_conj_of_normalized_pGroup (hq : 2 < p ^ f)
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hA : IsPGroup p A)
    (hAN : ∀ b ∈ Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      ∀ α ∈ A, MulAut.conj b * α * (MulAut.conj b)⁻¹ ∈ A) :
    ∀ α ∈ A, ∃ r ∈ rootGroup J hJ, α = MulAut.conj r := by
  have hcenter := center_eq_bot J hJ hK hfix hq
  have hinj : ∀ g h : ProjectiveSpecialUnitaryMatrixGroup J,
      (MulAut.conj g : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) = MulAut.conj h → g = h := by
    intro g h hgh
    have hc : g⁻¹ * h ∈ Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have key : h * x * h⁻¹ = g * x * g⁻¹ := by
        have := DFunLike.congr_fun hgh x
        simpa [MulAut.conj_apply] using this.symm
      calc x * (g⁻¹ * h) = g⁻¹ * (g * x * g⁻¹) * h := by group
        _ = g⁻¹ * (h * x * h⁻¹) * h := by rw [key]
        _ = g⁻¹ * h * x := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact inv_mul_eq_one.1 hc
  let C : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    A.comap (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* MulAut _)
  have hCp : IsPGroup p C := by
    intro c
    obtain ⟨k, hk⟩ := hA ⟨MulAut.conj (c : ProjectiveSpecialUnitaryMatrixGroup J), c.2⟩
    refine ⟨k, Subtype.ext (hinj _ _ ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hRp : IsPGroup p (rootGroup J hJ) := isPGroup_rootGroup J hJ hK hfix
  have hRN : ∀ b ∈ Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      ∀ c ∈ C, b * c * b⁻¹ ∈ C := by
    intro b hb c hc
    show MulAut.conj (b * c * b⁻¹) ∈ A
    have := hAN b hb _ hc
    simpa [map_mul, map_inv] using this
  have hCR : C ≤ rootGroup J hJ := by
    obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hK hfix
      (show 1 ≤ f from by
        rcases Nat.eq_zero_or_pos f with rfl | h
        · simp at hq
        · exact h)
    have hle : rootGroup J hJ ≤
        Subgroup.normalizer (C : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro c
      have hrN : r ∈ Subgroup.normalizer
          (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
        Subgroup.le_normalizer hr
      have hrN' : r⁻¹ ∈ Subgroup.normalizer
          (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := inv_mem hrN
      constructor
      · intro hc
        exact hRN r hrN c hc
      · intro hc
        have := hRN r⁻¹ hrN' _ hc
        have e : r⁻¹ * (r * c * r⁻¹) * r⁻¹⁻¹ = c := by group
        rwa [e] at this
    have hsup : IsPGroup p ↥(C ⊔ rootGroup J hJ) := hCp.to_sup_of_normal_left' hRp hle
    have := S.is_maximal' hsup (by rw [hS]; exact le_sup_right)
    rw [hS] at this
    exact le_sup_left.trans this.le
  have hcomm : ∀ α ∈ A, ∀ b ∈ Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      b * (α b)⁻¹ ∈ rootGroup J hJ := by
    intro α hα b hb
    have h1 := hAN b hb α hα
    have h2 : (MulAut.conj (b * (α b)⁻¹) : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) =
        (MulAut.conj b * α * (MulAut.conj b)⁻¹) * α⁻¹ := by
      ext g
      obtain ⟨y, rfl⟩ : ∃ y, α y = g := ⟨α.symm g, by simp⟩
      simp [MulAut.conj_apply, MulAut.mul_apply, map_inv]
    have h3 : b * (α b)⁻¹ ∈ C := by
      show MulAut.conj (b * (α b)⁻¹) ∈ A
      rw [h2]
      exact A.mul_mem h1 (A.inv_mem hα)
    exact hCR h3
  intro α hα
  have hαR : ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ := by
    intro r hr
    have h1 := hcomm α hα r (Subgroup.le_normalizer hr)
    have h2 : (α r)⁻¹ ∈ rootGroup J hJ := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hr) h1
      simpa using this
    simpa using Subgroup.inv_mem _ h2
  obtain ⟨u, huR, hu⟩ := exists_conj_eq_on_torus J hJ hK hfix hq α fun k =>
    hcomm α hα _ (torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ k))
  let InnR : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    (rootGroup J hJ).map (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* MulAut _)
  have hInnp : IsPGroup p InnR := hRp.map _
  have hInnN : InnR ≤ Subgroup.normalizer
      (A : Set (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro β
    have hrN : r ∈ Subgroup.normalizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := Subgroup.le_normalizer hr
    have hrN' : r⁻¹ ∈ Subgroup.normalizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := inv_mem hrN
    constructor
    · intro hβ
      exact hAN r hrN β hβ
    · intro hβ
      have := hAN r⁻¹ hrN' _ hβ
      rw [map_inv, inv_inv] at this
      have e : (MulAut.conj r)⁻¹ * (MulAut.conj r * β * (MulAut.conj r)⁻¹) * MulAut.conj r = β := by
        group
      rwa [e] at this
  have hA'p : IsPGroup p ↥(A ⊔ InnR) := hA.to_sup_of_normal_left' hInnp hInnN
  let α' : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) := MulAut.conj u⁻¹ * α
  have hα'mem : α' ∈ A ⊔ InnR :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨u⁻¹, Subgroup.inv_mem _ huR, rfl⟩)
      (Subgroup.mem_sup_left hα)
  obtain ⟨k, hk⟩ := hA'p ⟨α', hα'mem⟩
  have hα'p : α' ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hα'R : ∀ r ∈ rootGroup J hJ, α' r ∈ rootGroup J hJ := by
    intro r hr
    show u⁻¹ * α r * u⁻¹⁻¹ ∈ rootGroup J hJ
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ huR) (hαR r hr))
      (Subgroup.inv_mem _ (Subgroup.inv_mem _ huR))
  have hα'T : ∀ t ∈ torusGroup J hJ, α' t = t := by
    intro t ht
    show u⁻¹ * α t * u⁻¹⁻¹ = t
    rw [hu t ht]
    group
  obtain ⟨z, hz, hα'z⟩ := eq_conj_of_pElement J hJ hK hfix hq α' hα'p hα'R hα'T
  refine ⟨u * z, Subgroup.mul_mem _ huR hz, ?_⟩
  have : α = MulAut.conj u * α' := by
    show α = MulAut.conj u * (MulAut.conj u⁻¹ * α)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [this, hα'z, ← map_mul]

end BorelPCore

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding

open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem kFactUnitaryBorelPCore : KFactUnitaryBorelPCore := by
  intro L _ _ p _ d hd h U A hA hAN α hα
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  let Φ : MulAut L ≃* MulAut _ := MulAut.congr e'
  have hΦconj : ∀ x : L, Φ (MulAut.conj x) = MulAut.conj (e' x) := by
    intro x
    ext y
    simp [Φ, MulAut.congr_apply, MulAut.conj_apply]
  have hAp : IsPGroup p (A.map Φ.toMonoidHom) := by
    rintro ⟨_, ⟨a, ha, rfl⟩⟩
    obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : a ^ p ^ k = 1 := congrArg Subtype.val hk
    show Φ a ^ p ^ k = 1
    rw [← map_pow, h1, map_one]
  have hAN' : ∀ b ∈ Subgroup.normalizer (rootGroup J hJ : Set _), ∀ β ∈ A.map Φ.toMonoidHom,
      MulAut.conj b * β * (MulAut.conj b)⁻¹ ∈ A.map Φ.toMonoidHom := by
    intro b hb β hβ
    obtain ⟨a, ha, rfl⟩ := hβ
    have hbU : e'.symm b ∈ Subgroup.normalizer ((U : Subgroup L) : Set L) := by
      have : b ∈ (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom := by
        rw [hN]
        exact hb
      exact Subgroup.mem_map_equiv.1 this
    refine ⟨_, hAN (e'.symm b) hbU a ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, hΦconj, MulEquiv.apply_symm_apply]
  obtain ⟨r, hr, hαr⟩ := UnitaryModel.eq_conj_of_normalized_pGroup J hJ hK hfix hq
    (A.map Φ.toMonoidHom) hAp hAN' (Φ α) ⟨α, hα, rfl⟩
  refine ⟨e'.symm r, ?_, Φ.injective ?_⟩
  · have : r ∈ (U : Subgroup L).map e'.toMonoidHom := hU ▸ hr
    exact Subgroup.mem_map_equiv.1 this
  · rw [hαr, hΦconj, MulEquiv.apply_symm_apply]

end CFSG.AGLEmbedding
