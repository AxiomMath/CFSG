module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinarySubgroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBlockCovariance

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem fixedSpace_map_conj {A : Type} [Group A] {q : ℕ} {W : Type} [AddCommGroup W]
    [Module (ZMod q) W] (τ : Representation (ZMod q) A W) (φ : A) (K : Subgroup A) :
    BinaryRepresentations.fixedSpace τ (K.map (MulAut.conj φ).toMonoidHom) =
      (BinaryRepresentations.fixedSpace τ K).map (τ φ) := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨τ φ⁻¹ v, ?_, ?_⟩
    · rw [BinaryRepresentations.mem_fixedSpace_iff]
      intro k hk
      have h := (BinaryRepresentations.mem_fixedSpace_iff τ _ v).mp hv (φ * k * φ⁻¹)
        ⟨k, hk, by simp [MulAut.conj_apply]⟩
      have : τ k (τ φ⁻¹ v) = τ φ⁻¹ (τ (φ * k * φ⁻¹) v) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2; group
      rw [this, h]
    · rw [← Module.End.mul_apply, ← map_mul]; simp
  · rintro ⟨w, hw, rfl⟩
    rw [BinaryRepresentations.mem_fixedSpace_iff]
    rintro _ ⟨k, hk, rfl⟩
    have h := (BinaryRepresentations.mem_fixedSpace_iff τ _ w).mp hw k hk
    have : τ ((MulAut.conj φ).toMonoidHom k) (τ φ w) = τ φ (τ k w) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      simp [MulAut.conj_apply]
    rw [this, h]

theorem conjOnP_mem_Bstar (hc : BinaryActionRankCounterexample G p P T B e ρ) (b : B) :
    conjOnP P hc.faithfulBinaryIrreducibleAction.normal b.val ∈ Bstar P B :=
  Subgroup.mem_map.mpr ⟨⟨b.val, mem_normalizer hc.faithfulBinaryIrreducibleAction.normal b.val⟩,
    Subgroup.mem_subgroupOf.mpr b.2, rfl⟩

theorem conjugate_hyperplane (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e)
    (K : BinaryRepresentations.hyperplanes 2 (X hc)) (b : B) :
    K.val.map (MulAut.conj (conjOnP P hc.faithfulBinaryIrreducibleAction.normal b.val)).toMonoidHom ∈
      BinaryRepresentations.hyperplanes 2 (X hc) := by
  set φ := conjOnP P hc.faithfulBinaryIrreducibleAction.normal b.val with hφ
  have hn : φ ∈ Subgroup.normalizer (X hc : Set (MulAut ↥P)) :=
    CentralBinarySubgroup.Bstar_normalizes_X hc he (conjOnP_mem_Bstar hc b)
  have hmap : (X hc).map (MulAut.conj φ).toMonoidHom = X hc := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hn y).mp hy
    · intro hx
      have hn' := (Subgroup.normalizer (X hc : Set (MulAut ↥P))).inv_mem hn
      refine ⟨φ⁻¹ * x * φ⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp hn' x).mp hx, ?_⟩
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]; group
  obtain ⟨hle, hidx⟩ := K.2
  refine ⟨?_, ?_⟩
  · exact (Subgroup.map_mono hle).trans hmap.le
  · have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj φ).toMonoidHom) K.val (X hc)
      (MulAut.conj φ).injective
    rw [hmap] at this
    rw [this]; exact hidx

theorem covariance (hc : BinaryActionRankCounterexample G p P T B e ρ) (K : Subgroup (MulAut ↥P)) (b : B) :
    (E hc K).map (sigma hc (conjOnP P hc.faithfulBinaryIrreducibleAction.normal b.val)) =
      E hc (K.map (MulAut.conj (conjOnP P hc.faithfulBinaryIrreducibleAction.normal b.val)).toMonoidHom) :=
  (fixedSpace_map_conj (sigma hc) _ K).symm

theorem stability (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e)
    (K : BinaryRepresentations.hyperplanes 2 (X hc)) :
    ∀ φ ∈ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal),
      (E hc K.val).map (sigma hc φ) = E hc K.val := by
  intro φ hφ
  have hcen := (CentralBinarySubgroup.central_binary hc he).2.2.2.2.1
  have hKX : K.val ≤ X hc := K.2.1
  have : K.val.map (MulAut.conj φ).toMonoidHom = K.val := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := (hcen y (hKX hy) φ hφ).eq
      simpa [MulAut.conj_apply, mul_assoc, ← this] using hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      have := (hcen x (hKX hx) φ hφ).eq
      simp [MulAut.conj_apply, ← this]
  unfold E
  rw [← fixedSpace_map_conj, this]

end CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBlockCovariance
