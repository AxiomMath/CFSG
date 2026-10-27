module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SylowPairs
public import CFSG.LieType.Chevalley.LangRootRankOne

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

@[expose] def orderThreeSL (K : Type) [Field K] : SL2 K :=
  ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two]⟩

section Groups

variable {G : Type*} [Group G]

theorem centralizer_singleton_inv (y : G) :
    Subgroup.centralizer {y⁻¹} = Subgroup.centralizer {y} := by
  ext g
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ((Commute.inv_left_iff (a := y) (b := g)).1 (Commute.symm h)).symm
  · intro h
    exact ((Commute.inv_left_iff (a := y) (b := g)).2 (Commute.symm h)).symm

theorem centralizer_singleton_conj (x y : G) :
    Subgroup.centralizer {x * y * x⁻¹} =
      (Subgroup.centralizer {y}).map (MulAut.conj x).toMonoidHom := by
  rw [CFSG.HardMathSupport.Seitz.Proving.map_centralizer_singleton]
  rfl

theorem centralizer_sup_eq_top_of_conj {z e a b x : G}
    (hz : x * z * x⁻¹ = a ∨ x * z * x⁻¹ = a⁻¹) (he : x * e * x⁻¹ = b ∨ x * e * x⁻¹ = b⁻¹)
    (hab : Subgroup.centralizer {a} ⊔ Subgroup.centralizer {b} = ⊤) :
    Subgroup.centralizer {z} ⊔ Subgroup.centralizer {e} = ⊤ := by
  have hz' : Subgroup.centralizer {x * z * x⁻¹} = Subgroup.centralizer {a} := by
    rcases hz with h | h <;> rw [h]
    exact centralizer_singleton_inv a
  have he' : Subgroup.centralizer {x * e * x⁻¹} = Subgroup.centralizer {b} := by
    rcases he with h | h <;> rw [h]
    exact centralizer_singleton_inv b
  rw [centralizer_singleton_conj] at hz' he'
  have hmap : (Subgroup.centralizer {z} ⊔ Subgroup.centralizer {e}).map
      (MulAut.conj x).toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup, hz', he', hab]
  have hsurj : Function.Surjective (MulAut.conj x).toMonoidHom := (MulAut.conj x).surjective
  rw [eq_top_iff]
  intro g _
  obtain ⟨g', hg'⟩ := hsurj g
  have hmem : (MulAut.conj x).toMonoidHom g ∈
      (Subgroup.centralizer {z} ⊔ Subgroup.centralizer {e}).map (MulAut.conj x).toMonoidHom := by
    rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨y, hy, hyg⟩ := hmem
  have : y = g := (MulAut.conj x).injective hyg
  rwa [← this]

theorem mem_smul_sylow_comm {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) {z : G}
    (hzc : ∀ y ∈ P, y * z = z * y) (x : G) :
    ∀ y ∈ (x • P : Sylow p G), y * (x * z * x⁻¹) = (x * z * x⁻¹) * y := by
  intro y hy
  rw [← SetLike.mem_coe, Sylow.coe_smul] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  have := hzc w hw
  simp only [MulAut.smul_def, MulAut.conj_apply]
  calc x * w * x⁻¹ * (x * z * x⁻¹) = x * (w * z) * x⁻¹ := by group
    _ = x * (z * w) * x⁻¹ := by rw [this]
    _ = x * z * x⁻¹ * (x * w * x⁻¹) := by group

end Groups

@[expose] noncomputable def zStd (K : Type) [Field K] : adjointGroup .G2 K :=
  ⟨rootSL2 .G2 K ![1, 2] (orderThreeSL K),
    (exceptional_Lang_root_rank_one_data .G2 K ![1, 2]).2.2.2.2.1 _⟩

@[expose] noncomputable def eStd (K : Type) [Field K] : adjointGroup .G2 K :=
  ⟨rootSL2 .G2 K ![1, 0] (orderThreeSL K),
    (exceptional_Lang_root_rank_one_data .G2 K ![1, 0]).2.2.2.2.1 _⟩

@[expose] def G2SylowPairNormalForm : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K → 3 ∣ Nat.card K + 1 →
    ∀ P : Sylow 3 (adjointGroup .G2 K), ∀ z ∈ P, (∀ x ∈ P, x * z = z * x) → z ≠ 1 →
      z ^ 3 = 1 → ∀ e ∈ P, e ≠ 1 → e ^ 3 = 1 → e ∉ Subgroup.zpowers z →
        ∃ x : adjointGroup .G2 K, (x * z * x⁻¹ = zStd K ∨ x * z * x⁻¹ = (zStd K)⁻¹) ∧
          (x * e * x⁻¹ = eStd K ∨ x * e * x⁻¹ = (eStd K)⁻¹)

@[expose] def G2SplitPairGenerationCentral : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K → 3 ∣ Nat.card K + 1 →
    ExceptionsTransport.CentralInSylow 3 (zStd K) →
    Subgroup.centralizer {zStd K} ⊔ Subgroup.centralizer {eStd K} =
      (⊤ : Subgroup (adjointGroup .G2 K))

theorem g2NativeCentralizerPairsSylow_of_residuals (hA : G2SylowPairNormalForm)
    (hB : G2SplitPairGenerationCentral) : G2NativeCentralizerPairsSylow := by
  intro K _ _ hK h3 P z hzP hzc hz1 hzp e heP he1 hep hez
  obtain ⟨x, hxz, hxe⟩ := hA K hK h3 P z hzP hzc hz1 hzp e heP he1 hep hez
  have hcen : ExceptionsTransport.CentralInSylow 3 (zStd K) := by
    refine ⟨x • P, fun y hy => ?_⟩
    have h1 := mem_smul_sylow_comm P hzc x y hy
    rcases hxz with h | h
    · rwa [h] at h1
    · rw [h] at h1
      calc y * zStd K = zStd K * ((zStd K)⁻¹ * y) * zStd K := by group
        _ = zStd K * (y * (zStd K)⁻¹) * zStd K := by rw [← h1]
        _ = zStd K * y := by group
  exact centralizer_sup_eq_top_of_conj hxz hxe (hB K hK h3 hcen)

end CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
