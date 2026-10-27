module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbedding.ReeCenterOver

theorem exists_conj_mem_of_ti {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G)
    (hTI : ∀ g : G, g ∉ Subgroup.normalizer ((S : Subgroup G) : Set G) →
      (S : Subgroup G) ⊓ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊥)
    {Y Z : Subgroup G} (hZ : Z ≠ ⊥) (hZS : Z ≤ S) (hZY : Z ≤ Y)
    {y₀ : G} (hy₀ : y₀ ∈ Y) (hp : ∃ k : ℕ, y₀ ^ p ^ k = 1) :
    ∃ y ∈ Y, y⁻¹ * y₀ * y ∈ (S : Subgroup G) := by
  classical
  have hSp : IsPGroup p (S : Subgroup G) := S.isPGroup'
  set P₀ : Subgroup Y := (Y ⊓ (S : Subgroup G)).subgroupOf Y with hP₀
  have hP₀p : IsPGroup p P₀ := by
    intro x
    obtain ⟨k, hk⟩ := hSp ⟨(x : Y).1, (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  obtain ⟨P₁, hP₁⟩ := hP₀p.exists_le_sylow
  have hZP₁ : ∀ z (hz : z ∈ Z), (⟨z, hZY hz⟩ : Y) ∈ (P₁ : Subgroup Y) := fun z hz =>
    hP₁ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hZY hz, hZS hz⟩))
  have hP₁S : ∀ x ∈ (P₁ : Subgroup Y), (x : G) ∈ (S : Subgroup G) := by
    have hp' : IsPGroup p ((P₁ : Subgroup Y).map Y.subtype) := P₁.isPGroup'.map Y.subtype
    obtain ⟨T, hT⟩ := hp'.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
    have hgS : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
      by_contra hn
      have h := hTI g hn
      have hgT : ((g • S : Sylow p G) : Subgroup G) =
          (S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
        rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
        rfl
      apply hZ
      rw [eq_bot_iff, ← h]
      intro z hz
      refine Subgroup.mem_inf.2 ⟨hZS hz, ?_⟩
      rw [← hgT, hg]
      exact hT ⟨⟨z, hZY hz⟩, hZP₁ z hz, rfl⟩
    have hTS : T = S := by rw [← hg]; exact (Sylow.smul_eq_iff_mem_normalizer.2 hgS)
    intro x hx
    have : (x : G) ∈ (T : Subgroup G) := hT ⟨x, hx, rfl⟩
    rwa [hTS] at this
  obtain ⟨k, hk⟩ := hp
  set x₀ : Y := ⟨y₀, hy₀⟩
  have hx₀p : IsPGroup p (Subgroup.zpowers x₀) := by
    rintro ⟨_, m, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    have : x₀ ^ p ^ k = 1 := Subtype.ext hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    simp [this]
  obtain ⟨P₂, hP₂⟩ := hx₀p.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y P₁ P₂
  have hx₀ : x₀ ∈ (P₂ : Subgroup Y) := hP₂ (Subgroup.mem_zpowers x₀)
  rw [← hy, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at hx₀
  obtain ⟨z, hz, hzx⟩ := hx₀
  refine ⟨(y : G), y.2, ?_⟩
  have hz2 : y * z * y⁻¹ = x₀ := by simpa [MulAut.conj_apply] using hzx
  have hzG : (z : G) = (y : G)⁻¹ * y₀ * y := by
    have h3 : z = y⁻¹ * x₀ * y := by rw [← hz2]; group
    rw [h3]
    rfl
  rw [← hzG]
  exact hP₁S z hz

theorem conj_mem_inf_centralizer {G : Type*} [Group G] (S : Subgroup G) {b z : G}
    (hb : b ∈ Subgroup.normalizer (S : Set G)) (hz : z ∈ S ⊓ Subgroup.centralizer (S : Set G)) :
    b * z * b⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 hb z).1 hz.1, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro x hx
  have hx' : b⁻¹ * x * b ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hb) x).1 hx
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.1 hz.2 _ hx'
  calc x * (b * z * b⁻¹) = b * ((b⁻¹ * x * b) * z) * b⁻¹ := by group
    _ = b * (z * (b⁻¹ * x * b)) * b⁻¹ := by rw [h2]
    _ = (b * z * b⁻¹) * x := by group

end CFSG.AGLEmbedding.ReeCenterOver
