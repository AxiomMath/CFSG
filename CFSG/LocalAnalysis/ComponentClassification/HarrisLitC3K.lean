module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup

variable {G : Type} [Group G] {Q : Subgroup G} {S H : Type*} [Group S] [Group H]

theorem x_alternative_abs {θ : S →* ↥Q} (hθs : Function.Surjective θ) (hθk : θ.ker ≤ center S)
    (bl br : H →* S) {t : S} (hbt : ∀ a, bl a * t = t * bl a) (hrt : ∀ b, br b * t = t * br b)
    (hlr : ∀ a b, bl a * br b = br b * bl a)
    (hcl : ∀ n : S, n * t = t * n → ∀ a, ∃ a', n * bl a * n⁻¹ = bl a')
    (hcr : ∀ n : S, n * t = t * n → ∀ b, ∃ b', n * br b * n⁻¹ = br b')
    {n₁ : H} (hinter : ∀ a b, θ (bl a) = θ (br b) → (a = 1 ∧ b = 1) ∨ (a = n₁ ∧ b = n₁))
    (hn₁ : θ (bl n₁) = θ t ∧ θ (br n₁) = θ t) (hn₁1 : n₁ ≠ 1) {u : H} (hu1 : u ≠ 1)
    (hun : u ≠ n₁) :
    ∃ X₁ X₂ : Subgroup G, X₁ ≠ X₂ ∧ X₁ ≤ Q ⊓ centralizer {((θ t : ↥Q) : G)} ∧
      X₂ ≤ Q ⊓ centralizer {((θ t : ↥Q) : G)} ∧
      (X₁.subgroupOf (Q ⊓ centralizer {((θ t : ↥Q) : G)})).IsSubnormal ∧
      (X₂.subgroupOf (Q ⊓ centralizer {((θ t : ↥Q) : G)})).IsSubnormal ∧
      X₁ ≤ centralizer (X₂ : Set G) ∧ X₁ ⊓ X₂ = zpowers ((θ t : ↥Q) : G) ∧
      Nonempty (↥X₁ ≃* H) ∧ Nonempty (↥X₂ ≃* H) := by
  classical
  set w : G := ((θ t : ↥Q) : G) with hw
  set CW := Q ⊓ centralizer ({w} : Set G) with hCW
  set X₁ : Subgroup G := ((θ.comp bl).range).map Q.subtype with hX₁
  set X₂ : Subgroup G := ((θ.comp br).range).map Q.subtype with hX₂
  set N₀ : Subgroup G :=
    ((θ.comp (centralizer ({t} : Set S)).subtype).range).map Q.subtype with hN₀
  have hmemX₁ : ∀ g, g ∈ X₁ ↔ ∃ a, ((θ (bl a) : ↥Q) : G) = g := fun g => by
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  have hmemX₂ : ∀ g, g ∈ X₂ ↔ ∃ b, ((θ (br b) : ↥Q) : G) = g := fun g => by
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨_, ⟨b, rfl⟩, rfl⟩
  have hcw : ∀ n : S, n * t = t * n → ((θ n : ↥Q) : G) ∈ CW := by
    intro n hn
    refine ⟨(θ n).2, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hw, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hn]
  have hX₁N : X₁ ≤ N₀ := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, ⟨⟨bl a, mem_centralizer_singleton_iff.mpr (hbt a)⟩, rfl⟩, rfl⟩
  have hX₂N : X₂ ≤ N₀ := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨_, ⟨⟨br b, mem_centralizer_singleton_iff.mpr (hrt b)⟩, rfl⟩, rfl⟩
  have hNC : N₀ ≤ CW := by
    rintro _ ⟨_, ⟨⟨n, hn⟩, rfl⟩, rfl⟩
    exact hcw n (mem_centralizer_singleton_iff.mp hn)
  have hNX₁ : N₀ ≤ normalizer (X₁ : Set G) := by
    apply Sol76.le_normalizer_of_forall_conj_mem
    rintro _ ⟨_, ⟨⟨n, hn⟩, rfl⟩, rfl⟩ _ ⟨_, ⟨a, rfl⟩, rfl⟩
    obtain ⟨a', ha'⟩ := hcl n (mem_centralizer_singleton_iff.mp hn) a
    refine ⟨_, ⟨a', rfl⟩, ?_⟩
    change ((θ (bl a') : ↥Q) : G) = _
    rw [← ha', map_mul, map_mul, map_inv]
    rfl
  have hNX₂ : N₀ ≤ normalizer (X₂ : Set G) := by
    apply Sol76.le_normalizer_of_forall_conj_mem
    rintro _ ⟨_, ⟨⟨n, hn⟩, rfl⟩, rfl⟩ _ ⟨_, ⟨b, rfl⟩, rfl⟩
    obtain ⟨b', hb'⟩ := hcr n (mem_centralizer_singleton_iff.mp hn) b
    refine ⟨_, ⟨b', rfl⟩, ?_⟩
    change ((θ (br b') : ↥Q) : G) = _
    rw [← hb', map_mul, map_mul, map_inv]
    rfl
  have hCN : CW ≤ normalizer (N₀ : Set G) := by
    apply Sol76.le_normalizer_of_forall_conj_mem
    rintro y ⟨hyQ, hyw⟩ _ ⟨_, ⟨⟨n, hn⟩, rfl⟩, rfl⟩
    obtain ⟨m, hm⟩ := hθs ⟨y, hyQ⟩
    have hmt : m * t * m⁻¹ * t⁻¹ ∈ center S := hθk (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hm]
      apply Subtype.ext
      have h1 := mem_centralizer_singleton_iff.mp hyw
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [hw] at h1
      calc y * (θ t : G) * y⁻¹ * (θ t : G)⁻¹ = (y * (θ t : G)) * y⁻¹ * (θ t : G)⁻¹ := rfl
        _ = ((θ t : G) * y) * y⁻¹ * (θ t : G)⁻¹ := by rw [h1]
        _ = 1 := by group)
    obtain ⟨z, hzc, hzt⟩ : ∃ z ∈ center S, m * t * m⁻¹ = z * t := ⟨_, hmt, by group⟩
    have hzc' : ∀ g, g * z = z * g := mem_center_iff.mp hzc
    have hzi : ∀ g, g * z⁻¹ = z⁻¹ * g := mem_center_iff.mp (inv_mem hzc)
    have hm1 : m⁻¹ * t * m = z⁻¹ * t := by
      have h3 : m⁻¹ * (z * t) * m = z * (m⁻¹ * t * m) := by
        rw [show m⁻¹ * (z * t) * m = (m⁻¹ * z) * t * m by group, hzc' m⁻¹]
        group
      rw [← hzt] at h3
      have h4 : t = z * (m⁻¹ * t * m) := by rw [← h3]; group
      calc m⁻¹ * t * m = z⁻¹ * (z * (m⁻¹ * t * m)) := by group
        _ = z⁻¹ * t := by rw [← h4]
    have hn' : m * n * m⁻¹ ∈ centralizer ({t} : Set S) := by
      rw [mem_centralizer_singleton_iff]
      have hnt := mem_centralizer_singleton_iff.mp hn
      calc m * n * m⁻¹ * t = m * n * (m⁻¹ * t * m) * m⁻¹ := by group
        _ = m * n * (z⁻¹ * t) * m⁻¹ := by rw [hm1]
        _ = m * (n * z⁻¹) * t * m⁻¹ := by group
        _ = m * (z⁻¹ * n) * t * m⁻¹ := by rw [hzi n]
        _ = (m * z⁻¹) * n * t * m⁻¹ := by group
        _ = (z⁻¹ * m) * n * t * m⁻¹ := by rw [hzi m]
        _ = z⁻¹ * (m * (n * t) * m⁻¹) := by group
        _ = z⁻¹ * (m * (t * n) * m⁻¹) := by rw [hnt]
        _ = z⁻¹ * (m * t * m⁻¹) * (m * n * m⁻¹) := by group
        _ = t * (m * n * m⁻¹) := by rw [hzt]; group
    refine ⟨_, ⟨⟨m * n * m⁻¹, hn'⟩, rfl⟩, ?_⟩
    change ((θ (m * n * m⁻¹) : ↥Q) : G) = _
    rw [map_mul, map_mul, map_inv, hm]
    rfl
  have hs₁ : (X₁.subgroupOf CW).IsSubnormal :=
    Sol76.isSubnormal_subgroupOf_of_le_normalizer hX₁N hNC hNX₁ hCN
  have hs₂ : (X₂.subgroupOf CW).IsSubnormal :=
    Sol76.isSubnormal_subgroupOf_of_le_normalizer hX₂N hNC hNX₂ hCN
  have hX₁X₂ : X₁ ⊓ X₂ = zpowers w := by
    apply le_antisymm
    · rintro g ⟨hg₁, hg₂⟩
      obtain ⟨a, rfl⟩ := (hmemX₁ g).mp hg₁
      obtain ⟨b, hb⟩ := (hmemX₂ _).mp hg₂
      rcases hinter a b (Subtype.ext hb.symm) with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [map_one, map_one]
        exact one_mem _
      · rw [hn₁.1]
        exact mem_zpowers _
    · rw [zpowers_le]
      exact ⟨(hmemX₁ w).mpr ⟨n₁, by rw [hn₁.1]⟩, (hmemX₂ w).mpr ⟨n₁, by rw [hn₁.2]⟩⟩
  have hne : X₁ ≠ X₂ := by
    intro hEq
    have hu : ((θ (bl u) : ↥Q) : G) ∈ X₂ := hEq ▸ (hmemX₁ _).mpr ⟨u, rfl⟩
    obtain ⟨b, hb⟩ := (hmemX₂ _).mp hu
    rcases hinter u b (Subtype.ext hb.symm) with ⟨h, -⟩ | ⟨h, -⟩
    · exact hu1 h
    · exact hun h
  have hinj₁ : Function.Injective (Q.subtype.comp (θ.comp bl)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply] at ha
    have ha' : θ (bl a) = θ (br 1) := by
      rw [map_one, map_one]
      exact Subtype.ext ha
    rcases hinter a 1 ha' with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h.symm hn₁1
  have hinj₂ : Function.Injective (Q.subtype.comp (θ.comp br)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply] at hb
    have hb' : θ (bl 1) = θ (br b) := by
      rw [map_one, map_one]
      exact (Subtype.ext hb).symm
    rcases hinter 1 b hb' with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h.symm hn₁1
  have hrange₁ : (Q.subtype.comp (θ.comp bl)).range = X₁ := by
    rw [MonoidHom.range_comp]
  have hrange₂ : (Q.subtype.comp (θ.comp br)).range = X₂ := by
    rw [MonoidHom.range_comp]
  refine ⟨X₁, X₂, hne, hX₁N.trans hNC, hX₂N.trans hNC, hs₁, hs₂, ?_, hX₁X₂,
    ⟨(MulEquiv.subgroupCongr hrange₁).symm.trans (MonoidHom.ofInjective hinj₁).symm⟩,
    ⟨(MulEquiv.subgroupCongr hrange₂).symm.trans (MonoidHom.ofInjective hinj₂).symm⟩⟩
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  change ((θ (br b) : ↥Q) : G) * ((θ (bl a) : ↥Q) : G) =
    ((θ (bl a) : ↥Q) : G) * ((θ (br b) : ↥Q) : G)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hlr]

end CFSG.ComponentClassification.HarrisLit.C3
