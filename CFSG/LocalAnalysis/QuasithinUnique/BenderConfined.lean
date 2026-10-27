module

public import CFSG.LocalAnalysis.QuasithinUnique.FusionDatum
public import CFSG.Milestones.QT_unique_Shult_simple_strongly_closed_TI_models

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem mem_of_inf_conj_ne_bot {G : Type*} [Group G] {U M : Subgroup G}
    (hcent : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ M)
    (hfus : ∀ u ∈ U, ∀ g : G, g⁻¹ * u * g ∈ U → ∃ m ∈ M, g⁻¹ * u * g = m⁻¹ * u * m)
    {g : G} (hg : U ⊓ U.map (MulAut.conj g).toMonoidHom ≠ ⊥) : g ∈ M := by
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
  obtain ⟨hvU, u, huU, huv⟩ := Subgroup.mem_inf.mp hv
  have huv' : g * u * g⁻¹ = v := by simpa [MulAut.conj_apply] using huv
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hv1
    ext
    simpa using huv'.symm
  have hconj : g⁻¹⁻¹ * u * g⁻¹ ∈ U := by simpa [huv'] using hvU
  obtain ⟨m, hmM, hm⟩ := hfus u huU g⁻¹ hconj
  have hcomm : m * g ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * u * g⁻¹ = m⁻¹ * u * m := by simpa using hm
    calc m * g * u = m * (g * u * g⁻¹) * g := by group
      _ = m * (m⁻¹ * u * m) * g := by rw [h1]
      _ = u * (m * g) := by group
  have hmg : m * g ∈ M := hcent u huU hu1 hcomm
  have : g = m⁻¹ * (m * g) := by group
  rw [this]
  exact M.mul_mem (M.inv_mem hmM) hmg

theorem isTI_of_centralizer_le {G : Type*} [Group G] {U M : Subgroup G}
    (hM : Subgroup.normalizer (U : Set G) = M)
    (hcent : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ M)
    (hfus : ∀ u ∈ U, ∀ g : G, g⁻¹ * u * g ∈ U → ∃ m ∈ M, g⁻¹ * u * g = m⁻¹ * u * m) :
    fusionIsTI U := by
  intro g hne
  by_contra hbot
  apply hne
  have hgM : g ∈ Subgroup.normalizer (U : Set G) := hM ▸ mem_of_inf_conj_ne_bot hcent hfus hbot
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hgM y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgM) x).mp hx
    simpa using this

theorem UniqueFusionDatum.fusionIsBenderGroup_of_centralizer_le
    {G : Type} [Group G] [Finite G]
    {T M U : Subgroup G} {z : G} (hd : UniqueFusionDatum T M U z)
    (hcent : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ M) :
    fusionIsBenderGroup G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hd.setting.simple
  have hT2 : ¬ 2 ∣ T.index := by
    simpa only [index_subgroupOf_top] using hd.setting.sylow.2.2
  let T' : Sylow 2 G := hd.setting.isPGroup.toSylow hT2
  have hUM : U ≤ M := hd.le_T.trans hd.setting.le
  have hfus : ∀ u ∈ U, ∀ g : G, g⁻¹ * u * g ∈ U → ∃ m ∈ M, g⁻¹ * u * g = m⁻¹ * u * m := by
    intro u hu g hg
    refine hd.control u (hUM hu) ⟨1, ?_⟩ g (hUM hg)
    simpa using hd.elem.2 u hu
  exact CFSG.Milestones.qt_unique_shult_simple_strongly_closed_ti_models G hd.setting.nonabelian
    T' U hd.le_T hd.ne_bot hd.elem hd.stronglyClosed
    (isTI_of_centralizer_le hd.normalizer_eq hcent hfus)

end CFSG.QuasithinUnique
