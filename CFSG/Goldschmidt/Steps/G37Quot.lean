module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Goldschmidt.Steps.G37CoreX

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)
open scoped commutatorElement

section Images

variable {G G' : Type*} [Group G] [Group G']

theorem isComponentOf_map' (f : G →* G') {K X : Subgroup G} (hK : IsComponentOf K X)
    (hKf : ¬ K ≤ f.ker) : IsComponentOf (K.map f) (X.map f) := by
  refine ⟨Subgroup.map_mono hK.1, ?_, ?_⟩
  · have h1 := hK.2.1.map (f.subgroupMap_surjective X)
    convert h1 using 1
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hK.1 hk⟩, hk, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
  · have hq : CFSG.IsQuasisimple K := ⟨Group.isPerfect_def.mpr hK.2.2.2.1, hK.2.2.2.2,
      CFSG.Walter.IsQuasisimple.exists_mul_ne_mul hK.2.2⟩
    have h3 := CFSG.LocalCores.isQuasisimple_map hq f hKf
    exact ⟨CFSG.LocalCores.isQuasisimple_nontrivial h3, Group.isPerfect_def.mp h3.1, h3.2.1⟩

theorem nonempty_centerQuotientEquiv {P Q : Type*} [Group P] [Group Q] (hP : Group.IsPerfect P)
    (f : P →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center P) :
    Nonempty (P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q) := by
  have hc : Subgroup.center P = ((QuotientGroup.mk' (Subgroup.center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.LocalCores.comap_center_eq_of_perfect hP f hf hker).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

theorem commutatorElement_mul_left_of_commute {x y z : G} (h : z * y = y * z) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev,
    show x * z * y = x * y * z by rw [mul_assoc, h, ← mul_assoc]]
  group

theorem commutatorElement_mul_right_of_commute {x y z : G} (h : z * x = x * z) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have h' : z * x⁻¹ = x⁻¹ * z := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [h']
    _ = x * y * x⁻¹ * y⁻¹ := by group

end Images

section Correspondence

variable {G : Type} [Group G] {H : Subgroup G}

theorem le_preOf_iff {B : Subgroup G} (hBH : B ≤ H)
    {L : Subgroup (H ⧸ goldschmidtOddCore H)} : B ≤ preOf H L ↔ barOf H B ≤ L := by
  rw [barOf, Subgroup.map_le_iff_le_comap]
  constructor
  · intro h x hx
    obtain ⟨y, hy, hyx⟩ := h hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro h x hx
    exact ⟨⟨x, hBH hx⟩, h hx, rfl⟩

theorem preOf_le (L : Subgroup (H ⧸ goldschmidtOddCore H)) : preOf H L ≤ H :=
  Subgroup.map_subtype_le _

theorem barOf_preOf (L : Subgroup (H ⧸ goldschmidtOddCore H)) : barOf H (preOf H L) = L := by
  have h : (preOf H L).subgroupOf H = L.comap (QuotientGroup.mk' (goldschmidtOddCore H)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [barOf, h, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem preOf_barOf' {B : Subgroup G} (hBH : B ≤ H) : preOf H (barOf H B) = B ⊔ oddCoreOf H := by
  rw [preOf, barOf, Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hBH]
  rfl

theorem preOf_bot : preOf H ⊥ = oddCoreOf H := by
  rw [preOf, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  rfl

theorem barOf_eq_bot_iff {B : Subgroup G} (hBH : B ≤ H) : barOf H B = ⊥ ↔ B ≤ oddCoreOf H := by
  rw [← preOf_bot, le_preOf_iff hBH, le_bot_iff]

theorem barOf_mono {B B' : Subgroup G} (h : B ≤ B') : barOf H B ≤ barOf H B' :=
  Subgroup.map_mono fun _ hx => h hx

theorem barOf_sup {B₁ B₂ : Subgroup G} (h₁ : B₁ ≤ H) (h₂ : B₂ ≤ H) :
    barOf H (B₁ ⊔ B₂) = barOf H B₁ ⊔ barOf H B₂ := by
  rw [barOf, Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]
  rfl

theorem subgroupOf_commutator {B₁ B₂ : Subgroup G} (h₁ : B₁ ≤ H) (h₂ : B₂ ≤ H) :
    ⁅B₁, B₂⁆.subgroupOf H = ⁅B₁.subgroupOf H, B₂.subgroupOf H⁆ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁,
    Subgroup.map_subgroupOf_eq_of_le h₂,
    Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_mono h₁ h₂).trans
      (commutator_self_le H))]

theorem barOf_commutator {B₁ B₂ : Subgroup G} (h₁ : B₁ ≤ H) (h₂ : B₂ ≤ H) :
    barOf H ⁅B₁, B₂⁆ = ⁅barOf H B₁, barOf H B₂⁆ := by
  rw [barOf, subgroupOf_commutator h₁ h₂, Subgroup.map_commutator]
  rfl

theorem barOf_zpowers {x : G} (hx : x ∈ H) :
    barOf H (Subgroup.zpowers x) =
      Subgroup.zpowers (QuotientGroup.mk' (goldschmidtOddCore H) ⟨x, hx⟩) := by
  have h : (Subgroup.zpowers x).subgroupOf H = Subgroup.zpowers (⟨x, hx⟩ : H) := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hx), MonoidHom.map_zpowers]
    rfl
  rw [barOf, h, MonoidHom.map_zpowers]

theorem mk_mem_normalizer_barOf {X : Subgroup G} (hXH : X ≤ H) {g : G} (hg : g ∈ H)
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) :
    QuotientGroup.mk' (goldschmidtOddCore H) ⟨g, hg⟩ ∈
      Subgroup.normalizer (barOf H X : Set (H ⧸ goldschmidtOddCore H)) := by
  have h1 : (⟨g, hg⟩ : H) ∈ Subgroup.normalizer (X.subgroupOf H : Set H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hXH]
    exact hgX
  exact Subgroup.le_normalizer_map _ ⟨_, h1, rfl⟩

theorem barOf_normalizer_le {X : Subgroup G} (hXH : X ≤ H) :
    barOf H (H ⊓ Subgroup.normalizer (X : Set G)) ≤
      Subgroup.normalizer (barOf H X : Set (H ⧸ goldschmidtOddCore H)) := by
  rintro _ ⟨x, hx, rfl⟩
  exact mk_mem_normalizer_barOf hXH x.2 (Subgroup.mem_inf.mp hx).2

theorem commutator_le_oddCoreOf_of_mk_mem_centralizer {L : Subgroup G} (hLH : L ≤ H) {x : G}
    (hx : x ∈ H)
    (hxL : QuotientGroup.mk' (goldschmidtOddCore H) ⟨x, hx⟩ ∈
      Subgroup.centralizer (barOf H L : Set (H ⧸ goldschmidtOddCore H))) :
    ⁅Subgroup.zpowers x, L⁆ ≤ oddCoreOf H := by
  have hxH : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hx
  rw [← barOf_eq_bot_iff ((Subgroup.commutator_mono hxH hLH).trans (commutator_self_le H)),
    barOf_commutator hxH hLH, barOf_zpowers hx]
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  rw [Subgroup.zpowers_le]
  exact hxL

end Correspondence

end CFSG.Goldschmidt.G37
