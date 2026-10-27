module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSFusion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.QuasithinUnique.Id2519.UHS

open CFSG.Sporadic.Schreier
open scoped commutatorElement

@[expose] def TabConjHS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    PatHS X K t → Subgroup.center ↥X = ⊥ →
    ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u

theorem card_alt_six' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem tabConjHS
    : TabConjHS := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat hZ u huK hu2
  obtain ⟨hA6, ⟨e⟩, l, hl, hlt⟩ := hpat
  let θ : ↥X ≃* PP :=
    ((((QuotientGroup.quotientBot (G := ↥X)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans e).trans hsPermEquiv).trans
      (MulEquiv.subgroupCongr hsP_eq_original)
  set c : G := t * l⁻¹ with hcdef
  have hcx : ∀ x ∈ X, c * x = x * c := by
    intro x hx
    calc c * x = t * (l⁻¹ * x * l) * l⁻¹ := by rw [hcdef]; group
      _ = t * (t⁻¹ * x * t) * l⁻¹ := by rw [← hlt x hx]
      _ = x * c := by rw [hcdef]; group
  have hct : t = c * l := by rw [hcdef]; group
  have hcc : c * c * (l * l) = 1 := by
    calc c * c * (l * l) = c * (c * l) * l := by group
      _ = c * (l * c) * l := by rw [hcx l hl]
      _ = (c * l) * (c * l) := by group
      _ = t * t := by rw [← hct]
      _ = 1 := ht2
  have hmemcc : c * c ∈ X := by
    have : c * c = (l * l)⁻¹ := eq_inv_of_mul_eq_one_left hcc
    rw [this]
    exact X.inv_mem (X.mul_mem hl hl)
  have hcc1 : c * c = 1 := by
    have hcent : (⟨c * c, hmemcc⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro g
      refine Subtype.ext ?_
      change (g : G) * (c * c) = c * c * (g : G)
      have h1 := hcx g g.2
      calc (g : G) * (c * c) = (g * c) * c := by group
        _ = (c * g) * c := by rw [h1]
        _ = c * (g * c) := by group
        _ = c * (c * g) := by rw [h1]
        _ = c * c * g := by group
    rw [hZ, Subgroup.mem_bot] at hcent
    exact congrArg Subtype.val hcent
  have hl2 : l * l = 1 := by
    have := hcc
    rwa [hcc1, one_mul] at this
  have hl1 : l ≠ 1 := by
    intro h1
    have hcent : ∀ x ∈ X, t * x = x * t := by
      intro x hx
      rw [hct, h1, mul_one]
      exact hcx x hx
    have hle : ⁅X, Subgroup.zpowers t⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro x hx g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hk : x * t ^ k = t ^ k * x :=
        ((Commute.zpow_left (show Commute t x from hcent x hx) k)).eq.symm
      rw [Subgroup.mem_bot, commutatorElement_def, hk]
      group
    rw [hcomm] at hle
    have hone : ∀ x : ↥X, x = 1 := fun x => Subtype.ext (Subgroup.mem_bot.mp (hle x.2))
    have hq := hXq.2.1
    have : Nontrivial (↥X ⧸ Subgroup.center ↥X) := hq.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥X ⧸ Subgroup.center ↥X)
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [hone a', hone b'])
  have hKle : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) :=
    hK.le.trans (Subgroup.map_subtype_le _)
  have hKX : K ≤ X := hKle.trans inf_le_left
  have hKC : ∀ x ∈ K, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKle hx).2
  have hcommL : ∀ x ∈ X, (x * t = t * x ↔ x * l = l * x) := by
    intro x hx
    have hxc := hcx x hx
    rw [hct]
    constructor
    · intro h
      have h' : c * (x * l) = c * (l * x) := by
        calc c * (x * l) = (c * x) * l := by group
          _ = (x * c) * l := by rw [hxc]
          _ = x * (c * l) := by group
          _ = (c * l) * x := h
          _ = c * (l * x) := by group
      exact mul_left_cancel h'
    · intro h
      calc x * (c * l) = (x * c) * l := by group
        _ = (c * x) * l := by rw [hxc]
        _ = c * (x * l) := by group
        _ = c * (l * x) := by rw [h]
        _ = c * l * x := by group
  let Kb : Subgroup PP := (K.subgroupOf X).map θ.toMonoidHom
  have hKb : Nat.card Kb = 360 := by
    obtain ⟨e6⟩ := hA6
    have h1 : Nat.card Kb = Nat.card (K.subgroupOf X) :=
      Subgroup.card_map_of_injective θ.injective
    have h2 : Nat.card (K.subgroupOf X) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
    have h3 : Nat.card K = 360 := (Nat.card_congr e6.toEquiv).trans card_alt_six'
    rw [h1, h2, h3]
  set s : PP := θ ⟨l, hl⟩ with hsdef
  have hs2 : s * s = 1 := by
    rw [hsdef, ← map_mul]
    have : (⟨l, hl⟩ * ⟨l, hl⟩ : ↥X) = 1 := Subtype.ext hl2
    rw [this, map_one]
  have hs1 : s ≠ 1 := by
    intro h
    have : (⟨l, hl⟩ : ↥X) = 1 := θ.injective (by rw [← hsdef, h, map_one])
    exact hl1 (congrArg Subtype.val this)
  have hKbc : ∀ k ∈ Kb, k * s = s * k := by
    rintro _ ⟨x, hx, rfl⟩
    have hxl : (x : G) * l = l * x := (hcommL x x.2).1 (hKC x hx)
    have : x * ⟨l, hl⟩ = ⟨l, hl⟩ * x := Subtype.ext hxl
    show θ x * θ ⟨l, hl⟩ = θ ⟨l, hl⟩ * θ x
    rw [← map_mul, ← map_mul, this]
  have hKbn : ∀ c' : PP, c' * s = s * c' → ∀ k ∈ Kb, c' * k * c'⁻¹ ∈ Kb := by
    intro c' hc' k hk
    obtain ⟨c₀, rfl⟩ := θ.surjective c'
    obtain ⟨x, hx, rfl⟩ := hk
    have hc₀ : c₀ * ⟨l, hl⟩ = ⟨l, hl⟩ * c₀ := θ.injective (by rw [map_mul, map_mul]; exact hc')
    have hc₀t : (c₀ : G) * t = t * c₀ :=
      (hcommL c₀ c₀.2).2 (congrArg Subtype.val hc₀)
    have hc₀mem : (c₀ : G) ∈ X ⊓ Subgroup.centralizer ({t} : Set G) :=
      ⟨c₀.2, Subgroup.mem_centralizer_singleton_iff.2 hc₀t⟩
    have hnormK : (c₀ : G) ∈ Subgroup.normalizer (K : Set G) := by
      have := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains
        (X ⊓ Subgroup.centralizer ({t} : Set G)) (Subgroup.le_normalizer hc₀mem)
      rwa [← hK] at this
    have hxK : (c₀ * x * c₀⁻¹ : ↥X) ∈ K.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp hnormK x).mp hx
    exact ⟨c₀ * x * c₀⁻¹, hxK, by simp [map_mul, map_inv]⟩
  have huX : u ∈ X := hKX huK
  have hu'mem : θ ⟨u, huX⟩ ∈ Kb := ⟨⟨u, huX⟩, huK, rfl⟩
  have hu'2 : θ ⟨u, huX⟩ * θ ⟨u, huX⟩ = 1 := by
    rw [← map_mul]
    have : (⟨u, huX⟩ * ⟨u, huX⟩ : ↥X) = 1 := Subtype.ext hu2
    rw [this, map_one]
  obtain ⟨x', hx'⟩ := hs_fusion s hs2 hs1 Kb hKb hKbc hKbn _ hu'mem hu'2
  obtain ⟨x₁, rfl⟩ := θ.surjective x'
  have hx₁ : (x₁ : G) * l * (x₁ : G)⁻¹ = l * u := by
    have : x₁ * ⟨l, hl⟩ * x₁⁻¹ = ⟨l, hl⟩ * ⟨u, huX⟩ := θ.injective (by
      rw [map_mul, map_mul, map_inv, map_mul]
      exact hx')
    exact congrArg Subtype.val this
  refine ⟨(x₁ : G)⁻¹, X.inv_mem x₁.2, ?_⟩
  rw [inv_inv, hct]
  calc (x₁ : G) * (c * l) * (x₁ : G)⁻¹ = c * ((x₁ : G) * l * (x₁ : G)⁻¹) := by
        calc (x₁ : G) * (c * l) * (x₁ : G)⁻¹ = ((x₁ : G) * c) * l * (x₁ : G)⁻¹ := by group
          _ = (c * (x₁ : G)) * l * (x₁ : G)⁻¹ := by rw [← hcx x₁ x₁.2]
          _ = c * ((x₁ : G) * l * (x₁ : G)⁻¹) := by group
    _ = c * (l * u) := by rw [hx₁]
    _ = c * l * u := by group

end CFSG.QuasithinUnique.Id2519.UHS
