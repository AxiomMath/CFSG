module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyDef

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {G : Type} [Group G] {t r : G} {Θ : HModel →* G}

@[expose] def confConj (c : G) (Θ : HModel →* G) : HModel →* G :=
  (MulAut.conj c).toMonoidHom.comp Θ

@[simp] theorem confConj_apply (c : G) (Θ : HModel →* G) (x : HModel) :
    confConj c Θ x = c * Θ x * c⁻¹ := rfl

theorem FyConf.orderOf_r (h : FyConf t r Θ) : orderOf r = 3 := by
  rw [← h.r_eq, orderOf_injective Θ h.inj]
  have h1 : orderOf (Multiplicative.ofAdd (1 : ZMod 3)) = 3 := by
    rw [orderOf_ofAdd_eq_addOrderOf]
    exact ZMod.addOrderOf_one 3
  rw [Prod.orderOf, Prod.orderOf]
  simp [h1]

theorem FyConf.conj (h : FyConf t r Θ) (c : G) (hc : c * t = t * c) :
    FyConf t (c * r * c⁻¹) (confConj c Θ) where
  inj := by
    intro a b hab
    apply h.inj
    simpa using hab
  mem_range := by
    intro x
    have hct : c⁻¹ * t = t * c⁻¹ := by
      calc c⁻¹ * t = c⁻¹ * t * c * c⁻¹ := by group
        _ = c⁻¹ * (t * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hc]
        _ = t * c⁻¹ := by group
    constructor
    · rintro ⟨hxt, hxr⟩
      have h1 : c⁻¹ * x * c ∈ Θ.range := by
        refine (h.mem_range _).1 ⟨?_, ?_⟩
        · calc c⁻¹ * x * c * t = c⁻¹ * x * (c * t) := by group
            _ = c⁻¹ * (x * t) * c := by rw [hc]; group
            _ = c⁻¹ * (t * x) * c := by rw [hxt]
            _ = (c⁻¹ * t) * x * c := by group
            _ = t * c⁻¹ * x * c := by rw [hct]
            _ = t * (c⁻¹ * x * c) := by group
        · calc c⁻¹ * x * c * r = c⁻¹ * x * (c * r * c⁻¹) * c := by group
            _ = c⁻¹ * (x * (c * r * c⁻¹)) * c := by group
            _ = c⁻¹ * ((c * r * c⁻¹) * x) * c := by rw [hxr]
            _ = r * (c⁻¹ * x * c) := by group
      obtain ⟨a, ha⟩ := h1
      refine ⟨a, ?_⟩
      show c * Θ a * c⁻¹ = x
      rw [ha]; group
    · rintro ⟨a, rfl⟩
      have h1 : Θ a ∈ Θ.range := ⟨a, rfl⟩
      obtain ⟨h2, h3⟩ := (h.mem_range _).2 h1
      refine ⟨?_, ?_⟩
      · show c * Θ a * c⁻¹ * t = t * (c * Θ a * c⁻¹)
        calc c * Θ a * c⁻¹ * t = c * Θ a * (c⁻¹ * t) := by group
          _ = c * Θ a * (t * c⁻¹) := by rw [hct]
          _ = c * (Θ a * t) * c⁻¹ := by group
          _ = c * (t * Θ a) * c⁻¹ := by rw [h2]
          _ = (c * t) * Θ a * c⁻¹ := by group
          _ = (t * c) * Θ a * c⁻¹ := by rw [hc]
          _ = t * (c * Θ a * c⁻¹) := by group
      · show c * Θ a * c⁻¹ * (c * r * c⁻¹) = (c * r * c⁻¹) * (c * Θ a * c⁻¹)
        calc c * Θ a * c⁻¹ * (c * r * c⁻¹) = c * (Θ a * r) * c⁻¹ := by group
          _ = c * (r * Θ a) * c⁻¹ := by rw [h3]
          _ = (c * r * c⁻¹) * (c * Θ a * c⁻¹) := by group
  t_eq := by
    show c * Θ (DihedralGroup.r 2, 1, 1) * c⁻¹ = t
    rw [h.t_eq]
    calc c * t * c⁻¹ = t * c * c⁻¹ := by rw [hc]
      _ = t := by group
  r_eq := by
    show c * Θ (1, Multiplicative.ofAdd 1, 1) * c⁻¹ = c * r * c⁻¹
    rw [h.r_eq]
  v_conj := by
    obtain ⟨δ, hδ, ⟨g, hg⟩, hng⟩ := h.v_conj
    refine ⟨δ, hδ, ⟨c * g, ?_⟩, ?_⟩
    · show c * Θ (δ, 1, v0) * c⁻¹ = c * g * t * (c * g)⁻¹
      rw [hg]; group
    · rintro ⟨g', hg'⟩
      apply hng
      refine ⟨c⁻¹ * g', ?_⟩
      have hg'' : t * (c * Θ (δ, 1, v0) * c⁻¹) = g' * t * g'⁻¹ := hg'
      have hct' : t * c = c * t := hc.symm
      calc t * Θ (δ, 1, v0) = c⁻¹ * (c * t) * Θ (δ, 1, v0) * c⁻¹ * c := by group
        _ = c⁻¹ * (t * c) * Θ (δ, 1, v0) * c⁻¹ * c := by rw [hct']
        _ = c⁻¹ * (t * (c * Θ (δ, 1, v0) * c⁻¹)) * c := by group
        _ = c⁻¹ * (g' * t * g'⁻¹) * c := by rw [hg'']
        _ = c⁻¹ * g' * t * (c⁻¹ * g')⁻¹ := by group
  one_class := by
    intro a hat ha3
    obtain ⟨n, hnt, hn⟩ := h.one_class a hat ha3
    refine ⟨c * n, ?_, ?_⟩
    · calc c * n * t = c * (n * t) := by group
        _ = c * (t * n) := by rw [hnt]
        _ = (c * t) * n := by group
        _ = (t * c) * n := by rw [hc]
        _ = t * (c * n) := by group
    · calc c * n * a * (c * n)⁻¹ = c * (n * a * n⁻¹) * c⁻¹ := by group
        _ = c * r * c⁻¹ := by rw [hn]
  fusion := by
    obtain ⟨n, hnt, hn⟩ := h.fusion
    refine ⟨c * n * c⁻¹, ?_, ?_⟩
    · have hct : c⁻¹ * t = t * c⁻¹ := by
        calc c⁻¹ * t = c⁻¹ * t * c * c⁻¹ := by group
          _ = c⁻¹ * (t * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hc]
          _ = t * c⁻¹ := by group
      calc c * n * c⁻¹ * t = c * n * (c⁻¹ * t) := by group
        _ = c * n * (t * c⁻¹) := by rw [hct]
        _ = c * (n * t) * c⁻¹ := by group
        _ = c * (t * n) * c⁻¹ := by rw [hnt]
        _ = (c * t) * n * c⁻¹ := by group
        _ = (t * c) * n * c⁻¹ := by rw [hc]
        _ = t * (c * n * c⁻¹) := by group
    · show c * n * c⁻¹ * (c * Θ (DihedralGroup.sr 0, 1, 1) * c⁻¹) * (c * n * c⁻¹)⁻¹ =
        c * Θ (DihedralGroup.sr 1, 1, Equiv.swap 0 1) * c⁻¹
      rw [← hn]; group

theorem FyCoset.conj {L : Subgroup G} {f y : G} (h : FyCoset L f y Θ) (c : G)
    (hcf : ∀ z : G, z ∈ L ⊔ zpowers f ↔ c * z * c⁻¹ ∈ L ⊔ zpowers f)
    (hcy : ∀ z : G, z ∈ L ⊔ zpowers y ↔ c * z * c⁻¹ ∈ L ⊔ zpowers y) :
    FyCoset L f y (confConj c Θ) where
  mem_f := by
    intro d c' σ
    rw [confConj_apply, ← hcf]
    exact h.mem_f d c' σ
  mem_y := by
    intro d c' σ
    rw [confConj_apply, ← hcy]
    exact h.mem_y d c' σ

theorem FyConf.exists_conj_cent (h : FyConf t r Θ) {u : G} (hur : u * r = r * u)
    (hu : ∃ g : G, u = g * t * g⁻¹) :
    ∃ g : G, g * r = r * g ∧ u = g * t * g⁻¹ := by
  obtain ⟨g, hg⟩ := hu
  have hgt : g⁻¹ * u * g = t := by rw [hg]; group
  have hr' : (g⁻¹ * r * g) * t = t * (g⁻¹ * r * g) := by
    calc g⁻¹ * r * g * t = g⁻¹ * r * (g * t * g⁻¹) * g := by group
      _ = g⁻¹ * (r * u) * g := by rw [← hg]; group
      _ = g⁻¹ * (u * r) * g := by rw [hur]
      _ = (g⁻¹ * u * g) * (g⁻¹ * r * g) := by group
      _ = t * (g⁻¹ * r * g) := by rw [hgt]
  have hord : orderOf (g⁻¹ * r * g) = 3 := by
    rw [← h.orderOf_r]
    exact (SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * r = g⁻¹ * r * g * g⁻¹ by group)).symm
  obtain ⟨n, hnt, hn⟩ := h.one_class _ hr' hord
  refine ⟨g * n⁻¹, ?_, ?_⟩
  · have h1 : n * (g⁻¹ * r * g) * n⁻¹ = r := hn
    have h2 : (g * n⁻¹)⁻¹ * r * (g * n⁻¹) = r := by
      calc (g * n⁻¹)⁻¹ * r * (g * n⁻¹) = n * (g⁻¹ * r * g) * n⁻¹ := by group
        _ = r := h1
    calc g * n⁻¹ * r = (g * n⁻¹) * ((g * n⁻¹)⁻¹ * r * (g * n⁻¹)) := by rw [h2]
      _ = r * (g * n⁻¹) := by group
  · have hnt' : n⁻¹ * t = t * n⁻¹ := by
      calc n⁻¹ * t = n⁻¹ * t * n * n⁻¹ := by group
        _ = n⁻¹ * (t * n) * n⁻¹ := by group
        _ = n⁻¹ * (n * t) * n⁻¹ := by rw [hnt]
        _ = t * n⁻¹ := by group
    calc u = g * t * g⁻¹ := hg
      _ = g * (t * n⁻¹ * n) * g⁻¹ := by group
      _ = g * (n⁻¹ * t * n) * g⁻¹ := by rw [← hnt']
      _ = g * n⁻¹ * t * (g * n⁻¹)⁻¹ := by group

end CFSG.EvenSporadicStandard.TwoHS
