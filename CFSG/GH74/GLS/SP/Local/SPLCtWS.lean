module

public import CFSG.GH74.GLS.SP.Local.SPLCtW
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.GH74.GLS.IVK

section WS

variable {G : Type} [Group G]

theorem zpowers_mk_eq_subgroupOf (T : Subgroup G) {y : G} (hy : y ∈ T) :
    zpowers (⟨y, hy⟩ : ↥T) = (zpowers y).subgroupOf T := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem isDihedralOrder_subgroupOf {T A : Subgroup G} (hA : A ≤ T) {m : ℕ}
    (h : IsDihedralOrder ↥A m) : IsDihedralOrder ↥(A.subgroupOf T) m :=
  CtW.isDihedralOrder_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hA).symm h

theorem isDihedralOrder_map_subtype {T : Subgroup G} {A : Subgroup ↥T} {m : ℕ}
    (h : IsDihedralOrder ↥A m) : IsDihedralOrder ↥(A.map T.subtype) m :=
  CtW.isDihedralOrder_of_mulEquiv (Subgroup.equivMapOfInjective A T.subtype T.subtype_injective) h

theorem map_subtype_zpowers (T : Subgroup G) (y : ↥T) :
    (zpowers y).map T.subtype = zpowers (y : G) := by
  rw [MonoidHom.map_zpowers]; rfl

end WS

theorem lemmaW_sub {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 3 ≤ n)
    (T B₁ B₂ T₁ : Subgroup G) (y z t : G)
    (hB₁T : B₁ ≤ T) (hB₂T : B₂ ≤ T) (hyT : y ∈ T) (hT₁T : T₁ ≤ T) (hzT : z ∈ T) (htT : t ∈ T)
    (hcomm : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) (hinf : B₁ ⊓ B₂ = ⊥)
    (hy2 : y * y = 1)
    (hy₁ : ∀ a ∈ B₁, y * a * y⁻¹ ∈ B₁) (hy₂ : ∀ a ∈ B₂, y * a * y⁻¹ ∈ B₂)
    (hT : T = B₁ ⊔ B₂ ⊔ zpowers y)
    (hB₁ : IsDihedralOrder ↥B₁ (2 ^ (n - 1))) (hB₂ : IsDihedralOrder ↥B₂ (2 ^ (n - 1)))
    (hB₁y : IsDihedralOrder ↥(B₁ ⊔ zpowers y) (2 ^ n))
    (hB₂y : IsDihedralOrder ↥(B₂ ⊔ zpowers y) (2 ^ n))
    (hT₁n : ∀ c ∈ T, ∀ a ∈ T₁, c * a * c⁻¹ ∈ T₁) (hT₁ : IsDihedralOrder ↥T₁ (2 ^ (n - 1)))
    (hz : orderOf z = 2) (ht : orderOf t = 2) (htc : ∀ c ∈ T, c * t = t * c) (hzt : z ≠ t)
    (hzT₁ : ∀ a ∈ T₁, z * a = a * z)
    (hinfU : (zpowers z ⊔ zpowers t) ⊓ T₁ = ⊥)
    (hC : centralizer ({z} : Set G) ⊓ T = (zpowers z ⊔ zpowers t) ⊔ T₁) :
    ∃ (X : Subgroup G) (y₀ : G), X ≤ T ∧ (∀ c ∈ T, ∀ a ∈ X, c * a * c⁻¹ ∈ X) ∧ z ∈ X ∧
      (∀ N : Subgroup G, N ≤ T → (∀ c ∈ T, ∀ a ∈ N, c * a * c⁻¹ ∈ N) → z ∈ N → X ≤ N) ∧
      IsDihedralOrder ↥X (2 ^ (n - 1)) ∧
      (∀ a ∈ X, ∀ b ∈ T₁, a * b = b * a) ∧ X ⊓ T₁ = ⊥ ∧
      (∀ c ∈ T, (∀ a ∈ T₁, c * a = a * c) →
        ∃ x ∈ X, ∃ ζ ∈ T₁, (∀ a ∈ T₁, ζ * a = a * ζ) ∧ c = x * ζ) ∧
      y₀ ∈ T ∧ y₀ * y₀ = 1 ∧ T = X ⊔ T₁ ⊔ zpowers y₀ ∧
      IsDihedralOrder ↥(X ⊔ zpowers y₀) (2 ^ n) ∧ IsDihedralOrder ↥(T₁ ⊔ zpowers y₀) (2 ^ n) := by
  have hzy : zpowers y ≤ T := zpowers_le.mpr hyT
  have hzz : zpowers z ≤ T := zpowers_le.mpr hzT
  have hzt' : zpowers t ≤ T := zpowers_le.mpr htT
  set y' : ↥T := ⟨y, hyT⟩ with hy'
  set z' : ↥T := ⟨z, hzT⟩ with hz'
  set t' : ↥T := ⟨t, htT⟩ with ht'
  have hsubsup : ∀ A A' : Subgroup G, A ≤ T → A' ≤ T →
      (A ⊔ A').subgroupOf T = A.subgroupOf T ⊔ A'.subgroupOf T := fun A A' h h' =>
    Subgroup.subgroupOf_sup h h'
  have hB₁'y : B₁.subgroupOf T ⊔ zpowers y' = (B₁ ⊔ zpowers y).subgroupOf T := by
    rw [hy', zpowers_mk_eq_subgroupOf T hyT, ← hsubsup _ _ hB₁T hzy]
  have hB₂'y : B₂.subgroupOf T ⊔ zpowers y' = (B₂ ⊔ zpowers y).subgroupOf T := by
    rw [hy', zpowers_mk_eq_subgroupOf T hyT, ← hsubsup _ _ hB₂T hzy]
  have hT' : B₁.subgroupOf T ⊔ B₂.subgroupOf T ⊔ zpowers y' = ⊤ := by
    rw [hy', zpowers_mk_eq_subgroupOf T hyT, ← hsubsup _ _ hB₁T hB₂T,
      ← hsubsup _ _ (sup_le hB₁T hB₂T) hzy, ← hT, Subgroup.subgroupOf_self]
  have hinf' : B₁.subgroupOf T ⊓ B₂.subgroupOf T = ⊥ := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · rintro ⟨h1, h2⟩
      have : (x : G) ∈ B₁ ⊓ B₂ := ⟨h1, h2⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · rintro rfl
      exact ⟨B₁.one_mem, B₂.one_mem⟩
  have hU' : zpowers z' ⊔ zpowers t' = (zpowers z ⊔ zpowers t).subgroupOf T := by
    rw [hz', ht', zpowers_mk_eq_subgroupOf T hzT, zpowers_mk_eq_subgroupOf T htT,
      ← hsubsup _ _ hzz hzt']
  have hinfU' : (zpowers z' ⊔ zpowers t') ⊓ T₁.subgroupOf T = ⊥ := by
    rw [hU']
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · rintro ⟨h1, h2⟩
      have : (x : G) ∈ (zpowers z ⊔ zpowers t) ⊓ T₁ := ⟨h1, h2⟩
      rw [hinfU, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · rintro rfl
      exact ⟨(zpowers z ⊔ zpowers t).one_mem, T₁.one_mem⟩
  have hC' : centralizer ({z'} : Set ↥T) = (zpowers z' ⊔ zpowers t') ⊔ T₁.subgroupOf T := by
    have h1 : centralizer ({z'} : Set ↥T) = (centralizer ({z} : Set G) ⊓ T).subgroupOf T := by
      ext x
      rw [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        mem_centralizer_singleton_iff]
      constructor
      · intro h; exact ⟨congrArg Subtype.val h, x.2⟩
      · intro h; exact Subtype.ext h.1
    rw [h1, hC, hU', hsubsup _ _ (sup_le hzz hzt') hT₁T]
  have hz'ord : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact hz
  have ht'ord : orderOf t' = 2 := by rw [ht', Subgroup.orderOf_mk]; exact ht
  have htc' : t' ∈ center ↥T := Subgroup.mem_center_iff.mpr fun g => Subtype.ext (htc g g.2)
  have hzt'' : z' ≠ t' := fun h => hzt (congrArg Subtype.val h)
  have hzT₁' : ∀ a ∈ T₁.subgroupOf T, z' * a = a * z' := fun a ha => Subtype.ext (hzT₁ a ha)
  have hT₁n' : (T₁.subgroupOf T).Normal := ⟨fun n hn g => hT₁n g g.2 n hn⟩
  obtain ⟨X', y₀', hXn, hzX, hXmin, hXdih, hXcomm, hXinf, hXC, hy₀2, hXT', hXy, hT₁y⟩ :=
    lemmaW (T := ↥T) hn (B₁.subgroupOf T) (B₂.subgroupOf T) y'
      (fun a ha b hb => Subtype.ext (hcomm a ha b hb)) hinf' (Subtype.ext hy2)
      (fun a ha => hy₁ a ha) (fun a ha => hy₂ a ha) hT'
      (isDihedralOrder_subgroupOf hB₁T hB₁) (isDihedralOrder_subgroupOf hB₂T hB₂)
      (by rw [hB₁'y]; exact isDihedralOrder_subgroupOf (sup_le hB₁T hzy) hB₁y)
      (by rw [hB₂'y]; exact isDihedralOrder_subgroupOf (sup_le hB₂T hzy) hB₂y)
      (T₁.subgroupOf T) hT₁n' (isDihedralOrder_subgroupOf hT₁T hT₁)
      z' t' hz'ord ht'ord htc' hzt'' hzT₁' hinfU' hC'
  set X : Subgroup G := X'.map T.subtype with hX
  have hXT : X ≤ T := Subgroup.map_subtype_le _
  have h2 : ∀ c ∈ T, ∀ a ∈ X, c * a * c⁻¹ ∈ X := by
    rintro c hc _ ⟨a', ha', rfl⟩
    exact ⟨⟨c, hc⟩ * a' * ⟨c, hc⟩⁻¹, hXn.conj_mem a' ha' ⟨c, hc⟩, rfl⟩
  have h3 : z ∈ X := ⟨z', hzX, rfl⟩
  have h4 : ∀ N : Subgroup G, N ≤ T → (∀ c ∈ T, ∀ a ∈ N, c * a * c⁻¹ ∈ N) → z ∈ N → X ≤ N := by
    intro N hNT hNn hzN
    have hN'n : (N.subgroupOf T).Normal := ⟨fun n hn g => hNn g g.2 n hn⟩
    have := hXmin (N.subgroupOf T) hN'n hzN
    rintro _ ⟨x', hx', rfl⟩
    exact this hx'
  have h6 : ∀ a ∈ X, ∀ b ∈ T₁, a * b = b * a := by
    rintro _ ⟨a', ha', rfl⟩ b hb
    have := hXcomm a' ha' ⟨b, hT₁T hb⟩ hb
    exact congrArg Subtype.val this
  have h7 : X ⊓ T₁ = ⊥ := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_bot]
    constructor
    · rintro ⟨⟨x', hx', rfl⟩, hxT₁⟩
      have : x' ∈ X' ⊓ T₁.subgroupOf T := ⟨hx', hxT₁⟩
      rw [hXinf, Subgroup.mem_bot] at this
      rw [this]; rfl
    · rintro rfl
      exact ⟨X.one_mem, T₁.one_mem⟩
  have h8 : ∀ c ∈ T, (∀ a ∈ T₁, c * a = a * c) →
      ∃ x ∈ X, ∃ ζ ∈ T₁, (∀ a ∈ T₁, ζ * a = a * ζ) ∧ c = x * ζ := by
    intro c hc hcT₁
    obtain ⟨x', hx', ζ', hζ', hζc, hcx⟩ := hXC ⟨c, hc⟩ (fun a ha => Subtype.ext (hcT₁ a ha))
    refine ⟨x', ⟨x', hx', rfl⟩, ζ', hζ', fun a ha => ?_, congrArg Subtype.val hcx⟩
    exact congrArg Subtype.val (hζc ⟨a, hT₁T ha⟩ ha)
  have h10 : (y₀' : G) * (y₀' : G) = 1 := congrArg Subtype.val hy₀2
  have hmapT : (X' ⊔ T₁.subgroupOf T ⊔ zpowers y₀').map T.subtype =
      X ⊔ T₁ ⊔ zpowers (y₀' : G) := by
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hT₁T,
      map_subtype_zpowers]
  have h11 : T = X ⊔ T₁ ⊔ zpowers (y₀' : G) := by
    rw [← hmapT, hXT', Subgroup.map_top, Subgroup.range_subtype]
  have h12 : IsDihedralOrder ↥(X ⊔ zpowers (y₀' : G)) (2 ^ n) := by
    have := isDihedralOrder_map_subtype hXy
    rwa [Subgroup.map_sup, map_subtype_zpowers] at this
  have h13 : IsDihedralOrder ↥(T₁ ⊔ zpowers (y₀' : G)) (2 ^ n) := by
    have := isDihedralOrder_map_subtype hT₁y
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hT₁T, map_subtype_zpowers] at this
  exact ⟨X, (y₀' : G), hXT, h2, h3, h4, isDihedralOrder_map_subtype hXdih, h6, h7, h8, y₀'.2, h10,
    h11, h12, h13⟩

end CFSG.GH74.GLS.SP.Local
