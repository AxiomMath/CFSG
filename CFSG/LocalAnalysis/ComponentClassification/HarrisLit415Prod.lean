module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndSetting
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

namespace L415

variable {G : Type*} [Group G]

structure IsProd (E K₁ K₂ : Subgroup G) (s : G) : Prop where
  sup_eq : K₁ ⊔ K₂ = E
  inf_eq : K₁ ⊓ K₂ = ⊥
  le_centralizer : K₁ ≤ centralizer (K₂ : Set G)
  map_conj : K₁.map (MulAut.conj s⁻¹).toMonoidHom = K₂
  simple : IsSimpleGroup ↥K₁
  nonabelian : ∃ a b : ↥K₁, a * b ≠ b * a

theorem eq_one_of_mem_center {K : Subgroup G} (hs : IsSimpleGroup ↥K)
    (hn : ∃ a b : ↥K, a * b ≠ b * a) {a : G} (ha : a ∈ K) (hc : ∀ k ∈ K, a * k = k * a) :
    a = 1 := by
  have hcen : (⟨a, ha⟩ : ↥K) ∈ center ↥K :=
    mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥K) with hb | ht
  · rw [hb, mem_bot] at hcen
    exact congrArg Subtype.val hcen
  · exfalso
    obtain ⟨x, y, hxy⟩ := hn
    have hx : x ∈ center ↥K := ht ▸ mem_top x
    exact hxy ((mem_center_iff.mp hx) y).symm

namespace IsProd

variable {E K₁ K₂ : Subgroup G} {s : G} (h : IsProd E K₁ K₂ s)
include h

theorem mem_K₂_iff {x : G} : x ∈ K₂ ↔ s * x * s⁻¹ ∈ K₁ := by
  rw [← h.map_conj]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk
  · intro hx
    exact ⟨s * x * s⁻¹, hx, by simp [mul_assoc]⟩

theorem conj_mem_K₂ {k : G} (hk : k ∈ K₁) : s⁻¹ * k * s ∈ K₂ :=
  h.mem_K₂_iff.mpr (by simpa [mul_assoc] using hk)

theorem comm {a b : G} (ha : a ∈ K₁) (hb : b ∈ K₂) : a * b = b * a :=
  ((mem_centralizer_iff.mp (h.le_centralizer ha)) b hb).symm

theorem K₁_le : K₁ ≤ E := h.sup_eq ▸ le_sup_left

theorem K₂_le : K₂ ≤ E := h.sup_eq ▸ le_sup_right

@[expose] def equivK₂ : ↥K₁ ≃* ↥K₂ :=
  (K₁.equivMapOfInjective _ (MulAut.conj s⁻¹).injective).trans
    (MulEquiv.subgroupCongr h.map_conj)

theorem simple₂ : IsSimpleGroup ↥K₂ := by
  have := h.simple
  exact h.equivK₂.symm.isSimpleGroup

theorem nonabelian₂ : ∃ a b : ↥K₂, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h.nonabelian
  refine ⟨h.equivK₂ a, h.equivK₂ b, fun hc => hab (h.equivK₂.injective ?_)⟩
  rw [map_mul, map_mul, hc]

theorem exists_mul [Finite G] {x : G} (hx : x ∈ E) : ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b := by
  obtain ⟨-, hset⟩ := GroupTheory.card_sup_mul_card_inf_of_commute K₁ K₂ fun a ha b hb =>
    h.comm ha hb
  have hx' : x ∈ ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by rw [h.sup_eq]; exact hx
  rw [hset] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem eq_of_mul_eq {a a' b b' : G} (ha : a ∈ K₁) (ha' : a' ∈ K₁) (hb : b ∈ K₂)
    (hb' : b' ∈ K₂) (he : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [he]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ K₁ ⊓ K₂ :=
    mem_inf.mpr ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
  rw [h.inf_eq, mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  subst h3
  exact mul_left_cancel he

theorem conj_mem_K₁_of_mem [Finite G] {x k : G} (hx : x ∈ E) (hk : k ∈ K₁) :
    x * k * x⁻¹ ∈ K₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hx
  have : a * b * k * (a * b)⁻¹ = a * k * a⁻¹ := by
    calc a * b * k * (a * b)⁻¹ = a * (b * k) * b⁻¹ * a⁻¹ := by group
      _ = a * (k * b) * b⁻¹ * a⁻¹ := by rw [h.comm hk hb]
      _ = a * k * a⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem ha hk) (inv_mem ha)

theorem conj_mem_K₂_of_mem [Finite G] {x k : G} (hx : x ∈ E) (hk : k ∈ K₂) :
    x * k * x⁻¹ ∈ K₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hx
  have : a * b * k * (a * b)⁻¹ = b * k * b⁻¹ := by
    calc a * b * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ := by group
      _ = (b * k * b⁻¹) * a * a⁻¹ := by
          rw [h.comm ha (mul_mem (mul_mem hb hk) (inv_mem hb))]
      _ = b * k * b⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hb hk) (inv_mem hb)

theorem eq_one_of_mem_centralizer [Finite G] {x : G} (hx : x ∈ E)
    (hc : x ∈ centralizer (E : Set G)) : x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hx
  have hcomm : ∀ y ∈ E, a * b * y = y * (a * b) := fun y hy =>
    ((mem_centralizer_iff.mp hc) y hy).symm
  have ha1 : a = 1 := by
    refine eq_one_of_mem_center h.simple h.nonabelian ha fun k hk => ?_
    have h1 := hcomm k (h.K₁_le hk)
    have h2 : b * k = k * b := (h.comm hk hb).symm
    calc a * k = a * b * k * b⁻¹ := by rw [mul_assoc a b k, h2]; group
      _ = k * (a * b) * b⁻¹ := by rw [h1]
      _ = k * a := by group
  subst ha1
  have hb1 : b = 1 := by
    refine eq_one_of_mem_center h.simple₂ h.nonabelian₂ hb fun k hk => ?_
    simpa using hcomm k (h.K₂_le hk)
  rw [hb1, mul_one]

theorem K₁_ne_K₂ : K₁ ≠ K₂ := by
  intro he
  obtain ⟨a, b, hab⟩ := h.nonabelian
  apply hab
  apply Subtype.ext
  exact h.comm a.2 (he ▸ b.2)

theorem isComponent₁ (hE : E.Normal) [Finite G] : IsComponent K₁ := by
  have := h.simple
  refine ⟨HarrisEnd.isQuasisimple_of_isSimpleGroup h.nonabelian, ?_⟩
  have hn : (K₁.subgroupOf E).Normal :=
    ⟨fun a ha g => h.conj_mem_K₁_of_mem g.2 ha⟩
  exact IsSubnormal.trans h.K₁_le hn.isSubnormal hE.isSubnormal

theorem isComponent₂ (hE : E.Normal) [Finite G] : IsComponent K₂ := by
  have := h.simple₂
  refine ⟨HarrisEnd.isQuasisimple_of_isSimpleGroup h.nonabelian₂, ?_⟩
  have hn : (K₂.subgroupOf E).Normal :=
    ⟨fun a ha g => h.conj_mem_K₂_of_mem g.2 ha⟩
  exact IsSubnormal.trans h.K₂_le hn.isSubnormal hE.isSubnormal

theorem eq_bot_of_commute [Finite G] {N : Subgroup G} (hNE : N ≤ E)
    (h₁ : ⁅N, K₁⁆ = ⊥) (h₂ : ⁅N, K₂⁆ = ⊥) : N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  refine h.eq_one_of_mem_centralizer (hNE hx) ?_
  have hle : E ≤ centralizer (N : Set G) := by
    rw [← h.sup_eq]
    refine sup_le ?_ ?_
    · rw [commutator_comm] at h₁
      exact commutator_eq_bot_iff_le_centralizer.mp h₁
    · rw [commutator_comm] at h₂
      exact commutator_eq_bot_iff_le_centralizer.mp h₂
  rw [mem_centralizer_iff]
  intro y hy
  exact ((mem_centralizer_iff.mp (hle hy)) x hx).symm

theorem conj_cases (hE : E.Normal) [Finite G] (g : G) :
    K₁.map (MulAut.conj g).toMonoidHom = K₁ ∨ K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
  have hc := LocalCores.isComponent_map_mulEquiv (MulAut.conj g) (h.isComponent₁ hE)
  have hNE : K₁.map (MulAut.conj g).toMonoidHom ≤ E := by
    rintro _ ⟨k, hk, rfl⟩
    exact hE.conj_mem k (h.K₁_le hk) g
  rcases LocalCores.distinct_components_commute hc (h.isComponent₁ hE) with h1 | h1
  · exact Or.inl h1
  rcases LocalCores.distinct_components_commute hc (h.isComponent₂ hE) with h2 | h2
  · exact Or.inr h2
  exfalso
  have hb := h.eq_bot_of_commute hNE h1 h2
  have hb' : K₁ = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have : (MulAut.conj g) k ∈ (⊥ : Subgroup G) := hb ▸ ⟨k, hk, rfl⟩
    rw [mem_bot] at this
    exact (map_eq_one_iff _ (MulAut.conj g).injective).mp this
  obtain ⟨a, b, hab⟩ := h.nonabelian
  apply hab
  have ha : (a : G) ∈ (⊥ : Subgroup G) := by rw [← hb']; exact a.2
  have hb1 : (b : G) ∈ (⊥ : Subgroup G) := by rw [← hb']; exact b.2
  rw [mem_bot] at ha hb1
  exact Subtype.ext (by simp [ha, hb1])

@[expose] def diag : ↥K₁ →* G where
  toFun k := (k : G) * (s⁻¹ * k * s)
  map_one' := by simp
  map_mul' a b := by
    have hc := h.comm b.2 (h.conj_mem_K₂ a.2)
    simp only [Subgroup.coe_mul]
    calc (a : G) * b * (s⁻¹ * (a * b) * s) = a * (b * (s⁻¹ * a * s)) * (s⁻¹ * b * s) := by
          group
      _ = a * ((s⁻¹ * a * s) * b) * (s⁻¹ * b * s) := by rw [hc]
      _ = a * (s⁻¹ * a * s) * (b * (s⁻¹ * b * s)) := by group

theorem diag_apply (k : ↥K₁) : h.diag k = (k : G) * (s⁻¹ * k * s) := rfl

theorem diag_injective : Function.Injective h.diag := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker, diag_apply] at hk
  have h1 : (k : G) = (s⁻¹ * k * s)⁻¹ := eq_inv_of_mul_eq_one_left hk
  have h2 : (k : G) ∈ K₁ ⊓ K₂ := mem_inf.mpr ⟨k.2, h1 ▸ inv_mem (h.conj_mem_K₂ k.2)⟩
  rw [h.inf_eq, mem_bot] at h2
  exact Subtype.ext h2

theorem mem_centralizer_iff [Finite G] (hs : s * s = 1) {x : G} (hx : x ∈ E) :
    s * x = x * s ↔ ∃ k : ↥K₁, h.diag k = x := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  constructor
  · intro hsx
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hx
    have hb1 : s * b * s⁻¹ ∈ K₁ := h.mem_K₂_iff.mp hb
    have ha2 : s * a * s⁻¹ ∈ K₂ := by
      have := h.conj_mem_K₂ ha
      rw [hsi] at this ⊢
      exact this
    have he : (s * b * s⁻¹) * (s * a * s⁻¹) = a * b := by
      calc (s * b * s⁻¹) * (s * a * s⁻¹) = (s * a * s⁻¹) * (s * b * s⁻¹) := h.comm hb1 ha2
        _ = s * (a * b) * s⁻¹ := by group
        _ = a * b := by rw [hsx]; group
    obtain ⟨-, h2⟩ := h.eq_of_mul_eq hb1 ha ha2 hb he
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [diag_apply]
    show a * (s⁻¹ * a * s) = a * b
    rw [show s⁻¹ * a * s = s * a * s⁻¹ by rw [hsi], h2]
  · rintro ⟨k, rfl⟩
    rw [diag_apply]
    have hc := h.comm k.2 (h.conj_mem_K₂ k.2)
    rw [hsi] at hc ⊢
    calc s * ((k : G) * (s * k * s)) = s * k * s * k * s := by group
      _ = (k : G) * (s * k * s) * s := by rw [← hc]

theorem card_centralizer [Finite G] (hs : s * s = 1) :
    Nat.card ↥(E ⊓ centralizer {s}) = Nat.card ↥K₁ := by
  have hmem : ∀ k : ↥K₁, h.diag k ∈ E ⊓ centralizer {s} := fun k => by
    have hk : h.diag k ∈ E := mul_mem (h.K₁_le k.2) (h.K₂_le (h.conj_mem_K₂ k.2))
    exact mem_inf.mpr ⟨hk, mem_centralizer_singleton_iff.mpr
      ((h.mem_centralizer_iff hs hk).mpr ⟨k, rfl⟩).symm⟩
  refine (Nat.card_eq_of_bijective (fun k => ⟨h.diag k, hmem k⟩) ⟨fun a b hab => ?_,
    fun x => ?_⟩).symm
  · exact h.diag_injective (congrArg Subtype.val hab)
  · obtain ⟨k, hk⟩ := (h.mem_centralizer_iff hs (mem_inf.mp x.2).1).mp
      (mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2).symm
    exact ⟨k, Subtype.ext hk⟩

end IsProd

end L415

end CFSG.ComponentClassification.HarrisLit
