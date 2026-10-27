module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' G'' : Type} [Group G] [Group G'] [Group G'']
  {K : Subgroup G} {K' : Subgroup G'} {K'' : Subgroup G''}

theorem IsIsoOn.map_one {f : G → G'} (hf : IsIsoOn K K' f) : f 1 = 1 := by
  have h := hf.map_mul 1 K.one_mem 1 K.one_mem
  rw [mul_one] at h
  exact left_eq_mul.mp h

theorem IsIsoOn.map_inv {f : G → G'} (hf : IsIsoOn K K' f) {x : G} (hx : x ∈ K) :
    f x⁻¹ = (f x)⁻¹ := by
  have h := hf.map_mul x hx x⁻¹ (K.inv_mem hx)
  rw [mul_inv_cancel, hf.map_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem IsIsoOn.map_pow {f : G → G'} (hf : IsIsoOn K K' f) {x : G} (hx : x ∈ K) (n : ℕ) :
    f (x ^ n) = f x ^ n := by
  induction n with
  | zero => simpa using hf.map_one
  | succ n ih =>
    rw [pow_succ, hf.map_mul _ (K.pow_mem hx n) _ hx, ih, pow_succ]

theorem IsIsoOn.orderOf_eq {f : G → G'} (hf : IsIsoOn K K' f) {x : G} (hx : x ∈ K) :
    orderOf (f x) = orderOf x := by
  refine (orderOf_eq_orderOf_iff.mpr fun n => ?_)
  constructor
  · intro h
    refine hf.injOn _ (K.pow_mem hx n) 1 K.one_mem ?_
    rw [hf.map_pow hx, h, hf.map_one]
  · intro h
    rw [← hf.map_pow hx, h, hf.map_one]

theorem IsIsoOn.map_conj {f : G → G'} (hf : IsIsoOn K K' f) {g x : G} (hg : g ∈ K) (hx : x ∈ K) :
    f (g * x * g⁻¹) = f g * f x * (f g)⁻¹ := by
  rw [hf.map_mul _ (K.mul_mem hg hx) _ (K.inv_mem hg), hf.map_mul _ hg _ hx, hf.map_inv hg]

theorem IsIsoOn.natCard_eq {f : G → G'} (hf : IsIsoOn K K' f) : Nat.card K = Nat.card K' := by
  refine Nat.card_congr (Equiv.ofBijective (fun x : K => (⟨f x, hf.mem x x.2⟩ : K')) ⟨?_, ?_⟩)
  · intro x y hxy
    exact Subtype.ext (hf.injOn x x.2 y y.2 (congrArg Subtype.val hxy))
  · intro y
    obtain ⟨x, hx, hxy⟩ := hf.surjOn y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[expose] noncomputable def IsIsoOn.toMulEquiv {f : G → G'} (hf : IsIsoOn K K' f) : K ≃* K' :=
  MulEquiv.ofBijective
    (MonoidHom.mk' (fun x : K => (⟨f x, hf.mem x x.2⟩ : K'))
      (fun x y => Subtype.ext (hf.map_mul x x.2 y y.2)))
    ⟨fun x y hxy => Subtype.ext (hf.injOn x x.2 y y.2 (congrArg Subtype.val hxy)),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := hf.surjOn y y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem IsIsoOn.toMulEquiv_apply {f : G → G'} (hf : IsIsoOn K K' f) (x : K) :
    ((hf.toMulEquiv x : K') : G') = f x := rfl

theorem IsIsoOn.derived {f : G → G'} (hf : IsIsoOn K K' f) :
    IsIsoOn (derivedOf K) (derivedOf K') f := by
  obtain ⟨e, he⟩ : ∃ e : K ≃* K', ∀ x : K, ((e x : K') : G') = f x :=
    ⟨hf.toMulEquiv, fun x => rfl⟩
  have hcomm : (_root_.commutator ↥K).map e.toMonoidHom = _root_.commutator ↥K' := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  refine ⟨fun x hx y hy => hf.map_mul x (derivedOf_le K hx) y (derivedOf_le K hy), ?_,
    fun x hx y hy h => hf.injOn x (derivedOf_le K hx) y (derivedOf_le K hy) h, ?_⟩
  · intro x hx
    obtain ⟨hxK, hxc⟩ := mem_derivedOf_iff.mp hx
    refine mem_derivedOf_iff.mpr ⟨hf.mem x hxK, ?_⟩
    rw [← hcomm]
    refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hxc, ?_⟩
    exact Subtype.ext (he ⟨x, hxK⟩)
  · intro y hy
    obtain ⟨hyK, hyc⟩ := mem_derivedOf_iff.mp hy
    rw [← hcomm] at hyc
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hyc
    refine ⟨x, mem_derivedOf_iff.mpr ⟨x.2, hx⟩, ?_⟩
    rw [← he x]
    exact congrArg Subtype.val hxy

theorem IsIsoOn.comp {f : G → G'} {g : G' → G''} (hf : IsIsoOn K K' f) (hg : IsIsoOn K' K'' g) :
    IsIsoOn K K'' (g ∘ f) where
  map_mul x hx y hy := by
    simp only [Function.comp_apply]
    rw [hf.map_mul x hx y hy, hg.map_mul _ (hf.mem x hx) _ (hf.mem y hy)]
  mem x hx := hg.mem _ (hf.mem x hx)
  injOn x hx y hy h :=
    hf.injOn x hx y hy (hg.injOn _ (hf.mem x hx) _ (hf.mem y hy) h)
  surjOn y hy := by
    obtain ⟨u, hu, rfl⟩ := hg.surjOn y hy
    obtain ⟨x, hx, rfl⟩ := hf.surjOn u hu
    exact ⟨x, hx, rfl⟩

theorem IsIsoOn.congr {f g : G → G'} (hf : IsIsoOn K K' f) (h : ∀ x ∈ K, f x = g x) :
    IsIsoOn K K' g where
  map_mul x hx y hy := by
    rw [← h _ (K.mul_mem hx hy), ← h x hx, ← h y hy]
    exact hf.map_mul x hx y hy
  mem x hx := h x hx ▸ hf.mem x hx
  injOn x hx y hy hxy := hf.injOn x hx y hy (by rw [h x hx, h y hy]; exact hxy)
  surjOn y hy := by
    obtain ⟨x, hx, rfl⟩ := hf.surjOn y hy
    exact ⟨x, hx, (h x hx).symm⟩

theorem IsIsoOn.exists_inv {f : G → G'} (hf : IsIsoOn K K' f) :
    ∃ g : G' → G, IsIsoOn K' K g ∧ (∀ x ∈ K, g (f x) = x) ∧ ∀ y ∈ K', f (g y) = y := by
  classical
  let g : G' → G := fun y => if h : ∃ x ∈ K, f x = y then Classical.choose h else 1
  have hg : ∀ y ∈ K', g y ∈ K ∧ f (g y) = y := by
    intro y hy
    have h : ∃ x ∈ K, f x = y := hf.surjOn y hy
    simp only [g, dif_pos h]
    exact Classical.choose_spec h
  have hgf : ∀ x ∈ K, g (f x) = x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hg (f x) (hf.mem x hx)
    exact hf.injOn _ h1 x hx h2
  refine ⟨g, ⟨?_, fun y hy => (hg y hy).1, ?_, ?_⟩, hgf, fun y hy => (hg y hy).2⟩
  · intro y₁ hy₁ y₂ hy₂
    obtain ⟨h1, h1'⟩ := hg y₁ hy₁
    obtain ⟨h2, h2'⟩ := hg y₂ hy₂
    have hm : y₁ * y₂ ∈ K' := K'.mul_mem hy₁ hy₂
    obtain ⟨h3, h3'⟩ := hg _ hm
    refine hf.injOn _ h3 _ (K.mul_mem h1 h2) ?_
    rw [h3', hf.map_mul _ h1 _ h2, h1', h2']
  · intro y₁ hy₁ y₂ hy₂ h
    obtain ⟨h1, h1'⟩ := hg y₁ hy₁
    obtain ⟨h2, h2'⟩ := hg y₂ hy₂
    rw [← h1', ← h2', h]
  · intro x hx
    exact ⟨f x, hf.mem x hx, hgf x hx⟩

theorem IsIsoOn.restrict {f : G → G'} (hf : IsIsoOn K K' f) {L : Subgroup G} {L' : Subgroup G'}
    (hL : L ≤ K) (himg : ∀ y, y ∈ L' ↔ ∃ x ∈ L, f x = y) : IsIsoOn L L' f where
  map_mul x hx y hy := hf.map_mul x (hL hx) y (hL hy)
  mem x hx := (himg _).mpr ⟨x, hx, rfl⟩
  injOn x hx y hy h := hf.injOn x (hL hx) y (hL hy) h
  surjOn y hy := (himg y).mp hy

theorem IsIsoOn.restrict_cent {f : G → G'} (hf : IsIsoOn K K' f) {t : G} (ht : t ∈ K) :
    IsIsoOn (K ⊓ Gx t) (K' ⊓ Gx (f t)) f where
  map_mul x hx y hy :=
    hf.map_mul x (Subgroup.mem_inf.mp hx).1 y (Subgroup.mem_inf.mp hy).1
  mem x hx := by
    obtain ⟨hxK, hxt⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hf.mem x hxK, mem_Gx.mpr ?_⟩
    rw [← hf.map_mul _ ht _ hxK, ← hf.map_mul _ hxK _ ht, mem_Gx.mp hxt]
  injOn x hx y hy h :=
    hf.injOn x (Subgroup.mem_inf.mp hx).1 y (Subgroup.mem_inf.mp hy).1 h
  surjOn y hy := by
    obtain ⟨hyK, hyt⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨x, hx, rfl⟩ := hf.surjOn y hyK
    refine ⟨x, Subgroup.mem_inf.mpr ⟨hx, mem_Gx.mpr ?_⟩, rfl⟩
    refine hf.injOn _ (K.mul_mem ht hx) _ (K.mul_mem hx ht) ?_
    rw [hf.map_mul _ ht _ hx, hf.map_mul _ hx _ ht]
    exact mem_Gx.mp hyt

theorem isIsoOn_conj {g : G} (hg : g ∈ K) : IsIsoOn K K (fun x => g * x * g⁻¹) where
  map_mul x _ y _ := by group
  mem x hx := K.mul_mem (K.mul_mem hg hx) (K.inv_mem hg)
  injOn x _ y _ h := by simpa using h
  surjOn y hy := ⟨g⁻¹ * y * g, K.mul_mem (K.mul_mem (K.inv_mem hg) hy) hg, by group⟩

theorem exists_isIsoOn_of_mulEquiv (e : K ≃* K') :
    ∃ f : G → G', IsIsoOn K K' f ∧ ∀ x : K, f x = e x := by
  classical
  let f : G → G' := fun x => if h : x ∈ K then (e ⟨x, h⟩ : G') else 1
  have hf : ∀ x : K, f x = e x := fun x => by simp [f, x.2]
  refine ⟨f, ⟨?_, ?_, ?_, ?_⟩, hf⟩
  · intro x hx y hy
    have := hf ⟨x * y, K.mul_mem hx hy⟩
    have h2 := hf ⟨x, hx⟩
    have h3 := hf ⟨y, hy⟩
    simp only at this h2 h3
    rw [this, h2, h3]
    exact congrArg Subtype.val (map_mul e ⟨x, hx⟩ ⟨y, hy⟩)
  · intro x hx
    have := hf ⟨x, hx⟩
    simp only at this
    rw [this]
    exact (e ⟨x, hx⟩).2
  · intro x hx y hy h
    have h2 := hf ⟨x, hx⟩
    have h3 := hf ⟨y, hy⟩
    simp only at h2 h3
    rw [h2, h3] at h
    have := e.injective (Subtype.ext h)
    exact congrArg Subtype.val this
  · intro y hy
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
    refine ⟨x, x.2, ?_⟩
    have := hf x
    rw [this, hx]

theorem iso_dichotomy_of_aut {S : Set G} {t : G} (hSK : ∀ x ∈ S, x ∈ K)
    (haut : ∀ η : G → G, IsIsoOn K K η → (∀ x ∈ S, η x = x) →
      (∀ x ∈ K, η x = x) ∨ ∀ x ∈ K, η x = t * x * t⁻¹)
    {φ₁ φ₂ : G → G'} (h₁ : IsIsoOn K K' φ₁) (h₂ : IsIsoOn K K' φ₂)
    (hS : ∀ x ∈ S, φ₁ x = φ₂ x) :
    (∀ x ∈ K, φ₁ x = φ₂ x) ∨ ∀ x ∈ K, φ₁ x = φ₂ (t * x * t⁻¹) := by
  obtain ⟨g₂, hg₂, hg₂f, hfg₂⟩ := h₂.exists_inv
  have hη : IsIsoOn K K (g₂ ∘ φ₁) := h₁.comp hg₂
  have hfix : ∀ x ∈ S, (g₂ ∘ φ₁) x = x := by
    intro x hx
    simp only [Function.comp_apply]
    rw [hS x hx, hg₂f x (hSK x hx)]
  rcases haut _ hη hfix with h | h
  · left
    intro x hx
    have := h x hx
    simp only [Function.comp_apply] at this
    rw [← hfg₂ (φ₁ x) (h₁.mem x hx), this]
  · right
    intro x hx
    have := h x hx
    simp only [Function.comp_apply] at this
    rw [← hfg₂ (φ₁ x) (h₁.mem x hx), this]

end CFSG.EvenSporadicStandard.HNRecog.Section4
