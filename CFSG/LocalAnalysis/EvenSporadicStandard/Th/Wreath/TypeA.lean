module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.NormalizerD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.OmegaOneInvariant
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

structure IsLayer (L A Y₁ Y₂ : Subgroup G) (ψ : G → G) : Prop where
  le : Y₁ ≤ Y₂
  conj_mem : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Y₂, n * y * n⁻¹ ∈ Y₂
  mem : ∀ y ∈ Y₂, ψ y ∈ A
  map_mul : ∀ y ∈ Y₂, ∀ y' ∈ Y₂, ψ (y * y') = ψ y * ψ y'
  eq_one_iff : ∀ y ∈ Y₂, ψ y = 1 ↔ y ∈ Y₁
  surj : ∀ a ∈ A, ∃ y ∈ Y₂, ψ y = a
  conj : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Y₂, ψ (n * y * n⁻¹) = n * ψ y * n⁻¹

inductive IsTypeA (L A : Subgroup G) : Subgroup G → Subgroup G → Prop
  | refl (Y : Subgroup G) (hY : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Y,
      n * y * n⁻¹ ∈ Y) : IsTypeA L A Y Y
  | step {Y₀ Y₁ Y₂ : Subgroup G} (ψ : G → G) (h : IsTypeA L A Y₀ Y₁)
      (hψ : IsLayer L A Y₁ Y₂ ψ) : IsTypeA L A Y₀ Y₂

section Layer

variable {Y₁ Y₂ : Subgroup G} {ψ : G → G}

theorem IsLayer.map_one (h : IsLayer L A Y₁ Y₂ ψ) : ψ 1 = 1 := by
  have h1 : ψ (1 * 1) = ψ 1 * ψ 1 := h.map_mul 1 (h.le Y₁.one_mem) 1 (h.le Y₁.one_mem)
  rw [mul_one] at h1
  have h2 : ψ 1 * 1 = ψ 1 * ψ 1 := by
    rw [mul_one]
    exact h1
  exact (mul_left_cancel h2).symm

theorem IsLayer.map_inv (h : IsLayer L A Y₁ Y₂ ψ) {y : G} (hy : y ∈ Y₂) :
    ψ y⁻¹ = (ψ y)⁻¹ := by
  have h1 : ψ (y * y⁻¹) = ψ y * ψ y⁻¹ := h.map_mul y hy y⁻¹ (Y₂.inv_mem hy)
  rw [mul_inv_cancel, h.map_one] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem IsLayer.inf_mem_of_map_eq (h : IsLayer L A Y₁ Y₂ ψ) {x x' : G} (hx : x ∈ Y₂)
    (hx' : x' ∈ Y₂) (heq : ψ x = ψ x') : x * x'⁻¹ ∈ Y₁ := by
  refine (h.eq_one_iff (x * x'⁻¹) (Y₂.mul_mem hx (Y₂.inv_mem hx'))).1 ?_
  rw [h.map_mul x hx x'⁻¹ (Y₂.inv_mem hx'), h.map_inv hx', heq, mul_inv_cancel]

end Layer

theorem ThLocalIn.mem_inf_normalizer_of_forall_conj_mem (W : ThLocalIn L S A B z) {n : G}
    (hnL : n ∈ L) (hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A) : n ∈ L ⊓ normalizer (A : Set G) := by
  have hmapeq : A.map (MulAut.conj n).toMonoidHom = A := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro a ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using hnA x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have hmapInv : ∀ y ∈ A, n⁻¹ * y * n ∈ A := by
    intro y hy
    have hy' : y ∈ A.map (MulAut.conj n).toMonoidHom := by rw [hmapeq]; exact hy
    obtain ⟨y₀, hy₀, hy₀eq⟩ := Subgroup.mem_map.1 hy'
    have : y₀ = n⁻¹ * y * n := by
      rw [← hy₀eq]
      change y₀ = n⁻¹ * ((MulAut.conj n) y₀) * n
      rw [MulAut.conj_apply]
      group
    rw [← this]
    exact hy₀
  refine Subgroup.mem_inf.2 ⟨hnL, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hnA x
  · intro hx
    have : x = n⁻¹ * (n * x * n⁻¹) * n := by group
    rw [this]
    exact hmapInv _ hx

theorem IsTypeA.le {Y₀ Y : Subgroup G} (h : IsTypeA L A Y₀ Y) : Y₀ ≤ Y := by
  induction h with
  | refl hY => exact le_rfl
  | step ψ h hψ ih => exact ih.trans hψ.le

theorem IsTypeA.conj_mem {Y₀ Y : Subgroup G} (h : IsTypeA L A Y₀ Y) :
    ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
  induction h with
  | refl hY => exact hY
  | step ψ h hψ ih => exact hψ.conj_mem

theorem IsLayer.card_eq (W : ThLocalIn L S A B z) {Y₁ Y₂ : Subgroup G} {ψ : G → G}
    (h : IsLayer L A Y₁ Y₂ ψ) :
    Nat.card Y₂ = 16 * Nat.card Y₁ := by
  classical
  let φ : ↥Y₂ →* ↥A :=
    { toFun := fun y => ⟨ψ y, h.mem y y.2⟩
      map_one' := Subtype.ext h.map_one
      map_mul' := fun y y' => Subtype.ext (h.map_mul y y.2 y' y'.2) }
  have hker : φ.ker = Y₁.subgroupOf Y₂ := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun hy => (h.eq_one_iff y y.2).1 (congrArg Subtype.val hy),
      fun hy => Subtype.ext ((h.eq_one_iff y y.2).2 hy)⟩
  have hrange : φ.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro a
    obtain ⟨y, hy, hψy⟩ := h.surj a a.2
    exact ⟨⟨y, hy⟩, Subtype.ext hψy⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hq : Nat.card (↥Y₂ ⧸ φ.ker) = Nat.card ↥A := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange,
      Subgroup.card_top]
  have hk : Nat.card ↥φ.ker = Nat.card Y₁ := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv]
  rw [hq, hk, W.A_card] at h1
  exact h1

theorem IsTypeA.exists_card_eq (W : ThLocalIn L S A B z)
    {Y₀ Y : Subgroup G} (h : IsTypeA L A Y₀ Y) :
    ∃ r : ℕ, Nat.card Y = 16 ^ r * Nat.card Y₀ := by
  induction h with
  | refl hY => exact ⟨0, by simp⟩
  | step ψ h hψ ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r + 1, ?_⟩
      rw [hψ.card_eq W, hr, pow_succ]
      ring

theorem IsTypeA.exists_isLayer_of_card_eq (W : ThLocalIn L S A B z)
    {Y₀ Y : Subgroup G} (h : IsTypeA L A Y₀ Y) (hc : Nat.card Y = 16 * Nat.card Y₀) :
    ∃ ψ : G → G, IsLayer L A Y₀ Y ψ := by
  refine IsTypeA.rec (motive := fun Y _ => Nat.card Y = 16 * Nat.card Y₀ →
    ∃ ψ : G → G, IsLayer L A Y₀ Y ψ) ?_ ?_ h hc
  · intro hY hc
    exfalso
    have hpos : 0 < Nat.card Y₀ := Nat.card_pos
    omega
  · intro Y₁ Y₂ ψ h hψ ih hc
    have hcard := hψ.card_eq W
    have hc1 : Nat.card Y₁ = Nat.card Y₀ := by
      have hpos : 0 < Nat.card Y₀ := Nat.card_pos
      omega
    have hYeq : Y₀ = Y₁ :=
      Subgroup.eq_of_le_of_card_ge h.le (le_of_eq hc1)
    exact ⟨ψ, hYeq.symm ▸ hψ⟩

private theorem IsLayer.inf_or_eq (W : ThLocalIn L S A B z) {Y₁ Y₂ : Subgroup G} {ψ : G → G}
    (h : IsLayer L A Y₁ Y₂ ψ) {Y' : Subgroup G}
    (hY' : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Y', n * y * n⁻¹ ∈ Y') :
    IsLayer L A (Y₁ ⊓ Y') (Y₂ ⊓ Y') ψ ∨ Y₂ ⊓ Y' = Y₁ ⊓ Y' := by
  classical
  let K : Subgroup G :=
    { carrier := {a | ∃ y ∈ Y₂ ⊓ Y', ψ y = a}
      one_mem' := ⟨1, ⟨h.le Y₁.one_mem, Y'.one_mem⟩, h.map_one⟩
      mul_mem' := by
        rintro a b ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
        exact ⟨y * y', ⟨Y₂.mul_mem hy.1 hy'.1, Y'.mul_mem hy.2 hy'.2⟩,
          h.map_mul y hy.1 y' hy'.1⟩
      inv_mem' := by
        rintro a ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, ⟨Y₂.inv_mem hy.1, Y'.inv_mem hy.2⟩, h.map_inv hy.1⟩ }
  have hKle : K ≤ A := by
    rintro a ⟨y, hy, rfl⟩
    exact h.mem y hy.1
  have hKN : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ k ∈ K, n * k * n⁻¹ ∈ K := by
    rintro n hn a ⟨y, hy, rfl⟩
    exact ⟨n * y * n⁻¹, ⟨h.conj_mem n hn y hy.1, hY' n hn y hy.2⟩,
      h.conj n hn y hy.1⟩
  rcases W.eq_bot_or_eq_A_of_le hKle hKN with hKbot | hKtop
  · right
    refine le_antisymm ?_ (le_inf (le_trans inf_le_left h.le) inf_le_right)
    rintro y ⟨hy₂, hy'⟩
    have hyK : ψ y ∈ K := ⟨y, ⟨hy₂, hy'⟩, rfl⟩
    rw [hKbot] at hyK
    exact ⟨(h.eq_one_iff y hy₂).1 (by simpa using hyK), hy'⟩
  · left
    refine ⟨le_inf (le_trans inf_le_left h.le) inf_le_right,
      fun n hn y hy => ⟨h.conj_mem n hn y hy.1, hY' n hn y hy.2⟩,
      fun y hy => h.mem y hy.1, fun y hy y' hy' => h.map_mul y hy.1 y' hy'.1,
      fun y hy => ⟨fun h1 => ⟨(h.eq_one_iff y hy.1).1 h1, hy.2⟩,
        fun h1 => (h.eq_one_iff y hy.1).2 h1.1⟩,
      ?_, fun n hn y hy => h.conj n hn y hy.1⟩
    intro a ha
    have haK : a ∈ K := by rw [hKtop]; exact ha
    obtain ⟨y, hy, hψy⟩ := haK
    exact ⟨y, hy, hψy⟩

theorem IsTypeA.inf (W : ThLocalIn L S A B z) {Y₀ Y : Subgroup G} (h : IsTypeA L A Y₀ Y)
    {Y' : Subgroup G}
    (hY' : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Y', n * y * n⁻¹ ∈ Y') :
    IsTypeA L A (Y₀ ⊓ Y') (Y ⊓ Y') := by
  induction h with
  | refl hY =>
      exact IsTypeA.refl (Y₀ ⊓ Y') fun n hn y hy => ⟨hY n hn y hy.1, hY' n hn y hy.2⟩
  | step ψ h hψ ih =>
      rcases hψ.inf_or_eq W hY' with hlay | heq
      · exact IsTypeA.step ψ ih hlay
      · rw [heq]
        exact ih

private noncomputable def supLayerFun (ψ : G → G) (Y₂ Y₁ Y'' : Subgroup G) : G → G :=
  fun g => by
    classical
    exact if h : ∃ y ∈ Y₂, ∃ w ∈ Y₁ ⊔ Y'', g = y * w then ψ (Classical.choose h) else 1

private theorem supLayerFun_apply {Y₁ Y₂ Y'' : Subgroup G} {ψ : G → G}
    (h : IsLayer L A Y₁ Y₂ ψ) (hker : ∀ y ∈ Y₂ ⊓ (Y₁ ⊔ Y''), ψ y = 1) {y w : G}
    (hy : y ∈ Y₂) (hw : w ∈ Y₁ ⊔ Y'') :
    supLayerFun ψ Y₂ Y₁ Y'' (y * w) = ψ y := by
  classical
  have hex : ∃ y₀ ∈ Y₂, ∃ w₀ ∈ Y₁ ⊔ Y'', y * w = y₀ * w₀ := ⟨y, hy, w, hw, rfl⟩
  rw [supLayerFun, dif_pos hex]
  obtain ⟨hy₀, w₀, hw₀, heq⟩ := Classical.choose_spec hex
  have hquot : (Classical.choose hex)⁻¹ * y = w₀ * w⁻¹ := by
    have h := congrArg (fun t => (Classical.choose hex)⁻¹ * t * w⁻¹) heq
    have e1 : (Classical.choose hex)⁻¹ * y =
        (Classical.choose hex)⁻¹ * (y * w) * w⁻¹ := by group
    rw [e1, h]
    group
  have hmem : (Classical.choose hex)⁻¹ * y ∈ Y₂ ⊓ (Y₁ ⊔ Y'') := by
    refine ⟨Y₂.mul_mem (Y₂.inv_mem hy₀) hy, ?_⟩
    rw [hquot]
    exact (Y₁ ⊔ Y'').mul_mem hw₀ ((Y₁ ⊔ Y'').inv_mem hw)
  have h1 : ψ ((Classical.choose hex)⁻¹ * y) = 1 := hker _ hmem
  have hmul : ψ ((Classical.choose hex) * ((Classical.choose hex)⁻¹ * y)) =
      ψ (Classical.choose hex) * ψ ((Classical.choose hex)⁻¹ * y) :=
    h.map_mul _ hy₀ _ hmem.1
  calc ψ (Classical.choose hex) = ψ (Classical.choose hex) * 1 := (mul_one _).symm
    _ = ψ (Classical.choose hex) * ψ ((Classical.choose hex)⁻¹ * y) := by rw [h1]
    _ = ψ ((Classical.choose hex) * ((Classical.choose hex)⁻¹ * y)) := hmul.symm
    _ = ψ y := by
        congr 1
        group

private theorem IsLayer.sup_step (W : ThLocalIn L S A B z) {Y₁ Y₂ : Subgroup G} {ψ : G → G}
    (h : IsLayer L A Y₁ Y₂ ψ) {Y'' : Subgroup G}
    (hY'' : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Y'', n * y * n⁻¹ ∈ Y'')
    (hc : ∀ x ∈ Y₂ ⊔ Y'', ∀ y ∈ Y₂ ⊔ Y'', x * y = y * x) :
    (∃ ψ' : G → G, IsLayer L A (Y₁ ⊔ Y'') (Y₂ ⊔ Y'') ψ') ∨ Y₂ ⊔ Y'' = Y₁ ⊔ Y'' := by
  classical
  have hcomm : ∀ x ∈ Y₂, ∀ y ∈ Y'', x * y = y * x := fun x hx y hy =>
    hc x (Subgroup.mem_sup_left hx) y (Subgroup.mem_sup_right hy)
  have hcomm₁ : ∀ x ∈ Y₁, ∀ y ∈ Y'', x * y = y * x := fun x hx y hy =>
    hcomm x (h.le hx) y hy
  have hprod : ∀ z ∈ Y₂ ⊔ Y'', ∃ y ∈ Y₂, ∃ w ∈ Y'', z = y * w := fun z hz => by
    obtain ⟨y, hy, w, hw, e⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hz
    exact ⟨y, hy, w, hw, e.symm⟩
  have hnormY₁ : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ a ∈ Y₁, n * a * n⁻¹ ∈ Y₁ := by
    intro n hn a ha
    have hmem : n * a * n⁻¹ ∈ Y₂ := h.conj_mem n hn a (h.le ha)
    refine (h.eq_one_iff _ hmem).1 ?_
    rw [h.conj n hn a (h.le ha), (h.eq_one_iff a (h.le ha)).2 ha]
    group
  have hnormSup : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Y₁ ⊔ Y'',
      n * y * n⁻¹ ∈ Y₁ ⊔ Y'' := by
    intro n hn y hy
    obtain ⟨a, ha, w, hw, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm₁ hy
    have h1 : n * (a * w) * n⁻¹ = (n * a * n⁻¹) * (n * w * n⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem_sup (hnormY₁ n hn a ha) (hY'' n hn w hw)
  let K : Subgroup G :=
    { carrier := {a | ∃ y ∈ Y₂ ⊓ (Y₁ ⊔ Y''), ψ y = a}
      one_mem' := ⟨1, ⟨h.le Y₁.one_mem, (Y₁ ⊔ Y'').one_mem⟩, h.map_one⟩
      mul_mem' := by
        rintro a b ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
        exact ⟨y * y', ⟨Y₂.mul_mem hy.1 hy'.1, (Y₁ ⊔ Y'').mul_mem hy.2 hy'.2⟩,
          h.map_mul y hy.1 y' hy'.1⟩
      inv_mem' := by
        rintro a ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, ⟨Y₂.inv_mem hy.1, (Y₁ ⊔ Y'').inv_mem hy.2⟩, h.map_inv hy.1⟩ }
  have hKle : K ≤ A := by
    rintro a ⟨y, hy, rfl⟩
    exact h.mem y hy.1
  have hKN : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ k ∈ K, n * k * n⁻¹ ∈ K := by
    rintro n hn a ⟨y, hy, rfl⟩
    exact ⟨n * y * n⁻¹, ⟨h.conj_mem n hn y hy.1, hnormSup n hn y hy.2⟩,
      h.conj n hn y hy.1⟩
  rcases W.eq_bot_or_eq_A_of_le hKle hKN with hKbot | hKtop
  · left
    have hker : ∀ y ∈ Y₂ ⊓ (Y₁ ⊔ Y''), ψ y = 1 := by
      intro y hy
      have hyK : ψ y ∈ K := ⟨y, hy, rfl⟩
      rw [hKbot] at hyK
      simpa using hyK
    refine ⟨supLayerFun ψ Y₂ Y₁ Y'', ?_⟩
    refine ⟨sup_le (le_trans h.le le_sup_left) le_sup_right, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n hn z hz
      obtain ⟨y, hy, w, hw, rfl⟩ := hprod z hz
      have h1 : n * (y * w) * n⁻¹ = (n * y * n⁻¹) * (n * w * n⁻¹) := by group
      rw [h1]
      exact Subgroup.mul_mem_sup (h.conj_mem n hn y hy) (hY'' n hn w hw)
    · intro z hz
      obtain ⟨y, hy, w, hw, rfl⟩ := hprod z hz
      rw [supLayerFun_apply h hker hy (Subgroup.mem_sup_right hw)]
      exact h.mem y hy
    · intro z hz z' hz'
      obtain ⟨y, hy, w, hw, rfl⟩ := hprod z hz
      obtain ⟨y', hy', w', hw', rfl⟩ := hprod z' hz'
      have hassoc : (y * w) * (y' * w') = (y * y') * (w * w') := by
        calc (y * w) * (y' * w') = y * (w * y') * w' := by group
          _ = y * (y' * w) * w' := by rw [hcomm y' hy' w hw]
          _ = (y * y') * (w * w') := by group
      rw [hassoc, supLayerFun_apply h hker (Y₂.mul_mem hy hy')
          (Subgroup.mem_sup_right (Y''.mul_mem hw hw')),
        supLayerFun_apply h hker hy (Subgroup.mem_sup_right hw),
        supLayerFun_apply h hker hy' (Subgroup.mem_sup_right hw'), h.map_mul y hy y' hy']
    · intro z hz
      obtain ⟨y, hy, w, hw, rfl⟩ := hprod z hz
      rw [supLayerFun_apply h hker hy (Subgroup.mem_sup_right hw)]
      constructor
      · intro h1
        exact (Y₁ ⊔ Y'').mul_mem (Subgroup.mem_sup_left ((h.eq_one_iff y hy).1 h1))
          (Subgroup.mem_sup_right hw)
      · intro h1
        have hmem : y ∈ Y₂ ⊓ (Y₁ ⊔ Y'') := by
          refine ⟨hy, ?_⟩
          have hyw : y = (y * w) * w⁻¹ := by group
          rw [hyw]
          exact (Y₁ ⊔ Y'').mul_mem h1 ((Y₁ ⊔ Y'').inv_mem (Subgroup.mem_sup_right hw))
        exact hker y hmem
    · intro a ha
      obtain ⟨y, hy, hψy⟩ := h.surj a ha
      refine ⟨y * 1, Subgroup.mul_mem_sup hy Y''.one_mem, ?_⟩
      rw [supLayerFun_apply h hker hy (Subgroup.mem_sup_right Y''.one_mem), hψy]
    · intro n hn z hz
      obtain ⟨y, hy, w, hw, rfl⟩ := hprod z hz
      have h1 : n * (y * w) * n⁻¹ = (n * y * n⁻¹) * (n * w * n⁻¹) := by group
      rw [h1, supLayerFun_apply h hker (h.conj_mem n hn y hy)
          (Subgroup.mem_sup_right (hY'' n hn w hw)),
        supLayerFun_apply h hker hy (Subgroup.mem_sup_right hw), h.conj n hn y hy]
  · right
    refine le_antisymm ?_ (sup_le (le_trans h.le le_sup_left) le_sup_right)
    intro z hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hprod z hz
    have hψyK : ψ y ∈ K := by
      rw [hKtop]
      exact h.mem y hy
    obtain ⟨y', hy', hψy'⟩ := hψyK
    have hker : y * y'⁻¹ ∈ Y₁ :=
      h.inf_mem_of_map_eq hy hy'.1 hψy'.symm
    have hyW : y ∈ Y₁ ⊔ Y'' := by
      have h2 : y = (y * y'⁻¹) * y' := by group
      rw [h2]
      exact (Y₁ ⊔ Y'').mul_mem (Subgroup.mem_sup_left hker) hy'.2
    exact (Y₁ ⊔ Y'').mul_mem hyW (Subgroup.mem_sup_right hw)

theorem IsTypeA.sup (W : ThLocalIn L S A B z) {Y₀ Y : Subgroup G} (h : IsTypeA L A Y₀ Y)
    {Y'' : Subgroup G}
    (hY'' : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Y'', n * y * n⁻¹ ∈ Y'')
    (hc : ∀ x ∈ Y ⊔ Y'', ∀ y ∈ Y ⊔ Y'', x * y = y * x) :
    IsTypeA L A (Y₀ ⊔ Y'') (Y ⊔ Y'') := by
  revert hc
  refine IsTypeA.rec (motive := fun Y _ => (∀ x ∈ Y ⊔ Y'', ∀ y ∈ Y ⊔ Y'', x * y = y * x) →
    IsTypeA L A (Y₀ ⊔ Y'') (Y ⊔ Y'')) ?_ ?_ h
  · intro hY hc
    have hcomm : ∀ x ∈ Y₀, ∀ y ∈ Y'', x * y = y * x := fun x hx y hy =>
      hc x (Subgroup.mem_sup_left hx) y (Subgroup.mem_sup_right hy)
    refine IsTypeA.refl (Y₀ ⊔ Y'') fun n hn y hy => ?_
    obtain ⟨a, ha, w, hw, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hy
    have h1 : n * (a * w) * n⁻¹ = (n * a * n⁻¹) * (n * w * n⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem_sup (hY n hn a ha) (hY'' n hn w hw)
  · intro Y₁ Y₂ ψ h hψ ih hc
    have hle : Y₁ ⊔ Y'' ≤ Y₂ ⊔ Y'' :=
      sup_le (le_trans hψ.le le_sup_left) le_sup_right
    have hc₁ : ∀ x ∈ Y₁ ⊔ Y'', ∀ y ∈ Y₁ ⊔ Y'', x * y = y * x :=
      fun x hx y hy => hc x (hle hx) y (hle hy)
    rcases hψ.sup_step W hY'' hc with ⟨ψ', hlay⟩ | heq
    · exact IsTypeA.step ψ' (ih hc₁) hlay
    · rw [heq]
      exact ih hc₁

theorem ThCyc.isLayer_omega1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    IsLayer L A A (omega1 D hD.comm) (thV t) := by
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  refine ⟨H.A_le_omega1 W W2 hD, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn y hy
    have hnD : n ∈ L ⊓ normalizer (D : Set G) := by
      rw [H.inf_normalizer_D_eq W W2 hD]
      exact hn
    refine ⟨(mem_normalizer_iff.1 hnD.2 y).1 hy.1, ?_⟩
    calc (n * y * n⁻¹) ^ 2 = n * y ^ 2 * n⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hy.2]; group
  · intro y hy
    exact H.thV_mem_A W W2 hD hy
  · intro y hy y' hy'
    exact H.thV_mul W W2 hD hy hy'
  · intro y hy
    exact H.thV_eq_one_iff W W2 hD hy
  · intro a ha
    exact H.thV_surj W W2 hD hsq a ha
  · intro n hn y hy
    exact H.thV_conj W W2 hD hn.1

theorem ThCyc.isLayer_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    IsLayer L A (omega1 D hD.comm) D (fun d => d ^ 2) := by
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  refine ⟨fun x hx => hx.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn y hy
    have hnD : n ∈ L ⊓ normalizer (D : Set G) := by
      rw [H.inf_normalizer_D_eq W W2 hD]
      exact hn
    exact (mem_normalizer_iff.1 hnD.2 y).1 hy
  · intro y hy
    exact hsq y hy
  · intro y hy y' hy'
    exact (show Commute y y' from hD.comm y hy y' hy').mul_pow 2
  · intro y hy
    rw [mem_omega1_iff]
    exact ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩
  · intro a ha
    obtain ⟨x, hx, hx2⟩ := (W2.A_eq_sq a).1 ha
    exact ⟨x, hD.Aa_le hx, hx2⟩
  · intro n hn y hy
    show (n * y * n⁻¹) ^ 2 = n * y ^ 2 * n⁻¹
    rw [sq, sq]
    group

theorem ThCyc.isTypeA_bot_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    IsTypeA L A ⊥ D := by
  have hbot : IsTypeA L A ⊥ ⊥ :=
    IsTypeA.refl ⊥ fun n hn y hy => by
      rw [Subgroup.mem_bot] at hy ⊢
      rw [hy]
      group
  have hid : IsLayer L A ⊥ A (fun y => y) := by
    refine ⟨bot_le, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n hn y hy
      exact (mem_normalizer_iff.1 hn.2 y).1 hy
    · intro y hy
      exact hy
    · intro y hy y' hy'
      rfl
    · intro y hy
      exact ⟨fun h => by rw [h]; exact Subgroup.one_mem ⊥, fun h => by simpa using h⟩
    · intro a ha
      exact ⟨a, ha, rfl⟩
    · intro n hn y hy
      rfl
  exact IsTypeA.step (fun d => d ^ 2)
    (IsTypeA.step (thV t) (IsTypeA.step (fun y => y) hbot hid)
      (H.isLayer_omega1 W W2 hD h4))
    (H.isLayer_D W W2 hD h4)

end CFSG.EvenSporadicStandard.ThStd

end
