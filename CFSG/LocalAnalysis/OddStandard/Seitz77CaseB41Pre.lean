module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Config

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Pre

variable {G : Type} [Group G] (W : Subgroup G)

abbrev qN : ↥(normalizer (W : Set G)) →* Hh27 W := QuotientGroup.mk' (KW27 W)

@[expose] noncomputable def qG (x : G) : Hh27 W :=
  open scoped Classical in
  if h : x ∈ normalizer (W : Set G) then qN W ⟨x, h⟩ else 1

@[expose] def preN (Y : Subgroup (Hh27 W)) : Subgroup G :=
  (Y.comap (qN W)).map (normalizer (W : Set G)).subtype

variable {W}

theorem qG_of_mem {x : G} (hx : x ∈ normalizer (W : Set G)) : qG W x = qN W ⟨x, hx⟩ := by
  simp [qG, hx]

theorem qG_mul {x y : G} (hx : x ∈ normalizer (W : Set G)) (hy : y ∈ normalizer (W : Set G)) :
    qG W (x * y) = qG W x * qG W y := by
  rw [qG_of_mem (mul_mem hx hy), qG_of_mem hx, qG_of_mem hy, ← map_mul]
  rfl

theorem qG_inv {x : G} (hx : x ∈ normalizer (W : Set G)) : qG W x⁻¹ = (qG W x)⁻¹ := by
  rw [qG_of_mem (inv_mem hx), qG_of_mem hx, ← map_inv]
  rfl

theorem qG_commutator {x y : G} (hx : x ∈ normalizer (W : Set G))
    (hy : y ∈ normalizer (W : Set G)) : qG W ⁅x, y⁆ = ⁅qG W x, qG W y⁆ := by
  simp only [commutatorElement_def]
  rw [qG_mul (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy), qG_mul (mul_mem hx hy)
    (inv_mem hx), qG_mul hx hy, qG_inv hx, qG_inv hy]

theorem qG_conj {x y : G} (hx : x ∈ normalizer (W : Set G)) (hy : y ∈ normalizer (W : Set G)) :
    qG W (x * y * x⁻¹) = qG W x * qG W y * (qG W x)⁻¹ := by
  rw [qG_mul (mul_mem hx hy) (inv_mem hx), qG_mul hx hy, qG_inv hx]

theorem qG_eq_one_iff {x : G} (hx : x ∈ normalizer (W : Set G)) :
    qG W x = 1 ↔ x ∈ centralizer (W : Set G) := by
  rw [qG_of_mem hx]
  exact (QuotientGroup.eq_one_iff _).trans mem_subgroupOf

theorem qG_surjective (y : Hh27 W) :
    ∃ x : G, ∃ hx : x ∈ normalizer (W : Set G), qN W ⟨x, hx⟩ = y := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨n, n.2, rfl⟩

theorem qG_act {x : G} (hx : x ∈ normalizer (W : Set G)) (w : ↥W) :
    ((alpha27 W (qG W x) w : ↥W) : G) = x * (w : G) * x⁻¹ := by
  rw [qG_of_mem hx, qN, QuotientGroup.mk'_apply, alpha27_mk]
  rfl

theorem mem_preN {Y : Subgroup (Hh27 W)} {x : G} :
    x ∈ preN W Y ↔ ∃ h : x ∈ normalizer (W : Set G), qN W ⟨x, h⟩ ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem mem_preN' {Y : Subgroup (Hh27 W)} {x : G} :
    x ∈ preN W Y ↔ x ∈ normalizer (W : Set G) ∧ qG W x ∈ Y := by
  rw [mem_preN]
  constructor
  · rintro ⟨h, hx⟩
    exact ⟨h, by rwa [qG_of_mem h]⟩
  · rintro ⟨h, hx⟩
    exact ⟨h, by rwa [qG_of_mem h] at hx⟩

theorem preN_le_normalizer (Y : Subgroup (Hh27 W)) : preN W Y ≤ normalizer (W : Set G) :=
  fun _ hx => (mem_preN.mp hx).1

theorem preN_mono {Y Y' : Subgroup (Hh27 W)} (h : Y ≤ Y') : preN W Y ≤ preN W Y' := by
  intro x hx
  obtain ⟨hn, hq⟩ := mem_preN'.mp hx
  exact mem_preN'.mpr ⟨hn, h hq⟩

theorem preN_inf (Y Y' : Subgroup (Hh27 W)) : preN W (Y ⊓ Y') = preN W Y ⊓ preN W Y' := by
  ext x
  simp only [mem_inf, mem_preN']
  tauto

theorem mem_preN_bot {x : G} : x ∈ preN W ⊥ ↔ x ∈ centralizer (W : Set G) := by
  rw [mem_preN']
  constructor
  · rintro ⟨hn, hq⟩
    exact (qG_eq_one_iff hn).mp (Subgroup.mem_bot.mp hq)
  · intro hx
    have hn : x ∈ normalizer (W : Set G) := Subgroup.centralizer_le_normalizer _ hx
    exact ⟨hn, Subgroup.mem_bot.mpr ((qG_eq_one_iff hn).mpr hx)⟩

theorem centralizer_le_preN (Y : Subgroup (Hh27 W)) : centralizer (W : Set G) ≤ preN W Y := by
  intro x hx
  have hn : x ∈ normalizer (W : Set G) := Subgroup.centralizer_le_normalizer _ hx
  exact mem_preN'.mpr ⟨hn, by rw [(qG_eq_one_iff hn).mpr hx]; exact Y.one_mem⟩

theorem preN_sup_of_commute {Y Y' : Subgroup (Hh27 W)} (hc : ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a) :
    preN W (Y ⊔ Y') = preN W Y ⊔ preN W Y' := by
  refine le_antisymm (fun x hx => ?_) (sup_le (preN_mono le_sup_left) (preN_mono le_sup_right))
  obtain ⟨hn, hq⟩ := mem_preN'.mp hx
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_forall_comm hc hq
  obtain ⟨y₁, hy₁, hay⟩ := qG_surjective a
  obtain ⟨y₂, hy₂, hby⟩ := qG_surjective b
  have h1 : y₁ ∈ preN W Y := mem_preN.mpr ⟨hy₁, hay ▸ ha⟩
  have h2 : y₂ ∈ preN W Y' := mem_preN.mpr ⟨hy₂, hby ▸ hb⟩
  have hk : (y₁ * y₂)⁻¹ * x ∈ centralizer (W : Set G) := by
    have hn' : (y₁ * y₂)⁻¹ * x ∈ normalizer (W : Set G) :=
      mul_mem (inv_mem (mul_mem hy₁ hy₂)) hn
    rw [← qG_eq_one_iff hn', qG_mul (inv_mem (mul_mem hy₁ hy₂)) hn,
      qG_inv (mul_mem hy₁ hy₂), qG_mul hy₁ hy₂, qG_of_mem hy₁, qG_of_mem hy₂, hay, hby, hab]
    exact inv_mul_cancel _
  have hxe : x = y₁ * (y₂ * ((y₁ * y₂)⁻¹ * x)) := by group
  rw [hxe]
  exact Subgroup.mul_mem_sup h1 ((preN W Y').mul_mem h2 (centralizer_le_preN Y' hk))

theorem exists_mul_of_preN [Finite G] (Lam : Subgroup (Hh27 W)) [Group.IsPerfect ↥Lam] {y : G}
    (hy : y ∈ preN W Lam) :
    ∃ k ∈ centralizer (W : Set G), ∃ m ∈ perfectResidualOf (preN W Lam), y = k * m := by
  let f : ↥(preN W Lam) →* ↥Lam :=
    MonoidHom.mk' (fun z => ⟨qG W z.1, (mem_preN'.mp z.2).2⟩) (fun a b => Subtype.ext
      (qG_mul (mem_preN'.mp a.2).1 (mem_preN'.mp b.2).1))
  have hf : Function.Surjective f := by
    intro l
    obtain ⟨x, hx, hxl⟩ := qG_surjective (l : Hh27 W)
    have hxP : x ∈ preN W Lam := mem_preN.mpr ⟨hx, by rw [hxl]; exact l.2⟩
    refine ⟨⟨x, hxP⟩, Subtype.ext ?_⟩
    show qG W x = l
    rw [qG_of_mem hx, hxl]
  have hmap := finite_perfectResidual_surjects_to_perfect_image f hf
  have hyT : (⟨y, hy⟩ : ↥(preN W Lam)) ∈ (⊤ : Subgroup ↥(preN W Lam)) := trivial
  obtain ⟨m', hm', hfm⟩ : ∃ m' ∈ perfectResidual ↥(preN W Lam), f m' = f ⟨y, hy⟩ := by
    have : f ⟨y, hy⟩ ∈ (⊤ : Subgroup ↥Lam) := trivial
    rw [← hmap] at this
    exact this
  have hm'N : (m' : G) ∈ normalizer (W : Set G) := (mem_preN'.mp m'.2).1
  have hyN : y ∈ normalizer (W : Set G) := (mem_preN'.mp hy).1
  have hq : qG W (m' : G) = qG W y := congrArg Subtype.val hfm
  refine ⟨y * (m' : G)⁻¹, ?_, (m' : G), ⟨m', hm', rfl⟩, by group⟩
  have hn : y * (m' : G)⁻¹ ∈ normalizer (W : Set G) := mul_mem hyN (inv_mem hm'N)
  rw [← qG_eq_one_iff hn, qG_mul hyN (inv_mem hm'N), qG_inv hm'N, hq, mul_inv_cancel]

theorem qG_pow {x : G} (hx : x ∈ normalizer (W : Set G)) (n : ℕ) :
    qG W (x ^ n) = (qG W x) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, qG_of_mem (one_mem _)]
    exact map_one _
  | succ n ih =>
    rw [pow_succ, pow_succ, qG_mul (pow_mem hx n) hx, ih]

theorem relIndex_preN [Finite G] (Lam : Subgroup (Hh27 W)) :
    (centralizer (W : Set G)).relIndex (preN W Lam) = Nat.card ↥Lam := by
  let f : ↥(preN W Lam) →* ↥Lam :=
    MonoidHom.mk' (fun z => ⟨qG W z.1, (mem_preN'.mp z.2).2⟩) (fun a b => Subtype.ext
      (qG_mul (mem_preN'.mp a.2).1 (mem_preN'.mp b.2).1))
  have hf : Function.Surjective f := by
    intro l
    obtain ⟨x, hx, hxl⟩ := qG_surjective (l : Hh27 W)
    have hxP : x ∈ preN W Lam := mem_preN.mpr ⟨hx, by rw [hxl]; exact l.2⟩
    refine ⟨⟨x, hxP⟩, Subtype.ext ?_⟩
    show qG W x = l
    rw [qG_of_mem hx, hxl]
  have hker : f.ker = (centralizer (W : Set G)).subgroupOf (preN W Lam) := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : qG W (z : G) = 1 := congrArg Subtype.val h
      exact (qG_eq_one_iff (mem_preN'.mp z.2).1).mp h1
    · intro h
      exact Subtype.ext ((qG_eq_one_iff (mem_preN'.mp z.2).1).mpr h)
  have h1 := Subgroup.card_ker_mul_card_of_surjective hf
  rw [hker] at h1
  have h2 := Subgroup.card_mul_index ((centralizer (W : Set G)).subgroupOf (preN W Lam))
  have hpos : 0 < Nat.card ↥((centralizer (W : Set G)).subgroupOf (preN W Lam)) := Nat.card_pos
  have : Nat.card ↥((centralizer (W : Set G)).subgroupOf (preN W Lam)) *
      (centralizer (W : Set G)).relIndex (preN W Lam) =
      Nat.card ↥((centralizer (W : Set G)).subgroupOf (preN W Lam)) * Nat.card ↥Lam := by
    rw [h1]
    exact h2
  exact Nat.eq_of_mul_eq_mul_left hpos this

end Pre

end CFSG.OddStandard.Seitz77
