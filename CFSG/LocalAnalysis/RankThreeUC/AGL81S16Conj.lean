module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup

variable {G : Type} [Group G]

abbrev cj (g : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj g).toMonoidHom

theorem mem_cj_iff {g x : G} {X : Subgroup G} : x ∈ cj g X ↔ g⁻¹ * x * g ∈ X :=
  Subgroup.mem_map_equiv (f := MulAut.conj g)

theorem cj_le_cj_iff {g : G} {X Y : Subgroup G} : cj g X ≤ cj g Y ↔ X ≤ Y :=
  Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective

theorem cj_cj (g h : G) (X : Subgroup G) : cj g (cj h X) = cj (g * h) X := by
  ext x
  simp only [mem_cj_iff, mul_inv_rev, mul_assoc]

theorem cj_one (X : Subgroup G) : cj (1 : G) X = X := by
  ext x
  simp only [mem_cj_iff, inv_one, one_mul, mul_one]

theorem cj_inf (g : G) (X Y : Subgroup G) : cj g (X ⊓ Y) = cj g X ⊓ cj g Y := by
  ext x
  simp only [mem_cj_iff, Subgroup.mem_inf]

theorem cj_eq_bot_iff {g : G} {X : Subgroup G} : cj g X = ⊥ ↔ X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective X (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective

theorem cj_centralizer (g : G) (X : Subgroup G) :
    centralizer ((cj g X : Subgroup G) : Set G) = cj g (centralizer (X : Set G)) := by
  ext y
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, mem_cj_iff]
  constructor
  · intro H k hk
    have h1 := H (g * k * g⁻¹) (by rw [show g⁻¹ * (g * k * g⁻¹) * g = k by group]; exact hk)
    calc k * (g⁻¹ * y * g) = g⁻¹ * (g * k * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * k * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * y * g * k := by group
  · intro H h hh
    have h1 := H (g⁻¹ * h * g) hh
    calc h * y = g * (g⁻¹ * h * g * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
      _ = y * h := by group

theorem cj_normalizer (g : G) (X : Subgroup G) :
    normalizer ((cj g X : Subgroup G) : Set G) = cj g (normalizer (X : Set G)) :=
  (Subgroup.map_equiv_normalizer_eq X (MulAut.conj g)).symm

theorem card_cj (g : G) (X : Subgroup G) : Nat.card ↥(cj g X) = Nat.card ↥X :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem isPGroup_cj {p : ℕ} {g : G} {X : Subgroup G} (h : IsPGroup p ↥X) :
    IsPGroup p ↥(cj g X) :=
  h.map (MulAut.conj g).toMonoidHom

theorem isElemAbelian_cj {p : ℕ} {g : G} {X : Subgroup G} (h : IsElemAbelian p X) :
    IsElemAbelian p (cj g X) := by
  unfold IsElemAbelian at h ⊢
  obtain ⟨hcomm, hpow⟩ := h
  rw [isMulCommutative_iff] at hcomm
  refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
  · rintro ⟨y₁, h₁⟩ ⟨y₂, h₂⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp h₁
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp h₂
    have hab : a * b = b * a := congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
    apply Subtype.ext
    show (MulAut.conj g) a * (MulAut.conj g) b = (MulAut.conj g) b * (MulAut.conj g) a
    rw [← map_mul, ← map_mul, hab]
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_pow (MulAut.conj g).toMonoidHom a p, hpow a ha, map_one]

theorem pRank_cj [Finite G] (p : ℕ) (g : G) (X : Subgroup G) :
    CFSG.Open.pRank p (cj g X) = CFSG.Open.pRank p X := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨E, hE, hab, hcard⟩
    refine ⟨cj g⁻¹ E, ?_, isElemAbelian_cj (g := g⁻¹) hab, ?_⟩
    · calc cj g⁻¹ E ≤ cj g⁻¹ (cj g X) := (cj_le_cj_iff (g := g⁻¹)).mpr hE
        _ = X := by rw [cj_cj, inv_mul_cancel, cj_one]
    · rw [card_cj]
      exact hcard
  · rintro ⟨E, hE, hab, hcard⟩
    refine ⟨cj g E, (cj_le_cj_iff (g := g)).mpr hE, isElemAbelian_cj (g := g) hab, ?_⟩
    rw [card_cj]
    exact hcard

end CFSG.LocalAnalysis.RankThreeUC
