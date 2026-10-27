module

public import CFSG.Sporadic.SmallOddCore.CompImage
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Subgroup CFSG

theorem isComponent_eq_top_of_perfect {C X : Type*} [Group C] [Finite C] [Group X]
    (hC : Group.IsPerfect C) (ρ : C →* X) (hρ : Function.Surjective ρ) (hX : IsSimpleGroup X)
    (hker : ρ.ker ≤ center C) {K : Subgroup C} (hK : IsComponent K) : K = ⊤ := by
  have hsolv : Group.IsSolvable ρ.ker := by
    have : IsMulCommutative ρ.ker := ⟨⟨fun a b => Subtype.ext (by
      have := Subgroup.mem_center_iff.1 (hker a.2) b
      exact this.symm)⟩⟩
    infer_instance
  have hmap := Sporadic.SmallOddCore.map_eq_top_of_isComponent ρ hρ hsolv hX hK
  have hsup : K ⊔ ρ.ker = ⊤ := by
    have h := Subgroup.comap_map_eq ρ K
    rw [hmap, Subgroup.comap_top] at h
    exact h.symm
  have hKn : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    refine sup_le Subgroup.le_normalizer (fun z hz => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_center_iff.1 (hker hz) h
    have hz' : z * h * z⁻¹ = h := by rw [← this]; group
    rw [hz']
  have hcomm : ∀ a b : C ⧸ K, a * b = b * a := by
    intro a b
    obtain ⟨c₁, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨c₂, rfl⟩ := QuotientGroup.mk_surjective b
    have h1 : c₁ ∈ K ⊔ ρ.ker := by rw [hsup]; trivial
    have h2 : c₂ ∈ K ⊔ ρ.ker := by rw [hsup]; trivial
    rw [Subgroup.mem_sup_of_normal_right] at h1 h2
    obtain ⟨b₁, hb₁, z₁, hz₁, rfl⟩ := h1
    obtain ⟨b₂, hb₂, z₂, hz₂, rfl⟩ := h2
    have hb1 : (QuotientGroup.mk b₁ : C ⧸ K) = 1 := (QuotientGroup.eq_one_iff b₁).2 hb₁
    have hb2 : (QuotientGroup.mk b₂ : C ⧸ K) = 1 := (QuotientGroup.eq_one_iff b₂).2 hb₂
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hb1, hb2, one_mul, one_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subgroup.mem_center_iff.1 (hker hz₂) z₁)
  have hperf : Group.IsPerfect (C ⧸ K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective K)
  by_contra hne
  have hnt : Nontrivial (C ⧸ K) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    apply hne
    rw [eq_top_iff]
    intro x _
    exact (QuotientGroup.eq_one_iff x).1 (Subsingleton.elim _ _)
  have : IsMulCommutative (C ⧸ K) := ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ ‹_›

theorem isQuasisimple_of_perfect_cover {C X : Type*} [Group C] [Group X] (hC : Group.IsPerfect C)
    (ρ : C →* X) (hρ : Function.Surjective ρ) (hX : IsSimpleGroup X)
    (hXn : ∃ a b : X, a * b ≠ b * a) (hker : ρ.ker ≤ center C) : IsQuasisimple C := by
  have hZX : center X = ⊥ := LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hXn
  have hcen : center C ≤ ρ.ker := by
    intro x hx
    have : ρ x ∈ center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨c, rfl⟩ := hρ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx c]
    rw [hZX, Subgroup.mem_bot] at this
    exact this
  have heq : center C = ρ.ker := le_antisymm hcen hker
  let e : (C ⧸ center C) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq heq).trans (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  refine ⟨hC, e.isSimpleGroup_congr.2 hX, ?_⟩
  obtain ⟨a, b, hab⟩ := hXn
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end CFSG.GH74.GLS.IVK.GHInv
