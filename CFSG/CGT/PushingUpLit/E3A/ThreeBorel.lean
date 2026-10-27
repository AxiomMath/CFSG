module

public import CFSG.CGT.PushingUpLit.E3A.ThreeBase

public section

namespace CFSG.CGT.PushingUpLit.E3A

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit.SolK CFSG.RankThree.PartOne.SolD3
open CFSG.Assembly (pCoreOf)

variable {G : Type} [Group G] [Finite G] {R X : Subgroup G} {a : G}

theorem false_of_sylow_eq (h : Hyp3 G (Subgroup.normalizer (R : Set G)) X) (hb : Blk3 X a)
    (hXC : X ≤ Subgroup.centralizer (R : Set G)) (S : Sylow 2 G) (hSR : (S : Subgroup G) = R) :
    False := by
  refine false_of_W_le_R hb hXC fun w hw => ?_
  have hM : Subgroup.normalizer (R : Set G) = Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [hSR]
  rw [← hSR]
  exact (W_le_center_sylow h hb S hM w hw).1

theorem false_of_center_sylow (h : Hyp3 G (Subgroup.normalizer (R : Set G)) X) (hb : Blk3 X a)
    (hXC : X ≤ Subgroup.centralizer (R : Set G)) (S S' : Sylow 2 G)
    (hR : R = (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hN : Subgroup.normalizer (R : Set G) = Subgroup.normalizer ((S' : Subgroup G) : Set G)) :
    False := by
  have hRmem : ∀ x : G, x ∈ R ↔ x ∈ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), s * x * s⁻¹ = x := by
    intro x
    rw [hR]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, fun s hs => ?_⟩
      have := Subgroup.mem_center_iff.1 hz ⟨s, hs⟩
      have h2 : s * (z : G) = (z : G) * s := congrArg Subtype.val this
      change s * (z : G) * s⁻¹ = (z : G)
      rw [h2]
      group
    · rintro ⟨hxS, hxc⟩
      refine ⟨⟨x, hxS⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
      have := hxc g g.2
      simp only [Subgroup.coe_mul]
      exact mul_inv_eq_iff_eq_mul.1 this
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := (hRmem x).1 hx
      rw [this.2 s hs]
      exact hx
    · intro hx
      have hc := ((hRmem _).1 hx).2 s⁻¹ ((S : Subgroup G).inv_mem hs)
      have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
      rw [e] at hc
      rw [hc]
      exact hx
  have hSS' : (S : Subgroup G) ≤ (S' : Subgroup G) :=
    le_sylow_of_le_normalizer S' S.isPGroup' (by rw [← hN]; exact hSN)
  have hEq : (S' : Subgroup G) = (S : Subgroup G) := S.is_maximal' S'.isPGroup' hSS'
  have hM : Subgroup.normalizer (R : Set G) = Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [hN, hEq]
  refine false_of_W_le_R hb hXC fun w hw => ?_
  obtain ⟨hwS, hwc⟩ := W_le_center_sylow h hb S hM w hw
  exact (hRmem w).2 ⟨hwS, hwc⟩

end CFSG.CGT.PushingUpLit.E3A
