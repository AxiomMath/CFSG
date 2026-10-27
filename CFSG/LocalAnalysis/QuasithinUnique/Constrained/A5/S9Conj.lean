module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.TwoThree
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.QuasithinUnique.A5

section ConjSq

variable {G : Type} [Group G] {K : Subgroup G}

theorem conj_mem_of_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    g⁻¹ * (k : G) * g ∈ K :=
  (Subgroup.mem_set_normalizer_iff''.1 hg k).1 k.2

theorem inv_mem_normalizer' {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g⁻¹ ∈ Subgroup.normalizer (K : Set G) := (Subgroup.normalizer (K : Set G)).inv_mem hg

@[expose] def conjSq {i : G} (hii : i * i = 1) (hi : i ∈ Subgroup.normalizer (K : Set G)) :
    MulAut ↥K where
  toFun k := ⟨i⁻¹ * (k : G) * i, conj_mem_of_normalizer hi k⟩
  invFun k := ⟨i⁻¹ * (k : G) * i, conj_mem_of_normalizer hi k⟩
  left_inv k := Subtype.ext (by
    show i⁻¹ * (i⁻¹ * (k : G) * i) * i = k
    calc i⁻¹ * (i⁻¹ * (k : G) * i) * i = (i * i)⁻¹ * (k : G) * (i * i) := by group
      _ = k := by rw [hii]; simp)
  right_inv k := Subtype.ext (by
    show i⁻¹ * (i⁻¹ * (k : G) * i) * i = k
    calc i⁻¹ * (i⁻¹ * (k : G) * i) * i = (i * i)⁻¹ * (k : G) * (i * i) := by group
      _ = k := by rw [hii]; simp)
  map_mul' a b := Subtype.ext (by
    show i⁻¹ * ((a : G) * b) * i = (i⁻¹ * a * i) * (i⁻¹ * b * i)
    group)

theorem conjSq_sq {i : G} (hii : i * i = 1) (hi : i ∈ Subgroup.normalizer (K : Set G))
    (k : ↥K) : conjSq hii hi (conjSq hii hi k) = k := (conjSq hii hi).symm_apply_apply k

@[expose] def conjAutK (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) : MulAut ↥K where
  toFun k := ⟨x⁻¹ * (k : G) * x, conj_mem_of_normalizer hx k⟩
  invFun k := ⟨x * (k : G) * x⁻¹, by
    have := conj_mem_of_normalizer (inv_mem_normalizer' hx) k
    simpa using this⟩
  left_inv k := Subtype.ext (by
    show x * (x⁻¹ * (k : G) * x) * x⁻¹ = k
    group)
  right_inv k := Subtype.ext (by
    show x⁻¹ * (x * (k : G) * x⁻¹) * x = k
    group)
  map_mul' a b := Subtype.ext (by
    show x⁻¹ * ((a : G) * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x)
    group)

end ConjSq

end CFSG.QuasithinUnique.A5
