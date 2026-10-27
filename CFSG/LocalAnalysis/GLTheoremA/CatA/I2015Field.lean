module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Yardstones.Md0ec50421ce4

section Field

variable {G : Type} [Group G]

theorem inv_mul_mul_mem_of_normalizer {J : Subgroup G} {d : G} (hd : d ∈ Subgroup.normalizer (J : Set G))
    {x : G} (hx : x ∈ J) : d⁻¹ * x * d ∈ J := by
  have hdi : d⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hd
  have := (Subgroup.mem_normalizer_iff.1 hdi x).1 hx
  simpa using this

@[expose] def conjAutOf (J : Subgroup G) (d : G) (hd : d ∈ Subgroup.normalizer (J : Set G)) :
    MulAut ↥J where
  toFun x := ⟨d⁻¹ * x.1 * d, inv_mul_mul_mem_of_normalizer hd x.2⟩
  invFun y := ⟨d * y.1 * d⁻¹, by
    have hdi : d⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hd
    have := inv_mul_mul_mem_of_normalizer hdi y.2
    simpa using this⟩
  left_inv x := Subtype.ext (by group)
  right_inv y := Subtype.ext (by group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjAutOf_apply (J : Subgroup G) (d : G) (hd : d ∈ Subgroup.normalizer (J : Set G))
    (x : ↥J) : ((conjAutOf J d hd) x : G) = d⁻¹ * x.1 * d :=
  rfl

theorem indRel_eq_relOfAut (p : ℕ) (J : Subgroup G) (d : G)
    (hd : d ∈ Subgroup.normalizer (J : Set G)) :
    indRel p J d = relOfAut p (conjAutOf J d hd) := by
  funext q q'
  apply propext
  constructor
  · rintro ⟨l, l', h1, h2, h3⟩
    exact ⟨l, l', h1, h2, Subtype.ext (by rw [conjAutOf_apply]; exact h3.symm)⟩
  · rintro ⟨l, l', h1, h2, h3⟩
    refine ⟨l, l', h1, h2, ?_⟩
    have h4 := congrArg Subtype.val h3
    rw [conjAutOf_apply] at h4
    exact h4.symm

theorem fieldAutOn_of_R2Prop {p : ℕ} {J : Subgroup G} {d : G} [Finite G]
    (h : R2Prop p d J) : ∃ hd : d ∈ Subgroup.normalizer (J : Set G),
      FieldAutOn p ↥J (conjAutOf J d hd) := by
  rcases h with hF | ⟨hp3, hT, hNI⟩
  · obtain ⟨hd, hM⟩ := hF
    refine ⟨hd, Or.inl ?_⟩
    have hrel := indRel_eq_relOfAut p J d hd
    rw [← hrel]
    exact hM
  · obtain ⟨hd, hNI'⟩ := hNI
    refine ⟨hd, Or.inr ⟨hp3, hT, ?_⟩⟩
    rintro ⟨l, hl⟩
    apply hNI'
    refine ⟨l.1, l.2, ?_⟩
    intro y hy
    have h1 := hl ⟨y, hy⟩
    unfold GLAPPrimeCoreOf
    refine Subgroup.mem_map.2 ⟨_, h1, ?_⟩
    simp [conjAutOf_apply]

theorem conjAutOf_pow_apply (J : Subgroup G) (d : G) (hd : d ∈ Subgroup.normalizer (J : Set G))
    (n : ℕ) (x : ↥J) : (((conjAutOf J d hd) ^ n) x : G) = d⁻¹ ^ n * x.1 * d ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, conjAutOf_apply, ih]
    simp only [pow_succ', mul_assoc]
    group

theorem conjAutOf_pow_eq_one (J : Subgroup G) (d : G) (hd : d ∈ Subgroup.normalizer (J : Set G))
    {p : ℕ} (hdp : d ^ p = 1) : (conjAutOf J d hd) ^ p = 1 := by
  ext x
  rw [conjAutOf_pow_apply]
  simp [inv_pow, hdp]

theorem fixSub_conjAutOf (J : Subgroup G) (d : G) (hd : d ∈ Subgroup.normalizer (J : Set G)) :
    fixSub (conjAutOf J d hd) = (J ⊓ cx d).subgroupOf J := by
  ext x
  show (conjAutOf J d hd) x = x ↔ x ∈ (J ⊓ cx d).subgroupOf J
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hx
    have hx' : d⁻¹ * x.1 * d = x.1 := by
      have := congrArg Subtype.val hx
      rw [conjAutOf_apply] at this
      exact this
    have h2 : x.1 * d = d * x.1 := by
      calc x.1 * d = d * (d⁻¹ * x.1 * d) := by group
        _ = d * x.1 := by rw [hx']
    refine ⟨x.2, ?_⟩
    rw [cx, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact h2.symm
  · rintro ⟨-, hc⟩
    rw [cx, Subgroup.mem_centralizer_iff] at hc
    have h2 := hc d (Set.mem_singleton d)
    apply Subtype.ext
    rw [conjAutOf_apply]
    calc d⁻¹ * x.1 * d = d⁻¹ * (x.1 * d) := by group
      _ = d⁻¹ * (d * x.1) := by rw [h2]
      _ = x.1 := by group

end Field

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
