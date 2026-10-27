module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Quasi
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section K

variable {Y : Type*} [Group Y] (K : Subgroup Y)

@[expose] def i253α (a : Y) (ha : a ∈ Subgroup.normalizer (K : Set Y)) : MulAut ↥K :=
  K.normalizerMonoidHom ⟨a, ha⟩

theorem i253α_coe (a : Y) (ha : a ∈ Subgroup.normalizer (K : Set Y)) (x : ↥K) :
    ((i253α K a ha x : ↥K) : Y) = a * x * a⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem mem_fixSubgroup_i253α (a : Y) (ha : a ∈ Subgroup.normalizer (K : Set Y)) (x : ↥K) :
    x ∈ fixSubgroup (i253α K a ha) ↔ a * (x : Y) = (x : Y) * a := by
  rw [mem_fixSubgroup]
  constructor
  · intro h
    have := congrArg Subtype.val h
    rw [i253α_coe] at this
    calc a * (x : Y) = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [this]
  · intro h
    apply Subtype.ext
    rw [i253α_coe]
    calc a * (x : Y) * a⁻¹ = (x : Y) * a * a⁻¹ := by rw [h]
      _ = x := by group

theorem map_fixSubgroup_i253α (a : Y) (ha : a ∈ Subgroup.normalizer (K : Set Y)) :
    (fixSubgroup (i253α K a ha)).map K.subtype = K ⊓ Subgroup.centralizer ({a} : Set Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    show (x : Y) ∈ Subgroup.centralizer ({a} : Set Y)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((mem_fixSubgroup_i253α K a ha x).1 hx).symm
  · rintro ⟨hyK, hy⟩
    have hy' : y ∈ Subgroup.centralizer ({a} : Set Y) := hy
    refine ⟨⟨y, hyK⟩, ?_, rfl⟩
    show (⟨y, hyK⟩ : ↥K) ∈ fixSubgroup (i253α K a ha)
    rw [mem_fixSubgroup_i253α]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hy').symm

theorem i253α_pow_three (a : Y) (ha : a ∈ Subgroup.normalizer (K : Set Y)) (ha3 : a ^ 3 = 1) :
    i253α K a ha ^ 3 = 1 := by
  have h : (⟨a, ha⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  unfold i253α
  rw [← map_pow, h, map_one]

theorem mem_centralizer_zpowers_iff (x y : Y) :
    x ∈ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup Y) : Set Y) ↔ y * x = x * y := by
  constructor
  · intro h
    exact (Subgroup.mem_centralizer_iff.1 h) y (Subgroup.mem_zpowers y)
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ((Commute.zpow_left (show Commute y x from h) n).eq)

theorem i253_isQuasisimple_map {G H : Type*} [Group G] [Group H] (ι : G →* H)
    (hι : Function.Injective ι) {T : Subgroup G} (hT : CFSG.Open.IsQuasisimple ↥T) :
    CFSG.Open.IsQuasisimple ↥(T.map ι) := by
  let e : ↥T ≃* ↥(T.map ι) := T.equivMapOfInjective ι hι
  refine i253_isQuasisimple_of_surj hT e.toMonoidHom e.surjective ?_
  intro x hx
  have : x = 1 := e.injective (by simpa using hx)
  simp [this]

end K

end CFSG.HardMathSupport.Solomon.Coordinator
