module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

private lemma fiberLe_centerOf_eq_map_center {C : Type*} [Group C] (Q : Subgroup C) :
    centerOf Q = (Subgroup.center ↥Q).map Q.subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) y y.2)
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)

private lemma fiberLe_conj_mem_centerOf {C : Type*} [Group C] {Q : Subgroup C} [Q.Normal]
    {x : C} (hx : x ∈ centerOf Q) (t : C) : t * x * t⁻¹ ∈ centerOf Q := by
  obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨Subgroup.Normal.conj_mem inferInstance x hxQ t, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hxc ⊢
  intro h hh
  have hh' : t⁻¹ * h * t ∈ Q := by
    have := Subgroup.Normal.conj_mem (inferInstance : Q.Normal) h hh t⁻¹
    simpa using this
  have h1 := hxc _ hh'
  calc h * (t * x * t⁻¹) = t * ((t⁻¹ * h * t) * x) * t⁻¹ := by group
    _ = t * (x * (t⁻¹ * h * t)) * t⁻¹ := by rw [h1]
    _ = (t * x * t⁻¹) * h := by group

private lemma fiberLe_sq_mem_centerOf {C : Type*} [Group C] {Q : Subgroup C}
    (hQ : IsPlusExtraspecial 4 Q) {q : C} (hq : q ∈ Q) : q ^ 2 ∈ centerOf Q := by
  have hExt : CFSG.IsExtraspecial 2 ↥Q := hQ.1
  haveI : CFSG.IsElementaryAbelian 2 (↥Q ⧸ Subgroup.center ↥Q) :=
    hExt.quotient_elementary_abelian
  have hexp : ∀ g : (↥Q ⧸ Subgroup.center ↥Q), g ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 (↥Q ⧸ Subgroup.center ↥Q))
  have hq2 : (⟨q, hq⟩ : ↥Q) ^ 2 ∈ Subgroup.center ↥Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hexp (⟨q, hq⟩ : ↥Q)
  rw [fiberLe_centerOf_eq_map_center]
  exact Subgroup.mem_map.mpr ⟨(⟨q, hq⟩ : ↥Q) ^ 2, hq2, by simp⟩

private lemma fiberLe_fiber_mem {C : Type*} [Group C] (Q : Subgroup C) [Q.Normal]
    (hQ : IsPlusExtraspecial 4 Q) {c s : C} (hc2 : c ^ 2 = 1)
    (hs : ∃ k : C, k * c * k⁻¹ = s) (hcos : (s : C ⧸ Q) = (c : C ⧸ Q)) :
    c⁻¹ * s ∈ Q ∧ ⁅c⁻¹ * s, c⁆ ∈ centerOf Q := by
  obtain ⟨k, rfl⟩ := hs
  have hcc : c * c = 1 := by rwa [pow_two] at hc2
  have hs2 : (k * c * k⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    calc k * c * k⁻¹ * (k * c * k⁻¹) = k * (c * c) * k⁻¹ := by group
      _ = 1 := by rw [hcc]; group
  set q : C := c⁻¹ * (k * c * k⁻¹) with hqdef
  have hqQ : q ∈ Q := by
    have h1 : (q : C ⧸ Q) = 1 := by
      rw [hqdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcos, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff q).mp h1
  have hq2 : q ^ 2 ∈ centerOf Q := fiberLe_sq_mem_centerOf hQ hqQ
  have hcq : c * q = k * c * k⁻¹ := by rw [hqdef]; group
  have hcq2 : (c * q) ^ 2 = 1 := by rw [hcq]; exact hs2
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have h2 : c * q * c = q⁻¹ := by
    have h : c * q * c * q = 1 := by
      calc c * q * c * q = (c * q) ^ 2 := by rw [pow_two]; group
        _ = 1 := hcq2
    calc c * q * c = c * q * c * q * q⁻¹ := by group
      _ = 1 * q⁻¹ := by rw [h]
      _ = q⁻¹ := by group
  have hcqc : c * q * c⁻¹ = q⁻¹ := by rw [hc_inv]; exact h2
  have hqinv : c * q⁻¹ * c⁻¹ = q := by
    have h1 : (c * q * c⁻¹)⁻¹ = c * q⁻¹ * c⁻¹ := by group
    rw [← h1, hcqc, inv_inv]
  have hcomm : ⁅q, c⁆ = q ^ 2 := by
    calc ⁅q, c⁆ = q * (c * q⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
      _ = q * q := by rw [hqinv]
      _ = q ^ 2 := by rw [pow_two]
  exact ⟨hqQ, hcomm ▸ hq2⟩

theorem card_fiber_lt {C : Type} [Group C] [Finite C] (Q : Subgroup C) [Q.Normal]
    (hQ : IsPlusExtraspecial 4 Q) {c ζ : C} (hc2 : c ^ 2 = 1) (hζ : ζ ∈ centerOf Q)
    (hne : ∀ k : C, k * c * k⁻¹ ≠ c * ζ) :
    Nat.card {s : C // (∃ k : C, k * c * k⁻¹ = s) ∧ (s : C ⧸ Q) = (c : C ⧸ Q)} <
      Nat.card {q : C // q ∈ Q ∧ ⁅q, c⁆ ∈ centerOf Q} := by
  let F : Type := {s : C // (∃ k : C, k * c * k⁻¹ = s) ∧ (s : C ⧸ Q) = (c : C ⧸ Q)}
  let W : Type := {q : C // q ∈ Q ∧ ⁅q, c⁆ ∈ centerOf Q}
  let f : F → W := fun s => ⟨c⁻¹ * (s : C), fiberLe_fiber_mem Q hQ hc2 s.2.1 s.2.2⟩
  have hf : Function.Injective f := by
    intro s t h
    have h' : c⁻¹ * (s : C) = c⁻¹ * (t : C) := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel h')
  have hζQ : ζ ∈ Q := (Subgroup.mem_inf.mp hζ).1
  have hζW : ζ ∈ Q ∧ ⁅ζ, c⁆ ∈ centerOf Q := by
    refine ⟨hζQ, ?_⟩
    have hkey : ⁅ζ, c⁆ = ζ * (c * ζ⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
    rw [hkey]
    exact (centerOf Q).mul_mem hζ ((fiberLe_conj_mem_centerOf ((centerOf Q).inv_mem hζ)) c)
  let ζW : W := ⟨ζ, hζW⟩
  have hnotmem : ζW ∉ Set.range f := by
    rintro ⟨s, hs⟩
    have hval : c⁻¹ * (s : C) = ζ := congrArg Subtype.val hs
    have hs_eq : (s : C) = c * ζ := by rw [← hval]; group
    obtain ⟨k, hk⟩ := s.2.1
    exact hne k (by rw [hk, hs_eq])
  have hne_univ : Set.range f ≠ Set.univ := by
    intro h
    apply hnotmem
    rw [h]
    exact Set.mem_univ ζW
  have hlt : (Set.range f).ncard < Nat.card W := Set.ncard_lt_card hne_univ
  have hfin : (Set.range f).ncard = Nat.card F := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hf, Set.ncard_univ]
  rw [hfin] at hlt
  exact hlt

end CFSG.EvenSporadicStandard.HNRecog.Section3
