module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {A G : Type} [Group A] [Group G]

theorem isElemTwo_map_of_injective {f : A →* G} (hf : Function.Injective f) {n : ℕ} {E : Subgroup A}
    (h : IsElemTwo n E) : IsElemTwo n (E.map f) := by
  obtain ⟨hEab, hcard⟩ := h
  obtain ⟨hcomm, hexp⟩ := hEab
  haveI : IsMulCommutative ↥E := hcomm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine isMulCommutative_iff.mpr fun a b => ?_
    obtain ⟨xa, hxa, hax⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨xb, hxb, hbx⟩ := Subgroup.mem_map.1 b.2
    have hcommE : (⟨xa, hxa⟩ : ↥E) * (⟨xb, hxb⟩ : ↥E) =
        (⟨xb, hxb⟩ : ↥E) * (⟨xa, hxa⟩ : ↥E) :=
      mul_comm' (M := ↥E) ⟨xa, hxa⟩ ⟨xb, hxb⟩
    apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    rw [← hax, ← hbx, ← map_mul, ← map_mul]
    exact congrArg (fun z : ↥E => f (z : A)) hcommE
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hexp x hx, map_one]
  · rw [Subgroup.card_map_of_injective hf, hcard]

theorem QuotShape.map {f : A →* G} (hf : Function.Injective f) {M N : Subgroup A} {P : Type*}
    [Group P] (h : QuotShape M N P) : QuotShape (M.map f) (N.map f) P := by
  obtain ⟨hn, ⟨φ⟩⟩ := h
  haveI := hn
  let e : ↥M ≃* ↥(M.map f) := Subgroup.equivMapOfInjective M f hf
  have hclaim : (N.subgroupOf M).map e.toMonoidHom = (N.map f).subgroupOf (M.map f) := by
    ext y
    constructor
    · intro hy
      obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.1 hy
      have hmN : (m : A) ∈ N := Subgroup.mem_subgroupOf.1 hm
      rw [Subgroup.mem_subgroupOf, ← hmy]
      exact Subgroup.mem_map_of_mem f hmN
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      obtain ⟨n, hnN, hny⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [Subgroup.mem_subgroupOf]
      have hfn : f (e.symm y : A) = (y : G) := by
        have h2 : (e (e.symm y) : G) = f (e.symm y : A) := rfl
        rw [← h2]
        exact congrArg Subtype.val (e.apply_symm_apply y)
      have : (e.symm y : A) = n := hf (hfn.trans hny.symm)
      rwa [this]
  have hNnorm : ((N.map f).subgroupOf (M.map f)).Normal :=
    hclaim ▸ Subgroup.Normal.map hn e.toMonoidHom e.surjective
  haveI := hNnorm
  exact ⟨hNnorm, ⟨(QuotientGroup.congr (N.subgroupOf M)
    ((N.map f).subgroupOf (M.map f)) e hclaim).symm.trans φ⟩⟩

private theorem isPlusExtraspecial_map_mulEquiv {m : ℕ} {Γ Γ' : Type*} [Group Γ] [Group Γ']
    (e : Γ ≃* Γ') {D : Subgroup Γ} (h : IsPlusExtraspecial m D) :
    IsPlusExtraspecial m (D.map e.toMonoidHom) := by
  obtain ⟨hExt, hcard, E, hED, hEel, hEcard⟩ := h
  refine ⟨TwoHSData.isExtraspecial_of_mulEquiv (e.subgroupMap D) hExt, ?_,
    E.map e.toMonoidHom, Subgroup.map_mono hED, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · haveI : IsMulCommutative ↥E := hEel.1
    exact ⟨inferInstance, fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hEel.2 y hy, map_one]⟩
  · rw [Subgroup.card_map_of_injective e.injective, hEcard]

theorem IsShapeZ2Z4StarExtra.of_mulEquiv {N N' : Type*} [Group N] [Group N'] (e : N ≃* N')
    (h : IsShapeZ2Z4StarExtra N) : IsShapeZ2Z4StarExtra N' := by
  obtain ⟨hp, hcard, ⟨hcen⟩, Q, hQ, hQsup, hQcard⟩ := h
  let Q' : Subgroup N' := Q.map e.toMonoidHom
  have hmap_center : (Subgroup.center N).map e.toMonoidHom = Subgroup.center N' := by
    apply le_antisymm
    · exact Subgroup.map_center_le_center (f := (e : N →* N')) e.surjective
    · rintro x hx
      obtain ⟨y, rfl⟩ := e.surjective x
      refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro z
      apply e.injective
      rw [map_mul, map_mul]
      exact hx (e z)
  refine ⟨hp.of_equiv e, (Nat.card_congr e.toEquiv).symm.trans hcard,
    ⟨(Subgroup.centerCongr e).symm.trans hcen⟩, Q',
    isPlusExtraspecial_map_mulEquiv e hQ, ?_, ?_⟩
  · have hh := congrArg (Subgroup.map e.toMonoidHom) hQsup
    rw [Subgroup.map_sup, hmap_center,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hh
    exact hh
  · have hinf : (Subgroup.center N ⊓ Q).map e.toMonoidHom = Subgroup.center N' ⊓ Q' := by
      rw [Subgroup.map_inf_eq (Subgroup.center N) Q e.toMonoidHom e.injective, hmap_center]
    rw [← hinf, Subgroup.card_map_of_injective e.injective, hQcard]

theorem IsShapeZ2Z4StarExtra.map {f : A →* G} (hf : Function.Injective f) {N : Subgroup A}
    (h : IsShapeZ2Z4StarExtra ↥N) : IsShapeZ2Z4StarExtra ↥(N.map f) := by
  exact IsShapeZ2Z4StarExtra.of_mulEquiv (Subgroup.equivMapOfInjective N f hf) h

end CFSG.EvenSporadicStandard.HNRecog.Section3
