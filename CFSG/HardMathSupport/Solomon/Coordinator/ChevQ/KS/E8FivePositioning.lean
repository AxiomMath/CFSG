module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoMono
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.GroupTheory.ElemAbelianClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import CFSG.LieType.AlgebraicGroups.FiniteSubgroupConjugacyExtension
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoDich
public import CFSG.LocalAnalysis.StandardType.GGFinModelEps
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Mathlib.GroupTheory.NormalizerActionTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveFourLift
public import CFSG.RankThree.PartOne.KE8F.E8Frame

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace One

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess

abbrev PrimeFieldClosure : Type := AlgebraicClosure (ZMod 2)

theorem exists_finite_descent
    (E : Subgroup (adjointGroup Tag.E8 PrimeFieldClosure)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian 5 E)
    {ζ : PrimeFieldClosure} (hζ : IsPrimitiveRoot ζ 5) :
    ∃ (F : Subfield PrimeFieldClosure) (_ : Finite F) (ζF : F) (_ : IsPrimitiveRoot ζF 5)
      (E0 : Subgroup (adjointGroup Tag.E8 F)),
      CFSG.Open.IsElemAbelian 5 E0 ∧
      E0.map (adjointBaseChangeHom Tag.E8 F.subtype) = E ∧
      Nat.card E0 = Nat.card E := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  let Sx : E → Finset PrimeFieldClosure := fun x =>
    (exists_finset_descent (τ := Tag.E8) (k := PrimeFieldClosure)
      (x := (x : adjointGroup Tag.E8 PrimeFieldClosure))
      (x : adjointGroup Tag.E8 PrimeFieldClosure).2).choose
  have hSx : ∀ x : E, ∀ K : Subfield PrimeFieldClosure,
      (Sx x : Set PrimeFieldClosure) ⊆ K →
      ∃ y ∈ adjointGroup Tag.E8 K,
        baseChangeGL K.subtype y = (x : ModGL Tag.E8 PrimeFieldClosure) := by
    intro x K hK
    exact (exists_finset_descent (τ := Tag.E8) (k := PrimeFieldClosure)
      (x := (x : adjointGroup Tag.E8 PrimeFieldClosure))
      (x : adjointGroup Tag.E8 PrimeFieldClosure).2).choose_spec K hK
  let S : Finset PrimeFieldClosure := insert ζ (Finset.univ.biUnion Sx)
  obtain ⟨F, hFfin, hSF, -⟩ :=
    exists_finite_subfield_of_finset (K := ZMod 2) (L := PrimeFieldClosure) S
  have : Finite F := hFfin
  have hζF_mem : ζ ∈ F := hSF (Finset.mem_insert_self ζ _)
  let ζF : F := ⟨ζ, hζF_mem⟩
  have hζF : IsPrimitiveRoot ζF 5 :=
    IsPrimitiveRoot.of_map_of_injective (f := F.subtype) (by simpa [ζF] using hζ)
      F.subtype.injective
  have hSxF : ∀ x : E, (Sx x : Set PrimeFieldClosure) ⊆ F := by
    intro x y hy
    exact hSF (Finset.mem_insert_of_mem
      (Finset.subset_biUnion_of_mem Sx (Finset.mem_univ x) hy))
  let f : adjointGroup Tag.E8 F →* adjointGroup Tag.E8 PrimeFieldClosure :=
    adjointBaseChangeHom Tag.E8 F.subtype
  let E0 : Subgroup (adjointGroup Tag.E8 F) := E.comap f
  have hf : Function.Injective f := adjointBaseChangeHom_injective Tag.E8 F.subtype
  have hE0 : CFSG.Open.IsElemAbelian 5 E0 := CFSG.Open.IsElemAbelian.comap hE hf
  have hmap : E0.map f = E := by
    refine le_antisymm ?_ ?_
    · rintro e ⟨y, hy, rfl⟩
      exact hy
    · intro e he
      let x : E := ⟨e, he⟩
      obtain ⟨y, hy, hyeq⟩ := hSx x F (hSxF x)
      let eF : adjointGroup Tag.E8 F := ⟨y, hy⟩
      have hfe : f eF = e := by
        apply Subtype.ext
        exact hyeq
      refine ⟨eF, ?_, hfe⟩
      show f eF ∈ E
      rwa [hfe]
  have hcard : Nat.card E0 = Nat.card E := by
    rw [← Subgroup.card_map_of_injective (K := E0) (f := f) hf, hmap]
  refine ⟨F, hFfin, ζF, hζF, E0, hE0, ?_, hcard⟩
  exact hmap

theorem algebraicClosure_primeField_positioning
    (E : Subgroup (adjointGroup Tag.E8 PrimeFieldClosure)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian 5 E)
    {ζ : PrimeFieldClosure} (hζ : IsPrimitiveRoot ζ 5) :
    ∃ c : adjointGroup Tag.E8 PrimeFieldClosure, ∀ e ∈ E,
      (((c * e * c⁻¹ : adjointGroup Tag.E8 PrimeFieldClosure) :
          ModGL Tag.E8 PrimeFieldClosure) * griessZ hζ =
        griessZ hζ * ((c * e * c⁻¹ : adjointGroup Tag.E8 PrimeFieldClosure) :
          ModGL Tag.E8 PrimeFieldClosure)) := by
  classical
  obtain ⟨F, hFfin, ζF, hζF, E0, hE0, hmap, hcard⟩ :=
    exists_finite_descent E hE hζ
  have : Finite F := hFfin
  have : CharP F 2 := Subfield.charP F 2
  have h5F : 5 ∣ Nat.card F - 1 := by
    rw [← Nat.card_units (α := F)]
    let u : Fˣ := Units.mk0 ζF (hζF.ne_zero (by norm_num))
    have hu : IsPrimitiveRoot u 5 :=
      IsPrimitiveRoot.coe_units_iff.1 (by simpa [u] using hζF)
    refine (show 5 ∣ orderOf u from ?_).trans (orderOf_dvd_natCard u)
    rw [← hu.eq_orderOf]
  let f : adjointGroup Tag.E8 F →* adjointGroup Tag.E8 PrimeFieldClosure :=
    adjointBaseChangeHom Tag.E8 F.subtype
  change E0.map f = E at hmap
  have hmemE : ∀ e ∈ E, ∃ eF ∈ E0, f eF = e := by
    intro e he
    rw [← hmap] at he
    exact Subgroup.mem_map.1 he
  obtain ⟨cF, hcN, hcW⟩ := exists_conj_monomialN_weyl_le (K := F) h5F
    (CFSG.StandardType.TableB.isPGroup_of_isElemAbelian hE0)
  refine ⟨f cF, fun e he => ?_⟩
  obtain ⟨eF, heF, hfe⟩ := hmemE e he
  let mF : ModGL Tag.E8 F := ((cF * eF * cF⁻¹ : adjointGroup Tag.E8 F) : ModGL Tag.E8 F)
  have hmF : mF ∈ monomialSubgroup Tag.E8 F := hcN eF heF
  have hWF : weylQuotientHom Tag.E8 F ⟨mF, hmF⟩ ∈ sylowW := by
    simpa only [mF, rhoN_apply] using hcW eF heF
  have hcomm := Two.monomial_commute_z (K₂ := F) (L := PrimeFieldClosure) F.subtype
    hmF hWF (griessU_prim hζ)
  have hz : griessZ hζ =
      rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (griessU hζ)) := by
    rw [griessZ, Two.powVec_czVec]
  rw [hz]
  have hm : baseChangeGL F.subtype mF =
      ((f cF * e * (f cF)⁻¹ : adjointGroup Tag.E8 PrimeFieldClosure) :
        ModGL Tag.E8 PrimeFieldClosure) := by
    rw [← hfe]
    change ((f (cF * eF * cF⁻¹) : adjointGroup Tag.E8 PrimeFieldClosure) :
        ModGL Tag.E8 PrimeFieldClosure) = _
    rw [map_mul, map_mul, map_inv]
  rw [hm] at hcomm
  exact hcomm

end One

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.StandardType.ExcFramesHalf

theorem isToralSubgroup_map_conj_iff {τ : Tag} {L : Type} [Field L]
    {A : Subgroup (ModGL τ L)} {c : ModGL τ L} (hc : c ∈ adjointGroup τ L) :
    IsToralSubgroup τ L (A.map (MulAut.conj c).toMonoidHom) ↔
      IsToralSubgroup τ L A := by
  constructor
  · rintro ⟨h, hh, hhA⟩
    refine ⟨c⁻¹ * h, mul_mem (inv_mem hc) hh, fun a ha => ?_⟩
    have := hhA (c * a * c⁻¹) (Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom ha)
    have hEq : (c⁻¹ * h)⁻¹ * a * (c⁻¹ * h) =
        h⁻¹ * (c * a * c⁻¹) * h := by group
    rw [hEq]
    simpa only [MulAut.conj_apply] using this
  · rintro ⟨g, hg, hgA⟩
    refine ⟨c * g, mul_mem hc hg, ?_⟩
    rintro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    change (c * g)⁻¹ * (c * a * c⁻¹) * (c * g) ∈ torusGroup τ L
    have hEq : (c * g)⁻¹ * (c * a * c⁻¹) * (c * g) = g⁻¹ * a * g := by group
    rw [hEq]
    exact hgA a ha

theorem universal_positioning
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]
    (E : Subgroup (adjointGroup Tag.E8 L)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian 5 E) :
    ∃ (ζ : L) (hζ : IsPrimitiveRoot ζ 5) (c : adjointGroup Tag.E8 L), ∀ e ∈ E,
      (((c * e * c⁻¹ : adjointGroup Tag.E8 L) : ModGL Tag.E8 L) * griessZ hζ =
        griessZ hζ * ((c * e * c⁻¹ : adjointGroup Tag.E8 L) : ModGL Tag.E8 L)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Algebra (ZMod 2) L := ZMod.algebra L 2
  let k := AlgebraicClosure (ZMod 2)
  let ι : k →+* L := (IsAlgClosed.lift (R := ZMod 2) (S := k) (M := L)).toRingHom
  let : Algebra k L := ι.toAlgebra
  letI : Fintype E := Fintype.ofFinite E
  obtain ⟨ζkU, hζkU⟩ := CFSG.StandardType.GGFinModel.exists_zeta k Nat.prime_five (by norm_num)
  let ζk : k := ζkU
  have hζk : IsPrimitiveRoot ζk 5 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζkU)
  let ζL : L := ι ζk
  have hζL : IsPrimitiveRoot ζL 5 := hζk.map_of_injective (f := ι) ι.injective
  have hbase : ∀ f : E →* adjointGroup Tag.E8 k, Function.Injective f →
      ∃ g ∈ adjointGroup Tag.E8 k, ∀ a,
        (g * (f a : ModGL Tag.E8 k) * g⁻¹) * griessZ hζk =
          griessZ hζk * (g * (f a : ModGL Tag.E8 k) * g⁻¹) := by
    intro f hf
    have hErange : CFSG.Open.IsElemAbelian 5 f.range :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.2
        (CFSG.IsElementaryAbelian.of_mulEquiv (MonoidHom.ofInjective hf)
          hE.isElementaryAbelian)
    obtain ⟨g, hgcomm⟩ := One.algebraicClosure_primeField_positioning f.range hErange hζk
    refine ⟨g, g.2, fun a => ?_⟩
    exact hgcomm (f a) (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  have hzL : baseChangeGL ι (griessZ hζk) = griessZ hζL := by
    rw [griessZ, baseChangeGL_rootDiagUnit, griessZ]
    congr 1
    funext i
    rw [map_pow]
    congr 1
    apply Units.ext
    rfl
  obtain ⟨c, hc, hcomm⟩ :=
    CFSG.LieType.AlgebraicGroups.finite_subgroup_centralizer_field_extension
      (τ := Tag.E8) (Γ := E) (k := k) (L := L)
      (griessZ hζk) hbase E.subtype E.subtype_injective
  refine ⟨ζL, hζL, ⟨c, hc⟩, fun e he => ?_⟩
  have h := hcomm ⟨e, he⟩
  rw [show algebraMap k L = ι from rfl, hzL] at h
  simpa [Subgroup.subtype_apply] using h

theorem universal_nonToral_cube
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]
    (E : Subgroup (adjointGroup Tag.E8 L)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian 5 E)
    (hNT : ¬ IsToralSubgroup Tag.E8 L (E.map (adjointGroup Tag.E8 L).subtype))
    (hcard : 5 ^ 3 ≤ Nat.card E) :
    ∃ (ζ : L) (hζ : IsPrimitiveRoot ζ 5) (c : adjointGroup Tag.E8 L)
      (a b : ModGL Tag.E8 L),
      let A : Subgroup (ModGL Tag.E8 L) :=
        (E.map (adjointGroup Tag.E8 L).subtype).map
          (MulAut.conj (c : ModGL Tag.E8 L)).toMonoidHom
      A ≤ Two.mulSub L ∧ Two.CubeBasis (griessZ hζ) a b ∧
        Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) = A := by
  classical
  obtain ⟨ζ, hζ, c, hcomm⟩ := universal_positioning L E hE
  have h5L : (5 : L) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff L 2 5).1 h
    norm_num at this
  let A : Subgroup (ModGL Tag.E8 L) :=
    (E.map (adjointGroup Tag.E8 L).subtype).map
      (MulAut.conj (c : ModGL Tag.E8 L)).toMonoidHom
  have hA5 : CFSG.Open.IsElemAbelian 5 A :=
    (hE.map (adjointGroup Tag.E8 L).subtype).map
      (MulAut.conj (c : ModGL Tag.E8 L)).toMonoidHom
  have hA_nt : ¬ IsToralSubgroup Tag.E8 L A := by
    intro h
    exact hNT ((isToralSubgroup_map_conj_iff (A := E.map (adjointGroup Tag.E8 L).subtype)
      (c := (c : ModGL Tag.E8 L)) c.2).mp h)
  have hAmul : A ≤ Two.mulSub L := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hy
    refine Two.centralizer_le_mulSub hζ ?_ ?_
    · show ((c * e * c⁻¹ : adjointGroup Tag.E8 L) : ModGL Tag.E8 L) ∈ adjointGroup Tag.E8 L
      exact (c * e * c⁻¹).2
    · simpa [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply]
        using hcomm e he
  have hcardA : Nat.card A = Nat.card E := by
    rw [show A = (E.map (adjointGroup Tag.E8 L).subtype).map
      (MulAut.conj (c : ModGL Tag.E8 L)).toMonoidHom from rfl]
    rw [Subgroup.card_map_of_injective (MulAut.conj (c : ModGL Tag.E8 L)).injective,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective (adjointGroup Tag.E8 L))]
  have hcardAge : 5 ^ 3 ≤ Nat.card A := by
    rw [hcardA]
    exact hcard
  obtain ⟨a, ha, b, hb, hzA, hbasis, hcl⟩ :=
    Two.exists_z_cube_of_nontoral_le_mulSub (L := L) h5L hζ A hAmul hA5 hcardAge hA_nt
  exact ⟨ζ, hζ, c, a, b, hAmul, hbasis, hcl⟩

theorem universal_nonToral_centralizer_eq
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]
    (E : Subgroup (adjointGroup Tag.E8 L)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian 5 E)
    (hNT : ¬ IsToralSubgroup Tag.E8 L (E.map (adjointGroup Tag.E8 L).subtype))
    (hcard : 5 ^ 3 ≤ Nat.card E) :
    Subgroup.centralizer (E : Set (adjointGroup Tag.E8 L)) = E := by
  classical
  obtain ⟨ζ, hζ, c, a, b, hAmul, hbasis, hcl⟩ := universal_nonToral_cube L E hE hNT hcard
  let A : Subgroup (ModGL Tag.E8 L) :=
    (E.map (adjointGroup Tag.E8 L).subtype).map
      (MulAut.conj (c : ModGL Tag.E8 L)).toMonoidHom
  change A ≤ Two.mulSub L at hAmul
  change Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) = A at hcl
  have h5 : (5 : L) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff L 2 5).mp h
    norm_num at this
  have hANT : ¬ IsToralSubgroup Tag.E8 L A := by
    intro h
    exact hNT ((isToralSubgroup_map_conj_iff c.2).mp h)
  have haA : a ∈ A := hcl ▸ Subgroup.subset_closure (by simp)
  have hbA : b ∈ A := hcl ▸ Subgroup.subset_closure (by simp)
  have hCA : Subgroup.centralizer (A : Set (ModGL Tag.E8 L)) ⊓ adjointGroup Tag.E8 L = A := by
    rw [← hcl]
    exact Two.centralizer_nontoral_cube_eq h5 hζ hbasis (hAmul haA) (hAmul hbA)
      (by rw [hcl]; exact hANT)
  let f : adjointGroup Tag.E8 L →* ModGL Tag.E8 L :=
    (adjointGroup Tag.E8 L).subtype.comp (MulAut.conj c).toMonoidHom
  have hf : Function.Injective f :=
    (adjointGroup Tag.E8 L).subtype_injective.comp (MulAut.conj c).injective
  have hAf : E.map f = A := by
    dsimp only [A]
    rw [Subgroup.map_map]
    congr 1
  apply le_antisymm
  · intro g hg
    have hgC := Subgroup.mem_centralizer_iff.mp hg
    have hfgC : f g ∈ Subgroup.centralizer (A : Set (ModGL Tag.E8 L)) := by
      rw [← hAf]
      apply Subgroup.mem_centralizer_iff.mpr
      rintro x ⟨e, he, rfl⟩
      rw [← map_mul, hgC e he, map_mul]
    have hfgAd : f g ∈ adjointGroup Tag.E8 L := (c * g * c⁻¹).2
    have hfgA : f g ∈ A := hCA ▸ ⟨hfgC, hfgAd⟩
    rw [← hAf] at hfgA
    obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp hfgA
    exact hf heq ▸ he
  · intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro e he
    exact congrArg (fun x : E => (x : adjointGroup Tag.E8 L))
      (hE.1.is_comm.comm ⟨e, he⟩ ⟨g, hg⟩)

theorem centralizer_eq_of_nonToral_baseChange
    {K L : Type} [Field K] [Field L] [IsAlgClosed L] [CharP L 2]
    (f : K →+* L) (E : Subgroup (adjointGroup Tag.E8 K)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian 5 E)
    (hNT : ¬ IsToralSubgroup Tag.E8 L
      (E.map ((baseChangeGL f).comp (adjointGroup Tag.E8 K).subtype)))
    (hcard : 5 ^ 3 ≤ Nat.card E) :
    Subgroup.centralizer (E : Set (adjointGroup Tag.E8 K)) = E := by
  classical
  let ι : adjointGroup Tag.E8 K →* adjointGroup Tag.E8 L :=
    ((baseChangeGL f).comp (adjointGroup Tag.E8 K).subtype).codRestrict _
      (fun g => baseChangeGL_mem_adjointGroup f g.2)
  have hι : Function.Injective ι := by
    intro x y h
    apply Subtype.ext
    exact baseChangeGL_injective f (congrArg Subtype.val h)
  let A : Subgroup (adjointGroup Tag.E8 L) := E.map ι
  letI : Finite A := Finite.of_equiv E (E.equivMapOfInjective ι hι).toEquiv
  have hιcomp : (adjointGroup Tag.E8 L).subtype.comp ι =
      (baseChangeGL f).comp (adjointGroup Tag.E8 K).subtype := by
    ext g
    rfl
  have hANT : ¬ IsToralSubgroup Tag.E8 L (A.map (adjointGroup Tag.E8 L).subtype) := by
    simpa only [A, Subgroup.map_map, hιcomp] using hNT
  have hAcard : 5 ^ 3 ≤ Nat.card A := by
    rwa [show Nat.card A = Nat.card E from Subgroup.card_map_of_injective hι]
  have hC := universal_nonToral_centralizer_eq L A (hE.map ι) hANT hAcard
  apply le_antisymm
  · intro x hx
    have hxL : ι x ∈ Subgroup.centralizer (A : Set (adjointGroup Tag.E8 L)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨e, he, rfl⟩
      rw [← map_mul, Subgroup.mem_centralizer_iff.mp hx e he, map_mul]
    have hxA : ι x ∈ A := hC ▸ hxL
    obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp hxA
    exact hι heq ▸ he
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    exact fun e he => hE.comm he hx

section PerfectNormalizerTransfer

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem universal_perfect_normalizer_transfer
    (hgeom : ∀ (F : Subgroup (adjointGroup Tag.E8 L)) [Finite F],
      CFSG.Open.IsElemAbelian 5 F →
      ¬ IsToralSubgroup Tag.E8 L (F.map (adjointGroup Tag.E8 L).subtype) →
      ∀ {ζ : L} (hζ : IsPrimitiveRoot ζ 5) {a b : ModGL Tag.E8 L},
        F.map (adjointGroup Tag.E8 L).subtype ≤ Two.mulSub L →
        Two.CubeBasis (griessZ hζ) a b →
        Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) =
          F.map (adjointGroup Tag.E8 L).subtype →
        Group.IsPerfect F.normalizerMonoidHom.range)
    (E : Subgroup (adjointGroup Tag.E8 L)) [Finite E]
    (hE : CFSG.Open.IsElemAbelian 5 E)
    (hNT : ¬ IsToralSubgroup Tag.E8 L (E.map (adjointGroup Tag.E8 L).subtype))
    (hcard : 5 ^ 3 ≤ Nat.card E) :
    Group.IsPerfect E.normalizerMonoidHom.range := by
  classical
  obtain ⟨ζ, hζ, c, a, b, hAmul, hbasis, hcl⟩ :=
    universal_nonToral_cube L E hE hNT hcard
  let A : Subgroup (ModGL Tag.E8 L) :=
    (E.map (adjointGroup Tag.E8 L).subtype).map
      (MulAut.conj (c : ModGL Tag.E8 L)).toMonoidHom
  let F : Subgroup (adjointGroup Tag.E8 L) :=
    E.map (MulAut.conj c).toMonoidHom
  have hFmap : F.map (adjointGroup Tag.E8 L).subtype = A := by
    dsimp only [F, A]
    rw [Subgroup.map_map, Subgroup.map_map]
    apply le_antisymm
    · rintro x ⟨e, he, rfl⟩
      exact Subgroup.mem_map_of_mem _ he
    · rintro x ⟨e, he, rfl⟩
      exact Subgroup.mem_map_of_mem _ he
  have hFsurj : Function.Surjective (fun x : E =>
      (⟨(MulAut.conj c) x, Subgroup.mem_map_of_mem _ x.2⟩ : F)) := by
    intro y
    rcases y with ⟨y, hy⟩
    change y ∈ E.map (MulAut.conj c).toMonoidHom at hy
    rcases Subgroup.mem_map.1 hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxy
  haveI : Finite F := Finite.of_surjective _ hFsurj
  have hF5 : CFSG.Open.IsElemAbelian 5 F := by
    dsimp only [F]
    exact CFSG.Open.IsElemAbelian.map hE (MulAut.conj c).toMonoidHom
  have hA_nt : ¬ IsToralSubgroup Tag.E8 L A := by
    intro h
    exact hNT ((isToralSubgroup_map_conj_iff (A := E.map (adjointGroup Tag.E8 L).subtype)
      (c := (c : ModGL Tag.E8 L)) c.2).mp h)
  have hFnt : ¬ IsToralSubgroup Tag.E8 L (F.map (adjointGroup Tag.E8 L).subtype) := by
    rwa [hFmap]
  have hAmul' : F.map (adjointGroup Tag.E8 L).subtype ≤ Two.mulSub L := by
    rwa [hFmap]
  have hcl' : Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)) =
      F.map (adjointGroup Tag.E8 L).subtype := by
    rwa [hFmap]
  have hFperf : Group.IsPerfect F.normalizerMonoidHom.range :=
    hgeom F hF5 hFnt hζ hAmul' hbasis hcl'
  have hiff := CFSG.GroupTheory.isPerfect_normalizerRange_iff E (MulAut.conj c)
  exact hiff.mpr (by simpa only [F] using hFperf)

end PerfectNormalizerTransfer

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
