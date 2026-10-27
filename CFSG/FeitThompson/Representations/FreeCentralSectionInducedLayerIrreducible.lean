module

public import CFSG.FeitThompson.Representations.NormalRestrictionSingleConstituentOrbit
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.Definitions.CoreDetectingNormalInducedFamily
public import CFSG.FeitThompson.Representations.FreeCentralSectionTISylowRestriction
public import CFSG.FeitThompson.Representations.CentralScalarInductionDegreeSum
import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.NormalInductionPreservesKernelSubgroup
import CFSG.FeitThompson.Representations.CentralSubgroupBoundsDegreeSquare
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Subgroup
open NormalInduction (conjClassFun conjClassFun_apply)

section Centre

variable {Q : Type*} [Group Q] [Finite Q] {θ : Q → ℂ}

theorem apply_ne_zero_of_mem_center (hθ : θ ∈ Irr Q) {y : Q} (hy : y ∈ center Q) : θ y ≠ 0 := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hθ
  have hirr : Representation.IsIrreducible W.ρ := hW
  have h1 : ‖FDRep.character W y‖ = (finrank ℂ (W.V : Type) : ℝ) := by
    rw [fdRepCharacter_eq]
    exact Representation.norm_character_eq_finrank_of_mem_center W.ρ hy
  have hpos : 0 < finrank ℂ (W.V : Type) :=
    haveI : Nontrivial (W.V : Type) := Representation.nontrivial_of_isIrreducible W.ρ hirr
    finrank_pos
  intro h0
  rw [h0, norm_zero] at h1
  have hz : finrank ℂ (W.V : Type) = 0 := by exact_mod_cast h1.symm
  omega

end Centre

section CentralLinearChar

variable {Q : Type*} [Group Q] [Finite Q] {θ : Q → ℂ} {A : Subgroup Q}

theorem centralLinearChar_ne_zero (hθ : θ ∈ Irr Q) (hA : A ≤ center Q) (z : A) :
    centralLinearChar hθ hA z ≠ 0 := by
  rw [centralLinearChar_apply]
  exact div_ne_zero (apply_ne_zero_of_mem_center hθ (hA z.2)) (apply_one_ne_zero_of_mem_Irr hθ)

theorem centralLinearChar_eq_one_iff (hθ : θ ∈ Irr Q) (hA : A ≤ center Q) :
    (∀ z : A, centralLinearChar hθ hA z = 1) ↔ (A : Set Q) ⊆ charValueKernel θ := by
  have h := centralLinearChar_ne_one_iff hθ hA
  rw [not_iff_not, funext_iff] at h
  simpa using h

end CentralLinearChar

theorem surjective_mul_inv_apply_of_fixedPointFree {A : Type*} [Group A] [Finite A] (α : A ≃* A)
    (hα : ∀ z : A, α z = z → z = 1) : Function.Surjective fun z : A => z * (α z)⁻¹ := by
  refine Finite.surjective_of_injective fun y z hyz => ?_
  have hyz' : y * (α y)⁻¹ = z * (α z)⁻¹ := hyz
  have hw : α (z⁻¹ * y) = z⁻¹ * y := by
    have h : z⁻¹ * y = (α z)⁻¹ * α y := by
      calc z⁻¹ * y = z⁻¹ * (y * (α y)⁻¹) * α y := by group
        _ = z⁻¹ * (z * (α z)⁻¹) * α y := by rw [hyz']
        _ = (α z)⁻¹ * α y := by group
    rw [map_mul, map_inv, h]
  exact (inv_mul_eq_one.1 (hα _ hw)).symm

theorem subset_charValueKernel_of_invariant_of_fixedPointFree {Q : Type*} [Group Q] [Finite Q]
    {θ : Q → ℂ} {A : Subgroup Q} (hθ : θ ∈ Irr Q) (hA : A ≤ center Q) (α : A ≃* A)
    (hα : ∀ z : A, α z = z → z = 1) (hinv : ∀ z : A, θ ((α z : A) : Q) = θ (z : Q)) :
    (A : Set Q) ⊆ charValueKernel θ := by
  refine (centralLinearChar_eq_one_iff hθ hA).1 fun w => ?_
  obtain ⟨z, rfl⟩ := surjective_mul_inv_apply_of_fixedPointFree α hα w
  have hlamα : centralLinearChar hθ hA (α z) = centralLinearChar hθ hA z := by
    rw [centralLinearChar_apply, centralLinearChar_apply, hinv]
  rw [map_mul, map_inv, hlamα, mul_inv_cancel₀ (centralLinearChar_ne_zero hθ hA z)]

theorem subset_charValueKernel_of_conj_invariant {Q : Type*} [Group Q] [Finite Q] {θ : Q → ℂ}
    {A : Subgroup Q} (hθ : θ ∈ Irr Q) (hA : A ≤ center Q) {u : Q}
    (hmaps : ∀ z ∈ A, u⁻¹ * z * u ∈ A) (hfree : ∀ z ∈ A, u * z = z * u → z = 1)
    (hinv : ∀ z ∈ A, θ (u⁻¹ * z * u) = θ z) : (A : Set Q) ⊆ charValueKernel θ := by
  set f : A →* A :=
    { toFun := fun z => ⟨u⁻¹ * (z : Q) * u, hmaps (z : Q) z.2⟩
      map_one' := by refine Subtype.ext ?_; simp
      map_mul' := fun y z => by refine Subtype.ext ?_; push_cast; group } with hf
  have hfval : ∀ z : A, ((f z : A) : Q) = u⁻¹ * (z : Q) * u := fun z => rfl
  have hinj : Function.Injective f := by
    intro y z hyz
    have hval := congrArg (fun w : A => ((w : A) : Q)) hyz
    simp only [hfval] at hval
    refine Subtype.ext ?_
    have h2 : u⁻¹ * (y : Q) * u = u⁻¹ * (z : Q) * u := hval
    calc (y : Q) = u * (u⁻¹ * (y : Q) * u) * u⁻¹ := by group
      _ = u * (u⁻¹ * (z : Q) * u) * u⁻¹ := by rw [h2]
      _ = (z : Q) := by group
  set α : A ≃* A := MulEquiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩ with hα
  have hαval : ∀ z : A, ((α z : A) : Q) = u⁻¹ * (z : Q) * u := fun z => rfl
  refine subset_charValueKernel_of_invariant_of_fixedPointFree hθ hA α ?_ ?_
  · intro z hz
    have hzc : u⁻¹ * (z : Q) * u = (z : Q) := by rw [← hαval z, hz]
    refine Subtype.ext (hfree (z : Q) z.2 ?_)
    calc u * (z : Q) = u * (u⁻¹ * (z : Q) * u) := by rw [hzc]
      _ = (z : Q) * u := by group
  · intro z
    rw [hαval z]
    exact hinv (z : Q) z.2

section Stabilizer

variable {L : Type*} [Group L] {P Z : Subgroup L}

theorem subgroupOf_le_center (hZc : Z ≤ centralizer (P : Set L)) :
    Z.subgroupOf P ≤ center P := by
  intro x hx
  refine mem_center_iff.2 fun g => Subtype.ext ?_
  push_cast
  exact (mem_centralizer_iff.1 (hZc hx)) _ g.2

variable [P.Normal] [Z.Normal]

theorem conjClassFun_ne_of_free [Finite L] (hZc : Z ≤ centralizer (P : Set L))
    {θ : ↥P → ℂ} (hθ : θ ∈ Irr ↥P)
    (hker : ¬ ((Z.subgroupOf P : Subgroup ↥P) : Set ↥P) ⊆ charValueKernel θ) {u : L}
    (hfree : ∀ z ∈ Z, u * z = z * u → z = 1) : conjClassFun P u θ ≠ θ := by
  intro hcon
  refine hker ?_
  have hmapsP : ∀ v : ↥P, ((u⁻¹ * (v : L) * u : L)) ∈ P := fun v => by
    simpa using Subgroup.Normal.conj_mem ‹P.Normal› (v : L) v.2 u⁻¹
  have hmapsZ : ∀ z : ↥(Z.subgroupOf P), ((u⁻¹ * ((z : ↥P) : L) * u : L)) ∈ Z := by
    intro z
    have hz : (((z : ↥P) : L)) ∈ Z := z.2
    simpa using Subgroup.Normal.conj_mem ‹Z.Normal› _ hz u⁻¹
  set f : ↥(Z.subgroupOf P) →* ↥(Z.subgroupOf P) :=
    { toFun := fun z => ⟨⟨u⁻¹ * ((z : ↥P) : L) * u, hmapsP _⟩, hmapsZ z⟩
      map_one' := by refine Subtype.ext (Subtype.ext ?_); simp
      map_mul' := fun y z => by refine Subtype.ext (Subtype.ext ?_); push_cast; group } with hf
  have hfval : ∀ z : ↥(Z.subgroupOf P), (((f z : ↥(Z.subgroupOf P)) : ↥P) : L)
      = u⁻¹ * ((z : ↥P) : L) * u := fun z => rfl
  have hinj : Function.Injective f := by
    intro y z hyz
    have hval : u⁻¹ * ((y : ↥P) : L) * u = u⁻¹ * ((z : ↥P) : L) * u := by
      rw [← hfval y, ← hfval z, hyz]
    refine Subtype.ext (Subtype.ext ?_)
    calc (((y : ↥P) : L)) = u * (u⁻¹ * ((y : ↥P) : L) * u) * u⁻¹ := by group
      _ = u * (u⁻¹ * ((z : ↥P) : L) * u) * u⁻¹ := by rw [hval]
      _ = ((z : ↥P) : L) := by group
  set α : ↥(Z.subgroupOf P) ≃* ↥(Z.subgroupOf P) :=
    MulEquiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩ with hαdef
  have hαval : ∀ z : ↥(Z.subgroupOf P), (((α z : ↥(Z.subgroupOf P)) : ↥P) : L)
      = u⁻¹ * ((z : ↥P) : L) * u := fun z => rfl
  refine subset_charValueKernel_of_invariant_of_fixedPointFree hθ
    (subgroupOf_le_center hZc) α ?_ ?_
  · intro z hz
    have hzc : u⁻¹ * ((z : ↥P) : L) * u = ((z : ↥P) : L) := by rw [← hαval z, hz]
    refine Subtype.ext (Subtype.ext (hfree _ z.2 ?_))
    calc u * ((z : ↥P) : L) = u * (u⁻¹ * ((z : ↥P) : L) * u) := by rw [hzc]
      _ = ((z : ↥P) : L) * u := by group
  · intro z
    have h2 : θ (MulAut.conjNormal (u⁻¹) ((z : ↥P))) = θ ((z : ↥P)) := by
      have hz := congrFun hcon (z : ↥P)
      rwa [conjClassFun_apply] at hz
    have heq : ((α z : ↥(Z.subgroupOf P)) : ↥P) = MulAut.conjNormal (u⁻¹) ((z : ↥P)) := by
      refine Subtype.ext ?_
      rw [hαval z, MulAut.conjNormal_apply]
      group
    rw [heq]
    exact h2

theorem conjClassFun_ne_of_free_of_exists [Finite L] (hZc : Z ≤ centralizer (P : Set L))
    {θ : ↥P → ℂ} (hθ : θ ∈ Irr ↥P) (hker : ∃ x : ↥P, (x : L) ∈ Z ∧ θ x ≠ θ 1) {u : L}
    (hfree : ∀ z ∈ Z, u * z = z * u → z = 1) : conjClassFun P u θ ≠ θ := by
  refine conjClassFun_ne_of_free hZc hθ ?_ hfree
  obtain ⟨x, hxZ, hx⟩ := hker
  intro hsub
  exact hx (mem_charValueKernel.1 (hsub (show x ∈ Z.subgroupOf P from hxZ)))

variable {E : Subgroup L}

theorem inertiaGroup_eq [Finite L] (hZc : Z ≤ centralizer (P : Set L)) (hPE : P ⊔ E = ⊤)
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1)
    {θ : ↥P → ℂ} (hθ : θ ∈ Irr ↥P)
    (hker : ¬ ((Z.subgroupOf P : Subgroup ↥P) : Set ↥P) ⊆ charValueKernel θ) :
    inertiaGroup P θ = P := by
  refine le_antisymm ?_ (le_inertiaGroup P (Irr_subset_classFun hθ))
  intro g hg
  have hgtop : g ∈ ((P ⊔ E : Subgroup L) : Set L) := by rw [hPE]; trivial
  rw [Subgroup.normal_mul] at hgtop
  obtain ⟨x, hx, u, hu, hxu⟩ := hgtop
  have hxP : x ∈ P := hx
  have huE : u ∈ E := hu
  have hgeq : g = x * u := hxu.symm
  subst hgeq
  have hxI : x ∈ inertiaGroup P θ := le_inertiaGroup P (Irr_subset_classFun hθ) hxP
  have huI : u ∈ inertiaGroup P θ := by
    have hm := (inertiaGroup P θ).mul_mem (inv_mem hxI) hg
    simpa using hm
  have hu1 : u = 1 := by
    by_contra hne
    exact conjClassFun_ne_of_free hZc hθ hker (hfree u huE hne) (mem_inertiaGroup.1 huI)
  rw [hu1, mul_one]
  exact hxP

end Stabilizer

section Irreducibility

open scoped ComplexOrder

variable {L : Type*} [Group L] [Fintype L] {P E Z : Subgroup L} [P.Normal] [Z.Normal]

theorem indClassFun_mem_Irr_of_inertiaGroup_eq {θ : ↥P → ℂ} (hθ : θ ∈ Irr ↥P)
    (hI : inertiaGroup P θ = P) : indClassFun P θ ∈ Irr L := by
  have hnorm : cfInner (indClassFun P θ) (indClassFun P θ) = 1 := by
    rw [cfInner_self_indClassFun P hθ, hI, Subgroup.relIndex_self]
    simp
  obtain ⟨V, -, hV⟩ := mem_Irr.1 hθ
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_indClassFun P V
  rw [hV] at hW
  refine mem_Irr.2 ⟨W, ?_, hW⟩
  have hchar : Representation.character W.ρ = indClassFun P θ := by
    rw [← fdRepCharacter_eq]; exact hW
  rw [isIrreducible_iff_cfInner_self_eq_one W.ρ, hchar]
  exact hnorm

omit [Fintype L] [Z.Normal] in
theorem exists_resConstituent_not_subset_charValueKernel [Finite L] [Fintype ↥P] (hZP : Z ≤ P)
    {χ : L → ℂ}
    (hχ : χ ∈ Irr L) (hker : ¬ (Z : Set L) ⊆ charValueKernel χ) :
    ∃ θ ∈ resConstituents P χ,
      ¬ ((Z.subgroupOf P : Subgroup ↥P) : Set ↥P) ⊆ charValueKernel θ := by
  classical
  by_contra hcon
  push Not at hcon
  refine hker fun z hz => mem_charValueKernel.2 ?_
  obtain ⟨e, -, -, hres⟩ := exists_pos_resClassFun_eq_nsmul_sum (N := P) hχ
  have hval : ∀ θ ∈ resConstituents P χ, θ (⟨z, hZP hz⟩ : ↥P) = θ 1 := fun θ hθ =>
    mem_charValueKernel.1 (hcon θ hθ (show (⟨z, hZP hz⟩ : ↥P) ∈ Z.subgroupOf P from hz))
  have h1 := congrFun hres (⟨z, hZP hz⟩ : ↥P)
  have h2 := congrFun hres (1 : ↥P)
  rw [resClassFun_apply] at h1 h2
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Subgroup.coe_one] at h1 h2
  rw [h1, h2, Finset.sum_congr rfl hval]

theorem indFamDetect_eq_irrDetect (hZP : Z ≤ P) (hZc : Z ≤ centralizer (P : Set L))
    (hPE : P ⊔ E = ⊤) (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1) :
    indFamDetect P (Z.subgroupOf P) = irrDetect ℂ Z := by
  ext f
  constructor
  · rintro hf
    obtain ⟨θ, hθ, rfl⟩ := (mem_indFamDetect P).1 hf
    obtain ⟨hθIrr, hθker⟩ := mem_irrDetect.1 hθ
    rw [← Irr_eq_irrChar] at hθIrr
    have hI := inertiaGroup_eq (E := E) hZc hPE hfree hθIrr hθker
    have hind : indClassFun P θ ∈ Irr L := indClassFun_mem_Irr_of_inertiaGroup_eq hθIrr hI
    refine mem_irrDetect.2 ⟨by rwa [← Irr_eq_irrChar], ?_⟩
    rw [← normalInduction_indClassFun_eq,
      NormalInduction.subset_charValueKernel_indClassFun_iff hZP
        (by rw [normalInduction_irrChars_eq_Irr]; exact hθIrr)]
    exact hθker
  · rintro hf
    classical
    haveI : Fintype ↥P := Fintype.ofFinite _
    obtain ⟨hfIrr, hfker⟩ := mem_irrDetect.1 hf
    rw [← Irr_eq_irrChar] at hfIrr
    obtain ⟨θ, hθcon, hθker⟩ :=
      exists_resConstituent_not_subset_charValueKernel hZP hfIrr hfker
    obtain ⟨hθIrr, hθpos⟩ := mem_resConstituents.1 hθcon
    have hI := inertiaGroup_eq (E := E) hZc hPE hfree hθIrr hθker
    have hind : indClassFun P θ ∈ Irr L := indClassFun_mem_Irr_of_inertiaGroup_eq hθIrr hI
    have hfr : cfInner (indClassFun P θ) f = cfInner (resClassFun P f) θ :=
      cfInner_indClassFun_eq_cfInner_resClassFun hfIrr hθIrr
    have hpos : 0 < cfInner (indClassFun P θ) f := by rw [hfr]; exact hθpos
    have hrow := cfInner_eq_ite_of_mem_Irr hind hfIrr
    have heq : indClassFun P θ = f := by
      by_contra hne
      rw [if_neg hne, ] at hrow
      rw [hrow] at hpos
      exact absurd hpos (by simp)
    rw [← heq]
    exact (mem_indFamDetect P).2
      ⟨θ, mem_irrDetect.2 ⟨by rwa [Irr_eq_irrChar] at hθIrr, hθker⟩, rfl⟩

end Irreducibility

section Reality

open scoped ComplexConjugate

variable {L : Type*} [Group L] [Finite L] {Z : Subgroup L}

theorem conj_mem_irrDetect {f : L → ℂ} (hf : f ∈ irrDetect ℂ Z) :
    (fun x => conj (f x)) ∈ irrDetect ℂ Z := by
  obtain ⟨hfIrr, hfker⟩ := mem_irrDetect.1 hf
  rw [← Irr_eq_irrChar] at hfIrr
  refine mem_irrDetect.2 ⟨by rw [← Irr_eq_irrChar]; exact conj_mem_Irr hfIrr, ?_⟩
  intro hsub
  refine hfker fun z hz => mem_charValueKernel.2 ?_
  exact (starRingEnd ℂ).injective (mem_charValueKernel.1 (hsub hz))

omit [Finite L] in
theorem ne_one_of_mem_irrDetect {f : L → ℂ} (hf : f ∈ irrDetect ℂ Z) : f ≠ 1 := by
  obtain ⟨-, hfker⟩ := mem_irrDetect.1 hf
  intro h1
  exact hfker fun z hz => mem_charValueKernel.2 (by rw [h1]; rfl)

theorem not_conj_eq_self_of_mem_irrDetect (hodd : Odd (Nat.card L))
    {f : L → ℂ} (hf : f ∈ irrDetect ℂ Z) : f ≠ fun x => conj (f x) := by
  obtain ⟨hfIrr, -⟩ := mem_irrDetect.1 hf
  rw [← Irr_eq_irrChar] at hfIrr
  exact ne_conj_of_mem_Irr_of_ne_one_of_odd hodd hfIrr (ne_one_of_mem_irrDetect hf)

end Reality

namespace IsFreeCentralSection

variable {G : Type*} [Group G] {p a : ℕ} {L P E Z : Subgroup G}
  (h : IsFreeCentralSection p a L P E Z)

include h

theorem normal_Z_subgroupOf : (Z.subgroupOf L).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.Z_le).2 h.le_normalizer_Z

theorem sup_subgroupOf : P.subgroupOf L ⊔ E.subgroupOf L = ⊤ := by
  rw [← Subgroup.subgroupOf_sup h.P_le h.E_le, h.sup_eq, Subgroup.subgroupOf_self]

theorem Z_subgroupOf_le_centralizer :
    Z.subgroupOf L ≤ centralizer ((P.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  intro x hx
  refine mem_centralizer_iff.2 fun g hg => Subtype.ext ?_
  push_cast
  exact (mem_centralizer_iff.1 (h.Z_le_center (show ((x : ↥L) : G) ∈ Z from hx)).2) _ hg

theorem free_subgroupOf : ∀ u ∈ E.subgroupOf L, u ≠ 1 →
    ∀ z ∈ Z.subgroupOf L, u * z = z * u → z = 1 := by
  intro u hu hu1 z hz hcomm
  have hu1' : ((u : ↥L) : G) ≠ 1 := fun hcon => hu1 (Subtype.ext hcon)
  have hbot := h.inf_centralizer_eq_bot _ (show ((u : ↥L) : G) ∈ E from hu) hu1'
  have hmem : ((z : ↥L) : G) ∈ Z ⊓ centralizer ({((u : ↥L) : G)} : Set G) := by
    refine ⟨hz, mem_centralizer_iff.2 ?_⟩
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    have hc := congrArg (fun w : ↥L => (w : G)) hcomm
    push_cast at hc
    exact hc
  rw [hbot] at hmem
  exact Subtype.ext (Subgroup.mem_bot.1 hmem)

section Conclusions

variable [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal]

theorem inertiaGroup_subgroupOf_eq [Finite ↥L] {θ : ↥(P.subgroupOf L) → ℂ}
    (hθ : θ ∈ Irr ↥(P.subgroupOf L))
    (hker : ¬ (((Z.subgroupOf L).subgroupOf (P.subgroupOf L) : Subgroup _) : Set _)
      ⊆ charValueKernel θ) :
    inertiaGroup (P.subgroupOf L) θ = P.subgroupOf L :=
  inertiaGroup_eq (E := E.subgroupOf L) h.Z_subgroupOf_le_centralizer h.sup_subgroupOf
    h.free_subgroupOf hθ hker

variable [Fintype ↥L]

theorem indFamDetect_eq_irrDetect :
    indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
      = irrDetect ℂ (Z.subgroupOf L) :=
  CFSG.FeitThompson.indFamDetect_eq_irrDetect (E := E.subgroupOf L)
    (fun _ hx => h.Z_le_P hx) h.Z_subgroupOf_le_centralizer h.sup_subgroupOf h.free_subgroupOf

theorem conj_mem_indFamDetect {f : ↥L → ℂ}
    (hf : f ∈ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) :
    (fun x => (starRingEnd ℂ) (f x))
      ∈ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) := by
  rw [h.indFamDetect_eq_irrDetect] at hf ⊢
  exact conj_mem_irrDetect hf

theorem not_conj_eq_self_of_mem_indFamDetect {f : ↥L → ℂ}
    (hf : f ∈ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) :
    f ≠ fun x => (starRingEnd ℂ) (f x) := by
  rw [h.indFamDetect_eq_irrDetect] at hf
  exact not_conj_eq_self_of_mem_irrDetect h.odd_natCard_L hf

end Conclusions

end IsFreeCentralSection

end CFSG.FeitThompson
