module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Groups
public import CFSG.Quasithin.Background.SmithCurtisHecke

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem conj_mem_subgroupOf {M : Type*} [Group M] {A S : Subgroup M} {g x : A}
    (h : (g : M) * x * (g : M)⁻¹ ∈ S) : g * x * g⁻¹ ∈ S.subgroupOf A := h

theorem conj_inv_mem_subgroupOf {M : Type*} [Group M] {A S : Subgroup M} {g x : A}
    (h : (g : M)⁻¹ * x * g ∈ S) : g⁻¹ * x * g ∈ S.subgroupOf A := h

theorem inv_conj_mem_of_mem_normalizer {M : Type*} [Group M] {S : Subgroup M} {h g : M}
    (hN : h ∈ Subgroup.normalizer (S : Set M)) (hg : g ∈ S) : h⁻¹ * g * h ∈ S := by
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem hN) g).mp hg
  rwa [inv_inv] at this

theorem heckeDeg_subgroupOf' {M : Type*} [Group M] {A U : Subgroup M} (hU : U ≤ A) (g : A) :
    CFSG.Quasithin.SmithCurtis.heckeDeg (U.subgroupOf A) g =
      CFSG.Quasithin.SmithCurtis.heckeDeg U (g : M) := by
  unfold CFSG.Quasithin.SmithCurtis.heckeDeg
  have h : (U.subgroupOf A).map (MulAut.conj g).toMonoidHom =
      (U.map (MulAut.conj (g : M)).toMonoidHom).subgroupOf A := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, hU hy⟩, hy, Subtype.ext e⟩
  rw [h, Subgroup.relIndex_subgroupOf hU]

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] def nC (a : Fin t.foldedTag.rank) : ↥(graphFixedRootGroup t K σ) :=
  ⟨canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a),
    graphFixedRootMonomial_le t K σ
      (canonicalRep_mem_graphFixedRootMonomial t K σ (t.orbitReflection_mem a))⟩

@[expose] def nWC (w : ↥(relWeylTwist t)) : ↥(graphFixedRootGroup t K σ) :=
  ⟨canonicalRep (coxeterSystem t.tag) K (w : WeylGroup t.tag),
    graphFixedRootMonomial_le t K σ (canonicalRep_mem_graphFixedRootMonomial t K σ w.2)⟩

@[expose] def xC (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    ↥(graphFixedRootGroup t K σ) :=
  ⟨(orbitX t K σ a c : ModGL t.tag K),
    graphFixedPosUnipotent_le_graphFixedRootGroup t K σ (orbitX_mem_graphFixedPosUnipotent t σ a c)⟩

@[expose] def yC (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    ↥(graphFixedRootGroup t K σ) :=
  ⟨(orbitY t K σ a c : ModGL t.tag K),
    graphFixedNegUnipotent_le_graphFixedRootGroup t K σ (orbitY_mem_graphFixedNegUnipotent t σ a c)⟩

@[expose] def hC (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    ↥(graphFixedRootGroup t K σ) :=
  ⟨(orbitH t K σ a u : ModGL t.tag K), orbitH_mem_graphFixedRootGroup t σ a u⟩

variable {t K σ}

theorem hC_mem (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    (hC t K σ a u : ModGL t.tag K) ∈ graphFixedRootTorus t K σ :=
  orbitH_mem_graphFixedRootTorus t σ a u

theorem yC_mem (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (yC t K σ a c : ModGL t.tag K) ∈ graphFixedNegUnipotent t K σ :=
  orbitY_mem_graphFixedNegUnipotent t σ a c

theorem xC_mem (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (xC t K σ a c : ModGL t.tag K) ∈ graphFixedPosUnipotent t K σ :=
  orbitX_mem_graphFixedPosUnipotent t σ a c

theorem yC_zero (a : Fin t.foldedTag.rank) : yC t K σ a 0 = 1 := by
  refine Subtype.ext ?_
  show (orbitY t K σ a 0 : ModGL t.tag K) = 1
  have h : (vSL (0 : orbitField t K σ a) : SL2 (orbitField t K σ a)) = 1 := by
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_vSL]
  rw [← orbitRankOneHom_vSL (σ := σ) a, h, map_one]

theorem xC_mul_nC (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    xC t K σ a (u : orbitField t K σ a) * nC t K σ a =
      yC t K σ a ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) * hC t K σ a (-u) *
        xC t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) :=
  Subtype.ext (orbitX_mul_n σ a u)

theorem nC_mul_xC_mul_nC (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    nC t K σ a * xC t K σ a (u : orbitField t K σ a) * nC t K σ a =
      xC t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) * nC t K σ a *
        hC t K σ a (-u) *
        xC t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) :=
  Subtype.ext (n_mul_orbitX_mul_n σ a u)

theorem yC_eq (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    yC t K σ a (u : orbitField t K σ a) =
      xC t K σ a ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) *
        (hC t K σ a (-u⁻¹) * nC t K σ a) *
        xC t K σ a ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) :=
  Subtype.ext (orbitY_eq σ a u)

open Classical in
variable (t K σ) in
@[expose] def torusPart (a : Fin t.foldedTag.rank) (g : ↥(graphFixedRootGroup t K σ)) :
    ↥(graphFixedRootGroup t K σ) :=
  if h : ∃ c : (orbitField t K σ a)ˣ,
      (g : ModGL t.tag K) = (orbitX t K σ a (c : orbitField t K σ a) : ModGL t.tag K) then
    hC t K σ a (-h.choose) else 1

theorem torusPart_eq {a : Fin t.foldedTag.rank} {g : ↥(graphFixedRootGroup t K σ)}
    {c : (orbitField t K σ a)ˣ}
    (hg : (g : ModGL t.tag K) = (orbitX t K σ a (c : orbitField t K σ a) : ModGL t.tag K)) :
    torusPart t K σ a g = hC t K σ a (-c) := by
  have h : ∃ c : (orbitField t K σ a)ˣ,
      (g : ModGL t.tag K) = (orbitX t K σ a (c : orbitField t K σ a) : ModGL t.tag K) := ⟨c, hg⟩
  have hc : h.choose = c := by
    have h2 := h.choose_spec
    have h3 : orbitX t K σ a (h.choose : orbitField t K σ a) = orbitX t K σ a (c : _) :=
      Subtype.ext (h2.symm.trans hg)
    exact Units.ext (orbitX_injective σ a h3)
  rw [torusPart, dite_eq_left h, hc]

theorem exists_unit_of_mem_Xg {a : Fin t.foldedTag.rank} {g : ↥(graphFixedRootGroup t K σ)}
    (hg : (g : ModGL t.tag K) ∈ Xg t K σ a) (hg1 : g ≠ 1) :
    ∃ c : (orbitField t K σ a)ˣ,
      (g : ModGL t.tag K) = (orbitX t K σ a (c : orbitField t K σ a) : ModGL t.tag K) := by
  obtain ⟨c, hc⟩ := (mem_Xg_iff a).1 hg
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hg1
    refine Subtype.ext ?_
    rw [← hc]
    show (orbitX t K σ a 0 : ModGL t.tag K) = 1
    rw [orbitX_zero]
    rfl
  exact ⟨Units.mk0 c hc0, hc.symm⟩

theorem exists_unit_of_mem_Yg {a : Fin t.foldedTag.rank} {g : ↥(graphFixedRootGroup t K σ)}
    (hg : (g : ModGL t.tag K) ∈ Yg t K σ a) (hg1 : g ≠ 1) :
    ∃ c : (orbitField t K σ a)ˣ,
      (g : ModGL t.tag K) = (orbitY t K σ a (c : orbitField t K σ a) : ModGL t.tag K) := by
  obtain ⟨c, hc⟩ := (mem_Yg_iff a).1 hg
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hg1
    refine Subtype.ext ?_
    rw [← hc]
    exact congrArg Subtype.val (yC_zero (σ := σ) a)
  exact ⟨Units.mk0 c hc0, hc.symm⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
