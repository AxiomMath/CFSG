module

public import CFSG.ClassicalInvolution.Uniform.USylow
public import CFSG.ClassicalInvolution.Asc77.AscIH8Model
public import CFSG.ClassicalInvolution.Uniform.UOmegaLie

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

omit [Fact p.Prime] in
theorem IsClassicalMemberU.exists_noncomm (h : IsClassicalMemberU (.sl2 p f) L z) :
    ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  obtain ⟨x, -, y, -, hxy⟩ := h.exists_noncomm_sylow (MemberType.cert_sl2 p f) T
  exact ⟨x, x.2, y, y.2, fun h' => hxy (Subtype.ext h')⟩

end Members

section Simple

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

namespace OmegaLieU

variable {Ω : Set (Subgroup G)}

omit [Finite G] in
variable (D : OmegaLieU p f Ω) in
theorem comp_eq_top_of_simple [IsSimpleGroup G] (hΩ : HypOmegaModU (.sl2 p f) Ω)
    (hne : Ω.Nonempty) (i : Fin D.card) : D.comp i = ⊤ := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  have hKne : K ≠ ⊥ := by
    intro h
    have h1 := hz.mem
    rw [h, Subgroup.mem_bot] at h1
    exact hz.ne_one h1
  have htop : omegaGen Ω = ⊤ := ih8_omegaGen_eq_top hΩ.conjInvariant hK hKne
  have hnorm : (D.comp i).Normal :=
    ⟨fun x hx g => D.mem_comp_conj (htop ▸ Subgroup.mem_top g) hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.comp i) with h | h
  · exfalso
    obtain ⟨R, hR, hmem⟩ := D.meets i
    obtain ⟨z', hz'⟩ := hΩ.classical _ hmem
    have hbot : R.map (D.hom i) = ⊥ := by
      rw [eq_bot_iff]
      calc R.map (D.hom i) ≤ D.comp i := Subgroup.map_le_range _ _
        _ ≤ ⊥ := h.le
    have h1 := hz'.mem
    rw [hbot, Subgroup.mem_bot] at h1
    exact hz'.ne_one h1
  · exact h

variable (D : OmegaLieU p f Ω) in
theorem card_eq_one_of_simple [IsSimpleGroup G] (hΩ : HypOmegaModU (.sl2 p f) Ω)
    (hne : Ω.Nonempty) : D.card = 1 := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  obtain ⟨i₀, -⟩ := D.exists_comp_of_mem hK
  have hpos : 0 < D.card := i₀.pos
  by_contra hne1
  have h1 : 1 < D.card := by omega
  have hij : (⟨0, hpos⟩ : Fin D.card) ≠ ⟨1, h1⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hc := D.comp_commute hij
  rw [D.comp_eq_top_of_simple hΩ ⟨K, hK⟩, D.comp_eq_top_of_simple hΩ ⟨K, hK⟩] at hc
  obtain ⟨x, hx, y, hy, hxy⟩ := hz.exists_noncomm
  exact hxy (hc x (Subgroup.mem_top x) y (Subgroup.mem_top y))

omit [Finite G] in
variable (D : OmegaLieU p f Ω) in
theorem hom_surjective_of_simple [IsSimpleGroup G] (hΩ : HypOmegaModU (.sl2 p f) Ω)
    (hne : Ω.Nonempty) (i : Fin D.card) : Function.Surjective (D.hom i) :=
  MonoidHom.range_eq_top.mp (D.comp_eq_top_of_simple hΩ hne i)

@[expose] def cls (D : OmegaLieU p f Ω) (i : Fin D.card) : Set (Subgroup (D.kind i).G) :=
  {R | R ∈ (D.kind i).fund ∧ R.map (D.hom i) ∈ Ω}

omit [Finite G] in
theorem mem_iff_exists_cls (D : OmegaLieU p f Ω) (hcard : D.card = 1) (i : Fin D.card)
    {L : Subgroup G} : L ∈ Ω ↔ ∃ R ∈ D.cls i, L = R.map (D.hom i) := by
  constructor
  · intro hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl : j = i := Fin.ext (by have := i.2; have := j.2; omega)
    exact ⟨R, ⟨hR, hLR ▸ hL⟩, hLR⟩
  · rintro ⟨R, hR, rfl⟩
    exact hR.2

noncomputable def toIh8Model [IsSimpleGroup G] (D : OmegaLieU p f Ω)
    (hΩ : HypOmegaModU (.sl2 p f) Ω) (hne : Ω.Nonempty) (hcard : D.card = 1) (i : Fin D.card)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ} (ht : Generic.IsFundTag t)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t k p e)
    (he : e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) (hc : D.kind i = compModel p e t k) :
    Ih8Model p f Ω t k e where
  isFundTag := ht
  admissible := hadm
  exp_eq := he
  ψ := castHom hc (D.hom i)
  ker_le_center := castHom_ker_le_center hc (D.hom i) (D.ker_le_center i)
  surj := by
    have h := D.hom_surjective_of_simple hΩ hne i
    rw [← MonoidHom.range_eq_top] at h ⊢
    rw [range_castHom]
    exact h
  cls := {R | R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D ∧
    R.map (castHom hc (D.hom i)) ∈ Ω}
  cls_sub := fun _ hR => hR.1
  mem_iff := by
    intro L
    constructor
    · intro hL
      obtain ⟨R, hR, rfl⟩ := (D.mem_iff_exists_cls hcard i).mp hL
      obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom i) hR.1
      exact ⟨R', ⟨hR', by rw [hRR]; exact hR.2⟩, hRR.symm⟩
    · rintro ⟨R, hR, rfl⟩
      exact hR.2
  cls_conj := by
    intro R hR g
    refine ⟨Asc77.OmegaLie.fund_conj hR.1 g, ?_⟩
    have := map_conj_eq_conjSub_map (castHom hc (D.hom i)) g R
    change Subgroup.map (castHom hc (D.hom i)) (conjSub g R) ∈ Ω
    rw [show Subgroup.map (castHom hc (D.hom i)) (conjSub g R) =
      conjSub (castHom hc (D.hom i) g) (R.map (castHom hc (D.hom i))) from this]
    exact hΩ.conjInvariant _ _ hR.2

end OmegaLieU

theorem exists_omegaLieU_of_simple [IsSimpleGroup G] {Ω : Set (Subgroup G)} {n : ℕ}
    (hn : CITBelowT (.sl2 p f) n) (hlt : Nat.card G < n) (hΩ : HypOmegaModU (.sl2 p f) Ω)
    (hne : Ω.Nonempty) : ∃ D : OmegaLieU p f Ω, D.card = 1 := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  have hO := ih8_oddCore_eq_bot_of_simple hz.orderOf_eq_two
  obtain ⟨D⟩ := exists_omegaLieU hn hΩ ⟨K, hK⟩ hO hlt
  exact ⟨D, D.card_eq_one_of_simple hΩ ⟨K, hK⟩⟩

end Simple

end CFSG.ClassicalInvolution.Uniform
