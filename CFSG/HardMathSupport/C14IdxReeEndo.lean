module

public import CFSG.RankThree.PartOne.KLR.FrameTorus
public import CFSG.RankThree.PartOne.TCX.Ree.Closure

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.TCX.Ree

private theorem frobeniusTwist_surjective
    {τ : Tag} {K : Type} [Field K]
    (σ : K →+* K) (hσ : Function.Surjective σ) :
    Function.Surjective (frobeniusTwist τ K σ) := by
  have hgen : Subgroup.closure {g : adjointGroup τ K | ∃ (i : Fin τ.rank) (c : K),
      g = xElement i c ∨ g = yElement i c} ≤ (frobeniusTwist τ K σ).range := by
    rw [Subgroup.closure_le]
    rintro g ⟨i, c, rfl | rfl⟩
    · obtain ⟨c', rfl⟩ := hσ c
      exact ⟨xElement i c', frobeniusTwist_xElement σ i c'⟩
    · obtain ⟨c', rfl⟩ := hσ c
      exact ⟨yElement i c', frobeniusTwist_yElement σ i c'⟩
  have htop : (⊤ : Subgroup (adjointGroup τ K)) ≤ (frobeniusTwist τ K σ).range := by
    rw [← closure_xElement_yElement]
    exact hgen
  intro g
  exact MonoidHom.mem_range.mp (by
    rw [top_le_iff.mp htop]
    exact Subgroup.mem_top g)

private theorem exceptionalEndo_bijective_F4 {L : Type}
    [Field L] [CharP L 2] [PerfectRing L 2] (hf : ReeTag.F4.ShortFaithful L) :
    Function.Bijective (ReeTag.F4.exceptionalEndo L (CharP.cast_eq_zero L 2) hf) := by
  have hp : ((ReeTag.F4.prime : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
  have hCh : CharP L ReeTag.F4.prime := ‹CharP L 2›
  refine ⟨ReeTag.exceptionalEndo_injective hp hf, ?_⟩
  have hsq : Function.Surjective
      ((ReeTag.F4.exceptionalEndo L hp hf) ∘ (ReeTag.F4.exceptionalEndo L hp hf)) := by
    rw [← MonoidHom.coe_comp, ReeTag.exceptionalEndo_comp_self hp hf]
    exact frobeniusTwist_surjective (frobenius L 2)
      (surjective_frobenius L 2)
  exact Function.Surjective.of_comp hsq

theorem reeEndo_bijective
    {t : ReeTag} {K : Type} [Field K] [CharP K t.prime]
    [PerfectRing K t.prime] (hf : t.ShortFaithful K) (a : ℕ) :
    Function.Bijective (t.reeEndo K hf a) := by
  have hp : ((t.prime : ℕ) : K) = 0 := CharP.cast_eq_zero K t.prime
  have hφ : Function.Surjective (t.exceptionalEndo K hp hf) := by
    have hsq : Function.Surjective
        ((t.exceptionalEndo K hp hf) ∘ (t.exceptionalEndo K hp hf)) := by
      rw [← MonoidHom.coe_comp, t.exceptionalEndo_comp_self hp hf]
      exact frobeniusTwist_surjective (frobenius K t.prime)
        (surjective_frobenius K t.prime)
    exact Function.Surjective.of_comp hsq
  have hFt : Function.Surjective
      (frobeniusTwist t.tag K (iterateFrobenius K t.prime a)) :=
    frobeniusTwist_surjective (iterateFrobenius K t.prime a)
      (bijective_iterateFrobenius K t.prime a).surjective
  refine ⟨t.reeEndo_injective hf a, ?_⟩
  change Function.Surjective ((t.exceptionalEndo K hp hf) ∘
    (frobeniusTwist t.tag K (iterateFrobenius K t.prime a)))
  exact hφ.comp hFt

theorem exists_reeClosure_reeEndo {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] (hf : ReeTag.F4.ShortFaithful L) (a : ℕ) :
    ∃ C : ReeClosure L, ∀ g, (C.Φ * C.Fr ^ a) g = ReeTag.F4.reeEndo L hf a g := by
  classical
  have hCh : CharP L ReeTag.F4.prime := ‹CharP L 2›
  have : PerfectRing L 2 := inferInstance
  have hp : ((ReeTag.F4.prime : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
  let Φ : MulAut (adjointGroup ReeTag.F4.tag L) :=
    MulEquiv.ofBijective (ReeTag.F4.exceptionalEndo L hp hf)
      (exceptionalEndo_bijective_F4 hf)
  let Fr : MulAut (adjointGroup ReeTag.F4.tag L) :=
    MulEquiv.ofBijective (frobeniusTwist ReeTag.F4.tag L (iterateFrobenius L 2 1))
      ⟨frobeniusTwist_injective (iterateFrobenius L 2 1),
        frobeniusTwist_surjective (iterateFrobenius L 2 1)
          (bijective_iterateFrobenius L 2 1).surjective⟩
  have hfr : ∀ y : adjointGroup ReeTag.F4.tag L,
      ((Fr y : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
        Units.map (entrywiseHom (iterateFrobenius L 2 1))
          (y : ModGL ReeTag.F4.tag L) := by
    intro y
    simp only [Fr]
    exact coe_frobeniusTwist (iterateFrobenius L 2 1) y
  have hsq : Φ * Φ = Fr := by
    refine MulEquiv.ext fun y => ?_
    simp only [Φ, Fr, MulAut.mul_apply, MulEquiv.ofBijective_apply]
    rw [← MonoidHom.comp_apply, ReeTag.exceptionalEndo_comp_self hp hf]
    rfl
  have hisExc : IsReeExceptional ReeTag.F4 L Φ := by
    intro i c
    exact ⟨by simpa [Φ] using ReeTag.exceptionalEndo_xElement (t := ReeTag.F4) hp hf i c,
      by simpa [Φ] using ReeTag.exceptionalEndo_yElement (t := ReeTag.F4) hp hf i c⟩
  let C : ReeClosure L := ⟨Φ, Fr, hisExc, hfr, hsq⟩
  refine ⟨C, ?_⟩
  have hform : IsReeFrob a (C.Φ * C.Fr ^ a) :=
    isReeFrob_of_exceptional C.isExc (fun y => Subtype.ext (C.fr_apply y)) a
  have hhom : (C.Φ * C.Fr ^ a).toMonoidHom = ReeTag.F4.reeEndo L hf a := by
    refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
    · exact (hform i c).1.trans
        (ReeTag.reeEndo_xElement (t := ReeTag.F4) hf a i c).symm
    · exact (hform i c).2.trans
        (ReeTag.reeEndo_yElement (t := ReeTag.F4) hf a i c).symm
  intro g
  exact DFunLike.congr_fun hhom g

theorem isReeFrob_of_reeEndo {L : Type} [Field L]
    [CharP L 2] {hf : ReeTag.F4.ShortFaithful L} {a : ℕ}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : ∀ g, F g = ReeTag.F4.reeEndo L hf a g) :
    IsReeFrob a F := by
  intro i c
  exact ⟨by rw [hF, ReeTag.reeEndo_xElement (t := ReeTag.F4) hf a i c],
    by rw [hF, ReeTag.reeEndo_yElement (t := ReeTag.F4) hf a i c]⟩

private theorem exists_relationExponent_eq_pow (a : ℕ) (j : Fin ReeTag.F4.tag.rank) :
    ∃ k : ℕ, ReeTag.F4.relationExponent a j = 2 ^ k := by
  by_cases h : j ∈ ReeTag.F4.longSet
  · exact ⟨a, by rw [ReeTag.relationExponent, if_pos h]; rfl⟩
  · exact ⟨a + 1, by rw [ReeTag.relationExponent, if_neg h]; rfl⟩

private theorem exists_unit_pow_eq {L : Type} [Field L] [CharP L 2] [PerfectRing L 2]
    (m : ℕ) (x : Lˣ) : ∃ y : Lˣ, y ^ 2 ^ m = x := by
  classical
  let e : Lˣ ≃* Lˣ := Units.mapEquiv (iterateFrobeniusEquiv L 2 m).toMulEquiv
  refine ⟨e.symm x, ?_⟩
  refine Units.ext ?_
  have h : (e (e.symm x) : L) = ((e.symm x : Lˣ) : L) ^ 2 ^ m := by
    rw [Units.coe_mapEquiv]
    change (iterateFrobeniusEquiv L 2 m) ((e.symm x : Lˣ) : L) = _
    rw [iterateFrobeniusEquiv_def]
  rw [e.apply_symm_apply] at h
  exact h.symm

theorem reeTuple_surjective {L : Type} [Field L] [CharP L 2]
    [PerfectRing L 2] (a : ℕ) : Function.Surjective (reeTuple (L := L) a) := by
  intro c
  choose k hk using fun j : Fin ReeTag.F4.tag.rank => exists_relationExponent_eq_pow a j
  choose b hb using fun j : Fin ReeTag.F4.tag.rank =>
    exists_unit_pow_eq (L := L) (k j) (c (ReeTag.F4.perm j))
  refine ⟨b, ?_⟩
  funext j
  rw [reeTuple, hk (ReeTag.F4.perm j)]
  exact (hb (ReeTag.F4.perm j)).trans
    (congrArg c (ReeTag.perm_perm (t := ReeTag.F4) j))

end CFSG.HardMathSupport.C14Idx
