module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTorus
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

section LangComponentPieces


theorem exists_quasisimple_of_mem_bigComponentSet (S : LangSetup τ L p)
    {D₁ : Subgroup (ModGL τ L)} (hD₁ : D₁ ≤ S.E) {x : ModGL τ L}
    (hx : x ∈ bigComponentSet S D₁) :
    ∃ d ∈ D₁, d ≠ 1 ∧ ∃ R : Subgroup (ModGL τ L), R ≤ S.Γ ⊓ Subgroup.centralizer {d} ∧
      CFSG.IsQuasisimple R ∧ ¬ Nat.Coprime p (Nat.card R) := by
  classical
  obtain ⟨a, haD, ha1, i, hbig, -⟩ := hx
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  have hE : rootDiagUnit τ a ∈ S.E := hD₁ haD
  obtain ⟨hLC, -⟩ := hsub τ L p S a hE ha1 i
  refine ⟨rootDiagUnit τ a, haD, ha1,
    rationalComponent S.ρ S.Γ (rootCharHom a) i, hLC, ?_, hbig⟩
  cases hkind : twistKind S.ρ (rootCharHom a) i
  · exact hin τ L p S a hE ha1 i hkind hbig
  · exact hsu τ L p S a hE ha1 i hkind hbig
  · exact htw τ L p S a hE ha1 i hkind hbig
  · exact hex τ L p S a hE ha1 i hkind hbig

theorem perfectCentralizerPlanes_of_langSetup (S : LangSetup τ L p)
    (hconj : ∀ F : Subgroup (ModGL τ L), F ≤ S.Γ → (∀ x ∈ F, x ^ p = 1) → Nat.card F = p ^ 2 →
      ∃ h ∈ S.Γ, F.map (MulAut.conj h).toMonoidHom ≤ S.E)
    (hbig : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      (bigComponentSet S D₁).Nonempty) :
    PerfectCentralizerPlanes p S.Γ := by
  classical
  refine PerfectCentralizerPlanes.of_conj_le (Γ := S.Γ) (E := S.E) hconj ?_
  intro D hDE _ hDcard
  obtain ⟨x, hx⟩ := hbig D hDE hDcard
  obtain ⟨d, hdD, hd1, R, hRle, hRq, hRnc⟩ :=
    exists_quasisimple_of_mem_bigComponentSet S hDE hx
  have hRperf : ⁅R, R⁆ = R := by
    haveI : Group.IsPerfect ↥R := hRq.1
    exact Subgroup.commutator_eq_self
  exact ⟨d, hdD, hd1, R, hRle, hRperf,
    (Nat.Prime.dvd_iff_not_coprime S.hp).mpr hRnc⟩

end LangComponentPieces

section HasBigAnyComponent


theorem bigComponentSet_nonempty_of_hasBigAnyComponent (S : LangSetup τ L p)
    {D₁ : Subgroup (ModGL τ L)} (h : HasBigAnyComponent S D₁) :
    (bigComponentSet S D₁).Nonempty := by
  obtain ⟨a, haD, ha1, i, hbig, -⟩ := h
  exact ⟨1, a, haD, ha1, i, hbig, Subgroup.one_mem _⟩

end HasBigAnyComponent

section CentralizerTrivial


theorem bigComponentSet_nonempty_of_centralizerTrivial (S : LangSetup τ L p)
    {D₁ : Subgroup (ModGL τ L)} (hD₁ : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2)
    (h : CentralizerTrivial S D₁) : (bigComponentSet S D₁).Nonempty := by
  classical
  by_contra hne
  have hempty : bigComponentSet S D₁ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  have hp2 : 1 < p ^ 2 := by
    have := S.hp.one_lt
    nlinarith
  have hfin : Finite D₁ :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero 2 S.hp.ne_zero)
  have hnt : Nontrivial D₁ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; exact hp2)
  obtain ⟨z, hz1⟩ := exists_ne (1 : D₁)
  have hzT : (z : ModGL τ L) ∈ S.D.torus := (S.E_le (hD₁ z.2)).1
  have hzΓ : (z : ModGL τ L) ∈ S.Γ := (S.E_le (hD₁ z.2)).2
  have hzAdj : (z : ModGL τ L) ∈ adjointGroup τ L :=
    ((Subgroup.commutator_le_self S.D.model).trans inf_le_left) hzΓ
  haveI : IsMulCommutative S.D.torus := S.D.isMulCommutative_torus
  have hzcomm : ∀ x ∈ rigidTestSet S D₁, Commute (z : ModGL τ L) x := by
    intro x hx
    rw [rigidTestSet, hempty, Set.empty_union] at hx
    exact setLike_mul_comm hzT (S.E_le (hD₁ hx)).1
  exact hz1 (Subtype.ext (h z hzAdj hzcomm))

end CentralizerTrivial

section BigAnyPBig


theorem bigComponentSet_nonempty_of_bigAnyPBig (S : LangSetup τ L p) (hP : BigAnyPBig S)
    {D₁ : Subgroup (ModGL τ L)} (hD₁ : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) :
    (bigComponentSet S D₁).Nonempty := by
  classical
  obtain ⟨γ, hγr, hγn⟩ := S.exists_root_not_mem_planeKernel hD₁ hc
  obtain ⟨a', ha'D, ha'1⟩ : ∃ a', rootDiagUnit τ a' ∈ D₁ ∧ rootChar a' γ ≠ 1 := by
    by_contra h
    push Not at h
    exact hγn ⟨hγr, h⟩
  obtain ⟨a, haD, ha1, hγa⟩ := S.exists_nontrivial_killing hD₁ hc γ
  have hmem : γ ∈ kernelRoots (rootCharHom a) := ⟨hγr, hγa⟩
  refine ⟨1, a, haD, ha1, (⟦⟨γ, hmem⟩⟧ : KernelComponent (rootCharHom a)), ?_,
    Subgroup.one_mem _⟩
  exact hP D₁ hD₁ hc a haD a' ha'D γ hγr hγa ha'1 _ ⟨hmem, rfl⟩

end BigAnyPBig

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
