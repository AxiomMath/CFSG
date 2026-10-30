module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankFrame
public import CFSG.GroupTheory.WeirSylow.Orthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankSiegel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCMax
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankTorus
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenWeir
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TStdCovDiag
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicProof
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_frame_five (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hn : 6 ≤ n) :
    ∃ l : List (V × V), IsFrame Q l ∧ l.length = 5 ∧
      finrank (ZMod 2) (perpL Q l) = 2 * n - 10 := by
  obtain ⟨l₀, hl₀, hno⟩ := exists_frame_perpL_no_minusPair (Q := Q) hdim
  have hdimW := hl₀.finrank_Wspan
  have hle2 := hl₀.finrank_perpL_le hQ hno
  have hcompl := hl₀.isCompl
  have hadd := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hdimW] at hadd
  have hlen : 5 ≤ l₀.length := by omega
  let l := l₀.take 5
  have hl : IsFrame Q l := hl₀.sublist (List.take_sublist _ _)
  have hlen5 : l.length = 5 := by
    simp only [l, List.length_take]
    omega
  have hpdim : finrank (ZMod 2) (perpL Q l) = 2 * n - 10 := by
    rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hl.finrank_Wspan, hlen5]
    omega
  exact ⟨l, hl, hlen5, hpdim⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_singular_of_isPlusType {W : Submodule (ZMod 2) V}
    (hW : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp W.subtype))
    (hdimW : 2 ≤ finrank (ZMod 2) W) :
    ∃ e ∈ W, e ≠ 0 ∧ Q e = 0 := by
  obtain ⟨U, hU, hU0⟩ := hW
  have hUne : U ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hU
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  exact ⟨u, u.2, fun h => hu0 (Subtype.ext h), hU0 u hu⟩

theorem exists_singular_of_isMinusType {W : Submodule (ZMod 2) V}
    (hW : CFSG.GroupTheory.WeirSylow.IsMinusType (Q.comp W.subtype))
    (hdimW : 4 ≤ finrank (ZMod 2) W) :
    ∃ e ∈ W, e ≠ 0 ∧ Q e = 0 := by
  obtain ⟨⟨U, hU, hU0⟩, -⟩ := hW
  have hUne : U ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hU
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  exact ⟨u, u.2, fun h => hu0 (Subtype.ext h), hU0 u hu⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem not_isPlusType_perpL_five_of_plus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 6 ≤ n)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {l : List (V × V)}
    (hl : IsFrame Q l) (hlen : l.length = 5) :
    ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (perpL Q l).subtype) := by
  have hdisj : Disjoint (Wspan l) (perpL Q l) := hl.isCompl.disjoint
  have horth : ∀ a ∈ Wspan l, ∀ b ∈ perpL Q l, polar Q a b = 0 := by
    intro a ha b hb
    have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hb) a ha
    rwa [QuadraticMap.polarBilin_apply_apply] at h1
  have hA : (QuadraticMap.polarBilin (Q.comp (Wspan l).subtype)).Nondegenerate :=
    nondeg_Wspan hl
  have hB : (QuadraticMap.polarBilin (Q.comp (perpL Q l).subtype)).Nondegenerate :=
    nondeg_comp_subtype (hl.perpL_nondeg hQ)
  have hsup : Wspan l ⊔ perpL Q l = ⊤ := hl.isCompl.sup_eq_top
  have htopForm : CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (Wspan l ⊔ perpL Q l).subtype) :=
    (CFSG.GroupTheory.WeirSylow.isPlusType_congr
      (Q := Q.comp (Wspan l ⊔ perpL Q l).subtype) (Q' := Q)
      { toLinearEquiv := LinearEquiv.ofTop _ hsup
        map_app' := fun x => rfl }).2 hplus
  have hiff := (isPlusType_sup_iff hdisj horth hA hB (d₁ := 5) (d₂ := n - 5)
    (by norm_num) (by omega) (by rw [hl.finrank_Wspan, hlen])
    (by rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hl.finrank_Wspan, hlen, hdim]; omega))
  have hAmin : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (Wspan l).subtype) := by
    rw [isPlusType_Wspan_iff hl, hlen]
    norm_num
  exact fun hBplus => hAmin ((hiff.1 htopForm).mpr hBplus)

theorem isPlusType_perpL_five_of_minus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 6 ≤ n)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) {l : List (V × V)}
    (hl : IsFrame Q l) (hlen : l.length = 5) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (perpL Q l).subtype) := by
  have hdisj : Disjoint (Wspan l) (perpL Q l) := hl.isCompl.disjoint
  have horth : ∀ a ∈ Wspan l, ∀ b ∈ perpL Q l, polar Q a b = 0 := by
    intro a ha b hb
    have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hb) a ha
    rwa [QuadraticMap.polarBilin_apply_apply] at h1
  have hA : (QuadraticMap.polarBilin (Q.comp (Wspan l).subtype)).Nondegenerate :=
    nondeg_Wspan hl
  have hB : (QuadraticMap.polarBilin (Q.comp (perpL Q l).subtype)).Nondegenerate :=
    nondeg_comp_subtype (hl.perpL_nondeg hQ)
  have hsup : Wspan l ⊔ perpL Q l = ⊤ := hl.isCompl.sup_eq_top
  have htopForm : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (Wspan l ⊔ perpL Q l).subtype) := by
    intro hplus
    exact hminus ((CFSG.GroupTheory.WeirSylow.isPlusType_congr
      (Q := Q.comp (Wspan l ⊔ perpL Q l).subtype) (Q' := Q)
      { toLinearEquiv := LinearEquiv.ofTop _ hsup
        map_app' := fun x => rfl }).1 hplus)
  have hiff := (isPlusType_sup_iff hdisj horth hA hB (d₁ := 5) (d₂ := n - 5)
    (by norm_num) (by omega) (by rw [hl.finrank_Wspan, hlen])
    (by rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hl.finrank_Wspan, hlen, hdim]; omega))
  have hAmin : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (Wspan l).subtype) := by
    rw [isPlusType_Wspan_iff hl, hlen]
    norm_num
  have hnot : ¬ (CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (Wspan l).subtype) ↔
      CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (perpL Q l).subtype)) :=
    fun h => htopForm (hiff.2 h)
  by_contra hBplus
  exact hnot ⟨fun hA' => absurd hA' hAmin, fun hB' => absurd hB' hBplus⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem isMinusType_perpL_five_of_plus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 6 ≤ n)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {l : List (V × V)}
    (hl : IsFrame Q l) (hlen : l.length = 5) :
    CFSG.GroupTheory.WeirSylow.IsMinusType (Q.comp (perpL Q l).subtype) := by
  have hWminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (perpL Q l).subtype) :=
    not_isPlusType_perpL_five_of_plus hQ hdim (by omega) hplus hl hlen
  have hWdim : finrank (ZMod 2) (perpL Q l) = 2 * (n - 5) := by
    rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hl.finrank_Wspan, hlen]
    omega
  exact (CFSG.LocalAnalysis.RankFourTheoremC.isPlusType_or_isMinusType
    (Q.comp (perpL Q l).subtype)
    (nondeg_comp_subtype (hl.perpL_nondeg hQ)) (n := n - 5) (by omega) hWdim).resolve_left hWminus

theorem exists_twoLocal_of_fiveFrameData (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 6 ≤ n) {l : List (V × V)}
    (hl : IsFrame Q l) (hlen : l.length = 5) {a b : Fin 5 → V}
    (hp : ∀ i, MinusPair Q (a i) (b i))
    (hperp : ∀ i j, i ≠ j → PairPerp Q (a i, b i) (a j, b j))
    {e f : V} (heW : e ∈ perpL Q l) (he0 : e ≠ 0) (heQ : Q e = 0)
    (horth : ∀ x ∈ perpL Q l, ∀ i, polar Q x (a i) = 0 ∧ polar Q x (b i) = 0)
    (hfW : f ∈ perpL Q l) (hfe : polar Q e f = 1) (hfa : polar Q f (a 0) = 0) :
    ∃ E : Subgroup ↥(orthDerived Q), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ TwoLocal E := by
  let E : Subgroup ↥(orthDerived Q) :=
    Subgroup.closure (Set.range fun i => rotOrthDerived Q (a := a i) (b := b i) (hp i))
  have hEel : IsElemAbelian 3 E :=
    (isElemAbelian_card_closure_rotOrthDerived (Q := Q) (a := a) (b := b) hp hperp).1
  have hEcard : Nat.card E = 3 ^ 5 := by
    simpa [E] using
      (isElemAbelian_card_closure_rotOrthDerived (Q := Q) (a := a) (b := b) hp hperp).2
  have hEfix : ∀ g ∈ E, (g : V ≃ₗ[ZMod 2] V) e = e := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact rot_apply_of_perp (hp i) (horth e heW i).1 (horth e heW i).2
    | one => rfl
    | mul x y hx hy ihx ihy =>
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ihy, ihx]
    | inv x hx ih =>
        have h1 : ((x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V).symm e = e :=
          (congrArg ((x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V).symm ih.symm).trans
            (((x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V).symm_apply_apply e)
        rw [Subgroup.coe_inv]
        exact h1
  have hEnorm : E ≤ Subgroup.normalizer
      (((rootGroup Q e).subgroupOf (orthDerived Q) : Subgroup ↥(orthDerived Q)) :
        Set ↥(orthDerived Q)) :=
    fun g hg => mem_normalizer_subgroupOf_rootGroup (hEfix g hg)
  have h5dim : 5 ≤ finrank (ZMod 2) V := by omega
  have ha : Q (a 0) = 1 := (hp 0).qa
  have hea : polar Q e (a 0) = 0 := (horth e heW 0).1
  have hT1 : (rootGroup Q e).subgroupOf (orthDerived Q) ≠ ⊥ :=
    subgroupOf_rootGroup_ne_bot hQ h5dim heQ ha hea (by rw [polar_comm]; exact hfe) hfa
  exact ⟨E, hEel, hEcard,
    ⟨(rootGroup Q e).subgroupOf (orthDerived Q), isPGroup_two_subgroupOf_rootGroup e, hT1, hEnorm⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section



namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_fiveFrameData_plus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 7 ≤ n)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ (l : List (V × V)) (a b : Fin 5 → V) (e f : V),
      IsFrame Q l ∧ l.length = 5 ∧ (∀ i, MinusPair Q (a i) (b i)) ∧
      (∀ i j, i ≠ j → PairPerp Q (a i, b i) (a j, b j)) ∧
      e ∈ perpL Q l ∧ e ≠ 0 ∧ Q e = 0 ∧
      (∀ x ∈ perpL Q l, ∀ i, polar Q x (a i) = 0 ∧ polar Q x (b i) = 0) ∧
      f ∈ perpL Q l ∧ polar Q e f = 1 ∧ polar Q f (a 0) = 0 := by
  obtain ⟨l, hl, hlen, hpdim⟩ := exists_frame_five hQ hdim (by omega)
  obtain ⟨a, b, hp, hperp, horth⟩ := exists_family_of_isFrame hl hlen
  have hWtype : CFSG.GroupTheory.WeirSylow.IsMinusType (Q.comp (perpL Q l).subtype) :=
    isMinusType_perpL_five_of_plus hQ hdim (by omega) hplus hl hlen
  have hWdim : finrank (ZMod 2) (perpL Q l) = 2 * (n - 5) := by
    rw [hpdim]; omega
  have hWdim4 : 4 ≤ finrank (ZMod 2) (perpL Q l) := by rw [hWdim]; omega
  obtain ⟨e, heW, he0, heQ⟩ := exists_singular_of_isMinusType hWtype hWdim4
  have hex : ∃ f ∈ perpL Q l, polar Q e f = 1 := by
    by_contra h
    push Not at h
    have hzero : ∀ y ∈ perpL Q l, polar Q e y = 0 := by
      intro y hy
      rcases zmod_two_cases (polar Q e y) with h0 | h1
      · exact h0
      · exact absurd h1 (h y hy)
    have hzeroV : ∀ y : V, polar Q e y = 0 := by
      intro y
      have hy : y ∈ Wspan l ⊔ perpL Q l := by rw [hl.isCompl.sup_eq_top]; trivial
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy
      have h1 : polar Q e u = 0 := by
        have h2 := (LinearMap.BilinForm.mem_orthogonal_iff.1 heW) u hu
        rw [QuadraticMap.polarBilin_apply_apply] at h2
        rw [polar_comm]
        exact h2
      rw [polar_add_right, h1, hzero v hv, add_zero]
    exact he0 (hQ.1 e hzeroV)
  obtain ⟨f, hfW, hfe⟩ := hex
  have hfa : polar Q f (a 0) = 0 := (horth f hfW 0).1
  exact ⟨l, a, b, e, f, hl, hlen, hp, hperp, heW, he0, heQ, horth, hfW, hfe, hfa⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_twoLocal_three_pow_five_plus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 7 ≤ n)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ E : Subgroup ↥(orthDerived Q), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ TwoLocal E := by
  obtain ⟨l, a, b, e, f, hl, hlen, hp, hperp, heW, he0, heQ, horth, hfW, hfe, hfa⟩ :=
    exists_fiveFrameData_plus hQ hdim hn hplus
  exact exists_twoLocal_of_fiveFrameData hQ hdim (by omega) hl hlen hp hperp heW he0 heQ horth
    hfW hfe hfa

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_fiveFrameData_minus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 6 ≤ n)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ (l : List (V × V)) (a b : Fin 5 → V) (e f : V),
      IsFrame Q l ∧ l.length = 5 ∧ (∀ i, MinusPair Q (a i) (b i)) ∧
      (∀ i j, i ≠ j → PairPerp Q (a i, b i) (a j, b j)) ∧
      e ∈ perpL Q l ∧ e ≠ 0 ∧ Q e = 0 ∧
      (∀ x ∈ perpL Q l, ∀ i, polar Q x (a i) = 0 ∧ polar Q x (b i) = 0) ∧
      f ∈ perpL Q l ∧ polar Q e f = 1 ∧ polar Q f (a 0) = 0 := by
  obtain ⟨l, hl, hlen, hpdim⟩ := exists_frame_five hQ hdim hn
  obtain ⟨a, b, hp, hperp, horth⟩ := exists_family_of_isFrame hl hlen
  have hWplus : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (perpL Q l).subtype) :=
    isPlusType_perpL_five_of_minus hQ hdim hn hminus hl hlen
  have hWdim : finrank (ZMod 2) (perpL Q l) = 2 * (n - 5) := by
    rw [hpdim]; omega
  have hWdim2 : 2 ≤ finrank (ZMod 2) (perpL Q l) := by rw [hWdim]; omega
  obtain ⟨e, heW, he0, heQ⟩ := exists_singular_of_isPlusType hWplus hWdim2
  have hex : ∃ f ∈ perpL Q l, polar Q e f = 1 := by
    by_contra h
    push Not at h
    have hzero : ∀ y ∈ perpL Q l, polar Q e y = 0 := by
      intro y hy
      rcases zmod_two_cases (polar Q e y) with h0 | h1
      · exact h0
      · exact absurd h1 (h y hy)
    have hzeroV : ∀ y : V, polar Q e y = 0 := by
      intro y
      have hy : y ∈ Wspan l ⊔ perpL Q l := by rw [hl.isCompl.sup_eq_top]; trivial
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy
      have h1 : polar Q e u = 0 := by
        have h2 := (LinearMap.BilinForm.mem_orthogonal_iff.1 heW) u hu
        rw [QuadraticMap.polarBilin_apply_apply] at h2
        rw [polar_comm]
        exact h2
      rw [polar_add_right, h1, hzero v hv, add_zero]
    exact he0 (hQ.1 e hzeroV)
  obtain ⟨f, hfW, hfe⟩ := hex
  have hfa : polar Q f (a 0) = 0 := (horth f hfW 0).1
  exact ⟨l, a, b, e, f, hl, hlen, hp, hperp, heW, he0, heQ, horth, hfW, hfe, hfa⟩

theorem exists_twoLocal_three_pow_five_minus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 6 ≤ n)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ E : Subgroup ↥(orthDerived Q), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ TwoLocal E := by
  obtain ⟨l, a, b, e, f, hl, hlen, hp, hperp, heW, he0, heQ, horth, hfW, hfe, hfa⟩ :=
    exists_fiveFrameData_minus hQ hdim hn hminus
  exact exists_twoLocal_of_fiveFrameData hQ hdim (by omega) hl hlen hp hperp heW he0 heQ horth
    hfW hfe hfa

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem noSmallModel_plus_ge_seven (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 7 ≤ n)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) : NoSmallModel ↥(orthDerived Q) := by
  intro Bb h
  obtain ⟨E, hEel, hEcard, hEtwo⟩ := exists_twoLocal_three_pow_five_plus hQ hdim hn hplus
  have hle := h.max E hEel hEtwo
  rw [hEcard] at hle
  have hle' : Nat.card Bb ≤ 3 ^ 4 := by simpa using h.card_le
  have : (3 ^ 5 : ℕ) ≤ 3 ^ 4 := hle.trans hle'
  norm_num at this

theorem noSmallModel_minus_ge_six (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) (hn : 6 ≤ n)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) : NoSmallModel ↥(orthDerived Q) := by
  intro Bb h
  obtain ⟨E, hEel, hEcard, hEtwo⟩ := exists_twoLocal_three_pow_five_minus hQ hdim hn hminus
  have hle := h.max E hEel hEtwo
  rw [hEcard] at hle
  have hle' : Nat.card Bb ≤ 3 ^ 4 := by simpa using h.card_le
  have : (3 ^ 5 : ℕ) ≤ 3 ^ 4 := hle.trans hle'
  norm_num at this

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
