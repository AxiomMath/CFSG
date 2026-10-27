module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1313Z

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1313
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

section Inputs

@[expose] def Input18_3DiagZ : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → ∀ x y : G, orderOf x = p → orderOf y = p →
    x * y = y * x → ∀ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x, y} : Set G)) J →
    ∀ L : ZMod p → Subgroup G, (∀ i, GLAPComponent p (Subgroup.centralizer ({y} : Set G)) (L i)) →
    Function.Injective L → (∀ i, GLBConj x (L i) = L (i + 1)) →
    (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J) = ⨆ i, L i →
    ∀ i, Nonempty ((↥J ⧸ GLAPPrimeCore p ↥J) ⧸ Subgroup.center (↥J ⧸ GLAPPrimeCore p ↥J) ≃*
      (↥(L i) ⧸ GLAPPrimeCore p ↥(L i)) ⧸ Subgroup.center (↥(L i) ⧸ GLAPPrimeCore p ↥(L i)))

end Inputs

section Pi

theorem isPiGroup_of_center_quot_equiv {p : ℕ} {X Y : Type*} [Group X] [Group Y]
    (hX : IsPiGroup p X) (hYq : CFSG.Open.IsQuasisimple Y) (hYcore : GLAPPrimeCore p Y = ⊥)
    (e : (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y)) : IsPiGroup p Y := by
  obtain ⟨-, -, hcase⟩ := hX
  refine ⟨hYq, hYcore, ?_⟩
  rcases hcase with ⟨k, ⟨f⟩⟩ | ⟨n, ε, hn, hΩ, hfp⟩ | ⟨hp3, ⟨f⟩⟩
  · exact Or.inl ⟨k, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, ε, hn, IsOmegaTwo.of_mulEquiv e hΩ, hfp⟩)
  · exact Or.inr (Or.inr ⟨hp3, ⟨e.symm.trans f⟩⟩)

end Pi

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem B_parts_of_inputsZ {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (hI183 : Prop115.Input18_3Gen) (hI182 : Input18_3Two) (hDiag : Input18_3DiagZ)
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U)
    {b : G} (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1)
    (hBal : GLAPComponent p (Subgroup.centralizer ({b, d} : Set G)) (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))))
    (hL0core : GLAPPrimeCoreOf p L0 ≤ GLAPPrimeCoreOf p M) :
    GLAPComponent p (Subgroup.centralizer ({d} : Set G))
        (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G)),
          GLBConj g (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)))) ∧
      GLAPComponent p ((⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G)),
          GLBConj g (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)))) ⊓
          Subgroup.centralizer ({b} : Set G)) (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))) := by
  classical
  have hp : p.Prime := GLStanding.prime h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := GLStanding.ne_two h.standing
  obtain ⟨hbord, -, hbC, -, -, -, -⟩ := setting_facts h hU hb hb1
  have hdD : d ∈ D := h.hd.1
  have hdord : orderOf d = p := orderOf_eq_prime (h.hD.2.1.2 d hdD) h.hd.2
  have hcomm : b * d = d * b := (Subgroup.mem_centralizer_iff.1 hbC d (Set.mem_singleton d)).symm
  have hS := h.standing
  have hB2 := hI182 p hp hp2 G hS.simple hS.nonabelian hS.kProper b d hbord hdord hcomm _ hBal
  have hB1 : GLAPComponent p (Subgroup.centralizer ({d} : Set G))
      (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G)),
        GLBConj g (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)))) := by
    have hI1 := hI183 p hp hp2 G hS.simple hS.nonabelian hS.kProper b d hbord hdord hcomm _ hBal
    rcases hI1 with ⟨L', hL'c, hLeq, -⟩ | ⟨Lf, hLfc, hLinj, hcyc, hLfsup⟩
    · rw [hLeq]
      exact hL'c
    · exfalso
      obtain ⟨e⟩ := barOf_L0b_iso h hU hb hb1
      have hX : IsPiGroup p (↥(GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
          GLAPPrimeCore p ↥(GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)))) :=
        IsPiGroup.of_mulEquiv e.symm (isPiGroup_barOf_L0 h)
      have hLle : (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G)),
          GLBConj g (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)))) ≤ piOf p d := by
        rw [hLfsup]
        refine iSup_le fun i => ?_
        obtain ⟨eZ⟩ := hDiag p hp hp2 G hS.simple hS.nonabelian hS.kProper b d hbord hdord hcomm _
          hBal Lf hLfc hLinj hcyc hLfsup i
        have hYq := isQuasisimple_barOf_of_pComp (hLfc i)
        have hYcore : GLAPPrimeCore p (↥(Lf i) ⧸ GLAPPrimeCore p ↥(Lf i)) = ⊥ :=
          Lemma1311.glaPPrimeCore_quot_eq_bot p ↥(Lf i)
        have hPi := isPiGroup_of_center_quot_equiv hX hYq hYcore eZ
        exact le_piOf_of_comp' (hLfc i) hPi
      exact not_le_piOf_of_setting h hU hb hb1 hL0core hLle
  exact ⟨hB1, hB2⟩

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1313Z

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

theorem lemma1313_of_inputsZ
    (hI183 : Prop115.Input18_3Gen) (hI182 : Lemma1313.Input18_3Two)
    (hDiag : Lemma1313Z.Input18_3DiagZ) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T R L0 : Subgroup G} {d : G}
      (h : Cex1310 G m p B M E A D T R L0 d)
      {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) {b : G} (hb : b ∈ centBar p U (L1of p M D L0))
      (hb1 : b ≠ 1)
      (hBal : GLAPComponent p (Subgroup.centralizer ({b, d} : Set G))
        (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))))
      (hL0core : GLAPPrimeCoreOf p L0 ≤ GLAPPrimeCoreOf p M)
      (hi : ∃ S : Set (Subgroup G), (∀ X ∈ S, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) X) ∧
        GLAPLayer p (L1of p M D L0 ⊓ Subgroup.centralizer ({b} : Set G)) = ⨆ X ∈ S, X),
    let L1b := GLAPLayer p (L1of p M D L0 ⊓ Subgroup.centralizer ({b} : Set G))
    let L0b := GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))
    let L := ⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G)), GLBConj g L0b
    (∃ S : Set (Subgroup G), (∀ X ∈ S, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) X) ∧
        L1b = ⨆ X ∈ S, X) ∧
      (GLAPComponent p (Subgroup.centralizer ({d} : Set G)) L ∧
        GLAPComponent p (L ⊓ Subgroup.centralizer ({b} : Set G)) L0b ∧
        ∀ L' : Subgroup G, GLAPComponent p (Istar p M D) L' → Nonempty (barOf p L0b ≃* barOf p L')) ∧
      ¬ L ≤ M ∧ ¬ L ≤ piOf p d := by
  intro G _ _ m p B M E A D T R L0 d h U hU b hb hb1 hBal hL0core hi
  intro L1b L0b L
  obtain ⟨hB1, hB2⟩ := Lemma1313Z.B_parts_of_inputsZ hI183 hI182 hDiag h hU hb hb1 hBal hL0core
  refine ⟨hi, ⟨hB1, hB2, ?_⟩, Lemma1313.not_le_M_of_setting h hU hb hb1 hL0core hB1,
    Lemma1313.not_le_piOf_of_setting h hU hb hb1 hL0core⟩
  intro L' hL'
  obtain ⟨e⟩ := Lemma1313.barOf_L0b_iso h hU hb hb1
  obtain ⟨e'⟩ := h.hL0iso L' hL'
  exact ⟨e.trans e'⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
