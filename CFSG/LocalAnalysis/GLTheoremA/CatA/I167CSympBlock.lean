module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CSympLieComps
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

private theorem i167CS_block_aux1 {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    {X J : Subgroup S} (hJ : GLAPComponent p X J) (hcomp : CFSG.Open.IsComponentOf J X) :
    Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* PSimple p J) := by
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hO : GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J := by
    by_cases htop : GLAPPrimeCore p ↥J = ⊤
    · exfalso
      haveI := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial hq
      obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot p J)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (QuotientGroup.eq.2 (htop ▸ Subgroup.mem_top _))
    · exact CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hcomp.2.2
        inferInstance htop
  let π : ↥J →* PQuot p J := QuotientGroup.mk' (GLAPPrimeCore p ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker ≤ Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk']
    exact hO
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv hcomp.2.2.1 π hπ hπk

private theorem i167CS_block_aux2 {K : Type} [Field K] [Finite K] {n m p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (x : StatedSp m K) (hx : x ^ p = 1)
    {J : Subgroup (StatedProj (StatedSp m K))}
    (hJ : GLAPComponent p (fixSubgroup (MulAut.conj (proj m K x))) J) :
    ∃ (X : Type) (inst : Group X) (_ : Finite X),
      letI := inst
      I167CSpFactor p 2 (Nat.card K) K X ∧
      Nonempty (PQuot p J ⧸ Subgroup.center (PQuot p J) ≃* X ⧸ Subgroup.center X) := by
  classical
  obtain ⟨hPIL, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsCore_conj_sp_card (a6 := False)
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds
      (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
      hp hp2 Nat.prime_two hn hK hm hp2 (fun h => h.elim) x hx
  have hcompR := i167CS_lieComps
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds hp hp2 hn hK hm x hx
  have hperfJ := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle := hPIL J hJ.1 hperfJ
  have hJcomp : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x))) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hJle).1
  obtain ⟨X, inst, hXfin, hXLie, hfac, f, hf, hker⟩ := hcompR J hJcomp
  letI := inst
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hXLie.perfect f hf hker
  obtain ⟨eP⟩ := i167CS_block_aux1 hp hJ hJcomp
  have eJP : PQuot p J ⧸ Subgroup.center (PQuot p J) ≃* X ⧸ Subgroup.center X := eP.symm.trans eJ
  exact ⟨X, inst, hXfin, hfac, ⟨eJP⟩⟩

private theorem i167CS_block_aux3 {K : Type} [Field K] {n m p : ℕ}
    {J : Subgroup (StatedProj (StatedSp m K))} (hK : Nat.card K = 2 ^ n) (hp : p.Prime)
    {X : Type} [Group X]
    (eJP : PQuot p J ⧸ Subgroup.center (PQuot p J) ≃* X ⧸ Subgroup.center X)
    (hSL : ∃ (a j : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 2 ≤ a ∧ 1 ≤ j ∧
      ringChar E = 2 ∧ Fintype.card E = Nat.card K ^ j ∧ (a = 2 → 4 ≤ Fintype.card E) ∧
      (a = 2 ∨ p ∣ Fintype.card E - 1) ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin a) E)) :
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ k ∧
        (a = 2 ∨ p ∣ 2 ^ k - 1) ∧ Nonempty (PSimple p J ≃* StatedProj (StatedSL a E))) ∨
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
        (hτ : ∀ y, τ (τ y) = y), 2 ≤ a ∧ (∀ y, τ y = y ^ 2 ^ k) ∧ Nat.card E = (2 ^ k) ^ 2 ∧
        Nonempty (PSimple p J ≃* heldSU a E τ hτ ⧸ Subgroup.center (heldSU a E τ hτ))) ∨
    (∃ s : ℕ, 2 ≤ s ∧ ¬ (s = 2 ∧ Nat.card K = 2) ∧
        Nonempty (PSimple p J ≃* StatedProj (StatedSp s K))) ∨
    (Nat.card K = 2 ∧ Nat.card (PSimple p J) ≤ 720) := by
  obtain ⟨a, j, E, hEfield, hEf, ha2, -, -, hcardE, -, hdvd, ⟨eX⟩⟩ := hSL
  letI := hEfield
  letI := hEf
  have hcard : Fintype.card E = 2 ^ (n * j) := by rw [hcardE, hK, pow_mul]
  obtain ⟨eXZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl (a := a) eX
  refine Or.inl ⟨a, n * j, E, inferInstance, inferInstance, ha2, ?_, ?_, ⟨eJP.trans eXZ⟩⟩
  · rw [Nat.card_eq_fintype_card, hcard]
  · rcases hdvd with h2 | hd
    · exact Or.inl h2
    · exact Or.inr (by rw [hcard] at hd; exact hd)

private theorem i167CS_block_aux4 {K : Type} [Field K] [Finite K] {m p : ℕ}
    {J : Subgroup (StatedProj (StatedSp m K))} {X : Type} [Group X] [Finite X]
    (eJP : PQuot p J ⧸ Subgroup.center (PQuot p J) ≃* X ⧸ Subgroup.center X)
    (hK2 : Nat.card K = 2)
    (eA : X ≃* ↥(commutator (StatedSp 2 K))) :
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ k ∧
        (a = 2 ∨ p ∣ 2 ^ k - 1) ∧ Nonempty (PSimple p J ≃* StatedProj (StatedSL a E))) ∨
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
        (hτ : ∀ y, τ (τ y) = y), 2 ≤ a ∧ (∀ y, τ y = y ^ 2 ^ k) ∧ Nat.card E = (2 ^ k) ^ 2 ∧
        Nonempty (PSimple p J ≃* heldSU a E τ hτ ⧸ Subgroup.center (heldSU a E τ hτ))) ∨
    (∃ s : ℕ, 2 ≤ s ∧ ¬ (s = 2 ∧ Nat.card K = 2) ∧
        Nonempty (PSimple p J ≃* StatedProj (StatedSp s K))) ∨
    (Nat.card K = 2 ∧ Nat.card (PSimple p J) ≤ 720) := by
  refine Or.inr (Or.inr (Or.inr ⟨hK2, ?_⟩))
  have h1 : Nat.card (X ⧸ Subgroup.center X) ≤ Nat.card X :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card X ≤ Nat.card ↥(commutator (StatedSp 2 K)) := (Nat.card_congr eA.toEquiv).le
  have h3 : Nat.card ↥(commutator (StatedSp 2 K)) ≤ Nat.card (StatedSp 2 K) :=
    Nat.card_le_card_of_injective (fun y : ↥(commutator (StatedSp 2 K)) => (y : StatedSp 2 K))
      Subtype.val_injective
  have h4 : Nat.card (StatedSp 2 K) = 720 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hK2]
    norm_num
  have h5 : Nat.card (PSimple p J) = Nat.card (X ⧸ Subgroup.center X) :=
    Nat.card_congr eJP.toEquiv
  omega

theorem i167CS_block {K : Type} [Field K] [Finite K] {n m p : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) (x : StatedSp m K) (hx : x ^ p = 1)
    {J : Subgroup (StatedProj (StatedSp m K))}
    (hJ : GLAPComponent p (fixSubgroup (MulAut.conj (proj m K x))) J) :
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ k ∧
        (a = 2 ∨ p ∣ 2 ^ k - 1) ∧ Nonempty (PSimple p J ≃* StatedProj (StatedSL a E))) ∨
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
        (hτ : ∀ y, τ (τ y) = y), 2 ≤ a ∧ (∀ y, τ y = y ^ 2 ^ k) ∧ Nat.card E = (2 ^ k) ^ 2 ∧
        Nonempty (PSimple p J ≃* heldSU a E τ hτ ⧸ Subgroup.center (heldSU a E τ hτ))) ∨
    (∃ s : ℕ, 2 ≤ s ∧ ¬ (s = 2 ∧ Nat.card K = 2) ∧
        Nonempty (PSimple p J ≃* StatedProj (StatedSp s K))) ∨
    (Nat.card K = 2 ∧ Nat.card (PSimple p J) ≤ 720) := by
  classical
  obtain ⟨X, inst, hXfin, hfac, ⟨eJP⟩⟩ := i167CS_block_aux2 hK hn hm hp hp2 x hx hJ
  letI := inst
  letI := hXfin
  unfold I167CSpFactor at hfac
  rcases hfac with hSL | hSU | hSp | hSp42
  ·
    exact i167CS_block_aux3 hK hp eJP hSL
  ·
    rw [hK] at hSU
    exact Or.inr (Or.inl (by
      obtain ⟨a, k, E, hE, hEf, τ, hτ, ha2, hτk, hEc, -, h⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.uniCase_of_factor eJP hSU
      exact ⟨a, k, E, hE, hEf, τ, hτ, ha2, hτk, hEc, h⟩))
  ·
    obtain ⟨-, -, s, hs2, hne, ⟨eX⟩⟩ := hSp
    have hne' : ¬(s = 2 ∧ Nat.card K = 2) := fun h => hne (by rw [h.1, h.2])
    have hchar : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
    obtain ⟨eXZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp (s := s)
      hs2 hne' hchar eX
    exact Or.inr (Or.inr (Or.inl ⟨s, hs2, hne', ⟨eJP.trans eXZ⟩⟩))
  ·
    obtain ⟨-, -, hK2, ⟨eA⟩⟩ := hSp42
    exact i167CS_block_aux4 eJP hK2 eA

end CFSG.LocalAnalysis.GLTheoremA.I167

end
