module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cLang
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


theorem kd147c_layer_ne_bot {K : Type} [Field K] [Finite K] (hpK : ¬ 3 ∣ Nat.card K)
    (hq4 : 4 ≤ Nat.card K) {S : Type} [Group S] [Finite S]
    (e : ↥(adjointGroup Tag.G2 K) ≃* S) (z : S) (hz : orderOf z = 3) :
    GLAPLayer 3 (Subgroup.centralizer ({z} : Set S)) ≠ ⊥ := by
  have hx : orderOf (e.symm z) = 3 := by rw [MulEquiv.orderOf_eq]; exact hz
  obtain ⟨R, hR, h3⟩ := kd147c_component hpK hq4 (e.symm z) hx
  haveI : Finite ↥(adjointGroup Tag.G2 K) := Finite.of_equiv S e.symm.toEquiv
  have hker : Nat.Coprime 3 (Nat.card ↥(Subgroup.centralizer ({e.symm z} : Set _) ⊓
      (e : ↥(adjointGroup Tag.G2 K) →* S).ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hmap := glaPComponent_map Nat.prime_three (e : ↥(adjointGroup Tag.G2 K) →* S) hker hR
  have hcen : (Subgroup.centralizer ({e.symm z} : Set _)).map
      (e : ↥(adjointGroup Tag.G2 K) →* S) = Subgroup.centralizer ({z} : Set S) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      have := congrArg e hc
      simpa using this
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      simpa using hy
  rw [hcen] at hmap
  intro hbot
  have hle : R.map (e : ↥(adjointGroup Tag.G2 K) →* S) ≤
      GLAPLayer 3 (Subgroup.centralizer ({z} : Set S)) := le_sSup hmap
  rw [hbot, le_bot_iff] at hle
  have hcard : Nat.card R = 1 := by
    rw [← Subgroup.card_map_of_injective (f := (e : ↥(adjointGroup Tag.G2 K) →* S)) e.injective,
      hle, Subgroup.card_bot]
  rw [hcard] at h3
  omega

theorem kd147c_g2_of_catalog {T : Type} [Group T] (h : catalogIs T (onLie isG2Big)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid),
      2 < q.card ∧ ¬ 3 ∣ q.card ∧
        Nonempty (T ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | G2 q =>
    obtain ⟨h1, h2⟩ := hP
    exact ⟨q, hv, h1, h2, ⟨e⟩⟩
  | _ => exact hP.elim

theorem kd147_clause_c (S : Type) [Group S] [Finite S] (hS : catalogIs S (onLie isG2Big)) :
    ∀ z : S, orderOf z = 3 → GLAPLayer 3 (Subgroup.centralizer ({z} : Set S)) ≠ ⊥ := by
  obtain ⟨q, hv, h2q, hq3, ⟨eS⟩⟩ := kd147c_g2_of_catalog hS
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨eQ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
    (GaloisField q.p q.exponent) hK
  have hZ : Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup
      CFSG.Blueprint.Chevalley.Tag.G2 (GaloisField q.p q.exponent)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := CFSG.Blueprint.Chevalley.Tag.G2)
      (K := GaloisField q.p q.exponent)
  let e := ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    (eQ.trans eS.symm)
  have hpK : ¬ 3 ∣ Nat.card (GaloisField q.p q.exponent) := by rw [hK]; exact hq3
  have hq4 : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hK]
    by_contra hlt
    have h3 : q.card = 3 := by omega
    exact hq3 (by rw [h3])
  intro z hz
  exact kd147c_layer_ne_bot hpK hq4 (S := S) e z hz

theorem kd147_holds : KD147 :=
  kd147_of_clause_c fun S _ _ hS => kd147_clause_c S hS

end CFSG.LocalAnalysis.GLTheoremA
