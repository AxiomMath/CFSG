module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ExcLift
import CFSG.Adapters.CatalogueFieldBridges.Linear
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU4SplitThree
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

namespace ClassExc

private theorem disjoint_pairs {N : ℕ} (hN : 8 ≤ N) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint ({⟨2 * i, by omega⟩, ⟨2 * i + 1, by omega⟩} : Finset (Fin N))
      {⟨2 * j, by omega⟩, ⟨2 * j + 1, by omega⟩} := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  rcases hx with rfl | rfl <;> rcases hy with h | h <;> simp only [Fin.ext_iff] at h <;> omega

end ClassExc

open ClassExc

theorem p3At_A_of_seven_le {n : ℕ} (hn : 7 ≤ n) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A n Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set F := GaloisField Q.p Q.exponent with hFdef
  have hFcard : Nat.card F = Q.card := by
    rw [hFdef, GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hQq : Q.p = q := (TauCeti.LieTypeIndex.characteristic_A n Q).symm.trans hchar
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨E⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie (k := F) Q hv
    hFcard
  have hab : ∀ i : Fin 4, (⟨2 * i, by omega⟩ : Fin (n + 1)) ≠ ⟨2 * i + 1, by omega⟩ := fun i =>
    Fin.ne_of_val_ne (by simp)
  have hmem : ∀ (i : Fin 4) (A : SL(2, F)), CFSG.SeitzReduction.LinearPilot.pairEmbed (hab i) A ∈
      CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
        {⟨2 * i, by omega⟩, ⟨2 * i + 1, by omega⟩} := fun i A => by
    rw [← CFSG.SeitzReduction.LinearPilot.range_pairEmbed (hab i)]
    exact ⟨A, rfl⟩
  refine H.false_of_commuting_SL2 (e.trans E.symm) (F := F) ?_ ?_
    (fun i => (LinearFlag.proj (n + 1) F).comp (CFSG.SeitzReduction.LinearPilot.pairEmbed (hab i)))
    (fun i => CFSG.SeitzReduction.LinearPilot.proj_comp_pairEmbed_injective (hab i) (by omega))
    (fun i j hij A B => ?_)
  · rw [ringChar.eq F Q.p, hQq]
    exact H.two
  · rw [ringChar.eq F Q.p, hQq]
    exact H.three
  · simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul,
      (CFSG.SeitzReduction.LinearPilot.commute_blockSpecialLinear_of_disjoint
        (disjoint_pairs (by omega) hij) (hmem i A) (hmem j B)).eq]

theorem p3At_twistedA_of_seven_le {n : ℕ} (hn : 7 ≤ n) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA n Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  set d : TauCeti.ValidLieTypeIndex := ⟨.twistedA n Q, hv⟩ with hd
  set p := d.characteristic with hpdef
  set f := d.fieldExponent with hfdef
  haveI : Fact p.Prime := ⟨d.characteristic_prime⟩
  have hfQ : f = Q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA n Q
  have hpq : p = q := hchar
  have hf1 : 1 ≤ f := by rw [hfQ]; exact Q.exponent_pos
  set K := GaloisField p (2 * f) with hKdef
  have hK : UnitaryFieldData p f K := ⟨Fact.out, hf1, GaloisField.card p (2 * f) (by omega)⟩
  set e₁ := e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj n Q hv)
  obtain ⟨F, _, _, hFc, ⟨e₂⟩⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.kaU4S3_exists_su2_equiv hK
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hFc])
  have hJ : ∀ i : Fin 4, ({⟨2 * i, by omega⟩, ⟨2 * i + 1, by omega⟩} : Finset (Fin (n + 1))).card =
      2 := fun i => Finset.card_pair (Fin.ne_of_val_ne (by simp))
  choose ι hι hrange using fun i : Fin 4 =>
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.kaU4S3_block_hom hK e₂ _ (hJ i)
  have hmem : ∀ (i : Fin 4) (A : SL(2, F)), ι i A ∈ CFSG.ComponentClassification.Burgoyne.U.uBlock
      p f K {⟨2 * i, by omega⟩, ⟨2 * i + 1, by omega⟩} := fun i A => by
    rw [← hrange i]
    exact ⟨A, rfl⟩
  have hk : ∀ i : Fin 4, (⟨2 * ((i + 1 : Fin 4) : ℕ), by omega⟩ : Fin (n + 1)) ∉
      ({⟨2 * i, by omega⟩, ⟨2 * i + 1, by omega⟩} : Finset (Fin (n + 1))) := fun i => by
    have hne : (i + 1 : Fin 4) ≠ i := by
      intro h
      have := congrArg (fun x : Fin 4 => x - i) h
      simp at this
    have hne' : ((i + 1 : Fin 4) : ℕ) ≠ i := fun h => hne (Fin.ext h)
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  refine H.false_of_commuting_SL2 e₁ (F := F) ?_ ?_
    (fun i => (CFSG.ComponentClassification.Burgoyne.Proj.projH _).comp (ι i))
    (fun i => CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.kaU4S3_proj_block_injective (hk i) (ι i) (hι i)
      (hmem i)) (fun i j hij A B => ?_)
  · rw [ringChar.eq F p, hpq]
    exact H.two
  · rw [ringChar.eq F p, hpq]
    exact H.three
  · simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.kaU4S3_block_commute
      (disjoint_pairs (by omega) hij) (hmem i A) (hmem j B)]

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
