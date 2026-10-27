module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeEscape
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeFix
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeG2
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.ToralCensus
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem g2_nodes {i k : Fin (Tag.rank .G2)} (hik : i ≠ k) :
    ((i = ⟨0, by decide⟩ ∧ k = ⟨1, by decide⟩) ∨ (i = ⟨1, by decide⟩ ∧ k = ⟨0, by decide⟩)) ∧
      ∀ c : Fin (Tag.rank .G2), c ≠ k → c = i := by
  revert i k
  decide

section G2


theorem centralizerEscapes_g2 {F : Type} [Field F] [Finite F] [CharP F 2] {X : Type} [Group X]
    [Finite X] (e : X ≃* AdjointQuotient .G2 F) (hq4 : 4 ≤ Nat.card F) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CentralizerEscapes p X := by
  intro S J hNJ hJN hJtop _ u hu hup _
  have : Finite ↥(adjointGroup .G2 F) := generated_group_finite .G2 F
  have h := borelQuotient_g2 e
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq S
  have hQ : BorelQuotient (g2Datum F) (weylElement .G2 F) (torus (τ := .G2) F) π'
      (Nat.card F - 1) :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel (g2Datum F) (torus (τ := .G2) F)).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  have hBA : borel (g2Datum F) (torus (τ := .G2) F) ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hne : J.comap π' ≠ borel (g2Datum F) (torus (τ := .G2) F) := by
    intro he
    apply hJN
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i, hi⟩ := negIndices_nonempty_of_ne hQ.ct hQ.extras hBA hne
  obtain ⟨k, hk⟩ := LieOut.exists_node_not_mem_negIndices hQ hBJ hJtop
  have hik : i ≠ k := fun e => hk (e ▸ hi)
  obtain ⟨hcase, hrest⟩ := g2_nodes hik
  have hI : negIndices (g2Datum F) (J.comap π') = {i} := by
    ext c
    exact ⟨fun hc => hrest c fun e => hk (e ▸ hc), fun hc => hc ▸ hi⟩
  obtain ⟨g, hg, hgu⟩ := exists_conj_mem_rankOne_of_single hQ hBJ hI hp hp2 hu hup
  refine ⟨g, hg, ?_⟩
  have h01 : (⟨0, by decide⟩ : Fin (Tag.rank .G2)) ≠ ⟨1, by decide⟩ := by decide
  have h1 : (g2Datum F).cartan (⟨0, by decide⟩ : Fin (Tag.rank .G2))
      (⟨1, by decide⟩ : Fin (Tag.rank .G2)) = -1 := rfl
  have h2 : (g2Datum F).cartan (⟨1, by decide⟩ : Fin (Tag.rank .G2))
      (⟨0, by decide⟩ : Fin (Tag.rank .G2)) = -3 := rfl
  have hD : (g2Datum F).divisible = ∅ := rfl
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨P, hP, hPc, hPJ⟩ := exists_escape_of_witness hQ hBJ hk
      ((actsAs_n hQ.ct _).mul (actsAs_n hQ.ct _))
      (by rw [weylAction_gTwo_long h1 h2]; simp [pair_apply])
      ((rankOneNode_g2 _).perfect hq4)
      (commutes_rankOne_gTwo_long hQ.ct hQ.extras hD h01 h1 h2) hgu
    exact ⟨P, hP, fun x hx => hPc x hx, hPJ⟩
  · obtain ⟨P, hP, hPc, hPJ⟩ := exists_escape_of_witness hQ hBJ hk
      ((actsAs_n hQ.ct _).mul (actsAs_n hQ.ct _))
      (by rw [weylAction_gTwo_short h1 h2]; simp [pair_apply])
      ((rankOneNode_g2 _).perfect hq4)
      (commutes_rankOne_gTwo_short hQ.ct hQ.extras hD h01 h1 h2) hgu
    exact ⟨P, hP, fun x hx => hPc x hx, hPJ⟩

theorem centralizerEscapes_of_isLieOf_g2 {X : Type} [Group X] [Finite X] (hX : IsLieOf IdxG2 X)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CentralizerEscapes p X := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  cases d with
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hq4 : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
      rw [hK, TauCeti.PrimePower.card_def, hd]
      rw [TauCeti.PrimePower.card_def, hd] at hq3
      have hf : 2 ≤ q.exponent := by
        by_contra hf
        have : q.exponent = 1 := by have := q.exponent_pos; omega
        rw [this] at hq3
        omega
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
    exact centralizerEscapes_g2 (e.trans b.symm) hq4 hp hp2
  | _ => exact hd.elim

theorem fixThreeVoid_g2 : FixThreeVoid (IsLieOf IdxG2) := fun _ _ _ _ _ _ h hL =>
  h.false_of_escapes (centralizerEscapes_of_isLieOf_g2 hL Nat.prime_three (by norm_num))

theorem fixPrimeCyc_g2 : FixPrimeCyc (IsLieOf IdxG2) := fun _ _ _ _ _ _ _ h hL =>
  (h.false_of_escapes (centralizerEscapes_of_isLieOf_g2 hL h.prime
    (by have := h.five_le; omega))).elim

end G2

end CFSG.AGLEmbedding
