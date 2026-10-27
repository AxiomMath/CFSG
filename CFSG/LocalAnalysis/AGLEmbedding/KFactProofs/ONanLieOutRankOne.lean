module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
open CFSG.LieType.Universal.Unitary
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)

section Rank

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem eq_map_borel_of_rank_one (h : BorelQuotient D n H π M) (hr : D.rank = 1)
    {J : Subgroup Y} (hBJ : (borel D H).map π ≤ J) (hJ : J ≠ ⊤) :
    J = (borel D H).map π := by
  obtain ⟨j, hj⟩ := exists_node_not_mem_negIndices h hBJ hJ
  have hneg : negIndices D (J.comap π) = ∅ := by
    ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    have : i = j := Fin.ext (by have := i.2; have := j.2; omega)
    exact hj (this ▸ hi)
  calc J = (borel D H).map π ⊔ ⨆ i ∈ negIndices D (J.comap π), (rankOne D.rootGroup i).map π :=
        eq_map_borel_sup_of_le h.ct h.extras h.surj hBJ
    _ = (borel D H).map π := by rw [hneg]; simp

end Rank

@[expose] def BorelMaximal (Y : Type*) [Group Y] : Prop :=
  ∀ (S : Sylow 2 Y) (J : Subgroup Y), Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤ J →
    J ≠ ⊤ → J = Subgroup.normalizer ((S : Subgroup Y) : Set Y)

theorem borelMaximal_of_borelQuotient {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y]
    {D : CFSG.LieType.Universal.UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ} (h : BorelQuotient D n H π M)
    (hr : D.rank = 1) : BorelMaximal Y := by
  intro S J hNJ hJ
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq S
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  rw [hNπ]
  exact eq_map_borel_of_rank_one hQ hr (hNπ ▸ hNJ) hJ

theorem borelMaximal_of_model_psl_two {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (h : StatedClassicalModel Y .PSL 2 2 f) : BorelMaximal Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact borelMaximal_of_borelQuotient
    (borelQuotient_sl (m := 1) ((projectiveSpecialLinearGroupEquivStatedProj 2 F).trans e.symm))
    rfl

theorem borelMaximal_of_model_psu_three {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (h : StatedClassicalModel Y .PSU 3 2 f) : BorelMaximal Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  exact borelMaximal_of_borelQuotient (borelQuotient_su hcard (by omega) ζ hζ e) rfl

end CFSG.AGLEmbedding.LieOut
