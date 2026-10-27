module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabStated
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem TauCeti.GLSymplecticFin

section Sp

variable {n : ℕ} {F : Type} [Field F]

theorem corootVec_pow_eq_one (k : Fin n) {c : Fˣ} {M : ℕ} (hc : c ^ M = 1) :
    corootVec n F k c ^ M = 1 := by
  funext a
  simp only [corootVec, Pi.pow_apply, Pi.one_apply]
  split_ifs
  · exact hc
  · rw [inv_pow, hc, inv_one]
  · exact one_pow M

theorem torus_pow_eq_one_sp [Finite F] (k : Fin n) {g : StatedSp n F} (hg : g ∈ torus n F k) :
    g ^ (Nat.card F - 1) = 1 := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
  have hy1 : y ^ (Nat.card F - 1) = 1 := by
    refine pow_eq_one_of_mem_closure ?_ ?_ hy
    · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ _
      exact (Commute.all (corootVec n F k c) (corootVec n F k c')).map diagonal
    · rintro _ ⟨c, rfl⟩
      rw [← map_pow, corootVec_pow_eq_one k (unit_pow_card_sub_one c), map_one]
  rw [← map_pow, hy1, map_one]

theorem borelQuotient_sp [Finite F] [CharP F 2] {Y : Type} [Group Y]
    (e : Y ≃* StatedProj (StatedSp n F)) :
    BorelQuotient (rootDatum n F) (weylRep n F) (torus n F)
      (e.symm.toMonoidHom.comp (QuotientGroup.mk' _)) (Nat.card F - 1) :=
  borelQuotient_of_stated e (isCTGroupDatum n F) (steinbergExtras n F)
    (fun _ hγ => isPGroup_of_isParametrization Sp.isParametrization hγ)
    (fun k _ hg => torus_pow_eq_one_sp k hg)

theorem hasSL2Node_sp (i : Fin n) : HasSL2Node (rootDatum n F) i F := by
  obtain ⟨φ, hφ, hx, hy⟩ := Sp.rankOne (F := F) i
  have hpar := Sp.isParametrization (n := n) (F := F)
  have hα : (Pi.single i 1 : Fin n → ℤ) ∈ (rootDatum n F).roots :=
    (RootSystem.ofCartan (rootDatum n F).isFiniteType (rootDatum n F).divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin n → ℤ) ∈ (rootDatum n F).roots :=
    (RootSystem.ofCartan (rootDatum n F).isFiniteType (rootDatum n F).divisible).neg_mem _ hα
  refine ⟨φ, hφ, fun c => ?_, fun c => ?_⟩
  · rw [hx c]
    exact ((hpar _ hα).1 _).2 ⟨c, rfl⟩
  · rw [hy c]
    exact ((hpar _ hα').1 _).2 ⟨c, rfl⟩

theorem threeDvd_sp [Finite F] [CharP F 2] {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSp n F)) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J :=
  (borelQuotient_sp e).three_dvd_card (fun i => (hasSL2Node_sp i).hasOrderThree) T J hNJ hJ

end Sp

theorem threeDvd_of_model_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact threeDvd_sp e T J hNJ hJ

end CFSG.AGLEmbedding.ParabHub
