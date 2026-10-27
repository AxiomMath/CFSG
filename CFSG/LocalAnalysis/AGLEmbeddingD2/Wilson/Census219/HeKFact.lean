module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeTc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.SylowExp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Facts
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensus

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21
  Subgroup Equiv

section HeLevel

set_option linter.unusedSectionVars false


@[expose] noncomputable def heY : heP := ⟨bOf heThreeWordsA, bOf_mem⟩

theorem he_centralizer_map :
    (centralizer ({heY} : Set heP)).map heP.subtype = heTcQ := by
  rw [CFSG.AGLEmbeddingD2.Wilson.ThreeCore.map_subtype_centralizer, heTcQ_eq, centralizerIn]
  rfl

theorem he_layer :
    CFSG.inSubgroup CFSG.layer (centralizer ({heY} : Set heP)) = centralizer ({heY} : Set heP) ∧
      Nonempty (↥(centralizer ({heY} : Set heP)) ≃* ↥heTcQ) ∧
        CFSG.RankThree.PartTwo.Sec4.IsTripleCover ↥heTcQ (alternatingGroup (Fin 7)) := by
  let e : ↥(centralizer ({heY} : Set heP)) ≃* ↥heTcQ :=
    ((centralizer ({heY} : Set heP)).equivMapOfInjective heP.subtype
      heP.subtype_injective).trans (MulEquiv.subgroupCongr he_centralizer_map)
  have hq : CFSG.IsQuasisimple ↥(centralizer ({heY} : Set heP)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm heTc_spec.2.1
  exact ⟨Proving.inSubgroup_layer_eq_self hq, ⟨e⟩, heTc_spec.2.2⟩

theorem card_centralizer_heP (y : heP) :
    Nat.card ↥(centralizer ({y} : Set heP)) =
      Nat.card ↥(centralizerIn heP (y : Perm (Fin 8330))) := by
  rw [← Subgroup.card_map_of_injective (f := heP.subtype) heP.subtype_injective,
    CFSG.AGLEmbeddingD2.Wilson.ThreeCore.map_subtype_centralizer, centralizerIn]

theorem he_pow_three {y : heP} {k : ℕ} (hy : y ^ 3 ^ k = 1) : y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : Nat.card (heSylS.subgroupOf heP) = 3 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe heSylS_le_heP).toEquiv, card_heSylS]
    norm_num
  refine pow_eq_one_of_pPower_of_exp 3 3 _ hQ (by rw [card_heP]; norm_num) (fun q hq => ?_) hy
  apply Subtype.ext
  simpa using heSyl_exp (Subgroup.mem_subgroupOf.1 hq)

theorem he_sylow : (27 : ℕ) = 3 ^ (4030387200 : ℕ).factorization 3 := by
  rw [show (4030387200 : ℕ) = 3 ^ 3 * 149273600 by norm_num,
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  norm_num

theorem ks219He : KS219He := by
  intro X _ _ ⟨e⟩ x hx1 hxc
  obtain ⟨S, hScard, hSC, k, hk⟩ := isCentral218_data hxc
  let e' : X ≃* heP := e.trans heEquivP
  have hcardX : Nat.card X = 4030387200 := by rw [Nat.card_congr e'.toEquiv, card_heP]
  have hb3 : (e' x) ^ 3 = 1 := he_pow_three (k := k) (by rw [← map_pow, hk, map_one])
  have hb1 : e' x ≠ 1 := fun h => hx1 (e'.injective (h.trans (map_one e').symm))
  have hord : orderOf ((e' x : heP) : Perm (Fin 8330)) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hb3 hb1
  rcases three_conj_cases (e' x).2 hord with ⟨c, hc, hcx⟩ | ⟨c, hc, hcx⟩
  ·
    let φ : X ≃* heP := e'.trans (MulAut.conj (⟨c, hc⟩ : heP)⁻¹)
    have hφ : φ x = heY := by
      apply Subtype.ext
      show c⁻¹ * ((e' x : heP) : Perm (Fin 8330)) * c = bOf heThreeWordsA
      rw [hcx]
      group
    obtain ⟨hlayer, ⟨e''⟩, hQ⟩ := he_layer
    refine ks219_transport φ x (K := centralizer ({heY} : Set heP))
      (by rw [hφ]; exact hlayer) ?_ e'' hQ
    rw [hφ]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  ·
    exfalso
    let φ : X ≃* heP := e'.trans (MulAut.conj (⟨c, hc⟩ : heP)⁻¹)
    have hφ : (φ x : Perm (Fin 8330)) = bOf heThreeWordsB := by
      show c⁻¹ * ((e' x : heP) : Perm (Fin 8330)) * c = bOf heThreeWordsB
      rw [hcx]
      group
    have h27 : 27 ∣ Nat.card ↥(centralizer ({x} : Set X)) := by
      have := Subgroup.card_dvd_of_le hSC
      rwa [hScard, hcardX, ← he_sylow] at this
    have hcard : Nat.card ↥(centralizer ({x} : Set X)) = 504 := by
      calc Nat.card ↥(centralizer ({x} : Set X))
          = Nat.card ↥((centralizer ({x} : Set X)).map φ.toMonoidHom) :=
            (Subgroup.card_map_of_injective φ.injective).symm
        _ = Nat.card ↥(centralizer ({φ x} : Set heP)) := by
            rw [Proving.centralizer_map_mulEquiv_wilson φ x]
        _ = Nat.card ↥(centralizerIn heP (φ x : Perm (Fin 8330))) := card_centralizer_heP _
        _ = 504 := by rw [hφ]; exact card_cent_B
    rw [hcard] at h27
    exact absurd h27 (by norm_num)

end HeLevel

end CFSG.AGLEmbeddingD2.Wilson.Census219
