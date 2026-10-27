module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightLin
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived
  exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (perfectInLayer_primeFormConjHom)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

local notation "fixSub" => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup

theorem lieSEight_orderTwistedA_ne {r g : ℕ} (hr : 2 ≤ r) (hg : 1 ≤ g) :
    orderTwistedA r (2 ^ g) ≠ 1056706560 := by
  intro h
  have hQ : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have h2 : ordTwistedA r (2 ^ g) = orderTwistedA r (2 ^ g) := by
    unfold ordTwistedA orderTwistedA
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : 1 ≤ (2 ^ g) ^ i := Nat.one_le_pow _ _ hQ
    have hc : (((2 ^ g) ^ i : ℕ) : ℤ) = ((2 ^ g : ℕ) : ℤ) ^ i := Nat.cast_pow _ i
    rcases Nat.even_or_odd i with hi | hi
    · rw [if_pos hi, hi.neg_one_pow]
      omega
    · rw [if_neg (Nat.not_even_iff_odd.2 hi), hi.neg_one_pow]
      omega
  refine CFSG.SeitzReduction.SymplecticPilot.ordTwistedA_ne_ordBC (u := r) (g := g) (m := 2)
    (f := 3) hr hg le_rfl (by norm_num) ?_
  rw [h2, h, show ordBC 2 (2 ^ 3) = 1056706560 by decide +kernel]

theorem lieSEight_suQuot_card_ne (hLO : LieOrderBridge) {X : Type} [Group X] [Finite X]
    {E : Type} [Field E] [Fintype E] {m Q g : ℕ} (hQ : Q = 2 ^ g) (hm : 3 ≤ m) (hg : 1 ≤ g)
    (hE : Fintype.card E = Q ^ 2) (hne : (m, Q) ≠ (3, 2))
    (f : ↥(StatedSU m Q E) →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center ↥(StatedSU m Q E)) :
    Nat.card (X ⧸ Subgroup.center X) ≠ 1056706560 := by
  intro hc
  obtain ⟨q, hv, -, hqc, ⟨eU⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU hE hm hne
  have hperf := (suFactorFacts_holds E m Q hE hm hne).perfect
  obtain ⟨eJ⟩ := nonempty_centralQuotient_mulEquiv hperf f hf hker
  have h1 := hLO ⟨.twistedA (m - 1) q, hv⟩ (X ⧸ Subgroup.center X) ⟨eJ.symm.trans eU⟩
  change Nat.card _ = orderTwistedA (m - 1) q.card at h1
  rw [hc, hqc, hQ] at h1
  exact lieSEight_orderTwistedA_ne (r := m - 1) (g := g) (by omega) hg h1.symm

theorem lieSEightNoAt_unitary (hLO : LieOrderBridge) :
    LieSEightNoAt fun d => ∃ n q, d = .twistedA n q := by
  rintro Y _ _ hY - - d ⟨n, q, hdq⟩ hc hf ⟨e⟩ α hα hα3 - ⟨J, hJ, hT⟩
  have hU : KD264Lie.isUnitaryIdx d.1 := by rw [hdq]; trivial
  obtain ⟨r, q', K, hKf, h, hr, hd', hne, ⟨eP⟩⟩ :=
    KD264Lie.exists_primeFormP_mulEquiv_of_isUnitaryIdx hU
  have hq8 : q'.card = 8 := by
    have := hf
    rw [hd'] at this
    exact this
  have hp2 : q'.p = 2 := by
    have := hc
    rw [hd', TauCeti.LieTypeIndex.characteristic_twistedA] at this
    exact this
  have hexp : q'.exponent = 3 := by
    have h8 := q'.card_def
    rw [hq8, hp2] at h8
    exact Nat.pow_right_injective (le_refl 2) (h8.symm.trans (by norm_num : 8 = 2 ^ 3))
  let θ : Y ⧸ Subgroup.center Y ≃* primeFormP h (idGram K (r + 1)) := e.trans eP.symm
  haveI : Finite (primeFormP h (idGram K (r + 1))) := Finite.of_equiv _ θ.toEquiv
  have hβmem : MulAut.congr θ α ∈ innAutDerived (primeFormP h (idGram K (r + 1))) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hα
  have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hq' : ¬(r + 1 = 3 ∧ q'.p ^ q'.exponent = 2) := by
    rintro ⟨h1, h2⟩
    exact hne ⟨h1, by rw [TauCeti.PrimePower.card_def]; exact h2⟩
  obtain ⟨A, c, -, hA, hβeq⟩ :=
    exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived h isPrimeFormGram_idGram (by omega)
      hq' hβmem hβ3
  have hpℓ : 3 ≠ q'.p := by rw [hp2]; norm_num
  have hJ' : GLAPComponent 3 (fixSub (primeFormConjHom h (idGram K (r + 1)) A))
      (J.map θ.toMonoidHom) := by
    rw [← hβeq]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_transport θ α hJ
  have hpil := perfectInLayer_primeFormConjHom h Nat.prime_three hpℓ A hA
  have hJle := hpil _ hJ'.1 (glaPComponent_perfect hJ')
  have hcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJ' hJle).1
  obtain ⟨dd, hdd, hcase⟩ :=
    exists_field_factor_of_component_primeFormConjHom (h := h) Nat.prime_three hpℓ A hA _ hcomp
  have hT' : catalogIs (PSimple 3 (J.map θ.toMonoidHom)) S8.L84.isSp48 :=
    (CFSG.LocalAnalysis.GLTheoremA.T123C.catalogIs_pSimple_map_iff (f := θ.toMonoidHom)
      θ.injective 3 J _).2 hT
  have hcardJ := lieSEight_card_quot_center hLO hJ' hcomp.2.2 hT'
  rcases hcase with
      ⟨F, hF, hFt, -, hcardF, -, g, hg, hk⟩ |
      ⟨E, hE, hEt, m, -, hcardE, hm, hne', g, hg, hk⟩ |
      ⟨E, hE, hEt, m, -, hcardE, hm2, -, g, hg, hk⟩
  · letI : Field F := hF
    letI : Fintype F := hFt
    rw [hp2, hexp] at hcardF
    exact lieSEight_slQuot_card_ne hLO le_rfl (by omega) hcardF g hg hk hcardJ
  · letI : Field E := hE
    letI : Fintype E := hEt
    have hQ : q'.p ^ (q'.exponent * dd) = 2 ^ (3 * dd) := by rw [hp2, hexp]
    exact lieSEight_suQuot_card_ne hLO hQ hm (by omega) hcardE hne' g hg hk hcardJ
  · letI : Field E := hE
    letI : Fintype E := hEt
    rw [hp2, hexp] at hcardE
    exact lieSEight_slQuot_card_ne hLO hm2 (g := 2 * (3 * dd)) (by omega) hcardE g hg hk hcardJ

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
