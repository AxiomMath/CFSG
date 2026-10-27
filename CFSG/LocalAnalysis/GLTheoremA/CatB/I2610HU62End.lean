module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HL2
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Indices
import CFSG.HardMathSupport.Dickson.Bal207.ExcU62
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFixInf
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33b
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6Comp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (IsTwoPow)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram isPrimeFormGram_idGram)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSUEquiv)
open CFSG.HardMathSupport.Dickson.Bal207
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher


private theorem orderTwistedA_three_two : orderTwistedA 3 2 = 25920 := by decide

private theorem orderTwistedA_four_two : orderTwistedA 4 2 = 13685760 := by decide

private theorem orderTwistedA_five_two : orderTwistedA 5 2 = 9196830720 := by decide

private theorem orderA_one_eight : orderA 1 8 = 504 := by decide

private def l28Factors : List ℕ := [2, 2, 2, 3, 3, 7]

private def u5Factors : List ℕ :=
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 11]

private def u6Factors : List ℕ :=
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 7, 11]

private theorem prime_dvd_l28 {r : ℕ} (hr : r.Prime) (h7 : 7 ≤ r) (h : r ∣ 504) :
    r = 7 ∨ r = 11 := by
  have hL : ∀ p ∈ l28Factors, Nat.Prime p := by decide
  have hN : 504 = l28Factors.prod := by decide
  have hmem := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hr)
    (fun p hp => Nat.prime_iff.mp (hL p hp)) (hN ▸ h)
  simp [l28Factors] at hmem
  omega

private theorem prime_dvd_u5 {r : ℕ} (hr : r.Prime) (h7 : 7 ≤ r) (h : r ∣ 13685760) :
    r = 7 ∨ r = 11 := by
  have hL : ∀ p ∈ u5Factors, Nat.Prime p := by decide
  have hN : 13685760 = u5Factors.prod := by decide
  have hmem := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hr)
    (fun p hp => Nat.prime_iff.mp (hL p hp)) (hN ▸ h)
  simp [u5Factors] at hmem
  omega

private theorem prime_dvd_u6 {r : ℕ} (hr : r.Prime) (h7 : 7 ≤ r) (h : r ∣ 9196830720) :
    r = 7 ∨ r = 11 := by
  have hL : ∀ p ∈ u6Factors, Nat.Prime p := by decide
  have hN : 9196830720 = u6Factors.prod := by decide
  have hmem := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hr)
    (fun p hp => Nat.prime_iff.mp (hL p hp)) (hN ▸ h)
  simp [u6Factors] at hmem
  omega

private theorem dvd_l2prime_card {r N : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r)
    (hN : N = r * (r ^ 2 - 1) / 2) : r ∣ N := by
  have hr2 : r ≠ 2 := by omega
  have hodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨k, hk⟩ := hodd
  have h2 : 2 ∣ r ^ 2 - 1 := by
    refine ⟨2 * k * (k + 1), ?_⟩
    have h1 : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by
      have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
      omega
    rw [hk]
    exact h1
  rw [hN, Nat.mul_div_assoc r h2]
  exact dvd_mul_right r _

private theorem not_catalogIs_isL2prime_of_card_eq_of_prime_dvd {X : Type} [Group X] {N : ℕ}
    (h : Nat.card X = N) (h60 : N ≠ 60)
    (hdiv : ∀ r : ℕ, r.Prime → 7 ≤ r → r ∣ N → r = 7 ∨ r = 11)
    (h168 : N ≠ 168) (h660 : N ≠ 660) : ¬ catalogIs X isL2prime := by
  intro hc
  rcases card_of_catalogIs_isL2prime hc with hN | ⟨r, hr, hr7, hN⟩
  · exact h60 (h.symm.trans hN)
  · have hdvd : r ∣ N := dvd_l2prime_card hr hr7 (h.symm.trans hN)
    rcases hdiv r hr hr7 hdvd with rfl | rfl
    · have := h.symm.trans hN
      norm_num at this
      exact h168 this
    · have := h.symm.trans hN
      norm_num at this
      exact h660 this

private theorem not_catalogIs_isL2prime_of_card_eq_504 {X : Type} [Group X]
    (h : Nat.card X = 504) : ¬ catalogIs X isL2prime :=
  not_catalogIs_isL2prime_of_card_eq_of_prime_dvd h (by norm_num) (fun r => prime_dvd_l28)
    (by norm_num) (by norm_num)

private theorem not_catalogIs_isL2prime_of_card_eq_13685760 {X : Type} [Group X]
    (h : Nat.card X = 13685760) : ¬ catalogIs X isL2prime :=
  not_catalogIs_isL2prime_of_card_eq_of_prime_dvd h (by norm_num) (fun r => prime_dvd_u5)
    (by norm_num) (by norm_num)

private theorem not_catalogIs_isL2prime_of_card_eq_u62 {X : Type} [Group X]
    (h : Nat.card X = 9196830720) : ¬ catalogIs X isL2prime :=
  not_catalogIs_isL2prime_of_card_eq_of_prime_dvd h (by norm_num) (fun r => prime_dvd_u6)
    (by norm_num) (by norm_num)

private theorem card_quot_u62 {L : Type} [Group L] [Finite L]
    {q : TauCeti.PrimePower} (hq : IsTwoPow q 1)
    {hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group) :
    Nat.card (L ⧸ Subgroup.center L) = 9196830720 := by
  have hqcard : q.card = 2 := by
    rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
    norm_num
  have h := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    ⟨.twistedA 5 q, hv⟩ (L ⧸ Subgroup.center L) ⟨e⟩
  rw [h]
  show orderTwistedA 5 q.card = 9196830720
  rw [hqcard]
  exact orderTwistedA_five_two

private theorem card_of_excU62Type {X : Type} [Group X] [Finite X] (h : ExcU62Type X) :
    Nat.card X = 25920 ∨ Nat.card X = 13685760 ∨ Nat.card X = 504 := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  have hcard : Nat.card X = lieOrderFormula d :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩ X ⟨e⟩
  cases d with
  | twistedA r q =>
    obtain ⟨hr, hq⟩ := hd
    have hqcard : q.card = 2 := by
      rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
      norm_num
    rcases hr with rfl | rfl
    · left
      rw [hcard]
      show orderTwistedA 3 q.card = 25920
      rw [hqcard]
      exact orderTwistedA_three_two
    · right; left
      rw [hcard]
      show orderTwistedA 4 q.card = 13685760
      rw [hqcard]
      exact orderTwistedA_four_two
  | A r q =>
    obtain ⟨rfl, hq⟩ := hd
    have hqcard : q.card = 8 := by
      rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
      norm_num
    right; right
    rw [hcard]
    show orderA 1 q.card = 504
    rw [hqcard]
    exact orderA_one_eight
  | _ => exact hd.elim

theorem not_catalogIs_isL2prime_of_quot_u62 {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) {q : TauCeti.PrimePower} (hq : IsTwoPow q 1)
    {hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group)
    {β : MulAut L} (hβ : β ^ 3 = 1) {J : Subgroup L}
    (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    ¬ catalogIs (PSimple 3 J) isL2prime := by
  classical
  intro hcat
  let S := L ⧸ Subgroup.center L
  let π : L →* S := QuotientGroup.mk' (Subgroup.center L)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker ≤ Subgroup.center L := by
    rw [show π.ker = (QuotientGroup.mk' (Subgroup.center L)).ker from rfl,
      QuotientGroup.ker_mk']
  haveI hSsimple : IsSimpleGroup S := hL.2
  let βbar : MulAut S :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L β
  have hβbar_apply : ∀ k : L, βbar (QuotientGroup.mk k) = QuotientGroup.mk (β k) := fun k =>
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk β k
  have hβbar3 : βbar ^ 3 = 1 := by
    change (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L β) ^ 3 = 1
    rw [← map_pow, hβ, map_one]
  have hJ' : GLAPComponent 3 (fixSubgroup βbar) (J.map π) := by
    have hJ0 : GLAPComponent 3 (⨅ _ : Unit, fixSubgroup β) J := by
      simpa only [iInf_const] using hJ
    have h := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_iInf_fixSubgroup
      (ι := Unit) π hπker (fun _ : Unit => β) (fun _ : Unit => βbar)
      (fun _ k => (hβbar_apply k).symm) hπsurj Nat.prime_three hJ0
    simpa only [iInf_const] using h
  obtain ⟨eJ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map Nat.prime_three π hJ hJ'
  have hcard : Nat.card (PSimple 3 J) = Nat.card (PSimple 3 (J.map π)) :=
    Nat.card_congr eJ.toEquiv
  by_cases hβbar1 : βbar = 1
  · have hfix : fixSubgroup βbar = ⊤ := by
      rw [hβbar1]
      exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.fixSubgroup_one
    have hJtop : GLAPComponent 3 (⊤ : Subgroup S) (J.map π) := by
      rwa [hfix] at hJ'
    have hScard : Nat.card S = 9196830720 := card_quot_u62 hq e
    have hna : ∃ a b : S, a * b ≠ b * a :=
      CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6.exists_noncomm_of_simple_not_prime (by
        rw [hScard]
        norm_num)
    obtain ⟨eS⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv Nat.prime_three hna hJtop
    have hXcard : Nat.card (PSimple 3 J) = 9196830720 :=
      hcard.trans ((Nat.card_congr eS.toEquiv).trans hScard)
    exact not_catalogIs_isL2prime_of_card_eq_u62 hXcard hcat
  · obtain ⟨⟨hℓ, hfe, -, -⟩, F, _, _, hF, ⟨eT⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv e
    have h : UnitaryFieldData q.p q.exponent F :=
      ⟨hℓ, hfe, by rw [hF, ← pow_mul, mul_comm]⟩
    obtain ⟨eP⟩ :=
      nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := 5 + 1) (K := F))
    let ψ : S ≃* primeFormP h (idGram F 6) :=
      (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
    let βm : MulAut (primeFormP h (idGram F 6)) := MulAut.congr ψ βbar
    have hβm3 : βm ^ 3 = 1 := by
      change (MulAut.congr ψ βbar) ^ 3 = 1
      rw [← map_pow, hβbar3, map_one]
    have hβm1 : βm ≠ 1 := by
      intro h1
      have h1' : MulAut.congr ψ βbar = 1 := by simpa [βm] using h1
      have h1'' : MulAut.congr ψ βbar = MulAut.congr ψ (1 : MulAut S) := by
        rw [h1', map_one]
      exact hβbar1 ((MulAut.congr ψ).injective h1'')
    have hshape : CompShape ExcU62Type βm :=
      excU62_compShape_of_data hq.1 hq.2 h βm hβm3 hβm1
    have hshapeβ : CompShape ExcU62Type βbar :=
      CompShape.of_congr excU62Type_isoInvariant ψ hshape
    obtain ⟨hcomp, ⟨eQ⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.component_of_glaPComponent
        Nat.prime_three hshapeβ.layer hJ'
    have htype : ExcU62Type (PSimple 3 (J.map π)) :=
      excU62Type_isoInvariant _ _ eQ (hshapeβ.type (J.map π) hcomp)
    have htypeX : ExcU62Type (PSimple 3 J) :=
      excU62Type_isoInvariant _ _ eJ.symm htype
    rcases card_of_excU62Type htypeX with h1 | h2 | h3
    · exact CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.not_catalogIs_isL2prime_of_card_eq
        h1 hcat
    · exact not_catalogIs_isL2prime_of_card_eq_13685760 h2 hcat
    · exact not_catalogIs_isL2prime_of_card_eq_504 h3 hcat

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

end
