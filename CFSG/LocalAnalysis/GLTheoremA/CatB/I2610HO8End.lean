module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.HardMathSupport.Dickson.Bal207.D42Triality
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HL2
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFixInf
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33b
import CFSG.HardMathSupport.Dickson.Bal207.Closed
import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1LieOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula add_one_dvd_sq_sub_one)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (IsTwoPow)
open CFSG.HardMathSupport.Dickson.Bal207 (CompShapeOn OrthCompIdx OrthCompType
  isoInvariant_orthCompType)
open CFSG.RankThree.PartTwo.Census.Carrier.SpinD (typeDGroupEquivStatedProj_of_valid)
open CFSG.RankThree.PartTwo.Sec4.Ronan148R

section Orders

private theorem sixteen_dvd_pow_of_even {q : ℕ} (hq : Even q) {N : ℕ} (hN : 4 ≤ N) :
    16 ∣ q ^ N := by
  have h2 : 2 ∣ q := even_iff_two_dvd.mp hq
  have h16 : (16 : ℕ) ∣ q ^ 4 := by
    simpa using pow_dvd_pow_of_dvd h2 4
  exact h16.trans (pow_dvd_pow q hN)

private theorem orderD_ne_168 {n q : ℕ} (hn : 3 ≤ n) (hq : Even q) (hq2 : 2 ≤ q) :
    orderD n q ≠ 168 := by
  intro h
  have hodd : Odd (q ^ n - 1) := by
    have hqn : Even (q ^ n) := (Nat.even_pow' (by omega)).mpr hq
    have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    obtain ⟨k, hk⟩ := hqn
    exact ⟨k - 1, by omega⟩
  have hg : Nat.gcd 4 (q ^ n - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) |>.symm.symm
  unfold orderD at h
  rw [hg, Nat.div_one] at h
  have hN : 4 ≤ n * (n - 1) := by
    have h : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  have h16 : 16 ∣ q ^ (n * (n - 1)) := sixteen_dvd_pow_of_even hq hN
  have hdvd : 16 ∣ q ^ (n * (n - 1)) * (q ^ n - 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (h16.trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
  rw [h] at hdvd
  norm_num at hdvd

private theorem orderTwistedD_ne_168 {n q : ℕ} (hn : 3 ≤ n) (hq : Even q) (hq2 : 2 ≤ q) :
    orderTwistedD n q ≠ 168 := by
  intro h
  have hodd : Odd (q ^ n + 1) := by
    have hqn : Even (q ^ n) := (Nat.even_pow' (by omega)).mpr hq
    exact hqn.add_one
  have hg : Nat.gcd 4 (q ^ n + 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) |>.symm.symm
  unfold orderTwistedD at h
  rw [hg, Nat.div_one] at h
  have hN : 4 ≤ n * (n - 1) := by
    have h : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  have h16 : 16 ∣ q ^ (n * (n - 1)) := sixteen_dvd_pow_of_even hq hN
  have hdvd : 16 ∣ q ^ (n * (n - 1)) * (q ^ n + 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (h16.trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
  rw [h] at hdvd
  norm_num at hdvd

private theorem sixteen_dvd_orderTwistedA {n q : ℕ} (hn : 1 ≤ n) (hq : Even q) (hq2 : 2 ≤ q)
    (h16 : 16 ∣ q ^ (n * (n + 1) / 2)) : 16 ∣ orderTwistedA n q := by
  have hmem : 2 ∈ Finset.Icc 2 (n + 1) := by simp; omega
  have hfac : q + 1 ∣ (fun i => if Even i then q ^ i - 1 else q ^ i + 1) 2 := by
    show q + 1 ∣ (if Even 2 then q ^ 2 - 1 else q ^ 2 + 1)
    simpa using add_one_dvd_sq_sub_one q (by omega)
  have hGd : Nat.gcd (n + 1) (q + 1) ∣ q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Finset.Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q + 1) * orderTwistedA n q =
      q ^ (n * (n + 1) / 2) *
        ∏ i ∈ Finset.Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) :=
    Nat.mul_div_cancel' hGd
  have hodd : Odd (Nat.gcd (n + 1) (q + 1)) :=
    Odd.of_dvd_nat (by obtain ⟨k, rfl⟩ := hq; exact ⟨k, by ring⟩) (Nat.gcd_dvd_right _ _)
  have h16' : 16 ∣ q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Finset.Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) :=
    h16.trans (dvd_mul_right _ _)
  have h16'' : 16 ∣ Nat.gcd (n + 1) (q + 1) * orderTwistedA n q := by
    rw [hmul]
    exact h16'
  have hcop : Nat.Coprime 16 (Nat.gcd (n + 1) (q + 1)) :=
    (Nat.coprime_two_left.mpr hodd).pow_left 4
  exact hcop.dvd_of_dvd_mul_left h16''

private theorem orderTwistedA_ne_168 {n q : ℕ} (hn : 1 ≤ n) (hq : Even q) (hq2 : 2 ≤ q)
    (h16 : 16 ∣ q ^ (n * (n + 1) / 2)) : orderTwistedA n q ≠ 168 := by
  intro h
  have hdiv := sixteen_dvd_orderTwistedA hn hq hq2 h16
  rw [h] at hdiv
  norm_num at hdiv

private theorem orderTwistedA_two_three_ne_sixty' : orderTwistedA 2 3 ≠ 60 := by decide

private theorem orderA_one_eight_ne_168 : orderA 1 8 ≠ 168 := by decide

private theorem orderTwistedA_two_three_ne_168 : orderTwistedA 2 3 ≠ 168 := by decide

private theorem lieOrderFormula_ne_sixty_of_orthCompIdx {d : TauCeti.LieTypeIndex}
    (hd : OrthCompIdx d) : lieOrderFormula d ≠ 60 := by
  cases d with
  | D s q =>
    obtain ⟨hq, -, hs⟩ := hd
    obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
    exact orderD_ne_sixty (by omega) hev h2
  | twistedD s q =>
    obtain ⟨hq, -, hs⟩ := hd
    obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
    exact orderTwistedD_ne_sixty (by omega) hev h2
  | twistedA r q =>
    rcases hd with ⟨hq, hr, -⟩ | ⟨rfl, hp, he⟩
    · obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
      exact orderTwistedA_ne_sixty hr hev h2
    · have hqcard : q.card = 3 := by
        rw [TauCeti.PrimePower.card_def, hp, he]
        norm_num
      change orderTwistedA 2 q.card ≠ 60
      rw [hqcard]
      exact orderTwistedA_two_three_ne_sixty'
  | A r q =>
    obtain ⟨rfl, hq⟩ := hd
    exact orderA_one_eight_ne_sixty hq
  | _ => exact hd.elim

private theorem lieOrderFormula_ne_168_of_orthCompIdx {d : TauCeti.LieTypeIndex}
    (hd : OrthCompIdx d) : lieOrderFormula d ≠ 168 := by
  cases d with
  | D s q =>
    obtain ⟨hq, -, hs⟩ := hd
    obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
    exact orderD_ne_168 (by omega) hev h2
  | twistedD s q =>
    obtain ⟨hq, -, hs⟩ := hd
    obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
    exact orderTwistedD_ne_168 (by omega) hev h2
  | twistedA r q =>
    rcases hd with ⟨hq, hr, hne⟩ | ⟨rfl, hp, he⟩
    · obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
      by_cases hr2 : r = 2
      · have hq3 : IsTwoPow q 3 := by
          rcases hq with hq1 | hq3
          · exact absurd ⟨hr2, hq1⟩ hne
          · exact hq3
        have h16 : 16 ∣ q.card ^ (r * (r + 1) / 2) := by
          rw [hr2, card_of_isTwoPow hq3]
          norm_num
        exact orderTwistedA_ne_168 (by omega) hev h2 h16
      · have h3 : 3 ≤ r := by omega
        have hN : 4 ≤ r * (r + 1) / 2 := by
          rw [Nat.le_div_iff_mul_le (by norm_num)]
          nlinarith
        exact orderTwistedA_ne_168 (by omega) hev h2 (sixteen_dvd_pow_of_even hev hN)
    · have hqcard : q.card = 3 := by
        rw [TauCeti.PrimePower.card_def, hp, he]
        norm_num
      change orderTwistedA 2 q.card ≠ 168
      rw [hqcard]
      exact orderTwistedA_two_three_ne_168
  | A r q =>
    obtain ⟨rfl, hq⟩ := hd
    change orderA 1 q.card ≠ 168
    rw [card_of_isTwoPow hq]
    exact orderA_one_eight_ne_168
  | _ => exact hd.elim

private theorem not_catalogIs_isL2prime_of_card_dvd_o8plus {X : Type} [Group X]
    (hdvd : Nat.card X ∣ 174182400) (h60 : Nat.card X ≠ 60)
    (h168 : Nat.card X ≠ 168) : ¬ catalogIs X isL2prime := by
  intro hc
  rcases card_of_catalogIs_isL2prime hc with h | ⟨r, hrprime, hr7, hr⟩
  · exact h60 h
  · have hr2 : r ≠ 2 := by omega
    have hodd : Odd r := hrprime.odd_of_ne_two hr2
    have h2 : 2 ∣ r ^ 2 - 1 :=
      (show 2 ∣ 8 by norm_num).trans (Nat.eight_dvd_sq_sub_one_of_odd hodd)
    have h2' : 2 ∣ r * (r ^ 2 - 1) := dvd_mul_of_dvd_right h2 r
    have hrdvd : r ∣ Nat.card X := by
      rw [hr, Nat.mul_div_assoc r h2]
      exact dvd_mul_right r _
    have hrdvd' : r ∣ 174182400 := hrdvd.trans hdvd
    have hfac : r ∣ 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 := by
      rwa [show 174182400 = 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 by norm_num] at hrdvd'
    rcases hrprime.dvd_mul.mp hfac with h1 | h7
    · rcases hrprime.dvd_mul.mp h1 with h1 | h5
      · rcases hrprime.dvd_mul.mp h1 with h2p | h3p
        · have hr2' : r = 2 :=
            (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).1 (hrprime.dvd_of_dvd_pow h2p)
          omega
        · have hr3 : r = 3 :=
            (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_three).1 (hrprime.dvd_of_dvd_pow h3p)
          omega
      · have hr5 : r = 5 :=
          (Nat.prime_dvd_prime_iff_eq hrprime (by norm_num : Nat.Prime 5)).1
            (hrprime.dvd_of_dvd_pow h5)
        omega
    · have hr7' : r = 7 :=
        (Nat.prime_dvd_prime_iff_eq hrprime (by norm_num : Nat.Prime 7)).1 h7
      rw [hr7'] at hr
      have hX : Nat.card X = 168 := by
        rw [hr]
        norm_num
      exact h168 hX

end Orders

section Certificates


theorem not_catalogIs_isL2prime_of_quot_o8plus {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) {q : TauCeti.PrimePower} (hq : IsTwoPow q 1)
    {hv : (TauCeti.LieTypeIndex.D 4 q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group)
    {β : MulAut L} (hβ : β ^ 3 = 1) {J : Subgroup L}
    (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    ¬ catalogIs (PSimple 3 J) isL2prime := by
  classical
  intro hcat
  let S := L ⧸ Subgroup.center L
  let π : L →* S := QuotientGroup.mk' (Subgroup.center L)
  let βbar : MulAut S :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L β
  have hβbar_apply : ∀ k : L, βbar (π k) = π (β k) := fun k =>
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk β k
  have hβbar3 : βbar ^ 3 = 1 := by
    change (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L β) ^ 3 = 1
    rw [← map_pow, hβ, map_one]
  let J' : Subgroup S := J.map π
  have hker : π.ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']
  have hJ' : GLAPComponent 3 (fixSubgroup βbar) J' := by
    have hJ0 : GLAPComponent 3 (⨅ _ : Unit, fixSubgroup β) J := by
      simpa only [iInf_const] using hJ
    have h := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_iInf_fixSubgroup
      (ι := Unit) π hker (fun _ : Unit => β) (fun _ : Unit => βbar)
      (fun _ k => (hβbar_apply k).symm) (QuotientGroup.mk'_surjective _)
      Nat.prime_three hJ0
    simpa only [iInf_const] using h
  obtain ⟨eJ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map Nat.prime_three π hJ hJ'
  have hcard : Nat.card (PSimple 3 J) = Nat.card (PSimple 3 J') :=
    Nat.card_congr eJ.toEquiv
  haveI hSsimple : IsSimpleGroup S := hL.2
  have hS : Nat.card S = 174182400 := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
      ⟨.D 4 q, hv⟩ S ⟨e⟩
    rw [h]
    have hqcard : q.card = 2 := by
      rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
      norm_num
    change orderD 4 q.card = 174182400
    rw [hqcard]
    decide
  have hdvd : Nat.card (PSimple 3 J) ∣ 174182400 := by
    rw [hcard]
    simpa [hS] using
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.card_pSimple_dvd 3 J'
  have hM : StatedClassicalModel S .POmegaPlus 4 2 1 := by
    haveI : Finite (TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hK : Nat.card (TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = 2 ^ 1 := by
      rw [TauCeti.ValidLieTypeIndex.card_fixedField]
      simp [TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.PrimePower.card_def, hq.1, hq.2]
    exact ⟨⟨Nat.prime_two, le_rfl, le_rfl⟩,
      TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩, inferInstance, inferInstance, hK,
      ⟨e.trans (typeDGroupEquivStatedProj_of_valid 4 q hv)⟩⟩
  by_cases hβ1 : βbar = 1
  · have hconj1 : MulAut.conj (1 : S) = 1 := map_one _
    have hfix : fixSubgroup βbar = ⊤ := by
      rw [hβ1, ← hconj1]
      exact fixSubgroup_conj_one
    have hJtop : GLAPComponent 3 (⊤ : Subgroup S) J' := by
      rwa [hfix] at hJ'
    have hnc : ∃ a b : S, a * b ≠ b * a :=
      exists_noncomm_of_simple_not_prime (by rw [hS]; norm_num)
    obtain ⟨eTop⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv
      Nat.prime_three hnc hJtop
    have hcardTop : Nat.card (PSimple 3 J') = Nat.card S :=
      Nat.card_congr eTop.toEquiv
    have h60 : Nat.card (PSimple 3 J) ≠ 60 := by
      rw [hcard, hcardTop, hS]
      norm_num
    have h168 : Nat.card (PSimple 3 J) ≠ 168 := by
      rw [hcard, hcardTop, hS]
      norm_num
    exact not_catalogIs_isL2prime_of_card_dvd_o8plus hdvd h60 h168 hcat
  · have hshape : CompShapeOn 3 OrthCompType ⊤ βbar :=
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.compShapeOn_top_of_model
        (S := S) (t := .POmegaPlus) (n := 4) (f := 1)
        CFSG.HardMathSupport.Dickson.Bal207.OrthFix.orthInnerShapeInput_holds
        CFSG.HardMathSupport.Dickson.Bal207.OrthFix.orthInnerUniqueTwo_holds
        CFSG.HardMathSupport.Dickson.Bal207.D42Tri.d42TrialityShape_proved
        (Or.inl rfl) (Or.inl ⟨rfl, by norm_num, Or.inr ⟨rfl, rfl⟩⟩) hM hβbar3 hβ1
    obtain ⟨hcomp, ⟨eZ⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.component_of_glaPComponent
        Nat.prime_three hshape.layer hJ'
    have htype : OrthCompType (PSimple 3 J') :=
      isoInvariant_orthCompType (↥J' ⧸ Subgroup.center ↥J') (PSimple 3 J') eZ
        (hshape.type J' hcomp)
    obtain ⟨d, hd, ⟨eQ⟩⟩ := htype
    have hLie : Nat.card (PSimple 3 J') = lieOrderFormula d.1 :=
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d (PSimple 3 J') ⟨eQ⟩
    have h60 : Nat.card (PSimple 3 J) ≠ 60 := by
      rw [hcard, hLie]
      exact lieOrderFormula_ne_sixty_of_orthCompIdx hd
    have h168 : Nat.card (PSimple 3 J) ≠ 168 := by
      rw [hcard, hLie]
      exact lieOrderFormula_ne_168_of_orthCompIdx hd
    exact not_catalogIs_isL2prime_of_card_dvd_o8plus hdvd h60 h168 hcat

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

end
