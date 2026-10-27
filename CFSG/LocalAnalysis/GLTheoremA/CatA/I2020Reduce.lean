module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020Transfer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p q : ℕ}

private theorem i2020FixCentAt_linear (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {X K J : Subgroup G} {y : G}
    (hK : GLAPComponent p X K) (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hyp : y ^ p = 1) {r : ℕ} (hr3 : 3 ≤ r + 1) (hr4 : r + 1 ≤ 4)
    {Q : TauCeti.PrimePower} (hQp : Q.p = q)
    (hcat : pSimpleIsLie p K (.A r Q)) (hdiv : p ∣ Q.card - 1)
    (hLI : I2020LinInner) (hLO : I2020LinOuter)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J) :
    I2020FixCentAt (chevAut p K ⟨y, hyN⟩) (chevTransfer p K J) := by
  classical
  subst hQp
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  · change d = TauCeti.LieTypeIndex.A r Q at hi
    subst d
    let F := GaloisField Q.p Q.exponent
    let e : PSimple p K ≃* LinearFlag.projectiveSL (r + 1) F :=
      e₀.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r Q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) F))
    have hcard : Nat.card F = Q.card := by
      rw [show Nat.card F = Nat.card (GaloisField Q.p Q.exponent) from rfl,
        GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
    have hdivF : p ∣ Nat.card F - 1 := by rwa [hcard]
    let β := chevAut p K ⟨y, hyN⟩
    have hβp : MulAut.congr e β ^ p = 1 := by
      rw [← map_pow, chevAut_pow_eq_one p K hyN hyp, map_one]
    have hinner : I2020FixCent p (fun _ => True) (MulAut.congr e β) := by
      by_cases hinn : ∃ A : GL (Fin (r + 1)) F,
          MulAut.congr e β = LinearFlag.conjAut (r + 1) F A
      · obtain ⟨A, hA⟩ := hinn
        have h1 : LinearFlag.conjAut (r + 1) F (A ^ p) * LinearFlag.fieldAut (r + 1) F 1 = 1 := by
          rw [map_one, mul_one, map_pow, ← hA, hβp]
        obtain ⟨-, c, hc⟩ :=
          LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one hr3 (A ^ p) 1 h1
        rw [hA]
        exact hLI p Q.p hp hp2 hq hq2 hqp F hdivF (r + 1) hr3 hr4 A c hc.symm
      · push Not at hinn
        exact hLO p Q.p hp hp2 hq hq2 hqp F (r + 1) hr3 hr4 (MulAut.congr e β) hβp hinn
    exact i2020FixCentAt_of_fixCent_map hp e
      (glaPComponent_chevTransfer hp hyN (isPGroup_zpowers_of_pow_eq_one hyp) hJ) hinner
  · exact absurd hi id


private theorem i2020FixCentAt_unitary (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {X K J : Subgroup G} {y : G}
    (hK : GLAPComponent p X K) (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hyp : y ^ p = 1) {r : ℕ} (hr3 : 3 ≤ r + 1) (hr4 : r + 1 ≤ 4)
    {Q : TauCeti.PrimePower} (hQp : Q.p = q)
    (hcat : pSimpleIsLie p K (.twistedA r Q)) (hdiv : p ∣ Q.card + 1)
    (hUI : I2020UniInner) (hUO : I2020UniOuter)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J) :
    I2020FixCentAt (chevAut p K ⟨y, hyN⟩) (chevTransfer p K J) := by
  classical
  subst hQp
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  · change d = TauCeti.LieTypeIndex.twistedA r Q at hi
    subst d
    obtain ⟨-, Kf, _, _, hKcard, ⟨e₁⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r Q hv e₀
    have hU : UnitaryFieldData Q.p Q.exponent Kf :=
      ⟨Q.prime_p, Q.exponent_pos, by rw [hKcard, ← pow_mul, mul_comm]⟩
    obtain ⟨e₂⟩ :=
      nonempty_primeFormP_mulEquiv hU (isPrimeFormGram_idGram (K := Kf) (n := r + 1))
    let e : PSimple p K ≃* primeFormP hU (idGram Kf (r + 1)) :=
      e₁.trans ((CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU
        (by omega)).symm.trans e₂.symm)
    have hdivU : p ∣ Q.p ^ Q.exponent + 1 := by
      rwa [← TauCeti.PrimePower.card_def]
    let β := chevAut p K ⟨y, hyN⟩
    have hβp : MulAut.congr e β ^ p = 1 := by
      rw [← map_pow, chevAut_pow_eq_one p K hyN hyp, map_one]
    have hinner : I2020FixCent p (fun _ => True) (MulAut.congr e β) := by
      by_cases hinn : ∃ A : primeFormUnitary hU (idGram Kf (r + 1)),
          MulAut.congr e β = primeFormConjHom hU (idGram Kf (r + 1)) A
      · obtain ⟨A, hA⟩ := hinn
        have hC : IsPrimeFormGram (1 : GL (Fin (r + 1)) Kf) := isPrimeFormGram_idGram
        obtain ⟨-, -, hker, -⟩ := unitary_prime_form_full_semilinear_realization hU hC
          (by omega) (fun hh => by
            have h3 : Q.p ∣ Q.p ^ Q.exponent := dvd_pow_self _ Q.exponent_pos.ne'
            rw [hh.2] at h3
            exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h3))
        have hPsi : primeFormPsi hU hC ⟨A ^ p, 1⟩ = 1 := by
          rw [primeFormPsi_apply, map_one, mul_one, map_pow, ← hA, hβp]
        obtain ⟨-, c, -, hc⟩ := (hker ⟨A ^ p, 1⟩).1 hPsi
        have hc' : (A : GL (Fin (r + 1)) Kf) ^ p =
            Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
          rw [← hc, Subgroup.coe_pow]
        rw [hA]
        exact hUI p Q.p hp hp2 hq hq2 hqp Q.exponent Kf hU hdivU (r + 1) hr3 hr4 A c hc'
      · push Not at hinn
        exact hUO p Q.p hp hp2 hq hq2 hqp Q.exponent Kf hU (r + 1) hr3 hr4
          (MulAut.congr e β) hβp hinn
    exact i2020FixCentAt_of_fixCent_map hp e
      (glaPComponent_chevTransfer hp hyN (isPGroup_zpowers_of_pow_eq_one hyp) hJ) hinner
  · exact absurd hi id

private theorem i2020FixCent_of_orth_model {Y : Type} [Group Y] [Finite Y]
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hcenter : Subgroup.center Y = ⊥)
    {t : StatedLieTag} {n f : ℕ} (htag : I2020OrthTag t n)
    (hModel : StatedClassicalModel Y t n q f) (hdiv : p ∣ (q ^ f) ^ 2 - 1)
    (hOI : I2020OrthInner) (hOO : I2020OrthOuter) (hD : I2020D4Three)
    {β : MulAut Y} (hβp : β ^ p = 1) :
    I2020FixCent p (JType p q) β := by
  by_cases hinn : ∃ a : Y, β = MulAut.conj a
  · obtain ⟨a, rfl⟩ := hinn
    have hap : a ^ p = 1 := by
      have h1 : MulAut.conj (a ^ p) = 1 := by rw [map_pow, hβp]
      have hmem : a ^ p ∈ Subgroup.center Y := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h2 := congrArg (fun φ : MulAut Y => φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        calc g * a ^ p = a ^ p * g * (a ^ p)⁻¹ * a ^ p := by rw [h2]
          _ = a ^ p * g := by group
      rwa [hcenter, Subgroup.mem_bot] at hmem
    exact hOI p q hp hp2 hq hq2 hqp t n htag Y f hModel hdiv a hap
  · push Not at hinn
    by_cases h43 : t = .POmegaPlus ∧ p = 3
    · obtain ⟨rfl, hp3⟩ := h43
      have hn4 : n = 4 := by
        rcases htag with ⟨h1, -⟩ | ⟨-, hn⟩
        · exact absurd h1 (by decide)
        · exact hn
      subst p
      subst n
      exact hD q hq hq2 hqp Y f hModel β hβp hinn
    · exact hOO p q hp hp2 hq hq2 hqp t n htag Y f hModel
        (fun ht hp3 => h43 ⟨ht, hp3⟩) β hβp hinn

private theorem i2020FixCentAt_case_iii (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {X K J : Subgroup G} {y : G}
    (hK : GLAPComponent p X K) (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hyp : y ^ p = 1) (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (hJType : JType p q J) (hZ : Subgroup.center (PQuot p K) = ⊥)
    (hOI : I2020OrthInner) (hOO : I2020OrthOuter) (hD : I2020D4Three)
    {Q : TauCeti.PrimePower} (hQp : Q.p = q)
    (hcase : (pSimpleIsLie p K (.B 3 Q) ∨ pSimpleIsLie p K (.twistedD 4 Q)) ∧
      p ∣ Q.card ^ 2 - 1) :
    I2020FixCentAt (chevAut p K ⟨y, hyN⟩) (chevTransfer p K J) := by
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hcenter : Subgroup.center (PSimple p K) = ⊥ := by
    obtain ⟨hs, hna⟩ := chev_pSimple_simple_nonabelian hp hK
    haveI := hs
    exact chev_center_eq_bot_of_simple_nonabelian hna
  have hJType' : JType p q (chevTransfer p K J) := jType_chevTransfer hp hZ hJK hJType
  rcases hcase with ⟨hB | hTD, hdiv⟩
  · obtain ⟨i, hi, ⟨e₀⟩⟩ := hB
    rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
    · exact absurd hi id
    · exact absurd hi id
    · change d = TauCeti.LieTypeIndex.B 3 Q at hi
      subst d
      have hModel : StatedClassicalModel (PSimple p K) .POmegaOdd 3 Q.p Q.exponent :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 Q hv
          (by rw [hQp]; exact hq2) (by norm_num) e₀
      rw [hQp] at hModel
      have hdiv' : p ∣ (q ^ Q.exponent) ^ 2 - 1 := by
        simpa [TauCeti.PrimePower.card_def, hQp] using hdiv
      have hfc := i2020FixCent_of_orth_model hp hp2 hq hq2 hqp hcenter
        (t := .POmegaOdd) (n := 3) (f := Q.exponent) (Or.inl ⟨rfl, rfl⟩) hModel hdiv'
        hOI hOO hD (chevAut_pow_eq_one p K hyN hyp)
      exact hfc _ (glaPComponent_chevTransfer hp hyN (isPGroup_zpowers_of_pow_eq_one hyp) hJ)
        hJType'
    · exact absurd hi id
  · obtain ⟨i, hi, ⟨e₀⟩⟩ := hTD
    rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
    · exact absurd hi id
    · exact absurd hi id
    · change d = TauCeti.LieTypeIndex.twistedD 4 Q at hi
      subst d
      have hModel : StatedClassicalModel (PSimple p K) .POmegaMinus 4 Q.p Q.exponent :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD 4 Q hv e₀
      rw [hQp] at hModel
      have hdiv' : p ∣ (q ^ Q.exponent) ^ 2 - 1 := by
        simpa [TauCeti.PrimePower.card_def, hQp] using hdiv
      have hfc := i2020FixCent_of_orth_model hp hp2 hq hq2 hqp hcenter
        (t := .POmegaMinus) (n := 4) (f := Q.exponent) (Or.inr ⟨Or.inr rfl, rfl⟩) hModel
        hdiv' hOI hOO hD (chevAut_pow_eq_one p K hyN hyp)
      exact hfc _ (glaPComponent_chevTransfer hp hyN (isPGroup_zpowers_of_pow_eq_one hyp) hJ)
        hJType'
    · exact absurd hi id

private theorem i2020FixCentAt_case_iv (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {X K J : Subgroup G} {y : G}
    (hK : GLAPComponent p X K) (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hyp : y ^ p = 1) (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (hJType : JType p q J) (hZ : Subgroup.center (PQuot p K) = ⊥)
    (hOI : I2020OrthInner) (hOO : I2020OrthOuter) (hD : I2020D4Three)
    {Q : TauCeti.PrimePower} (hQp : Q.p = q)
    (hcase : pSimpleIsLie p K (.D 4 Q) ∧ p ∣ Q.card ^ 2 - 1) :
    I2020FixCentAt (chevAut p K ⟨y, hyN⟩) (chevTransfer p K J) := by
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hcenter : Subgroup.center (PSimple p K) = ⊥ := by
    obtain ⟨hs, hna⟩ := chev_pSimple_simple_nonabelian hp hK
    haveI := hs
    exact chev_center_eq_bot_of_simple_nonabelian hna
  have hJType' : JType p q (chevTransfer p K J) := jType_chevTransfer hp hZ hJK hJType
  obtain ⟨hD4, hdiv⟩ := hcase
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hD4
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  · change d = TauCeti.LieTypeIndex.D 4 Q at hi
    subst d
    have hModel : StatedClassicalModel (PSimple p K) .POmegaPlus 4 Q.p Q.exponent :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 Q hv e₀
    rw [hQp] at hModel
    have hdiv' : p ∣ (q ^ Q.exponent) ^ 2 - 1 := by
      simpa [TauCeti.PrimePower.card_def, hQp] using hdiv
    have hfc := i2020FixCent_of_orth_model hp hp2 hq hq2 hqp hcenter
      (t := .POmegaPlus) (n := 4) (f := Q.exponent) (Or.inr ⟨Or.inl rfl, rfl⟩) hModel
      hdiv' hOI hOO hD (chevAut_pow_eq_one p K hyN hyp)
    exact hfc _ (glaPComponent_chevTransfer hp hyN (isPGroup_zpowers_of_pow_eq_one hyp) hJ)
      hJType'
  · exact absurd hi id

private theorem i2020FixCentAt_case_i (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {X K J : Subgroup G} {y : G}
    (hK : GLAPComponent p X K) (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hyp : y ^ p = 1) (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (hLI : I2020LinInner) (hLO : I2020LinOuter) (hUI : I2020UniInner) (hUO : I2020UniOuter)
    {Q : TauCeti.PrimePower} (hQp : Q.p = q)
    (hcase : (pSimpleIsLie p K (.A 2 Q) ∧ p ∣ Q.card - 1) ∨
      (pSimpleIsLie p K (.twistedA 2 Q) ∧ p ∣ Q.card + 1)) :
    I2020FixCentAt (chevAut p K ⟨y, hyN⟩) (chevTransfer p K J) := by
  rcases hcase with ⟨hA, hdiv⟩ | ⟨hA, hdiv⟩
  · exact i2020FixCentAt_linear hp hp2 hq hq2 hqp hK hyN hyp (r := 2) (by norm_num)
      (by norm_num) hQp hA hdiv hLI hLO hJ
  · exact i2020FixCentAt_unitary hp hp2 hq hq2 hqp hK hyN hyp (r := 2) (by norm_num)
      (by norm_num) hQp hA hdiv hUI hUO hJ

private theorem i2020FixCentAt_case_ii (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {X K J : Subgroup G} {y : G}
    (hK : GLAPComponent p X K) (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hyp : y ^ p = 1) (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (hLI : I2020LinInner) (hLO : I2020LinOuter) (hUI : I2020UniInner) (hUO : I2020UniOuter)
    {Q : TauCeti.PrimePower} (hQp : Q.p = q)
    (hcase : (pSimpleIsLie p K (.A 3 Q) ∧ p ∣ Q.card - 1) ∨
      (pSimpleIsLie p K (.twistedA 3 Q) ∧ p ∣ Q.card + 1)) :
    I2020FixCentAt (chevAut p K ⟨y, hyN⟩) (chevTransfer p K J) := by
  rcases hcase with ⟨hA, hdiv⟩ | ⟨hA, hdiv⟩
  · exact i2020FixCentAt_linear hp hp2 hq hq2 hqp hK hyN hyp (r := 3) (by norm_num)
      (by norm_num) hQp hA hdiv hLI hLO hJ
  · exact i2020FixCentAt_unitary hp hp2 hq hq2 hqp hK hyN hyp (r := 3) (by norm_num)
      (by norm_num) hQp hA hdiv hUI hUO hJ

theorem i2020At_of_parts (hLI : I2020LinInner) (hLO : I2020LinOuter) (hUI : I2020UniInner)
    (hUO : I2020UniOuter) (hOI : I2020OrthInner) (hOO : I2020OrthOuter) (hD : I2020D4Three)
    (G : Type) [Group G] [Finite G] (p : ℕ) : I2020At G p := by
  intro hp hp2 q hq hq2 hqp B a K J T S D y hInT h64 hDN hyD hcent hyp hDC hJ hJType hT hS hSK
    hTS hSD hDS
  have hK : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K := hInT.1.2.2.2.1
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := hDN hyD
  have hfix : I2020FixCentAt (chevAut p K ⟨y, hyN⟩) (chevTransfer p K J) := by
    rcases h64 with ⟨-, Q, hQp, hcase⟩ | ⟨-, -, -, Q, hQp, hcase⟩ |
      ⟨-, -, hZ, Q, hQp, hcase⟩ | ⟨-, -, hZ, Q, hQp, hcase⟩
    · exact i2020FixCentAt_case_i hp hp2 hq hq2 hqp hK hyN hyp hJ hLI hLO hUI hUO hQp hcase
    · exact i2020FixCentAt_case_ii hp hp2 hq hq2 hqp hK hyN hyp hJ hLI hLO hUI hUO hQp hcase
    · exact i2020FixCentAt_case_iii hp hp2 hq hq2 hqp hK hyN hyp hJ hJType hZ hOI hOO hD hQp
        hcase
    · exact i2020FixCentAt_case_iv hp hp2 hq hq2 hqp hK hyN hyp hJ hJType hZ hOI hOO hD hQp
        hcase
  exact Or.inl (commutator_le_centMod_of_i2020FixCentAt hp hK hyN hJ hT hS hSK hTS hyD hDN hDC
    hSD hDS hfix)

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
