module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.FixedComponent
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.RuFi23
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SolStdSubgroup

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp12Lie

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder sporFactors)
open CFSG.ComponentClassification.HarrisLit.T1.SporRow
  (OddLieOrder not_oddLieOrder_U62 not_oddLieOrder_E62)

noncomputable def quotCenterEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem card_psu_six_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSU 6 2 1) : Nat.card X = 9196830720 := by
  obtain ⟨-, h1, -⟩ := hO X .PSU 6 2 1 h.admissible h
  have hd : lieOrderDivisor .PSU 6 (2 ^ 1) = 3 := by decide +kernel
  have hn : lieOrderNumerator .PSU 6 (2 ^ 1) = 27590492160 := by decide +kernel
  rw [hd, hn] at h1
  omega

theorem card_twistedE6_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .twistedE6 0 2 1) : Nat.card X = 76532479683774853939200 := by
  obtain ⟨-, h1, -⟩ := hO X .twistedE6 0 2 1 h.admissible h
  have hd : lieOrderDivisor .twistedE6 0 (2 ^ 1) = 3 := by decide +kernel
  have hn : lieOrderNumerator .twistedE6 0 (2 ^ 1) = 229597439051324561817600 := by decide +kernel
  rw [hd, hn] at h1
  omega

theorem factorial_div_two_ne_u62 (k : ℕ) : k.factorial / 2 ≠ 9196830720 := by
  intro h
  by_cases hk : k < 13
  · interval_cases k <;> simp [Nat.factorial] at h
  · have h13 : 13 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h2 : 2 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h3 : k.factorial = 2 * (k.factorial / 2) := (Nat.mul_div_cancel' h2).symm
    rw [h] at h3
    rw [h3] at h13
    revert h13
    decide +kernel

theorem factorial_div_two_ne_e62 (k : ℕ) : k.factorial / 2 ≠ 76532479683774853939200 := by
  intro h
  by_cases hk : k < 23
  · interval_cases k <;> simp [Nat.factorial] at h
  · have h23 : 23 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h2 : 2 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h3 : k.factorial = 2 * (k.factorial / 2) := (Nat.mul_div_cancel' h2).symm
    rw [h] at h3
    rw [h3] at h23
    revert h23
    decide +kernel

theorem dvd_sporOrder_u62 (s : TauCeti.SporadicName) (h : 9196830720 ∣ sporOrder s) :
    s = .Co1 ∨ s = .Co2 ∨ s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B ∨ s = .M := by
  cases s <;> first
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; left; rfl)
    | (right; right; right; left; rfl)
    | (right; right; right; right; left; rfl)
    | (right; right; right; right; right; left; rfl)
    | (right; right; right; right; right; right; rfl)
    | exact absurd h (by
        unfold sporOrder sporFactors
        decide +kernel)

theorem dvd_sporOrder_e62 (s : TauCeti.SporadicName) (h : 76532479683774853939200 ∣ sporOrder s) :
    s = .B ∨ s = .M := by
  cases s <;> first
    | (left; rfl)
    | (right; rfl)
    | exact absurd h (by
        unfold sporOrder sporFactors
        decide +kernel)

theorem not_innerRow_u62 {s : TauCeti.SporadicName}
    (h : s = .Co1 ∨ s = .Co2 ∨ s = .Fi24Prime ∨ s = .B ∨ s = .M) :
    ¬ SporadicInnerRow s 9196830720 := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp only [SporadicInnerRow] <;> decide

theorem not_innerRow_m_e62 : ¬ SporadicInnerRow .M 76532479683774853939200 := by
  simp only [SporadicInnerRow]
  decide

theorem false_of_oddLie_card (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    {S : Type} [Group S] [Finite S] (hodd : OddLieType S) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) {c : ℕ}
    (hc : Nat.card (↥D ⧸ center ↥D) = c) (hnot : ¬ OddLieOrder c) (hbig : 504 < c) : False := by
  rcases odd_arm hGLS hodd hσ hD with ⟨τ', n', p, f', hp, hp2, hadm', hmod'⟩ | hL
  · obtain ⟨-, h1, h2⟩ := hO _ τ' n' p f' hadm' hmod'
    rw [hc] at h1 h2
    exact hnot ⟨τ', n', p, f', hp, hp2, hadm', h1, h2⟩
  · have hadmL : StatedLieAdmissible .PSL 2 2 3 :=
      ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩
    obtain ⟨-, h1, -⟩ := hO _ .PSL 2 2 3 hadmL hL
    have h504 : Nat.card ↥D = 504 := by
      simp only [lieOrderDivisor, lieOrderNumerator] at h1
      norm_num [Finset.Icc_self] at h1
      omega
    have hle : Nat.card (↥D ⧸ center ↥D) ≤ Nat.card ↥D :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [hc, h504] at hle
    omega

@[expose] def Fi23NoTightU62 : Prop :=
  ∀ {S : Type} [Group S], (S ≃* Carrier .Fi23) → ∀ {L : Subgroup S}, CFSG.IsQuasisimple ↥L →
    Nat.card (↥L ⧸ center ↥L) = 9196830720 →
    (∀ r : S, orderOf r = 2 → r ∈ centralizer (L : Set S) →
      centralizer ({r} : Set S) ≤ normalizer (L : Set S)) →
    ∀ {z : S}, orderOf z = 2 → z ∈ centralizer (L : Set S) → False

theorem exists_inner_fixedComponent {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2) {L' : Subgroup Y} (hsol : SolStd L')
    (hq : CFSG.IsQuasisimple ↥L') (hev : Even (Nat.card ↥(center ↥L'))) :
    ∃ (z : Y) (hz : z ∈ N') (σ : MulAut ↥N') (D : Subgroup ↥(fixedSubgroup σ)),
      L' ≤ N' ∧ orderOf z = 2 ∧ z ∈ centralizer (L' : Set Y) ∧ orderOf σ = 2 ∧
        σ ∈ (MulAut.conj : ↥N' →* MulAut ↥N').range ∧ IsComponent D ∧ Nonempty (↥D ≃* ↥L') := by
  have hNn : N'.Normal := hN.normal
  have hLN : L' ≤ N' := Hyp.le_of_perfect_of_index_le_two hidx hq.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥L')) 2
    (even_iff_two_dvd.1 hev)
  have hr2 : orderOf ((r : ↥L') : Y) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hr
  have hrC : ((r : ↥L') : Y) ∈ centralizer (L' : Set Y) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 r.2 ⟨y, hy⟩)
  have hLC : L' ≤ centralizer ({((r : ↥L') : Y)} : Set Y) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hrC l hl)
  have hcomp : IsCompIn L' (centralizer ({((r : ↥L') : Y)} : Set Y)) :=
    isCompIn_of_normal hLC hq
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLC).2
        (hsol.centralizer_le_normalizer hrC hr2))
  have hrN : ((r : ↥L') : Y) ∈ N' := hLN (r : ↥L').2
  obtain ⟨σ, D, hσ, hD, hin, he⟩ := CFSG.ComponentClassification.CatFC.exists_fixedComponent hN hr2
    hcomp hLN
  exact ⟨_, hrN, σ, D, hLN, hr2, hrC, hσ, hin hrN, hD, he⟩

theorem catalogU62_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput) (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M → Nat.card (Carrier s) = sporOrder s)
    (hCo1 : SporadicRowsFor .Co1) (hCo2 : SporadicRowsFor .Co2)
    (hFi24 : SporadicRowsFor .Fi24Prime) (hB : SporadicRowsFor .B) (hM : SporadicRowsFor .M)
    (hFi23 : Fi23NoTightU62) {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2) (hcat : CFSG.Blueprint.Catalog ↥N')
    {L' : Subgroup Y} (hsol : SolStd L') (hq : CFSG.IsQuasisimple ↥L')
    (hev : Even (Nat.card ↥(center ↥L')))
    (hU : LieModel (↥L' ⧸ center ↥L') .PSU 6 2 1) : IsSporadic ↥N' .Fi22 := by
  have hNn := hN.normal
  have hSimple := hN.isSimpleGroup
  have hna := hN.nonabelian
  obtain ⟨z, hzN, σ, D, hLN, hz2, hzC, hσ, hDin, hD, ⟨e⟩⟩ :=
    exists_inner_fixedComponent hN hidx hsol hq hev
  have hKcard : Nat.card (↥L' ⧸ center ↥L') = 9196830720 := card_psu_six_two hO hU
  have hDcard : Nat.card (↥D ⧸ center ↥D) = 9196830720 := by
    rw [Nat.card_congr (quotCenterEquiv e).toEquiv, hKcard]
  have hdvd : 9196830720 ∣ Nat.card ↥N' := by
    rw [← hKcard]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hLN)
  rcases catalog_fixed_component hGLS hEI hEO hna hcat hσ hD with
    ⟨n, k, -, hk5, -, -, -, ⟨eA⟩⟩ | ⟨hodd, -⟩ | ⟨-, hout, -⟩ | ⟨s, ⟨es⟩⟩
  ·
    exfalso
    haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hk : Nat.card (↥D ⧸ center ↥D) = k.factorial / 2 := by
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    exact factorial_div_two_ne_u62 k (hk.symm.trans hDcard)
  ·
    exfalso
    exact false_of_oddLie_card hGLS hO hodd hσ hD hDcard not_oddLieOrder_U62 (by norm_num)
  · exact absurd hDin hout
  ·
    by_cases hsM : s = .M
    · subst hsM
      exfalso
      have := (hM hSimple hna es hσ hD).1 hDin
      rw [hDcard] at this
      exact not_innerRow_u62 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) this
    · have hcs : Nat.card ↥N' = sporOrder s := (Nat.card_congr es.toEquiv).trans (hcard s hsM)
      rw [hcs] at hdvd
      rcases dvd_sporOrder_u62 s hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso
        have := (hCo1 hSimple hna es hσ hD).1 hDin
        rw [hDcard] at this
        exact not_innerRow_u62 (Or.inl rfl) this
      · exfalso
        have := (hCo2 hSimple hna es hσ hD).1 hDin
        rw [hDcard] at this
        exact not_innerRow_u62 (Or.inr (Or.inl rfl)) this
      · exact ⟨es⟩
      ·
        exfalso
        have hsolN : SolStd (L'.subgroupOf N') := solStd_subgroupOf hLN hzN hz2 hzC hsol
        let φ : ↥(L'.subgroupOf N') ≃* ↥L' := Subgroup.subgroupOfEquivOfLe hLN
        have hzN2 : orderOf (⟨z, hzN⟩ : ↥N') = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
        have hzCN : (⟨z, hzN⟩ : ↥N') ∈ centralizer ((L'.subgroupOf N' : Subgroup ↥N') : Set ↥N') := by
          rw [mem_centralizer_iff]
          intro l hl
          exact Subtype.ext (mem_centralizer_iff.1 hzC (l : Y) hl)
        exact hFi23 es (CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hq)
          ((Nat.card_congr (quotCenterEquiv φ).toEquiv).trans hKcard)
          (fun r hr2 hrC => hsolN.centralizer_le_normalizer hrC hr2) hzN2 hzCN
      · exfalso
        have := (hFi24 hSimple hna es hσ hD).1 hDin
        rw [hDcard] at this
        exact not_innerRow_u62 (Or.inr (Or.inr (Or.inl rfl))) this
      · exfalso
        have := (hB hSimple hna es hσ hD).1 hDin
        rw [hDcard] at this
        exact not_innerRow_u62 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) this
      · exact absurd rfl hsM

theorem catalogE62_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput) (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M → Nat.card (Carrier s) = sporOrder s)
    (hM : SporadicRowsFor .M) {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2) (hcat : CFSG.Blueprint.Catalog ↥N')
    {L' : Subgroup Y} (hsol : SolStd L') (hq : CFSG.IsQuasisimple ↥L')
    (hev : Even (Nat.card ↥(center ↥L')))
    (hE : LieModel (↥L' ⧸ center ↥L') .twistedE6 0 2 1) : IsSporadic ↥N' .B := by
  have hNn := hN.normal
  have hSimple := hN.isSimpleGroup
  have hna := hN.nonabelian
  obtain ⟨z, hzN, σ, D, hLN, hz2, hzC, hσ, hDin, hD, ⟨e⟩⟩ :=
    exists_inner_fixedComponent hN hidx hsol hq hev
  have hKcard : Nat.card (↥L' ⧸ center ↥L') = 76532479683774853939200 :=
    card_twistedE6_two hO hE
  have hDcard : Nat.card (↥D ⧸ center ↥D) = 76532479683774853939200 := by
    rw [Nat.card_congr (quotCenterEquiv e).toEquiv, hKcard]
  have hdvd : 76532479683774853939200 ∣ Nat.card ↥N' := by
    rw [← hKcard]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hLN)
  rcases catalog_fixed_component hGLS hEI hEO hna hcat hσ hD with
    ⟨n, k, -, hk5, -, -, -, ⟨eA⟩⟩ | ⟨hodd, -⟩ | ⟨-, hout, -⟩ | ⟨s, ⟨es⟩⟩
  · exfalso
    haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hk : Nat.card (↥D ⧸ center ↥D) = k.factorial / 2 := by
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    exact factorial_div_two_ne_e62 k (hk.symm.trans hDcard)
  · exfalso
    exact false_of_oddLie_card hGLS hO hodd hσ hD hDcard not_oddLieOrder_E62 (by norm_num)
  · exact absurd hDin hout
  · by_cases hsM : s = .M
    · subst hsM
      exfalso
      have := (hM hSimple hna es hσ hD).1 hDin
      rw [hDcard] at this
      exact not_innerRow_m_e62 this
    · have hcs : Nat.card ↥N' = sporOrder s := (Nat.card_congr es.toEquiv).trans (hcard s hsM)
      rw [hcs] at hdvd
      rcases dvd_sporOrder_e62 s hdvd with rfl | rfl
      · exact ⟨es⟩
      · exact absurd rfl hsM

theorem catalogHyp12Lie_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput) (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M → Nat.card (Carrier s) = sporOrder s)
    (hCo1 : SporadicRowsFor .Co1) (hCo2 : SporadicRowsFor .Co2)
    (hFi24 : SporadicRowsFor .Fi24Prime) (hB : SporadicRowsFor .B) (hM : SporadicRowsFor .M)
    (hFi23 : Fi23NoTightU62) {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2) (hcat : CFSG.Blueprint.Catalog ↥N')
    {L' : Subgroup Y} (hsol : SolStd L') (hq : CFSG.IsQuasisimple ↥L')
    (hev : Even (Nat.card ↥(center ↥L'))) :
    (LieModel (↥L' ⧸ center ↥L') .PSU 6 2 1 → IsSporadic ↥N' .Fi22) ∧
      (LieModel (↥L' ⧸ center ↥L') .twistedE6 0 2 1 → IsSporadic ↥N' .B) :=
  ⟨catalogU62_of_inputs hGLS hEI hEO hO hcard hCo1 hCo2 hFi24 hB hM hFi23 hN hidx hcat hsol hq hev,
    catalogE62_of_inputs hGLS hEI hEO hO hcard hM hN hidx hcat hsol hq hev⟩

@[expose] def Sol78Hyp12LieCat : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Blueprint.Catalog ↥N' → ∀ L' : Subgroup Y, SolStd L' → CFSG.IsQuasisimple ↥L' →
      Even (Nat.card ↥(center ↥L')) →
        (LieModel (↥L' ⧸ center ↥L') .PSU 6 2 1 → IsSporadic ↥N' .Fi22) ∧
          (LieModel (↥L' ⧸ center ↥L') .twistedE6 0 2 1 → IsSporadic ↥N' .B)

theorem sol78Hyp12LieCat_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput) (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M → Nat.card (Carrier s) = sporOrder s)
    (hCo1 : SporadicRowsFor .Co1) (hCo2 : SporadicRowsFor .Co2)
    (hFi24 : SporadicRowsFor .Fi24Prime) (hB : SporadicRowsFor .B) (hM : SporadicRowsFor .M)
    (hFi23 : Fi23NoTightU62) : Sol78Hyp12LieCat := by
  intro Y _ _ N' hN hidx hcat L' hsol hq hev
  exact catalogHyp12Lie_of_inputs hGLS hEI hEO hO hcard hCo1 hCo2 hFi24 hB hM hFi23 hN hidx hcat
    hsol hq hev

end CFSG.EvenSporadicStandard.Induction.Hyp12Lie
