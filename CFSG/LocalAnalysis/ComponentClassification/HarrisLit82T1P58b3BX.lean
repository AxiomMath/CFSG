module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BSpin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BBlk
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieMap
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthMain

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups commutatorElement

namespace P58b3

section Images

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_isSubnormal_centralizer {S : Type*} [Group S] (π : X →* S)
    (hπ : Function.Surjective π) (hker : π.ker = center X) {t : X} {Q : Subgroup X}
    (hQt : Q ≤ centralizer {t}) (hQ : (Q.subgroupOf (centralizer {t})).IsSubnormal) :
    Q.map π ≤ centralizer {π t} ∧ ((Q.map π).subgroupOf (centralizer {π t})).IsSubnormal := by
  have hπZ : ∀ {x : X}, π x = 1 ↔ x ∈ center X := fun {x} => by rw [← MonoidHom.mem_ker, hker]
  have hcent : ∀ {x : X}, x ∈ centralizer ({t} : Set X) → π x ∈ centralizer ({π t} : Set S) :=
    fun {x} hx => by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, hx, map_mul]
  have hRv : Q.map π ≤ centralizer {π t} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcent (hQt hx)
  have hH₁v : (centralizer {t}).map π ≤ centralizer {π t} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcent hx
  let πH : ↥(centralizer ({t} : Set X)) →* ↥((centralizer ({t} : Set X)).map π) :=
    (π.comp (centralizer ({t} : Set X)).subtype).codRestrict _ fun h => ⟨h, h.2, rfl⟩
  have hπHs : Function.Surjective πH := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  have heq : (Q.subgroupOf (centralizer {t})).map πH =
      (Q.map π).subgroupOf ((centralizer {t}).map π) := by
    ext ⟨y, hy⟩
    simp only [mem_map, mem_subgroupOf]
    constructor
    · rintro ⟨⟨x, hxH⟩, hxQ, hxy⟩
      exact ⟨x, hxQ, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hxQ, rfl⟩
      exact ⟨⟨x, hQt hxQ⟩, hxQ, rfl⟩
  have h₁ : ((Q.map π).subgroupOf ((centralizer {t}).map π)).IsSubnormal := by
    rw [← heq]
    exact hQ.map hπHs
  exact ⟨hRv, CFSG.GroupTheory.isSubnormal_subgroupOf_trans (map_mono hQt) hH₁v h₁
    (P58b.normal_map_centralizer_of_ker π hπ hker t).isSubnormal⟩

theorem isSolvable_of_coreQuot {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nonempty (Q ⧸ pPrimeCore 2 Q ≃* PSL(2, ZMod 3)) ∨
      Nonempty (Q ⧸ pPrimeCore 2 Q ≃* SL(2, ZMod 3))) : Group.IsSolvable Q := by
  have h3 : Nat.card (ZMod 3) = 3 := card_zmod_three
  have hSL : Group.IsSolvable SL(2, ZMod 3) :=
    LieType.HighestRoot.isSolvable_of_mulEquiv h3 (MulEquiv.refl _)
  have : Group.IsSolvable (Q ⧸ pPrimeCore 2 Q) := by
    obtain he | he := hQ <;> obtain ⟨e⟩ := he
    · have : Group.IsSolvable PSL(2, ZMod 3) :=
        Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : Group.IsSolvable (pPrimeCore 2 Q) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ odd_card_pPrimeCore
  exact Group.isSolvable_of_ker_le_range (pPrimeCore 2 Q).subtype
    (QuotientGroup.mk' (pPrimeCore 2 Q))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem oddGen_of_coreQuot {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nonempty (Q ⧸ pPrimeCore 2 Q ≃* PSL(2, ZMod 3)) ∨
      Nonempty (Q ⧸ pPrimeCore 2 Q ≃* SL(2, ZMod 3))) : OddGen Q := by
  refine OddGen.of_quotient (N := pPrimeCore 2 Q) odd_card_pPrimeCore ?_
  obtain he | he := hQ <;> obtain ⟨e⟩ := he
  · exact oddGen_psl23.of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · exact oddGen_sl23.of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem three_dvd_card_of_coreQuot {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nonempty (Q ⧸ pPrimeCore 2 Q ≃* PSL(2, ZMod 3)) ∨
      Nonempty (Q ⧸ pPrimeCore 2 Q ≃* SL(2, ZMod 3))) : 3 ∣ Nat.card Q := by
  have hF : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  have hSL : Nat.card SL(2, ZMod 3) = 24 := by
    rw [GorensteinWalter.sl2_card_formula, Nat.card_zmod]
    norm_num
  have hPSL : Nat.card PSL(2, ZMod 3) = 12 := by
    have h := Burgoyne.C.card_PSL_mul_two hF
    rw [hSL] at h
    omega
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 Q)]
  obtain he | he := hQ <;> obtain ⟨e⟩ := he
  · rw [Nat.card_congr e.toEquiv, hPSL]
    exact Dvd.dvd.mul_right (by norm_num) _
  · rw [Nat.card_congr e.toEquiv, hSL]
    exact Dvd.dvd.mul_right (by norm_num) _

theorem eq_one_of_mem_center_map {S : Type*} [Group S] (π : X →* S)
    (hker : π.ker = center X) {c : X} (hcZ : c ∈ center X) (hc2 : orderOf c = 2)
    {Q : Subgroup X} (hcQ : c ∈ Q)
    (hQ : Nonempty (↥Q ⧸ pPrimeCore 2 ↥Q ≃* PSL(2, ZMod 3)) ∨
      Nonempty (↥Q ⧸ pPrimeCore 2 ↥Q ≃* SL(2, ZMod 3)))
    {s : S} (hs : s ∈ Q.map π) (hsc : ∀ h ∈ Q.map π, s * h = h * s) (hs2 : s * s = 1) :
    s = 1 := by
  have hπZ : ∀ {x : X}, π x = 1 ↔ x ∈ center X := fun {x} => by rw [← MonoidHom.mem_ker, hker]
  set c' : ↥Q := ⟨c, hcQ⟩ with hc'
  have hc'Z : c' ∈ center ↥Q := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp hcZ g)
  have hc'2 : orderOf c' = 2 := by rw [hc', Subgroup.orderOf_mk]; exact hc2
  obtain he | he := hQ
  · obtain ⟨e⟩ := he
    exact (P58b.OLie.false_of_mem_center_psl2 e hc'Z hc'2).elim
  obtain ⟨e⟩ := he
  obtain ⟨q, hq, rfl⟩ := hs
  set q' : ↥Q := ⟨q, hq⟩ with hq'
  set φ : ↥Q →* SL(2, ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥Q))
    with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφZ : ∀ z ∈ center ↥Q, φ z ∈ center SL(2, ZMod 3) := by
    intro z hz
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hφs g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]
  have hcomm : ∀ y : ↥Q, ⁅q', y⁆ ∈ center ↥Q := by
    intro y
    have h1 : π ((⁅q', y⁆ : ↥Q) : X) = 1 := by
      have h := hsc (π y) ⟨y, y.2, rfl⟩
      change π (q * (y : X) * q⁻¹ * (y : X)⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        show π q * π y * (π q)⁻¹ * (π y)⁻¹ = (π q * π y) * (π y * π q)⁻¹ by group, h,
        mul_inv_cancel]
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp (hπZ.mp h1) g)
  have hφq : φ q' ∈ center SL(2, ZMod 3) := by
    have hc : (QuotientGroup.mk (φ q') : PSL(2, ZMod 3)) ∈ center PSL(2, ZMod 3) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨y, rfl⟩ := hφs g
      have h1 := hφZ _ (hcomm y)
      rw [map_commutatorElement] at h1
      have h2 : QuotientGroup.mk' (center SL(2, ZMod 3)) ⁅φ q', φ y⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).2 h1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2.symm
    rw [GorensteinWalter.psl2_center_eq_bot, mem_bot, QuotientGroup.eq_one_iff] at hc
    exact hc
  have hφc : φ c' = -1 := by
    rcases (LieType.HighestRoot.mem_center_SL23_iff _).1 (hφZ c' hc'Z) with h | h
    · exfalso
      have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥Q) c' = 1 := e.injective (h.trans (map_one e).symm)
      exact Burgoyne.C.not_mem_pPrimeCore_of_orderOf hc'2 ((QuotientGroup.eq_one_iff _).1 h1)
    · exact h
  obtain ⟨o, ho, hoq⟩ : ∃ o ∈ pPrimeCore 2 ↥Q, π (o : X) = π q := by
    rcases (LieType.HighestRoot.mem_center_SL23_iff _).1 hφq with h | h
    · refine ⟨q', ?_, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 (e.injective (h.trans (map_one e).symm))
    · refine ⟨c'⁻¹ * q', ?_, ?_⟩
      · apply (QuotientGroup.eq_one_iff _).1
        apply e.injective
        change φ (c'⁻¹ * q') = e 1
        rw [map_mul, map_inv, hφc, h, map_one]
        simp
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hπZ.2 hcZ, inv_one, one_mul]
  have hodd : Odd (orderOf (π q)) := by
    rw [← hoq]
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd π _)
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (odd_card_pPrimeCore (R := ↥Q))
      (Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥Q) ho)
  have h2 : orderOf (π q) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hs2)
  have h1 : orderOf (π q) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hodd) dvd_rfl h2
  exact orderOf_eq_one_iff.1 h1

theorem facts_map_solvable {S : Type*} [Group S] (π : X →* S) (hπ : Function.Surjective π)
    (hker : π.ker = center X) (hZ2 : Nat.card (center X) = 2) {c : X} (hcZ : c ∈ center X)
    (hc2 : orderOf c = 2) {t : X} {Q : Subgroup X}
    (hQ : IsSolvableTwoComponentIn Q (centralizer {t})) (hcQ : c ∈ Q) :
    Q.map π ≤ centralizer {π t} ∧ ((Q.map π).subgroupOf (centralizer {π t})).IsSubnormal ∧
      Group.IsSolvable ↥(Q.map π) ∧ OddGen ↥(Q.map π) ∧
      (∃ r ∈ Q.map π, r ^ 3 = 1 ∧ r ≠ 1) ∧
      ∀ s ∈ Q.map π, (∀ h ∈ Q.map π, s * h = h * s) → s * s = 1 → s = 1 := by
  have hπZ : ∀ {x : X}, π x = 1 ↔ x ∈ center X := fun {x} => by rw [← MonoidHom.mem_ker, hker]
  obtain ⟨hQt, hQs, -, hQiso⟩ := hQ
  obtain ⟨h₁, h₂⟩ := map_isSubnormal_centralizer π hπ hker hQt hQs
  have : Group.IsSolvable ↥Q := isSolvable_of_coreQuot hQiso
  refine ⟨h₁, h₂, Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π Q),
    (oddGen_of_coreQuot hQiso).of_surjective (MonoidHom.subgroupMap_surjective π Q), ?_,
    fun s hs hsc hs2 => eq_one_of_mem_center_map π hker hcZ hc2 hcQ hQiso hs hsc hs2⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 3 (three_dvd_card_of_coreQuot hQiso)
  refine ⟨π y, ⟨y, y.2, rfl⟩, ?_, fun h1 => ?_⟩
  · rw [← map_pow, ← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one, map_one]
  · have hyZ : (y : X) ∈ center X := hπZ.1 h1
    have hdvd := Subgroup.orderOf_dvd_natCard (center X) hyZ
    rw [hZ2, Subgroup.orderOf_coe, hy] at hdvd
    exact absurd hdvd (by norm_num)

theorem facts_map_solvable' {S : Type*} [Group S] (π : X →* S) (hπ : Function.Surjective π)
    (hker : π.ker = center X) {t : X} {Q : Subgroup X}
    (hQ : IsSolvableTwoComponentIn Q (centralizer {t})) :
    Q.map π ≤ centralizer {π t} ∧ ((Q.map π).subgroupOf (centralizer {π t})).IsSubnormal ∧
      Group.IsSolvable ↥(Q.map π) ∧ OddGen ↥(Q.map π) := by
  obtain ⟨hQt, hQs, -, hQiso⟩ := hQ
  obtain ⟨h₁, h₂⟩ := map_isSubnormal_centralizer π hπ hker hQt hQs
  have : Group.IsSolvable ↥Q := isSolvable_of_coreQuot hQiso
  exact ⟨h₁, h₂, Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π Q),
    (oddGen_of_coreQuot hQiso).of_surjective (MonoidHom.subgroupMap_surjective π Q)⟩

end Images

section Diag

variable {K : Type} [Field K] [Finite K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

include hw in
theorem card_compl_eq_three (hK3 : Nat.card K = 3) (hd : Odd d) (hker : OKer (oQ (diagGL hw)))
    {J : Finset (Fin d)} (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hJne : J.Nonempty)
    (hJc : Jᶜ.Nonempty) (hNF : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I)
    {R₁ L : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hR₁x : R₁ ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hR₁s : (R₁.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))).IsSubnormal)
    (hR₁solv : Group.IsSolvable ↥R₁) (hR₁odd : OddGen ↥R₁) (hr : ∃ r ∈ R₁, r ^ 3 = 1 ∧ r ≠ 1)
    (hLx : L ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))))
    (hxL : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∈ L) :
    Jᶜ.card = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hJev := P58b.OLie.even_card_of_signGL_mem hK hJ
  have hcomp : Jᶜ.card = d - J.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hJle : J.card ≤ d := by
    have := Finset.card_le_univ J
    rwa [Fintype.card_fin] at this
  have hJcodd : ¬ Even Jᶜ.card := by
    intro hev
    rw [hcomp] at hev
    obtain ⟨a, ha⟩ := hev
    obtain ⟨b, hb⟩ := hJev
    obtain ⟨c, hc⟩ := hd
    omega
  obtain ⟨I', hI', hI'c, hLI', hc'⟩ := P51e.Orth.sign_comp_cases hw hK J hJ hJne hJc hLx hLc
  have hI'ev := P51e.Orth.even_card_of_mem_comp hw hK J I' hI' hJ hI'c hLI' hxL
  have hI'J : I' = J := by
    rcases hI' with h | h
    · exact h
    · exact absurd (h ▸ hI'ev) hJcodd
  subst hI'J
  obtain ⟨hLe, hLq, h3J⟩ : L = blockP K hw I' ∧ IsQuasisimple L ∧ 3 ≤ I'.card := by
    rcases hc' with h | ⟨-, hK3', -⟩
    · exact h
    · exact absurd hK3 hK3'
  have hqJ : IsQuasisimple (blockP K hw I') := hLe ▸ hLq
  have hR₁c := le_tBlockP_compl_of_isSubnormal hw hK hd hker hJ (Or.inl rfl) hJc
    (hNF I' (Or.inl rfl) h3J) hqJ hR₁x hR₁s hR₁solv hR₁odd.le_closure
  obtain ⟨r, hrR, hr3, hr1⟩ := hr
  have hro : Odd (orderOf r) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hr3)
  by_contra hne
  rcases (show I'ᶜ.card ≤ 2 ∨ 5 ≤ I'ᶜ.card by
      rcases (show I'ᶜ.card ≤ 2 ∨ I'ᶜ.card = 3 ∨ I'ᶜ.card = 4 ∨ 5 ≤ I'ᶜ.card by omega) with
        h | h | h | h
      · exact Or.inl h
      · exact absurd h hne
      · exact absurd ⟨2, by omega⟩ hJcodd
      · exact Or.inr h) with h | h
  · exact hr1 (eq_one_of_mem_tBlockP_of_card_le_two hw hK3 h (hR₁c hrR) hro)
  · have hIcc : I'ᶜᶜ.Nonempty := by rwa [compl_compl]
    have hq' := isQuasisimple_blockP_of_five_le hw hK h hIcc
    have hR₁J := le_tBlockP_compl_of_isSubnormal hw hK hd hker hJ (Or.inr rfl) hIcc
      (hNF I'ᶜ (Or.inr rfl) (by omega)) hq' hR₁x hR₁s hR₁solv hR₁odd.le_closure
    rw [compl_compl] at hR₁J
    exact hr1 (eq_one_of_mem_tBlockP_of_mem_compl hw h2 hd (hR₁J hrR) (hR₁c hrR))

include hw in
theorem false_of_two_solvable (hK3 : Nat.card K = 3) (hd : Odd d) (hd9 : 9 ≤ d)
    (hker : OKer (oQ (diagGL hw))) {J : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hJne : J.Nonempty) (hJc : Jᶜ.Nonempty)
    (hNF : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I)
    {R₁ R₂ : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hR₁x : R₁ ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hR₁s : (R₁.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))).IsSubnormal)
    (hR₁solv : Group.IsSolvable ↥R₁) (hR₁odd : OddGen ↥R₁) (hr : ∃ r ∈ R₁, r ^ 3 = 1 ∧ r ≠ 1)
    (hR₁z : ∀ s ∈ R₁, (∀ h ∈ R₁, s * h = h * s) → s * s = 1 → s = 1)
    (hR₂x : R₂ ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hR₂s : (R₂.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))).IsSubnormal)
    (hR₂solv : Group.IsSolvable ↥R₂) (hR₂odd : OddGen ↥R₂)
    (hxR₂ : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∈ R₂) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hJev := P58b.OLie.even_card_of_signGL_mem hK hJ
  have hcomp : Jᶜ.card = d - J.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hJle : J.card ≤ d := by
    have := Finset.card_le_univ J
    rwa [Fintype.card_fin] at this
  have hqJ : ¬ IsQuasisimple (blockP K hw J) := by
    intro hq
    have h3 := three_le_card_of_isQuasisimple_blockP hw hJc h2 hq
    have hR₂c := le_tBlockP_compl_of_isSubnormal hw hK hd hker hJ (Or.inl rfl) hJc
      (hNF J (Or.inl rfl) h3) hq hR₂x hR₂s hR₂solv hR₂odd.le_closure
    exact projH_sign_not_mem_tBlockP_compl hw hK hd hJ hJne (hR₂c hxR₂)
  have hJ4 : J.card ≤ 4 := by
    by_contra h
    exact hqJ (isQuasisimple_blockP_of_five_le hw hK (by omega) hJc)
  have hIcc : Jᶜᶜ.Nonempty := by rwa [compl_compl]
  have h5 : 5 ≤ Jᶜ.card := by omega
  have hq' := isQuasisimple_blockP_of_five_le hw hK h5 hIcc
  have hR₁J := le_tBlockP_compl_of_isSubnormal hw hK hd hker hJ (Or.inr rfl) hIcc
    (hNF Jᶜ (Or.inr rfl) (by omega)) hq' hR₁x hR₁s hR₁solv hR₁odd.le_closure
  have hR₂J := le_tBlockP_compl_of_isSubnormal hw hK hd hker hJ (Or.inr rfl) hIcc
    (hNF Jᶜ (Or.inr rfl) (by omega)) hq' hR₂x hR₂s hR₂solv hR₂odd.le_closure
  rw [compl_compl] at hR₁J hR₂J
  have hJpos : 0 < J.card := Finset.card_pos.2 hJne
  rcases (show J.card ≤ 2 ∨ J.card = 4 by
      obtain ⟨a, ha⟩ := hJev
      omega) with h | h
  ·
    have hbot : R₂ ≤ ⊥ := hR₂odd.le_closure.trans (closure_le _ |>.mpr fun y hy => by
      rw [SetLike.mem_coe, mem_bot]
      exact eq_one_of_mem_tBlockP_of_card_le_two hw hK3 h (hR₂J hy.1) hy.2)
    have hx1 := orderOf_projH_sign hw hK hJ hJne hJc
    rw [mem_bot.1 (hbot hxR₂), orderOf_one] at hx1
    exact absurd hx1 (by norm_num)
  ·
    obtain ⟨r, hrR, hr3, hr1⟩ := hr
    have hR₁sJ : (R₁.subgroupOf (tBlockP hw J)).IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (tBlockP_le_centralizer hw J J (Or.inl rfl) hJ)
        hR₁s
    obtain ⟨s, hs, hsc, hs2⟩ := exists_central_involution_of_le_tBlockP hw hK3 hd h hJc hqJ hR₁J
      hR₁sJ hR₁odd hrR hr3 hr1
    have hs1 := hR₁z s hs hsc (by rw [← pow_two, ← hs2, pow_orderOf_eq_one])
    rw [hs1, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)

end Diag

section XLevel

variable {X : Type} [Group X] [Finite X]

theorem rank_lift_eq_three {K : Type} [Field K] [Finite K] (hK3 : Nat.card K = 3) {d : ℕ}
    (hd : Odd d) {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (hker : OKer (oQ R)) (θ : X ⧸ center X ≃* StatedProj (matrixDerived (oQ R)))
    (hZ2 : Nat.card (center X) = 2) {c t : X} (hcZ : c ∈ center X) (hc2 : orderOf c = 2)
    (htZ : t ∉ center X) {T : GL (Fin d) K} (hT : T ∈ matrixDerived (oQ R))
    (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = 1)
    (hθT : θ (QuotientGroup.mk t) = projH _ ⟨T, hT⟩) {Q₁ L : Subgroup X}
    (hQ₁ : IsSolvableTwoComponentIn Q₁ (centralizer {t})) (hcQ₁ : c ∈ Q₁)
    (hL : IsTwoComponentIn L (centralizer {t})) (htL : t ∈ L) :
    ((T : Matrix (Fin d) (Fin d) K) + 1).rank = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hT1 : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ≠ 1 := by
    rw [← hθT]
    intro h
    apply htZ
    rw [← QuotientGroup.eq_one_iff]
    exact θ.injective (h.trans (map_one θ).symm)
  obtain ⟨w, hw, J, hJ, θ', hker', hJne, hJc, hNF, hθ'T, hrank⟩ :=
    exists_sign_frame_rank_ker hK hR hker hT hT2 hT1
  set pr : X →* StatedProj (matrixDerived (oQ (diagGL hw))) :=
    (θ.trans θ').toMonoidHom.comp (QuotientGroup.mk' (center X)) with hpr
  have hprs : Function.Surjective pr :=
    (θ.trans θ').surjective.comp (QuotientGroup.mk'_surjective _)
  have hprker : pr.ker = center X := by
    ext y
    rw [MonoidHom.mem_ker, hpr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hprt : pr t = projH _ ⟨signGL K J, hJ⟩ := by
    rw [hpr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
      QuotientGroup.mk'_apply, hθT, hθ'T]
  obtain ⟨hR₁x, hR₁s, hR₁solv, hR₁odd, hr, -⟩ :=
    facts_map_solvable pr hprs hprker hZ2 hcZ hc2 hQ₁ hcQ₁
  obtain ⟨hLx, hLc⟩ := P58b.OLie.map_isPComponent_centralizer pr hprs hprker hL
  rw [hprt] at hR₁x hR₁s hLx hLc
  have hxL : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∈ L.map pr :=
    hprt ▸ mem_map_of_mem pr htL
  rw [hrank]
  exact card_compl_eq_three hw hK3 hd hker' hJ hJne hJc hNF hR₁x hR₁s hR₁solv hR₁odd hr hLx hLc
    hxL

theorem false_of_lift {K : Type} [Field K] [Finite K] (hK3 : Nat.card K = 3) {d : ℕ}
    (hd : Odd d) (hd9 : 9 ≤ d) {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (hker : OKer (oQ R)) (θ : X ⧸ center X ≃* StatedProj (matrixDerived (oQ R)))
    (hZ2 : Nat.card (center X) = 2) {c t : X} (hcZ : c ∈ center X) (hc2 : orderOf c = 2)
    (htZ : t ∉ center X) {T : GL (Fin d) K} (hT : T ∈ matrixDerived (oQ R))
    (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = 1)
    (hθT : θ (QuotientGroup.mk t) = projH _ ⟨T, hT⟩) {Q₁ Q₂ : Subgroup X}
    (hQ₁ : IsSolvableTwoComponentIn Q₁ (centralizer {t})) (hcQ₁ : c ∈ Q₁)
    (hQ₂ : IsSolvableTwoComponentIn Q₂ (centralizer {t})) (htQ₂ : t ∈ Q₂) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hT1 : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ≠ 1 := by
    rw [← hθT]
    intro h
    apply htZ
    rw [← QuotientGroup.eq_one_iff]
    exact θ.injective (h.trans (map_one θ).symm)
  obtain ⟨w, hw, J, hJ, θ', hker', hJne, hJc, hNF, hθ'T, -⟩ :=
    exists_sign_frame_rank_ker hK hR hker hT hT2 hT1
  set pr : X →* StatedProj (matrixDerived (oQ (diagGL hw))) :=
    (θ.trans θ').toMonoidHom.comp (QuotientGroup.mk' (center X)) with hpr
  have hprs : Function.Surjective pr :=
    (θ.trans θ').surjective.comp (QuotientGroup.mk'_surjective _)
  have hprker : pr.ker = center X := by
    ext y
    rw [MonoidHom.mem_ker, hpr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hprt : pr t = projH _ ⟨signGL K J, hJ⟩ := by
    rw [hpr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
      QuotientGroup.mk'_apply, hθT, hθ'T]
  obtain ⟨hR₁x, hR₁s, hR₁solv, hR₁odd, hr, hR₁z⟩ :=
    facts_map_solvable pr hprs hprker hZ2 hcZ hc2 hQ₁ hcQ₁
  obtain ⟨hR₂x, hR₂s, hR₂solv, hR₂odd⟩ := facts_map_solvable' pr hprs hprker hQ₂
  rw [hprt] at hR₁x hR₁s hR₂x hR₂s
  have hxR₂ : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∈ Q₂.map pr :=
    hprt ▸ mem_map_of_mem pr htQ₂
  exact false_of_two_solvable hw hK3 hd hd9 hker' hJ hJne hJc hNF hR₁x hR₁s hR₁solv hR₁odd hr
    hR₁z hR₂x hR₂s hR₂solv hR₂odd hxR₂

end XLevel

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
