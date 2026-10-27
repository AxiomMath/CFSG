module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResAFamily
public import CFSG.CharacterTheory.Semidihedral.AllPrimeSL2Sections

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo IsChevIndexTwo)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.LieType.SeitzGeneration (RankLE2)

section Transfer

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]

theorem conjNormal_not_mem_inner (hC : Subgroup.centralizer (L : Set X) = ⊥) {d : X}
    (hdL : d ∉ L) : (MulAut.conjNormal d : MulAut ↥L) ∉ inner ↥L := by
  rintro ⟨y, hy⟩
  have hψ : Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) :=
    CFSG.LieType.SeitzGeneration.conjNormal_injective hC
  apply hdL
  have h1 : (MulAut.conjNormal (y : X) : MulAut ↥L) = MulAut.conj y := by
    ext z
    simp [MulAut.conjNormal_val, MulAut.conj_apply]
  have h2 : (MulAut.conjNormal d : MulAut ↥L) = MulAut.conjNormal (y : X) := by
    rw [h1]
    exact hy.symm
  have := hψ h2
  rw [this]
  exact y.2

theorem outerPElement_false_of_fixesPair {p : ℕ} (hp : p.Prime)
    (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hE : ∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) {d : X} (hdL : d ∉ L)
    (hdp : d ^ p = 1) (h : FixesIndepPair p (MulAut.conjNormal d : MulAut ↥L)) : False := by
  have hψ : Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) :=
    CFSG.LieType.SeitzGeneration.conjNormal_injective hC
  have hconj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) :=
    conj_injective_of_centralizer_eq_bot hC (MulEquiv.refl _)
  have hL : ∀ y : ↥L, ∃ l ∈ L, (MulAut.conjNormal : X →* MulAut ↥L) l = MulAut.conj y := by
    intro y
    refine ⟨(y : X), y.2, ?_⟩
    ext z
    simp [MulAut.conjNormal_val, MulAut.conj_apply]
  exact false_of_outer_fixesPair hp hconj (hE : RankLE2 p X)
    (MulAut.conjNormal : X →* MulAut ↥L) hψ L hL hdp (conjNormal_not_mem_inner hC hdL) h

theorem false_of_inner_of_pow {p : ℕ} (hC : Subgroup.centralizer (L : Set X) = ⊥) {d : X}
    (hdL : d ∉ L) (hdp : d ^ p = 1)
    (hin : ∀ α : MulAut ↥L, α ^ p = 1 → α ∈ inner ↥L) : False :=
  conjNormal_not_mem_inner hC hdL (hin _ (by rw [← map_pow, hdp, map_one]))

end Transfer

section Inner

theorem mem_inner_of_pow_eq_one_of_not_dvd_card_outer {G : Type*} [Group G] {p : ℕ}
    (hp : p.Prime) (h : ¬ p ∣ Nat.card (Outer G)) {α : MulAut G} (hαp : α ^ p = 1) :
    α ∈ inner G := by
  have hcop : Nat.Coprime p (Nat.card (Outer G)) := (Nat.Prime.coprime_iff_not_dvd hp).2 h
  have h1 : (QuotientGroup.mk α : Outer G) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hαp, QuotientGroup.mk_one]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk α : Outer G) ∣ Nat.card (Outer G) := orderOf_dvd_natCard _
  have h4 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h4)

end Inner

section ThirdDisjunct

theorem card_catA_one_seven {q : TauCeti.PrimePower} (hq7 : q.card = 7)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) :
    Nat.card (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group = 168 := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  rw [Nat.card_congr (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).toEquiv]
  have hcardK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hodd : Odd (Nat.card (GaloisField q.p q.exponent)) := by
    rw [hcardK, hq7]
    decide
  have h := CFSG.Semidihedral.AllPrime.SL2Sections.card_psl2_mul_two hodd
  rw [hcardK, hq7] at h
  change Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField q.p q.exponent))
    = 168
  omega

theorem false_of_pRank_catA_one_seven {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Type} [Group L]
    [Finite L] (hrk : CFSG.Open.pRank p (⊤ : Subgroup L) = 2) {q : TauCeti.PrimePower}
    (hq7 : q.card = 7) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (e : L ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) : False := by
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_of_pRank_eq_two hp hrk
  have hL : Nat.card L = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_catA_one_seven hq7 hv
  have hdvd : p ^ 2 ∣ 168 := by
    have := Subgroup.card_subgroup_dvd_card E
    rwa [hEc, hL] at this
  have hle : p ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) hdvd
  have hp12 : p ≤ 12 := by nlinarith
  interval_cases p <;> first | omega | (exfalso; norm_num at hp) | exact hp2 rfl

theorem inner_of_pow_catTwistedA_two_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Type}
    [Group L] {q : TauCeti.PrimePower} (hq3 : q.card = 3)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (e : L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) {α : MulAut L}
    (hαp : α ^ p = 1) : α ∈ inner L := by
  classical
  have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
  have hq : ¬ (2 + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h => hmodel.1.2.2.2 (by rw [h.1, h.2])
  obtain ⟨K, _, hU, ⟨e₀⟩, ⟨eP⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.exists_primeFormP_mulEquiv_of_statedModel
      hmodel
  let eL : L ≃* primeFormP hU (idCn (2 + 1) K) := e.trans eP
  have hqc : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq3
  have hexp : q.exponent = 1 := by
    have hpd : q.p ∣ 3 := by
      rw [← hqc]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hpd
    rw [hp3] at hqc
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using hqc)
  have hcard := (unitary_full_diagonal_outer_order hU (by norm_num) hq).2.2.2.1
  have hgcd : Nat.gcd (2 + 1) (q.p ^ q.exponent + 1) = 1 := by rw [hqc]; norm_num
  have hnd : ¬ p ∣ Nat.card (Outer (primeFormP hU (idCn (2 + 1) K))) := by
    have h2 : Nat.card (Outer (primeFormP hU (idCn (2 + 1) K))) = 2 := by
      rw [hcard, hgcd, hexp]
    rw [h2]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
  have hin := mem_inner_of_pow_eq_one_of_not_dvd_card_outer hp hnd
    (α := MulAut.congr eL α) (by rw [← map_pow, hαp, map_one])
  exact (congr_mem_inner_iff eL α).1 hin

end ThirdDisjunct

theorem chevTwoOuterPElementIsLThree_of_fixesPair
    (hC : ChevTwoOuterFixesPair LieFamilyClassical)
    (hE : ChevTwoOuterFixesPair LieFamilyExceptional)
    (hH : ChevTwoOuterFixesPair LieFamilyHalf) : ChevTwoOuterPElementIsLThree := by
  intro p hp hp2 X _ _ L _ hs hnab hcat hnalt hCL hE2 hrk hchev d hdL hdp
  by_cases h3 : p = 3 ∧ IsLThreeTwo ↥L
  · exact h3
  · exfalso
    have hα := conjNormal_not_mem_inner hCL hdL
    have hαp : (MulAut.conjNormal d : MulAut ↥L) ^ p = 1 := by rw [← map_pow, hdp, map_one]
    have key : FixesIndepPair p (MulAut.conjNormal d : MulAut ↥L) → False := fun h =>
      outerPElement_false_of_fixesPair hp hCL hE2 hdL hdp h
    rcases hchev with ⟨d', hchar, he⟩ | ⟨n, -, he⟩ | ⟨⟨d1, hv⟩, hd', he⟩
    · rcases lieFamily_cases d'.1 with hf | hf | hf | hf
      · exact key (chevTwoOuterFixesPair_A p hp hp2 ↥L hrk ⟨d', hchar, hf, he⟩ h3 _ hα hαp)
      · exact key (hC p hp hp2 ↥L hrk ⟨d', hchar, hf, he⟩ h3 _ hα hαp)
      · exact key (hE p hp hp2 ↥L hrk ⟨d', hchar, hf, he⟩ h3 _ hα hαp)
      · exact key (hH p hp hp2 ↥L hrk ⟨d', hchar, hf, he⟩ h3 _ hα hαp)
    · exact hnalt ⟨n, he⟩
    · obtain ⟨e⟩ := he
      rcases hd' with ⟨q, hq7, rfl⟩ | ⟨q, hq3, rfl⟩
      · exact false_of_pRank_catA_one_seven hp hp2 hrk hq7 hv e
      · exact false_of_inner_of_pow hCL hdL hdp fun α' hα' =>
          inner_of_pow_catTwistedA_two_three hp hp2 hq3 hv e hα'

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
