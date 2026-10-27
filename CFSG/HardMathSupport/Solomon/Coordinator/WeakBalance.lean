module

public import CFSG.HardMathSupport.Solomon.Coordinator.SignalizerFunctor
public import CFSG.RankThree.PartTwo.Sec20.Step208MSPairProof
public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

section CoprimeAction

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_left_of_le_normalizer {A Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) : ⁅Y, A⁆ ≤ Y := by
  refine Subgroup.commutator_le.2 fun y hy a ha => ?_
  have h1 : a * y⁻¹ * a⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.1 (hAY ha) y⁻¹).1 (Y.inv_mem hy)
  have h2 : y * a * y⁻¹ * a⁻¹ = y * (a * y⁻¹ * a⁻¹) := by group
  rw [commutatorElement_def, h2]
  exact Y.mul_mem hy h1

theorem le_commutator_sup_inf_centralizer_of_solvable {A Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hsolv : Group.IsSolvable ↥Y)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card Y)) :
    Y ≤ ⁅Y, A⁆ ⊔ (Y ⊓ Subgroup.centralizer (A : Set G)) := by
  have : Subgroup.Normalizes A Y := ⟨hAY⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥A) (G := ↥Y) hsolv hcop
  have hcommMap : (CFSG.commutatorAction (A := ↥A) (G := ↥Y)).map Y.subtype = ⁅Y, A⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator Y A hAY
  have hfixEq : CFSG.fixedPointSubgroup ↥A ↥Y =
      (Y ⊓ Subgroup.centralizer (A : Set G)).subgroupOf Y := by
    simpa [CFSG.subgroupCentralizerIn] using
      CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Y A hAY
  intro y hy
  have htop : (⟨y, hy⟩ : ↥Y) ∈ CFSG.fixedPointSubgroup ↥A ↥Y ⊔
      CFSG.commutatorAction (A := ↥A) (G := ↥Y) := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem Y.subtype htop
  rw [Subgroup.map_sup, hcommMap, hfixEq, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  rw [sup_comm]
  exact hmap

theorem le_commutator_sup_inf_centralizer_of_isPGroup {p : ℕ} (hp : p.Prime) {A Y : Subgroup G}
    (hA : IsPGroup p A) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hY : ¬ p ∣ Nat.card Y) :
    Y ≤ ⁅Y, A⁆ ⊔ (Y ⊓ Subgroup.centralizer (A : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  set S : Subgroup G := ⁅Y, A⁆ ⊔ (Y ⊓ Subgroup.centralizer (A : Set G)) with hS
  have hSY : S ≤ Y := sup_le (commutator_le_left_of_le_normalizer hAY) inf_le_left
  have hcopY : Nat.Coprime (Nat.card A) (Nat.card Y) := by
    obtain ⟨a, ha⟩ := hA.exists_card_eq
    rw [ha]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hY)
  have hdvd : Nat.card Y ∣ Nat.card S := by
    refine (Nat.dvd_iff_prime_pow_dvd_dvd (Nat.card S) (Nat.card Y)).2 fun q n hq hqn => ?_
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨Q, hQY, hQq, hQsyl, hAQ⟩ :=
      exists_sylow_normalized_of_not_dvd (q := q) Y A hA hAY hY
    have hQsolv : Group.IsSolvable ↥Q := by
      have := hQq.isNilpotent
      infer_instance
    have hcopQ : Nat.Coprime (Nat.card A) (Nat.card Q) :=
      hcopY.coprime_dvd_right (Subgroup.card_dvd_of_le hQY)
    have hQS : Q ≤ S := by
      refine (le_commutator_sup_inf_centralizer_of_solvable hAQ hQsolv hcopQ).trans
        (sup_le_sup (Subgroup.commutator_mono hQY le_rfl) (inf_le_inf_right _ hQY))
    exact (hQsyl n hqn).trans (Subgroup.card_dvd_of_le hQS)
  have hSeq : S = Y :=
    Subgroup.eq_of_le_of_card_ge hSY (Nat.le_of_dvd Nat.card_pos hdvd)
  rw [hSeq]

end CoprimeAction

section Products

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_dvd_card_sup_of_le_normalizer {p : ℕ} (hp : p.Prime) {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hH : ¬ p ∣ Nat.card H)
    (hN : ¬ p ∣ Nat.card N) : ¬ p ∣ Nat.card (H ⊔ N : Subgroup G) := by
  have hrel := CFSG.RankThree.PartTwo.Sec20.relIndex_sup_eq_of_le_normalizer hHN
  have hcard : N.relIndex (H ⊔ N) * Nat.card N = Nat.card (H ⊔ N : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card N (H ⊔ N)
    rwa [inf_eq_left.2 le_sup_right] at h
  have hdvdH : N.relIndex H ∣ Nat.card H := Subgroup.relIndex_dvd_card N H
  intro h
  rw [← hcard, hrel] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · exact hH (h1.trans hdvdH)
  · exact hN h1

end Products

section ThetaStar

variable {G : Type} [Group G] [Finite G]

@[expose] def thetaStarValue (p : ℕ) (A D : Subgroup G) : Subgroup G :=
  GLADelta p D ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G))

omit [Finite G] in
theorem glaPPrimeCoreOf_centralizer_le (p : ℕ) (A : Subgroup G) :
    GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) ≤ Subgroup.centralizer (A : Set G) :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem centralizer_le_centralizer_of_le {A D : Subgroup G} (hDA : D ≤ A) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (D : Set G) :=
  Subgroup.centralizer_le hDA

theorem glaDelta_inf_centralizer_le_glaPPrimeCoreOf {p : ℕ} (hp : p.Prime) {A D : Subgroup G}
    (hDA : D ≤ A) (hD : D ≠ ⊥) :
    GLADelta p D ⊓ Subgroup.centralizer (A : Set G) ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) := by
  obtain ⟨⟨d, hd⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD
  have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  set C := Subgroup.centralizer (A : Set G)
  set O := GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))
  have hCd : C ≤ Subgroup.centralizer ({d} : Set G) :=
    (centralizer_le_centralizer_of_le hDA).trans (Subgroup.centralizer_le (by simpa using hd))
  have hnorm : ((O ⊓ C).subgroupOf C).Normal := by
    refine ⟨fun x hx c => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_mul, Subgroup.coe_inv] at hx ⊢
    refine ⟨?_, C.mul_mem (C.mul_mem c.2 hx.2) (C.inv_mem c.2)⟩
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p _ (hCd c.2)) _).1 hx.1
  have hcop : Nat.Coprime p (Nat.card ((O ⊓ C).subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      not_dvd_card_glaPPrimeCoreOf hp _ (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hle : (O ⊓ C).subgroupOf C ≤ GLAPPrimeCore p ↥C := le_sSup ⟨hnorm, hcop⟩
  have hmap := Subgroup.map_mono (f := C.subtype) hle
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 inf_le_right] at hmap
  exact (inf_le_inf_right C (glaDelta_le_glaPPrimeCoreOf hd hd1')).trans hmap

omit [Finite G] in
theorem commutator_sup_le_of_le_centralizer {A U O : Subgroup G}
    (hOA : O ≤ Subgroup.centralizer (A : Set G)) (hOU : O ≤ Subgroup.normalizer (U : Set G)) :
    ⁅U ⊔ O, A⁆ ≤ ⁅U, A⁆ := by
  have hmul : ((U ⊔ O : Subgroup G) : Set G) = (U : Set G) * (O : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U O hOU
  refine Subgroup.commutator_le.2 fun x hx a ha => ?_
  have hx' : x ∈ (U : Set G) * (O : Set G) := hmul ▸ hx
  obtain ⟨u, hu, o, ho, rfl⟩ := hx'
  have hoa : o * a = a * o := ((Subgroup.mem_centralizer_iff.1 (hOA ho)) a ha).symm
  have h : ⁅u * o, a⁆ = ⁅u, a⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc u * o * a * (u * o)⁻¹ * a⁻¹ = u * (o * a) * o⁻¹ * u⁻¹ * a⁻¹ := by group
      _ = u * (a * o) * o⁻¹ * u⁻¹ * a⁻¹ := by rw [hoa]
      _ = u * a * u⁻¹ * a⁻¹ := by group
  rw [h]
  exact Subgroup.commutator_mem_commutator hu ha

omit [Finite G] in
theorem glaDelta_anti {p : ℕ} {D E : Subgroup G} (hDE : D ≤ E) : GLADelta p E ≤ GLADelta p D :=
  le_iInf fun d => le_iInf fun hd => le_iInf fun hd1 =>
    iInf_le_of_le d (iInf_le_of_le (hDE hd) (iInf_le _ hd1))

omit [Finite G] in
theorem le_centralizer_of_le_of_isElemAbelian {p : ℕ} {A D : Subgroup G} (hA : IsElemAbelian p A)
    (hDA : D ≤ A) : A ≤ Subgroup.centralizer (D : Set G) := fun a ha => by
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact elemAbelian_comm hA (hDA hd) ha

omit [Finite G] in
theorem sup_inf_le_inf_sup_of_le {U O C : Subgroup G} (hOU : O ≤ Subgroup.normalizer (U : Set G))
    (hOC : O ≤ C) : (U ⊔ O) ⊓ C ≤ (U ⊓ C) ⊔ O := by
  rintro y ⟨hy, hyC⟩
  have hmul : ((U ⊔ O : Subgroup G) : Set G) = (U : Set G) * (O : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U O hOU
  have hy' : y ∈ (U : Set G) * (O : Set G) := hmul ▸ hy
  obtain ⟨u, hu, o, ho, rfl⟩ := hy'
  have huC : u ∈ C := by
    have := C.mul_mem hyC (C.inv_mem (hOC ho))
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hu, huC⟩) (Subgroup.mem_sup_right ho)

omit [Finite G] in
theorem glaPPrimeCoreOf_centralizer_le_normalizer_glaDelta (p : ℕ) {A D : Subgroup G}
    (hDA : D ≤ A) : GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer (GLADelta p D : Set G) :=
  (glaPPrimeCoreOf_centralizer_le p A).trans
    ((centralizer_le_centralizer_of_le hDA).trans (centralizer_le_normalizer_glaDelta p D))

theorem not_dvd_card_thetaStarValue {p : ℕ} (hp : p.Prime) {A D : Subgroup G} (hDA : D ≤ A)
    (hD : D ≠ ⊥) : ¬ p ∣ Nat.card (thetaStarValue p A D) := by
  unfold thetaStarValue
  rw [sup_comm]
  exact not_dvd_card_sup_of_le_normalizer hp
    (glaPPrimeCoreOf_centralizer_le_normalizer_glaDelta p hDA)
    (not_dvd_card_glaPPrimeCoreOf hp _) (not_dvd_card_glaDelta hp hD)

omit [Finite G] in
theorem le_normalizer_sup {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  intro a ha
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (hH ha)
  have h2 := mem_normalizer_iff_gLBConj_eq.1 (hK ha)
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold GLBConj at h1 h2 ⊢
  rw [Subgroup.map_sup, h1, h2]

omit [Finite G] in
theorem le_normalizer_thetaStarValue {p : ℕ} {A D : Subgroup G} (hA : IsElemAbelian p A)
    (hDA : D ≤ A) : A ≤ Subgroup.normalizer (thetaStarValue p A D : Set G) :=
  le_normalizer_sup (le_normalizer_glaDelta hA hDA)
    ((le_centralizer_of_le_of_isElemAbelian hA le_rfl).trans (le_normalizer_glaPPrimeCoreOf p _))

end ThetaStar

section ThetaStarClosure

variable {G : Type} [Group G] [Finite G]

theorem thetaStarValue_inf_centralizer_le {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    {A D D' : Subgroup G} (hA : IsElemAbelian p A) (hwb : IsWeaklyBalancedWrt p k A)
    (hD : IsEkIn p k A D) (hD' : IsEkIn p k A D') :
    thetaStarValue p A D ⊓ Subgroup.centralizer (D' : Set G) ≤ thetaStarValue p A D' := by
  set O := GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) with hO
  set Y := thetaStarValue p A D ⊓ Subgroup.centralizer (D' : Set G) with hY
  have hDne : D ≠ ⊥ := hD.ne_bot hp hk
  have hOA : O ≤ Subgroup.centralizer (A : Set G) := glaPPrimeCoreOf_centralizer_le p A
  have hOΔ : O ≤ Subgroup.normalizer (GLADelta p D : Set G) :=
    glaPPrimeCoreOf_centralizer_le_normalizer_glaDelta p hD.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
    have h1 := le_normalizer_thetaStarValue (p := p) hA hD.1
    have h2 : A ≤ Subgroup.normalizer
        ((Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) :=
      (le_centralizer_of_le_of_isElemAbelian hA hD'.1).trans Subgroup.le_normalizer
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr ((Subgroup.mem_normalizer_iff.1 (h1 ha)) x)
      ((Subgroup.mem_normalizer_iff.1 (h2 ha)) x)
  have hYp : ¬ p ∣ Nat.card Y := fun h =>
    not_dvd_card_thetaStarValue hp hD.1 hDne (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hApg : IsPGroup p A := fun a => ⟨1, Subtype.ext (by simpa using hA.2 a a.2)⟩
  have hdec := le_commutator_sup_inf_centralizer_of_isPGroup hp hApg hAY hYp
  refine hdec.trans (sup_le ?_ ?_)
  ·
    refine le_trans ?_ (le_sup_left : GLADelta p D' ≤ thetaStarValue p A D')
    simp only [GLADelta]
    refine le_iInf fun x => le_iInf fun hx => le_iInf fun hx1 => ?_
    have hxA : x ∈ A := hD'.1 hx
    have hCx : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.centralizer_le (by simpa using hxA)
    have hYx : Y ≤ (GLADelta p D ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ O := by
      refine le_trans ?_ (sup_inf_le_inf_sup_of_le hOΔ (hOA.trans hCx))
      refine le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le ?_))
      simpa using hx
    have hOn : O ≤ Subgroup.normalizer
        ((GLADelta p D ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
      intro o ho
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      refine and_congr ((Subgroup.mem_normalizer_iff.1 (hOΔ ho)) z) ?_
      exact (Subgroup.mem_normalizer_iff.1
        (Subgroup.le_normalizer (hCx (hOA ho)) : o ∈ Subgroup.normalizer
          ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G)) z)
    calc ⁅Y, A⁆ ≤ ⁅(GLADelta p D ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ O, A⁆ :=
          Subgroup.commutator_mono hYx le_rfl
      _ ≤ ⁅GLADelta p D ⊓ Subgroup.centralizer ({x} : Set G), A⁆ :=
          commutator_sup_le_of_le_centralizer hOA hOn
      _ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := hwb D hD x hxA hx1
  ·
    refine le_trans ?_ (le_sup_right : O ≤ thetaStarValue p A D')
    have h1 : Y ⊓ Subgroup.centralizer (A : Set G) ≤
        (GLADelta p D ⊓ Subgroup.centralizer (A : Set G)) ⊔ O :=
      (inf_le_inf_right _ inf_le_left).trans (sup_inf_le_inf_sup_of_le hOΔ hOA)
    exact h1.trans (sup_le (glaDelta_inf_centralizer_le_glaPPrimeCoreOf hp hD.1 hDne) le_rfl)

omit [Finite G] in
theorem thetaStarClosure_eq_iSup {p k : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A)
    {D₀ : Subgroup G} (hD₀ : IsEkIn p k A D₀) :
    thetaStarClosure p k A =
      ⨆ (S : Subgroup G) (_ : S ∈ signalizerFunctorEk p k A), thetaStarValue p A S := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [thetaClosure_eq_iSup_signalizerFunctorEk hA]
      exact iSup₂_mono fun S _ => le_sup_left
    · exact le_iSup₂_of_le D₀ ((isEkIn_iff_mem_signalizerFunctorEk hA).1 hD₀) le_sup_right
  · refine iSup₂_le fun S hS => sup_le ?_ le_sup_right
    exact le_sup_of_le_left
      (le_iSup₂_of_le S ((isEkIn_iff_mem_signalizerFunctorEk hA).2 hS) le_rfl)

theorem thetaStarClosure_complete (hSF : SignalizerFunctorTheoremK) {p k : ℕ} (hp : p.Prime)
    (hk : 1 ≤ k) {A : Subgroup G} (hA : IsElemAbelian p A) (hrank : p ^ (k + 2) ≤ Nat.card A)
    (hwb : IsWeaklyBalancedWrt p k A)
    (hK : ∀ D : Subgroup G, IsEkIn p k A D →
      CFSG.SectionRank.IsKGroupCat ↥(thetaStarValue p A D)) :
    (Nat.Coprime p (Nat.card (thetaStarClosure p k A)) ∧
        A ≤ Subgroup.normalizer (thetaStarClosure p k A : Set G)) ∧
      ∀ D : Subgroup G, IsEkIn p k A D →
        thetaStarClosure p k A ⊓ Subgroup.centralizer (D : Set G) = thetaStarValue p A D := by
  have : Fact p.Prime := ⟨hp⟩
  have hE : ∀ S ∈ signalizerFunctorEk p k A, IsEkIn p k A S := fun S hS =>
    (isEkIn_iff_mem_signalizerFunctorEk hA).2 hS
  obtain ⟨n, hn⟩ := (show IsPGroup p A from fun a =>
    ⟨1, Subtype.ext (by simpa using hA.2 a a.2)⟩).exists_card_eq
  have hkn : k ≤ n := by
    have : p ^ (k + 2) ≤ p ^ n := hn ▸ hrank
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 this
    omega
  obtain ⟨D₀, hD₀A, hD₀el, hD₀card⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_elemAbelian_subgroup_card_pow hp hA hkn hn
  have hD₀ : IsEkIn p k A D₀ := ⟨hD₀A, hD₀el, hD₀card⟩
  obtain ⟨⟨hcop, hnorm⟩, hcent, -, -⟩ := hSF G p hp k hk A hA hrank (thetaStarValue p A)
    (fun S hS => sup_le ((glaDelta_le_centralizer p S))
      ((glaPPrimeCoreOf_centralizer_le p A).trans (centralizer_le_centralizer_of_le hS.1)))
    (fun S hS => (Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_card_thetaStarValue hp hS.1 ((hE S hS).ne_bot hp hk)))
    (fun S hS => le_normalizer_thetaStarValue hA hS.1)
    (fun S hS S' hS' => thetaStarValue_inf_centralizer_le hp hk hA hwb (hE S hS) (hE S' hS'))
    (fun S hS => hK S (hE S hS))
  rw [thetaStarClosure_eq_iSup hA hD₀]
  exact ⟨⟨hcop, hnorm⟩, fun D hD => hcent D ((isEkIn_iff_mem_signalizerFunctorEk hA).1 hD)⟩

end ThetaStarClosure

section Alpha

variable {G : Type} [Group G] [Finite G]

theorem alphaE_le_thetaClosure {p k : ℕ} (hp : p.Prime) {A E : Subgroup G}
    (hA : IsElemAbelian p A) (hE : IsEkIn p (k + 1) A E) :
    alphaE p k E ≤ thetaClosure p k A := by
  refine sup_le (iSup₂_le fun D hD => ?_) ?_
  · have hDA : D ≤ A := hD.1.trans hE.1
    exact (commutator_le_left_of_le_normalizer
      ((hE.1.trans (le_normalizer_glaDelta hA hDA)))).trans
        (le_iSup₂_of_le D ⟨hDA, hD.2⟩ le_rfl)
  · obtain ⟨D₀, hD₀E, hD₀el, hD₀card⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Proving.exists_elemAbelian_subgroup_card_pow hp hE.2.1
        (Nat.le_succ k) hE.2.2
    exact (glaDelta_anti hD₀E).trans
      (le_iSup₂_of_le D₀ ⟨hD₀E.trans hE.1, hD₀el, hD₀card⟩ le_rfl)

theorem alphaE_coprime (hSF : SignalizerFunctorTheoremK) {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    {A E : Subgroup G} (hA : IsElemAbelian p A) (hrank : p ^ (k + 2) ≤ Nat.card A)
    (hwb : IsWeaklyBalancedWrt p k A)
    (hK : ∀ D : Subgroup G, IsEkIn p k A D →
      CFSG.SectionRank.IsKGroupCat ↥(thetaStarValue p A D))
    (hE : IsEkIn p (k + 1) A E) : Nat.Coprime p (Nat.card (alphaE p k E)) := by
  obtain ⟨⟨hcop, -⟩, -⟩ := thetaStarClosure_complete hSF hp hk hA hrank hwb hK
  refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le ?_) hcop
  exact (alphaE_le_thetaClosure hp hA hE).trans le_sup_left

end Alpha

end CFSG.HardMathSupport.Solomon.Coordinator
