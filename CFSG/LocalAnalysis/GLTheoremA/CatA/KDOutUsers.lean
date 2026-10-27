module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.Holds
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma89
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open CFSG.ComponentClassification.CatLeafProof (lieOrderFormulasInput)
open CFSG.HardMathSupport.Solomon.Coordinator (lieOrderBridge_holds)
open scoped commutatorElement

section Certificates



private theorem isCatalogGroup_of_catalogIs' {S : Type} [Group S] {Q : TauCeti.CFSGIndex → Prop}
    (h : catalogIs S Q) : IsCatalogGroup S := by
  obtain ⟨i, -, e⟩ := h
  exact ⟨i, e⟩

private theorem isCatalogGroup_of_isChevSimple' {S : Type} [Group S] {r : ℕ}
    (h : IsChevSimple r S) : IsCatalogGroup S := by
  rcases h with h | h
  · exact isCatalogGroup_of_catalogIs' h
  · exact isCatalogGroup_of_catalogIs' h

section Lift

variable {G : Type} [Group G] [Finite G]

private theorem inducesInnerMod_of_comap {p : ℕ} {J : Subgroup G} [Group.IsPerfect (PQuot p J)]
    {g : G} (x : ↥(Subgroup.normalizer (J : Set G))) (hx : (x : G) = g⁻¹)
    (h : ((centerQuotientHom (PQuot p J)).comp (barAut p J)) x ∈ inner (PSimple p J)) :
    InducesInnerMod p J g := by
  have hxN : (x : G) ∈ Subgroup.normalizer (J : Set G) := x.2
  rw [hx] at hxN
  have hg : g ∈ Subgroup.normalizer (J : Set G) := inv_mem_iff.1 hxN
  have hxe : x = ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ := Subtype.ext hx
  subst hxe
  have h0 : centerQuotientHom (PQuot p J) (barAut p J ⟨g⁻¹, Subgroup.inv_mem _ hg⟩) ∈
      inner (PSimple p J) := h
  obtain ⟨u, hu0⟩ := mem_inner_of_centerQuotientHom_mem h0
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective u
  have hu : barAut p J ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ =
      MulAut.conj (QuotientGroup.mk w : PQuot p J) := hu0.symm
  refine ⟨((w : ↥J) : G)⁻¹, J.inv_mem w.2, fun y hy => ?_⟩
  set γ : ↥(Subgroup.normalizer (J : Set G)) := ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ with hγ
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom γ y : ↥J) : G) = g⁻¹ * y * g := fun y => by
    change (g⁻¹ : G) * y * (g⁻¹)⁻¹ = _
    rw [inv_inv]
  have h1 : barAut p J γ (QuotientGroup.mk ⟨y, hy⟩) =
      QuotientGroup.mk (w * ⟨y, hy⟩ * w⁻¹) := by
    rw [hu, MulAut.conj_apply]
    rfl
  rw [barAut_mk] at h1
  have h2 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) ∈
      GLAPPrimeCoreOf p J :=
    Subgroup.mem_map_of_mem J.subtype (QuotientGroup.eq.1 h1.symm)
  have h3 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) =
      (((w : G)⁻¹)⁻¹ * y * (w : G)⁻¹)⁻¹ * (g⁻¹ * y * g) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hs, inv_inv]
  rwa [h3] at h2

private theorem commutator_le_comap_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) (hcat : IsCatalogGroup (PSimple p J))
    (hexc : ¬ (p = 3 ∧ IsPOmegaEightPlusOdd (PSimple p J)))
    {P T : Subgroup G} (hP : IsPGroup p P) (hT : IsPGroup 2 T)
    (hPT : P ≤ Subgroup.normalizer (T : Set G)) :
    ⁅T.subgroupOf (Subgroup.normalizer (J : Set G)),
        P.subgroupOf (Subgroup.normalizer (J : Set G))⁆ ≤
      (inner (PSimple p J)).comap ((centerQuotientHom (PQuot p J)).comp (barAut p J)) := by
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  haveI : Group.IsPerfect (PQuot p J) := ⟨hq.1⟩
  have hsimple : IsSimpleGroup (PSimple p J) := hq.2
  have hnonab : ∃ a b : PSimple p J, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  set N : Subgroup G := Subgroup.normalizer (J : Set G) with hN
  set φ : ↥N →* MulAut (PSimple p J) := (centerQuotientHom (PQuot p J)).comp (barAut p J) with hφ
  have hBnorm : P.subgroupOf N ≤ Subgroup.normalizer ((T.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb t ht
    exact (Subgroup.mem_normalizer_iff.1 (hPT (Subgroup.mem_subgroupOf.1 hb)) (t : G)).1
      (Subgroup.mem_subgroupOf.1 ht)
  have hTp : IsPGroup 2 ((T.subgroupOf N).map φ) := hT.comap_subtype.map φ
  have hPp : IsPGroup p ((P.subgroupOf N).map φ) := hP.comap_subtype.map φ
  have hPT' : (P.subgroupOf N).map φ ≤
      Subgroup.normalizer (((T.subgroupOf N).map φ : Subgroup (MulAut (PSimple p J))) :
        Set (MulAut (PSimple p J))) :=
    (Subgroup.map_mono hBnorm).trans (Subgroup.le_normalizer_map φ)
  rcases kdOut_holds (PSimple p J) hsimple hnonab hcat p hp hp2 _ _ hPp hTp hPT' with h | h
  swap
  · exact absurd h hexc
  rw [Subgroup.commutator_le]
  intro t ht a ha
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact h (Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem φ ht)
    (Subgroup.mem_map_of_mem φ ha))

end Lift

section Exceptions

private theorem pow_twelve_dvd_orderD4 {q : TauCeti.PrimePower} (hq : q.p ≠ 2) :
    q.p ^ 12 ∣ CFSG.Open.orderD 4 q.card := by
  have hp : q.p.Prime := q.prime_p
  have hpc : q.p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
  have h2 : Nat.Coprime q.p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hq
  have hcop4 : Nat.Coprime q.p 4 := by
    have h := Nat.Coprime.pow_right 2 h2
    norm_num at h
    exact h
  set c := q.card with hc
  have hmul : Nat.gcd 4 (c ^ 4 - 1) * CFSG.Open.orderD 4 c =
      c ^ (4 * (4 - 1)) * ((c ^ 4 - 1) * ∏ i ∈ Finset.Icc 1 (4 - 1), (c ^ (2 * i) - 1)) := by
    have hGd : Nat.gcd 4 (c ^ 4 - 1) ∣
        c ^ (4 * (4 - 1)) * ((c ^ 4 - 1) * ∏ i ∈ Finset.Icc 1 (4 - 1), (c ^ (2 * i) - 1)) :=
      Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
    have h1 : c ^ (4 * (4 - 1)) * (c ^ 4 - 1) * ∏ i ∈ Finset.Icc 1 (4 - 1), (c ^ (2 * i) - 1) =
        c ^ (4 * (4 - 1)) * ((c ^ 4 - 1) * ∏ i ∈ Finset.Icc 1 (4 - 1), (c ^ (2 * i) - 1)) := by
      ring
    unfold CFSG.Open.orderD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have hcopG : Nat.Coprime q.p (Nat.gcd 4 (c ^ 4 - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) hcop4
  have hdvd : q.p ^ 12 ∣ Nat.gcd 4 (c ^ 4 - 1) * CFSG.Open.orderD 4 c := by
    rw [hmul]
    exact (pow_dvd_pow_of_dvd hpc 12).trans (dvd_mul_right _ _)
  exact (Nat.Coprime.pow_left 12 hcopG).dvd_of_dvd_mul_left hdvd

private theorem false_of_pow_twelve_dvd_small {S : Type} [Group S] [Finite S]
    {q : TauCeti.PrimePower} (hq2 : q.p ≠ 2) (hcard : Nat.card S = CFSG.Open.orderD 4 q.card)
    {N : ℕ} (hle : Nat.card S ≤ N) (hN : N < 531441) : False := by
  have hdvd : q.p ^ 12 ∣ Nat.card S := by
    rw [hcard]
    exact pow_twelve_dvd_orderD4 hq2
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h1 : q.p ^ 12 ≤ Nat.card S := Nat.le_of_dvd hpos hdvd
  have h2 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have h3 : 3 ^ 12 ≤ q.p ^ 12 := Nat.pow_le_pow_left h2 12
  have h4 : (3 : ℕ) ^ 12 = 531441 := by norm_num
  rw [h4] at h3
  omega

private theorem false_of_pow_twelve_dvd_co2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ^ 12 ∣ 42305421312000) : False := by
  have hle : p ≤ 13 := by
    by_contra hlt
    have h14 : 14 ≤ p := by omega
    have h1 : 14 ^ 12 ≤ p ^ 12 := Nat.pow_le_pow_left h14 12
    have h2 : p ^ 12 ≤ 42305421312000 := Nat.le_of_dvd (by norm_num) hd
    have h3 : (14 : ℕ) ^ 12 = 56693912375296 := by norm_num
    omega
  interval_cases p
  all_goals first
    | (norm_num at hp; done)
    | (norm_num at hp2; done)
    | (norm_num at hd; done)

private theorem false_of_charTwo_iso_D4 {S : Type} [Group S] [Finite S]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hq2 : q.p ≠ 2)
    (eD : S ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) : False := by
  obtain ⟨t, n, f, hX⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hd e
  have hadm := CFSG.SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hX
  have hBP : CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.POmegaPlus 4 q.p q.exponent :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [CFSG.Blueprint.classicalTags]) (CFSG.Models.lieModel_D 4 q hv eD)
  have hodd : CFSG.Blueprint.OddLieType S :=
    ⟨CFSG.Open.StatedLieTag.POmegaPlus, 4, q.p, q.exponent, q.prime_p, hq2,
      CFSG.SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hBP, hBP⟩
  have hmain := CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType
    lieOrderFormulasInput hX hodd
  have hO := lieOrderFormulasInput S t n 2 f hadm hX
  have hcard : Nat.card S = CFSG.Open.orderD 4 q.card :=
    lieOrderBridge_holds ⟨.D 4 q, hv⟩ S ⟨eD⟩
  rcases hmain with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have h := hO.2.1
    have hd : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor
        CFSG.Open.StatedLieTag.PSL 2 (2 ^ 2) = 1 := by decide
    have hn : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator
        CFSG.Open.StatedLieTag.PSL 2 (2 ^ 2) = 60 := by decide
    rw [hd, hn] at h
    exact false_of_pow_twelve_dvd_small hq2 hcard (N := 25920) (by omega) (by norm_num)
  · have h := hO.2.1
    have hd : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor
        CFSG.Open.StatedLieTag.PSL 3 (2 ^ 1) = 1 := by decide
    have hn : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator
        CFSG.Open.StatedLieTag.PSL 3 (2 ^ 1) = 168 := by decide
    rw [hd, hn] at h
    exact false_of_pow_twelve_dvd_small hq2 hcard (N := 25920) (by omega) (by norm_num)
  · have h := hO.2.1
    have hd : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor
        CFSG.Open.StatedLieTag.PSU 4 (2 ^ 1) = 1 := by decide
    have hn : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator
        CFSG.Open.StatedLieTag.PSU 4 (2 ^ 1) = 25920 := by decide
    rw [hd, hn] at h
    exact false_of_pow_twelve_dvd_small hq2 hcard (N := 25920) (by omega) (by norm_num)

private theorem card_alternating_of_iso {S : Type} [Group S] {n : ℕ} (hn : 5 ≤ n)
    (e : S ≃* (TauCeti.CFSGIndex.alternating n hn).Group) : Nat.card S = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [Nat.card_congr e.toEquiv]
  show Nat.card (alternatingGroup (Fin n)) = _
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem lieOrder_le_of_ambiguous_two (d : TauCeti.ValidLieTypeIndex)
    (h : ambiguousChev 2 (TauCeti.CFSGIndex.lie d)) :
    CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 ≤ 6048 := by
  obtain ⟨d, hvd⟩ := d
  cases d with
  | A r q =>
    rcases r with _ | _ | _ | _
    · exact absurd h (by simp [ambiguousChev])
    · have hq : q.card = 7 := by simpa [ambiguousChev] using h
      show CFSG.Open.orderA 1 q.card ≤ 6048
      rw [hq]
      decide
    · exact absurd h (by simp [ambiguousChev])
    · exact absurd h (by simp [ambiguousChev])
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · exact absurd h (by simp [ambiguousChev])
    · exact absurd h (by simp [ambiguousChev])
    · have hq : q.card = 3 := by simpa [ambiguousChev] using h
      show CFSG.Open.orderTwistedA 2 q.card ≤ 6048
      rw [hq]
      decide
    · exact absurd h (by simp [ambiguousChev])
    · exact absurd h (by simp [ambiguousChev])
  | B r q => exact absurd h (by simp [ambiguousChev])
  | C r q => exact absurd h (by simp [ambiguousChev])
  | D r q => exact absurd h (by simp [ambiguousChev])
  | twistedD r q => exact absurd h (by simp [ambiguousChev])
  | E6 q => exact absurd h (by simp [ambiguousChev])
  | E7 q => exact absurd h (by simp [ambiguousChev])
  | E8 q => exact absurd h (by simp [ambiguousChev])
  | F4 q => exact absurd h (by simp [ambiguousChev])
  | G2 q => exact absurd h (by simp [ambiguousChev])
  | twistedE6 q => exact absurd h (by simp [ambiguousChev])
  | trialityD4 q => exact absurd h (by simp [ambiguousChev])
  | suzuki m => exact absurd h (by simp [ambiguousChev])
  | reeG2 m => exact absurd h (by simp [ambiguousChev])
  | reeF4 m => exact absurd h (by simp [ambiguousChev])
  | tits => exact absurd h (by simp [ambiguousChev])

private theorem not_isPOmegaEightPlusOdd_of_isChevSimple_two {S : Type} [Group S] [Finite S]
    (h : IsChevSimple 2 S) : ¬ IsPOmegaEightPlusOdd S := by
  rintro ⟨q, hv, hq2, ⟨eD⟩⟩
  have hcard : Nat.card S = CFSG.Open.orderD 4 q.card :=
    lieOrderBridge_holds ⟨.D 4 q, hv⟩ S ⟨eD⟩
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic p hp => exact absurd hi (by simp [onLie])
    | alternating n hn => exact absurd hi (by simp [onLie])
    | sporadic s => exact absurd hi (by simp [onLie])
    | lie d => exact false_of_charTwo_iso_D4 d hi e hv hq2 eD
  · cases i with
    | cyclic p hp => exact absurd hi (by simp [ambiguousChev])
    | alternating n hn =>
      have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by simpa [ambiguousChev] using hi
      have hc := card_alternating_of_iso hn e
      refine false_of_pow_twelve_dvd_small hq2 hcard (N := 20160) ?_ (by norm_num)
      rw [hc]
      rcases hn' with rfl | rfl | rfl <;> decide
    | sporadic s => exact absurd hi (by simp [ambiguousChev])
    | lie d =>
      have hle := lieOrder_le_of_ambiguous_two d hi
      have hc : Nat.card S = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 :=
        lieOrderBridge_holds d S ⟨e⟩
      exact false_of_pow_twelve_dvd_small hq2 hcard (N := 6048) (by omega) (by norm_num)

end Exceptions

section ListExceptions

private theorem p_eq_two_of_card_dvd_two_pow {q : TauCeti.PrimePower} {k : ℕ}
    (h : q.card ∣ 2 ^ k) : q.p = 2 := by
  have hpc : q.p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
  have h1 : q.p ∣ 2 ^ k := hpc.trans h
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
    (q.prime_p.dvd_of_dvd_pow h1)


private theorem char_two_of_isSp8of2 (d : TauCeti.LieTypeIndex)
    (h : (fun | .B 4 q => q.card = 2 | _ => False : TauCeti.LieTypeIndex → Prop) d) :
    d.characteristic = 2 := by
  cases d with
  | A r q => exact absurd h (by simp)
  | twistedA r q => exact absurd h (by simp)
  | B r q =>
    rcases r with _ | _ | _ | _ | _ | r
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · have hq : q.card = 2 := h
      rw [TauCeti.LieTypeIndex.characteristic_B]
      exact p_eq_two_of_card_dvd_two_pow (k := 1) (by rw [hq]; norm_num)
    · exact absurd h (by simp)
  | C r q => exact absurd h (by simp)
  | D r q => exact absurd h (by simp)
  | twistedD r q => exact absurd h (by simp)
  | E6 q => exact absurd h (by simp)
  | E7 q => exact absurd h (by simp)
  | E8 q => exact absurd h (by simp)
  | F4 q => exact absurd h (by simp)
  | G2 q => exact absurd h (by simp)
  | twistedE6 q => exact absurd h (by simp)
  | trialityD4 q => exact absurd h (by simp)
  | suzuki m => exact absurd h (by simp)
  | reeG2 m => exact absurd h (by simp)
  | reeF4 m => exact absurd h (by simp)
  | tits  => exact absurd h (by simp)

private theorem char_two_of_isD4of2 (d : TauCeti.LieTypeIndex)
    (h : (fun | .D 4 q => q.card = 2 | _ => False : TauCeti.LieTypeIndex → Prop) d) :
    d.characteristic = 2 := by
  cases d with
  | A r q => exact absurd h (by simp)
  | twistedA r q => exact absurd h (by simp)
  | B r q => exact absurd h (by simp)
  | C r q => exact absurd h (by simp)
  | D r q =>
    rcases r with _ | _ | _ | _ | _ | r
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · have hq : q.card = 2 := h
      rw [TauCeti.LieTypeIndex.characteristic_D]
      exact p_eq_two_of_card_dvd_two_pow (k := 1) (by rw [hq]; norm_num)
    · exact absurd h (by simp)
  | twistedD r q => exact absurd h (by simp)
  | E6 q => exact absurd h (by simp)
  | E7 q => exact absurd h (by simp)
  | E8 q => exact absurd h (by simp)
  | F4 q => exact absurd h (by simp)
  | G2 q => exact absurd h (by simp)
  | twistedE6 q => exact absurd h (by simp)
  | trialityD4 q => exact absurd h (by simp)
  | suzuki m => exact absurd h (by simp)
  | reeG2 m => exact absurd h (by simp)
  | reeF4 m => exact absurd h (by simp)
  | tits  => exact absurd h (by simp)

private theorem char_two_of_isU5of2 (d : TauCeti.LieTypeIndex)
    (h : (fun | .twistedA 4 q => q.card = 2 | _ => False : TauCeti.LieTypeIndex → Prop) d) :
    d.characteristic = 2 := by
  cases d with
  | A r q => exact absurd h (by simp)
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | r
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · have hq : q.card = 2 := h
      rw [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact p_eq_two_of_card_dvd_two_pow (k := 1) (by rw [hq]; norm_num)
    · exact absurd h (by simp)
  | B r q => exact absurd h (by simp)
  | C r q => exact absurd h (by simp)
  | D r q => exact absurd h (by simp)
  | twistedD r q => exact absurd h (by simp)
  | E6 q => exact absurd h (by simp)
  | E7 q => exact absurd h (by simp)
  | E8 q => exact absurd h (by simp)
  | F4 q => exact absurd h (by simp)
  | G2 q => exact absurd h (by simp)
  | twistedE6 q => exact absurd h (by simp)
  | trialityD4 q => exact absurd h (by simp)
  | suzuki m => exact absurd h (by simp)
  | reeG2 m => exact absurd h (by simp)
  | reeF4 m => exact absurd h (by simp)
  | tits  => exact absurd h (by simp)

private theorem char_two_of_isU6of2 (d : TauCeti.LieTypeIndex)
    (h : (fun | .twistedA 5 q => q.card = 2 | _ => False : TauCeti.LieTypeIndex → Prop) d) :
    d.characteristic = 2 := by
  cases d with
  | A r q => exact absurd h (by simp)
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · have hq : q.card = 2 := h
      rw [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact p_eq_two_of_card_dvd_two_pow (k := 1) (by rw [hq]; norm_num)
    · exact absurd h (by simp)
  | B r q => exact absurd h (by simp)
  | C r q => exact absurd h (by simp)
  | D r q => exact absurd h (by simp)
  | twistedD r q => exact absurd h (by simp)
  | E6 q => exact absurd h (by simp)
  | E7 q => exact absurd h (by simp)
  | E8 q => exact absurd h (by simp)
  | F4 q => exact absurd h (by simp)
  | G2 q => exact absurd h (by simp)
  | twistedE6 q => exact absurd h (by simp)
  | trialityD4 q => exact absurd h (by simp)
  | suzuki m => exact absurd h (by simp)
  | reeG2 m => exact absurd h (by simp)
  | reeF4 m => exact absurd h (by simp)
  | tits  => exact absurd h (by simp)

private theorem char_two_of_isU4of8 (d : TauCeti.LieTypeIndex)
    (h : (fun | .twistedA 3 q => q.card = 8 | _ => False : TauCeti.LieTypeIndex → Prop) d) :
    d.characteristic = 2 := by
  cases d with
  | A r q => exact absurd h (by simp)
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · have hq : q.card = 8 := h
      rw [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact p_eq_two_of_card_dvd_two_pow (k := 3) (by rw [hq]; norm_num)
    · exact absurd h (by simp)
  | B r q => exact absurd h (by simp)
  | C r q => exact absurd h (by simp)
  | D r q => exact absurd h (by simp)
  | twistedD r q => exact absurd h (by simp)
  | E6 q => exact absurd h (by simp)
  | E7 q => exact absurd h (by simp)
  | E8 q => exact absurd h (by simp)
  | F4 q => exact absurd h (by simp)
  | G2 q => exact absurd h (by simp)
  | twistedE6 q => exact absurd h (by simp)
  | trialityD4 q => exact absurd h (by simp)
  | suzuki m => exact absurd h (by simp)
  | reeG2 m => exact absurd h (by simp)
  | reeF4 m => exact absurd h (by simp)
  | tits  => exact absurd h (by simp)


private theorem not_isPOmegaEightPlusOdd_of_i1431 {S : Type} [Group S] [Finite S]
    (h : catalogIs S S8.L89.i1431List) : ¬ IsPOmegaEightPlusOdd S := by
  rintro ⟨q, hv, hq2, ⟨eD⟩⟩
  have hcard : Nat.card S = CFSG.Open.orderD 4 q.card :=
    lieOrderBridge_holds ⟨.D 4 q, hv⟩ S ⟨eD⟩
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp =>
    exact absurd hi (by simp [S8.L89.i1431List, S8.sporIs, S8.L89.isSp8of2, S8.isD4of,
      S8.L89.isU5of2, S8.L89.isU6of2, S8.isU4of, onLie])
  | alternating n hn =>
    exact absurd hi (by simp [S8.L89.i1431List, S8.sporIs, S8.L89.isSp8of2, S8.isD4of,
      S8.L89.isU5of2, S8.L89.isU6of2, S8.isU4of, onLie])
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.Co2 := by
      simpa [S8.L89.i1431List, S8.sporIs, S8.L89.isSp8of2, S8.isD4of, S8.L89.isU5of2,
        S8.L89.isU6of2, S8.isU4of, onLie] using hi
    subst hs
    have hC : Nat.card S = 42305421312000 := by
      obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
      have h1 := Nat.card_congr f.toEquiv
      rw [CFSG.Sporadic.Co2.card_Co2] at h1
      exact (Nat.card_congr e.toEquiv).trans h1.symm
    have hdvd : q.p ^ 12 ∣ 42305421312000 := by
      rw [← hC, hcard]
      exact pow_twelve_dvd_orderD4 hq2
    exact false_of_pow_twelve_dvd_co2 q.prime_p hq2 hdvd
  | lie d =>
    simp only [S8.L89.i1431List] at hi
    rcases hi with hco | hsp8 | hd4 | hu5 | hu6 | hu4
    · exact absurd hco (by simp [S8.sporIs])
    · exact false_of_charTwo_iso_D4 d (char_two_of_isSp8of2 d.1 hsp8) e hv hq2 eD
    · exact false_of_charTwo_iso_D4 d (char_two_of_isD4of2 d.1 hd4) e hv hq2 eD
    · exact false_of_charTwo_iso_D4 d (char_two_of_isU5of2 d.1 hu5) e hv hq2 eD
    · exact false_of_charTwo_iso_D4 d (char_two_of_isU6of2 d.1 hu6) e hv hq2 eD
    · exact false_of_charTwo_iso_D4 d (char_two_of_isU4of8 d.1 hu4) e hv hq2 eD

end ListExceptions

theorem i71InnerAt_holds (G : Type) [Group G] [Finite G] : S8.L89.I71InnerAt G := by
  intro X J T D _hX hJ hcat hT hTN hD hDN hDT hTD t ht
  have hcat' : IsCatalogGroup (PSimple 3 J) := isCatalogGroup_of_catalogIs' hcat
  haveI : Group.IsPerfect (PQuot 3 J) := ⟨(isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ).1⟩
  have hexc : ¬ (3 = 3 ∧ IsPOmegaEightPlusOdd (PSimple 3 J)) := fun h =>
    not_isPOmegaEightPlusOdd_of_i1431 hcat h.2
  have hK := commutator_le_comap_inner Nat.prime_three (by norm_num) hJ hcat' hexc hD hT hDT
  have hTle : T.subgroupOf (Subgroup.normalizer (J : Set G)) ≤
      ⁅T.subgroupOf (Subgroup.normalizer (J : Set G)),
        D.subgroupOf (Subgroup.normalizer (J : Set G))⁆ := by
    rw [← Subgroup.map_le_map_iff_of_injective (Subgroup.subtype_injective _),
      Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTN,
      Subgroup.map_subgroupOf_eq_of_le hDN]
    exact hTD
  have htN : t ∈ Subgroup.normalizer (J : Set G) := hTN ht
  have hmem : (⟨t⁻¹, Subgroup.inv_mem _ htN⟩ : ↥(Subgroup.normalizer (J : Set G))) ∈
      T.subgroupOf (Subgroup.normalizer (J : Set G)) := by
    rw [Subgroup.mem_subgroupOf]
    exact T.inv_mem ht
  exact inducesInnerMod_of_comap (⟨t⁻¹, Subgroup.inv_mem _ htN⟩) rfl (hK (hTle hmem))

theorem i712At_holds (G : Type) [Group G] [Finite G] (p : ℕ) : I712At G p := by
  intro hp hp2 X L A T _hX hL hchev hA hT hAN hTN hAT a ha t ht
  have hcat : IsCatalogGroup (PSimple p L) := isCatalogGroup_of_isChevSimple' hchev
  haveI : Group.IsPerfect (PQuot p L) := ⟨(isQuasisimple_pQuot_of_glaPComponent hp hL).1⟩
  have hexc : ¬ (p = 3 ∧ IsPOmegaEightPlusOdd (PSimple p L)) := fun h =>
    not_isPOmegaEightPlusOdd_of_isChevSimple_two hchev h.2
  have hK := commutator_le_comap_inner hp hp2 hL hcat hexc hA hT hAT
  have htN : t ∈ Subgroup.normalizer (L : Set G) := hTN ht
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hAN ha
  have hcomm := Subgroup.commutator_mem_commutator
    (Subgroup.mem_subgroupOf.2 ht :
      (⟨t, htN⟩ : ↥(Subgroup.normalizer (L : Set G))) ∈
        T.subgroupOf (Subgroup.normalizer (L : Set G)))
    (Subgroup.mem_subgroupOf.2 ha :
      (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G))) ∈
        A.subgroupOf (Subgroup.normalizer (L : Set G)))
  have hx : (((⁅(⟨t, htN⟩ : ↥(Subgroup.normalizer (L : Set G))),
      (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁆ : ↥(Subgroup.normalizer (L : Set G))) : G)) =
      (⁅a, t⁆)⁻¹ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact inducesInnerMod_of_comap
    (⁅(⟨t, htN⟩ : ↥(Subgroup.normalizer (L : Set G))),
      (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁆) hx (hK hcomm)

end Certificates

end CFSG.LocalAnalysis.GLTheoremA
