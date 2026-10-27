module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ClsRed
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge SporadicOrdersTable)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner_le_innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (CompOfType isL2three6)
open CFSG.LocalAnalysis.GLTheoremA.H1420.ClsRed (isPGroup_zpowers_three)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop1116Design (InputAltNotLie alt_chev_cases)

private theorem isAltType_six {X : Type} [Group X] (h : catalogIs X isA6) :
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.IsAltType 6 X := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  rcases hi with hi | hi
  · cases i with
    | alternating n hn =>
      have h6 : n = 6 := hi
      subst h6
      exact ⟨f⟩
    | _ => exact False.elim hi
  · exfalso
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact hi
        · have hq : q.card = 9 := hi
          exact ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
            ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2
              (Or.inl ⟨rfl, Or.inr (Or.inr hq)⟩))
        · exact hi
      | _ => exact hi
    | _ => exact hi

private theorem out_of_l2three6 {i : TauCeti.CFSGIndex} (h : isL2three6 i) : I1430Out i := by
  refine Or.inl (Or.inr (Or.inr ?_))
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A n q =>
      rcases n with _ | _ | n
      · exact False.elim h
      · exact h
      · exact False.elim h
    | _ => exact False.elim h
  | _ => exact False.elim h

private theorem out_of_sp48 {i : TauCeti.CFSGIndex} (h : isSp48 i) : I1430Out i := by
  refine Or.inl (Or.inr (Or.inr ?_))
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B n q =>
      rcases n with _ | _ | _ | _ | n
      · exact False.elim h
      · exact False.elim h
      · exact h
      · exact False.elim h
      · exact False.elim h
    | _ => exact False.elim h
  | _ => exact False.elim h

private theorem out_of_bOfTwo {i : TauCeti.CFSGIndex} {ℓ : ℕ} (hℓ : 3 ≤ ℓ) (h : isBOfTwo ℓ i) :
    I1430Out i := by
  rcases Nat.eq_or_lt_of_le hℓ with rfl | h4
  · refine Or.inl (Or.inr (Or.inr ?_))
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | B n q =>
        obtain ⟨rfl, hq⟩ := h
        exact hq
      | _ => exact False.elim h
    | _ => exact False.elim h
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ℓ, h4, h⟩)))

private theorem card_l2three6 (hB : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (h : catalogIs T isL2three6) : Nat.card T = 193709880 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A n q =>
      rcases n with _ | _ | n
      · exact False.elim hi
      · have hq : q.card = 729 := hi
        rw [hB ⟨_, hv⟩ T ⟨f⟩]
        show orderA 1 q.card = 193709880
        rw [hq]
        decide
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

private theorem card_bOfTwo (hB : LieOrderBridge) {T : Type} [Group T] [Finite T] {ℓ : ℕ}
    (h : catalogIs T (isBOfTwo ℓ)) : Nat.card T = orderBC ℓ 2 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B n q =>
      obtain ⟨rfl, hq⟩ := hi
      rw [hB ⟨_, hv⟩ T ⟨f⟩]
      show orderBC n q.card = orderBC n 2
      rw [hq]
    | _ => exact False.elim hi
  | _ => exact False.elim hi

private theorem orderBC_two_ne {ℓ N : ℕ} (hℓ : 3 ≤ ℓ) (hN : ¬ 2 ^ 16 ∣ N) (hN3 : N ≠ 1451520) :
    orderBC ℓ 2 ≠ N := by
  intro h
  rcases Nat.eq_or_lt_of_le hℓ with rfl | h4
  · apply hN3
    rw [← h]
    decide
  · apply hN
    rw [← h]
    have hd : 2 ^ (ℓ * ℓ) ∣ orderBC ℓ 2 := by
      unfold orderBC
      have h1 : Nat.gcd 2 (2 - 1) = 1 := by norm_num
      rw [h1, Nat.div_one]
      exact Dvd.intro _ rfl
    exact (pow_dvd_pow 2 (by nlinarith)).trans hd

variable {Q : Type} [Group Q] [Finite Q]

private theorem chevAut_eq_conj {K : Subgroup Q} (hKn : K.Normal) {y g : Q}
    (hyN : y ∈ Subgroup.normalizer (K : Set Q)) (hgK : g ∈ K)
    (hg : ∀ k ∈ K, y⁻¹ * k * y = g * k * g⁻¹) :
    chevAut 3 K ⟨y, hyN⟩ = MulAut.conj (chevQuotHom 3 K ⟨g⁻¹, K.inv_mem hgK⟩) := by
  ext t
  obtain ⟨k, rfl⟩ := chevQuotHom_surjective 3 K t
  rw [chevAut_chevQuotHom, MulAut.conj_apply]
  have h : K.normalizerMonoidHom ⟨y, hyN⟩ k =
      ⟨g⁻¹, K.inv_mem hgK⟩ * k * (⟨g⁻¹, K.inv_mem hgK⟩ : ↥K)⁻¹ := by
    apply Subtype.ext
    show y * (k : Q) * y⁻¹ = g⁻¹ * k * g⁻¹⁻¹
    have h1 := hg (y * k * y⁻¹) (hKn.conj_mem k k.2 y)
    have h2 : y⁻¹ * (y * (k : Q) * y⁻¹) * y = k := by group
    rw [h2] at h1
    calc y * (k : Q) * y⁻¹ = g⁻¹ * (g * (y * k * y⁻¹) * g⁻¹) * g⁻¹⁻¹ := by group
      _ = g⁻¹ * k * g⁻¹⁻¹ := by rw [← h1]
  rw [h, map_mul, map_mul, map_inv]

theorem i1430ClsLie_of_parts (hB : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hAlt : InputAltNotLie) (hD : ∀ q : ℕ, KDChevDownQ 3 q)
    (hL3 : I1430LieThree) (hI : I1430LieTwoInn) (hO : I1430LieTwoOut) : I1430ClsLie := by
  intro Q _ _ K I₀ y hM d he
  obtain ⟨e⟩ := he
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨hKn, -, -, hyN, hy3, -, hI₀, hIt, -⟩ := id hM
  have hyp := isPGroup_zpowers_three hy3
  have hβ1 := chevAut_ne_one hM
  have hβ3 : chevAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hyN hy3
  obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp hI₀
  have hJ := glaPComponent_chevTransfer hp hyN hyp hI₀
  have hJT : catalogIs (PSimple 3 (chevTransfer 3 K I₀)) isA6 := by
    obtain ⟨i, hi, ⟨f⟩⟩ := hIt.1
    exact ⟨i, hi, ⟨g.symm.trans f⟩⟩
  have hSs : IsSimpleGroup (PSimple 3 K) := (isQuasisimple_pQuot hM).2
  have hnab : ∃ a b : PSimple 3 K, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
      (isQuasisimple_pQuot hM)
  have eS : PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group := (pSimpleEquiv hM).trans e
  have hcomp : CompOfType (PSimple 3 K) (chevAut 3 K ⟨y, hyN⟩) isA6 := ⟨_, hJ, hJT⟩
  have hchS : IsChevSimple d.1.characteristic (PSimple 3 K) := Or.inl ⟨.lie d, rfl, ⟨eS⟩⟩
  have hchJ := hD d.1.characteristic (PSimple 3 K) hSs hnab hchS _ hβ3 _ hJ
  have hr : d.1.characteristic = 2 ∨ d.1.characteristic = 3 := by
    by_cases h2 : d.1.characteristic = 2
    · exact Or.inl h2
    · refine Or.inr ?_
      rcases alt_chev_cases hAlt h2 (by norm_num) (isAltType_six hJT) hchJ with
        ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · exact h
  rcases hr with h2 | h3
  · by_cases hin : chevAut 3 K ⟨y, hyN⟩ ∈ innAutDerived (PSimple 3 K)
    ·
      obtain ⟨ℓ, hℓ, hBl⟩ := hI (PSimple 3 K) hSs hnab d h2 ⟨eS⟩ _ hin hβ3 hβ1 hcomp
      have hc := card_bOfTwo hB (T := ↥K ⧸ Subgroup.center ↥K) ⟨.lie d, hBl, ⟨e⟩⟩
      refine ⟨⟨_, out_of_bOfTwo hℓ hBl, ⟨e⟩⟩, fun h => ?_, fun h => ?_⟩
      · exact absurd (hc.symm.trans (card_on hOrd h))
          (orderBC_two_ne hℓ (by decide) (by decide))
      · exact absurd (hc.symm.trans (card_sp48 hB h))
          (orderBC_two_ne hℓ (by decide) (by decide))
    ·
      have hSp := hO (PSimple 3 K) hSs hnab d h2 ⟨eS⟩ _ hin hβ3 hcomp
      have hcS : catalogIs (↥K ⧸ Subgroup.center ↥K) isSp48 := ⟨.lie d, hSp, ⟨e⟩⟩
      refine ⟨⟨_, out_of_sp48 hSp, ⟨e⟩⟩, fun h => ?_, fun _ hg => ?_⟩
      · exact absurd ((card_on hOrd h).symm.trans (card_sp48 hB hcS)) (by decide)
      · obtain ⟨g, hgK, hg⟩ := hg
        exact hin (inner_le_innAutDerived _ ⟨_, (chevAut_eq_conj hKn hyN hgK hg).symm⟩)
  ·
    have hL := hL3 (PSimple 3 K) hSs hnab d h3 ⟨eS⟩ _ hβ3 hβ1 hcomp
    have hc := card_l2three6 hB (T := ↥K ⧸ Subgroup.center ↥K) ⟨.lie d, hL, ⟨e⟩⟩
    refine ⟨⟨_, out_of_l2three6 hL, ⟨e⟩⟩, fun h => ?_, fun h => ?_⟩
    · exact absurd (hc.symm.trans (card_on hOrd h)) (by decide)
    · exact absurd (hc.symm.trans (card_sp48 hB h)) (by decide)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
