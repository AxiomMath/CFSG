module

public import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear

public section

namespace CFSG.Semidihedral.SemilinearOddExtensions

noncomputable section

open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOuterQuotient
open scoped Pointwise

universe u v

abbrev specialLayer (K : Type u) [Field K] :=
  (coordinateG K).subgroupOf (coordinateE K)

abbrev linearLayer (K : Type u) [Field K] :=
  (coordinateD K).subgroupOf (coordinateE K)

@[expose] def fieldImage (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) : Subgroup (K ≃+* K) :=
  Gamma.map (fieldProjection K)

@[expose] def liftedField (K : Type u) [Field K] [Finite K]
    (A : Subgroup (K ≃+* K)) : Subgroup (coordinateE K) :=
  A.map (fieldLift K)

@[expose] def ambientImage (K : Type u) [Field K]
    (Gamma : Subgroup (coordinateE K)) : Subgroup (Equiv.Perm (Omega K)) :=
  Gamma.map (coordinateE K).subtype

theorem dihedralSylows_of_supplied {H : Type u} [Group H] [Finite H]
    (S : Sylow 2 H) {k : ℕ} (hk : 2 ≤ k)
    (e : S ≃* DihedralGroup (2 ^ (k - 1))) : HasDihedralSylowTwo H := by
  intro T
  exact ⟨k - 1, by omega, ⟨(Sylow.equiv T S).trans e⟩⟩

@[expose] def nativeSubgroup (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) : Subgroup (PGammaL2 K) :=
  Gamma.map (semilinearEquivCoordinateE K).symm.toMonoidHom

theorem nativeSubgroup_contains_psl (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) (hG : specialLayer K ≤ Gamma) :
    pGammaL2PSLRange K ≤ nativeSubgroup K Gamma := by
  have h := Subgroup.map_mono (f := (semilinearEquivCoordinateE K).symm.toMonoidHom) hG
  rw [specialLayer, ← semilinearPSLRange_map, Subgroup.map_map] at h
  simpa [nativeSubgroup] using h

theorem nativeSubgroup_field_image (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) :
    (pGammaL2FieldProjection K (nativeSubgroup K Gamma)).range = fieldImage K Gamma := by
  rw [pGammaL2FieldProjection, MonoidHom.range_comp, Subgroup.range_subtype,
    nativeSubgroup, Subgroup.map_map]
  rfl

theorem field_image_odd_of_card_gt_three (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (Gamma : Subgroup (coordinateE K)) (hG : specialLayer K ≤ Gamma)
    (hdihedral : HasDihedralSylowTwo Gamma) : Odd (Nat.card (fieldImage K Gamma)) := by
  let e := Subgroup.equivMapOfInjective Gamma
    (semilinearEquivCoordinateE K).symm.toMonoidHom
    (semilinearEquivCoordinateE K).symm.injective
  let : Finite (nativeSubgroup K Gamma) := Finite.of_equiv Gamma e.toEquiv
  have hnative : HasDihedralSylowTwo (nativeSubgroup K Gamma) :=
    hasDihedralSylowTwo_of_mulEquiv e.symm hdihedral
  rw [← nativeSubgroup_field_image]
  exact pGammaL2_field_projection_range_odd_of_dihedral K hK hcard
    (nativeSubgroup K Gamma) (nativeSubgroup_contains_psl K Gamma hG) hnative

theorem field_image_odd (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (Gamma : Subgroup (coordinateE K)) (hG : specialLayer K ≤ Gamma)
    (hdihedral : HasDihedralSylowTwo Gamma) : Odd (Nat.card (fieldImage K Gamma)) := by
  by_cases hcard : 3 < Nat.card K
  · exact field_image_odd_of_card_gt_three K hK hcard Gamma hG hdihedral
  · obtain ⟨p, f, hp, hodd, hf, hpow⟩ := hK
    have hp3 : 3 ≤ p := by
      have hp2 := hp.two_le
      have hn2 : p ≠ 2 := by intro h; subst p; norm_num at hodd
      omega
    have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hp_eq : p = 3 := by omega
    have hq : Nat.card K = 3 := by omega
    have hf_eq : f = 1 := Nat.pow_right_injective hp.two_le (by simpa [hp_eq] using hpow.symm.trans hq)
    have hAut : Nat.card (K ≃+* K) = 1 := by rw [fieldAut_card K hp hpow, hf_eq]
    have hd := Subgroup.card_subgroup_dvd_card (fieldImage K Gamma)
    rw [hAut] at hd
    rw [Nat.dvd_one.mp hd]
    decide

theorem field_image_card_dvd (K : Type u) [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hcard : Nat.card K = p ^ f)
    (Gamma : Subgroup (coordinateE K)) : Nat.card (fieldImage K Gamma) ∣ f := by
  rw [← fieldAut_card K hp hcard]
  exact Subgroup.card_subgroup_dvd_card _

theorem product_subgroup_eq_projections
    {Q : Type u} {H : Type v} [Group Q] [Group H]
    (hQ : Nat.card Q = 2) (B : Subgroup (Q × H))
    (hodd : Odd (Nat.card (B.map (MonoidHom.snd Q H)))) :
    B = (B.map (MonoidHom.fst Q H)).prod (B.map (MonoidHom.snd Q H)) := by
  let A := B.map (MonoidHom.snd Q H)
  have pure_right {q : Q} {a : H} (hqa : (q, a) ∈ B) : (1, a) ∈ B := by
    have ha : a ∈ A := ⟨(q, a), hqa, rfl⟩
    have ham : a ^ Nat.card A = 1 := by
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : A)))
    have hq2 : q ^ 2 = 1 := by simpa [hQ] using (pow_card_eq_one' (x := q))
    obtain ⟨t, ht⟩ := (show Odd (Nat.card A) from hodd).add_one
    have hqm : q ^ (Nat.card A + 1) = 1 := by
      rw [show Nat.card A + 1 = 2 * t by omega, pow_mul, hq2, one_pow]
    have hp := B.pow_mem hqa (Nat.card A + 1)
    rw [Prod.pow_mk, hqm, pow_succ, ham, one_mul] at hp
    exact hp
  have pure_left {q : Q} {a : H} (hqa : (q, a) ∈ B) : (q, 1) ∈ B := by
    have h := B.mul_mem hqa (B.inv_mem (pure_right hqa))
    simpa only [Prod.inv_mk, inv_one, Prod.mk_mul_mk, mul_one, mul_inv_cancel] using h
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  · rintro ⟨⟨qa, hqa, hq⟩, ⟨ta, hta, ha⟩⟩
    change qa.1 = x.1 at hq
    change ta.2 = x.2 at ha
    have h := B.mul_mem (pure_left hqa) (pure_right hta)
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, hq, ha, Prod.mk.eta] using h

theorem product_subgroup_two_cases
    {Q : Type u} {H : Type v} [Group Q] [Group H]
    (hQ : Nat.card Q = 2) (B : Subgroup (Q × H))
    (hodd : Odd (Nat.card (B.map (MonoidHom.snd Q H)))) :
    B = (⊥ : Subgroup Q).prod (B.map (MonoidHom.snd Q H)) ∨
      B = (⊤ : Subgroup Q).prod (B.map (MonoidHom.snd Q H)) := by
  let : Fact (Nat.Prime (Nat.card Q)) := ⟨by rw [hQ]; decide⟩
  have h := product_subgroup_eq_projections hQ B hodd
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (B.map (MonoidHom.fst Q H)) with hl | hl
  · exact Or.inl (by rwa [hl] at h)
  · exact Or.inr (by rwa [hl] at h)

@[expose] def outerImage (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K)) :=
  Gamma.map (theta K hK)

theorem outerImage_field_image (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K)) :
    (outerImage K hK Gamma).map (MonoidHom.snd _ _) = fieldImage K Gamma := by
  rw [outerImage, Subgroup.map_map]
  rfl

theorem outerImage_two_cases (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hodd : Odd (Nat.card (fieldImage K Gamma))) :
    outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma) ∨
      outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma) := by
  have h := product_subgroup_two_cases (squareClass_card_two K hK)
    (outerImage K hK Gamma) (by rwa [outerImage_field_image])
  simpa only [outerImage_field_image] using h

theorem gamma_eq_outer_preimage (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) :
    Gamma = (outerImage K hK Gamma).comap (theta K hK) := by
  exact (Subgroup.comap_map_eq_self (by rwa [theta_ker])).symm

theorem liftedField_le_gamma (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma))) :
    liftedField K (fieldImage K Gamma) ≤ Gamma := by
  rintro _ ⟨sigma, hsigma, rfl⟩
  rw [gamma_eq_outer_preimage K hK Gamma hG]
  change theta K hK (fieldLift K sigma) ∈ outerImage K hK Gamma
  rw [theta_fieldLift]
  rcases outerImage_two_cases K hK Gamma hodd with h | h
  · rw [h]
    exact ⟨(⊥ : Subgroup (SquareClass K)).one_mem, hsigma⟩
  · rw [h]
    exact ⟨trivial, hsigma⟩

theorem linearLayer_le_gamma_of_full_square_image (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma)
    (hB : outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    linearLayer K ≤ Gamma := by
  intro e he
  rw [gamma_eq_outer_preimage K hK Gamma hG]
  change theta K hK e ∈ outerImage K hK Gamma
  rw [hB]
  refine ⟨trivial, ?_⟩
  rw [theta_snd]
  have hd : e ∈ (fieldProjection K).ker := by rwa [fieldProjection_ker]
  exact (show fieldProjection K e = 1 from hd) ▸ (fieldImage K Gamma).one_mem

theorem linearPart_mem_special_of_trivial_square_image (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hB : outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma))
    (e : coordinateE K) (he : e ∈ Gamma) :
    linearInclusion K (linearPart K e) ∈ specialLayer K := by
  have htheta : theta K hK e ∈ (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma) :=
    hB ▸ Subgroup.mem_map_of_mem (theta K hK) he
  have hd : (theta K hK e).1 = 1 := htheta.1
  rw [coordinate_decomposition K e, map_mul, theta_linear, theta_fieldLift] at hd
  simp only [Prod.fst_mul, mul_one] at hd
  rw [specialLayer, ← theta_ker K hK]
  change theta K hK (linearInclusion K (linearPart K e)) = 1
  rw [theta_linear]
  exact Prod.ext hd rfl

theorem gamma_factorization_special (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hB : outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma))
    (e : Gamma) :
    ∃ g : specialLayer K, ∃ a : liftedField K (fieldImage K Gamma),
      (e : coordinateE K) = g * a := by
  refine ⟨⟨linearInclusion K (linearPart K e),
    linearPart_mem_special_of_trivial_square_image K hK Gamma hB e e.property⟩,
    ⟨fieldLift K (fieldProjection K e), ?_⟩, coordinate_decomposition K e⟩
  exact ⟨fieldProjection K e, ⟨e, e.property, rfl⟩, rfl⟩

theorem gamma_factorization_linear (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) (e : Gamma) :
    ∃ d : linearLayer K, ∃ a : liftedField K (fieldImage K Gamma),
      (e : coordinateE K) = d * a := by
  refine ⟨⟨linearInclusion K (linearPart K e), (linearPart K e).property⟩,
    ⟨fieldLift K (fieldProjection K e), ?_⟩, coordinate_decomposition K e⟩
  exact ⟨fieldProjection K e, ⟨e, e.property, rfl⟩, rfl⟩

theorem linearLayer_disjoint_liftedField (K : Type u) [Field K] [Finite K]
    (A : Subgroup (K ≃+* K)) : Disjoint (linearLayer K) (liftedField K A) := by
  apply disjoint_iff_inf_le.mpr
  rintro e ⟨hd, sigma, hsigma, he⟩
  have hfield : fieldProjection K e = 1 := by
    exact (show e ∈ (fieldProjection K).ker by rwa [fieldProjection_ker])
  rw [← he, fieldProjection_fieldLift] at hfield
  have hone : e = 1 := by rw [← he, hfield, map_one]
  exact hone ▸ (⊥ : Subgroup (coordinateE K)).one_mem

theorem specialLayer_disjoint_liftedField (K : Type u) [Field K] [Finite K]
    (A : Subgroup (K ≃+* K)) : Disjoint (specialLayer K) (liftedField K A) :=
  (linearLayer_disjoint_liftedField K A).mono_left
    (Subgroup.subgroupOf_mono (coordinateE K) (coordinateG_le_D K))

theorem factorization_isComplement
    {H : Type u} [Group H] (Gamma N L : Subgroup H)
    (hN : N ≤ Gamma) (hL : L ≤ Gamma) (hdis : Disjoint N L)
    (hfactor : ∀ e : Gamma, ∃ n : N, ∃ l : L, (e : H) = n * l) :
    (N.subgroupOf Gamma).IsComplement' (L.subgroupOf Gamma) := by
  have hdis' : Disjoint (N.subgroupOf Gamma) (L.subgroupOf Gamma) := by
    apply disjoint_iff_inf_le.mpr
    intro e he
    have h : (e : H) ∈ (⊥ : Subgroup H) :=
      (disjoint_iff_inf_le.mp hdis) ⟨he.1, he.2⟩
    exact Subtype.ext (show (e : H) = 1 from h)
  refine ⟨Subgroup.mul_injective_of_disjoint hdis', ?_⟩
  intro e
  obtain ⟨n, l, he⟩ := hfactor e
  refine ⟨(⟨⟨n, hN n.property⟩, n.property⟩, ⟨⟨l, hL l.property⟩, l.property⟩), ?_⟩
  exact Subtype.ext he.symm

theorem gamma_internal_special (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma)))
    (hB : outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    ((specialLayer K).subgroupOf Gamma).IsComplement'
      ((liftedField K (fieldImage K Gamma)).subgroupOf Gamma) :=
  factorization_isComplement Gamma (specialLayer K) (liftedField K (fieldImage K Gamma))
    hG (liftedField_le_gamma K hK Gamma hG hodd)
    (specialLayer_disjoint_liftedField K _) (gamma_factorization_special K hK Gamma hB)

theorem gamma_internal_linear (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma)))
    (hB : outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    ((linearLayer K).subgroupOf Gamma).IsComplement'
      ((liftedField K (fieldImage K Gamma)).subgroupOf Gamma) :=
  factorization_isComplement Gamma (linearLayer K) (liftedField K (fieldImage K Gamma))
    (linearLayer_le_gamma_of_full_square_image K hK Gamma hG hB)
    (liftedField_le_gamma K hK Gamma hG hodd)
    (linearLayer_disjoint_liftedField K _) (gamma_factorization_linear K Gamma)

abbrev GammaQuotient (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) :=
  Gamma ⧸ (specialLayer K).subgroupOf Gamma

@[expose] def restrictedTheta (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K)) :
    Gamma →* outerImage K hK Gamma := (theta K hK).subgroupMap Gamma

theorem restrictedTheta_ker (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K)) :
    (restrictedTheta K hK Gamma).ker = (specialLayer K).subgroupOf Gamma := by
  ext e
  change restrictedTheta K hK Gamma e = 1 ↔ _
  rw [Subtype.ext_iff]
  change theta K hK (e : coordinateE K) = 1 ↔ _
  rw [← MonoidHom.mem_ker, theta_ker]
  rfl

@[expose] def gammaQuotientEquivOuter (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K)) :
    GammaQuotient K Gamma ≃* outerImage K hK Gamma :=
  QuotientGroup.liftEquiv ((specialLayer K).subgroupOf Gamma)
    ((theta K hK).subgroupMap_surjective Gamma) (restrictedTheta_ker K hK Gamma).symm

theorem gammaQuotientEquivOuter_mk (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K)) (e : Gamma) :
    gammaQuotientEquivOuter K hK Gamma (QuotientGroup.mk e) = restrictedTheta K hK Gamma e :=
  QuotientGroup.liftEquiv_mk _ _ _ e

@[expose] def subgroupEquivOfEq {H : Type u} [Group H] {N L : Subgroup H} (h : N = L) :
    N ≃* L where
  toFun x := ⟨x, h ▸ x.property⟩
  invFun x := ⟨x, h.symm ▸ x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] def gammaQuotientEquivField (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hB : outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    GammaQuotient K Gamma ≃* fieldImage K Gamma :=
  (gammaQuotientEquivOuter K hK Gamma).trans
    ((subgroupEquivOfEq hB).trans
      ((Subgroup.prodEquiv _ _).trans MulEquiv.uniqueProd))

@[expose] def gammaQuotientEquivSquareField (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hB : outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    GammaQuotient K Gamma ≃* SquareClass K × fieldImage K Gamma :=
  (gammaQuotientEquivOuter K hK Gamma).trans
    ((subgroupEquivOfEq hB).trans
      ((Subgroup.prodEquiv _ _).trans
        (MulEquiv.prodCongr Subgroup.topEquiv (MulEquiv.refl _))))

theorem gammaQuotientEquivField_mk (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hB : outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma))
    (e : Gamma) :
    (gammaQuotientEquivField K hK Gamma hB (QuotientGroup.mk e) : K ≃+* K) =
      fieldProjection K e := rfl

theorem gammaQuotientEquivSquareField_mk (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hB : outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma))
    (e : Gamma) :
    (gammaQuotientEquivSquareField K hK Gamma hB (QuotientGroup.mk e)).1 =
      (theta K hK e).1 ∧
    ((gammaQuotientEquivSquareField K hK Gamma hB (QuotientGroup.mk e)).2 : K ≃+* K) =
      fieldProjection K e := ⟨rfl, rfl⟩

theorem gamma_quotient_special_card (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hB : outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    Nat.card (GammaQuotient K Gamma) = Nat.card (fieldImage K Gamma) :=
  Nat.card_congr (gammaQuotientEquivField K hK Gamma hB).toEquiv

theorem gamma_quotient_linear_card (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hB : outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    Nat.card (GammaQuotient K Gamma) = 2 * Nat.card (fieldImage K Gamma) := by
  rw [Nat.card_congr (gammaQuotientEquivSquareField K hK Gamma hB).toEquiv,
    Nat.card_prod, squareClass_card_two K hK]

theorem gamma_quotient_special_cyclic (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hB : outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    IsCyclic (GammaQuotient K Gamma) := by
  let : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  exact (gammaQuotientEquivField K hK Gamma hB).isCyclic.mpr inferInstance

theorem gamma_quotient_linear_cyclic (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hodd : Odd (Nat.card (fieldImage K Gamma)))
    (hB : outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    IsCyclic (GammaQuotient K Gamma) := by
  let : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have hQ : IsCyclic (SquareClass K) := isCyclic_of_prime_card (squareClass_card_two K hK)
  have hprod : IsCyclic (SquareClass K × fieldImage K Gamma) :=
    Group.isCyclic_prod_iff.mpr ⟨hQ, inferInstance, by
      rw [squareClass_card_two K hK, Nat.coprime_two_left]; exact hodd⟩
  exact (gammaQuotientEquivSquareField K hK Gamma hB).isCyclic.mpr hprod

@[expose] def internalAction {H : Type u} [Group H] (N L : Subgroup H) [N.Normal] :
    L →* MulAut N :=
  N.normalizerMonoidHom.comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))

theorem internalAction_coe {H : Type u} [Group H] (N L : Subgroup H) [N.Normal]
    (l : L) (n : N) : (internalAction N L l n : H) = l * n * (l : H)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe N _ n

@[expose] def internalSemidirectEquiv {H : Type u} [Group H]
    (N L : Subgroup H) [N.Normal] (h : N.IsComplement' L) :
    N ⋊[internalAction N L] L ≃* H := SemidirectProduct.mulEquivSubgroup h

theorem internalSemidirectEquiv_apply {H : Type u} [Group H]
    (N L : Subgroup H) [N.Normal] (h : N.IsComplement' L)
    (x : N ⋊[internalAction N L] L) : internalSemidirectEquiv N L h x = x.left * x.right :=
  SemidirectProduct.mulEquivSubgroup_apply h x

theorem factorization_set_eq {H : Type u} [Group H] (Gamma N L : Subgroup H)
    (hN : N ≤ Gamma) (hL : L ≤ Gamma)
    (hfactor : ∀ e : Gamma, ∃ n : N, ∃ l : L, (e : H) = n * l) :
    (Gamma : Set H) = (N : Set H) * (L : Set H) := by
  ext e
  constructor
  · intro he
    obtain ⟨n, l, h⟩ := hfactor ⟨e, he⟩
    exact ⟨n, n.property, l, l.property, h.symm⟩
  · rintro ⟨n, hn, l, hl, rfl⟩
    exact Gamma.mul_mem (hN hn) (hL hl)

theorem map_factorization_set_eq {H : Type u} {J : Type v} [Group H] [Group J]
    (phi : H →* J) (Gamma N L : Subgroup H)
    (hN : N ≤ Gamma) (hL : L ≤ Gamma)
    (hfactor : ∀ e : Gamma, ∃ n : N, ∃ l : L, (e : H) = n * l) :
    ((Gamma.map phi : Subgroup J) : Set J) =
      ((N.map phi : Subgroup J) : Set J) * ((L.map phi : Subgroup J) : Set J) := by
  rw [Subgroup.coe_map, factorization_set_eq Gamma N L hN hL hfactor, Set.image_mul,
    ← Subgroup.coe_map, ← Subgroup.coe_map]

@[expose] def ambientLiftedField (K : Type u) [Field K] [Finite K]
    (A : Subgroup (K ≃+* K)) : Subgroup (Equiv.Perm (Omega K)) :=
  ambientImage K (liftedField K A)

theorem ambientLiftedField_mem (K : Type u) [Field K] [Finite K]
    (A : Subgroup (K ≃+* K)) (e : Equiv.Perm (Omega K)) :
    e ∈ ambientLiftedField K A ↔ ∃ sigma ∈ A, fieldExtension K sigma = e := by
  constructor
  · rintro ⟨x, ⟨sigma, hsigma, rfl⟩, rfl⟩
    exact ⟨sigma, hsigma, (fieldLift_coe K sigma).symm⟩
  · rintro ⟨sigma, hsigma, rfl⟩
    exact ⟨fieldLift K sigma, ⟨sigma, hsigma, rfl⟩, fieldLift_coe K sigma⟩

theorem ambient_special_factorization (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma)))
    (hB : outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    (ambientImage K Gamma : Set (Equiv.Perm (Omega K))) =
      (coordinateG K : Set (Equiv.Perm (Omega K))) *
        (ambientLiftedField K (fieldImage K Gamma) : Set (Equiv.Perm (Omega K))) := by
  have h := map_factorization_set_eq (coordinateE K).subtype Gamma (specialLayer K)
    (liftedField K (fieldImage K Gamma)) hG (liftedField_le_gamma K hK Gamma hG hodd)
    (gamma_factorization_special K hK Gamma hB)
  rw [specialLayer, Subgroup.map_subgroupOf_eq_of_le
    ((coordinateG_le_D K).trans (coordinateD_le_E K))] at h
  exact h

theorem ambient_linear_factorization (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma)))
    (hB : outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    (ambientImage K Gamma : Set (Equiv.Perm (Omega K))) =
      (coordinateD K : Set (Equiv.Perm (Omega K))) *
        (ambientLiftedField K (fieldImage K Gamma) : Set (Equiv.Perm (Omega K))) := by
  have h := map_factorization_set_eq (coordinateE K).subtype Gamma (linearLayer K)
    (liftedField K (fieldImage K Gamma))
    (linearLayer_le_gamma_of_full_square_image K hK Gamma hG hB)
    (liftedField_le_gamma K hK Gamma hG hodd) (gamma_factorization_linear K Gamma)
  rw [linearLayer, Subgroup.map_subgroupOf_eq_of_le (coordinateD_le_E K)] at h
  exact h

theorem gamma_index_eq_quotient_card (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) :
    (specialLayer K).relIndex Gamma = Nat.card (GammaQuotient K Gamma) :=
  Subgroup.index_eq_card _

theorem gamma_index_even_iff_full_square_image (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hodd : Odd (Nat.card (fieldImage K Gamma))) :
    Even ((specialLayer K).relIndex Gamma) ↔
      outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma) := by
  rcases outerImage_two_cases K hK Gamma hodd with hB | hB
  · have hindex : (specialLayer K).relIndex Gamma = Nat.card (fieldImage K Gamma) := by
      rw [gamma_index_eq_quotient_card, gamma_quotient_special_card K hK Gamma hB]
    constructor
    · intro he
      exact False.elim (Nat.not_even_iff_odd.mpr hodd (hindex ▸ he))
    · intro hfull
      have h2 := gamma_quotient_linear_card K hK Gamma hfull
      rw [gamma_quotient_special_card K hK Gamma hB] at h2
      have hpos := (show Odd (Nat.card (fieldImage K Gamma)) from hodd).pos
      omega
  · refine ⟨fun _ => hB, fun _ => ?_⟩
    rw [gamma_index_eq_quotient_card, gamma_quotient_linear_card K hK Gamma hB]
    exact even_two_mul _

theorem fieldLift_injective (K : Type u) [Field K] [Finite K] :
    Function.Injective (fieldLift K) := by
  intro sigma tau h
  have h' := congrArg (fieldProjection K) h
  simpa only [fieldProjection_fieldLift] using h'

@[expose] def liftedFieldEquiv (K : Type u) [Field K] [Finite K]
    (A : Subgroup (K ≃+* K)) : liftedField K A ≃* A :=
  (Subgroup.equivMapOfInjective A (fieldLift K) (fieldLift_injective K)).symm

theorem liftedFieldEquiv_symm_coe (K : Type u) [Field K] [Finite K]
    (A : Subgroup (K ≃+* K)) (a : A) :
    ((liftedFieldEquiv K A).symm a : Equiv.Perm (Omega K)) = fieldExtension K a := by
  have h := Subgroup.coe_equivMapOfInjective_apply A (fieldLift K) (fieldLift_injective K) a
  exact (congrArg (fun e : coordinateE K => (e : Equiv.Perm (Omega K))) h).trans
    (fieldLift_coe K a)

theorem fieldProjection_map_liftedField (K : Type u) [Field K] [Finite K]
    (A : Subgroup (K ≃+* K)) : (liftedField K A).map (fieldProjection K) = A := by
  rw [liftedField, Subgroup.map_map]
  have h : (fieldProjection K).comp (fieldLift K) = MonoidHom.id _ := by
    exact MonoidHom.ext (fieldProjection_fieldLift K)
  rw [h, Subgroup.map_id]

theorem factorization_sup_eq {H : Type u} [Group H] (Gamma N L : Subgroup H)
    (hN : N ≤ Gamma) (hL : L ≤ Gamma)
    (hfactor : ∀ e : Gamma, ∃ n : N, ∃ l : L, (e : H) = n * l) :
    Gamma = N ⊔ L := by
  apply le_antisymm
  · intro e he
    obtain ⟨n, l, h⟩ := hfactor ⟨e, he⟩
    change e = (n : H) * l at h
    rw [h]
    exact Subgroup.mul_mem_sup n.property l.property
  · exact sup_le hN hL

theorem ambientImage_specialLayer (K : Type u) [Field K] :
    ambientImage K (specialLayer K) = coordinateG K :=
  Subgroup.map_subgroupOf_eq_of_le ((coordinateG_le_D K).trans (coordinateD_le_E K))

theorem ambientImage_linearLayer (K : Type u) [Field K] :
    ambientImage K (linearLayer K) = coordinateD K :=
  Subgroup.map_subgroupOf_eq_of_le (coordinateD_le_E K)

theorem ambient_index_eq (K : Type u) [Field K]
    (Gamma : Subgroup (coordinateE K)) :
    (coordinateG K).relIndex (ambientImage K Gamma) = (specialLayer K).relIndex Gamma := by
  rw [← ambientImage_specialLayer]
  exact Subgroup.relIndex_map_map_of_injective (specialLayer K) Gamma
    (coordinateE K).subtype_injective

theorem gamma_special_eq_sup (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma)))
    (hB : outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    Gamma = specialLayer K ⊔ liftedField K (fieldImage K Gamma) :=
  factorization_sup_eq Gamma _ _ hG (liftedField_le_gamma K hK Gamma hG hodd)
    (gamma_factorization_special K hK Gamma hB)

theorem gamma_linear_eq_sup (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma)))
    (hB : outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    Gamma = linearLayer K ⊔ liftedField K (fieldImage K Gamma) :=
  factorization_sup_eq Gamma _ _ (linearLayer_le_gamma_of_full_square_image K hK Gamma hG hB)
    (liftedField_le_gamma K hK Gamma hG hodd) (gamma_factorization_linear K Gamma)

theorem fieldImage_special_sup (K : Type u) [Field K] [Finite K]
    (A : Subgroup (K ≃+* K)) :
    fieldImage K (specialLayer K ⊔ liftedField K A) = A := by
  rw [fieldImage, Subgroup.map_sup, fieldProjection_map_liftedField]
  have h : (specialLayer K).map (fieldProjection K) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [fieldProjection_ker]
    exact Subgroup.subgroupOf_mono (coordinateE K) (coordinateG_le_D K)
  rw [h, bot_sup_eq]

theorem fieldImage_linear_sup (K : Type u) [Field K] [Finite K]
    (A : Subgroup (K ≃+* K)) :
    fieldImage K (linearLayer K ⊔ liftedField K A) = A := by
  rw [fieldImage, Subgroup.map_sup, fieldProjection_map_liftedField]
  have h : (linearLayer K).map (fieldProjection K) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [fieldProjection_ker]
  rw [h, bot_sup_eq]

theorem ambientImage_injective (K : Type u) [Field K] : Function.Injective (ambientImage K) :=
  Subgroup.map_injective (coordinateE K).subtype_injective

theorem fieldImage_eq_of_ambient_decomposition (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) (A : Subgroup (K ≃+* K))
    (h : ambientImage K Gamma = coordinateG K ⊔ ambientLiftedField K A ∨
      ambientImage K Gamma = coordinateD K ⊔ ambientLiftedField K A) :
    fieldImage K Gamma = A := by
  rcases h with h | h
  · have hs : Gamma = specialLayer K ⊔ liftedField K A := by
      apply ambientImage_injective K
      change ambientImage K Gamma =
        (specialLayer K ⊔ liftedField K A).map (coordinateE K).subtype
      rw [Subgroup.map_sup, ← ambientImage, ambientImage_specialLayer]
      exact h
    rw [hs, fieldImage_special_sup]
  · have hs : Gamma = linearLayer K ⊔ liftedField K A := by
      apply ambientImage_injective K
      change ambientImage K Gamma =
        (linearLayer K ⊔ liftedField K A).map (coordinateE K).subtype
      rw [Subgroup.map_sup, ← ambientImage, ambientImage_linearLayer]
      exact h
    rw [hs, fieldImage_linear_sup]

@[expose] def InternalCoordinateSemidirect (K : Type u) [Field K] [Finite K]
    (Gamma N : Subgroup (coordinateE K)) [N.Normal] (A : Subgroup (K ≃+* K)) : Prop :=
  ∃ iso : N.subgroupOf Gamma ⋊[internalAction (N.subgroupOf Gamma)
      ((liftedField K A).subgroupOf Gamma)] (liftedField K A).subgroupOf Gamma ≃* Gamma,
    ∀ x, ((iso x : coordinateE K) : Equiv.Perm (Omega K)) =
      (((x.left : Gamma) : coordinateE K) : Equiv.Perm (Omega K)) *
        (((x.right : Gamma) : coordinateE K) : Equiv.Perm (Omega K))

theorem internalCoordinateSemidirect_of_complement (K : Type u) [Field K] [Finite K]
    (Gamma N : Subgroup (coordinateE K)) [N.Normal] (A : Subgroup (K ≃+* K))
    (h : (N.subgroupOf Gamma).IsComplement' ((liftedField K A).subgroupOf Gamma)) :
    InternalCoordinateSemidirect K Gamma N A := by
  refine ⟨internalSemidirectEquiv _ _ h, ?_⟩
  intro x
  have hh := congrArg (fun e : Gamma => ((e : coordinateE K) : Equiv.Perm (Omega K)))
    (internalSemidirectEquiv_apply _ _ h x)
  exact hh

@[expose] def ExtensionCase (K : Type u) [Field K] [Finite K]
    (Gamma N : Subgroup (coordinateE K)) [N.Normal]
    (A : Subgroup (K ≃+* K)) (m : ℕ) : Prop :=
  N ≤ Gamma ∧ liftedField K A ≤ Gamma ∧ Gamma = N ⊔ liftedField K A ∧
    ambientImage K Gamma = ambientImage K N ⊔ ambientLiftedField K A ∧
    (ambientImage K Gamma : Set (Equiv.Perm (Omega K))) =
      (ambientImage K N : Set (Equiv.Perm (Omega K))) *
        (ambientLiftedField K A : Set (Equiv.Perm (Omega K))) ∧
    (N.subgroupOf Gamma).IsComplement' ((liftedField K A).subgroupOf Gamma) ∧
    InternalCoordinateSemidirect K Gamma N A ∧
    Nat.card (GammaQuotient K Gamma) = m * Nat.card A ∧
    (specialLayer K).relIndex Gamma = m * Nat.card A ∧ IsCyclic (GammaQuotient K Gamma)

@[expose] def SpecialExtension (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) (A : Subgroup (K ≃+* K)) : Prop :=
  ExtensionCase K Gamma (specialLayer K) A 1 ∧
    ∃ iso : GammaQuotient K Gamma ≃* A,
      ∀ e : Gamma, (iso (QuotientGroup.mk e) : K ≃+* K) = fieldProjection K e

@[expose] def LinearExtension (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) (A : Subgroup (K ≃+* K)) : Prop :=
  ExtensionCase K Gamma (linearLayer K) A 2 ∧
    ∃ iso : GammaQuotient K Gamma ≃* SquareClass K × A,
      ∀ e : Gamma, ((iso (QuotientGroup.mk e)).2 : K ≃+* K) = fieldProjection K e

theorem specialExtension_of_square_image (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma)))
    (hB : outerImage K hK Gamma = (⊥ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    SpecialExtension K Gamma (fieldImage K Gamma) := by
  have hsup := gamma_special_eq_sup K hK Gamma hG hodd hB
  have hcard := gamma_quotient_special_card K hK Gamma hB
  have hi : (specialLayer K).relIndex Gamma = Nat.card (fieldImage K Gamma) :=
    (gamma_index_eq_quotient_card K Gamma).trans hcard
  have hcomp := gamma_internal_special K hK Gamma hG hodd hB
  refine ⟨⟨hG, liftedField_le_gamma K hK Gamma hG hodd, hsup, ?_, ?_, hcomp,
    internalCoordinateSemidirect_of_complement K Gamma (specialLayer K) _ hcomp,
    by simpa using hcard, by simpa using hi,
    gamma_quotient_special_cyclic K hK Gamma hB⟩,
    gammaQuotientEquivField K hK Gamma hB, gammaQuotientEquivField_mk K hK Gamma hB⟩
  · rw [hsup, fieldImage_special_sup]
    exact Subgroup.map_sup (specialLayer K) (liftedField K (fieldImage K Gamma))
      (coordinateE K).subtype
  · rw [ambientImage_specialLayer]
    exact ambient_special_factorization K hK Gamma hG hodd hB

theorem linearExtension_of_square_image (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma)))
    (hB : outerImage K hK Gamma = (⊤ : Subgroup (SquareClass K)).prod (fieldImage K Gamma)) :
    LinearExtension K Gamma (fieldImage K Gamma) := by
  have hsup := gamma_linear_eq_sup K hK Gamma hG hodd hB
  have hcard := gamma_quotient_linear_card K hK Gamma hB
  have hi : (specialLayer K).relIndex Gamma = 2 * Nat.card (fieldImage K Gamma) :=
    (gamma_index_eq_quotient_card K Gamma).trans hcard
  have hcomp := gamma_internal_linear K hK Gamma hG hodd hB
  refine ⟨⟨linearLayer_le_gamma_of_full_square_image K hK Gamma hG hB,
    liftedField_le_gamma K hK Gamma hG hodd, hsup, ?_, ?_, hcomp,
    internalCoordinateSemidirect_of_complement K Gamma (linearLayer K) _ hcomp,
    hcard, hi, gamma_quotient_linear_cyclic K hK Gamma hodd hB⟩,
    gammaQuotientEquivSquareField K hK Gamma hB, fun e =>
      (gammaQuotientEquivSquareField_mk K hK Gamma hB e).2⟩
  · rw [hsup, fieldImage_linear_sup]
    exact Subgroup.map_sup (linearLayer K) (liftedField K (fieldImage K Gamma))
      (coordinateE K).subtype
  · rw [ambientImage_linearLayer]
    exact ambient_linear_factorization K hK Gamma hG hodd hB

theorem specialExtension_fieldImage (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) (A : Subgroup (K ≃+* K))
    (h : SpecialExtension K Gamma A) : fieldImage K Gamma = A := by
  exact fieldImage_eq_of_ambient_decomposition K Gamma A
    (Or.inl (by simpa only [ambientImage_specialLayer] using h.1.2.2.2.1))

theorem linearExtension_fieldImage (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) (A : Subgroup (K ≃+* K))
    (h : LinearExtension K Gamma A) : fieldImage K Gamma = A := by
  exact fieldImage_eq_of_ambient_decomposition K Gamma A
    (Or.inr (by simpa only [ambientImage_linearLayer] using h.1.2.2.2.1))

theorem specialExtension_index (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) (A : Subgroup (K ≃+* K))
    (h : SpecialExtension K Gamma A) : (specialLayer K).relIndex Gamma = Nat.card A := by
  simpa only [one_mul] using h.1.2.2.2.2.2.2.2.2.1

theorem linearExtension_index (K : Type u) [Field K] [Finite K]
    (Gamma : Subgroup (coordinateE K)) (A : Subgroup (K ≃+* K))
    (h : LinearExtension K Gamma A) : (specialLayer K).relIndex Gamma = 2 * Nat.card A :=
  h.1.2.2.2.2.2.2.2.2.1

theorem gamma_index_even_iff_linearExtension (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma))) :
    Even ((specialLayer K).relIndex Gamma) ↔ LinearExtension K Gamma (fieldImage K Gamma) := by
  constructor
  · intro he
    exact linearExtension_of_square_image K hK Gamma hG hodd
      ((gamma_index_even_iff_full_square_image K hK Gamma hodd).mp he)
  · intro h
    rw [linearExtension_index K Gamma _ h]
    exact even_two_mul _

theorem gamma_index_odd_iff_specialExtension (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hodd : Odd (Nat.card (fieldImage K Gamma))) :
    Odd ((specialLayer K).relIndex Gamma) ↔ SpecialExtension K Gamma (fieldImage K Gamma) := by
  constructor
  · intro ho
    rcases outerImage_two_cases K hK Gamma hodd with hB | hB
    · exact specialExtension_of_square_image K hK Gamma hG hodd hB
    · have he := (gamma_index_even_iff_full_square_image K hK Gamma hodd).mpr hB
      exact False.elim (Nat.not_even_iff_odd.mpr ho he)
  · intro h
    rw [specialExtension_index K Gamma _ h]
    exact hodd

theorem odd_field_extension_unique (K : Type u) [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (Gamma : Subgroup (coordinateE K))
    (hG : specialLayer K ≤ Gamma) (hdihedral : HasDihedralSylowTwo Gamma) :
    ∃! A : Subgroup (K ≃+* K), Odd (Nat.card A) ∧ Nat.card A ∣ f ∧
      (SpecialExtension K Gamma A ∨ LinearExtension K Gamma A) := by
  have hodd := field_image_odd K hK Gamma hG hdihedral
  refine ⟨fieldImage K Gamma, ⟨hodd, field_image_card_dvd K hp hcard Gamma, ?_⟩, ?_⟩
  · rcases outerImage_two_cases K hK Gamma hodd with hB | hB
    · exact Or.inl (specialExtension_of_square_image K hK Gamma hG hodd hB)
    · exact Or.inr (linearExtension_of_square_image K hK Gamma hG hodd hB)
  · intro A hA
    rcases hA.2.2 with h | h
    · exact (specialExtension_fieldImage K Gamma A h).symm
    · exact (linearExtension_fieldImage K Gamma A h).symm

theorem dihedral_projective_semilinear_overgroups_have_odd_field_part
    (K : Type u) [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f)
    (Gamma : Subgroup (coordinateE K)) (hG : specialLayer K ≤ Gamma)
    (S : Sylow 2 Gamma) {k : ℕ} (hk : 2 ≤ k)
    (e : S ≃* DihedralGroup (2 ^ (k - 1))) :
    (∃! A : Subgroup (K ≃+* K), Odd (Nat.card A) ∧ Nat.card A ∣ f ∧
      (SpecialExtension K Gamma A ∨ LinearExtension K Gamma A)) ∧
    Odd (Nat.card (fieldImage K Gamma)) ∧ Nat.card (fieldImage K Gamma) ∣ f ∧
    (SpecialExtension K Gamma (fieldImage K Gamma) ∨ LinearExtension K Gamma (fieldImage K Gamma)) ∧
    (Even ((specialLayer K).relIndex Gamma) ↔ LinearExtension K Gamma (fieldImage K Gamma)) ∧
    (Odd ((specialLayer K).relIndex Gamma) ↔ SpecialExtension K Gamma (fieldImage K Gamma)) := by
  let hK : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hodd, hf, hcard⟩
  have hdihedral := dihedralSylows_of_supplied S hk e
  have hfield := field_image_odd K hK Gamma hG hdihedral
  have hcases : SpecialExtension K Gamma (fieldImage K Gamma) ∨
      LinearExtension K Gamma (fieldImage K Gamma) := by
    rcases outerImage_two_cases K hK Gamma hfield with hB | hB
    · exact Or.inl (specialExtension_of_square_image K hK Gamma hG hfield hB)
    · exact Or.inr (linearExtension_of_square_image K hK Gamma hG hfield hB)
  exact ⟨odd_field_extension_unique K hp hcard hK Gamma hG hdihedral, hfield,
    field_image_card_dvd K hp hcard Gamma, hcases,
    gamma_index_even_iff_linearExtension K hK Gamma hG hfield,
    gamma_index_odd_iff_specialExtension K hK Gamma hG hfield⟩

theorem dihedral_projective_semilinear_overgroups_have_odd_field_part_int
    (K : Type u) [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card K = p ^ f)
    (Gamma : Subgroup (coordinateE K)) (hG : specialLayer K ≤ Gamma)
    (S : Sylow 2 Gamma) {k : ℤ} (hk : 2 ≤ k)
    (e : S ≃* DihedralGroup (2 ^ (k - 1).toNat)) :
    (∃! A : Subgroup (K ≃+* K), Odd (Nat.card A) ∧ Nat.card A ∣ f ∧
      (SpecialExtension K Gamma A ∨ LinearExtension K Gamma A)) ∧
    Odd (Nat.card (fieldImage K Gamma)) ∧ Nat.card (fieldImage K Gamma) ∣ f ∧
    (SpecialExtension K Gamma (fieldImage K Gamma) ∨ LinearExtension K Gamma (fieldImage K Gamma)) ∧
    (Even ((specialLayer K).relIndex Gamma) ↔ LinearExtension K Gamma (fieldImage K Gamma)) ∧
    (Odd ((specialLayer K).relIndex Gamma) ↔ SpecialExtension K Gamma (fieldImage K Gamma)) := by
  have hk' : 2 ≤ k.toNat := by omega
  have he : (k - 1).toNat = k.toNat - 1 := Int.toNat_sub' k 1
  rw [he] at e
  exact dihedral_projective_semilinear_overgroups_have_odd_field_part
    K hp hodd hf hcard Gamma hG S hk' e

end

end CFSG.Semidihedral.SemilinearOddExtensions
