module

public import CFSG.CharacterTheory.Wreathed.StationaryScalarCoverageSupport
public import CFSG.CharacterTheory.Wreathed.StationaryNormalizerCentralization
public import CFSG.CharacterTheory.Wreathed.OriginalScalarSylowCoverage
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamiliesLocal

public section

namespace CFSG.Wreathed.StationaryScalarCoverage

open scoped Pointwise
open CFSG.SignalizerFunctor.Helpers
open CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Wreathed.LocalizedFixedPoints
open CFSG.Wreathed.BrauerWong CFSG.Wreathed.BaseFourCentralizerStructure
open CFSG.Wreathed.StationaryNormalizerCentralization
open CFSG.Wreathed.OriginalScalarSylowCoverage

universe u

variable {G : Type u} [Group G]

theorem multiplicative_zmod_two_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h (Multiplicative.toAdd q) with h | h
  · exact Or.inl (Multiplicative.toAdd.injective (by simpa using h))
  · exact Or.inr (Multiplicative.toAdd.injective (by simpa using h))

@[expose] def twoPointMulEquiv (M : Type*) [Group M] :
    (Multiplicative (ZMod 2) → M) ≃* M × M where
  toFun f := (f 1, f (Multiplicative.ofAdd 1))
  invFun p := fun q => if q = 1 then p.1 else p.2
  left_inv f := by
    funext q
    rcases multiplicative_zmod_two_cases q with rfl | rfl
    · simp
    · have h : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
      simp [h]
  right_inv p := by
    have h : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    ext
    · simp
    · simp [h]
  map_mul' _ _ := rfl

theorem base_four_centralizer_quotient_equiv [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    Nonempty (Subgroup.centralizer (modelT n S e : Set G) ⧸
        CFSG.pPrimeCore 2 (Subgroup.centralizer (modelT n S e : Set G)) ≃*
      Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) := by
  obtain ⟨q, -⟩ := (sylow_and_base_four_group_centralizer_structure n hn S e).base_quotient
  exact ⟨((QuotientGroup.quotientMulEquivOfEq original_oddCore_eq_twoPrimeCore).symm.trans
    q.symm).trans (((modelBaseEquiv S e).symm.trans (baseFunctionEquiv (2 ^ n))).trans
      (twoPointMulEquiv _))⟩

theorem modelT_le_involutionCentralizer (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : modelT n S e ≤ involutionCentralizer n S e := by
  have := modelT_isKleinFour n (by omega) S e
  apply kleinFour_le_centralizer
  rw [CompatibleFamilies.modelT_eq_closure S e (by omega)]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem involutionCentralizer_le_normalizer_oddCore [Finite G] (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    involutionCentralizer n S e ≤ Subgroup.normalizer
      (((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Subgroup G) :
        Set G) := by
  have : (centralizerOddCore n S e).Characteristic :=
    BaseFourCentralizerStructure.oddCore_characteristic
  exact characteristic_subgroup_map_normalized _ _ (involutionCentralizer n S e).le_normalizer
    (centralizerOddCore n S e)

theorem oddCore_map_odd [Finite G] (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Odd (Nat.card ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)) := by
  rw [Subgroup.card_map_of_injective (involutionCentralizer n S e).subtype_injective]
  exact weakClosure_oddCore_card _

theorem exists_invariant_sylow_centralizerOddCore [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) {ell : ℕ} (hell : ell.Prime) :
    ∃ P : Sylow ell (centralizerOddCore n S e),
      modelT n S e ≤ Subgroup.normalizer
        ((((P : Subgroup (centralizerOddCore n S e)).map (centralizerOddCore n S e).subtype).map
          (involutionCentralizer n S e).subtype : Subgroup G) : Set G) := by
  have := modelT_isKleinFour n (by omega) S e
  have hT2 : IsPGroup 2 (modelT n S e) :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨Q, hQ⟩ := normalized_subgroup_invariant_sylow 2 ell Nat.prime_two hell
    (modelT n S e) _ hT2 ((modelT_le_involutionCentralizer n hn S e).trans
      (involutionCentralizer_le_normalizer_oddCore n S e))
    (oddCore_map_odd n S e).coprime_two_left
  obtain ⟨P, hP⟩ := intrinsic_sylow_from_ambient hell (involutionCentralizer n S e)
    (centralizerOddCore n S e) Q
  refine ⟨P, ?_⟩
  rw [hP]
  exact hQ

theorem scalar_of_stationary_factorizations [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) {ell : ℕ} (hell : ell.Prime) (hellodd : Odd ell)
    (P : Subgroup G)
    (hPR : P ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    (hPp : IsPGroup ell P) (hTP : modelT n S e ≤ Subgroup.normalizer (P : Set G))
    (hstP : ∃ Q : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer (P : Set G))),
      ((Q : Subgroup _).map (CFSG.pPrimeCore 2
        (Subgroup.normalizer (P : Set G))).subtype).map
          (Subgroup.normalizer (P : Set G)).subtype = P)
    (hfactor : ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup ell U →
      U ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
      modelT n S e ≤ Subgroup.normalizer (U : Set G) →
        (((CFSG.pPrimeCore 2 (Subgroup.normalizer (U : Set G))).map
          (Subgroup.normalizer (U : Set G)).subtype : Subgroup G) : Set G) *
          ((Subgroup.normalizer (U : Set G) ⊓
            Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) :
              Subgroup G) : Set G) = (Subgroup.normalizer (U : Set G) : Set G)) :
    (∀ a ∈ P, wreathModelHom S e (Original.x2 (2 ^ n)) * a *
        (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = a) ∨
      ∀ a ∈ P, wreathModelHom S e (Original.x2 (2 ^ n)) * a *
        (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = a⁻¹ := by
  have : Fact ell.Prime := ⟨hell⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x := wreathModelHom S e (Original.x (2 ^ n)) with hxdef
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hydef
  set y' := wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) with hy'def
  set T := modelT n S e with hTdef
  set N := involutionCentralizer n S e with hNdef
  set Ra := (centralizerOddCore n S e).map N.subtype with hRadef
  have : IsKleinFour T := modelT_isKleinFour n (by omega) S e
  have hTeq : T = Subgroup.closure {x, y} := CompatibleFamilies.modelT_eq_closure S e (by omega)
  have hxT : x ∈ T := by
    rw [hTeq]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hyT : y ∈ T := by
    rw [hTeq]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx2 : orderOf x = 2 := CompatibleFamilies.orderOf_x S e hn
  have hy2 : orderOf y = 2 := CompatibleFamilies.orderOf_x2 S e hn
  have hxy : x ≠ y := modelHom_x_ne_x2 S e (by omega)
  have hx1 : x ≠ 1 := CompatibleFamilies.ne_one_of_orderOf hx2
  have hy1 : y ≠ 1 := CompatibleFamilies.ne_one_of_orderOf hy2
  have hxyy' : x * y = y' := modelHom_x_mul_x2 S e (by omega)
  have hxy' : x ≠ y' := modelHom_x_ne_t_half S e (by omega)
  have hyy' : y ≠ y' := modelHom_x2_ne_t_half S e (by omega)
  have hT2 : IsPGroup 2 T :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hTN : T ≤ N := modelT_le_involutionCentralizer n hn S e
  have hNRa : N ≤ Subgroup.normalizer (Ra : Set G) :=
    involutionCentralizer_le_normalizer_oddCore n S e
  have hRaN : Ra ≤ N := Subgroup.map_subtype_le _
  have hRanormal : (Ra.subgroupOf N).Normal := by
    rw [show Ra.subgroupOf N = centralizerOddCore n S e from
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _]
    infer_instance
  have hRaodd : Odd (Nat.card Ra) := oddCore_map_odd n S e
  have hPx : P ≤ Subgroup.centralizer ({x} : Set G) := hPR.trans hRaN
  set C := Subgroup.centralizer (T : Set G) with hCdef
  set D := (CFSG.pPrimeCore 2 C).map C.subtype with hDdef
  have hCq := (sylow_and_base_four_group_centralizer_structure n hn S e).base_quotient_isPGroup
  have hCD := base_four_centralizer_quotient_equiv n hn S e
  have hDC : D ≤ C := Subgroup.map_subtype_le _
  have hDodd : Odd (Nat.card D) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hoddD : ∀ c ∈ C, Odd (orderOf c) → c ∈ D := by
    intro c hc hodd
    have hW : Odd (Nat.card (Subgroup.zpowers (⟨c, hc⟩ : C))) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk]
      exact hodd
    have hle := odd_subgroup_le_normal_of_two_quotient _ (CFSG.oddCore C) hW hCq
    have hmem : (⟨c, hc⟩ : C) ∈ CFSG.pPrimeCore 2 C := by
      rw [← original_oddCore_eq_twoPrimeCore]
      exact hle (Subgroup.mem_zpowers _)
    exact ⟨⟨c, hc⟩, hmem, rfl⟩
  have hCN : C ≤ N := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxT)
  have hDN : D ≤ N := hDC.trans hCN
  have hTC : T ≤ C :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr IsKleinFour.isMulCommutative
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := hTC.trans (le_normalizer_map_pPrimeCore C)
  have hTcD : T ≤ Subgroup.centralizer (D : Set G) := Subgroup.le_centralizer_iff.mp hDC
  have hloc := (stationary_normalizer_factorizations_force_local_prime_centralization T x y
    hxT hyT hx2 hy2 hxy hell hellodd P hPp hTP hPx hstP
    (fun U hU1 hUP hTU => hfactor U hU1 (hPp.to_le hUP) (hUP.trans hPR) hTU)).2
  set RD := Ra ⊔ D with hRDdef
  have hRDodd : Odd (Nat.card RD) :=
    odd_card_sup_in_parent N Ra D hRaN hDN hRanormal hRaodd hDodd
  have hTRD : T ≤ Subgroup.normalizer (RD : Set G) :=
    (le_inf (hTN.trans hNRa) hTD).trans (Subgroup.inf_normalizer_le_normalizer_sup Ra D)
  let PD0s : Sylow ell D := default
  have hTPD0 : T ≤ Subgroup.normalizer
      (((PD0s : Subgroup D).map D.subtype : Subgroup G) : Set G) :=
    (hTcD.trans (Subgroup.centralizer_le (Subgroup.map_subtype_le _))).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨Q0s, hPDQ0, hTQ0⟩ := exists_invariant_sylow_containing hell T RD
    ((PD0s : Subgroup D).map D.subtype) hT2 hRDodd hTRD
    ((Subgroup.map_subtype_le _).trans le_sup_right) (PD0s.isPGroup'.map _) hTPD0
  obtain ⟨c, hc, hPQ⟩ := invariant_pgroup_le_fixed_conjugate_sylow hell T RD P hT2 hTRD
    hRDodd Q0s hTQ0 (hPR.trans le_sup_left) hPp hTP
  have hcD : c ∈ D :=
    hoddD c hc.2 (hRDodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard RD hc.1))
  let PDs : Sylow ell D := (⟨c, hcD⟩ : D) • PD0s
  set PD := (PDs : Subgroup D).map D.subtype with hPDdef
  set Q := ((Q0s : Subgroup RD).map RD.subtype).map (MulAut.conj c).toMonoidHom with hQdef
  have hPDeq : PD = ((PD0s : Subgroup D).map D.subtype).map (MulAut.conj c).toMonoidHom :=
    map_subtype_smul_sylow D PD0s ⟨c, hcD⟩
  have hQp : IsPGroup ell Q := (Q0s.isPGroup'.map _).map _
  have hPDQ : PD ≤ Q := by
    rw [hPDeq]
    exact Subgroup.map_mono hPDQ0
  have hcT : ∀ v ∈ T, (MulAut.conj c) v = v := by
    intro v hv
    change c * v * c⁻¹ = v
    rw [← Subgroup.mem_centralizer_iff.mp hc.2 v hv, mul_inv_cancel_right]
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    normalized_map_of_fixed (MulAut.conj c) T _ hcT hTQ0
  have hQRD : Q ≤ RD := by
    rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hc.1) z).mp
      (Subgroup.map_subtype_le _ hz)
  have hQx : Q ≤ Subgroup.centralizer ({x} : Set G) := hQRD.trans (sup_le hRaN hDN)
  have hQD : Q ⊓ D ≤ PD := by
    have hX : IsPGroup ell (Q.subgroupOf D) := hQp.comap_subtype
    have hle : (PDs : Subgroup D) ≤ Q.subgroupOf D := fun z hz => hPDQ ⟨z, hz, rfl⟩
    have heq := PDs.is_maximal' hX hle
    rintro z ⟨hzQ, hzD⟩
    have hz : (⟨z, hzD⟩ : D) ∈ (PDs : Subgroup D) := by
      rw [← heq]
      exact hzQ
    exact ⟨⟨z, hzD⟩, hz, rfl⟩
  set F := P ⊓ Subgroup.centralizer ({y} : Set G) with hFdef
  have hPodd := odd_card_of_pgroup hell hellodd P hPp
  have hFPD : F ≤ PD := by
    rintro f ⟨hfP, hfy⟩
    exact hQD ⟨hPQ hfP, hoddD f (mem_centralizer_of_pair T hxT hyT hx1 hy1 hxy (hPx hfP) hfy)
      (hPodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard P hfP))⟩
  by_cases hFP : F = P
  · left
    intro a ha
    have haF : a ∈ F := by
      rw [hFP]
      exact ha
    exact (conj_fixed_iff y a).mpr haF.2
  by_cases hF1 : F = ⊥
  · right
    exact inverted_of_trivial_fixed_subgroup y hy2 P hPodd (hTP hyT) hF1
  exfalso
  have hQPD : ¬ Q ≤ PD := by
    intro hle
    apply hFP
    apply le_antisymm inf_le_left
    intro a ha
    refine ⟨ha, ?_⟩
    have haC : a ∈ C := hDC (Subgroup.map_subtype_le _ (hle (hPQ ha)))
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp haC y hyT).symm
  obtain ⟨Y, hYB, hY1, hY2, hY3⟩ := exists_base_three_cycle hn S e
    (simple_wreathed_one_involution_class_and_local_S3 hnonab n hn S e).1
  have hY1' : Y⁻¹ * x * Y = y := hY1
  have hY2' : Y⁻¹ * y * Y = y' := hY2
  have hY3' : Y⁻¹ * y' * Y = x := hY3
  have hYT : Y ∈ Subgroup.normalizer (T : Set G) :=
    modelBase_normalizer_le_modelT_normalizer n (by omega) S e hYB
  have hYD : Y ∈ Subgroup.normalizer (D : Set G) :=
    CFSG.Semidihedral.Local.mem_normalizer_map_pPrimeCore 2
      (normalizer_le_normalizer_centralizer T hYT)
  obtain ⟨d, hdD, hdH⟩ := exists_mul_mem_normalizer_sylow PDs hYD
  have hdT : ∀ v ∈ T, d * v * d⁻¹ = v := by
    intro v hv
    rw [← Subgroup.mem_centralizer_iff.mp (hDC hdD) v hv, mul_inv_cancel_right]
  have hgT : d * Y ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ (hDC hdD)) hYT
  have hconj : ∀ v ∈ T, d * Y * v * (d * Y)⁻¹ = Y * v * Y⁻¹ := by
    intro v hv
    have hu : Y * v * Y⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hYT v).mp hv
    rw [show d * Y * v * (d * Y)⁻¹ = d * (Y * v * Y⁻¹) * d⁻¹ by group, hdT _ hu]
  have hYx : Y * x * Y⁻¹ = y' := by
    rw [← hY3']
    group
  have hYy : Y * y * Y⁻¹ = x := by
    rw [← hY1']
    group
  have hYy' : Y * y' * Y⁻¹ = y := by
    rw [← hY2']
    group
  have hg : ∀ v ∈ T, v ≠ 1 → d * Y * v * (d * Y)⁻¹ ≠ v := by
    intro v hv hv1
    rw [hconj v hv]
    rcases CFSG.Semidihedral.Local.kleinFour_mem_cases T hxT hyT hx1 hy1 hxy hv with
      rfl | rfl | rfl | rfl
    · rw [hxyy', hYy']
      exact hyy'
    · rw [hYx]
      exact hxy'.symm
    · rw [hYy]
      exact hxy
    · exact absurd rfl hv1
  have hgy : d * Y * y * (d * Y)⁻¹ = x := by rw [hconj y hyT, hYy]
  have hTF : T ≤ Subgroup.normalizer (F : Set G) :=
    (le_inf hTP ((kleinFour_le_centralizer T hyT).trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact false_of_intermediate_fixed_subgroup hell hellodd T hxT hyT hx2 hy2 hxy n n
    (by omega) (by omega) hCD hDC hoddD PDs hQp hPDQ hTQ hQx hQD hQPD hFPD
    (inf_le_left.trans hPx) hdH hgT hg hgy
    (hfactor F hF1 (hPp.to_le inf_le_left) (inf_le_left.trans hPR) hTF)
    (fun W hWK hWp hxW => hloc F hF1 inf_le_left hTF W hWK hWp hxW)

end CFSG.Wreathed.StationaryScalarCoverage
