module

public import CFSG.CharacterTheory.Wreathed.ComponentCoverConfinementSetup
public import CFSG.CharacterTheory.Wreathed.StationaryInvertedSylow

public section

open scoped Classical Pointwise

namespace CFSG.Wreathed.ComponentCoverConfinement

open CFSG.Assembly.LowTwoRank SmallerRecognitionOriginalField
open OriginalStationarityCoverageCriterion ComponentCoverFactorizations
open CFSG.Wreathed.OriginalSylowNormalizerWitness CFSG.SignalizerFunctor.Helpers

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem inverted_prime_order_confined
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) (hst : OriginalAllPrimeStationarity n S e)
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal] [Group.IsPerfect J]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hcomm : ∀ j ∈ J, ∀ r ∈ centralizerOddCore n S e, Commute j r)
    (B : Subgroup G)
    (hBR : B ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    (hBinv : ∀ b ∈ B, wreathModelHom S e (Original.x2 (2 ^ n)) * b *
      (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = b⁻¹)
    (hBE : ∀ E : Subgroup G, E ≤ involutionCentralizer n S e → Odd (Nat.card E) →
      (∀ z ∈ E, wreathModelHom S e (Original.x2 (2 ^ n)) * z *
        (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = z⁻¹) →
      ∀ b ∈ B, ∀ z ∈ E, b * z = z * b)
    (u : G) (huB : u ∈ B) (hu : (orderOf u).Prime) :
    Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ involutionCentralizer n S e := by
  set x := wreathModelHom S e (Original.x (2 ^ n)) with hxdef
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hydef
  set T := Subgroup.closure ({x, y} : Set G) with hTdef
  have hTeq : BaseFourCentralizerStructure.modelT n S e = T :=
    CompatibleFamilies.modelT_eq_closure S e (by omega)
  have : IsKleinFour T := hTeq ▸ BaseFourCentralizerStructure.modelT_isKleinFour n (by omega) S e
  have hxT : x ∈ T := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyT : y ∈ T := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx2 : orderOf x = 2 := CompatibleFamilies.orderOf_x S e hn
  have hy2 : orderOf y = 2 := CompatibleFamilies.orderOf_x2 S e hn
  have hxy : x ≠ y := BrauerWong.modelHom_x_ne_x2 S e (by omega)
  have hx1 : x ≠ 1 := CompatibleFamilies.ne_one_of_orderOf hx2
  have hy1 : y ≠ 1 := CompatibleFamilies.ne_one_of_orderOf hy2
  have huR : u ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype := hBR huB
  have huN : u ∈ involutionCentralizer n S e := Subgroup.map_subtype_le _ huR
  have hxu : x * u = u * x := (Subgroup.mem_centralizer_singleton_iff.mp huN).symm
  have hyu : y * u * y⁻¹ = u⁻¹ := hBinv u huB
  have hRodd := StationaryScalarCoverage.oddCore_map_odd n S e
  have huodd : Odd (orderOf u) := hRodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ huR)
  have hu1 : u ≠ 1 := fun h => by
    rw [h, orderOf_one] at hu
    exact Nat.not_prime_one hu
  have hTu : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    rw [hTdef, Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | ht
    · exact mem_normalizer_zpowers_of_conj (Or.inl (by rw [hxu, mul_inv_cancel_right]))
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact mem_normalizer_zpowers_of_conj (Or.inr hyu)
  have hU : Subgroup.zpowers u ≠ ⊥ := fun h =>
    hu1 (Subgroup.zpowers_eq_bot.mp h)
  have hUR : Subgroup.zpowers u ≤ (centralizerOddCore n S e).map
      (involutionCentralizer n S e).subtype := Subgroup.zpowers_le.mpr huR
  have hfacR : ∀ U : Subgroup G, U ≠ ⊥ →
      U ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
        NormalizerFactorization n S e U := fun U hU' hUR' =>
    normalizerFactorization_of_lift hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec J hJM
      hcomm U hUR' hU'
  have hNF := hfacR _ hU hUR
  set H0 := Subgroup.normalizer (Subgroup.zpowers u : Set G) with hH0
  have hJ0 : J.map (involutionCentralizer n S e).subtype ≤ H0 := by
    rintro _ ⟨j, hj, rfl⟩
    apply ConfinedOddCore.centralizer_singleton_le_normalizer_zpowers
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨r', hr', hr'eq⟩ := huR
    rw [← hr'eq]
    exact congrArg Subtype.val (hcomm j hj r' hr').eq
  have hfactor := factorization_sup n S e _ hNF
  have hstI := fun ell (hell : ell.Prime) hdiv =>
    stationary_intrinsic n S e hst (ell := ell) hell hdiv
  have hfacT : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
      ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup ell U →
        U ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
        T ≤ Subgroup.normalizer (U : Set G) →
          (((CFSG.pPrimeCore 2 (Subgroup.normalizer (U : Set G))).map
            (Subgroup.normalizer (U : Set G)).subtype : Subgroup G) : Set G) *
            ((Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :
              Subgroup G) : Set G) = (Subgroup.normalizer (U : Set G) : Set G) :=
    fun _ _ _ U hU' _ hUR' _ => factorization_set n S e U (hfacR U hU' hUR')
  by_contra hH0N
  have hact :=
    StationaryInvertedSylow.stationary_factorizations_produce_actual_inverted_sylow_and_cyclic_actor
      hnonab n hn S e (not_sym4_center n hn S e hfour) J hJM hcomm H0 hJ0 hfactor hH0N
  obtain ⟨-, ⟨ell, hell, hdivO, W, hTW, hWN⟩, hall⟩ := hact hTu hstI hfacT
  obtain ⟨⟨-, hWinv⟩, -, -, ⟨hE1, -⟩, -, -, -, -, -, -, -, -, -, hKinv⟩ :=
    hall ell hell W hTW hWN
  set WG := ((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype).map H0.subtype
    with hWG
  set E := WG ⊓ Subgroup.centralizer ({y} : Set G) with hEdef
  set K := Subgroup.centralizer (E : Set G) with hKdef
  set D := (CFSG.oddCore K).map K.subtype with hDdef
  have hWodd : Odd (Nat.card WG) := by
    have hO : Odd (Nat.card ((CFSG.oddCore H0).map H0.subtype)) := by
      rw [Subgroup.card_map_of_injective H0.subtype_injective]
      exact weakClosure_oddCore_card H0
    exact hO.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.map_mono (Subgroup.map_subtype_le _)))
  have hWH0 : WG ≤ H0 := Subgroup.map_subtype_le _
  have hWu : ∀ w ∈ WG, w * u = u * w := fun w hw =>
    commute_of_inverted_mem_normalizer (hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard WG hw))
      (hWinv w hw) (hWH0 hw) hxu
  have huK : u ∈ K := Subgroup.mem_centralizer_iff.mpr fun z hz => hWu z hz.1
  have huD : u ∈ D := hKinv u huK huodd hyu
  obtain ⟨g, hgT, hgx, hgy, hgxy⟩ := exists_cycler hnonab n hn S e
  replace hgT : g ∈ Subgroup.normalizer (T : Set G) := hgT
  replace hgx : g * x * g⁻¹ = y := hgx
  replace hgy : g * y * g⁻¹ = x * y := hgy
  replace hgxy : g * (x * y) * g⁻¹ = x := hgxy
  set uy := g * u * g⁻¹ with huydef
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'def
  have hxg : x = g⁻¹ * y * g := by rw [← hgx]; group
  have hyg : y = g⁻¹ * (x * y) * g := by rw [← hgy]; group
  have hE'N : E' ≤ involutionCentralizer n S e := by
    rintro _ ⟨z, hz, rfl⟩
    rw [ConfinedOddCore.mem_involutionCentralizer_iff]
    have hzy : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp hz.2
    change g⁻¹ * z * g⁻¹⁻¹ * x = x * (g⁻¹ * z * g⁻¹⁻¹)
    rw [hxg]
    calc g⁻¹ * z * g⁻¹⁻¹ * (g⁻¹ * y * g) = g⁻¹ * (z * y) * g := by group
      _ = g⁻¹ * (y * z) * g := by rw [hzy]
      _ = g⁻¹ * y * g * (g⁻¹ * z * g⁻¹⁻¹) := by group
  have hE'odd : Odd (Nat.card E') := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hWodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hE'inv : ∀ z ∈ E', y * z * y⁻¹ = z⁻¹ := by
    rintro _ ⟨z, hz, rfl⟩
    have hzy : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp hz.2
    have hxz : x * z * x⁻¹ = z⁻¹ := hWinv z hz.1
    have hxyz : (x * y) * z * (x * y)⁻¹ = z⁻¹ := by
      calc (x * y) * z * (x * y)⁻¹ = x * (z * y) * y⁻¹ * x⁻¹ := by rw [hzy]; group
        _ = z⁻¹ := by rw [show x * (z * y) * y⁻¹ * x⁻¹ = x * z * x⁻¹ by group, hxz]
    change y * (g⁻¹ * z * g⁻¹⁻¹) * y⁻¹ = (g⁻¹ * z * g⁻¹⁻¹)⁻¹
    rw [hyg]
    calc g⁻¹ * (x * y) * g * (g⁻¹ * z * g⁻¹⁻¹) * (g⁻¹ * (x * y) * g)⁻¹ =
        g⁻¹ * ((x * y) * z * (x * y)⁻¹) * g := by group
      _ = (g⁻¹ * z * g⁻¹⁻¹)⁻¹ := by rw [hxyz]; group
  have huE' := hBE E' hE'N hE'odd hE'inv u huB
  have huyK : uy ∈ K := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have h1 := huE' (g⁻¹ * z * g⁻¹⁻¹) ⟨z, hz, rfl⟩
    calc z * uy = g * (g⁻¹ * z * g⁻¹⁻¹ * u) * g⁻¹ := by rw [huydef]; group
      _ = g * (u * (g⁻¹ * z * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = uy * z := by rw [huydef]; group
  have hxg' : x = g * (x * y) * g⁻¹ := hgxy.symm
  have hxuy : x * uy * x⁻¹ = uy⁻¹ := by
    have hxyu : (x * y) * u * (x * y)⁻¹ = u⁻¹ := by
      calc (x * y) * u * (x * y)⁻¹ = x * (y * u * y⁻¹) * x⁻¹ := by group
        _ = u⁻¹ := by
          rw [hyu, show x * u⁻¹ * x⁻¹ = (x * u * x⁻¹)⁻¹ by group, hxu, mul_inv_cancel_right]
    rw [huydef]
    nth_rewrite 1 [hxg']
    nth_rewrite 2 [hxg']
    calc g * (x * y) * g⁻¹ * (g * u * g⁻¹) * (g * (x * y) * g⁻¹)⁻¹ =
        g * ((x * y) * u * (x * y)⁻¹) * g⁻¹ := by group
      _ = (g * u * g⁻¹)⁻¹ := by rw [hxyu]; group
  have hTg : T.map (MulAut.conj g).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgT
  have hTuy : T ≤ Subgroup.normalizer (Subgroup.zpowers uy : Set G) := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hTu
    rw [hTg, Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers] at h1
    exact h1
  have huyord : orderOf uy = orderOf u := by
    rw [huydef, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hTE : T ≤ Subgroup.normalizer (E : Set G) :=
    (le_inf hTW ((LocalizedFixedPoints.kleinFour_le_centralizer T hyT).trans
      Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    hTE.trans (BrauerWong.normalizer_le_normalizer_centralizer E)
  have : (CFSG.oddCore K).Characteristic := BaseFourCentralizerStructure.oddCore_characteristic
  have hTD : T ≤ Subgroup.normalizer (D : Set G) :=
    characteristic_subgroup_map_normalized T K hTK (CFSG.oddCore K)
  have hDK : D ≤ K := Subgroup.map_subtype_le _
  have hDn : (D.subgroupOf K).Normal := by
    rw [hDdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    infer_instance
  have hDodd : Odd (Nat.card D) := by
    rw [hDdef, Subgroup.card_map_of_injective K.subtype_injective]
    exact weakClosure_oddCore_card K
  have huyodd : Odd (Nat.card (Subgroup.zpowers uy)) := by
    rw [Nat.card_zpowers, huyord]
    exact huodd
  set X := D ⊔ Subgroup.zpowers uy with hXdef
  have hXodd : Odd (Nat.card X) :=
    CFSG.Semidihedral.StationaryOddLocalization.odd_card_sup_in_parent K D
      (Subgroup.zpowers uy) hDK (Subgroup.zpowers_le.mpr huyK) hDn hDodd huyodd
  have hTX : T ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf hTD hTuy).trans (Subgroup.inf_normalizer_le_normalizer_sup D (Subgroup.zpowers uy))
  obtain ⟨v, hv1, hvp, hxv, hvu⟩ := exists_inverted_centralizing_witness T hxT hyT hx1 hy1 hxy
    hu X hXodd hTX (le_sup_left (b := Subgroup.zpowers uy) huD) rfl hxu hTu
    (le_sup_right (a := D) (Subgroup.mem_zpowers uy)) huyord hxuy hTuy
  have hloc := StationaryInvertedSylow.localization_of_stationary_factorizations n hn S e hstI
    (fun ell hell hdiv U hU' hUp hUR' hTU => hfacT ell hell hdiv U hU' hUp hUR' (hTeq ▸ hTU))
  have hrdiv : orderOf u ∣ Nat.card ((centralizerOddCore n S e).map
      (involutionCentralizer n S e).subtype) := Subgroup.orderOf_dvd_natCard _ huR
  have hup : IsPGroup (orderOf u) (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one])
  have hvN : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    apply Subgroup.zpowers_le.mpr
    apply ConfinedOddCore.centralizer_singleton_le_normalizer_zpowers
    exact Subgroup.mem_centralizer_singleton_iff.mpr hvu
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G) :=
    mem_normalizer_zpowers_of_conj (Or.inr hxv)
  have hvx := hloc (orderOf u) hu hrdiv (Subgroup.zpowers u) hU hUR hup (hTeq ▸ hTu)
    (Subgroup.zpowers v) hvN hvp hxN (Subgroup.mem_zpowers v)
  have hvx' : x * v * x⁻¹ = v := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hvx
    rw [← h, mul_inv_cancel_right]
  have hvodd : Odd (orderOf v) := by
    obtain ⟨k, hk⟩ := hvp ⟨v, Subgroup.mem_zpowers v⟩
    have hdvd : orderOf v ∣ orderOf u ^ k :=
      orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    exact huodd.pow.of_dvd_nat hdvd
  exact hv1 (eq_one_of_eq_inv_of_odd hvodd (hvx'.symm.trans hxv))

end CFSG.Wreathed.ComponentCoverConfinement

namespace CFSG.Wreathed.ComponentCoverConfinement

open CFSG.Assembly.LowTwoRank SmallerRecognitionOriginalField
open OriginalStationarityCoverageCriterion ComponentCoverFactorizations

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [Finite G] [IsSimpleGroup G] in
theorem inverted_factor_ambient (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (J B : Subgroup (involutionCentralizer n S e))
    (hBset : (B : Set (involutionCentralizer n S e)) = {r | r ∈ centralizerOddCore n S e ∧
      wreathModelHom S e (Original.x2 (2 ^ n)) * (r : G) *
        (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = (r : G)⁻¹})
    (hBE : ∀ E : Subgroup (involutionCentralizer n S e), Odd (Nat.card E) →
      (∀ z ∈ E, wreathModelHom S e (Original.x2 (2 ^ n)) * (z : G) *
        (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = (z : G)⁻¹) →
      E ≤ J ⊔ B ∧ B ≤ Subgroup.centralizer (E : Set (involutionCentralizer n S e))) :
    (B.map (involutionCentralizer n S e).subtype ≤
        (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) ∧
      (∀ b ∈ B.map (involutionCentralizer n S e).subtype,
        wreathModelHom S e (Original.x2 (2 ^ n)) * b *
          (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = b⁻¹) ∧
      ∀ E : Subgroup G, E ≤ involutionCentralizer n S e → Odd (Nat.card E) →
        (∀ z ∈ E, wreathModelHom S e (Original.x2 (2 ^ n)) * z *
          (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = z⁻¹) →
        ∀ b ∈ B.map (involutionCentralizer n S e).subtype, ∀ z ∈ E, b * z = z * b := by
  have hmem : ∀ b ∈ B, b ∈ centralizerOddCore n S e ∧
      wreathModelHom S e (Original.x2 (2 ^ n)) * (b : G) *
        (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = (b : G)⁻¹ := fun b hb => by
    have h : b ∈ (B : Set (involutionCentralizer n S e)) := hb
    rw [hBset] at h
    exact h
  refine ⟨Subgroup.map_mono fun b hb => (hmem b hb).1, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact (hmem b hb).2
  · rintro E hEN hEodd hEinv _ ⟨b, hb, rfl⟩ z hz
    have hodd : Odd (Nat.card (E.subgroupOf (involutionCentralizer n S e))) := by
      rw [CFSG.natCard_subgroupOf_eq _ _ hEN]
      exact hEodd
    have hC := (hBE _ hodd fun w hw => hEinv w hw).2 hb
    have h := Subgroup.mem_centralizer_iff.mp hC ⟨z, hEN hz⟩ hz
    exact (congrArg Subtype.val h).symm

theorem stationarity_and_original_coverage_confine_inverted_odd_core_elements
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e) :
    ∃ B : Subgroup (involutionCentralizer n S e),
      (B : Set (involutionCentralizer n S e)) = {r | r ∈ centralizerOddCore n S e ∧
        wreathModelHom S e (Original.x2 (2 ^ n)) * (r : G) *
          (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = (r : G)⁻¹} ∧
      B ≤ centralizerOddCore n S e ∧ IsMulCommutative B ∧
      (B.subgroupOf (centralizerOddCore n S e)).Characteristic ∧
      Nat.Coprime (Nat.card B) (B.relIndex (centralizerOddCore n S e)) ∧
      (B.subgroupOf (centralizerOddCore n S e)).Normal ∧
      B ⊔ (centralizerOddCore n S e ⊓ (Subgroup.centralizer
        ({wreathModelHom S e (Original.x2 (2 ^ n))} : Set G)).subgroupOf
          (involutionCentralizer n S e)) = centralizerOddCore n S e ∧
      B ⊓ (centralizerOddCore n S e ⊓ (Subgroup.centralizer
        ({wreathModelHom S e (Original.x2 (2 ^ n))} : Set G)).subgroupOf
          (involutionCentralizer n S e)) = ⊥ ∧
      ∀ u ∈ B, u ≠ 1 →
        Subgroup.normalizer (Subgroup.zpowers (u : G) : Set G) ≤ involutionCentralizer n S e ∧
          Subgroup.centralizer ({(u : G)} : Set G) ≤ involutionCentralizer n S e := by
  obtain ⟨J, hJn, hJperf, hJM, hcomm, hidx⟩ :=
    canonical_lift hnonab n hn S e hfour p f hp hpodd hf hlocal hcov
  have hfac := normalizerFactorization_of_lift hnonab n hn S e hfour p f hp hpodd hf hq hlocal
    hrec J hJM hcomm
  obtain ⟨B, hBset, hBR, hBab, hBchar, hBhall, hBn, hBsup, hBinf, -, hBE⟩ :=
    inverted_factor hnonab n hn S e hfour hst (fun U hU hUR => hfac U hUR hU) J hcomm hidx
  obtain ⟨hBR', hBinv', hBE'⟩ := inverted_factor_ambient n S e J B hBset hBE
  refine ⟨B, hBset, hBR, hBab, hBchar, hBhall, hBn, hBsup, hBinf, fun u hu hu1 => ?_⟩
  exact confined_of_prime_order (involutionCentralizer n S e)
    (B.map (involutionCentralizer n S e).subtype)
    (fun v hv hvp => inverted_prime_order_confined hnonab n hn S e hfour p f hp hpodd hf hq
      hlocal hrec hst J hJM hcomm _ hBR' hBinv' hBE' v hv hvp)
    (Subgroup.mem_map_of_mem _ hu) (fun h => hu1 (Subtype.ext h))

end CFSG.Wreathed.ComponentCoverConfinement
