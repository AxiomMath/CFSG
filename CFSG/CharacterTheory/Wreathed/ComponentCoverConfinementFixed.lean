module

public import CFSG.CharacterTheory.Wreathed.ComponentCoverConfinementInverted
public import CFSG.CharacterTheory.Wreathed.ComponentCoverConfinementDimension
public import CFSG.CharacterTheory.Wreathed.ReducedCentralizerSylowCentralizer

public section

open scoped Classical Pointwise

namespace CFSG.Wreathed.ComponentCoverConfinement

open CFSG.Assembly.LowTwoRank SmallerRecognitionOriginalField
open OriginalStationarityCoverageCriterion ComponentCoverFactorizations
open CFSG.Semidihedral CFSG.Semidihedral.ExchangedEigensubgroups
open CFSG.Wreathed.ReducedCentralizerSylow CFSG.Semidihedral.Principal.PrimewiseScalar

section Elements

variable {G : Type} [Group G]

theorem orderOf_ne_of_normal_inverted_sylow {x u : G} (H0 : Subgroup G)
    (hH0 : H0 ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G))
    (huO : u ∈ (CFSG.oddCore H0).map H0.subtype) {ell : ℕ} (hell : ell.Prime)
    (W : Sylow ell (CFSG.oddCore H0))
    (hWinv : ∀ w ∈ ((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype).map
      H0.subtype, x * w * x⁻¹ = w⁻¹)
    (hxu : x * u = u * x) (huodd : Odd (orderOf u)) (hu1 : u ≠ 1) : orderOf u ≠ ell := by
  intro hul
  have : Fact ell.Prime := ⟨hell⟩
  let φ : CFSG.oddCore H0 →* G := H0.subtype.comp (CFSG.oddCore H0).subtype
  have hφ : Function.Injective φ :=
    H0.subtype_injective.comp (CFSG.oddCore H0).subtype_injective
  let U' : Subgroup (CFSG.oddCore H0) := (Subgroup.zpowers u).comap φ
  have hU'n : U'.Normal := ⟨fun a ha o => by
    change φ (o * a * o⁻¹) ∈ Subgroup.zpowers u
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hH0 (o : H0).2) (φ a)).mp ha⟩
  have hU'p : IsPGroup ell U' := by
    intro a
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    apply hφ
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    change φ ((a : CFSG.oddCore H0) ^ ell) = φ 1
    rw [map_pow, map_one, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      ← hul, pow_orderOf_eq_one, one_zpow]
  have hle := hU'p.le_sylow_of_normal W
  obtain ⟨o, ho, hou⟩ := huO
  have ha : (⟨o, ho⟩ : CFSG.oddCore H0) ∈ U' := by
    change (o : G) ∈ Subgroup.zpowers u
    rw [show (o : G) = u from hou]
    exact Subgroup.mem_zpowers u
  have huW : u ∈ ((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype).map
      H0.subtype := ⟨o, ⟨⟨o, ho⟩, hle ha, rfl⟩, hou⟩
  have h1 := hWinv u huW
  rw [hxu, mul_inv_cancel_right] at h1
  exact hu1 (eq_one_of_eq_inv_of_odd huodd h1)

theorem factorization_layer_card {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    (p ^ f * ((p ^ f) ^ 2 - 1)).factorization p = f := by
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have hq2 : 1 < (p ^ f) ^ 2 := Nat.one_lt_pow (by norm_num) hq1
  have hne : (p ^ f) ^ 2 - 1 ≠ 0 := by omega
  have hndvd : ¬ p ∣ (p ^ f) ^ 2 - 1 := by
    intro h
    have h1 : p ∣ (p ^ f) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
    have h2 := Nat.dvd_sub h1 h
    rw [show (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) = 1 by omega] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  rw [Nat.factorization_mul (pow_ne_zero f hp.ne_zero) hne, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]

theorem normalizer_zpowers_le_of_conj {K : Subgroup G} {c u : G} (hc : c ∈ K)
    (h : Subgroup.normalizer (Subgroup.zpowers (c * u * c⁻¹) : Set G) ≤ K) :
    Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ K := by
  intro g hg
  have h1 : c * g * c⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers (c * u * c⁻¹) : Set G) := by
    have := Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hg
    rw [Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers] at this
    exact this
  have h2 := h h1
  have : g = c⁻¹ * (c * g * c⁻¹) * c := by group
  rw [this]
  exact K.mul_mem (K.mul_mem (K.inv_mem hc) h2) hc

end Elements

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem eq_one_of_commute_defining_sylow
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (P : Subgroup (centralizerOddCoreQuotient n S e))
    (hPM : P ≤ CFSG.layer (centralizerOddCoreQuotient n S e)) (hPcard : Nat.card P = p ^ f)
    (h : centralizerOddCoreQuotient n S e) (hh : ∀ z ∈ P, z * h = h * z)
    {r : ℕ} (hr : r.Prime) (hrodd : Odd r) (hhr : orderOf h ∣ r) (hrp : r ≠ p) : h = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h2 => by
    rw [h2] at hpodd
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  obtain ⟨F, hFf, hFfin, hcard, -, -, theta, rho, eta, hin, -, -, -⟩ :=
    FullCentralizerFromProjectiveModel.actual_projective_layer_model_determines_full_centralizer
      hnonab n hn S e hfour p f hp hp2 hf hlocal
  let : Field F := hFf
  let : Finite F := hFfin
  set M := CFSG.layer (centralizerOddCoreQuotient n S e) with hMdef
  have hMcard : Nat.card M = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [hin.matrix_card, hcard]
  let PM : Subgroup M := P.subgroupOf M
  have hPMcard : Nat.card PM = p ^ (Nat.card M).factorization p := by
    rw [hMcard, factorization_layer_card hp hf]
    change Nat.card (P.subgroupOf M) = _
    rw [CFSG.natCard_subgroupOf_eq _ _ hPM, hPcard]
  let PS : Sylow p M := Sylow.ofCard PM hPMcard
  obtain ⟨hall, -, -⟩ :=
    actual_reduced_centralizer_defining_sylow_centralizer_is_center_times_sylow
      hnonab n hn S e hfour p f hp hp2 hf hq hlocal
  obtain ⟨-, -, -, -, -, hodd⟩ := hall PS
  have hPH : (PS : Subgroup M).map M.subtype = P := by
    rw [Sylow.coe_ofCard]
    exact Subgroup.map_subgroupOf_eq_of_le hPM
  have hhC : h ∈ Subgroup.centralizer (((PS : Subgroup M).map M.subtype :
      Subgroup (centralizerOddCoreQuotient n S e)) : Set (centralizerOddCoreQuotient n S e)) := by
    rw [hPH, Subgroup.mem_centralizer_iff]
    exact hh
  obtain ⟨k, hk⟩ := hodd h hhC (hrodd.of_dvd_nat hhr)
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exfalso
    have hpdvd : p ∣ r := (dvd_pow_self p (Nat.succ_ne_zero k)).trans (hk ▸ hhr)
    exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp hpdvd).symm

theorem false_of_two_lifts
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) (J : Subgroup (involutionCentralizer n S e))
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (K : Subgroup G) (hK : K < ⊤) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (hyK : wreathModelHom S e (Original.x2 (2 ^ n)) ∈ K)
    (hJK : ∀ j ∈ J, (j : G) ∈ K) (g : G)
    (hgx : g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ =
      wreathModelHom S e (Original.x2 (2 ^ n)))
    (hJgK : ∀ j ∈ J, g * (j : G) * g⁻¹ ∈ K) (hO : CFSG.oddCore K ≠ ⊥) : False := by
  have hcoverx : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K := by
    rw [← hJM]
    exact Subgroup.map_mono fun j hj => hJK j hj
  set K' := K.map (MulAut.conj g⁻¹).toMonoidHom with hK'
  have hcovK' : ComponentCovered (wreathModelHom S e (Original.x (2 ^ n))) K' := by
    change CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      (K'.subgroupOf (involutionCentralizer n S e)).map (centralizerOddCoreMap n S e)
    rw [← hJM]
    refine Subgroup.map_mono fun j hj => ?_
    refine ⟨g * (j : G) * g⁻¹, hJgK j hj, ?_⟩
    change g⁻¹ * (g * (j : G) * g⁻¹) * g⁻¹⁻¹ = j
    group
  have hcovy := hcovK'.conj g
  have hKK : K'.map (MulAut.conj g).toMonoidHom = K := by
    rw [hK', Subgroup.map_map]
    convert Subgroup.map_id K
    ext b
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
    group
  rw [hKK, hgx] at hcovy
  have hy2 : orderOf (wreathModelHom S e (Original.x2 (2 ^ n))) = 2 :=
    CompatibleFamilies.orderOf_x2 S e hn
  have hyx : wreathModelHom S e (Original.x2 (2 ^ n)) ≠ wreathModelHom S e (Original.x (2 ^ n)) :=
    (BrauerWong.modelHom_x_ne_x2 S e (by omega)).symm
  exact hO (two_commuting_involution_component_covers_force_trivial_proper_subgroup_odd_core
    hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec _ hy2 hyx
    (ConfinedOddCore.x_mul_y n S e hn).symm K hK hxK hyK hcoverx hcovy).1

theorem fixed_prime_order_confined
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) (hst : OriginalAllPrimeStationarity n S e)
    (hdim : ExchangedDimension p f)
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal] [Group.IsPerfect J]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hcomm : ∀ j ∈ J, ∀ r ∈ centralizerOddCore n S e, Commute j r)
    (B : Subgroup G)
    (hBmem : ∀ z ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype,
      wreathModelHom S e (Original.x2 (2 ^ n)) * z *
        (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = z⁻¹ → z ∈ B)
    (hBconf : ∀ b ∈ B, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ involutionCentralizer n S e)
    (hBM : ∀ E : Subgroup G, ∀ hEN : E ≤ involutionCentralizer n S e, Odd (Nat.card E) →
      (∀ z ∈ E, wreathModelHom S e (Original.x2 (2 ^ n)) * z *
        (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = z⁻¹) →
      ∀ z (hz : z ∈ E), centralizerOddCoreMap n S e ⟨z, hEN hz⟩ ∈
        CFSG.layer (centralizerOddCoreQuotient n S e))
    (u : G) (huR : u ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    (huy : u * wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) * u)
    (hu : (orderOf u).Prime) :
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
  have huN : u ∈ involutionCentralizer n S e := Subgroup.map_subtype_le _ huR
  have hxu : x * u = u * x := (Subgroup.mem_centralizer_singleton_iff.mp huN).symm
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
      exact mem_normalizer_zpowers_of_conj (Or.inl (by rw [← huy, mul_inv_cancel_right]))
  have hU : Subgroup.zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.mp h)
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
  obtain ⟨⟨hWab, hWinv⟩, hJW, -, ⟨-, hF1⟩, -, -, -, -, -, -, -, -, -, -⟩ :=
    hall ell hell W hTW hWN
  set WG := ((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype).map H0.subtype
    with hWG
  have hWodd : Odd (Nat.card WG) := by
    have hO : Odd (Nat.card ((CFSG.oddCore H0).map H0.subtype)) := by
      rw [Subgroup.card_map_of_injective H0.subtype_injective]
      exact weakClosure_oddCore_card H0
    exact hO.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.map_mono (Subgroup.map_subtype_le _)))
  have hellodd : Odd ell :=
    (weakClosure_oddCore_card H0).of_dvd_nat hdivO
  have hWH0 : WG ≤ H0 := Subgroup.map_subtype_le _
  have hWu : ∀ w ∈ WG, w * u = u * w := fun w hw =>
    commute_of_inverted_mem_normalizer (hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard WG hw))
      (hWinv w hw) (hWH0 hw) hxu
  have hWp : IsPGroup ell WG := (W.isPGroup'.map _).map _
  have hWN' : ¬ WG ≤ involutionCentralizer n S e := hWN
  have hW1 : WG ≠ ⊥ := fun h => hWN' (by rw [h]; exact bot_le)
  have hJWG : ∀ j ∈ J, (j : G) ∈ Subgroup.normalizer (WG : Set G) := fun j hj =>
    Subgroup.le_normalizer_map H0.subtype (hJW ⟨j, hj, rfl⟩)
  have hyW : y ∈ Subgroup.normalizer (WG : Set G) := hTW hyT
  obtain ⟨g, hgT, hgx, hgy, hgxy⟩ := exists_cycler hnonab n hn S e
  replace hgx : g * x * g⁻¹ = y := hgx
  replace hgy : g * y * g⁻¹ = x * y := hgy
  have hxg : x = g⁻¹ * y * g⁻¹⁻¹ := by rw [← hgx]; group
  have hyg : y = g⁻¹ * (x * y) * g⁻¹⁻¹ := by rw [← hgy]; group
  have hcN : ∀ w : G, w * y = y * w → g⁻¹ * w * g⁻¹⁻¹ ∈ involutionCentralizer n S e := by
    intro w hwy
    rw [ConfinedOddCore.mem_involutionCentralizer_iff]
    change g⁻¹ * w * g⁻¹⁻¹ * x = x * (g⁻¹ * w * g⁻¹⁻¹)
    rw [hxg]
    calc g⁻¹ * w * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (w * y) * g⁻¹⁻¹ := by group
      _ = g⁻¹ * (y * w) * g⁻¹⁻¹ := by rw [hwy]
      _ = g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * w * g⁻¹⁻¹) := by group
  have hcinv : ∀ w ∈ WG, w * y = y * w →
      y * (g⁻¹ * w * g⁻¹⁻¹) * y⁻¹ = (g⁻¹ * w * g⁻¹⁻¹)⁻¹ := by
    intro w hw hwy
    have hxw : x * w * x⁻¹ = w⁻¹ := hWinv w hw
    have hxyw : (x * y) * w * (x * y)⁻¹ = w⁻¹ := by
      calc (x * y) * w * (x * y)⁻¹ = x * (w * y) * y⁻¹ * x⁻¹ := by rw [hwy]; group
        _ = w⁻¹ := by rw [show x * (w * y) * y⁻¹ * x⁻¹ = x * w * x⁻¹ by group, hxw]
    rw [hyg]
    calc g⁻¹ * (x * y) * g⁻¹⁻¹ * (g⁻¹ * w * g⁻¹⁻¹) * (g⁻¹ * (x * y) * g⁻¹⁻¹)⁻¹ =
        g⁻¹ * ((x * y) * w * (x * y)⁻¹) * g⁻¹⁻¹ := by group
      _ = (g⁻¹ * w * g⁻¹⁻¹)⁻¹ := by rw [hxyw]; group
  set E := WG ⊓ Subgroup.centralizer ({y} : Set G) with hEdef
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'def
  have hE'N : E' ≤ involutionCentralizer n S e := by
    rintro _ ⟨w, hw, rfl⟩
    exact hcN w (Subgroup.mem_centralizer_singleton_iff.mp hw.2)
  have hE'odd : Odd (Nat.card E') := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hWodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hE'inv : ∀ z ∈ E', y * z * y⁻¹ = z⁻¹ := by
    rintro _ ⟨w, hw, rfl⟩
    exact hcinv w hw.1 (Subgroup.mem_centralizer_singleton_iff.mp hw.2)
  have hEB : ∀ w ∈ WG, w * y = y * w → g⁻¹ * w * g⁻¹⁻¹ ∈ B → w = 1 := by
    intro w hw hwy hwB
    by_contra hw1
    have hb1 : g⁻¹ * w * g⁻¹⁻¹ ≠ 1 := fun h => hw1 (by
      have : w = g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ := by group
      rw [this, h]
      group)
    have hC := hBconf _ hwB hb1
    apply hF1
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzw : z * w = w * z :=
      congrArg Subtype.val (hWab.is_comm.comm ⟨z, hz.1⟩ ⟨w, hw⟩)
    have hcz : g⁻¹ * z * g⁻¹⁻¹ ∈ involutionCentralizer n S e := by
      apply hC
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * z * g⁻¹⁻¹ * (g⁻¹ * w * g⁻¹⁻¹) = g⁻¹ * (z * w) * g⁻¹⁻¹ := by group
        _ = g⁻¹ * (w * z) * g⁻¹⁻¹ := by rw [hzw]
        _ = g⁻¹ * w * g⁻¹⁻¹ * (g⁻¹ * z * g⁻¹⁻¹) := by group
    have hzy : z * y = y * z := by
      have h1 := (ConfinedOddCore.mem_involutionCentralizer_iff n S e _).mp hcz
      change g⁻¹ * z * g⁻¹⁻¹ * x = x * (g⁻¹ * z * g⁻¹⁻¹) at h1
      rw [hxg] at h1
      have h2 : g⁻¹ * (z * y) * g⁻¹⁻¹ = g⁻¹ * (y * z) * g⁻¹⁻¹ := by
        calc g⁻¹ * (z * y) * g⁻¹⁻¹ = g⁻¹ * z * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) := by group
          _ = g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * z * g⁻¹⁻¹) := h1
          _ = g⁻¹ * (y * z) * g⁻¹⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
    have hxz : x * z * x⁻¹ = z⁻¹ := hWinv z hz.1
    have hxyz : (x * y) * z = z * (x * y) := (Subgroup.mem_centralizer_singleton_iff.mp hz.2).symm
    have hyz : y * z * y⁻¹ = z⁻¹ := by
      have hy' : y = x⁻¹ * (x * y) := by group
      rw [hy']
      calc x⁻¹ * (x * y) * z * (x⁻¹ * (x * y))⁻¹ = x⁻¹ * ((x * y) * z) * (x * y)⁻¹ * x := by
            group
        _ = x⁻¹ * z * x := by rw [hxyz]; group
        _ = z⁻¹ := by
          have hx' : x⁻¹ = x := by
            rw [inv_eq_iff_mul_eq_one, ← pow_two, ← orderOf_dvd_iff_pow_eq_one, hx2]
          rw [hx']
          nth_rewrite 2 [← hx']
          exact hxz
    have hzodd : Odd (orderOf z) := hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard WG hz.1)
    apply eq_one_of_eq_inv_of_odd hzodd
    rw [← hyz, ← hzy, mul_inv_cancel_right]
  have hcM : ∀ w (hw : w ∈ WG) (hwy : w * y = y * w),
      centralizerOddCoreMap n S e ⟨g⁻¹ * w * g⁻¹⁻¹, hcN w hwy⟩ ∈
        CFSG.layer (centralizerOddCoreQuotient n S e) := fun w hw hwy =>
    hBM E' hE'N hE'odd hE'inv _ ⟨w, ⟨hw, Subgroup.mem_centralizer_singleton_iff.mpr hwy⟩, rfl⟩
  have hcker : ∀ w (hw : w ∈ WG) (hwy : w * y = y * w),
      centralizerOddCoreMap n S e ⟨g⁻¹ * w * g⁻¹⁻¹, hcN w hwy⟩ = 1 → w = 1 := by
    intro w hw hwy h1
    have hR : (⟨g⁻¹ * w * g⁻¹⁻¹, hcN w hwy⟩ : involutionCentralizer n S e) ∈
        centralizerOddCore n S e := (QuotientGroup.eq_one_iff _).mp h1
    exact hEB w hw hwy (hBmem _ ⟨_, hR, rfl⟩ (hcinv w hw hwy))
  obtain ⟨hlp, hEcard⟩ := eigen_dimension hnonab n hn S e hfour p f hp hpodd hf hlocal hdim J hJM
    hcomm WG hWab hW1 hell hellodd hWp hWinv hJWG hyW g⁻¹ (fun w _ hwy => hcN w hwy)
    (fun w hw hwy => hcM w hw hwy) (fun w hw hwy => hcker w hw hwy)
  set E'N := E'.subgroupOf (involutionCentralizer n S e) with hE'N'
  set P := E'N.map (centralizerOddCoreMap n S e) with hPdef
  have hPM : P ≤ CFSG.layer (centralizerOddCoreQuotient n S e) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hBM E' hE'N hE'odd hE'inv (z : G) hz
  have hπinj : Function.Injective ((centralizerOddCoreMap n S e).comp E'N.subtype) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    obtain ⟨w, hw, hwz⟩ := (z.2 : (z : involutionCentralizer n S e) ∈ E'N)
    replace hwz : g⁻¹ * w * g⁻¹⁻¹ = ((z : involutionCentralizer n S e) : G) := hwz
    have hwy : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
    have h1 : centralizerOddCoreMap n S e ⟨g⁻¹ * w * g⁻¹⁻¹, hcN w hwy⟩ = 1 := by
      have : (⟨g⁻¹ * w * g⁻¹⁻¹, hcN w hwy⟩ : involutionCentralizer n S e) = z :=
        Subtype.ext hwz
      rw [this]
      exact hz
    have hw1 := hcker w hw.1 hwy h1
    apply Subtype.ext
    apply Subtype.ext
    change ((z : involutionCentralizer n S e) : G) = 1
    rw [← hwz, hw1]
    group
  have hPcard : Nat.card P = p ^ f := by
    have hrange : P = ((centralizerOddCoreMap n S e).comp E'N.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv,
      CFSG.natCard_subgroupOf_eq _ _ hE'N,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hEcard]
  set uN : involutionCentralizer n S e := ⟨g⁻¹ * u * g⁻¹⁻¹, hcN u huy⟩ with huN'
  have huP : ∀ z ∈ P, z * centralizerOddCoreMap n S e uN = centralizerOddCoreMap n S e uN * z := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨w, hw, hwz⟩ := (hz : (z : G) ∈ E')
    replace hwz : g⁻¹ * w * g⁻¹⁻¹ = (z : G) := hwz
    apply Subtype.ext
    change (z : G) * (g⁻¹ * u * g⁻¹⁻¹) = (g⁻¹ * u * g⁻¹⁻¹) * z
    rw [← hwz]
    have hwu := hWu w hw.1
    calc g⁻¹ * w * g⁻¹⁻¹ * (g⁻¹ * u * g⁻¹⁻¹) = g⁻¹ * (w * u) * g⁻¹⁻¹ := by group
      _ = g⁻¹ * (u * w) * g⁻¹⁻¹ := by rw [hwu]
      _ = (g⁻¹ * u * g⁻¹⁻¹) * (g⁻¹ * w * g⁻¹⁻¹) := by group
  have hrp : orderOf u ≠ p := hlp ▸
    orderOf_ne_of_normal_inverted_sylow H0 le_rfl (hNF.2.1 (Subgroup.mem_zpowers u)) hell W
      hWinv hxu huodd hu1
  have huNord : orderOf (centralizerOddCoreMap n S e uN) ∣ orderOf u := by
    refine (orderOf_map_dvd _ uN).trans ?_
    rw [← Subgroup.orderOf_coe]
    change orderOf ((MulAut.conj g⁻¹) u) ∣ orderOf u
    rw [MulEquiv.orderOf_eq]
  have hu1' := eq_one_of_commute_defining_sylow hnonab n hn S e hfour p f hp hpodd hf hq hlocal P
    hPM hPcard _ huP hu huodd huNord hrp
  have huR' : uN ∈ centralizerOddCore n S e := (QuotientGroup.eq_one_iff _).mp hu1'
  have hJg : ∀ j ∈ J, g * (j : G) * g⁻¹ ∈ H0 := by
    intro j hj
    apply ConfinedOddCore.centralizer_singleton_le_normalizer_zpowers
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val (hcomm j hj uN huR').eq
    change (j : G) * (g⁻¹ * u * g⁻¹⁻¹) = (g⁻¹ * u * g⁻¹⁻¹) * j at h1
    calc g * (j : G) * g⁻¹ * u = g * ((j : G) * (g⁻¹ * u * g⁻¹⁻¹)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g⁻¹⁻¹) * j) * g⁻¹ := by rw [h1]
      _ = u * (g * (j : G) * g⁻¹) := by group
  exact false_of_two_lifts hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec J hJM H0 hNF.1
    (hTu hxT) (hTu hyT) (fun j hj => hJ0 ⟨j, hj, rfl⟩) g hgx hJg
    (fun h => hNF.2.2.1 (by rw [h, Subgroup.map_bot]))

theorem odd_core_confined_of_dimension
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e)
    (hdim : ExchangedDimension p f) :
    ∀ u ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, u ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ involutionCentralizer n S e ∧
        Subgroup.centralizer ({u} : Set G) ≤ involutionCentralizer n S e := by
  obtain ⟨J, hJn, hJperf, hJM, hcomm, hidx⟩ :=
    canonical_lift hnonab n hn S e hfour p f hp hpodd hf hlocal hcov
  have hfac := normalizerFactorization_of_lift hnonab n hn S e hfour p f hp hpodd hf hq hlocal
    hrec J hJM hcomm
  obtain ⟨B, hBset, hBR, -, -, -, -, -, -, -, hBE⟩ :=
    inverted_factor hnonab n hn S e hfour hst (fun U hU hUR => hfac U hUR hU) J hcomm hidx
  obtain ⟨B₁, hB₁set, -, -, -, -, -, -, -, hconf₁⟩ :=
    stationarity_and_original_coverage_confine_inverted_odd_core_elements hnonab n hn S e hfour
      p f hp hpodd hf hq hlocal hrec hst hcov
  have hB₁ : B₁ = B := SetLike.coe_injective (hB₁set.trans hBset.symm)
  subst hB₁
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hydef
  have hmemB : ∀ r : involutionCentralizer n S e, r ∈ B₁ ↔
      r ∈ centralizerOddCore n S e ∧ y * (r : G) * y⁻¹ = (r : G)⁻¹ := fun r => by
    change r ∈ (B₁ : Set (involutionCentralizer n S e)) ↔ _
    rw [hB₁set]
    rfl
  have hBmem : ∀ z ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype,
      y * z * y⁻¹ = z⁻¹ → z ∈ B₁.map (involutionCentralizer n S e).subtype := by
    rintro _ ⟨r, hr, rfl⟩ hinv
    exact ⟨r, (hmemB r).mpr ⟨hr, hinv⟩, rfl⟩
  have hBconf : ∀ b ∈ B₁.map (involutionCentralizer n S e).subtype, b ≠ 1 →
      Subgroup.centralizer ({b} : Set G) ≤ involutionCentralizer n S e := by
    rintro _ ⟨b, hb, rfl⟩ hb1
    exact (hconf₁ b hb (fun h => hb1 (by rw [h]; rfl))).2
  have hBM : ∀ E : Subgroup G, ∀ hEN : E ≤ involutionCentralizer n S e, Odd (Nat.card E) →
      (∀ z ∈ E, y * z * y⁻¹ = z⁻¹) →
      ∀ z (hz : z ∈ E), centralizerOddCoreMap n S e ⟨z, hEN hz⟩ ∈
        CFSG.layer (centralizerOddCoreQuotient n S e) := by
    intro E hEN hEodd hEinv z hz
    have hodd : Odd (Nat.card (E.subgroupOf (involutionCentralizer n S e))) := by
      rw [CFSG.natCard_subgroupOf_eq _ _ hEN]
      exact hEodd
    have hle := (hBE _ hodd fun w hw => hEinv w hw).1
    have hzJB : (⟨z, hEN hz⟩ : involutionCentralizer n S e) ∈ J ⊔ B₁ := hle hz
    have hmap : (J ⊔ B₁).map (centralizerOddCoreMap n S e) =
        CFSG.layer (centralizerOddCoreQuotient n S e) := by
      rw [Subgroup.map_sup, hJM]
      have hBbot : B₁.map (centralizerOddCoreMap n S e) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        intro b hb
        exact (QuotientGroup.ker_mk' (centralizerOddCore n S e)).symm ▸ hBR hb
      rw [hBbot, sup_bot_eq]
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hzJB
  have hprime : ∀ u ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype,
      (orderOf u).Prime →
        Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ involutionCentralizer n S e := by
    rintro _ ⟨uN, huN, rfl⟩ hu
    set r := orderOf (uN : G) with hrdef
    have : Fact r.Prime := ⟨hu⟩
    let uR : centralizerOddCore n S e := ⟨uN, huN⟩
    have hordR : orderOf uR = r := by
      rw [hrdef, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    have hup : IsPGroup r (Subgroup.zpowers uR) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordR, pow_one])
    have hrdiv : r ∣ Nat.card (centralizerOddCore n S e) := by
      rw [← hordR]
      exact orderOf_dvd_natCard uR
    let yN : involutionCentralizer n S e :=
      ⟨y, ConfinedOddCore.y_mem_involutionCentralizer n hn S e⟩
    obtain ⟨P, ⟨Q, hQP⟩, -, hscalar⟩ := scalar_sylows hnonab n hn S e hfour hst
      (fun U hU hUR => hfac U hUR hU) yN rfl r hu hrdiv
    obtain ⟨Q', hQ'⟩ := hup.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (centralizerOddCore n S e) Q' Q
    have hvQ : c * uR * c⁻¹ ∈ (Q : Subgroup (centralizerOddCore n S e)) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul uR (MulAut.conj c) (Q' : Subgroup _)
        (hQ' (Subgroup.mem_zpowers uR))
    set vR := c * uR * c⁻¹ with hvR
    have hvP : (vR : involutionCentralizer n S e) ∈ P := by
      rw [← hQP]
      exact ⟨vR, hvQ, rfl⟩
    have hvG : ((vR : involutionCentralizer n S e) : G) = (c : G) * uN * (c : G)⁻¹ := rfl
    have hvR' : ((vR : involutionCentralizer n S e) : G) ∈
        (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype :=
      ⟨vR, vR.2, rfl⟩
    have hvord : orderOf ((vR : involutionCentralizer n S e) : G) = r := by
      rw [hvG, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    have hcN : ((c : involutionCentralizer n S e) : G) ∈ involutionCentralizer n S e :=
      (c : involutionCentralizer n S e).2
    apply normalizer_zpowers_le_of_conj hcN
    change Subgroup.normalizer (Subgroup.zpowers ((vR : involutionCentralizer n S e) : G) :
      Set G) ≤ involutionCentralizer n S e
    rcases hscalar with hfix | hinv
    · have h1 := congrArg Subtype.val (hfix _ hvP)
      change y * ((vR : involutionCentralizer n S e) : G) * y⁻¹ = _ at h1
      have hvy : ((vR : involutionCentralizer n S e) : G) * y =
          y * ((vR : involutionCentralizer n S e) : G) := by
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      exact fixed_prime_order_confined hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec hst
        hdim J hJM hcomm _ hBmem hBconf hBM _ hvR' hvy (by rw [hvord]; exact hu)
    · have h1 := congrArg Subtype.val (hinv _ hvP)
      change y * ((vR : involutionCentralizer n S e) : G) * y⁻¹ = _ at h1
      have hvB := hBmem _ hvR' h1
      obtain ⟨b, hb, hbv⟩ := hvB
      have hb1 : b ≠ 1 := by
        intro h
        have h2 : orderOf ((vR : involutionCentralizer n S e) : G) = 1 := by
          rw [← hbv, h, map_one, orderOf_one]
        rw [hvord] at h2
        exact hu.one_lt.ne' h2
      have := (hconf₁ b hb hb1).1
      rw [← hbv]
      exact this
  exact fun u hu hu1 => confined_of_prime_order (involutionCentralizer n S e)
    ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) hprime hu hu1

end Main

end CFSG.Wreathed.ComponentCoverConfinement
