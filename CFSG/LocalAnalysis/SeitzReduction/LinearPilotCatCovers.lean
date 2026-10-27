module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatStatement
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatCovers

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut centerQuotientAut_mk FixedCentralizerTwoFree
  centerFixedProjection coe_centerFixedProjection map_center_mulAut orderOf_centerQuotientAut
  centerQuotientAut_mem_range odd_card_center_of_twoFree twoFree_centerQuotientAut
  isPGroup_zpowers_of_pow_eq_one)

theorem lieModel_quotient_center_of_center_eq_bot {D : Type} [Group D] (hZ : center D = ⊥)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (h : LieModel D t n p f) :
    LieModel (D ⧸ center D) t n p f :=
  LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm h

section Image

variable {K : Type} [Group K] {τ : MulAut K}

theorem ker_subgroupMap_centerFixedProjection_le_center (D : Subgroup (fixedSubgroup τ)) :
    ((centerFixedProjection τ).subgroupMap D).ker ≤ center D := by
  intro d hd
  rw [MonoidHom.mem_ker] at hd
  have hdZ : ((d : fixedSubgroup τ) : K) ∈ center K := by
    have h1 : QuotientGroup.mk' (center K) ((d : fixedSubgroup τ) : K) = 1 :=
      congrArg Subtype.val (congrArg Subtype.val hd)
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  rw [mem_center_iff]
  intro d'
  apply Subtype.ext
  apply Subtype.ext
  exact mem_center_iff.mp hdZ _

theorem isComponent_map_centerFixedProjection {D : Subgroup (fixedSubgroup τ)}
    (hD : IsComponent D) :
    IsComponent (D.map (centerFixedProjection τ)) ∧
      Nonempty (D ⧸ center D ≃*
        (D.map (centerFixedProjection τ)) ⧸ center (D.map (centerFixedProjection τ))) := by
  have hinv := map_center_mulAut τ
  have hker := ker_subgroupMap_centerFixedProjection_le_center D
  have hsurj := (centerFixedProjection τ).subgroupMap_surjective D
  refine ⟨⟨CFSG.LocalCores.isQuasisimple_of_surjective hD.1 _ hsurj hker, ?_⟩,
    LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hD.1 _ hsurj hker⟩
  have hsub : (D.map (fixedImageProjection (center K) τ hinv)).IsSubnormal :=
    hD.2.map (fixedImageProjection_surjective (center K) τ hinv)
  have hnormal : (fixedImage (center K) τ hinv).Normal :=
    fixedImage_normal (center K) τ hinv le_rfl
  have htrans := hsub.trans' hnormal.isSubnormal
  have hcomp : (fixedImage (center K) τ hinv).subtype.comp
      (fixedImageProjection (center K) τ hinv) = centerFixedProjection τ :=
    MonoidHom.ext fun _ => rfl
  rwa [map_map, hcomp] at htrans

end Image

section TwoSmall

variable {K : Type} [Group K] [Finite K] {τ : MulAut K}

theorem exists_two_element_conj_eq {k : K} (hτ : orderOf (MulAut.conj k) = 2) :
    ∃ k' : K, MulAut.conj k' = MulAut.conj k ∧ ∃ a : ℕ, k' ^ 2 ^ a = 1 := by
  obtain ⟨a, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  refine ⟨k ^ o, ?_, a, ?_⟩
  · rw [map_pow]
    obtain ⟨j, rfl⟩ := ho
    have h2 : (MulAut.conj k) ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one _
    rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  · rw [← pow_mul, mul_comm, ← hko, pow_orderOf_eq_one]

theorem odd_card_center_of_twoSmall_inner {D : Subgroup (fixedSubgroup τ)} (hτ : orderOf τ = 2)
    (hin : τ ∈ (MulAut.conj : K →* MulAut K).range) (hsmall : FixedCentralizerTwoSmall τ D) :
    Odd (Nat.card (center K)) := by
  obtain ⟨k, rfl⟩ := hin
  obtain ⟨k', hk', a, hka⟩ := exists_two_element_conj_eq hτ
  by_contra hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (center K) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := center K) 2 h2
  set z : K := (g : K) with hzdef
  have hzZ : z ∈ center K := g.2
  have hz : orderOf z = 2 := by rw [hzdef, Subgroup.orderOf_coe]; exact hg
  have hzle : zpowers z ≤ center K := zpowers_le.mpr hzZ
  have hzN : (zpowers z).Normal := ⟨fun n hn x => by
    rw [mem_center_iff.mp (hzle hn) x, mul_inv_cancel_right]
    exact hn⟩
  have hp1 : IsPGroup 2 (zpowers k') := isPGroup_zpowers_of_pow_eq_one hka
  have hp2 : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hp := hp1.to_sup_of_normal_right hp2
  have hk'fix : ∀ x : K, x ∈ fixedSubgroup (MulAut.conj k) → x * k' = k' * x := by
    intro x hx
    have hx' : MulAut.conj k' x = x := by rw [hk']; exact hx
    rw [MulAut.conj_apply] at hx'
    calc x * k' = k' * x * k'⁻¹ * k' := by rw [hx']
      _ = k' * x := by group
  have hUc : zpowers k' ⊔ zpowers z ≤
      centralizer ((D.map (fixedSubgroup (MulAut.conj k)).subtype : Subgroup K) : Set K) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_iff]
      rintro _ ⟨d, -, rfl⟩
      exact hk'fix _ d.2
    · rw [mem_centralizer_iff]
      intro x _
      exact (mem_center_iff.mp hzZ x)
  have hUf : zpowers k' ⊔ zpowers z ≤ fixedSubgroup (MulAut.conj k) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · change MulAut.conj k k' = k'
      rw [← hk', MulAut.conj_apply, mul_inv_cancel_right]
    · change MulAut.conj k z = z
      rw [MulAut.conj_apply, mem_center_iff.mp hzZ k, mul_inv_cancel_right]
  have hcard := hsmall _ hp hUc hUf
  have heq : zpowers z = zpowers k' ⊔ zpowers z :=
    eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, hz]; exact hcard)
  have hk'Z : k' ∈ center K := hzle (heq ▸ mem_sup_left (mem_zpowers k'))
  have hc1 : MulAut.conj k' = 1 := by
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← mem_center_iff.mp hk'Z x, mul_inv_cancel_right]
  rw [← hk', hc1, orderOf_one] at hτ
  exact absurd hτ (by norm_num)

omit [Finite K] in
theorem fixed_and_mem_centralizer_of_two_element {D : Subgroup (fixedSubgroup τ)}
    (hDp : Group.IsPerfect D) (hZ : Odd (Nat.card (center K))) {u : K} {k : ℕ}
    (hun : u ^ 2 ^ k = 1)
    (hfix : QuotientGroup.mk' (center K) u ∈ fixedSubgroup (centerQuotientAut τ))
    (hcen : QuotientGroup.mk' (center K) u ∈ centralizer
      (((D.map (centerFixedProjection τ)).map (fixedSubgroup (centerQuotientAut τ)).subtype :
        Subgroup (K ⧸ center K)) : Set (K ⧸ center K))) :
    u ∈ fixedSubgroup τ ∧
      u ∈ centralizer ((D.map (fixedSubgroup τ).subtype : Subgroup K) : Set K) := by
  set n := 2 ^ k with hn
  have hcop : (Nat.card (center K)).Coprime n :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hZ)
  have hτu : τ u = u := by
    have h1 : QuotientGroup.mk' (center K) (τ u) = QuotientGroup.mk' (center K) u := by
      rw [← centerQuotientAut_mk]
      exact hfix
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    set c := (τ u)⁻¹ * u with hcdef
    have hcZ : c ∈ center K := h1
    have hτu' : τ u = u * c⁻¹ := by rw [hcdef]; group
    have hcn : c ^ n = 1 := by
      have h2 : (τ u) ^ n = 1 := by rw [← map_pow, hun, map_one]
      have hcomm : Commute u c⁻¹ := mem_center_iff.mp (inv_mem hcZ) u
      rw [hτu', hcomm.mul_pow, hun, one_mul, inv_pow] at h2
      exact inv_eq_one.mp h2
    have hco : orderOf (⟨c, hcZ⟩ : center K) = 1 := by
      have h3 : orderOf (⟨c, hcZ⟩ : center K) ∣ n :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hcn))
      exact Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard _) hcop) h3
    have hc1 : c = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hco)
    rw [hcdef, inv_mul_eq_one] at hc1
    exact hc1
  refine ⟨hτu, ?_⟩
  let ι : D →* K := (fixedSubgroup τ).subtype.comp D.subtype
  have hcomZ : ∀ d : D, u * ι d * u⁻¹ * (ι d)⁻¹ ∈ center K := by
    intro d
    have hmem : ((centerFixedProjection τ (d : fixedSubgroup τ) :
        fixedSubgroup (centerQuotientAut τ)) : K ⧸ center K) ∈
        ((D.map (centerFixedProjection τ)).map (fixedSubgroup (centerQuotientAut τ)).subtype :
          Subgroup (K ⧸ center K)) :=
      mem_map_of_mem _ (mem_map_of_mem _ d.2)
    have h1 := mem_centralizer_iff.mp hcen _ hmem
    rw [coe_centerFixedProjection, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have hab : (ι d * u)⁻¹ * (u * ι d) ∈ center K := h1
    have hc := mem_center_iff.mp hab (ι d * u)
    have heq : u * ι d * u⁻¹ * (ι d)⁻¹ = (ι d * u)⁻¹ * (u * ι d) := by
      calc u * ι d * u⁻¹ * (ι d)⁻¹ =
            ((ι d * u) * ((ι d * u)⁻¹ * (u * ι d))) * (ι d * u)⁻¹ := by group
        _ = (((ι d * u)⁻¹ * (u * ι d)) * (ι d * u)) * (ι d * u)⁻¹ := by rw [hc]
        _ = (ι d * u)⁻¹ * (u * ι d) := by group
    rw [heq]
    exact hab
  let γ : D →* center K :=
    { toFun := fun d => ⟨u * ι d * u⁻¹ * (ι d)⁻¹, hcomZ d⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        have hb := mem_center_iff.mp (hcomZ b) (ι a)⁻¹
        change u * ι (a * b) * u⁻¹ * (ι (a * b))⁻¹ =
          (u * ι a * u⁻¹ * (ι a)⁻¹) * (u * ι b * u⁻¹ * (ι b)⁻¹)
        calc u * ι (a * b) * u⁻¹ * (ι (a * b))⁻¹ =
              u * ι a * u⁻¹ * ((u * ι b * u⁻¹ * (ι b)⁻¹) * (ι a)⁻¹) := by
                rw [map_mul]; group
          _ = u * ι a * u⁻¹ * ((ι a)⁻¹ * (u * ι b * u⁻¹ * (ι b)⁻¹)) := by rw [hb]
          _ = (u * ι a * u⁻¹ * (ι a)⁻¹) * (u * ι b * u⁻¹ * (ι b)⁻¹) := by group }
  have hγ : ∀ d : D, u * ι d = ι d * u := by
    intro d
    have h1 : γ d = 1 := Abelianization.commutator_subset_ker γ Group.IsPerfect.mem_commutator
    have h2 : u * ι d * u⁻¹ * (ι d)⁻¹ = 1 := congrArg Subtype.val h1
    calc u * ι d = (u * ι d * u⁻¹ * (ι d)⁻¹) * (ι d * u) := by group
      _ = ι d * u := by rw [h2, one_mul]
  rw [mem_centralizer_iff]
  rintro _ ⟨g, hg, rfl⟩
  exact (hγ ⟨g, hg⟩).symm

theorem card_comap_mk_center (Ū : Subgroup (K ⧸ center K)) :
    Nat.card (Ū.comap (QuotientGroup.mk' (center K))) = Nat.card Ū * Nat.card (center K) := by
  have hidx : (Ū.comap (QuotientGroup.mk' (center K))).index = Ū.index :=
    index_comap_of_surjective Ū (QuotientGroup.mk'_surjective _)
  have h1 := card_mul_index (Ū.comap (QuotientGroup.mk' (center K)))
  have h2 := card_mul_index Ū
  have h3 := card_eq_card_quotient_mul_card_subgroup (center K)
  have hpos : 0 < Ū.index := Nat.pos_of_ne_zero (index_ne_zero_of_finite)
  rw [hidx] at h1
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, h3, ← h2]
  ring

theorem twoSmall_centerQuotientAut {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (hZ : Odd (Nat.card (center K))) (hsmall : FixedCentralizerTwoSmall τ D) :
    FixedCentralizerTwoSmall (centerQuotientAut τ) (D.map (centerFixedProjection τ)) := by
  intro Ū hŪ hŪc hŪf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup K := Ū.comap (QuotientGroup.mk' (center K)) with hP
  obtain ⟨S⟩ : Nonempty (Sylow 2 P) := inferInstance
  set U : Subgroup K := (S : Subgroup P).map P.subtype with hU
  have hUp : IsPGroup 2 U := S.isPGroup'.map _
  have hUmem : ∀ u ∈ U, QuotientGroup.mk' (center K) u ∈ Ū := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hUlift : ∀ u ∈ U, u ∈ fixedSubgroup τ ∧
      u ∈ centralizer ((D.map (fixedSubgroup τ).subtype : Subgroup K) : Set K) := by
    intro u hu
    obtain ⟨k, hk⟩ := hUp ⟨u, hu⟩
    have huk : u ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact fixed_and_mem_centralizer_of_two_element hD.1.1 hZ huk (hŪf (hUmem u hu))
      (hŪc (hUmem u hu))
  have hU2 := hsmall U hUp (fun u hu => (hUlift u hu).2) (fun u hu => (hUlift u hu).1)
  obtain ⟨a, ha⟩ := hŪ.exists_card_eq
  have hcardU : Nat.card U = Nat.card Ū := by
    have hZ0 : Nat.card (center K) ≠ 0 := Nat.card_pos.ne'
    have hZ2 : ¬ 2 ∣ Nat.card (center K) := by
      rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
      exact hZ
    rw [hU, card_map_of_injective P.subtype_injective, Sylow.card_eq_multiplicity,
      card_comap_mk_center, ha, Nat.factorization_mul (by positivity) hZ0,
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hZ2, add_zero]
  omega

end TwoSmall

theorem catSLmCovers : CatSLmCovers := by
  intro K _ _ hK τ hτ m f D hD hDm
  have : Group.IsPerfect K := hK.1
  obtain ⟨hD', ⟨e⟩⟩ := isComponent_map_centerFixedProjection hD
  refine ⟨orderOf_centerQuotientAut hτ, centerQuotientAut_mem_range,
    D.map (centerFixedProjection τ), hD', LieType.CurtisTits.lieModel_of_mulEquiv e hDm,
    fun hodd => ⟨odd_card_center_of_twoFree hτ hodd, twoFree_centerQuotientAut hD hτ hodd⟩,
    fun hin hsmall => ?_⟩
  have hZ := odd_card_center_of_twoSmall_inner hτ hin hsmall
  exact ⟨hZ, twoSmall_centerQuotientAut hD hZ hsmall⟩

end CFSG.SeitzReduction.LinearPilot
