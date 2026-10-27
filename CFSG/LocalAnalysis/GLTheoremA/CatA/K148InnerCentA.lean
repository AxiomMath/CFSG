module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148InnerCentATorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148InnerMain
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148Inner

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley
open CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
open CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)

open scoped Matrix Pointwise

theorem twoPart_mul_odd {m n : ℕ} (hm : m ≠ 0) (hn : ¬ 2 ∣ n) : twoPart (m * n) = twoPart m := by
  unfold twoPart
  rw [Nat.factorization_mul hm (fun h => hn (by rw [h]; exact dvd_zero 2)), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hn, add_zero]

theorem twoPart_two_pow (k : ℕ) : twoPart (2 ^ k) = 2 ^ k := by
  unfold twoPart
  rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

theorem natCard_le_twoPart_of_le_of_isPGroup {G : Type*} [Group G] [Finite G] {U R : Subgroup G}
    (hUR : U ≤ R) (hU : IsPGroup 2 U) : Nat.card U ≤ twoPart (Nat.card R) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card R := hk ▸ Subgroup.card_dvd_of_le hUR
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  calc Nat.card U = 2 ^ k := hk
    _ ≤ 2 ^ (Nat.card R).factorization 2 := Nat.pow_le_pow_right (by norm_num) hle
    _ = twoPart (Nat.card R) := rfl

theorem d4A2Qv_le_adjointGroup {L : Type} [Field L]
    (v : WeylGroup Tag.D4) :
    CFSG.RankThree.Chevalley.d4A2Qv L v ≤ adjointGroup Tag.D4 L := by
  intro u hu
  rw [CFSG.RankThree.Chevalley.d4A2Qv, Subgroup.mem_map] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  have hn := canonicalRep_mem_adjointGroup (coxeterSystem Tag.D4) L v
  exact mul_mem (mul_mem hn (subsystemGroup_le_adjointGroup_of_any _ hs)) (inv_mem hn)

section Certs


theorem threeSixSingularR_equiv_threeSixRΩ {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ε : ℤ}
    {g : ModGL TwistTag.D4.tag Ω} (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε) (v : WeylGroup Tag.D4) :
    Nonempty (threeSixSingularR Ω K σ Fr ε v g ≃*
      threeSixRΩ Ω Fr ε v) := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hq0)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hFrs : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hq0)
    exact ⟨z, by rw [hFr, hz]⟩
  have hrange := range_threeSixEmb hℓ hf hK hσ Fr hFr
  have hR := threeSixSingularR_eq_comap (K := K) (σ := σ) hrange hgG hFg v
  have hRmem : ∀ y, y ∈ threeSixSingularR Ω K σ Fr ε v g ↔
      threeSixEmb' Ω K σ g y ∈ tsQv Ω v := fun y => by
    rw [hR, Subgroup.mem_comap]
  have hfixι : ∀ y, threeSixFrob Ω Fr ε (threeSixEmb' Ω K σ g y) = threeSixEmb' Ω K σ g y :=
    fun y => ((mem_range_threeSixEmb' hrange hgG hFg _).1 ⟨y, rfl⟩).2
  have hQG : tsQv Ω v ≤ adjointGroup TwistTag.D4.tag Ω :=
    fun u hu => d4A2Qv_le_adjointGroup v hu
  let eR : threeSixSingularR Ω K σ Fr ε v g ≃* threeSixRΩ Ω Fr ε v :=
    MulEquiv.ofBijective (((threeSixEmb' Ω K σ g).comp
      (threeSixSingularR Ω K σ Fr ε v g).subtype).codRestrict (threeSixRΩ Ω Fr ε v)
        fun y => Subgroup.mem_inf.2 ⟨(hRmem y).1 y.2, hfixι y⟩)
      ⟨fun y y' h => Subtype.ext (threeSixEmb'_injective g (congrArg Subtype.val h)), fun u => by
        obtain ⟨y, hy⟩ := (mem_range_threeSixEmb' hrange hgG hFg u).2
          ⟨hQG (Subgroup.mem_inf.1 u.2).1, (Subgroup.mem_inf.1 u.2).2⟩
        refine ⟨⟨y, (hRmem y).2 ?_⟩, Subtype.ext hy⟩
        rw [hy]
        exact (Subgroup.mem_inf.1 u.2).1⟩
  exact ⟨eR⟩

theorem natCard_threeSixSingularR_unitary {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {a : Fin TwistTag.D4.tag.rank → Ωˣ}
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr (-1))
    {v : WeylGroup Tag.D4} (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a)
    {g : ModGL TwistTag.D4.tag Ω} (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω (-1)) :
    Nat.card (threeSixSingularR Ω K σ Fr (-1) v g) =
      (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hq0)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hFrs : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hq0)
    exact ⟨z, by rw [hFr, hz]⟩
  have hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW (-1) *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma :=
    threeSix_stab hFr (Or.inr rfl) ha hv
  obtain ⟨eR⟩ := threeSixSingularR_equiv_threeSixRΩ hℓ hf hK hσ hFr hgG hFg v
  have eRF := eR.trans (threeSixRΩEquivFix Fr hFrs (Or.inr rfl) v hstab)
  rw [Nat.card_congr eRF.toEquiv]
  obtain ⟨π, b, hb⟩ := threeSix_phi_unitary (Ω := Ω) Fr hFrs v hstab
  obtain ⟨hcl, h₀⟩ := setup_k₀ (Ω := Ω) hℓ hf hK hσ
  haveI := hcl
  obtain ⟨-, ⟨H, hH⟩, -, -, -⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary
      (k := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) hℓ hf h₀ π _ b
      (fun i j hij t => by rw [hb, hFr])
  exact CFSG.RankThree.PartOne.D4RC.rcl_card_fix_unitary
    (k := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) hℓ hf h₀ _ H hH

theorem twoPart_natCard_threeSixSingularR {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ = 2) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {a : Fin TwistTag.D4.tag.rank → Ωˣ}
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr (-1))
    {v : WeylGroup Tag.D4} (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a)
    {g : ModGL TwistTag.D4.tag Ω} (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω (-1)) :
    twoPart (Nat.card (threeSixSingularR Ω K σ Fr (-1) v g)) = (ℓ ^ f) ^ 3 := by
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have hm : (ℓ ^ f) ^ 3 ≠ 0 := pow_ne_zero _ hq0
  have h2dvd : 2 ∣ (ℓ ^ f) ^ 2 := by
    rw [hℓ2, ← pow_mul]
    exact dvd_pow_self 2 (by omega : f * 2 ≠ 0)
  have hodd2 : Odd ((ℓ ^ f) ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow 2 (ℓ ^ f) (by positivity)) (even_iff_two_dvd.2 h2dvd)
      odd_one
  have h3dvd : 2 ∣ (ℓ ^ f) ^ 3 := by
    rw [hℓ2, ← pow_mul]
    exact dvd_pow_self 2 (by omega : f * 3 ≠ 0)
  have hodd3 : ¬ 2 ∣ (ℓ ^ f) ^ 3 + 1 :=
    Odd.not_two_dvd_nat (Even.add_one (even_iff_two_dvd.2 h3dvd))
  have hodd : ¬ 2 ∣ ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
    rw [Nat.Prime.dvd_mul Nat.prime_two]
    exact not_or.2 ⟨Odd.not_two_dvd_nat hodd2, hodd3⟩
  have hq3 : (ℓ ^ f) ^ 3 = 2 ^ (f * 3) := by rw [hℓ2, ← pow_mul]
  calc twoPart (Nat.card (threeSixSingularR Ω K σ Fr (-1) v g))
      = twoPart ((ℓ ^ f) ^ 3 * (((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1))) := by
        rw [natCard_threeSixSingularR_unitary hℓ hf hK hσ hFr ha hv hgG hFg, mul_assoc]
    _ = twoPart ((ℓ ^ f) ^ 3) := twoPart_mul_odd hm hodd
    _ = (ℓ ^ f) ^ 3 := by rw [hq3, twoPart_two_pow]

theorem mem_threeSixSingularR_of_pow_two_pow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ = 2)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ε : ℤ}
    {g : ModGL TwistTag.D4.tag Ω} (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε)
    {a : Fin TwistTag.D4.tag.rank → Ωˣ}
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3) {v : WeylGroup Tag.D4}
    (hSig : rootCharKernel a = (fun α => v • α) '' d4A2Sigma)
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹)
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hy : y ∈ Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    {k : ℕ} (hk : y ^ (2 ^ k) = 1) :
    y ∈ threeSixSingularR Ω K σ Fr ε v g := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hq0)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hchar : CharP Ω ℓ := charP_of_card_cube (K := K) hℓ hf hK
  haveI : CharP Ω 2 := hℓ2 ▸ hchar
  have hrange := range_threeSixEmb hℓ hf hK hσ Fr hFr
  have hD := centralizer_eq_comap (K := K) (σ := σ) hrange hgG hFg hx
  have hR := threeSixSingularR_eq_comap (K := K) (σ := σ) hrange hgG hFg (v := v)
  rw [hD, Subgroup.mem_comap] at hy
  have hy2 : threeSixEmb' Ω K σ g y ^ (2 ^ k) = 1 := by
    rw [← map_pow, hk, map_one]
  have hQ := mem_d4A2Qv_of_pow_two_pow (L := Ω) hord hSig hy hy2
  rw [hR, Subgroup.mem_comap]
  exact hQ

theorem twoPart_centralizer_threeA_le {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ = 2) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (g : ModGL TwistTag.D4.tag Ω) (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω (-1)) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr (-1))
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3) (v : WeylGroup Tag.D4)
    (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) :
    twoPart (Nat.card (Subgroup.centralizer
      ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) ≤ (ℓ ^ f) ^ 3 := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hq0)
  have hRtwo : twoPart (Nat.card (threeSixSingularR Ω K σ Fr (-1) v g)) = (ℓ ^ f) ^ 3 :=
    twoPart_natCard_threeSixSingularR hℓ hℓ2 hf hK hσ hFr ha hv hgG hFg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    with hC
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥C) := Sylow.nonempty
  let S' : Subgroup ↥C := S
  have hSyl : IsPGroup 2 S' := S.isPGroup'
  have hScard : Nat.card ↥S' = twoPart (Nat.card ↥C) := Sylow.card_eq_multiplicity S
  have hSR : S'.map C.subtype ≤ threeSixSingularR Ω K σ Fr (-1) v g := by
    rintro u hu
    rw [Subgroup.mem_map] at hu
    obtain ⟨s, hs, rfl⟩ := hu
    obtain ⟨k, hk⟩ := hSyl.exists_card_eq
    have hdiv : orderOf (⟨s, hs⟩ : ↥S') ∣ 2 ^ k := by
      rw [← hk]
      exact orderOf_dvd_natCard _
    have hord0 : orderOf (⟨s, hs⟩ : ↥S') = orderOf s := by
      rw [← Subgroup.orderOf_coe (a := (⟨s, hs⟩ : ↥S'))]
    have h0 : s ^ (2 ^ k) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← hord0]
      exact hdiv
    have hsk : (C.subtype s) ^ (2 ^ k) = 1 := by rw [← map_pow, h0, map_one]
    exact mem_threeSixSingularR_of_pow_two_pow hℓ hℓ2 hf hK hσ hFr hgG hFg
      hord hv.symm hx s.2 hsk
  have hUle : Nat.card ↥S' ≤ twoPart (Nat.card (threeSixSingularR Ω K σ Fr (-1) v g)) := by
    have hcard : Nat.card ↥S' = Nat.card ↥(S'.map C.subtype) :=
      (Subgroup.card_map_of_injective C.subtype_injective).symm
    rw [hcard]
    exact natCard_le_twoPart_of_le_of_isPGroup hSR (IsPGroup.map hSyl C.subtype)
  calc twoPart (Nat.card ↥C) = Nat.card ↥S' := hScard.symm
    _ ≤ twoPart (Nat.card (threeSixSingularR Ω K σ Fr (-1) v g)) := hUle
    _ = (ℓ ^ f) ^ 3 := hRtwo

theorem exists_threeA_model_data {K : Type} [Field K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP (AlgebraicClosure K) ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hq : ℓ ^ f % 3 = 2)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    ∃ (g k : ModGL TwistTag.D4.tag (AlgebraicClosure K))
      (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      g ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      trialityFrob (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f) g =
        g * threeSixN (AlgebraicClosure K) (-1) ∧
      threeSixEmb K (AlgebraicClosure K) σ x =
        g * rootDiagUnit TwistTag.D4.tag (tup ζ gT) * g⁻¹ ∧
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      threeSixEmb K (AlgebraicClosure K) σ x =
        k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  have hqε : ((ℓ ^ f : ℕ) : ZMod 3) = -1 := by
    rw [← ZMod.natCast_mod, hq]
    decide
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure K) ℓ f c = c ^ (ℓ ^ f) :=
    fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g, hgG, hFg⟩ := CFSG.RankThree.PartOne.KGD.lang_conjugator_D4 (K := K) (ℓ := ℓ) hf
    (AlgebraicClosure K) (threeSixN (AlgebraicClosure K) (-1))
    (threeSixN_mem_adjointGroup (L := AlgebraicClosure K) (Or.inr rfl))
  have ha : rootDiagUnit TwistTag.D4.tag (tup ζ gT) ∈
      threeSixTorus (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f) (-1) :=
    mem_threeSixTorus_tup_gT (Fr := iterateFrobenius (AlgebraicClosure K) ℓ f) hFr (Or.inr rfl)
      hqε hζ3
  obtain ⟨x, hx⟩ := exists_threeSixEmb_eq_conj hℓp hf hK hσ hFr hgG hFg ha
  have hd : rootDiagUnit TwistTag.D4.tag (tup ζ gT) =
      (canonicalRep (coxeterSystem TwistTag.D4.tag) (AlgebraicClosure K)
        ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) *
          canonicalRep (coxeterSystem TwistTag.D4.tag) (AlgebraicClosure K)
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]) := by
    rw [rootDiagUnit_tup_eq_conj hζ3 [3, 2, 1, 0, 2, 3] gT,
      show wordExp [3, 2, 1, 0, 2, 3] gT = gA by decide]
  refine ⟨g, g * (canonicalRep (coxeterSystem TwistTag.D4.tag) (AlgebraicClosure K)
      ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹, x, hgG, hFg, hx,
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ _ _)), ?_⟩
  rw [hx, hd]
  group

theorem k148RepA_of_odd {f : ℕ}
    (hf : 1 ≤ f) (hodd : f % 2 = 1) : K148RepA f := by
  intro K _ _ σ hK hσ z hzS hz3 hz1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = 2 ^ (f * 3) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h3L : (3 : AlgebraicClosure K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure K) 2] at h'
    norm_num at h'
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_units_orderOf_three
    (AlgebraicClosure K) h3L
  have hq : 2 ^ f % 3 = 2 := two_pow_mod_three_of_odd hodd
  obtain ⟨g, k, x, hgG, hFg, hx, hk, hxk⟩ :=
    exists_threeA_model_data (ℓ := 2) hf hK hσ hq hζ
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  have hqε : ((2 ^ f : ℕ) : ZMod 3) = -1 := by
    rw [← ZMod.natCast_mod, hq]
    decide
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure K) 2 f c = c ^ 2 ^ f :=
    fun c => iterateFrobenius_def 2 f c
  have ha : rootDiagUnit TwistTag.D4.tag (tup ζ gT) ∈
      threeSixTorus (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) 2 f) (-1) :=
    mem_threeSixTorus_tup_gT (Fr := iterateFrobenius (AlgebraicClosure K) 2 f) hFr (Or.inr rfl)
      hqε hζ3
  have hord : orderOf (rootDiagUnit TwistTag.D4.tag (tup ζ gT)) = 3 :=
    orderOf_rootDiagUnit_tup_gT hζ
  have hv : (fun α => vT • α) '' d4A2Sigma = survivingRoots (tup ζ gT) :=
    survivingRoots_tup_gT hζ
  have hbound : twoPart (Nat.card (Subgroup.centralizer
      ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) ≤ (2 ^ f) ^ 3 :=
    twoPart_centralizer_threeA_le Nat.prime_two rfl hf K hK σ hσ (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 f) hFr g hgG hFg (tup ζ gT) ha hord vT hv x hx
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have h := CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using h
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hf hK hσ (isPointIrreducible_gA hζ) hk' hk hzk hxk
  have hconj := natCard_centralizer_conj c z
  rw [hc] at hconj
  rw [← hconj]
  exact hbound

theorem k148InnerCentFact_holds :
    K148InnerCentFact :=
  k148InnerCentFact_of_repA fun f hf hodd => k148RepA_of_odd hf hodd

end Certs

end CFSG.LocalAnalysis.GLTheoremA.K148Inner

end
