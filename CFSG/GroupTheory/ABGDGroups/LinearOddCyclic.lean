module

public import Mathlib
public import CFSG.GroupTheory.ABGDGroups.LinearASeven
public import CFSG.GroupTheory.ABGDGroups.LinearOddSubgroups
public import CFSG.GroupTheory.ABGDGroups.LinearQuotient
public import CFSG.GroupTheory.QuasiDihedralFusion.Quotient
public import CFSG.GroupTheory.QuasiDihedralFusion.Structure
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeNormalExtension
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public noncomputable section

namespace CFSG.ABGDGroups

open CFSG.QuasiDihedralFusion
open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower pGammaL2PSLRange
  pGammaL2PGLRange mem_pGammaL2PSLRange_iff a7t a7u a7a a7v a7s a7S a7U a7V)
open scoped commutatorElement

universe u

section General

variable {G G' : Type*} [Group G] [Group G']

theorem isKleinFour_map_of_inf_ker_eq_bot (f : G →* G') {V : Subgroup G} (hV : IsKleinFour V)
    (h : V ⊓ f.ker = ⊥) : IsKleinFour (V.map f) := by
  have hinj : Function.Injective (f.comp V.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ V ⊓ f.ker := ⟨x.2, hx⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  have hrange : (f.comp V.subtype).range = V.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : V ≃* V.map f := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact ⟨by rw [← Nat.card_congr e.toEquiv]; exact hV.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact hV.exponent_two⟩

theorem isPGroup_two_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) : IsPGroup 2 V :=
  IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)

theorem exists_zpow_mem_of_isCyclic_map {N : Subgroup G} [N.Normal] {K : Subgroup G}
    (h : IsCyclic (K.map (QuotientGroup.mk' N))) :
    ∃ g ∈ K, ∀ k ∈ K, ∃ n : ℤ, k⁻¹ * g ^ n ∈ N := by
  obtain ⟨⟨_, ⟨g, hg, rfl⟩⟩, hgen⟩ := h.exists_generator
  refine ⟨g, hg, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := hgen ⟨QuotientGroup.mk' N k, ⟨k, hk, rfl⟩⟩
  refine ⟨n, ?_⟩
  have hn' := congrArg Subtype.val hn
  simp only [SubgroupClass.coe_zpow, QuotientGroup.mk'_apply] at hn'
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hn'
  have h := N.inv_mem hn'
  rwa [mul_inv_rev, inv_inv] at h

theorem isCyclic_map_of_exists_zpow_mem {N : Subgroup G} [N.Normal] {K : Subgroup G}
    (h : ∃ g ∈ K, ∀ k ∈ K, ∃ n : ℤ, k⁻¹ * g ^ n ∈ N) :
    IsCyclic (K.map (QuotientGroup.mk' N)) := by
  obtain ⟨g, hg, hgen⟩ := h
  refine ⟨⟨⟨QuotientGroup.mk' N g, g, hg, rfl⟩, ?_⟩⟩
  rintro ⟨_, k, hk, rfl⟩
  obtain ⟨n, hn⟩ := hgen k hk
  refine ⟨n, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_zpow, QuotientGroup.mk'_apply]
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
  have h' := N.inv_mem hn
  rwa [mul_inv_rev, inv_inv] at h'

end General

section ASeven

local notation "A₇" => alternatingGroup (Fin 7)

private def a7g₁ : A₇ := ⟨Equiv.swap (2 : Fin 7) 4 * Equiv.swap 3 5, by simp [Equiv.Perm.sign_mul]⟩

private def a7g₂ : A₇ := ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap 1 5, by simp [Equiv.Perm.sign_mul]⟩

private def a7c : Fin 3 → A₇ := ![a7a, a7g₁ * a7a * a7g₁⁻¹, a7g₂ * a7a * a7g₂⁻¹]

private theorem pow_three_eq_one_of_odd {M : Type*} [Monoid M] {x : M} (hx : Odd (orderOf x))
    (h12 : x ^ 12 = 1) : x ^ 3 = 1 := by
  have hdvd : orderOf x ∣ 3 * 4 := orderOf_dvd_of_pow_eq_one h12
  have hcop : Nat.Coprime (orderOf x) 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_right.mpr hx).pow_right 2
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)

private theorem a7S_involution_cases {v : A₇} (hv : v ∈ a7S) (hv1 : v ≠ 1) (hv2 : v ^ 2 = 1) :
    v = a7t ∨ v = a7u ∨ v = a7t * a7u ∨ v = a7g₁ * a7t * a7g₁⁻¹ ∨ v = a7g₂ * a7t * a7g₂⁻¹ := by
  change v = 1 ∨ v = a7v ∨ v = a7v ^ 2 ∨ v = a7v ^ 3 ∨ v = a7s ∨ v = a7s * a7v ∨
    v = a7s * a7v ^ 2 ∨ v = a7s * a7v ^ 3 at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hv1
  · exact absurd hv2 (by decide +kernel)
  · left; decide +kernel
  · exact absurd hv2 (by decide +kernel)
  · right; right; right; left; decide +kernel
  · right; left; decide +kernel
  · right; right; right; right; decide +kernel
  · right; right; left; decide +kernel

private theorem eq_of_commute_conj_a7t {g x : A₇} (hx : Odd (orderOf x))
    (hc : x * (g * a7t * g⁻¹) = g * a7t * g⁻¹ * x) :
    x = 1 ∨ x = g * a7a * g⁻¹ ∨ x = (g * a7a * g⁻¹) ^ 2 := by
  set y := g⁻¹ * x * g with hy
  have hxy : x = g * y * g⁻¹ := by rw [hy]; group
  have hyc : y * a7t = a7t * y := by
    rw [hy]
    calc g⁻¹ * x * g * a7t = g⁻¹ * (x * (g * a7t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a7t * g⁻¹ * x) * g := by rw [hc]
      _ = a7t * (g⁻¹ * x * g) := by group
  have hyo : orderOf y = orderOf x := by
    rw [hy, show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, MulEquiv.orderOf_eq]
  obtain ⟨h12, h3⟩ := (aSeven_centralizer_involution_a7V_certificate y).1 hyc
  rcases h3 (pow_three_eq_one_of_odd (hyo ▸ hx) h12) with h | h | h
  · left
    rw [hxy, h]
    group
  · right; left
    rw [hxy, h]
  · right; right
    rw [hxy, h, conj_pow]

private theorem exists_index_of_involution {v : A₇} (hv : v ∈ a7S) (hv1 : v ≠ 1)
    (hv2 : v ^ 2 = 1) :
    ∃ i : Fin 3, ∀ x : A₇, x * v = v * x → Odd (orderOf x) →
      x = 1 ∨ x = a7c i ∨ x = a7c i ^ 2 := by
  have hcert := aSeven_centralizer_involution_a7V_certificate
  rcases a7S_involution_cases hv hv1 hv2 with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, fun x hc hx => ((hcert x).1 hc).2
      (pow_three_eq_one_of_odd hx ((hcert x).1 hc).1)⟩
  · exact ⟨0, fun x hc hx => ((hcert x).2.1 hc).2
      (pow_three_eq_one_of_odd hx ((hcert x).2.1 hc).1)⟩
  · exact ⟨0, fun x hc hx => ((hcert x).2.2 hc).2
      (pow_three_eq_one_of_odd hx ((hcert x).2.2 hc).1)⟩
  · exact ⟨1, fun x hc hx => eq_of_commute_conj_a7t hx hc⟩
  · exact ⟨2, fun x hc hx => eq_of_commute_conj_a7t hx hc⟩

private theorem a7c_pair_certificate : ∀ i j : Fin 3, i ≠ j →
    (a7c i * (a7c j * a7c i * (a7c j)⁻¹)) ^ 2 = 1 ∧ a7c i * (a7c j * a7c i * (a7c j)⁻¹) ≠ 1 := by
  decide +kernel

private theorem a7c_pow_four : ∀ i : Fin 3, a7c i ^ 4 = a7c i := by
  decide +kernel

theorem aSeven_isCyclic_of_odd_of_kleinFour_le_a7S {T K : Subgroup A₇} (hT : IsKleinFour T)
    (hTS : T ≤ a7S) (hK : Odd (Nat.card K)) (hKT : T ≤ Subgroup.normalizer (K : Set A₇)) :
    IsCyclic K := by
  classical
  have hpow : ∀ v : T, v ^ 2 = 1 := fun v => by
    have h := Monoid.pow_exponent_eq_one v
    rwa [hT.exponent_two] at h
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two T K hpow hT.card_four
    (fun h => (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr h)) hKT
  have hidx : ∀ v : T, v ≠ 1 → ∃ i : Fin 3, ∀ x : A₇, x * v = v * x → Odd (orderOf x) →
      x = 1 ∨ x = a7c i ∨ x = a7c i ^ 2 := fun v hv =>
    exists_index_of_involution (hTS v.2) (fun h => hv (Subtype.ext h))
      (by simpa using congrArg Subtype.val (hpow v))
  have hmem : ∀ (i : Fin 3) (x : A₇), x ∈ K → x ≠ 1 → (x = 1 ∨ x = a7c i ∨ x = a7c i ^ 2) →
      a7c i ∈ K := by
    rintro i x hxK hx1 (rfl | rfl | rfl)
    · exact absurd rfl hx1
    · exact hxK
    · rw [← a7c_pow_four i, show 4 = 2 * 2 by norm_num, pow_mul]
      exact K.pow_mem hxK 2
  have hpair : ∀ i j : Fin 3, i ≠ j → a7c i ∈ K → a7c j ∈ K → False := by
    intro i j hij hi hj
    obtain ⟨h2, h1⟩ := a7c_pair_certificate i j hij
    have hw : a7c i * (a7c j * a7c i * (a7c j)⁻¹) ∈ K :=
      K.mul_mem hi (K.mul_mem (K.mul_mem hj hi) (K.inv_mem hj))
    have hord : orderOf (a7c i * (a7c j * a7c i * (a7c j)⁻¹)) = 2 := orderOf_eq_prime h2 h1
    have h2K := Subgroup.orderOf_dvd_natCard K hw
    rw [hord] at h2K
    exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr h2K)
  by_cases hne : ∃ v : T, v ≠ 1 ∧ K ⊓ Subgroup.centralizer ({(v : A₇)} : Set A₇) ≠ ⊥
  · obtain ⟨v, hv1, hvne⟩ := hne
    obtain ⟨i, hi⟩ := hidx v hv1
    obtain ⟨x, ⟨hxK, hxC⟩, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hvne
    have hciK : a7c i ∈ K := hmem i x hxK hx1
      (hi x (Subgroup.mem_centralizer_singleton_iff.mp hxC)
        (hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hxK)))
    have hle : K ≤ Subgroup.zpowers (a7c i) := by
      refine hgen.le.trans (iSup₂_le fun w hw => ?_)
      rintro y ⟨hyK, hyC⟩
      obtain ⟨j, hj⟩ := hidx w hw
      have hy := hj y (Subgroup.mem_centralizer_singleton_iff.mp hyC)
        (hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hyK))
      by_cases hy1 : y = 1
      · rw [hy1]
        exact Subgroup.one_mem _
      by_cases hij : i = j
      · subst hij
        rcases hy with h | h | h
        · rw [h]; exact Subgroup.one_mem _
        · rw [h]; exact Subgroup.mem_zpowers _
        · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
      · exact (hpair i j hij hciK (hmem j y hyK hy1 hy)).elim
    exact Subgroup.isCyclic_of_le hle
  · push Not at hne
    have hbot : K = ⊥ := by
      rw [hgen]
      exact iSup₂_eq_bot.mpr hne
    rw [hbot]
    infer_instance

theorem aSeven_isCyclic_of_odd_of_kleinFour
    {H : Type} [Group H] [Finite H] (e : H ≃* A₇)
    {T K : Subgroup H} (hT : IsKleinFour T) (hK : Odd (Nat.card K))
    (hKT : T ≤ Subgroup.normalizer (K : Set H)) : IsCyclic K := by
  obtain ⟨S, hTS⟩ := (isPGroup_two_of_isKleinFour hT).exists_le_sylow
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_aSeven_map_sylow_eq e S
  have hT' : IsKleinFour (T.map φ.toMonoidHom) :=
    isKleinFour_map_of_inf_ker_eq_bot _ hT (by
      rw [eq_bot_iff]
      rintro x ⟨-, hx⟩
      exact Subgroup.mem_bot.mpr (φ.injective (hx.trans (map_one φ).symm)))
  have hcyc := aSeven_isCyclic_of_odd_of_kleinFour_le_a7S hT'
    (hφ ▸ Subgroup.map_mono hTS)
    (by rwa [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective])
    ((Subgroup.map_mono hKT).trans (Subgroup.le_normalizer_map _))
  exact (K.equivMapOfInjective φ.toMonoidHom φ.injective).isCyclic.mpr hcyc

end ASeven

section Linear

variable {F : Type} [Field F] [Finite F]

theorem sq_mem_pGammaL2PSLRange (hF : IsOddPrimePower (Nat.card F)) {x : PGammaL2 F}
    (hx : x.right ^ 2 = 1) : x ^ 2 ∈ pGammaL2PSLRange F := by
  rw [pGammaL2PSLRange_eq_inf_ker hF, Subgroup.mem_inf, MonoidHom.mem_ker, map_pow,
    squareClass_sq]
  refine ⟨?_, rfl⟩
  rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_pow,
    SemidirectProduct.rightHom_eq_right, hx]

theorem IsStandardLayer.right_sq {M : Subgroup (PGammaL2 F)} (hM : IsStandardLayer M)
    {x : PGammaL2 F} (hx : x ∈ M) : x.right ^ 2 = 1 := by
  rcases hM with rfl | rfl | rfl
  · obtain ⟨y, rfl⟩ := hx
    simp
  · obtain ⟨y, rfl⟩ := hx
    simp
  · exact hx.1

theorem IsStandardLayer.mem_pGLRange_of_orderOf_eq_two (hF : IsOddPrimePower (Nat.card F))
    {M : Subgroup (PGammaL2 F)} (hM : IsStandardLayer M) {x : PGammaL2 F} (hx : x ∈ M)
    (h2 : orderOf x = 2) : x ∈ pGammaL2PGLRange F := by
  rcases hM with rfl | rfl | rfl
  · exact pGammaL2PSLRange_le_pGLRange hx
  · exact hx
  · exact pGammaL2PSLRange_le_pGLRange (mem_pGammaL2PSLRange_of_mem_pGLStar hF hx h2)

omit [Finite F] in
private theorem nonempty_comap_inl_mulEquiv {A : Subgroup (PGammaL2 F)}
    (hA : A ≤ pGammaL2PGLRange F) :
    Nonempty (A.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) ≃* A) :=
  ⟨((A.comap SemidirectProduct.inl).equivMapOfInjective _ SemidirectProduct.inl_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hA))⟩

namespace IsLinearDecomposition

variable {H : Type} [Group H] [Finite H] {ι : H →* PGammaL2 F} {L E : Subgroup H}
  {S : Sylow 2 H}

theorem isCyclic_of_commutator_eq
    (hd : IsLinearDecomposition ι L E S) {T : Subgroup H}
    (hT : IsKleinFour T) {K : Subgroup H} (hKT : T ≤ Subgroup.normalizer (K : Set H))
    (hK : Odd (Nat.card K)) (hTK : ⁅T, K⁆ = K) : IsCyclic K := by
  have hF := hd.isOddPrimePower_card
  have hL := hd.normal
  have hTL : T ≤ L := by
    obtain ⟨P, hTP⟩ := (isPGroup_two_of_isKleinFour hT).exists_le_sylow
    exact hTP.trans (hd.sylow_le P)
  have hKL : K ≤ L := by
    rw [← hTK, Subgroup.commutator_le]
    intro t ht k _
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine L.mul_mem (hTL ht) ?_
    rw [← mul_assoc]
    exact hL.conj_mem _ (L.inv_mem (hTL ht)) k
  have hKL₀ : K.map ι ≤ pGammaL2PSLRange F := by
    rintro _ ⟨k, hk, rfl⟩
    have hsq : ι k ^ 2 ∈ pGammaL2PSLRange F :=
      sq_mem_pGammaL2PSLRange hF (hd.isStandardLayer.right_sq ⟨k, hKL hk, rfl⟩)
    obtain ⟨j, hj⟩ := hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hk)
    have hk' : ι k = (ι k ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = orderOf k + 1 by omega, pow_succ, ← map_pow,
        pow_orderOf_eq_one, map_one, one_mul]
    rw [hk']
    exact Subgroup.pow_mem _ hsq _
  have hTPGL : T.map ι ≤ pGammaL2PGLRange F := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases ht1 : t = 1
    · rw [ht1, map_one]
      exact Subgroup.one_mem _
    have h2 : orderOf t = 2 := by
      have h := Monoid.pow_exponent_eq_one (⟨t, ht⟩ : T)
      rw [hT.exponent_two] at h
      exact orderOf_eq_prime (by simpa using congrArg Subtype.val h) ht1
    exact hd.isStandardLayer.mem_pGLRange_of_orderOf_eq_two hF ⟨t, hTL ht, rfl⟩
      (by rw [orderOf_injective ι hd.injective, h2])
  set K₁ := (K.map ι).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  set T₁ := (T.map ι).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hKPGL : K.map ι ≤ pGammaL2PGLRange F := hKL₀.trans pGammaL2PSLRange_le_pGLRange
  obtain ⟨eK⟩ := nonempty_comap_inl_mulEquiv hKPGL
  obtain ⟨eT⟩ := nonempty_comap_inl_mulEquiv hTPGL
  let eK' : K ≃* K.map ι := K.equivMapOfInjective ι hd.injective
  let eT' : T ≃* T.map ι := T.equivMapOfInjective ι hd.injective
  have hK₁J : K₁ ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    intro x hx
    obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff F _).mp (hKL₀ hx)
    exact ⟨y, SemidirectProduct.inl_injective hy⟩
  have hK₁ : Odd (Nat.card K₁) := by
    rwa [Nat.card_congr eK.toEquiv, ← Nat.card_congr eK'.toEquiv]
  have hT₁ : IsKleinFour T₁ := by
    refine ⟨?_, ?_⟩
    · rw [Nat.card_congr eT.toEquiv, ← Nat.card_congr eT'.toEquiv]
      exact hT.card_four
    · rw [Monoid.exponent_eq_of_mulEquiv eT, ← Monoid.exponent_eq_of_mulEquiv eT']
      exact hT.exponent_two
  have hT₁K : T₁ ≤ Subgroup.normalizer (K₁ : Set (PGL2 F)) := by
    intro t ht
    apply Subgroup.mem_normalizer_fintype
    intro k hk
    have hN := Subgroup.le_normalizer_map ι
      (Subgroup.map_mono hKT (show SemidirectProduct.inl t ∈ T.map ι from ht))
    change SemidirectProduct.inl (t * k * t⁻¹) ∈ K.map ι
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hN _).mp hk
  have hcyc := pgl2_isCyclic_of_odd_of_kleinFour_le_normalizer hF hK₁J hK₁ hT₁ hT₁K
  exact (eK'.trans eK.symm).isCyclic.mpr hcyc

end IsLinearDecomposition

end Linear

section Main

variable {H : Type} [Group H] [Finite H]

theorem isCyclic_of_commutator_eq_of_oddCore_eq_bot
    (hH : IsDGroup H)
    (hO : CFSG.oddCore H = ⊥) {T : Subgroup H} (hT : IsKleinFour T) {K : Subgroup H}
    (hKT : T ≤ Subgroup.normalizer (K : Set H)) (hK : Odd (Nat.card K)) (hTK : ⁅T, K⁆ = K) :
    IsCyclic K := by
  by_cases hW : ∃ n, HasWreathedSylow H n
  · obtain ⟨n, hn⟩ := hW
    rcases hH with ⟨hD, -⟩ | ⟨K', hK'⟩
    · exact (not_hasWreathedSylow_and_dihedral hn hD).elim
    · have hle := wreathed_dGroup_odd_four_invariant_le_oddCore hK' hn hT hK hKT
      rw [hO, le_bot_iff] at hle
      rw [hle]
      infer_instance
  · rcases aSeven_or_linearDecomposition hH hO hW with he | hlin
    · obtain ⟨e⟩ := he
      exact aSeven_isCyclic_of_odd_of_kleinFour e hT hK hKT
    · obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
      obtain ⟨F, _, _, ι, L, E, hd⟩ := hlin S
      exact hd.isCyclic_of_commutator_eq hT hKT hK hTK

theorem isCyclic_map_oddCore_of_commutator_eq
    (hH : IsDGroup H) {T : Subgroup H}
    (hT : IsKleinFour T) {K : Subgroup H} (hKT : T ≤ Subgroup.normalizer (K : Set H))
    (hK : Odd (Nat.card K)) (hTK : ⁅T, K⁆ = K) :
    IsCyclic (K.map (QuotientGroup.mk' (CFSG.oddCore H))) := by
  set π := QuotientGroup.mk' (CFSG.oddCore H)
  have hTπ : T ⊓ π.ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [hT.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_left.mpr (odd_card_oddCore H)).pow_left 2
  refine isCyclic_of_commutator_eq_of_oddCore_eq_bot (isDGroup_quotient_oddCore hH)
    (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot H)
    (isKleinFour_map_of_inf_ker_eq_bot π hT hTπ)
    ((Subgroup.map_mono hKT).trans (Subgroup.le_normalizer_map π))
    (hK.of_dvd_nat (Subgroup.card_map_dvd K π)) ?_
  rw [← Subgroup.map_commutator, hTK]

end Main

section Universe

theorem isCyclic_map_oddCore_of_commutator_eq_univ
    {X : Type u} [Group X] [Finite X]
    (hX : IsDGroup X) {T : Subgroup X} (hT : IsKleinFour T) {K : Subgroup X}
    (hKT : T ≤ Subgroup.normalizer (K : Set X)) (hK : Odd (Nat.card K)) (hTK : ⁅T, K⁆ = K) :
    IsCyclic (K.map (QuotientGroup.mk' (CFSG.oddCore X))) := by
  let e : Shrink.{0} X ≃* X := Shrink.mulEquiv
  have hker : Odd (Nat.card e.toMonoidHom.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective, Subgroup.card_bot]
    exact odd_one
  have hX₀ : IsDGroup (Shrink.{0} X) :=
    (isDGroup_iff_of_oddKernel e.toMonoidHom e.surjective hker).mp hX
  have hT₀ : IsKleinFour (T.map e.symm.toMonoidHom) :=
    isKleinFour_map_of_inf_ker_eq_bot _ hT (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.symm.injective, inf_bot_eq])
  have hcyc := isCyclic_map_oddCore_of_commutator_eq hX₀ hT₀
    ((Subgroup.map_mono hKT).trans (Subgroup.le_normalizer_map _))
    (by rwa [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective])
    (by rw [← Subgroup.map_commutator, hTK])
  obtain ⟨g₀, hg₀, hgen₀⟩ := exists_zpow_mem_of_isCyclic_map hcyc
  have hO := CFSG.LyonsUnitaryFour.oddCore_map_mulEquiv e
  apply isCyclic_map_of_exists_zpow_mem
  obtain ⟨g, hg, rfl⟩ := hg₀
  refine ⟨g, hg, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := hgen₀ (e.symm k) ⟨k, hk, rfl⟩
  refine ⟨n, ?_⟩
  rw [← hO]
  refine ⟨_, hn, ?_⟩
  simp

theorem exists_zpow_mem_oddCore_map_of_commutator_eq
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsDGroup H) {T : Subgroup G} (hTH : T ≤ H)
    (hT : IsKleinFour (T.subgroupOf H)) {F : Subgroup G} (hFH : F ≤ H)
    (hF : Odd (Nat.card F)) (hTF : T ≤ Subgroup.normalizer (F : Set G)) (hFT : ⁅F, T⁆ = F) :
    ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ (CFSG.oddCore H).map H.subtype := by
  set T' := T.subgroupOf H
  set F' := F.subgroupOf H
  have hF' : Odd (Nat.card F') := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFH).toEquiv]
  have hTF' : T' ≤ Subgroup.normalizer (F' : Set H) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hTF (Subgroup.mem_subgroupOf.mp ht))) x
  have hcomm : ⁅T', F'⁆ = F' := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTH, inf_eq_left.mpr hFH,
      Subgroup.commutator_comm, hFT]
  obtain ⟨g, hg, hgen⟩ := exists_zpow_mem_of_isCyclic_map
    (isCyclic_map_oddCore_of_commutator_eq_univ hH hT hTF' hF' hcomm)
  refine ⟨g, hg, fun f hf => ?_⟩
  obtain ⟨k, hk⟩ := hgen ⟨f, hFH hf⟩ hf
  exact ⟨k, ⟨_, hk, by simp⟩⟩

end Universe

end CFSG.ABGDGroups
