module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLemma228
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix
public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalOrbits

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type} [Group G]

theorem le_pRank_of_isElemTwo [Finite G] {H E : Subgroup G} (hEH : E ≤ H) (hE : IsElemTwo E)
    {k : ℕ} (hk : Nat.card E = 2 ^ k) : k ≤ pRank 2 ↥H := by
  have hEA : IsElementaryAbelian 2 ↥(E.subgroupOf H) :=
    { is_comm := ⟨fun u v => Subtype.ext (Subtype.ext
        (hE.1 _ (mem_subgroupOf.mp u.2) _ (mem_subgroupOf.mp v.2)))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u =>
        Subtype.ext (Subtype.ext (by
          show ((u : H) : G) ^ 2 = 1
          rw [pow_two]
          exact hE.2 _ (mem_subgroupOf.mp u.2))) }
  have hcard : Nat.card ↥(E.subgroupOf H) = 2 ^ k := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv, hk]
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E.subgroupOf H, hEA, hcard⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := card_le_card_group B

theorem isSylowTwoIn_inf [Finite G] {S J : Subgroup G}
    (hS : IsSylowTwoIn S (normalizer (J : Set G))) : IsSylowTwoIn (S ⊓ J) J := by
  obtain ⟨hSN, P, hP⟩ := hS
  obtain ⟨T, hT⟩ := RankProjectiveAction.exists_sylow_inf_of_le_normalizer hSN ⟨P, hP⟩
    le_normalizer le_rfl
  exact ⟨inf_le_right, T, hT⟩

theorem not_mem_coreActionKernel [Finite G] {a x : G} {J : Subgroup G}
    (h : GSUnbalancingTriple a x J) : x ∉ coreActionKernel J := by
  intro hx
  have hq := GSLit.isQuasisimple_of_gsUnbalancingTriple h
  have hle : J ≤ (pPrimeCore 2 J).map J.subtype := by
    calc J = closure {y | ∃ j ∈ J, y = j⁻¹ * x⁻¹ * j * x} := h.2.2.2.2.2.1.symm
      _ ≤ _ := by
        rw [closure_le]
        rintro y ⟨j, hj, rfl⟩
        exact (mem_coreActionKernel.mp hx).2 j hj
  have hall : ∀ u v : J ⧸ pPrimeCore 2 J, u = v := by
    intro u v
    induction u using QuotientGroup.induction_on with
    | H u =>
    induction v using QuotientGroup.induction_on with
    | H v =>
    rw [QuotientGroup.eq]
    obtain ⟨k, hk, hkj⟩ := hle (u⁻¹ * v).2
    rwa [show k = u⁻¹ * v from Subtype.ext hkj] at hk
  obtain ⟨-, -, a', b', hab⟩ := hq
  apply hab
  induction a' using QuotientGroup.induction_on with
  | H a' =>
  induction b' using QuotientGroup.induction_on with
  | H b' =>
  rw [hall a' b']

theorem sixtyFour_le_card [Finite G] {J P : Subgroup G}
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hP : IsSylowTwoIn P J) : 64 ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPJ, T, hT⟩ := hP
  obtain ⟨e⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hL34
  have hcardQ : Nat.card (J ⧸ Open.fusionZStar J) = 20160 := by
    rw [Nat.card_congr e.toEquiv, PSL3Four.card_S]
  let T' := T.mapSurjective (QuotientGroup.mk'_surjective (Open.fusionZStar ↥J))
  have h1 : Nat.card T' = 64 := by
    rw [Sylow.card_eq_multiplicity, hcardQ,
      show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 315 by norm_num)]
  have h2 : Nat.card T' ≤ Nat.card T :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (H := (T : Subgroup ↥J))
      (QuotientGroup.mk' (Open.fusionZStar ↥J)))
  have h3 : Nat.card T = Nat.card P := by
    rw [hT]
    exact Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv
  omega

theorem not_le_coreActionKernel_self [Finite G] {C J : Subgroup G} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) : ¬ J ≤ coreActionKernel J := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J C hJC).mp hJ
  obtain ⟨-, -, a, b, hab⟩ := hq
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
  induction b using QuotientGroup.induction_on with
  | H b =>
  induction a using QuotientGroup.induction_on with
  | H u =>
  induction b using QuotientGroup.induction_on with
  | H v =>
  have hc : (QuotientGroup.mk u : J ⧸ pPrimeCore 2 J) * QuotientGroup.mk v =
      QuotientGroup.mk v * QuotientGroup.mk u := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 := (mem_coreActionKernel.mp (h u.2)).2 v v.2
    obtain ⟨w, hw, hwe⟩ := h1
    have : w = (u * v)⁻¹ * (v * u) := by
      apply Subtype.ext
      rw [show (w : G) = _ from hwe]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [← this]
  rw [← QuotientGroup.mk_mul, hc, QuotientGroup.mk_mul]

theorem conj_mem_oddIn {C : Subgroup G} {h d : G} (hh : h ∈ C) (hd : d ∈ oddIn C) :
    h * d * h⁻¹ ∈ oddIn C := by
  obtain ⟨d', hd', rfl⟩ := hd
  have hn : (pPrimeCore 2 ↥C).Normal := inferInstance
  exact ⟨⟨h, hh⟩ * d' * ⟨h, hh⟩⁻¹, hn.conj_mem d' hd' ⟨h, hh⟩, by simp⟩

theorem eq_of_le_oddIn_sup [Finite G] {C J K : Subgroup G} (hJC : J ≤ C) (hKC : K ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) (hK : IsPComponent 2 (K.subgroupOf C))
    (hle : J ≤ oddIn C ⊔ K) : J = K := by
  by_contra hne
  have hKk : K ≤ coreActionKernel J := GSThmB.B5a.le_coreActionKernel_of_ne hJC hKC hJ hK hne
  have hOk : oddIn C ≤ coreActionKernel J := by
    intro o ho
    have hoN : o ∈ normalizer (J : Set G) :=
      UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hJC hJ ho
    have hoC : o ∈ C := by
      obtain ⟨o', -, rfl⟩ := ho
      exact o'.2
    refine mem_coreActionKernel.mpr ⟨hoN, fun j hj => ?_⟩
    have hD : J ⊓ oddIn C ≤ (pPrimeCore 2 J).map J.subtype := by
      refine le_map_pPrimeCore inf_le_left (fun h hh d hd => mem_inf.mpr ⟨?_, ?_⟩) ?_
      · exact mul_mem (mul_mem hh (mem_inf.mp hd).1) (inv_mem hh)
      · exact conj_mem_oddIn (hJC hh) (mem_inf.mp hd).2
      · exact Odd.of_dvd_nat (odd_card_map_pPrimeCore C)
          (Subgroup.card_dvd_of_le inf_le_right)
    refine hD (mem_inf.mpr ⟨?_, ?_⟩)
    · have h1 : o⁻¹ * j * o ∈ J := by
        have := (mem_normalizer_iff.mp (inv_mem hoN) j).mp hj
        rwa [inv_inv] at this
      rw [show j⁻¹ * o⁻¹ * j * o = j⁻¹ * (o⁻¹ * j * o) by group]
      exact mul_mem (inv_mem hj) h1
    · rw [show j⁻¹ * o⁻¹ * j * o = (j⁻¹ * o⁻¹ * j⁻¹⁻¹) * o by group]
      exact mul_mem (conj_mem_oddIn (inv_mem (hJC hj)) (inv_mem ho)) ho
  exact not_le_coreActionKernel_self hJC hJ (hle.trans (sup_le hOk hKk))

theorem gsFixedLayer_eq_self [Finite G] {a : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G)))) : gsFixedLayer J a = J := by
  have hinf : J ⊓ centralizer ({a} : Set G) = J := inf_eq_left.mpr hJa
  unfold gsFixedLayer
  rw [hinf]
  exact pLayer_eq_self_of_isPComponent hJa hJ

theorem exists_conj_le_sylow [Finite G] {H : Subgroup G} (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) {V : Subgroup G} (hVH : V ≤ H) (hVp : IsPGroup 2 V) :
    ∃ h ∈ H, ∀ x ∈ V, h⁻¹ * x * h ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp' : IsPGroup 2 (V.subgroupOf H) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  obtain ⟨S, hS⟩ := hVp'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H (T.subtype hTH) S
  refine ⟨h, h.2, fun x hx => ?_⟩
  have hxS : (⟨x, hVH hx⟩ : H) ∈ (S : Subgroup H) := hS hx
  rw [← hh, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Sylow.coe_subtype,
    Subgroup.mem_subgroupOf] at hxS
  convert hxS using 1
  simp [MulAut.inv_def, MulAut.conj_symm_apply]

theorem centralizer_le_normalizer_of_solomon (hSol : SolomonFixedLayerStep) [Finite G]
    (hbase : L34BaseSetting G) {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hmax : GSWeakMaximalComponent J) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) :
    centralizer ({a} : Set G) ≤ normalizer (J : Set G) := by
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  haveI := hsimple
  intro c hc
  have htop : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup G) := eF.isSimpleGroup
  have hnF : ∃ u v : GeneralizedFitting.subgroup G, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnab
    exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hoF : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) := fun h => hUo (Or.inl h)
  have hca : c⁻¹ * a * c = a := by
    have := mem_centralizer_singleton_iff.mp hc
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  have hjc : ∀ j ∈ J, j * a = a * j := fun j hj => mem_centralizer_singleton_iff.mp (hJa hj)
  have haN : a ∈ normalizer (J : Set G) := by
    rw [mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      rwa [show a * j * a⁻¹ = j by rw [← hjc j hj]; group]
    · intro hj
      have h1 := hjc _ hj
      have h2 : j = a * j * a⁻¹ := mul_left_cancel (a := a) (by rw [← h1]; group)
      rwa [h2]
  have h1 := hSol G hsF hnF hoF hK a J ha hJa hJ hmax hL34 hbase c (by rw [hca])
    (by rw [hca]; exact haN)
    (by
      rw [hca]
      intro j hj
      rw [show j⁻¹ * a⁻¹ * j * a = 1 by rw [mul_assoc, hjc j hj]; group]
      exact one_mem _)
  rw [hca, gsFixedLayer_eq_self hJa hJ] at h1
  obtain ⟨hJcC, hJcp⟩ := GSThmB.OddQuot.isPComponent_conjugate_subgroupOf hc hJa hJ
  have heq : J = conjugate J c := eq_of_le_oddIn_sup hJa hJcC hJ hJcp h1
  exact UnbalancedLayer.mem_normalizer_of_conjugate_eq heq.symm

theorem map_conj_inf_centralizer {T : Subgroup G} {x s : G} (hs : s ∈ T) :
    (T ⊓ centralizer ({x} : Set G)).map (MulAut.conj s⁻¹).toMonoidHom =
      T ⊓ centralizer ({s⁻¹ * x * s} : Set G) := by
  ext y
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨z, ⟨hzT, hzx⟩, rfl⟩
    refine ⟨mul_mem (mul_mem (inv_mem hs) hzT) hs, ?_⟩
    calc s⁻¹ * z * s * (s⁻¹ * x * s) = s⁻¹ * (z * x) * s := by group
      _ = s⁻¹ * (x * z) * s := by rw [hzx]
      _ = s⁻¹ * x * s * (s⁻¹ * z * s) := by group
  · rintro ⟨hyT, hyx⟩
    refine ⟨s * y * s⁻¹, ⟨mul_mem (mul_mem hs hyT) (inv_mem hs), ?_⟩, by group⟩
    calc s * y * s⁻¹ * x = s * (y * (s⁻¹ * x * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * x * s) * y) * s⁻¹ := by rw [hyx]
      _ = x * (s * y * s⁻¹) := by group

noncomputable def infCentralizerConjEquiv {T : Subgroup G} {x s : G} (hs : s ∈ T) :
    ↥(T ⊓ centralizer ({x} : Set G)) ≃* ↥(T ⊓ centralizer ({s⁻¹ * x * s} : Set G)) :=
  ((T ⊓ centralizer ({x} : Set G)).equivMapOfInjective _ (MulAut.conj s⁻¹).injective).trans
    (MulEquiv.subgroupCongr (map_conj_inf_centralizer hs))

theorem card_inf_centralizer_conj [Finite G] {T : Subgroup G} {x s : G} (hs : s ∈ T) :
    Nat.card ↥(T ⊓ centralizer ({s⁻¹ * x * s} : Set G)) =
      Nat.card ↥(T ⊓ centralizer ({x} : Set G)) :=
  (Nat.card_congr (infCentralizerConjEquiv hs).toEquiv).symm

theorem exists_normalizer_conj_eq [Finite G] (T : Sylow 2 G) {a x : G}
    (haZ : ∀ s ∈ (T : Subgroup G), a * s = s * a) (hxT : x ∈ (T : Subgroup G))
    (hfus : ∀ y ∈ (T : Subgroup G), (∃ g : G, y = g⁻¹ * a * g) →
      y = a ∨ ∃ s ∈ (T : Subgroup G), y = s⁻¹ * x * s)
    (hxa : ∃ g : G, x = g⁻¹ * a * g) (hax : ¬ ∃ s ∈ (T : Subgroup G), a = s⁻¹ * x * s) :
    ∃ s ∈ (T : Subgroup G), ∃ n ∈ normalizer
      (((T : Subgroup G) ⊓ centralizer ({s⁻¹ * x * s} : Set G) : Subgroup G) : Set G),
      n⁻¹ * (s⁻¹ * x * s) * n = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := hxa
  set P : Subgroup G := (T : Subgroup G) ⊓ centralizer ({x} : Set G) with hPdef
  have hxP : x ∈ P := mem_inf.mpr ⟨hxT, mem_centralizer_singleton_iff.mpr rfl⟩
  have hTa : (T : Subgroup G) ≤ centralizer ({a} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (haZ s hs).symm
  have hV : P.map (MulAut.conj g).toMonoidHom ≤ centralizer ({a} : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzx := mem_centralizer_singleton_iff.mp (mem_inf.mp hz).2
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hga : a = g * x * g⁻¹ := by rw [hg]; group
    rw [hga]
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hzx]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
  have hVp : IsPGroup 2 (P.map (MulAut.conj g).toMonoidHom) :=
    (T.isPGroup'.to_le inf_le_left).map _
  obtain ⟨c, hc, hcT⟩ := exists_conj_le_sylow T hTa hV hVp
  have hca : c⁻¹ * a * c = a := by
    have := mem_centralizer_singleton_iff.mp hc
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  set k₀ : G := g⁻¹ * c with hk₀
  have hk₀P : P.map (MulAut.conj k₀⁻¹).toMonoidHom ≤ (T : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hcT (g * z * g⁻¹) ⟨z, hz, by simp⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hk₀]
    rwa [show (g⁻¹ * c)⁻¹ * z * (g⁻¹ * c) = c⁻¹ * (g * z * g⁻¹) * c by group]
  obtain ⟨k, hdec, hk⟩ := RankTwoShapes.alperin_centric_radical_fusion T inf_le_left hk₀P
  have hkx : k⁻¹ * x * k = a := by
    rw [hk x hxP, hk₀, hg, show (g⁻¹ * c)⁻¹ * (g⁻¹ * a * g) * (g⁻¹ * c) = c⁻¹ * a * c by group,
      hca]
  have hconj : ∀ k' : G, ∃ g' : G, k'⁻¹ * x * k' = g'⁻¹ * a * g' := fun k' =>
    ⟨g * k', by rw [hg]; group⟩
  have key : ∀ k' : G, RankTwoShapes.AlperinDecomposition 2 (T : Subgroup G) P k' →
      (∃ s ∈ (T : Subgroup G), k'⁻¹ * x * k' = s⁻¹ * x * s) ∨
      (k'⁻¹ * x * k' = a ∧ ∃ s ∈ (T : Subgroup G), ∃ n ∈ normalizer
        (((T : Subgroup G) ⊓ centralizer ({s⁻¹ * x * s} : Set G) : Subgroup G) : Set G),
        n⁻¹ * (s⁻¹ * x * s) * n = a) := by
    intro k' hk'
    induction hk' with
    | one => exact Or.inl ⟨1, one_mem _, by group⟩
    | @step c' n Q hdec' hQ hPQ hn ih =>
      have hyQ : c'⁻¹ * x * c' ∈ Q :=
        hPQ ⟨x, hxP, by simp⟩
      have hy'Q : n⁻¹ * (c'⁻¹ * x * c') * n ∈ Q := by
        have := (mem_normalizer_iff.mp (inv_mem hn) _).mp hyQ
        rwa [inv_inv] at this
      have hy'eq : (c' * n)⁻¹ * x * (c' * n) = n⁻¹ * (c'⁻¹ * x * c') * n := by group
      rw [hy'eq]
      rcases hfus _ (hQ.1 hy'Q) (by
          obtain ⟨g', hg'⟩ := hconj (c' * n)
          exact ⟨g', by rw [← hy'eq, hg']⟩) with hya | hyx
      · rcases ih with ⟨s, hs, hys⟩ | ⟨hya', rest⟩
        · refine Or.inr ⟨hya, s, hs, n, ?_, by rw [← hys, hya]⟩
          have hQle : Q ≤ (T : Subgroup G) ⊓ centralizer ({s⁻¹ * x * s} : Set G) := by
            intro q hq
            refine mem_inf.mpr ⟨hQ.1 hq, mem_centralizer_singleton_iff.mpr ?_⟩
            have hq' : n⁻¹ * q * n ∈ Q := by
              have := (mem_normalizer_iff.mp (inv_mem hn) q).mp hq
              rwa [inv_inv] at this
            have hz := haZ _ (hQ.1 hq')
            have hy : s⁻¹ * x * s = n * a * n⁻¹ := by rw [← hys, ← hya]; group
            rw [hy]
            calc q * (n * a * n⁻¹) = n * ((n⁻¹ * q * n) * a) * n⁻¹ := by group
              _ = n * (a * (n⁻¹ * q * n)) * n⁻¹ := by rw [hz]
              _ = n * a * n⁻¹ * q := by group
          have hge : (T : Subgroup G) ⊓ centralizer ({s⁻¹ * x * s} : Set G) ≤ Q := by
            have hWle : P.map (MulAut.conj c'⁻¹).toMonoidHom ≤
                (T : Subgroup G) ⊓ centralizer ({s⁻¹ * x * s} : Set G) := by
              refine le_inf (hdec'.map_le inf_le_left) ?_
              rintro _ ⟨z, hz, rfl⟩
              have hzx := mem_centralizer_singleton_iff.mp (mem_inf.mp hz).2
              rw [mem_centralizer_singleton_iff, ← hys]
              simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
              calc c'⁻¹ * z * c' * (c'⁻¹ * x * c') = c'⁻¹ * (z * x) * c' := by group
                _ = c'⁻¹ * (x * z) * c' := by rw [hzx]
                _ = c'⁻¹ * x * c' * (c'⁻¹ * z * c') := by group
            have hcard : Nat.card ↥((T : Subgroup G) ⊓ centralizer ({s⁻¹ * x * s} : Set G)) ≤
                Nat.card ↥(P.map (MulAut.conj c'⁻¹).toMonoidHom) := by
              rw [Subgroup.card_map_of_injective (MulAut.conj c'⁻¹).injective,
                card_inf_centralizer_conj hs]
            rw [← Subgroup.eq_of_le_of_card_ge hWle hcard]
            exact hPQ
          rw [le_antisymm hQle hge] at hn
          exact hn
        · exact Or.inr ⟨hya, rest⟩
      · exact Or.inl hyx
  rcases key k hdec with ⟨s, hs, hsx⟩ | ⟨-, rest⟩
  · exact absurd ⟨s, hs, by rw [← hsx, hkx]⟩ hax
  · exact rest

theorem lt_inf_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {Q S : Subgroup G}
    (hS : IsPGroup p S) (hQS : Q < S) : Q < S ⊓ normalizer (Q : Set G) := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : Q.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hQS.not_ge ?_
    exact Subgroup.subgroupOf_eq_top.mp h
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := S) _ hlt
  obtain ⟨x, hx, hxQ⟩ := IsConcreteLE.exists_of_lt hnorm
  have hxN : (x : G) ∈ normalizer (Q : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    have hx' := mem_normalizer_iff.mp hx
    constructor
    · intro hg
      exact (hx' ⟨g, hQS.le hg⟩).mp hg
    · intro hg
      have hgS : g ∈ S := by
        have h1 : x * g * x⁻¹ ∈ S := hQS.le hg
        have h2 : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) := by group
        rw [h2]
        exact S.mul_mem (S.mul_mem (S.inv_mem x.2) h1) x.2
      exact (hx' ⟨g, hgS⟩).mpr hg
  refine lt_of_le_of_ne (le_inf hQS.le le_normalizer) fun h => hxQ ?_
  have : (x : G) ∈ S ⊓ normalizer (Q : Set G) := ⟨x.2, hxN⟩
  rw [← h] at this
  exact this

theorem mem_normalizer_of_le_centralizer {a : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G)) : a ∈ normalizer (J : Set G) := by
  have hjc : ∀ j ∈ J, j * a = a * j := fun j hj => mem_centralizer_singleton_iff.mp (hJa hj)
  rw [mem_normalizer_iff]
  intro j
  constructor
  · intro hj
    rwa [show a * j * a⁻¹ = j by rw [← hjc j hj]; group]
  · intro hj
    have h1 := hjc _ hj
    have h2 : j = a * j * a⁻¹ := mul_left_cancel (a := a) (by rw [← h1]; group)
    rwa [h2]

theorem mem_coreActionKernel_of_le_centralizer {a : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G)) : a ∈ coreActionKernel J := by
  refine mem_coreActionKernel.mpr ⟨mem_normalizer_of_le_centralizer hJa, fun j hj => ?_⟩
  rw [show j⁻¹ * a⁻¹ * j * a = 1 by
    rw [mul_assoc, mem_centralizer_singleton_iff.mp (hJa hj)]; group]
  exact one_mem _

theorem mem_zStarIn_of_le_centralizer {a : G} {J : Subgroup G} (haJ : a ∈ J)
    (hJa : J ≤ centralizer ({a} : Set G)) : a ∈ zStarIn J := by
  refine ⟨⟨a, haJ⟩, ?_, rfl⟩
  show QuotientGroup.mk' (Open.fusionOddCore ↥J) ⟨a, haJ⟩ ∈ center _
  rw [mem_center_iff]
  intro q
  induction q using QuotientGroup.induction_on with
  | H j =>
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJa j.2))

theorem isElemTwo_sup_zpowers [Finite G] {E : Subgroup G} {t : G} (hE : IsElemTwo E)
    (ht : t * t = 1) (htE : t ∉ E) (hc : ∀ e ∈ E, e * t = t * e) :
    IsElemTwo (E ⊔ zpowers t) ∧ Nat.card ↥(E ⊔ zpowers t) = 2 * Nat.card E := by
  have hcz : ∀ u ∈ E, ∀ v ∈ zpowers t, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (hc u hu) k)
  refine ⟨hE.sup (isElemTwo_zpowers ht) hcz, le_antisymm ?_ ?_⟩
  · have htN : t ∈ normalizer (E : Set G) :=
      mem_normalizer_of_le_centralizer fun e he => mem_centralizer_singleton_iff.mpr (hc e he)
    rw [sup_comm]
    exact card_zpowers_sup_le ht htN
  · have hlt : E < E ⊔ zpowers t := lt_of_le_of_ne le_sup_left fun h =>
      htE (h ▸ mem_sup_right (mem_zpowers t))
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hlt.le
    have hne : Nat.card E ≠ Nat.card ↥(E ⊔ zpowers t) := fun h =>
      hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.symm.le)
    have hpos : 0 < Nat.card E := Nat.card_pos
    rw [hk] at hne ⊢
    rcases k with _ | _ | k
    · simp at hk
      exact absurd hk Nat.card_pos.ne'
    · simp at hne
    · nlinarith

theorem isPGroup_of_isSylowTwoIn {S H : Subgroup G} (h : IsSylowTwoIn S H) : IsPGroup 2 S := by
  obtain ⟨hSH, P, hP⟩ := h
  have h1 := P.isPGroup'
  rw [hP] at h1
  exact h1.of_equiv (subgroupOfEquivOfLe hSH)

theorem eq_one_or_eq_of_mem_zpowers {u v : G} (hu : u * u = 1) (hv : v ∈ zpowers u) :
    v = 1 ∨ v = u := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
  have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, hu2, one_zpow]
  · right; rw [zpow_add, zpow_mul, hu2, one_zpow, one_mul, zpow_one]

theorem mem_or_mul_of_mem_sup_zpowers {E : Subgroup G} {t v : G} (ht : t * t = 1)
    (hc : ∀ e ∈ E, e * t = t * e) (hv : v ∈ E ⊔ zpowers t) : v ∈ E ∨ ∃ e ∈ E, v = e * t := by
  have hle : zpowers t ≤ normalizer (E : Set G) := zpowers_le.mpr
    (mem_normalizer_of_le_centralizer fun e he => mem_centralizer_singleton_iff.mpr (hc e he))
  have hv' : v ∈ ((E : Set G) * (zpowers t : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left E (zpowers t) hle]
    exact hv
  obtain ⟨e, he, u, hu, rfl⟩ := hv'
  rcases eq_one_or_eq_of_mem_zpowers ht hu with rfl | rfl
  · left; simpa using he
  · right; exact ⟨e, he, rfl⟩

theorem sq_and_involutions_of_card_eight [Finite G] {R : Subgroup G}
    (hRab : ∀ u ∈ R, ∀ v ∈ R, u * v = v * u) (h8 : Nat.card R = 8) {a w : G} (haR : a ∈ R)
    (hwR : w ∈ R) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hw1 : w * w ≠ 1) (hwa : w * w ≠ a)
    (hw4 : w * w * (w * w) = 1) :
    (∀ r ∈ R, r * r = 1 ∨ r * r = w * w) ∧
      ∀ r ∈ R, r * r = 1 → r = 1 ∨ r = a ∨ r = w * w ∨ r = a * (w * w) := by
  have hw2R : w * w ∈ R := mul_mem hwR hwR
  have hE1 : IsElemTwo (zpowers a) := isElemTwo_zpowers ha2
  have hwnot : w * w ∉ zpowers a := fun h =>
    (eq_one_or_eq_of_mem_zpowers ha2 h).elim hw1 hwa
  obtain ⟨hE2, hc2⟩ := isElemTwo_sup_zpowers hE1 hw4 hwnot fun e he => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (hRab a haR _ hw2R) k)
  set E₂ := zpowers a ⊔ zpowers (w * w) with hE₂
  have hcardA : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1]
  have hE₂4 : Nat.card E₂ = 4 := by rw [hc2, hcardA]
  have hE₂R : E₂ ≤ R := sup_le (zpowers_le.mpr haR) (zpowers_le.mpr hw2R)
  have hcE : ∀ e ∈ E₂, e * w = w * e := fun e he => hRab e (hE₂R he) w hwR
  have hwE : w ∉ E₂ := fun h => hw1 (hE2.2 w h)
  have hlt : E₂ < E₂ ⊔ zpowers w := lt_of_le_of_ne le_sup_left fun h =>
    hwE (h ▸ mem_sup_right (mem_zpowers w))
  have hER : E₂ ⊔ zpowers w ≤ R := sup_le hE₂R (zpowers_le.mpr hwR)
  have hEw : E₂ ⊔ zpowers w = R := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hER
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hlt.le
    have hne : Nat.card E₂ ≠ Nat.card ↥(E₂ ⊔ zpowers w) := fun h =>
      hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.symm.le)
    rw [h8] at hk
    rw [hE₂4] at hm hne
    have hle8 : Nat.card ↥(E₂ ⊔ zpowers w) ≤ 8 := Nat.le_of_dvd (by norm_num) ⟨k, hk⟩
    have hpos : 0 < Nat.card ↥(E₂ ⊔ zpowers w) := Nat.card_pos
    have : Nat.card ↥(E₂ ⊔ zpowers w) = 8 := by
      rcases m with _ | _ | _ | m <;> omega
    exact Subgroup.eq_of_le_of_card_ge hER (by rw [h8, this])
  refine ⟨fun r hr => ?_, fun r hr hr2 => ?_⟩
  · rw [← hEw] at hr
    have hwcomm : ∀ e ∈ E₂, e * w = w * e := hcE
    have hle : zpowers w ≤ normalizer (E₂ : Set G) := zpowers_le.mpr
      (mem_normalizer_of_le_centralizer fun e he => mem_centralizer_singleton_iff.mpr (hcE e he))
    have hr' : r ∈ ((E₂ : Set G) * (zpowers w : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left E₂ (zpowers w) hle]
      exact hr
    obtain ⟨e, he, u, hu, rfl⟩ := hr'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    have hcomm : e * w ^ k = w ^ k * e := (Commute.zpow_right (hcE e he) k)
    have hsq : e * w ^ k * (e * w ^ k) = (w * w) ^ k := by
      have h1 : e * w ^ k * (e * w ^ k) = e * e * (w ^ k * w ^ k) := by
        rw [show e * w ^ k * (e * w ^ k) = e * (w ^ k * e) * w ^ k by group, ← hcomm]; group
      rw [h1, hE2.2 e he, one_mul, ← zpow_add, ← two_mul, zpow_mul, zpow_two]
    rw [hsq]
    rcases eq_one_or_eq_of_mem_zpowers hw4 (zpow_mem (mem_zpowers (w * w)) k) with h | h
    · left; exact h
    · right; exact h
  ·
    have hrE : r ∈ E₂ := by
      by_contra hrE
      obtain ⟨hE3, hc3⟩ := isElemTwo_sup_zpowers hE2 hr2 hrE fun e he => hRab e (hE₂R he) r hr
      have hE3R : E₂ ⊔ zpowers r ≤ R := sup_le hE₂R (zpowers_le.mpr hr)
      have hEq : E₂ ⊔ zpowers r = R :=
        Subgroup.eq_of_le_of_card_ge hE3R (by rw [h8, hc3, hE₂4])
      exact hw1 (hE3.2 w (hEq ▸ hwR))
    rcases mem_or_mul_of_mem_sup_zpowers hw4 (fun e he => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
        exact (Commute.zpow_left (hRab a haR _ hw2R) k)) hrE with h | ⟨e, he, rfl⟩
    · rcases eq_one_or_eq_of_mem_zpowers ha2 h with rfl | rfl
      · left; rfl
      · right; left; rfl
    · rcases eq_one_or_eq_of_mem_zpowers ha2 he with rfl | rfl
      · right; right; left; rw [one_mul]
      · right; right; right; rfl

end CFSG.ComponentClassification.GrSLit.GrS4
