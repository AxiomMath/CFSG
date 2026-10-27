module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type} [Group G]

theorem conjugate_zpowers (a g : G) : conjugate (zpowers a) g = zpowers (g⁻¹ * a * g) := by
  unfold conjugate
  rw [MonoidHom.map_zpowers]
  simp

theorem isPComponent_conjugate_of_centralizer [Finite G] {a g : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G)))) :
    conjugate J g ≤ centralizer ({g⁻¹ * a * g} : Set G) ∧
      IsPComponent 2 ((conjugate J g).subgroupOf (centralizer ({g⁻¹ * a * g} : Set G))) := by
  rw [← centralizer_zpowers_eq] at hJa hJ
  have h := GSLit.isPComponent_conjugate_centralizer hJa hJ g
  rwa [conjugate_zpowers, centralizer_zpowers_eq] at h

theorem mem_of_mem_sup_of_odd [Finite G] {D N : Subgroup G} (hDN : D ≤ normalizer (N : Set G))
    (hD : Odd (Nat.card D)) {y : G} (hy : y ∈ D ⊔ N) {k : ℕ} (hyk : y ^ (2 ^ k) = 1) :
    y ∈ N := by
  set X : Subgroup G := D ⊔ N with hX
  have hXN : X ≤ normalizer (N : Set G) := sup_le hDN le_normalizer
  have hn : (N.subgroupOf X).Normal := by
    rw [normal_subgroupOf_iff le_sup_right]
    intro h k hh hk
    exact (mem_normalizer_iff.mp (hXN hk) h).mp hh
  let q := QuotientGroup.mk' (N.subgroupOf X)
  let f : ↥D →* X ⧸ N.subgroupOf X := q.comp (Subgroup.inclusion le_sup_left)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hw' : w ∈ (D : Set G) * (N : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right D N hDN]
      exact hw
    obtain ⟨d, hd, n, hn', rfl⟩ := hw'
    refine ⟨⟨d, hd⟩, ?_⟩
    show q (Subgroup.inclusion le_sup_left ⟨d, hd⟩) = q ⟨d * n, hw⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    simpa using hn'
  have hodd : Odd (Nat.card (X ⧸ N.subgroupOf X)) :=
    Odd.of_dvd_nat hD (Subgroup.card_dvd_of_surjective hf)
  have h1 : orderOf (q ⟨y, hy⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    rw [← map_pow]
    have : (⟨y, hy⟩ : X) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hyk)
    rw [this, map_one])
  have h2 : orderOf (q ⟨y, hy⟩) ∣ Nat.card (X ⧸ N.subgroupOf X) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (X ⧸ N.subgroupOf X)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h3 : orderOf (q ⟨y, hy⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h3
  exact h3

theorem exists_conj_mem_of_isSylowTwoIn [Finite G] {S H : Subgroup G} (hS : IsSylowTwoIn S H)
    {V : Subgroup G} (hVH : V ≤ H) (hVp : IsPGroup 2 V) :
    ∃ h ∈ H, ∀ x ∈ V, h⁻¹ * x * h ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, P, hP⟩ := hS
  have hVp' : IsPGroup 2 (V.subgroupOf H) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  obtain ⟨R, hR⟩ := hVp'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H P R
  refine ⟨h, h.2, fun x hx => ?_⟩
  have hxR : (⟨x, hVH hx⟩ : H) ∈ (R : Subgroup H) := hR hx
  rw [← hh, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hP, Subgroup.mem_subgroupOf] at hxR
  convert hxR using 1
  simp [MulAut.inv_def, MulAut.conj_symm_apply]

theorem conj_mem_zStarIn {K : Subgroup G} {m z : G} (hm : m ∈ normalizer (K : Set G))
    (hz : z ∈ zStarIn K) : m * z * m⁻¹ ∈ zStarIn K := by
  have h : zStarIn K = K ⊓ coreActionKernel K := GSThmB.map_fusionZStar_eq K
  rw [h] at hz ⊢
  exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hm z).mp (mem_inf.mp hz).1,
    UnbalancedLayer.conj_mem_coreActionKernel hm (mem_inf.mp hz).2⟩

theorem mem_zStarIn_of_le [Finite G] {J J₁ : Subgroup G} (hJJ₁ : J ≤ J₁) {z : G} (hzJ : z ∈ J)
    (hz : z ∈ zStarIn J₁) : z ∈ zStarIn J := by
  have h1 : zStarIn J₁ = J₁ ⊓ coreActionKernel J₁ := GSThmB.map_fusionZStar_eq J₁
  have h2 : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  rw [h1] at hz
  rw [h2]
  refine mem_inf.mpr ⟨hzJ, mem_coreActionKernel.mpr ⟨le_normalizer hzJ, fun k hk => ?_⟩⟩
  have hk1 := (mem_coreActionKernel.mp (mem_inf.mp hz).2).2 k (hJJ₁ hk)
  have hD : J ⊓ oddIn J₁ ≤ (pPrimeCore 2 J).map J.subtype := by
    refine le_map_pPrimeCore inf_le_left (fun h hh d hd => mem_inf.mpr ⟨?_, ?_⟩) ?_
    · exact mul_mem (mul_mem hh (mem_inf.mp hd).1) (inv_mem hh)
    · exact conj_mem_oddIn (hJJ₁ hh) (mem_inf.mp hd).2
    · exact Odd.of_dvd_nat (odd_card_map_pPrimeCore J₁) (Subgroup.card_dvd_of_le inf_le_right)
  exact hD (mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem (inv_mem hk) (inv_mem hzJ)) hk) hzJ, hk1⟩)

theorem le_normalizer_map_of_normal {C : Subgroup G} (N : Subgroup ↥C) [N.Normal] :
    C ≤ normalizer ((N.map C.subtype : Subgroup G) : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹, Subgroup.Normal.conj_mem inferInstance y' hy' ⟨c, hc⟩,
      by simp⟩
  · rintro ⟨y', hy', hyy⟩
    refine ⟨⟨c, hc⟩⁻¹ * y' * ⟨c, hc⟩⁻¹⁻¹,
      Subgroup.Normal.conj_mem inferInstance y' hy' ⟨c, hc⟩⁻¹, ?_⟩
    simp only [subtype_apply, coe_mul, coe_inv, inv_inv] at hyy ⊢
    rw [hyy]
    group

theorem generalizedFitting_facts [Finite G] [IsSimpleGroup G] (hnab : ∃ g h : G, g * h ≠ h * g)
    (hUo : ¬ OutcomeLocal.UOutcome G) :
    IsSimpleGroup (GeneralizedFitting.subgroup G) ∧
      (∃ u v : GeneralizedFitting.subgroup G, u * v ≠ v * u) ∧
      ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) := by
  have htop : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  refine ⟨eF.isSimpleGroup, ?_, fun h => hUo (Or.inl h)⟩
  obtain ⟨u, v, huv⟩ := hnab
  exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise
open GrS4

theorem l34Lemma45_of_inputs (hSol : SolomonFixedLayerStep) : L34Lemma45 := by
  intro G _ _ a x J S hset M₁ hJM hJ₁n hSM haZ hNM g hbM hbZ
  obtain ⟨hbase, hU3, hL34, hmax, hS, haS, -⟩ := hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  have : IsSimpleGroup G := hsimple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J₁ : Subgroup G := oddIn M₁ ⊔ J with hJ₁
  have hJJ₁ : J ≤ J₁ := le_sup_right
  have hMJ₁ : ∀ m ∈ M₁, m ∈ normalizer (J₁ : Set G) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro y
    have hJ₁M : J₁ ≤ M₁ := sup_le (map_subtype_le _) hJM
    have hn := (normal_subgroupOf_iff hJ₁M).mp hJ₁n
    constructor
    · intro hy
      exact hn y m hy hm
    · intro hy
      have := hn _ m⁻¹ hy (inv_mem hm)
      rwa [show m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y by group] at this
  have ha2 : orderOf a = 2 := hU3.1
  have ha2' : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hJa := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  have hSM' : S ≤ M₁ := hSM.1
  have hb2 : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    rw [show (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, ha2']; group
  have hbp : IsPGroup 2 (zpowers (g⁻¹ * a * g)) := (isElemTwo_zpowers hb2).isPGroup
  obtain ⟨m₀, hm₀, hm₀S⟩ := exists_conj_mem_of_isSylowTwoIn hSM (zpowers_le.mpr hbM) hbp
  set g₁ : G := g * m₀ with hg₁
  have hb₁S : g₁⁻¹ * a * g₁ ∈ S := by
    have := hm₀S _ (mem_zpowers (g⁻¹ * a * g))
    rwa [show m₀⁻¹ * (g⁻¹ * a * g) * m₀ = g₁⁻¹ * a * g₁ by rw [hg₁]; group] at this
  suffices hg₁M : g₁ ∈ M₁ from
    ⟨g, by rw [show g = g₁ * m₀⁻¹ by rw [hg₁]; group]; exact mul_mem hg₁M (inv_mem hm₀), rfl⟩
  set b₁ : G := g₁⁻¹ * a * g₁ with hb₁
  have hb₁2 : b₁ * b₁ = 1 := by
    rw [hb₁, show g₁⁻¹ * a * g₁ * (g₁⁻¹ * a * g₁) = g₁⁻¹ * (a * a) * g₁ by group, ha2']; group
  have hb₁i : b₁⁻¹ = b₁ := inv_eq_of_mul_eq_one_right hb₁2
  have hb₁N : b₁ ∈ normalizer (J : Set G) := hSN hb₁S
  have hb₁Z : ∀ j ∈ J₁, j⁻¹ * b₁⁻¹ * j * b₁ ∈ zStarIn J₁ := by
    intro j hj
    have hm₀N := hMJ₁ m₀ hm₀
    have hj' : m₀ * j * m₀⁻¹ ∈ J₁ := (mem_normalizer_iff.mp hm₀N j).mp hj
    have h1 := conj_mem_zStarIn (inv_mem hm₀N) (hbZ _ hj')
    rwa [show m₀⁻¹ * ((m₀ * j * m₀⁻¹)⁻¹ * (g⁻¹ * a * g)⁻¹ * (m₀ * j * m₀⁻¹) * (g⁻¹ * a * g)) *
      m₀⁻¹⁻¹ = j⁻¹ * b₁⁻¹ * j * b₁ by rw [hb₁, hg₁]; group] at h1
  have hbJZ : ∀ l ∈ J, b₁ * l * b₁⁻¹ * l⁻¹ ∈ (Open.fusionZStar J).map J.subtype := by
    intro l hl
    have h1 := hb₁Z l⁻¹ (hJJ₁ (inv_mem hl))
    rw [inv_inv] at h1
    have hc : l * b₁⁻¹ * l⁻¹ * b₁ ∈ J := by
      have : b₁⁻¹ * l⁻¹ * b₁ ∈ J := by
        have := (mem_normalizer_iff.mp (inv_mem hb₁N) l⁻¹).mp (inv_mem hl)
        rwa [inv_inv] at this
      rw [show l * b₁⁻¹ * l⁻¹ * b₁ = l * (b₁⁻¹ * l⁻¹ * b₁) by group]
      exact mul_mem hl this
    have h2 := inv_mem (mem_zStarIn_of_le hJJ₁ hc h1)
    rwa [show (l * b₁⁻¹ * l⁻¹ * b₁)⁻¹ = b₁ * l * b₁⁻¹ * l⁻¹ by
      calc (l * b₁⁻¹ * l⁻¹ * b₁)⁻¹ = b₁⁻¹ * l * b₁ * l⁻¹ := by group
        _ = b₁ * l * b₁⁻¹ * l⁻¹ := by rw [hb₁i]] at h2
  have hJper : Group.IsPerfect ↥J := by
    have h1 : Group.IsPerfect ↥(J.subgroupOf (centralizer ({a} : Set G))) :=
      CatalogueBAlternating.pComponent_perfect hJc
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJa).toMonoidHom)
      (subgroupOfEquivOfLe hJa).surjective
  have hbJO := commutator_mem_oddCore_of_mem_fusionZStar hJper hb₁N hbJZ
  have hb₁a : a * b₁ = b₁ * a := haZ b₁ hb₁S
  set P : Subgroup G := S ⊓ J with hPdef
  have hPS : P ≤ S := inf_le_left
  have hPJ : P ≤ J := inf_le_right
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  have hPb : ∀ p ∈ P, p * b₁ = b₁ * p := by
    intro p hp
    have hc := hbJO p (hPJ hp)
    have hcS : b₁ * p * b₁⁻¹ * p⁻¹ ∈ S :=
      mul_mem (mul_mem (mul_mem hb₁S (hPS hp)) (inv_mem hb₁S)) (inv_mem (hPS hp))
    have h1 := UnbalancedLayer.eq_bot_of_le_two_group_of_le_odd hS2 (odd_card_map_pPrimeCore J)
      (zpowers_le.mpr hcS) (zpowers_le.mpr hc)
    have h2 : b₁ * p * b₁⁻¹ * p⁻¹ = 1 := by
      have := mem_zpowers (b₁ * p * b₁⁻¹ * p⁻¹)
      rw [h1] at this
      exact this
    calc p * b₁ = (b₁ * p * b₁⁻¹ * p⁻¹)⁻¹ * (b₁ * p) := by group
      _ = b₁ * p := by rw [h2, inv_one, one_mul]
  have hb₁C : b₁ ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hb₁a.symm
  have hcov := le_pLayer_inf_centralizer_sup hJa hJc (zpowers_le.mpr hb₁C)
    (isElemTwo_zpowers hb₁2).isPGroup (zpowers_le.mpr hb₁N) (fun f hf l hl => by
      rcases eq_one_or_eq_of_mem_zpowers hb₁2 hf with rfl | rfl
      · rw [show (1 : G) * l * 1⁻¹ * l⁻¹ = 1 by group]
        exact one_mem _
      · exact hbJO l hl)
  rw [centralizer_zpowers_eq] at hcov
  set C' : Subgroup G := J ⊓ centralizer ({b₁} : Set G) with hC'
  set K₀ : Subgroup G := gsFixedLayer J b₁ with hK₀
  have hK₀C : K₀ ≤ C' := gsFixedLayer_le_inf J b₁
  have hcov' : J ≤ K₀ ⊔ oddIn J := hcov
  have hPK : P ≤ K₀ := by
    intro p hp
    have hpJ := hPJ hp
    have hJO : K₀ ≤ normalizer ((oddIn J : Subgroup G) : Set G) := fun k hk =>
      mem_normalizer_iff.mpr fun y => ⟨fun hy => conj_mem_oddIn ((hK₀C hk).1) hy, fun hy => by
        have := conj_mem_oddIn (inv_mem (hK₀C hk).1) hy
        rwa [show k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y by group] at this⟩
    have hp' : p ∈ (K₀ : Set G) * (oddIn J : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right K₀ (oddIn J) hJO]
      exact hcov' hpJ
    obtain ⟨k, hk, o, ho, hko⟩ := hp'
    have hoC : o ∈ C' := by
      refine mem_inf.mpr ⟨(map_subtype_le _ : oddIn J ≤ J) ho, ?_⟩
      have hkC := (mem_inf.mp (hK₀C hk)).2
      have hpC : p ∈ centralizer ({b₁} : Set G) := mem_centralizer_singleton_iff.mpr (hPb p hp)
      have : o = k⁻¹ * p := by rw [← hko]; group
      rw [this]
      exact mul_mem (inv_mem hkC) hpC
    obtain ⟨n, hn⟩ := (hS2.to_le hPS) ⟨p, hp⟩
    refine mem_of_mem_sup_of_odd (D := C' ⊓ oddIn J) (fun d hd => ?_) ?_ ?_ (k := n) ?_
    · exact le_normalizer_map_of_normal (C := C') (pLayer ↥C' 2) (mem_inf.mp hd).1
    · exact Odd.of_dvd_nat (odd_card_map_pPrimeCore J) (Subgroup.card_dvd_of_le inf_le_right)
    · rw [← hko, sup_comm]
      exact mul_mem (mem_sup_left hk) (mem_sup_right (mem_inf.mpr ⟨hoC, ho⟩))
    · have := congrArg Subtype.val hn
      simpa using this
  obtain ⟨hsF, hnF, hoF⟩ := generalizedFitting_facts hnab hUo
  have hO : ∀ j ∈ J, j⁻¹ * b₁⁻¹ * j * b₁ ∈ oddIn J := by
    intro j hj
    have h1 := hbJO j⁻¹ (inv_mem hj)
    have hON : b₁⁻¹ ∈ normalizer ((oddIn J : Subgroup G) : Set G) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J)
        (inv_mem hb₁N)
    have h2 := (mem_normalizer_iff.mp hON _).mp h1
    rwa [show b₁⁻¹ * (b₁ * j⁻¹ * b₁⁻¹ * j⁻¹⁻¹) * b₁⁻¹⁻¹ = j⁻¹ * b₁⁻¹ * j * b₁ by group] at h2
  have hstep := hSol G hsF hnF hoF hK a J ha2 hJa hJc hmax hL34 hbase g₁ hb₁a hb₁N
    hO
  obtain ⟨hJgC, hJgp⟩ := isPComponent_conjugate_of_centralizer (g := g₁) hJa hJc
  have hPJg : P ≤ conjugate J g₁ := by
    intro p hp
    obtain ⟨n, hn⟩ := (hS2.to_le hPS) ⟨p, hp⟩
    refine mem_of_mem_sup_of_odd (D := oddIn (centralizer ({b₁} : Set G)))
      (UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hJgC hJgp)
      (odd_card_map_pPrimeCore _) (hstep (hPK hp)) (k := n) ?_
    have := congrArg Subtype.val hn
    simpa using this
  have hP := isSylowTwoIn_inf hS
  obtain ⟨-, T₀, hT₀⟩ := hP
  set Q : Subgroup G := P.map (MulAut.conj g₁).toMonoidHom with hQ
  have hQJ : Q ≤ J := by
    rintro _ ⟨p, hp, rfl⟩
    have := hPJg hp
    rw [mem_conjugate_iff] at this
    simpa using this
  have hQp : IsPGroup 2 (Q.subgroupOf J) :=
    ((hS2.to_le hPS).map _).of_equiv (subgroupOfEquivOfLe hQJ).symm
  obtain ⟨R, hR⟩ := hQp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥J T₀ R
  have hcardQ : Nat.card ↥(Q.subgroupOf J) = Nat.card ↥(P.subgroupOf J) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQJ).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv, hQ,
      Subgroup.card_map_of_injective (MulAut.conj g₁).injective]
  have hQR : Q.subgroupOf J = (R : Subgroup ↥J) := by
    refine Subgroup.eq_of_le_of_card_ge hR ?_
    rw [hcardQ, ← hT₀, Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  set k : G := (c : G)⁻¹ * g₁ with hk
  have hkP : P.map (MulAut.conj k).toMonoidHom ≤ P := by
    rintro _ ⟨p, hp, rfl⟩
    have h1 : (⟨g₁ * p * g₁⁻¹, hQJ ⟨p, hp, rfl⟩⟩ : ↥J) ∈ (R : Subgroup ↥J) := by
      rw [← hQR, mem_subgroupOf]
      exact ⟨p, hp, rfl⟩
    rw [← hc, Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hT₀, mem_subgroupOf] at h1
    have h2 : (c : G)⁻¹ * (g₁ * p * g₁⁻¹) * (c : G) ∈ P := by
      convert h1 using 1
      simp [MulAut.inv_def, MulAut.conj_symm_apply]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hk]
    convert h2 using 1
    group
  have hkPe : P.map (MulAut.conj k).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hkP (by
      rw [Subgroup.card_map_of_injective (MulAut.conj k).injective])
  have hkN : k ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← hkPe]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hkPe] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
      have : z = y := by
        have := congrArg (fun w => k⁻¹ * w * k) hzy
        simpa [mul_assoc] using this
      rwa [← this]
  have hcM : (c : G) ∈ M₁ := hJM c.2
  rw [show g₁ = (c : G) * k by rw [hk]; group]
  exact mul_mem hcM (hNM hkN)

end CFSG.ComponentClassification.GrSLit
