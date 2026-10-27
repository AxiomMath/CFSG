module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxChain
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxInputs

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

theorem centralizer_zpowers_eq' (a : X) :
    centralizer ((zpowers a : Subgroup X) : Set X) = centralizer ({a} : Set X) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem mem_normalizer_zpowers_of_commute {a b : X} (hab : a * b = b * a) :
    b ∈ normalizer ((zpowers a : Subgroup X) : Set X) := by
  have hy : ∀ y : X, y ∈ zpowers a → b * y * b⁻¹ = y := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have hc : Commute b (a ^ k) := Commute.zpow_right (show Commute a b from hab).symm k
    rw [hc.eq, mul_inv_cancel_right]
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro h
    rw [hy y h]
    exact h
  · intro h
    have h1 := hy _ h
    have e : y = b * y * b⁻¹ := by
      calc y = b⁻¹ * (b * y * b⁻¹) * b := by group
        _ = b⁻¹ * (b * (b * y * b⁻¹) * b⁻¹) * b := by rw [h1]
        _ = b * y * b⁻¹ := by group
    rw [e]
    exact h

theorem centralizer_le_normalizer' (A : Subgroup X) :
    centralizer (A : Set X) ≤ normalizer (A : Set X) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [(mem_centralizer_iff.mp hc a ha).symm, mul_inv_cancel_right]
    exact ha
  · intro ha
    have h1 := (mem_centralizer_iff.mp hc _ ha).symm
    have e : a = c * a * c⁻¹ := by
      calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
        _ = c⁻¹ * (c * (c * a * c⁻¹)) := by rw [mul_assoc c⁻¹, h1]
        _ = c * a * c⁻¹ := by group
    rw [e]
    exact ha

variable [Finite X]

theorem normalizer_ne_top_of_isPGroup [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a)
    {A : Subgroup X} (hA : A ≠ ⊥) (hA2 : IsPGroup 2 A) : normalizer (A : Set X) ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hn : A.Normal := normalizer_eq_top_iff.mp h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with h1 | h1
  · exact hA h1
  · have hX2 : IsPGroup 2 X := by
      subst h1
      exact hA2.of_equiv Subgroup.topEquiv
    have : Nontrivial X := by
      obtain ⟨a, b, hab⟩ := hna
      exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have hZ := hX2.center_nontrivial
    rw [center_eq_bot_of_isSimpleGroup hna] at hZ
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hZ

theorem isKGroupCat_centralizer_sup [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) {A : Subgroup X} {x : X} (hA : A ≠ ⊥)
    (hA2 : IsPGroup 2 A) (hxA : x ∈ normalizer (A : Set X)) :
    SectionRank.IsKGroupCat ↥(centralizer (A : Set X) ⊔ zpowers x) := by
  refine UnbalancedCorr.isKGroupCat_of_ne_top hK fun h => ?_
  apply normalizer_ne_top_of_isPGroup hna hA hA2
  rw [eq_top_iff, ← h]
  exact sup_le (centralizer_le_normalizer' A) (zpowers_le.mpr hxA)

structure MaxSetting (X : Type) [Group X] [Finite X] (n : ℕ) : Prop where
  nonab : ∃ a b : X, a * b ≠ b * a
  kproper : Assembly.KProper Blueprint.Catalog X
  oddcore : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥
  noU : ¬ OutcomeLocal.UOutcome X
  odd : Odd n
  nine : 9 ≤ n
  maxdeg : ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' →
    Odd n' → n' ≤ n

variable [IsSimpleGroup X] {n : ℕ}

theorem exact_of_cover (hN1 : TwoGroupAltCoverExclusion) (hS : MaxSetting X n) :
    ∀ B : Subgroup X, B ≠ ⊥ → IsPGroup 2 B → ∀ T : Subgroup X,
      IsTwoComponentIn T (centralizer (B : Set X)) →
      ∀ m : ℕ, Odd m → 9 ≤ m → Nonempty (↥T ⧸ Open.fusionZStar ↥T ≃* alternatingGroup (Fin m)) →
        Open.fusionZStar ↥T = pPrimeCore 2 ↥T :=
  fun B hB hB2 T hT m hm hm9 e =>
    hN1 X hS.nonab hS.kproper hS.oddcore hS.noU B m T hB hB2 hm hm9 hT.1 hT.2 e

theorem kGroup_of_setting (hS : MaxSetting X n) :
    ∀ (A : Subgroup X) (x : X), A ≠ ⊥ → IsPGroup 2 A → x ∈ normalizer (A : Set X) →
      SectionRank.IsKGroupCat ↥(centralizer (A : Set X) ⊔ zpowers x) :=
  fun _ _ hA hA2 hxA => isKGroupCat_centralizer_sup hS.nonab hS.kproper hA hA2 hxA

omit [Finite X] [IsSimpleGroup X] in
theorem zpowers_facts {a : X} (ha : orderOf a = 2) :
    zpowers a ≠ ⊥ ∧ IsPGroup 2 (zpowers a) := by
  refine ⟨fun h => ?_, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])⟩
  have h1 : a ∈ zpowers a := mem_zpowers a
  rw [h, mem_bot] at h1
  rw [h1, orderOf_one] at ha
  omega

theorem invAt_zpowers (hN1 : TwoGroupAltCoverExclusion) (hS : MaxSetting X n) {K : Subgroup X}
    {a : X} (ha : orderOf a = 2) (eK : ↥K ⧸ Open.fusionZStar ↥K ≃* alternatingGroup (Fin n))
    (halt : AltAt K (zpowers a) n) : InvAt K (zpowers a) := by
  intro M hM hmove
  obtain ⟨m, hm, hnm, ⟨e⟩⟩ := halt M hM hmove
  obtain ⟨hza, hza2⟩ := zpowers_facts ha
  have hZO := exact_of_cover hN1 hS _ hza hza2 M hM m hm (by have := hS.nine; omega) ⟨e⟩
  have hC := centralizer_zpowers_eq' a
  have hAlt : SolAltLit.IsAltTwoComponent a M m := by
    refine ⟨ha, hC ▸ hM.1, ?_, ⟨(QuotientGroup.quotientMulEquivOfEq hZO.symm).trans e⟩⟩
    have h := hM.2
    rwa [hC] at h
  have hmn : m = n := le_antisymm (hS.maxdeg a M m hAlt hm) hnm
  subst hmn
  exact (Nat.card_congr e.toEquiv).trans (Nat.card_congr eK.toEquiv).symm

theorem exists_good_zpowers (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hS : MaxSetting X n) {K : Subgroup X}
    (hKmem : IsSolomonMember K) (eK : ↥K ⧸ Open.fusionZStar ↥K ≃* alternatingGroup (Fin n)) :
    ∃ b : X, orderOf b = 2 ∧ b ∈ coreActionKernel K ∧ StarAt K (zpowers b) ∧
      InvAt K (zpowers b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKq := Sol76.isQuasisimple_coreQuot_of_isSolomonMember hKmem
  obtain ⟨-, T₀, hT₀, hT₀2, hT₀Q, hK₀⟩ := hKmem
  obtain ⟨hst, hinv⟩ := starAt_inv_of_witness hKq hT₀2 hT₀Q hK₀
  have halt := altAt_of_invAt hKq hT₀2 hT₀Q hS.odd eK hst hinv
  have h2 : 2 ∣ Nat.card T₀ := by
    rcases hT₀2.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hT₀
    · exact h
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥T₀) 2 h2
  have hb' : orderOf (b : X) = 2 := by rw [Subgroup.orderOf_coe, hb]
  obtain ⟨hzb, hzb2⟩ := zpowers_facts hb'
  obtain ⟨hst', halt'⟩ := starAt_altAt_of_le hPump hKq hT₀2 hT₀Q hS.nine
    (kGroup_of_setting hS) (exact_of_cover hN1 hS) hst halt (zpowers (b : X))
    (zpowers_le.mpr b.2) hzb
  exact ⟨b, hb', hT₀Q b.2, hst', invAt_zpowers hN1 hS hb' eK halt'⟩

theorem good_zpowers_of_commute (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hS : MaxSetting X n) {K : Subgroup X} {a b : X}
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (eK : ↥K ⧸ Open.fusionZStar ↥K ≃* alternatingGroup (Fin n)) (ha : orderOf a = 2)
    (hb : orderOf b = 2) (haQ : a ∈ coreActionKernel K) (hbQ : b ∈ coreActionKernel K)
    (hab : a * b = b * a) (hst : StarAt K (zpowers b)) (hinv : InvAt K (zpowers b)) :
    StarAt K (zpowers a) ∧ InvAt K (zpowers a) := by
  by_cases heq : a = b
  · subst heq; exact ⟨hst, hinv⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hza, hza2⟩ := zpowers_facts ha
  obtain ⟨hzb, hzb2⟩ := zpowers_facts hb
  have ha2 : a ^ 2 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hb2 : b ^ 2 = 1 := by rw [← hb, pow_orderOf_eq_one]
  obtain ⟨h1, h2⟩ := good_sup_zpowers hKq hzb2 (zpowers_le.mpr hbQ) hza2 haQ
    (mem_normalizer_zpowers_of_commute hab.symm) (by rw [ha2]; exact one_mem _) hst hinv
  have hP2 : IsPGroup 2 ↥(zpowers b ⊔ zpowers a) := by
    have := IsPGroup.to_sup_of_normal_right' hza2 hzb2
      (zpowers_le.mpr (mem_normalizer_zpowers_of_commute hab.symm))
    rwa [sup_comm] at this
  have hPQ : zpowers b ⊔ zpowers a ≤ coreActionKernel K :=
    sup_le (zpowers_le.mpr hbQ) (zpowers_le.mpr haQ)
  have halt := altAt_of_invAt hKq hP2 hPQ hS.odd eK h1 h2
  have hbnA : b ∉ zpowers a := by
    intro h
    rcases UnbalancedGS.OrbitFixedComponent.eq_one_or_eq_of_mem_zpowers
      (by rw [← pow_two, ha2]) h with h' | h'
    · rw [h', orderOf_one] at hb; omega
    · exact heq h'.symm
  rw [sup_comm] at h1 halt
  obtain ⟨hst', halt'⟩ := altAt_of_sup_zpowers hPump hKq hza2 (zpowers_le.mpr haQ) hzb2 hbQ
    (mem_normalizer_zpowers_of_commute hab) (by rw [hb2]; exact one_mem _) hbnA hS.nine
    (kGroup_of_setting hS _ _ hza hza2 (mem_normalizer_zpowers_of_commute hab))
    (fun T hT m hm hm9 e => exact_of_cover hN1 hS _ (fun h => hza (eq_bot_iff.mpr
      (h ▸ le_sup_left))) (by rwa [sup_comm]) T hT m hm hm9 e) h1 halt
  exact ⟨hst', invAt_zpowers hN1 hS ha eK halt'⟩

omit [Finite X] [IsSimpleGroup X] in
theorem not_le_coreActionKernel_self {K : Subgroup X}
    (hq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) : ¬ K ≤ coreActionKernel K := by
  intro h
  have hcomm : ∀ a b : ↥K ⧸ pPrimeCore 2 ↥K, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    obtain ⟨o, ho, hoe⟩ := (h b.2).2 a a.2
    have e : (a * b)⁻¹ * (b * a) = o⁻¹ := by
      apply Subtype.ext
      have hoe' : (o : X) = (a : X)⁻¹ * (b : X)⁻¹ * a * b := hoe
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hoe']
      group
    rw [e]
    exact inv_mem ho
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm])

omit [Finite X] [IsSimpleGroup X] in
theorem ne_bot_of_isQuasisimple_coreQuot {J : Subgroup X}
    (hq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J)) : J ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, a, b, hab⟩ := hq
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have ha : a = 1 := Subtype.ext ((mem_bot).mp a.2)
  have hb : b = 1 := Subtype.ext ((mem_bot).mp b.2)
  rw [ha, hb]

omit [IsSimpleGroup X] in
theorem isTwoComponentIn_of_conjClosure {C J K₁ : Subgroup X} (hJE : J ≤ twoLayerIn C)
    (hK₁ : IsTwoComponentIn K₁ (conjClosure J (twoLayerIn C))) :
    IsTwoComponentIn K₁ C ∧ ¬ J ≤ coreActionKernel K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := twoLayerIn C with hE
  set P := conjClosure J E with hP
  have hPE : P ≤ E := Sol78.conjClosure_le hJE le_normalizer
  have hEP : E ≤ normalizer (P : Set X) := Sol78.le_normalizer_conjClosure J E
  have hEC : E ≤ C := map_subtype_le _
  have hCE : C ≤ normalizer (E : Set X) := Sol76.le_normalizer_twoLayerIn C
  have hPn : (P.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hPE).mpr hEP
  have hEn : (E.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hEC).mpr hCE
  have hK₁E : IsPComponent 2 (K₁.subgroupOf E) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hK₁.1 hPE
      hPn.isSubnormal).mpr hK₁.2
  have hK₁C : IsTwoComponentIn K₁ C := ⟨hK₁.1.trans (hPE.trans hEC),
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal (hK₁.1.trans hPE) hEC
      hEn.isSubnormal).mpr hK₁E⟩
  refine ⟨hK₁C, fun hJK => ?_⟩
  have hq : IsQuasisimple (↥K₁ ⧸ pPrimeCore 2 ↥K₁) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K₁ C hK₁C.1).mp hK₁C.2).2.2
  apply not_le_coreActionKernel_self hq
  refine hK₁.1.trans ((closure_le _).mpr fun x hx => ?_)
  obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨j, hj, rfl⟩ := hxe
  have hEN := twoLayerIn_le_normalizer hK₁C.1 hK₁C.2
  have h1 := conj_mem_coreActionKernel (hEN (inv_mem he)) (hJK hj)
  simpa [MulAut.conj_apply] using h1

theorem twoLayerIn_top_eq_top (hna : ∃ a b : X, a * b ≠ b * a) {x : X} (hx : orderOf x = 2) :
    twoLayerIn (⊤ : Subgroup X) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup ↥(⊤ : Subgroup X) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).isSimpleGroup
  have hx' : orderOf (⟨x, mem_top x⟩ : ↥(⊤ : Subgroup X)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hx
  have hO : pPrimeCore 2 ↥(⊤ : Subgroup X) = ⊥ := pPrimeCore_two_eq_bot_of_isSimpleGroup hx'
  have hXq : IsQuasisimple X := (LocalCores.isQuasisimple_of_isSimpleGroup hna).1
  have : Group.IsPerfect X := hXq.1
  have hperf : Group.IsPerfect ↥(⊤ : Subgroup X) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).symm.toMonoidHom)
      (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).symm.surjective
  have htop : IsPComponent 2 (⊤ : Subgroup X) := by
    rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2]
    refine ⟨normal_top.isSubnormal, Sol76.primeResidual_two_eq_top hperf, ?_⟩
    exact LocalCores.isQuasisimple_of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans
        Subgroup.topEquiv).symm hXq
  have htop' : IsPComponent 2 (⊤ : Subgroup ↥(⊤ : Subgroup X)) := by
    have := (isPComponent_subgroupOf_top_iff (⊤ : Subgroup X)).mpr htop
    rwa [subgroupOf_self] at this
  have hL : pLayer ↥(⊤ : Subgroup X) 2 = ⊤ := eq_top_iff.mpr (le_sSup htop')
  rw [twoLayerIn, hL, ← MonoidHom.range_eq_map, range_subtype]

theorem nonempty_fusionZStar_equiv_of_solomonLt (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hS : MaxSetting X n) {K K₁ : Subgroup X}
    (hKmem : IsSolomonMember K) (eK : ↥K ⧸ Open.fusionZStar ↥K ≃* alternatingGroup (Fin n))
    (hlt : SolomonLt K K₁) :
    Nonempty (↥K₁ ⧸ Open.fusionZStar ↥K₁ ≃* ↥K ⧸ Open.fusionZStar ↥K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKq := Sol76.isQuasisimple_coreQuot_of_isSolomonMember hKmem
  obtain ⟨-, hK₁mem, T, hT2, hTQ, hK₁⟩ := hlt
  obtain ⟨z₀, hz₀, -⟩ := hS.oddcore
  set Q := coreActionKernel K with hQ
  by_cases hT : T = ⊥
  ·
    exfalso
    subst hT
    have hC : centralizer ((⊥ : Subgroup X) : Set X) = ⊤ := by
      ext y
      simp [mem_centralizer_iff]
    rw [hC, twoLayerIn_top_eq_top hS.nonab hz₀] at hK₁
    set P := conjClosure (twoLayerIn (K ⊓ (⊤ : Subgroup X))) (⊤ : Subgroup X) with hP
    have hPn : P.Normal := normalizer_eq_top_iff.mp (eq_top_iff.mpr
      (Sol78.le_normalizer_conjClosure _ ⊤))
    have hK₁sub : (K₁.subgroupOf P).IsSubnormal :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K₁ P hK₁.1).mp hK₁.2).1
    have hK₁s : K₁.IsSubnormal := Subgroup.IsSubnormal.trans hK₁.1 hK₁sub hPn.isSubnormal
    have hK₁q : IsQuasisimple (↥K₁ ⧸ pPrimeCore 2 ↥K₁) :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K₁ P hK₁.1).mp hK₁.2).2.2
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hK₁s with h | h
    · exact ne_bot_of_isQuasisimple_coreQuot hK₁q h
    · obtain ⟨-, T₁, hT₁, -, hT₁C, -⟩ := hK₁mem
      rw [h, coreActionKernel_top_eq_bot hS.nonab hz₀, le_bot_iff] at hT₁C
      exact hT₁ hT₁C
  obtain ⟨b, hb, hbQ, hstb, hinvb⟩ := exists_good_zpowers hPump hN1 hS hKmem eK
  obtain ⟨hzb, hzb2⟩ := zpowers_facts hb
  have hT2' : IsPGroup 2 ↥(T.subgroupOf Q) := hT2.comap_subtype
  have hb2' : IsPGroup 2 ↥((zpowers b).subgroupOf Q) := hzb2.comap_subtype
  obtain ⟨P₁, hTP₁⟩ := hT2'.exists_le_sylow
  obtain ⟨P₂, hbP₂⟩ := hb2'.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥Q P₁ P₂
  set S := (P₂ : Subgroup ↥Q).map Q.subtype with hSdef
  have hS2 : IsPGroup 2 S := P₂.isPGroup'.map Q.subtype
  have hSQ : S ≤ Q := map_subtype_le _
  have hbS : b ∈ S := ⟨⟨b, hbQ⟩, hbP₂ (mem_subgroupOf.mpr (mem_zpowers b)), rfl⟩
  set φ := MulAut.conj (y : X) with hφ
  set Ty := T.map φ.toMonoidHom with hTy
  have hTyS : Ty ≤ S := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : (⟨t, hTQ ht⟩ : ↥Q) ∈ (P₁ : Subgroup ↥Q) := hTP₁ (mem_subgroupOf.mpr ht)
    have h2 := Subgroup.smul_mem_pointwise_smul (⟨t, hTQ ht⟩ : ↥Q) (MulAut.conj y)
      (P₁ : Subgroup ↥Q) h1
    rw [← Sylow.coe_subgroup_smul, hy] at h2
    refine ⟨_, h2, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, hφ]
  have hTy2 : IsPGroup 2 Ty := hS2.to_le hTyS
  have hTyne : Ty ≠ ⊥ := by
    intro h
    apply hT
    rw [eq_bot_iff]
    intro t ht
    have h1 : φ t ∈ Ty := mem_map_of_mem _ ht
    rw [h, mem_bot] at h1
    exact (mem_bot).mpr (φ.map_eq_one_iff.mp h1)
  have hbne : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; omega
  have hSne : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr fun h => by
    have := hbS
    rw [h, mem_bot] at this
    exact hbne this
  have hZS := hS2.center_nontrivial
  have hZ2 : 2 ∣ Nat.card (center ↥S) := by
    rcases (hS2.to_subgroup (center ↥S)).card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hZS).ne'
    · exact h
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥S)) 2 hZ2
  set z : X := ((w : ↥S) : X) with hz
  have hzo : orderOf z = 2 := by rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hzS : z ∈ S := (w : ↥S).2
  have hzc : ∀ s ∈ S, z * s = s * z := by
    intro s hs
    have := mem_center_iff.mp w.2 ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm
  obtain ⟨hstz, hinvz⟩ := good_zpowers_of_commute hPump hN1 hS hKq eK hzo hb (hSQ hzS) hbQ
    (hzc b hbS) hstb hinvb
  have hTy2' : 2 ∣ Nat.card Ty := by
    rcases hTy2.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hTyne
    · exact h
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥Ty) 2 hTy2'
  have hao : orderOf (a : X) = 2 := by rw [Subgroup.orderOf_coe, ha]
  have haS : (a : X) ∈ S := hTyS a.2
  obtain ⟨hsta, hinva⟩ := good_zpowers_of_commute hPump hN1 hS hKq eK hao hzo (hSQ haS)
    (hSQ hzS) (hzc _ haS).symm hstz hinvz
  obtain ⟨hstT, hinvT⟩ := starAt_inv_of_le hKq hTy2 (hTyS.trans hSQ) (zpowers (a : X))
    (zpowers_le.mpr a.2) hsta hinva
  have hyN : (y : X) ∈ normalizer (K : Set X) := (mem_coreActionKernel.mp y.2).1
  have hKφ : K.map φ.toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp hyN
  have h1 := Sol76.isTwoComponentIn_map φ hK₁
  rw [map_conjClosure, map_layerAt φ hKφ, Sol76.map_twoLayerIn, Sol76.map_centralizer] at h1
  obtain ⟨hK₁C, hmove⟩ := isTwoComponentIn_of_conjClosure hstT h1
  obtain ⟨hJp, hJq, hJZ, ⟨eJ⟩⟩ := layerAt_facts hKq hTy2 (hTyS.trans hSQ)
  obtain ⟨-, heq⟩ := card_fusionZStar_quot_le hstT hJp hJq hK₁C hmove
  obtain ⟨e⟩ := heq (hJZ.trans (hinvT _ hK₁C hmove).symm)
  obtain ⟨eφ⟩ := Sol76.nonempty_quotient_fusionZStar_map φ K₁
  exact ⟨eφ.trans (e.symm.trans eJ)⟩

end CFSG.ComponentClassification.SolMax
