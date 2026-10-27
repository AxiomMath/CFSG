module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13Aux
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Semisimple
public import CFSG.LocalAnalysis.ComponentClassification.Sol78SwapBasic
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

theorem mem_of_sup_odd {Q : Type*} [Group Q] {H O : Subgroup Q} [hH : H.Normal]
    (hO : Nat.Coprime 2 (Nat.card O)) {x : Q} (hx : x ∈ O ⊔ H) {k : ℕ} (hk : x ^ (2 ^ k) = 1) :
    x ∈ H := by
  obtain ⟨o, ho, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have h1 : (QuotientGroup.mk (o * h) : Q ⧸ H) = QuotientGroup.mk o := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff h).mpr hh, mul_one]
  have h2 : orderOf (QuotientGroup.mk (o * h) : Q ⧸ H) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one])
  have h3 : orderOf (QuotientGroup.mk o : Q ⧸ H) ∣ Nat.card O := by
    have h4 := orderOf_map_dvd (QuotientGroup.mk' H) o
    have h5 := orderOf_dvd_natCard (⟨o, ho⟩ : O)
    rw [Subgroup.orderOf_mk] at h5
    exact h4.trans h5
  rw [h1] at h2
  have h6 : Nat.Coprime (orderOf (QuotientGroup.mk o : Q ⧸ H)) (2 ^ k) :=
    Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.pow_right k hO.symm)
  have h7 := Nat.Coprime.eq_one_of_dvd h6 h2
  rw [orderOf_eq_one_iff, ← h1, QuotientGroup.eq_one_iff] at h7
  exact h7

theorem mem_normalizer_inf {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [mem_inf, mem_inf, hA x, hB x]

variable {G : Type} [Group G] [Finite G]

theorem le_conjClosure_of_not_le_coreActionKernel {C K J : Subgroup G}
    (hK : IsTwoComponentIn K C) (hJL : J ≤ twoLayerIn C) (hJK : ¬ J ≤ coreActionKernel K) :
    K ≤ conjClosure J (twoLayerIn C) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := twoLayerIn C with hE
  set P := conjClosure J E with hP
  have hKE : K ≤ E := le_twoLayerIn_of_isTwoComponentIn hK
  have hEN : E ≤ normalizer (K : Set G) := twoLayerIn_le_normalizer hK.1 hK.2
  have hPE : P ≤ E := Sol78.conjClosure_le hJL le_normalizer
  have hEP : E ≤ normalizer (P : Set G) := Sol78.le_normalizer_conjClosure J E
  have hJP : J ≤ P := fun j hj =>
    subset_closure (Set.mem_iUnion₂.mpr ⟨1, one_mem E, ⟨j, hj, by simp⟩⟩)
  have hKP : K ≤ normalizer (P : Set G) := hKE.trans hEP
  have hPK : P ≤ normalizer (K : Set G) := hPE.trans hEN
  have hDn : ((K ⊓ P).subgroupOf K).Normal :=
    normal_subgroupOf_of_le_normalizer fun k hk =>
      mem_normalizer_inf (le_normalizer hk) (hKP hk)
  have hcomm : ∀ k ∈ K, ∀ j ∈ J, k⁻¹ * j⁻¹ * k * j ∈ K ⊓ P := by
    intro k hk j hj
    have hjP := hJP hj
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : j⁻¹ * k * j ∈ K := by
        have := (mem_normalizer_iff.mp (hPK (inv_mem hjP)) k).mp hk
        simpa using this
      rw [show k⁻¹ * j⁻¹ * k * j = k⁻¹ * (j⁻¹ * k * j) by group]
      exact mul_mem (inv_mem hk) h1
    · have h1 : k⁻¹ * j⁻¹ * k ∈ P := by
        have := (mem_normalizer_iff.mp (hKP (inv_mem hk)) j⁻¹).mp (inv_mem hjP)
        simpa using this
      exact mul_mem h1 hjP
  obtain ⟨-, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K C hK.1).mp hK.2
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  have hD'n : (((K ⊓ P).subgroupOf K).map π).Normal :=
    hDn.map π (QuotientGroup.mk'_surjective _)
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq hD'n.isSubnormal with
    htop | hcen
  ·
    have hmem : ∀ x : K, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ P.subgroupOf K := by
      rintro x ⟨k, hk⟩
      have hx : π x ∈ ((K ⊓ P).subgroupOf K).map π := by rw [htop]; trivial
      obtain ⟨d, hd, hdx⟩ := hx
      have h1 : d⁻¹ * x ∈ pPrimeCore 2 ↥K := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        change (π d)⁻¹ * π x = 1
        rw [hdx, inv_mul_cancel]
      have hsup : x ∈ pPrimeCore 2 ↥K ⊔ (K ⊓ P).subgroupOf K := by
        rw [show x = d * (d⁻¹ * x) by group]
        exact mul_mem (mem_sup_right hd) (mem_sup_left h1)
      have h2 := mem_of_sup_odd (H := (K ⊓ P).subgroupOf K)
        (pPrimeCore_coprime_card (p := 2) (G := ↥K)) hsup (k := k)
        (by rw [← hk, pow_orderOf_eq_one])
      exact mem_subgroupOf.mpr (mem_inf.mp (mem_subgroupOf.mp h2)).2
    intro g hg
    have hgT : (⟨g, hg⟩ : K) ∈ CatalogueBPrimeJoin.primeResidual 2 K := by
      rw [hres]; trivial
    rw [CatalogueBPrimeJoin.primeResidual_eq_closure] at hgT
    have hle : closure {x : K | ∃ k : ℕ, orderOf x = 2 ^ k} ≤ P.subgroupOf K :=
      (closure_le _).mpr fun x hx => hmem x hx
    exact mem_subgroupOf.mp (hle hgT)
  ·
    exfalso
    apply hJK
    intro j hj
    refine ⟨hPK (hJP hj), fun k hk => ?_⟩
    have hKmem : ∀ k : K, (k : G)⁻¹ * j⁻¹ * k * j ∈ K := fun k =>
      (mem_inf.mp (hcomm k k.2 j hj)).1
    have hc : ∀ k : K, π ⟨(k : G)⁻¹ * j⁻¹ * k * j, hKmem k⟩ ∈ center (↥K ⧸ pPrimeCore 2 ↥K) :=
      fun k => hcen (mem_map_of_mem π (mem_subgroupOf.mpr (hcomm k k.2 j hj)))
    let f : K →* center (↥K ⧸ pPrimeCore 2 ↥K) :=
      { toFun := fun k => ⟨π ⟨(k : G)⁻¹ * j⁻¹ * k * j, hKmem k⟩, hc k⟩
        map_one' := by
          apply Subtype.ext
          change π ⟨((1 : K) : G)⁻¹ * j⁻¹ * ((1 : K) : G) * j, hKmem 1⟩ = 1
          have e : (⟨((1 : K) : G)⁻¹ * j⁻¹ * ((1 : K) : G) * j, hKmem 1⟩ : K) = 1 :=
            Subtype.ext (by simp)
          rw [e, map_one]
        map_mul' := by
          intro k₁ k₂
          apply Subtype.ext
          change π ⟨((k₁ * k₂ : K) : G)⁻¹ * j⁻¹ * ((k₁ * k₂ : K) : G) * j, hKmem (k₁ * k₂)⟩ =
            π ⟨(k₁ : G)⁻¹ * j⁻¹ * k₁ * j, hKmem k₁⟩ * π ⟨(k₂ : G)⁻¹ * j⁻¹ * k₂ * j, hKmem k₂⟩
          have e : (⟨((k₁ * k₂ : K) : G)⁻¹ * j⁻¹ * ((k₁ * k₂ : K) : G) * j, hKmem (k₁ * k₂)⟩ :
              K) = k₂⁻¹ * ⟨(k₁ : G)⁻¹ * j⁻¹ * k₁ * j, hKmem k₁⟩ * k₂ *
                ⟨(k₂ : G)⁻¹ * j⁻¹ * k₂ * j, hKmem k₂⟩ := by
            apply Subtype.ext
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
          rw [e, map_mul, map_mul, map_mul, map_inv]
          have hcm := mem_center_iff.mp (hc k₁) (π k₂)
          rw [mul_assoc (π k₂)⁻¹, ← hcm, ← mul_assoc, inv_mul_cancel, one_mul] }
    have hperf : commutator K = ⊤ :=
      Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr
        (UnbalancedCorr.commutator_eq_of_isPComponent hK.1 hK.2))
    have hf : f ⟨k, hk⟩ = 1 :=
      MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker f (by rw [hperf]; trivial))
    have h1 : π ⟨k⁻¹ * j⁻¹ * k * j, hKmem ⟨k, hk⟩⟩ = 1 := congrArg Subtype.val hf
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩

theorem isTwoComponentIn_conjClosure_of_not_le {C K J : Subgroup G}
    (hK : IsTwoComponentIn K C) (hJL : J ≤ twoLayerIn C) (hJK : ¬ J ≤ coreActionKernel K) :
    IsTwoComponentIn K (conjClosure J (twoLayerIn C)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKP := le_conjClosure_of_not_le_coreActionKernel hK hJL hJK
  have hPC : conjClosure J (twoLayerIn C) ≤ C :=
    (Sol78.conjClosure_le hJL le_normalizer).trans (map_subtype_le _)
  exact ⟨hKP, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hKP hPC hK.2⟩

theorem mul_eq_of_card {w d o a z c k : ℕ} (hw : w * d = a * o * c) (hdo : d ∣ o) (ho : Odd o)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (hk : k = a * z * c) (hz0 : 0 < z) (hz : z ≤ 2)
    (hwk : w ∣ k) : w * z = k := by
  obtain ⟨m, rfl⟩ := hdo
  have hw' : w = a * m * c := by
    have h : w * d = (a * m * c) * d := by rw [hw]; ring
    exact Nat.eq_of_mul_eq_mul_right hd h
  have hm : Odd m := (Nat.odd_mul.mp ho).2
  have hmz : m ∣ z := by
    rw [hw', hk] at hwk
    have h : m * (a * c) ∣ z * (a * c) := by
      have e1 : a * m * c = m * (a * c) := by ring
      have e2 : a * z * c = z * (a * c) := by ring
      rwa [e1, e2] at hwk
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.mul_pos ha hc) h
  have hm1 : m = 1 := by
    have hmle : m ≤ 2 := (Nat.le_of_dvd hz0 hmz).trans hz
    obtain ⟨r, hr⟩ := hm
    omega
  subst hm1
  rw [hw', hk]
  ring

theorem sup_oddCoreIn_eq_of_le {J K : Subgroup G} (hJK : J ≤ K) (hK : ⁅K, K⁆ = K) {n : ℕ}
    (eK : K ⧸ Open.fusionZStar K ≃* alternatingGroup (Fin n))
    (hZ : Nat.card (center (↥K ⧸ pPrimeCore 2 ↥K)) ≤ 2)
    (eJ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) : J ⊔ oddCoreIn K = K := by
  set O := oddCoreIn K with hO
  have hOK : O ≤ K := map_subtype_le _
  have hWK : J ⊔ O ≤ K := sup_le hJK hOK
  have hJO : J ≤ normalizer (O : Set G) :=
    hJK.trans (le_normalizer_map_subtype' (pPrimeCore 2 ↥K))
  have hOcard : Nat.card O = Nat.card (pPrimeCore 2 ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hcardW := Sol78.card_sup_mul_card_inf' hJO
  have hcardJ : Nat.card J = Nat.card (alternatingGroup (Fin n)) * Nat.card (pPrimeCore 2 ↥J) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J),
      Nat.card_congr eJ.toEquiv]
  have hdvd : Nat.card ↥(J ⊓ O) ∣ Nat.card (pPrimeCore 2 ↥J) := by
    have h1 : O ⊓ J ≤ oddCoreIn J := inf_le_oddCoreIn (coprime_card_oddCoreIn K) hJO
    rw [inf_comm] at h1
    have h2 := Subgroup.card_dvd_of_le h1
    rwa [oddCoreIn, Subgroup.card_map_of_injective J.subtype_injective] at h2
  have hcardK : Nat.card K = Nat.card (alternatingGroup (Fin n)) *
      Nat.card (center (↥K ⧸ pPrimeCore 2 ↥K)) * Nat.card O := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K), hOcard,
      Subgroup.card_eq_card_quotient_mul_card_subgroup (center (↥K ⧸ pPrimeCore 2 ↥K)),
      Nat.card_congr ((Sol78.coreQuotientCenterEquiv K).trans eK).toEquiv]
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥J)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥J))
  rw [hcardJ] at hcardW
  have hzpos : 0 < Nat.card (center (↥K ⧸ pPrimeCore 2 ↥K)) := Nat.card_pos
  have hkey := mul_eq_of_card hcardW hdvd hodd Nat.card_pos Nat.card_pos Nat.card_pos hcardK
    hzpos hZ (Subgroup.card_dvd_of_le hWK)
  rcases (show Nat.card (center (↥K ⧸ pPrimeCore 2 ↥K)) = 1 ∨
      Nat.card (center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 by omega) with h1 | h2
  · rw [h1, mul_one] at hkey
    exact Subgroup.eq_of_le_of_card_ge hWK hkey.ge
  ·
    exfalso
    set W := (J ⊔ O).subgroupOf K with hW
    have hWcard : Nat.card W = Nat.card ↥(J ⊔ O) :=
      Nat.card_congr (subgroupOfEquivOfLe hWK).toEquiv
    have hidx : W.index = 2 := by
      have h := W.card_mul_index
      rw [hWcard, ← hkey, h2] at h
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
    have hperf : commutator K = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hK)
    have hle : commutator K ≤ W := by
      rw [commutator_eq_closure, closure_le]
      rintro _ ⟨p, q, rfl⟩
      rw [commutatorElement_def, SetLike.mem_coe, mul_mem_iff_of_index_two hidx,
        mul_mem_iff_of_index_two hidx, mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
      tauto
    rw [hperf, top_le_iff] at hle
    rw [hle, index_top] at hidx
    omega

end CFSG.ComponentClassification.Sol76
