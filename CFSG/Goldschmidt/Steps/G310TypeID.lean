module

public import CFSG.Goldschmidt.Steps.G310TypeI
public import CFSG.Goldschmidt.Steps.AxB

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)

section Transport

variable {X : Type*} [Group X]

theorem fusionIsSylowIn_subgroupOf {p : ℕ} {T L N : Subgroup X} (h : fusionIsSylowIn p T L)
    (hLN : L ≤ N) : fusionIsSylowIn p (T.subgroupOf N) (L.subgroupOf N) := by
  obtain ⟨hTL, hT, hmax⟩ := h
  refine ⟨fun x hx => hTL hx, hT.comap_subtype, fun Q hQ hQp hTQ => ?_⟩
  have hQL : Q.map N.subtype ≤ L := by
    rintro _ ⟨q, hq, rfl⟩
    exact hQ hq
  have hTQ' : T ≤ Q.map N.subtype := fun t ht =>
    ⟨⟨t, hLN (hTL ht)⟩, hTQ (show (⟨t, hLN (hTL ht)⟩ : N) ∈ T.subgroupOf N from ht), rfl⟩
  have h1 := hmax _ hQL (hQp.map _) hTQ'
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective N.subtype_injective Q).symm

theorem normalClosureIn_subgroupOf {L B N : Subgroup X} (hLN : L ≤ N) :
    normalClosureIn (L.subgroupOf N) (B.subgroupOf N) = (normalClosureIn L B).subgroupOf N := by
  set e : L.subgroupOf N ≃* L := Subgroup.subgroupOfEquivOfLe hLN with he
  have heS : (e : L.subgroupOf N → L) ⁻¹'
      (((B.subgroupOf L : Subgroup L)) : Set L) =
      (((B.subgroupOf N).subgroupOf (L.subgroupOf N) : Subgroup (L.subgroupOf N)) : Set _) := by
    ext y
    rfl
  have hcl := Subgroup.comap_normalClosure (((B.subgroupOf L : Subgroup L)) : Set L) e
  rw [heS] at hcl
  ext n
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hcl, SetLike.mem_coe, Subgroup.mem_comap] at hy
    exact ⟨e y, hy, rfl⟩
  · rintro ⟨y, hy, hyn⟩
    have hyn' : (y : X) = (n : X) := hyn
    have hnL : n ∈ L.subgroupOf N := by
      show (n : X) ∈ L
      rw [← hyn']
      exact y.2
    refine ⟨⟨n, hnL⟩, ?_, rfl⟩
    rw [hcl, SetLike.mem_coe, Subgroup.mem_comap]
    have : e ⟨n, hnL⟩ = y := Subtype.ext hyn'.symm
    change e ⟨n, hnL⟩ ∈ _
    rw [this]
    exact hy

end Transport

section Unique

variable {M : Type} [Group M] [Finite M]

theorem eq_of_le_sylow {A L : Subgroup M} (hLq : CFSG.Open.IsQuasisimple L)
    {P : Sylow 2 L} {D : Subgroup (L ⧸ Subgroup.center L)}
    (hcl : fusionStronglyClosed (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) (P : Subgroup L))
    (h : G3a.BorelSetup (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L))) D)
    (hmap : ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L)) =
      sylowCenter ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)) :
        Sylow 2 (L ⧸ Subgroup.center L)) : Subgroup (L ⧸ Subgroup.center L)))
    (Q : Sylow 2 L) (hAQ : (A ⊓ L).subgroupOf L ≤ Q) : Q = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hLq.2
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  set P' : Sylow 2 (L ⧸ Subgroup.center L) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hP'def
  have hP' : (P' : Subgroup (L ⧸ Subgroup.center L)) = (P : Subgroup L).map π :=
    Sylow.coe_mapSurjective _ _
  set Z := sylowCenter (P' : Subgroup (L ⧸ Subgroup.center L)) with hZ
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq L P Q
  have hconj : ∀ a ∈ (A ⊓ L).subgroupOf L, g⁻¹ * a * g ∈ (A ⊓ L).subgroupOf L := by
    intro a ha
    refine hcl a ha g ?_
    have h1 := hAQ ha
    rw [Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  have hZN : (π g)⁻¹ ∈ Subgroup.normalizer (Z : Set (L ⧸ Subgroup.center L)) := by
    apply mem_normalizer_of_map_le
    rw [← hmap]
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨g⁻¹ * a * g, hconj a ha, ?_⟩
    simp [π]
  have hPZ : (P' : Subgroup (L ⧸ Subgroup.center L)) ≤ Subgroup.normalizer
      (Z : Set (L ⧸ Subgroup.center L)) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hzc := (mem_sylowCenter.mp hz).2 t ht
      have : t * z * t⁻¹ = z := by rw [hzc]; group
      rw [this]
      exact hz
    · intro hz
      have hzc := (mem_sylowCenter.mp hz).2 t ht
      have h2 : t * (t * z * t⁻¹) = t * z := hzc.trans (by group)
      have h3 : t * z * t⁻¹ = z := mul_left_cancel h2
      rw [← h3]
      exact hz
  have hNne : Subgroup.normalizer (Z : Set (L ⧸ Subgroup.center L)) ≠ ⊤ := by
    intro htop
    have hZn : Z.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Z with hb | ht
    · have := h.four
      rw [← hZ, hb, Subgroup.card_bot] at this
      omega
    · have hPt : (P' : Subgroup (L ⧸ Subgroup.center L)) = ⊤ :=
        top_unique (ht ▸ sylowCenter_le _)
      have hPn : (P' : Subgroup (L ⧸ Subgroup.center L)).Normal := by
        rw [hPt]
        infer_instance
      have := Sylow.unique_of_normal P' hPn
      have h1 := h.card
      rw [Nat.card_unique] at h1
      have h2 := Nat.card_pos (α := (P' : Subgroup (L ⧸ Subgroup.center L)))
      omega
  have hNP := h.le_normalizer_of_le hPZ hNne hZN
  have hgN : g⁻¹ ∈ Subgroup.normalizer ((P : Subgroup L) : Set L) := by
    apply G3a.mem_normalizer_of_map P
    rw [← hP']
    simpa [π] using hNP
  rw [Sylow.smul_eq_iff_mem_normalizer]
  exact (Subgroup.inv_mem_iff _).mp hgN

omit [Finite M] in
theorem eq_one_of_odd_of_mem_two {R T : Subgroup M} [Finite R] (hR : Odd (Nat.card R))
    (hT : IsPGroup 2 T) {x : M} (hxR : x ∈ R) (hxT : x ∈ T) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hT ⟨x, hxT⟩
  have h2 : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h1 : orderOf x ∣ Nat.card R := by
    have := Subgroup.orderOf_dvd_natCard R hxR
    exact this
  have h3 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨i, hi, hix⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  rcases i with _ | i
  · rw [pow_zero, orderOf_eq_one_iff] at hix
    exact hix
  · exfalso
    rw [hix] at h1
    exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr ((dvd_pow_self 2
      (Nat.succ_ne_zero i)).trans h1))

theorem le_centralizer_typeI
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A)
    {L : Subgroup M} (hL : IsComponentOf L (normalClosureIn ⊤ A)) (hI : IsGoldTypeI L)
    {R : Subgroup M} (hRC : R ≤ Subgroup.centralizer (A : Set M))
    (hCR : Subgroup.centralizer (A : Set M) ≤ Subgroup.normalizer (R : Set M))
    (hRodd : Odd (Nat.card R)) : R ≤ Subgroup.centralizer (L : Set M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := compFacts hO hS hL
  obtain ⟨P, D, hAP, hcl, h, hmap⟩ := typeI_data hO hS hL hI
  set T : Subgroup M := (P : Subgroup L).map L.subtype with hT
  have hTL : T ≤ L := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := P.isPGroup'.map _
  have hTsyl : fusionIsSylowIn 2 T L := fusionIsSylowIn_map P
  have hAT : A ⊓ L ≤ T := fun x hx => ⟨⟨x, hx.2⟩, hAP hx, rfl⟩
  have hRN : R ≤ Subgroup.normalizer (L : Set M) := fun d hd =>
    mem_normalizer_of_mem_centralizer hO hS hL (hRC hd)
  have hRT : R ≤ Subgroup.normalizer (T : Set M) := by
    intro d hd
    have hdN := hRN hd
    set φ : MulAut L := L.normalizerMonoidHom ⟨d, hdN⟩ with hφdef
    have hφ : ∀ x : L, ((φ x : L) : M) = d * x * d⁻¹ := fun x =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨d, hdN⟩ x
    have hAQ : (A ⊓ L).subgroupOf L ≤ ((φ • P : Sylow 2 L) : Subgroup L) := by
      intro a ha
      rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have hφa : φ a = a := by
        apply Subtype.ext
        rw [hφ]
        rw [← Subgroup.mem_centralizer_iff.mp (hRC hd) a ha.1]
        group
      have : φ⁻¹ • a = a := by
        rw [MulAut.smul_def, MulAut.inv_apply, MulEquiv.symm_apply_eq, hφa]
      rw [this]
      exact hAP ha
    have hQ := eq_of_le_sylow hL.2.2 hcl h hmap _ hAQ
    apply mem_normalizer_of_map_le
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : φ x ∈ ((φ • P : Sylow 2 L) : Subgroup L) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul x φ _ hx
    rw [hQ] at hx'
    refine ⟨φ x, hx', ?_⟩
    simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hφ x
  have hA2 := isPGroup_two_of_isSStarIn hS
  have hAN : A ≤ Subgroup.normalizer (T : Set M) := by
    apply le_normalizer_of_conj_mem
    intro a ha t ht
    obtain ⟨x, hx, hxact⟩ := exists_act_of_mem_A hO hS hL ha
    have haN : a ∈ Subgroup.normalizer (L : Set M) :=
      mem_normalizer_of_mem hO hS hL (le_normalClosureIn_top A ha)
    rw [conj_eq_of_act haN hxact t (hTL ht)]
    exact T.mul_mem (T.mul_mem (hAT hx) ht) (T.inv_mem (hAT hx))
  have hRA : ⁅R, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRC
  have hcop : Nat.Coprime (Nat.card R) 2 := (Nat.coprime_two_left.mpr hRodd).symm
  have hfix : T ⊓ Subgroup.centralizer (A : Set M) ≤ Subgroup.centralizer (R : Set M) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : t * d * t⁻¹ * d⁻¹ ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hCR ht.2) d).mp hd
      exact R.mul_mem this (R.inv_mem hd)
    have h2 : t * d * t⁻¹ * d⁻¹ ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (hRT hd) t⁻¹).mp (T.inv_mem ht.1)
      have e : t * d * t⁻¹ * d⁻¹ = t * (d * t⁻¹ * d⁻¹) := by group
      rw [e]
      exact T.mul_mem ht.1 this
    have h3 := eq_one_of_odd_of_mem_two hRodd hT2 h1 h2
    calc d * t = (t * d * t⁻¹ * d⁻¹)⁻¹ * t * d := by group
      _ = t * d := by rw [h3, inv_one, one_mul]
  have hTR := N10 M T R A hT2 hcop hA2 hRT hAN hRA hfix
  intro d hd
  set N := Subgroup.normalizer (L : Set M) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hdN : d ∈ N := hRN hd
  have hLn : (L.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hq : CFSG.Open.IsQuasisimple (L.subgroupOf N) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hLN) hL.2.2
  have hI' : IsGoldTypeI (L.subgroupOf N) :=
    SStarTransport.isGoldTypeI_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN).symm hI
  have hS' : IsSStarIn (L.subgroupOf N) ((A ⊓ L).subgroupOf N) :=
    SStarTransport.isSStarIn_subgroupOf hF.sstar hLN
  have hcl' : normalClosureIn (L.subgroupOf N) ((A ⊓ L).subgroupOf N) = L.subgroupOf N := by
    rw [normalClosureIn_subgroupOf hLN, hF.closure]
  have hT' : fusionIsSylowIn 2 (T.subgroupOf N) (L.subgroupOf N) :=
    fusionIsSylowIn_subgroupOf hTsyl hLN
  have hAT' : (A ⊓ L).subgroupOf N ≤ T.subgroupOf N := fun x hx => hAT hx
  have key := G33 N (L.subgroupOf N) ((A ⊓ L).subgroupOf N) (T.subgroupOf N) hLn hq hI' hS' hcl'
    hT' hAT' ⟨d, hdN⟩ (by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hRC hd) a ha.1)) (by
      rw [Subgroup.mem_normalizer_iff]
      intro t
      exact Subgroup.mem_normalizer_iff.mp (hRT hd) t) (by
      intro t ht
      have h1 : (d : M) * t = t * d := Subgroup.mem_centralizer_iff.mp (hTR ht) d hd
      have : (⟨d, hdN⟩ : N)⁻¹ * t * ⟨d, hdN⟩ * t⁻¹ = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
        calc d⁻¹ * (t : M) * d * (t : M)⁻¹ = d⁻¹ * ((t : M) * d) * (t : M)⁻¹ := by group
          _ = d⁻¹ * (d * t) * (t : M)⁻¹ := by rw [h1]
          _ = 1 := by group
      rw [this]
      exact Subgroup.one_mem _)
  have hmem : d ∈ T ⊔ Subgroup.centralizer (L : Set M) := by
    have h1 := Subgroup.mem_map_of_mem N.subtype key
    rw [Subgroup.map_sup] at h1
    have hle : (T.subgroupOf N).map N.subtype ⊔
        (Subgroup.centralizer ((L.subgroupOf N : Subgroup N) : Set N)).map N.subtype ≤
        T ⊔ Subgroup.centralizer (L : Set M) := by
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hx
      · rintro _ ⟨c, hc, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have := Subgroup.mem_centralizer_iff.mp hc ⟨y, hLN hy⟩ hy
        exact congrArg Subtype.val this
    exact hle h1
  have hTCL : T ≤ Subgroup.normalizer
      ((Subgroup.centralizer (L : Set M) : Subgroup M) : Set M) :=
    (Subgroup.le_centralizer_iff.mpr (Subgroup.centralizer_le hTL)).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨t, ht, c, hc, rfl⟩ := exists_mul_of_mem_sup hTCL hmem
  have htc : t * c = c * t := Subgroup.mem_centralizer_iff.mp hc t (hTL ht)
  set m := orderOf (t * c) with hm
  have hmodd : Odd m := Odd.of_dvd_nat hRodd (Subgroup.orderOf_dvd_natCard R hd)
  have hpow : (t * c) ^ m = t ^ m * c ^ m := (Commute.mul_pow htc m)
  have htm : t ^ m ∈ Subgroup.centralizer (L : Set M) := by
    have h1 : t ^ m * c ^ m = 1 := by rw [← hpow, hm, pow_orderOf_eq_one]
    have h2 : t ^ m = (c ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc m)
  have htz : t ∈ Subgroup.zpowers (t ^ m) := by
    rw [mem_zpowers_pow_iff]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨t, ht⟩
    have hk' : orderOf t = 2 ^ k := by rw [← Subgroup.orderOf_mk t ht]; exact hk
    rw [hk']
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hmodd)
  have htC : t ∈ Subgroup.centralizer (L : Set M) := Subgroup.zpowers_le.mpr htm htz
  exact Subgroup.mul_mem _ htC hc

end Unique

end CFSG.Goldschmidt.G310
