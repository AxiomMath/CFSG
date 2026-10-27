module

public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

namespace BenderStart

section OddCore

variable {G : Type*} [Group G]

private theorem oddCoreIn_le (H : Subgroup G) : oddCoreIn H ≤ H :=
  Subgroup.map_subtype_le _

private theorem le_normalizer_map_subtype (H : Subgroup G) (K : Subgroup H) [K.Normal] :
    H ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, Subgroup.Normal.conj_mem inferInstance k hk ⟨h, hh⟩, rfl⟩
  · rintro ⟨k, hk, hkg⟩
    refine ⟨⟨h, hh⟩⁻¹ * k * ⟨h, hh⟩, ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem (inferInstance : K.Normal) k hk ⟨h, hh⟩⁻¹
      simpa using this
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hkg ⊢
      rw [hkg]
      group

private theorem le_normalizer_oddCoreIn (H : Subgroup G) :
    H ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
  le_normalizer_map_subtype H (fusionOddCore H)

private theorem odd_card_oddCoreIn [Finite G] (H : Subgroup G) :
    Odd (Nat.card (oddCoreIn H)) := by
  rw [oddCoreIn, Nat.card_congr ((fusionOddCore H).equivMapOfInjective H.subtype
    H.subtype_injective).toEquiv.symm]
  exact CFSG.ComponentClassification.OddCore.odd_card_sSup _ (Set.toFinite _)
    (fun _ hmem => hmem.1) (fun _ hmem => hmem.2)

private theorem le_oddCoreIn {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreIn H := by
  have hnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnorm
  have hodd' : Odd (Nat.card (K.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hle : K.subgroupOf H ≤ fusionOddCore H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

private theorem oddCoreIn_inf_eq_bot [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (H : Subgroup G) : oddCoreIn H ⊓ Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (oddCoreIn H)) (Nat.card Q) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr (odd_card_oddCoreIn H))
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

private theorem oddCoreIn_le_centralizer [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    oddCoreIn (Subgroup.normalizer (Q : Set G)) ≤ Subgroup.centralizer (Q : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hr' : r ∈ Subgroup.normalizer (Q : Set G) := oddCoreIn_le _ hr
  have hq' : q ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hq
  have h1 : q * r * q⁻¹ ∈ oddCoreIn (Subgroup.normalizer (Q : Set G)) :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn _ hq') r).mp hr
  have h2 : q * r * q⁻¹ * r⁻¹ ∈ oddCoreIn (Subgroup.normalizer (Q : Set G)) :=
    Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hr)
  have h3 : q * r * q⁻¹ * r⁻¹ ∈ Q := by
    have := Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp hr' q⁻¹).mp (Q.inv_mem hq))
    simpa [mul_assoc] using this
  have h4 : q * r * q⁻¹ * r⁻¹ ∈ oddCoreIn (Subgroup.normalizer (Q : Set G)) ⊓ Q := ⟨h2, h3⟩
  rw [oddCoreIn_inf_eq_bot hQ] at h4
  have h5 : q * r * q⁻¹ * r⁻¹ = 1 := h4
  calc q * r = q * r * q⁻¹ * r⁻¹ * (r * q) := by group
    _ = r * q := by rw [h5, one_mul]

end OddCore

section Normalizers

variable {G : Type*} [Group G]

private theorem le_normalizer_sup {N X Y : Subgroup G} (hX : N ≤ Subgroup.normalizer (X : Set G))
    (hY : N ≤ Subgroup.normalizer (Y : Set G)) :
    N ≤ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  have key : ∀ n ∈ N, ∀ y ∈ X ⊔ Y, n * y * n⁻¹ ∈ X ⊔ Y := by
    intro n hn
    have hle : X ⊔ Y ≤ (X ⊔ Y).comap (MulAut.conj n).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun y hy => ?_)
      · exact (le_sup_left : X ≤ X ⊔ Y) ((Subgroup.mem_normalizer_iff.mp (hX hn) x).mp hx)
      · exact (le_sup_right : Y ≤ X ⊔ Y) ((Subgroup.mem_normalizer_iff.mp (hY hn) y).mp hy)
    intro y hy
    exact hle hy
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key n hn y, fun h => ?_⟩
  have := key n⁻¹ (N.inv_mem hn) _ h
  simpa [mul_assoc] using this

end Normalizers

section Finite

variable {G : Type*} [Group G] [Finite G]

private theorem exists_mem_conj_mem_of_coprime_relIndex {p : ℕ} [Fact p.Prime]
    {R A B : Subgroup G} (hAp : IsPGroup p A) (hA : Nat.Coprime p (A.relIndex R))
    (hBR : B ≤ R) (hBp : IsPGroup p B) :
    ∃ r ∈ R, ∀ y ∈ B, r⁻¹ * y * r ∈ A := by
  let SA : Sylow p R := (hAp.comap_subtype (K := R)).toSylow
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hA)
  obtain ⟨X, hX⟩ := (hBp.comap_subtype (K := R)).exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R X SA
  refine ⟨((r⁻¹ : R) : G), (r⁻¹ : R).2, fun y hy => ?_⟩
  have hmem : MulAut.conj r • (⟨y, hBR hy⟩ : R) ∈ ((r • X : Sylow p R) : Subgroup R) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _
      (hX (show (⟨y, hBR hy⟩ : R) ∈ B.comap R.subtype from hy))
  rw [hr] at hmem
  have hA' : ((MulAut.conj r • (⟨y, hBR hy⟩ : R) : R) : G) ∈ A := hmem
  simpa [MulAut.smul_def, MulAut.conj_apply] using hA'

private theorem relIndex_dvd_relIndex_of_le_normalizer {T R N : Subgroup G}
    (hTN : T ≤ N) (hRN : R ≤ N) (hNR : N ≤ (Subgroup.normalizer (R : Set G))) :
    T.relIndex R ∣ T.relIndex N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer (hTN.trans hNR)
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer (hTN.trans hNR)
  have hsecond : R.relIndex T = R.relIndex (T ⊔ R) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T R
      (hTN.trans hNR)).toEquiv
  have e1 := Subgroup.relIndex_mul_relIndex (R ⊓ T) T N inf_le_right hTN
  have e2 := Subgroup.relIndex_mul_relIndex (R ⊓ T) R N inf_le_left hRN
  have e3 := Subgroup.relIndex_mul_relIndex R (T ⊔ R) N le_sup_right (sup_le hTN hRN)
  rw [Subgroup.inf_relIndex_right] at e1
  rw [Subgroup.inf_relIndex_left] at e2
  have hne : R.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨(T ⊔ R).relIndex N, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) ?_⟩
  rw [e1, ← e2, ← e3, hsecond]
  ring

private theorem exists_subgroup_odd_elements {Γ : Type*} [Group Γ] [Finite Γ] (P : Subgroup Γ)
    (hP : IsPGroup 2 P) (hcentral : P ≤ Subgroup.center Γ) (hodd : ¬ 2 ∣ P.index) :
    ∃ K : Subgroup Γ, (∀ k : Γ, k ∈ K ↔ Odd (orderOf k)) ∧ P ⊔ K = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormal : P.Normal := Subgroup.normal_of_le_center hcentral
  have hcop : Nat.Coprime (Nat.card P) P.index := by
    obtain ⟨a, ha⟩ := hP.exists_card_eq
    rw [ha]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKcard : Nat.card K = P.index := hK.symm.index_eq_card.symm
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact Nat.odd_iff.mpr (by omega)
  refine ⟨K, fun k => ⟨fun hk => ?_, fun hk => ?_⟩, hK.sup_eq_top⟩
  · have := Subgroup.orderOf_dvd_natCard K hk
    exact Odd.of_dvd_nat hKodd this
  · have hk' : k ∈ P ⊔ K := by rw [hK.sup_eq_top]; exact Subgroup.mem_top k
    obtain ⟨p, hp, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk'
    have hcomm : Commute p z := (Subgroup.mem_center_iff.mp (hcentral hp) z).symm
    obtain ⟨a, ha⟩ := hP ⟨p, hp⟩
    have hpa : p ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    set m := orderOf (p * z) with hm
    have hpm : p ^ m * z ^ m = 1 := by
      rw [← hcomm.mul_pow]; exact pow_orderOf_eq_one _
    have hpmP : p ^ m ∈ P := P.pow_mem hp m
    have hzmK : (z ^ m)⁻¹ ∈ K := K.inv_mem (K.pow_mem hz m)
    have hpeq : p ^ m = (z ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hpm
    have hbot : p ^ m = 1 := by
      have hmem : p ^ m ∈ P ⊓ K := ⟨hpmP, hpeq ▸ hzmK⟩
      rw [disjoint_iff.mp hK.disjoint] at hmem
      exact hmem
    have hp1 : p = 1 := by
      have hdvd1 : orderOf p ∣ m := orderOf_dvd_of_pow_eq_one hbot
      have hdvd2 : orderOf p ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hpa
      have hcop' : Nat.Coprime m (2 ^ a) := Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hk)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' hdvd1 hdvd2)
    rw [hp1, one_mul]
    exact hz

private theorem le_sup_oddCoreIn_of_central_two {C N Z : Subgroup G} (hCN : C ≤ N)
    (hNC : N ≤ Subgroup.normalizer (C : Set G)) (hZ : IsPGroup 2 Z)
    (hcentral : ∀ z ∈ Z, z ∈ C → ∀ c ∈ C, c * z = z * c)
    (hodd : ¬ 2 ∣ (Z.subgroupOf C).index) : C ≤ Z ⊔ oddCoreIn N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPcentral : Z.subgroupOf C ≤ Subgroup.center C := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (hcentral p hp p.2 c c.2)
  obtain ⟨K, hK, hPK⟩ := exists_subgroup_odd_elements (Z.subgroupOf C)
    (hZ.comap_subtype (K := C)) hPcentral hodd
  set K' : Subgroup G := K.map C.subtype with hK'
  have hmemK' : ∀ x : G, x ∈ K' ↔ x ∈ C ∧ Odd (orderOf x) := by
    intro x
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hko : orderOf (k : G) = orderOf k := Subgroup.orderOf_coe k
      exact ⟨k.2, by rw [show C.subtype k = (k : G) from rfl, hko]; exact (hK k).1 hk⟩
    · rintro ⟨hx, hxo⟩
      refine ⟨⟨x, hx⟩, (hK _).2 ?_, rfl⟩
      have hko : orderOf ((⟨x, hx⟩ : C) : G) = orderOf (⟨x, hx⟩ : C) := Subgroup.orderOf_coe _
      rw [← hko]
      exact hxo
  have hK'C : K' ≤ C := fun x hx => ((hmemK' x).1 hx).1
  have hK'odd : Odd (Nat.card K') := by
    by_contra hcon
    have h2 : 2 ∣ Nat.card K' := by
      rcases Nat.even_or_odd (Nat.card K') with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho hcon
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K') 2 h2
    have := ((hmemK' x).1 x.2).2
    rw [Subgroup.orderOf_coe, hx] at this
    exact absurd this (by decide)
  have hnorm : N ≤ Subgroup.normalizer (K' : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hnC : ∀ y, y ∈ C ↔ n * y * n⁻¹ ∈ C := Subgroup.mem_normalizer_iff.mp (hNC hn)
    have hord : orderOf (n * y * n⁻¹) = orderOf y := by
      have := MulEquiv.orderOf_eq (MulAut.conj n) y
      simpa [MulAut.conj_apply] using this
    rw [hmemK', hmemK', ← hnC y, hord]
  have hKR : K' ≤ oddCoreIn N := le_oddCoreIn (hK'C.trans hCN) hnorm hK'odd
  intro c hc
  have hc' : (⟨c, hc⟩ : C) ∈ Z.subgroupOf C ⊔ K := by rw [hPK]; exact Subgroup.mem_top _
  have : c ∈ (Z.subgroupOf C ⊔ K).map C.subtype := ⟨⟨c, hc⟩, hc', rfl⟩
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype] at this
  exact (sup_le_sup inf_le_left hKR) this

open scoped Pointwise in
private theorem exists_relIndex_eq_two_pow {N A Q' : Subgroup G} (hQ'N : Q' ≤ N) (hAN : A ≤ N)
    (hNA : N ≤ Subgroup.normalizer (A : Set G)) (hx : ∀ x ∈ Q', ∃ k : ℕ, x ^ 2 ^ k ∈ A) :
    ∃ k : ℕ, (A.subgroupOf (Q' ⊔ A)).index = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R' := Q' ⊔ A with hR'
  have hAR' : A ≤ R' := le_sup_right
  have hR'N : R' ≤ N := sup_le hQ'N hAN
  have hnormal : (A.subgroupOf R').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAR').mpr (hR'N.trans hNA)
  have hQ'A : Q' ≤ Subgroup.normalizer (A : Set G) := hQ'N.trans hNA
  have hpg : IsPGroup 2 (R' ⧸ A.subgroupOf R') := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hg : (g : G) ∈ ((Q' : Set G) * (A : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right Q' A hQ'A]
        exact g.2
      obtain ⟨x, hxQ, a, haA, hxa⟩ := hg
      obtain ⟨k, hk⟩ := hx x hxQ
      refine ⟨k, ?_⟩
      have hxR : x ∈ R' := (le_sup_left : Q' ≤ Q' ⊔ A) hxQ
      have hmk : (QuotientGroup.mk ⟨x, hxR⟩ : R' ⧸ A.subgroupOf R') = QuotientGroup.mk g := by
        rw [QuotientGroup.eq]
        rw [Subgroup.mem_subgroupOf]
        have : (((⟨x, hxR⟩ : R')⁻¹ * g : R') : G) = a := by
          have hxa' : x * a = (g : G) := hxa
          rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hxa']
          exact inv_mul_cancel_left x a
        rw [this]
        exact haA
      rw [← hmk, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show (⟨x, hxR⟩ ^ 2 ^ k : R') ∈ A.subgroupOf R'
      rw [Subgroup.mem_subgroupOf]
      simpa using hk
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  exact ⟨n, hn⟩

end Finite

section Sylow

variable {G : Type*} [Group G]

theorem isPGroup_zpowers_of_pow_eq_one {x : G} {k : ℕ} (h : x ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers]; exact hi)

private theorem coprime_relIndex_of_isSylowTwoOf {T M : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hTM : T ≤ M) : Nat.Coprime 2 (T.relIndex M) := by
  have hT2 : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
    (fun h => hT2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTM)))

variable [Finite G]

theorem exists_mem_conj_mem_of_isSylowTwoOf {T M B : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hTM : T ≤ M) (hBM : B ≤ M) (hB : IsPGroup 2 B) :
    ∃ m ∈ M, ∀ y ∈ B, m⁻¹ * y * m ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_mem_conj_mem_of_coprime_relIndex hT.2.1 (coprime_relIndex_of_isSylowTwoOf hT hTM)
    hBM hB

theorem le_of_normal_isPGroup {T M U : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hTM : T ≤ M)
    (hUM : U ≤ M) (hUn : (U.subgroupOf M).Normal) (hU : IsPGroup 2 U) : U ≤ T := by
  obtain ⟨r, hr, hrU⟩ := exists_mem_conj_mem_of_isSylowTwoOf hT hTM hUM hU
  have hMU : M ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).mp hUn
  intro y hy
  have h1 : r * y * r⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hMU hr) y).mp hy
  have h2 := hrU _ h1
  simpa [mul_assoc] using h2

end Sylow

end BenderStart

variable {G : Type*} [Group G] [Finite G]

theorem isAGMember_of_isAlperinSubgroup {T Q : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hQ : CFSG.RankTwoShapes.IsAlperinSubgroup 2 T Q) (hQ1 : Q ≠ ⊥) : IsAGMember T Q := by
  obtain ⟨hQT, hcop, hCT, hrad⟩ := hQ
  have hTp : IsPGroup 2 T := hT.2.1
  have hQp : IsPGroup 2 Q := hTp.to_le hQT
  have hCN : Subgroup.centralizer (Q : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hNC : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer Q
  have hRC := BenderStart.oddCoreIn_le_centralizer hQp
  have hRQ := BenderStart.oddCoreIn_inf_eq_bot hQp (Subgroup.normalizer (Q : Set G))
  have hcentralZ : ∀ z ∈ T ⊓ Subgroup.centralizer (Q : Set G),
      z ∈ Subgroup.centralizer (Q : Set G) →
      ∀ c ∈ Subgroup.centralizer (Q : Set G), c * z = z * c := by
    intro z hz _ c hc
    exact (Subgroup.mem_centralizer_iff.mp hc z (hCT ⟨hz.2, hz.1⟩)).symm
  have hoddIdx : ¬ 2 ∣ ((T ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf
      (Subgroup.centralizer (Q : Set G))).index := by
    have hdvd := BenderStart.relIndex_dvd_relIndex_of_le_normalizer
      (T := T ⊓ Subgroup.normalizer (Q : Set G)) inf_le_right hCN hNC
    have heq : (T ⊓ Subgroup.normalizer (Q : Set G)).relIndex
        (Subgroup.centralizer (Q : Set G)) =
        ((T ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf
          (Subgroup.centralizer (Q : Set G))).index := by
      unfold Subgroup.relIndex
      congr 1
      ext g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1, g.2⟩, fun h => ⟨h.1, hCN g.2⟩⟩
    rw [← heq]
    intro h2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop (h2.trans hdvd)
  have hZQ : T ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
    rw [inf_comm]; exact hCT
  have hCRQ : Subgroup.centralizer (Q : Set G) ≤
      oddCoreIn (Subgroup.normalizer (Q : Set G)) ⊔ Q := by
    have h := BenderStart.le_sup_oddCoreIn_of_central_two hCN hNC hTp.to_inf_left hcentralZ
      hoddIdx
    rw [sup_comm] at h
    exact h.trans (sup_le_sup_left hZQ _)
  have hi : ∀ Q' : Subgroup G, oddCoreIn (Subgroup.normalizer (Q : Set G)) ≤ Q' →
      Q' ≤ Subgroup.normalizer (Q : Set G) →
      (Q'.subgroupOf (Subgroup.normalizer (Q : Set G))).Normal →
      (∀ x ∈ Q', ∃ k : ℕ, x ^ 2 ^ k ∈ oddCoreIn (Subgroup.normalizer (Q : Set G))) →
      Q' ≤ oddCoreIn (Subgroup.normalizer (Q : Set G)) ⊔ Q := by
    intro Q' _ hQ'N hQ'n hx
    have hNQ' : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Q' : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQ'N).mp hQ'n
    have hAN : Q ⊔ Subgroup.centralizer (Q : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
      sup_le Subgroup.le_normalizer hCN
    have hNA : Subgroup.normalizer (Q : Set G) ≤
        Subgroup.normalizer ((Q ⊔ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) :=
      BenderStart.le_normalizer_sup le_rfl hNC
    have hRA : oddCoreIn (Subgroup.normalizer (Q : Set G)) ≤
        Q ⊔ Subgroup.centralizer (Q : Set G) :=
      hRC.trans le_sup_right
    obtain ⟨k, hk⟩ := BenderStart.exists_relIndex_eq_two_pow hQ'N hAN hNA
      (fun x hx' => (hx x hx').imp fun k hk => hRA hk)
    have heq := hrad (Q' ⊔ (Q ⊔ Subgroup.centralizer (Q : Set G))) le_sup_right
      (sup_le hQ'N hAN) (BenderStart.le_normalizer_sup hNQ' hNA) ⟨k, hk⟩
    have hQ'A : Q' ≤ Q ⊔ Subgroup.centralizer (Q : Set G) := le_sup_left.trans heq.le
    exact hQ'A.trans (sup_le le_sup_right hCRQ)
  exact ⟨hQT, hQ1, ⟨inf_le_right, hTp.to_inf_left,
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop⟩, hi, hCRQ, hRC, hRQ⟩

open scoped Pointwise in
theorem IsAGMember.center_le {T D : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hD : IsAGMember T D) :
    T ⊓ Subgroup.centralizer (T : Set G) ≤ D := by
  obtain ⟨hDT, hD1, hsyl, hi, hCD, hRC, hRD⟩ := hD
  intro z hz
  have hzC : z ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_iff.mp hz.2 d (hDT hd)
  have hRN : oddCoreIn (Subgroup.normalizer (D : Set G)) ≤ Subgroup.normalizer (D : Set G) :=
    BenderStart.oddCoreIn_le _
  have hzRD : z ∈ ((oddCoreIn (Subgroup.normalizer (D : Set G)) : Set G) * (D : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRN]
    exact hCD hzC
  obtain ⟨r, hr, d, hd, hrd⟩ := hzRD
  have hrd' : r * d = z := hrd
  have hrT : r ∈ T := by
    have : r = z * d⁻¹ := by
      rw [← hrd', mul_inv_cancel_right]
    rw [this]
    exact T.mul_mem hz.1 (T.inv_mem (hDT hd))
  have hr1 : r = 1 := by
    have hmem : r ∈ oddCoreIn (Subgroup.normalizer (D : Set G)) ⊓ T := ⟨hr, hrT⟩
    rw [BenderStart.oddCoreIn_inf_eq_bot hT.2.1 _] at hmem
    exact hmem
  rw [← hrd', hr1, one_mul]
  exact hd

theorem IsAGMember.charTwo (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G)
    {T D : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hD : IsAGMember T D) :
    CharTwo (Subgroup.normalizer (D : Set G)) := by
  have hZ := hD.center_le hT
  have hDT : D ≤ T := hD.1
  have hD1 : D ≠ ⊥ := hD.2.1
  refine charTwo_normalizer_of_inf_center hev hT (hT.2.1.to_le hDT) ?_
  rw [inf_eq_right.mpr hZ]
  intro hbot
  have hnt : Nontrivial T := by
    obtain ⟨d, hd⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hD1
    refine ⟨⟨⟨d, hDT d.2⟩, 1, fun h => hd ?_⟩⟩
    have h' : (d : G) = 1 := congrArg (fun x : T => (x : G)) h
    exact Subtype.ext h'
  have hcn : Nontrivial (Subgroup.center T) := hT.2.1.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center T)
  have hzmem : ((z : T) : G) ∈ T ⊓ Subgroup.centralizer (T : Set G) := by
    refine ⟨(z : T).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.2) ⟨h, hh⟩)
  rw [hbot] at hzmem
  apply hz
  apply Subtype.ext
  apply Subtype.ext
  exact Subgroup.mem_bot.mp hzmem

theorem normalizer_le_of_forall_not_isEscaping
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T M D : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hTM : T ≤ M) (hδ : ∀ D : Subgroup G, ¬ IsEscaping M D)
    (hD : IsAGMember T D) : Subgroup.normalizer (D : Set G) ≤ M := by
  by_contra hnot
  exact hδ D ⟨hD.1.trans hTM, hD.2.1, hT.2.1.to_le hD.1, hD.charTwo hev hT, hnot⟩

private theorem mem_of_alperinDecomposition {T M P : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hAG : ∀ D : Subgroup G, IsAGMember T D → Subgroup.normalizer (D : Set G) ≤ M)
    (hP : P ≠ ⊥) {c : G} (h : CFSG.RankTwoShapes.AlperinDecomposition 2 T P c) : c ∈ M := by
  induction h with
  | one => exact M.one_mem
  | @step c n Q _ hQ hPQ hn ih =>
    have hQ1 : Q ≠ ⊥ := by
      intro hQ0
      apply hP
      rw [hQ0, le_bot_iff] at hPQ
      exact (Subgroup.map_eq_bot_iff_of_injective P (MulAut.conj c⁻¹).injective).mp hPQ
    exact M.mul_mem ih (hAG Q (isAGMember_of_isAlperinSubgroup hT hQ hQ1) hn)

private theorem exists_conj_eq_of_mem_sylow {T M : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hAG : ∀ D : Subgroup G, IsAGMember T D → Subgroup.normalizer (D : Set G) ≤ M)
    {x g : G} (hx : x ∈ T) (hxg : g⁻¹ * x * g ∈ T) :
    ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hx1 : x = 1
  · exact ⟨1, M.one_mem, by rw [hx1]; group⟩
  · have hT2 : ¬ 2 ∣ T.index := by
      rw [← Subgroup.relIndex_top_right]
      exact hT.2.2
    let S : Sylow 2 G := hT.2.1.toSylow hT2
    have hP : Subgroup.zpowers x ≤ (S : Subgroup G) := Subgroup.zpowers_le.2 hx
    have hxg' : g⁻¹ * x * g ∈ (S : Subgroup G) := hxg
    have hPg : (Subgroup.zpowers x).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
      rw [MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.2 (by simpa using hxg')
    obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hP hPg
    have hPne : Subgroup.zpowers x ≠ ⊥ := by
      intro h
      apply hx1
      have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    exact ⟨c, mem_of_alperinDecomposition hT hAG hPne hc,
      (hcg x (Subgroup.mem_zpowers x)).symm⟩

theorem exists_conj_eq_of_ag {T M : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hTM : T ≤ M)
    (hAG : ∀ D : Subgroup G, IsAGMember T D → Subgroup.normalizer (D : Set G) ≤ M)
    {x g : G} (hx : x ∈ M) (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) (hxg : g⁻¹ * x * g ∈ M) :
    ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m := by
  obtain ⟨k, hk⟩ := hx2
  have hy2 : (g⁻¹ * x * g) ^ 2 ^ k = 1 := by
    have := conj_pow (a := g⁻¹) (b := x) (i := 2 ^ k)
    simp only [inv_inv] at this
    rw [this, hk]
    group
  obtain ⟨m₁, hm₁, h₁⟩ := BenderStart.exists_mem_conj_mem_of_isSylowTwoOf hT hTM
    (Subgroup.zpowers_le.2 hx) (BenderStart.isPGroup_zpowers_of_pow_eq_one hk)
  obtain ⟨m₂, hm₂, h₂⟩ := BenderStart.exists_mem_conj_mem_of_isSylowTwoOf hT hTM
    (Subgroup.zpowers_le.2 hxg) (BenderStart.isPGroup_zpowers_of_pow_eq_one hy2)
  have hx₁ : m₁⁻¹ * x * m₁ ∈ T := h₁ x (Subgroup.mem_zpowers x)
  have hy₁ : m₂⁻¹ * (g⁻¹ * x * g) * m₂ ∈ T := h₂ _ (Subgroup.mem_zpowers _)
  have hconj : (m₁⁻¹ * g * m₂)⁻¹ * (m₁⁻¹ * x * m₁) * (m₁⁻¹ * g * m₂) ∈ T := by
    have : (m₁⁻¹ * g * m₂)⁻¹ * (m₁⁻¹ * x * m₁) * (m₁⁻¹ * g * m₂) =
        m₂⁻¹ * (g⁻¹ * x * g) * m₂ := by group
    rw [this]; exact hy₁
  obtain ⟨m₃, hm₃, h₃⟩ := exists_conj_eq_of_mem_sylow hT hAG hx₁ hconj
  refine ⟨m₁ * m₃ * m₂⁻¹, M.mul_mem (M.mul_mem hm₁ hm₃) (M.inv_mem hm₂), ?_⟩
  have h₄ : m₂⁻¹ * (g⁻¹ * x * g) * m₂ = m₃⁻¹ * (m₁⁻¹ * x * m₁) * m₃ := by
    rw [← h₃]; group
  calc g⁻¹ * x * g = m₂ * (m₂⁻¹ * (g⁻¹ * x * g) * m₂) * m₂⁻¹ := by group
    _ = m₂ * (m₃⁻¹ * (m₁⁻¹ * x * m₁) * m₃) * m₂⁻¹ := by rw [h₄]
    _ = (m₁ * m₃ * m₂⁻¹)⁻¹ * x * (m₁ * m₃ * m₂⁻¹) := by group

theorem stronglyClosed_of_ag {T M U : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hTM : T ≤ M)
    (hAG : ∀ D : Subgroup G, IsAGMember T D → Subgroup.normalizer (D : Set G) ≤ M)
    (hUM : U ≤ M) (hUn : (U.subgroupOf M).Normal) (hU : IsPGroup 2 U) :
    U ≤ T ∧ fusionStronglyClosed (U : Set G) T := by
  refine ⟨BenderStart.le_of_normal_isPGroup hT hTM hUM hUn hU, ?_⟩
  intro a ha g hag
  have hMU : M ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).mp hUn
  obtain ⟨k, hk⟩ := hU ⟨a, ha⟩
  have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm, hmeq⟩ := exists_conj_eq_of_ag hT hTM hAG (hUM ha) ⟨k, hk'⟩ (hTM hag)
  rw [hmeq]
  have := (Subgroup.mem_normalizer_iff.mp (hMU (M.inv_mem hm)) a).mp ha
  simpa using this

end CFSG.QuasithinUnique
