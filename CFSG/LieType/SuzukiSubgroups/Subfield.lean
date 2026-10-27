module

public import CFSG.LieType.SuzukiSubgroups.Facts
public import CFSG.LieType.SuzukiSubgroups.Generic
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.Quasithin.Vol2.Ch11SecA02Arith
public import CFSG.Quasithin.Background.F918Z4c1Sz

public section

namespace CFSG.LieType.SuzukiSubgroups

open CFSG.Open Subgroup

variable {n : ℕ} {H : Type} [Group H] [Finite H]

private lemma isPGroup_centralizer_subgroup (hH : CFSG.Quasithin.IsSz n H)
    {U : Subgroup H} {z : H} (hzU : z ∈ U) (hz : orderOf z = 2) :
    IsPGroup 2 (Subgroup.centralizer ({⟨z, hzU⟩} : Set ↥U)) := by
  have hzUord : orderOf (U.subtype ⟨z, hzU⟩) = 2 := by
    simpa using hz
  have hC := isPGroup_centralizer_of_isSz (n := n) (H := H) hH hzUord
  have heq : Subgroup.centralizer ({⟨z, hzU⟩} : Set ↥U) =
      (Subgroup.centralizer ({(U.subtype ⟨z, hzU⟩)} : Set H)).subgroupOf U := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      simpa using congrArg U.subtype hx
    · intro hx
      exact U.subtype_injective (by simpa using hx)
  rw [heq]
  exact hC.comap_of_injective U.subtype U.subtype_injective

private lemma exists_central_involution_map_sylow
    {U : Subgroup H} {N : Subgroup ↥U} {a : ℕ} (ha : 1 ≤ a) (e : ↥N ≃* ↥(Sz a))
    (P : Sylow 2 ↥N) :
    let T : Subgroup ↥U := (P : Subgroup ↥N).map N.subtype
    Nat.card ((Subgroup.center T).map T.subtype) = 2 ^ (2 * a + 1) ∧
      ∃ z ∈ (Subgroup.center T).map T.subtype, z ≠ 1 ∧ orderOf z = 2 ∧
        T ≤ Subgroup.centralizer ({z} : Set ↥U) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNsz : CFSG.Quasithin.IsSz (2 * a + 1) ↥N := isSz_of_mulEquiv ha e
  let T : Subgroup ↥U := (P : Subgroup ↥N).map N.subtype
  have hB := fusionBenderBorel_of_isSz (n := 2 * a + 1) (H := ↥N) hNsz
  have hcenterP : Nat.card (Subgroup.center (P : Subgroup ↥N)) = 2 ^ (2 * a + 1) :=
    (hB P).2.2.2.1
  have hexpP : ∀ z ∈ Subgroup.center (P : Subgroup ↥N), z ^ 2 = 1 := (hB P).2.2.1
  let ePT : ↥(P : Subgroup ↥N) ≃* ↥T :=
    Subgroup.equivMapOfInjective (P : Subgroup ↥N) N.subtype N.subtype_injective
  have hcenterT : Nat.card (Subgroup.center T) = 2 ^ (2 * a + 1) := by
    calc Nat.card (Subgroup.center T)
        = Nat.card (Subgroup.center (P : Subgroup ↥N)) :=
          (Nat.card_congr (Subgroup.centerCongr ePT).toEquiv).symm
      _ = 2 ^ (2 * a + 1) := hcenterP
  have hZcard : Nat.card ((Subgroup.center T).map T.subtype) = 2 ^ (2 * a + 1) := by
    rw [Subgroup.card_map_of_injective T.subtype_injective]
    exact hcenterT
  have hq0gt : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_pow (by omega) (by norm_num)
  have hcenterP_ne_bot : Subgroup.center (P : Subgroup ↥N) ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot _).mp (by rw [hcenterP]; exact hq0gt)
  obtain ⟨z0, hz0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenterP_ne_bot
  let zT : ↥T := ePT z0.1
  have hzTcenter : zT ∈ Subgroup.center T := (Subgroup.centerCongr ePT z0).2
  let z : ↥U := T.subtype zT
  have hzZ : z ∈ (Subgroup.center T).map T.subtype :=
    Subgroup.mem_map_of_mem T.subtype hzTcenter
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : zT = 1 := T.subtype_injective (by simpa [z] using h)
    have h2 : (z0.1 : ↥(P : Subgroup ↥N)) = 1 := ePT.injective (by simpa [zT] using h1)
    exact hz0ne (Subtype.ext h2)
  have hz0sq : (z0.1 : ↥(P : Subgroup ↥N)) ^ 2 = 1 := hexpP z0.1 z0.2
  have hzT2 : zT ^ 2 = 1 := by
    rw [show zT = ePT z0.1 from rfl, ← map_pow, hz0sq, map_one]
  have hz2 : z ^ 2 = 1 := by
    rw [show z = T.subtype zT from rfl, ← map_pow, hzT2, map_one]
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hTleC : T ≤ Subgroup.centralizer ({z} : Set ↥U) := by
    intro t ht
    have hcomm : (⟨t, ht⟩ : ↥T) * zT = zT * ⟨t, ht⟩ :=
      Subgroup.mem_center_iff.mp hzTcenter ⟨t, ht⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa [z] using congrArg T.subtype hcomm
  exact ⟨hZcard, z, hzZ, hz1, hzord, hTleC⟩

private lemma centralizer_le_map_sylow_of_odd_index (hH : CFSG.Quasithin.IsSz n H)
    {U : Subgroup H} {N : Subgroup ↥U} (hNodd : Odd N.index) (P : Sylow 2 ↥N)
    {z : ↥U} (hzord : orderOf z = 2)
    (hTleC : (P : Subgroup ↥N).map N.subtype ≤ Subgroup.centralizer ({z} : Set ↥U)) :
    Subgroup.centralizer ({z} : Set ↥U) ≤ (P : Subgroup ↥N).map N.subtype := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Subgroup ↥U := (P : Subgroup ↥N).map N.subtype
  have hTp : IsPGroup 2 T := P.isPGroup'.map N.subtype
  have hTodd : Odd T.index := by
    rw [Subgroup.index_map_subtype (P : Subgroup ↥N)]
    exact (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp P.not_dvd_index)).mul hNodd
  let ST : Sylow 2 ↥U := hTp.toSylow hTodd.not_two_dvd_nat
  have hSTcoe : (ST : Subgroup ↥U) = T := IsPGroup.toSylow_coe _ _
  have hzHord : orderOf ((z : ↥U) : H) = 2 := by
    simpa using (orderOf_injective U.subtype U.subtype_injective z).trans hzord
  have hC2 : IsPGroup 2 (Subgroup.centralizer ({z} : Set ↥U)) :=
    isPGroup_centralizer_subgroup hH z.2 hzHord
  have h := ST.3 hC2 (by rwa [hSTcoe])
  rw [hSTcoe] at h
  exact le_of_eq h

private lemma card_normalizer_map_sylow
    (hH : CFSG.Quasithin.IsSz n H) {U : Subgroup H}
    {N : Subgroup ↥U} (hNodd : Odd N.index) {a : ℕ} (ha : 1 ≤ a)
    (e : ↥N ≃* ↥(Sz a)) (P : Sylow 2 ↥N) :
    Nat.card (Subgroup.normalizer (((P : Subgroup ↥N).map N.subtype : Subgroup ↥U) : Set ↥U))
        = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) ∧
      Subgroup.normalizer (((P : Subgroup ↥N).map N.subtype : Subgroup ↥U) : Set ↥U) ≤ N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNsz : CFSG.Quasithin.IsSz (2 * a + 1) ↥N := isSz_of_mulEquiv ha e
  let T : Subgroup ↥U := (P : Subgroup ↥N).map N.subtype
  let S : Subgroup ↥U := Subgroup.normalizer (T : Set ↥U)
  let Z : Subgroup ↥U := (Subgroup.center T).map T.subtype
  obtain ⟨hZcard, z, hzZ, hz1, hzord, hTleC⟩ :=
    exists_central_involution_map_sylow (a := a) ha e P
  have hTcard : Nat.card T = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact (fusionBenderBorel_of_isSz (n := 2 * a + 1) (H := ↥N) hNsz P).2.2.2.2
  have hCU := centralizer_le_map_sylow_of_odd_index hH hNodd P hzord hTleC
  have hSZ : S ≤ Subgroup.normalizer (Z : Set ↥U) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (Subgroup.center T)
  have hC : S ⊓ Subgroup.centralizer ({z} : Set ↥U) ≤ T :=
    inf_le_right.trans hCU
  have hCardS : Nat.card S ≤ Nat.card T * (Nat.card Z - 1) :=
    card_le_mul_card_sub_one hSZ hzZ hz1 hC
  have himage_le : (Subgroup.normalizer (P : Set ↥N)).map N.subtype ≤ S :=
    Subgroup.le_normalizer_map N.subtype
  have himage_card : Nat.card ((Subgroup.normalizer (P : Set ↥N)).map N.subtype) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact card_normalizer_sylow_of_isSz (n := 2 * a + 1) (H := ↥N) hNsz P
  have hSleImage : Nat.card S ≤
      Nat.card ((Subgroup.normalizer (P : Set ↥N)).map N.subtype) := by
    calc Nat.card S ≤ Nat.card T * (Nat.card Z - 1) := hCardS
      _ = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by rw [hTcard, hZcard]
      _ = Nat.card ((Subgroup.normalizer (P : Set ↥N)).map N.subtype) := himage_card.symm
  have hEq : (Subgroup.normalizer (P : Set ↥N)).map N.subtype = S :=
    Subgroup.eq_of_le_of_card_ge himage_le hSleImage
  refine ⟨?_, ?_⟩
  · change Nat.card S = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1)
    rw [← hEq]
    exact himage_card
  · change S ≤ N
    rw [← hEq]
    exact Subgroup.map_subtype_le _

private lemma eq_top_of_normal_sz
    (hH : CFSG.Quasithin.IsSz n H) {U : Subgroup H} {N : Subgroup ↥U} (hN : N.Normal)
    (hNodd : Odd N.index) {a : ℕ} (ha : 1 ≤ a) (e : ↥N ≃* ↥(Sz a)) : N = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥N := Sylow.nonempty.some
  haveI : Finite (Sylow 2 ↥N) := Sylow.finite_of_finiteIndex P
  obtain ⟨-, hSleN⟩ := card_normalizer_map_sylow hH hNodd ha e P
  have hfratt := Sylow.normalizer_sup_eq_top (p := 2) (N := N) P
  rw [sup_comm] at hfratt
  rw [sup_eq_left.mpr hSleN] at hfratt
  exact hfratt

private lemma isPGroup_odd_index_map {U : Subgroup H} {a : ℕ} {T S : Subgroup ↥U}
    (hTS : T ≤ S) (hTp : IsPGroup 2 T)
    (hTcard : Nat.card T = (2 ^ (2 * a + 1)) ^ 2)
    (hScard : Nat.card S = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1)) :
    IsPGroup 2 ((T.map U.subtype).subgroupOf (S.map U.subtype)) ∧
      Odd ((T.map U.subtype).subgroupOf (S.map U.subtype)).index ∧
      Nat.card (T.map U.subtype) = (2 ^ (2 * a + 1)) ^ 2 ∧
      Nat.card (S.map U.subtype) =
        (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
  have hT1leR1 : T.map U.subtype ≤ S.map U.subtype := Subgroup.map_mono hTS
  have hT1card : Nat.card (T.map U.subtype) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [Subgroup.card_map_of_injective U.subtype_injective, hTcard]
  have hR1card : Nat.card (S.map U.subtype) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
    rw [Subgroup.card_map_of_injective U.subtype_injective, hScard]
  have hT1p : IsPGroup 2 (T.map U.subtype) := hTp.map U.subtype
  have hrel := Subgroup.relIndex_mul_card (H := T.map U.subtype) (K := S.map U.subtype)
  rw [inf_eq_left.mpr hT1leR1, hT1card, hR1card] at hrel
  have hT1rel : (T.map U.subtype).relIndex (S.map U.subtype) = 2 ^ (2 * a + 1) - 1 := by
    apply Nat.mul_right_cancel (show 0 < (2 ^ (2 * a + 1)) ^ 2 by positivity)
    rw [hrel, mul_comm ((2 ^ (2 * a + 1)) ^ 2) (2 ^ (2 * a + 1) - 1)]
  refine ⟨?_, ?_, hT1card, hR1card⟩
  · exact hT1p.comap_of_injective (S.map U.subtype).subtype
      (S.map U.subtype).subtype_injective
  · change Odd ((T.map U.subtype).relIndex (S.map U.subtype))
    rw [hT1rel]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one

private lemma inf_eq_of_isPGroup_of_odd_index {G : Type} [Group G] [Finite G]
    {T R Q : Subgroup G} (hTR : T ≤ R) (hTQ : T ≤ Q)
    (hT2 : IsPGroup 2 (T.subgroupOf R)) (hTodd : Odd (T.subgroupOf R).index)
    (hQ2 : IsPGroup 2 Q) : R ⊓ Q = T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ((R ⊓ Q).subgroupOf R) :=
    (hQ2.to_le inf_le_right).comap_of_injective R.subtype R.subtype_injective
  let TS : Sylow 2 R := hT2.toSylow hTodd.not_two_dvd_nat
  have hle : (TS : Subgroup R) ≤ (R ⊓ Q).subgroupOf R := by
    intro x hx
    change (x : G) ∈ T at hx
    exact ⟨x.2, hTQ hx⟩
  have hsub : (R ⊓ Q).subgroupOf R = T.subgroupOf R := by
    have h := TS.3 hS2 hle
    rwa [IsPGroup.toSylow_coe] at h
  have h := Subgroup.subgroupOf_inj.mp hsub
  rwa [inf_eq_left.mpr inf_le_left, inf_eq_left.mpr hTR] at h

private lemma dvd_of_card_normalizer_join {G : Type} [Group G] [Finite G]
    {q0 q : ℕ} {R Q : Subgroup G} (hRQ : R ≤ Subgroup.normalizer (Q : Set G))
    (hR : Nat.card R = q0 ^ 2 * (q0 - 1)) (hQ : Nat.card Q = q ^ 2)
    (hInf : Nat.card ↥(R ⊓ Q) = q0 ^ 2)
    (hNQ : Nat.card (Subgroup.normalizer (Q : Set G)) = q ^ 2 * (q - 1))
    (hq0 : 0 < q0) : q0 - 1 ∣ q - 1 := by
  have hjoin :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := R) (K := Q) hRQ
  rw [hInf, hR, hQ] at hjoin
  have hq : 0 < q ^ 2 := by rw [← hQ]; exact Nat.card_pos
  have hsupcard : Nat.card ↥(R ⊔ Q) = (q0 - 1) * q ^ 2 := by
    apply Nat.mul_right_cancel (show 0 < q0 ^ 2 by exact pow_pos hq0 2)
    rw [hjoin]
    ring
  have hsup_le : R ⊔ Q ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hRQ (Subgroup.le_normalizer)
  have hdiv : Nat.card ↥(R ⊔ Q) ∣ Nat.card (Subgroup.normalizer (Q : Set G)) :=
    Subgroup.card_dvd_of_le hsup_le
  rw [hsupcard, hNQ] at hdiv
  rw [mul_comm (q0 - 1) (q ^ 2)] at hdiv
  exact Nat.dvd_of_mul_dvd_mul_left hq hdiv

private lemma dvd_of_normal_sz
    (hH : CFSG.Quasithin.IsSz n H) {U : Subgroup H} {N : Subgroup ↥U}
    (hNodd : Odd N.index) {a : ℕ} (ha : 1 ≤ a) (e : ↥N ≃* ↥(Sz a)) :
    2 * a + 1 ∣ n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNsz : CFSG.Quasithin.IsSz (2 * a + 1) ↥N := isSz_of_mulEquiv ha e
  let P : Sylow 2 ↥N := Sylow.nonempty.some
  obtain ⟨hScard, -⟩ := card_normalizer_map_sylow hH hNodd ha e P
  let T : Subgroup ↥U := (P : Subgroup ↥N).map N.subtype
  let S : Subgroup ↥U := Subgroup.normalizer (T : Set ↥U)
  have hScard' : Nat.card S = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := hScard
  have hTp : IsPGroup 2 T := P.isPGroup'.map N.subtype
  have hTcard : Nat.card T = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact (fusionBenderBorel_of_isSz (n := 2 * a + 1) (H := ↥N) hNsz P).2.2.2.2
  let T₁ : Subgroup H := T.map U.subtype
  let R₁ : Subgroup H := S.map U.subtype
  obtain ⟨hT1p', hT1odd, hT1card, hR1card⟩ :=
    isPGroup_odd_index_map (Subgroup.le_normalizer (H := T)) hTp hTcard hScard'
  have hT1p : IsPGroup 2 T₁ := hTp.map U.subtype
  obtain ⟨Q, hTQ⟩ := hT1p.exists_le_sylow
  have hT1ne : T₁ ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot _).mp (by
      rw [hT1card, ← pow_mul]
      exact Nat.one_lt_pow (by omega) (by norm_num))
  have hRnormT : R₁ ≤ Subgroup.normalizer (T₁ : Set H) :=
    Subgroup.le_normalizer_map U.subtype
  have hRQ : R₁ ≤ Subgroup.normalizer (Q : Set H) :=
    hRnormT.trans (normalizer_le_normalizer_sylow_of_isSz hH Q hTQ hT1ne)
  have hT1leR1 : T₁ ≤ R₁ := Subgroup.map_mono (Subgroup.le_normalizer (H := T))
  have hinf : R₁ ⊓ (Q : Subgroup H) = T₁ :=
    inf_eq_of_isPGroup_of_odd_index hT1leR1 hTQ hT1p' hT1odd Q.isPGroup'
  have hQcard : Nat.card (Q : Subgroup H) = (2 ^ n) ^ 2 :=
    (fusionBenderBorel_of_isSz (n := n) (H := H) hH Q).2.2.2.2
  have hNQcard : Nat.card (Subgroup.normalizer (Q : Set H)) =
      (2 ^ n) ^ 2 * (2 ^ n - 1) := card_normalizer_sylow_of_isSz hH Q
  have hdiv' : 2 ^ (2 * a + 1) - 1 ∣ 2 ^ n - 1 :=
    dvd_of_card_normalizer_join hRQ hR1card hQcard (by rw [hinf]; exact hT1card) hNQcard
      (by positivity)
  exact CFSG.Quasithin.Vol2.Ch11.SecA.dvd_of_two_pow_sub_one_dvd hdiv'

private lemma lt_of_normal_sz (hH : CFSG.Quasithin.IsSz n H) {U : Subgroup H} (hU : U ≠ ⊤)
    {N : Subgroup ↥U} {a : ℕ} (ha : 1 ≤ a) (e : ↥N ≃* ↥(Sz a)) (hdvd : 2 * a + 1 ∣ n) :
    2 * a + 1 < n := by
  classical
  obtain ⟨k, hk, hkn, -⟩ := exists_mulEquiv_sz hH
  have hnpos : 0 < n := by omega
  rcases lt_or_eq_of_le (Nat.le_of_dvd hnpos hdvd) with hlt | heq
  · exact hlt
  · exfalso
    have hNsz : CFSG.Quasithin.IsSz (2 * a + 1) ↥N := isSz_of_mulEquiv ha e
    have hcardN := CFSG.Quasithin.card_of_isSz hNsz
    have hcardH := CFSG.Quasithin.card_of_isSz hH
    rw [← heq] at hcardH
    have hcardNH : Nat.card ↥N = Nat.card H := by rw [hcardN, hcardH]
    have hcardNU : Nat.card ↥N ≤ Nat.card ↥U := Subgroup.card_le_card_group (H := N)
    have hcardUH : Nat.card ↥U ≤ Nat.card H := Subgroup.card_le_card_group (H := U)
    have hcardU : Nat.card ↥U = Nat.card H :=
      le_antisymm hcardUH (hcardNH ▸ hcardNU)
    exact hU ((Subgroup.card_eq_iff_eq_top U).mp hcardU)

theorem isSz_of_normal_sz
    (hH : CFSG.Quasithin.IsSz n H) {U : Subgroup H} (hU : U ≠ ⊤) {N : Subgroup ↥U}
    (hN : N.Normal) (hNodd : Odd N.index) {a : ℕ} (ha : 1 ≤ a) (e : ↥N ≃* ↥(Sz a)) :
    2 * a + 1 ∣ n ∧ 2 * a + 1 < n ∧ CFSG.Quasithin.IsSz (2 * a + 1) ↥U := by
  have hdvd := dvd_of_normal_sz hH hNodd ha e
  have hlt := lt_of_normal_sz hH hU ha e hdvd
  have hNtop := eq_top_of_normal_sz hH hN hNodd ha e
  have eUN : ↥U ≃* ↥N :=
    ((MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv).symm
  exact ⟨hdvd, hlt, isSz_of_mulEquiv ha (eUN.trans e)⟩

end CFSG.LieType.SuzukiSubgroups
