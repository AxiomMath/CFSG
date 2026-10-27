module

public import CFSG.ClassicalInvolution.Q3.Q3TMFSBasic
public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum
public import CFSG.ClassicalInvolution.Q3.Q3T6LinMember

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T.MFS

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance

section Simple

theorem simple_of_isComponentOf_cent {Y : Type} [Group Y] {T : Subgroup Y}
    (hT : IsComponentOf T ⊤) (hC : Subgroup.centralizer (T : Set Y) = ⊥) :
    IsSimpleGroup T ∧ ∃ a b : T, a * b ≠ b * a := by
  have hsimple : IsSimpleGroup (T ⧸ Subgroup.center T) := hT.2.2.2
  have hZ : Subgroup.center T = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxc : (x : Y) ∈ Subgroup.centralizer (T : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hx) ⟨g, hg⟩)
    rw [hC, Subgroup.mem_bot] at hxc
    exact Subgroup.mem_bot.mpr (Subtype.ext hxc)
  have hsimp : IsSimpleGroup T :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm).isSimpleGroup
  refine ⟨hsimp, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := exists_ne (1 : T)
  have hxc : x ∈ Subgroup.center T := Subgroup.mem_center_iff.mpr fun g => hcon g x
  rw [hZ] at hxc
  exact hx (Subgroup.mem_bot.mp hxc)

end Simple

section Datum

variable {Y : Type} [Group Y]

theorem mem_sup_oddCoreIn {C Q' : Subgroup Y} (hQC : Q' ≤ C) {x : Y}
    (hx : x ∈ Q' ⊔ oddCoreIn C) : ∃ q ∈ Q', ∃ o ∈ oddCoreIn C, x = q * o := by
  have hO : oddCoreIn C ≤ C := oddCoreIn_le C
  have hN : ((oddCoreIn C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO).mpr (normalizer_oddCoreIn C)
  have hxC : x ∈ C := sup_le hQC hO hx
  have hx' : (⟨x, hxC⟩ : C) ∈ Q'.subgroupOf C ⊔ (oddCoreIn C).subgroupOf C := by
    rw [← Subgroup.subgroupOf_sup hQC hO]
    exact hx
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨a, ha, b, hb, congrArg Subtype.val hab.symm⟩

theorem eq_one_of_odd_of_pow_two {O : Subgroup Y} (hO : Odd (Nat.card O)) {o : Y} (ho : o ∈ O)
    {k : ℕ} (h : o ^ 2 ^ k = 1) : o = 1 := by
  have h1 : orderOf o ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf o ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨o, ho⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · exfalso
    have h3 : 2 ∣ Nat.card O := by
      refine dvd_trans ?_ h2
      rw [hj]
      exact dvd_pow_self 2 (Nat.succ_ne_zero j)
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h3)

theorem pow_mul_mem_oddCoreIn {C : Subgroup Y} {q o : Y} (hq : q ∈ C) (ho : o ∈ oddCoreIn C)
    (n : ℕ) : ∃ o' ∈ oddCoreIn C, (q * o) ^ n = q ^ n * o' := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨o', ho', h⟩ := ih
    refine ⟨q⁻¹ * o' * q * o, ?_, ?_⟩
    · have h1 : q⁻¹ * o' * q ∈ oddCoreIn C := by
        simpa using conj_mem_oddCoreIn (inv_mem hq) ho'
      exact mul_mem h1 ho
    · rw [pow_succ, h, pow_succ]
      group

@[expose] def QOddNormalInT (z : Y) (L T : Subgroup Y) (Q : Sylow 2 L) : Prop :=
  ((((Q : Subgroup L).map L.subtype ⊔
      oddCoreIn (Subgroup.centralizer ({z} : Set Y))) ⊓ T).subgroupOf
    (Subgroup.centralizer ({z} : Set Y) ⊓ T)).Normal

theorem QOddNormalInT.of_normal {z : Y} {L T : Subgroup Y} {Q : Sylow 2 L}
    (h : (((Q : Subgroup L).map L.subtype ⊔
      oddCoreIn (Subgroup.centralizer ({z} : Set Y))).subgroupOf
      (Subgroup.centralizer ({z} : Set Y))).Normal) : QOddNormalInT z L T Q := by
  refine ⟨fun n hn g => ?_⟩
  have key := h.conj_mem ⟨(n : Y), n.2.1⟩ hn.1 ⟨(g : Y), g.2.1⟩
  exact ⟨key, T.mul_mem (T.mul_mem g.2.2 n.2.2) (T.inv_mem g.2.2)⟩

variable [Finite Y]

theorem typeCNormalDatum_proved :
    ∀ (Y : Type) [Group Y] [Finite Y] (z : Y) (L T : Subgroup Y), Setting z L T →
      memberIndex L T = 3 → ∀ Q : Sylow 2 L, QOddNormalInT z L T Q →
        IsSimpleGroup T ∧ (∃ a b : T, a * b ≠ b * a) ∧
          ∃ (R : Subgroup T) (S : Sylow 2 R) (t : T), TightDatum R S t := by
  intro Y _ _ z L T hS hC Q hQ
  have hTn : T.Normal := hS.normal
  obtain ⟨hsimp, hnab⟩ := simple_of_isComponentOf_cent hS.comp hS.cent
  refine ⟨hsimp, hnab, ?_⟩
  have hz := hS.member
  set C : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hCdef
  have hLC : L ≤ C := isSubnormal_le hz.subnormal
  obtain ⟨hodd, -⟩ := odd_index_of_memberIndex_eq_three hS.sup hC
  set Q' : Subgroup Y := (Q : Subgroup L).map L.subtype with hQ'def
  have hQ'2 : IsPGroup 2 Q' := Q.isPGroup'.map L.subtype
  have hQ'T : Q' ≤ T := isPGroup_two_le_of_odd_index hodd hQ'2
  have hQ'L : Q' ≤ L := Subgroup.map_subtype_le _
  have hQ'C : Q' ≤ C := hQ'L.trans hLC
  have hzQ : z ∈ Q' := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set z' : L := ⟨z, hz.mem⟩ with hz'
    have hz'c : ∀ g : L, g * z' = z' * g := fun g =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLC g.2))
    have hZn : (Subgroup.zpowers z').Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hc : g * z' ^ k = z' ^ k * g := (Commute.zpow_right (hz'c g : Commute g z') k).eq
      have : g * z' ^ k * g⁻¹ = z' ^ k := by rw [hc]; simp
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z') k
    have hz'o : orderOf z' = 2 := by
      rw [hz', Subgroup.orderOf_mk]
      exact hz.orderOf_eq_two
    have hp : IsPGroup 2 (Subgroup.zpowers z') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'o]; norm_num)
    exact ⟨z', hp.le_sylow_of_normal Q (Subgroup.mem_zpowers z'), rfl⟩
  have hzT : z ∈ T := hQ'T hzQ
  set O : Subgroup Y := oddCoreIn C with hOdef
  have hOC : O ≤ C := oddCoreIn_le C
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn C
  set P : Subgroup Y := Q' ⊔ O with hPdef
  have hPC : P ≤ C := sup_le hQ'C hOC
  have hQ'P : Q' ≤ P := le_sup_left
  obtain ⟨R, hR⟩ : ∃ R : Subgroup T, ∀ x : T, x ∈ R ↔ (x : Y) ∈ P :=
    ⟨P.subgroupOf T, fun x => Iff.rfl⟩
  let ι : ↥R →* Y := T.subtype.comp R.subtype
  have hι : Function.Injective ι := T.subtype_injective.comp R.subtype_injective
  have hιmem : ∀ r : R, ι r ∈ P := fun r => (hR r.1).mp r.2
  have hQ'range : ∀ q ∈ Q', ∃ r : R, ι r = q := fun q hq =>
    ⟨⟨⟨q, hQ'T hq⟩, (hR _).mpr (hQ'P hq)⟩, rfl⟩
  have hQ''2 : IsPGroup 2 (Q'.comap ι) := hQ'2.comap_of_injective ι hι
  have hmax : ∀ {K : Subgroup R}, IsPGroup 2 K → Q'.comap ι ≤ K → K = Q'.comap ι := by
    intro K hK hle
    refine le_antisymm (fun r hr => ?_) hle
    have hKY2 : IsPGroup 2 (K.map ι) := hK.map ι
    obtain ⟨q, hq, o, ho, hqo⟩ := mem_sup_oddCoreIn hQ'C (hιmem r)
    have hqK : q ∈ K.map ι := by
      obtain ⟨r', hr'⟩ := hQ'range q hq
      exact ⟨r', hle (show ι r' ∈ Q' by rw [hr']; exact hq), hr'⟩
    have hoK : o ∈ K.map ι := by
      have : o = q⁻¹ * ι r := by rw [hqo]; group
      rw [this]
      exact mul_mem (inv_mem hqK) ⟨r, hr, rfl⟩
    obtain ⟨k, hk⟩ := hKY2 ⟨o, hoK⟩
    have ho1 : o = 1 := eq_one_of_odd_of_pow_two hOodd ho (by simpa using congrArg Subtype.val hk)
    show ι r ∈ Q'
    rw [hqo, ho1, mul_one]
    exact hq
  let S : Sylow 2 R := ⟨Q'.comap ι, hQ''2, hmax⟩
  have hSmem : ∀ r : R, r ∈ (S : Subgroup R) ↔ ι r ∈ Q' := fun r => Iff.rfl
  have hquat : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) := by
    obtain ⟨e⟩ := Q3T6.quaternion_sylow_of_isClassicalMember3 hz Q
    have hmap : (Q'.comap ι).map ι = Q' := Subgroup.map_comap_eq_self hQ'range
    exact ⟨3, le_rfl, ⟨((Subgroup.equivMapOfInjective (Q'.comap ι) ι hι).trans
      (MulEquiv.subgroupCongr hmap)).trans
      ((Subgroup.equivMapOfInjective (Q : Subgroup L) L.subtype L.subtype_injective).symm.trans
        e)⟩⟩
  have hmem : (⟨z, hzT⟩ : T) ∈ (S : Subgroup R).map R.subtype :=
    ⟨⟨⟨z, hzT⟩, (hR _).mpr (hQ'P hzQ)⟩, (hSmem _).mpr hzQ, rfl⟩
  have hcent : R ≤ Subgroup.centralizer ({(⟨z, hzT⟩ : T)} : Set T) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hPC ((hR r).mp hr)))
  have hnormal : (R.subgroupOf (Subgroup.centralizer ({(⟨z, hzT⟩ : T)} : Set T))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgC : ((g : T) : Y) ∈ C :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.2))
    have hnP : (((n : T)) : Y) ∈ P := (hR _).mp hn
    have hnC : (((n : T)) : Y) ∈ C := hPC hnP
    have key := hQ.conj_mem ⟨((n : T) : Y), hnC, (n : T).2⟩ ⟨hnP, (n : T).2⟩
      ⟨((g : T) : Y), hgC, (g : T).2⟩
    exact (hR _).mpr key.1
  have hOcore : O.comap ι ≤ classicalInvolutionOddCore ↥R := by
    have hnorm : (O.comap ι).Normal := ⟨fun n hn r => by
      rw [Subgroup.mem_comap] at hn ⊢
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_oddCoreIn (hPC (hιmem r)) hn⟩
    have hodd' : Odd (Nat.card (O.comap ι)) := by
      have hdvd : Nat.card (O.comap ι) ∣ Nat.card O := by
        have h1 : Nat.card ((O.comap ι).map ι) = Nat.card (O.comap ι) :=
          Subgroup.card_map_of_injective hι
        rw [← h1]
        exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le ι O)
      exact hOodd.of_dvd_nat hdvd
    exact le_sSup ⟨hnorm, hodd'⟩
  have htwo : IsPGroup 2 (↥R ⧸ classicalInvolutionOddCore ↥R) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨q, hq, o, ho, hqo⟩ := mem_sup_oddCoreIn hQ'C (hιmem x)
    obtain ⟨k, hk⟩ := hQ'2 ⟨q, hq⟩
    have hqk : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨o', ho', hpow⟩ := pow_mul_mem_oddCoreIn (hQ'C hq) ho (2 ^ k)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine hOcore ?_
    show ι (x ^ 2 ^ k) ∈ O
    rw [map_pow, hqo, hpow, hqk, one_mul]
    exact ho'
  refine ⟨R, S, ⟨z, hzT⟩, ?_⟩
  exact { quat := hquat
          mem := hmem
          order := by rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two
          cent := hcent
          normal := hnormal
          twoGroup := htwo }

end Datum

end CFSG.ClassicalInvolution.Q3.Q3T.MFS
