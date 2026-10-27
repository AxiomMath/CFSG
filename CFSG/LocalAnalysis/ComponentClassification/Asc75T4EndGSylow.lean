module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGThreeNine

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.ComponentClassification.AschbacherKnownGroup (HasCyclicSylowTwo)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_le {K X : Subgroup G} (hX : IsPGroup 2 X) (hXK : X ≤ K) :
    ∃ S : Subgroup G, IsSylowOf 2 S K ∧ X ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(P : Subgroup K).map K.subtype, ⟨P, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hXK hx⟩, hP (show (⟨x, hXK hx⟩ : K) ∈ X.subgroupOf K from hx), rfl⟩

theorem exists_sq_eq_one_ne_one {X : Subgroup G} (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥) :
    ∃ x ∈ X, x ^ 2 = 1 ∧ x ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card X := by
    rcases hX.card_eq_or_dvd with h | h
    · exact absurd ((eq_bot_iff_card X).mpr h) hX1
    · exact h
  obtain ⟨⟨x, hx⟩, hx2⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
  rw [Subgroup.orderOf_mk] at hx2
  exact ⟨x, hx, by rw [← hx2]; exact pow_orderOf_eq_one x,
    fun h => by rw [h, orderOf_one] at hx2; norm_num at hx2⟩

theorem exists_sq_eq_one_mem_inf_center {S N : Subgroup G} (hS : IsPGroup 2 S) (hNS : N ≤ S)
    (hSN : S ≤ normalizer (N : Set G)) (hN1 : N ≠ ⊥) :
    ∃ x ∈ N, x ^ 2 = 1 ∧ x ≠ 1 ∧ ∀ s ∈ S, x * s = s * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hn : (N.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hNS).mpr hSN
  have hne : N.subgroupOf S ≠ ⊥ := by
    intro h
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNS hx⟩ : S) ∈ N.subgroupOf S := hx
    rw [h, mem_bot] at this
    rw [mem_bot]
    exact congrArg Subtype.val this
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨y, hy, hy2, hy1⟩ := exists_sq_eq_one_ne_one
    (hS.to_subgroup (N.subgroupOf S ⊓ center S : Subgroup S)) h1
  obtain ⟨hyN, hyZ⟩ := mem_inf.mp hy
  refine ⟨(y : G), hyN, by simpa using congrArg Subtype.val hy2,
    fun h => hy1 (Subtype.ext h), fun s hs => ?_⟩
  have := mem_center_iff.mp hyZ ⟨s, hs⟩
  exact (congrArg Subtype.val this).symm

theorem isSylowOf_top_of_normalizer_le {S H : Subgroup G} (hS : IsSylowOf 2 S H)
    (hN : normalizer (S : Set G) ≤ H) : IsSylowOf 2 S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hST⟩ := exists_isSylowOf_le hS.isPGroup (le_top : S ≤ ⊤)
  by_cases hTS : T ≤ S
  · rwa [le_antisymm hTS hST] at hT
  exfalso
  have : Group.IsNilpotent T := hT.isPGroup.isNilpotent
  have hlt : S.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hTS fun x hx => ?_
    have : (⟨x, hx⟩ : T) ∈ S.subgroupOf T := h ▸ mem_top _
    exact this
  obtain ⟨y, hyN, hyS⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (S.subgroupOf T) hlt)
  rw [← subgroupOf_normalizer_eq hST, mem_subgroupOf] at hyN
  have hyH := hN hyN
  have hle : S ⊔ zpowers (y : G) ≤ H := sup_le hS.le ((zpowers_le).mpr hyH)
  have h2 : IsPGroup 2 ↥(S ⊔ zpowers (y : G)) :=
    hT.isPGroup.to_le (sup_le hST ((zpowers_le).mpr y.2))
  have heq := hS.eq_of_le le_sup_left hle h2
  exact hyS (show (y : G) ∈ S from heq ▸ mem_sup_right (mem_zpowers _))

namespace EndSetting

variable {Q : Subgroup G} (hE : EndSetting Q)
include hE

omit hE in
theorem isSylowOf_inf {S : Subgroup G} (hS : IsSylowOf 2 S (normalizer (Q : Set G))) :
    IsSylowOf 2 (S ⊓ Q) Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hS.inf_of_le_normalizer le_normalizer le_rfl

theorem inf_ne_bot {S : Subgroup G} (hS : IsSylowOf 2 S (normalizer (Q : Set G))) :
    S ⊓ Q ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hc := (isSylowOf_inf hS).card_eq
  rw [h, card_bot] at hc
  have h2 : 2 ∣ Nat.card Q := even_iff_two_dvd.mp hE.main.tight.1
  have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
  have h3 : (Nat.card Q).factorization 2 = 0 := by
    have := congrArg (fun m => m.factorization 2) hc
    simp only [Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at this
    exact this.symm
  omega

theorem hasFourGroup_inf {S : Subgroup G} (hS : IsSylowOf 2 S (normalizer (Q : Set G))) :
    HasFourGroup (S ⊓ Q) := by
  obtain ⟨E, hEK, hE2, hE4⟩ := hE.main.four
  obtain ⟨c, hcQ, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf
    (isSylowOf_inf hS) (isPGroup_of_sq_eq_one hE2) (hEK.trans (twoPrimeLayerIn_le Q))
  exact (hasFourGroup_rightConjugate_iff.mpr ⟨E, le_rfl, hE2, hE4⟩).mono hc

theorem isSylowOf_top {S : Subgroup G} (hS : IsSylowOf 2 S (normalizer (Q : Set G))) :
    IsSylowOf 2 S ⊤ := by
  refine isSylowOf_top_of_normalizer_le hS fun n hn => ?_
  by_contra hnH
  obtain ⟨E, hE', hE2, hE4⟩ := hE.hasFourGroup_inf hS
  apply hE.main.not_hasFourGroup_of_linkedClass_eq hE.linked hnH
  refine ⟨rightConjugate E n, fun y hy => ?_, ?_, ?_⟩
  · have hSn : rightConjugate S n = S := (rightConjugate_eq_self_iff S n).mpr hn
    refine mem_inf.mpr ⟨AschbacherTheorem3.rightConjugate_le_rightConjugate
      (hE'.trans inf_le_right) n hy, ?_⟩
    have hyS : y ∈ rightConjugate S n :=
      AschbacherTheorem3.rightConjugate_le_rightConjugate (hE'.trans inf_le_left) n hy
    rw [hSn] at hyS
    exact hS.le hyS
  · rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hE2 e he, map_one]
  · rw [rightConjugate_card, hE4]

theorem exists_involution_commute {t : G} (htN : t ∈ normalizer (Q : Set G)) {k : ℕ}
    (ht : t ^ 2 ^ k = 1) : ∃ S : Subgroup G, IsSylowOf 2 S (normalizer (Q : Set G)) ∧ t ∈ S ∧
      ∃ z ∈ S ⊓ Q, z ^ 2 = 1 ∧ z ≠ 1 ∧ z * t = t * z := by
  obtain ⟨S, hS, htS⟩ := exists_isSylowOf_le (isPGroup_zpowers_of_pow_eq_one ht)
    ((zpowers_le).mpr htN)
  have htS' : t ∈ S := htS (mem_zpowers t)
  have hSN : S ≤ normalizer ((S ⊓ Q : Subgroup G) : Set G) :=
    (le_inf le_normalizer hS.le).trans (inf_normalizer_le_normalizer_inf _ _)
  obtain ⟨z, hz, hz2, hz1, hzS⟩ := exists_sq_eq_one_mem_inf_center hS.isPGroup inf_le_left hSN
    (hE.inf_ne_bot hS)
  exact ⟨S, hS, htS', z, hz, hz2, hz1, hzS t htS'⟩

end EndSetting

namespace MainCounterexample

variable {Q : Subgroup G} (hM : MainCounterexample G Q) (hE : EndSetting Q)
include hM hE

theorem odd_card_centralizer :
    Odd (Nat.card (centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  set C := centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) with hC
  obtain ⟨t, ht⟩ := hE.exists_isOverlapInv
  obtain ⟨S, hS, htS, z, hz, hz2, hz1, hzt⟩ :=
    hE.exists_involution_commute ht.mem_normalizer (k := 1) (by simpa using ht.1)
  have hSbar : IsSylowOf 2 (bar Q S) ⊤ := by
    have h := isSylowOf_bar (D := Q) hS le_rfl
    rwa [show bar Q (normalizer (Q : Set G)) = ⊤ from by
      rw [eq_top_iff]
      intro x _
      obtain ⟨h, rfl⟩ := toBar_surjective Q x
      exact toBar_mem_bar Q h.2] at h
  have hCn : C.Normal := inferInstance
  have hC2 : IsSylowOf 2 (bar Q S ⊓ C) C :=
    hSbar.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hCn])
  have hne : bar Q S ⊓ C ≠ ⊥ := by
    intro h
    have hc := hC2.card_eq
    rw [h, card_bot] at hc
    have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne'
      (even_iff_two_dvd.mp hev)
    have h3 : (Nat.card C).factorization 2 = 0 := by
      have := congrArg (fun m => m.factorization 2) hc
      simp only [Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at this
      exact this.symm
    omega
  have hSN : bar Q S ≤ normalizer ((bar Q S ⊓ C : Subgroup (Bar Q)) : Set (Bar Q)) :=
    (le_inf le_normalizer (by rw [normalizer_eq_top_iff.mpr hCn]; exact le_top)).trans
      (inf_normalizer_le_normalizer_inf _ _)
  obtain ⟨ab, hab, hab2, hab1, habZ⟩ := exists_sq_eq_one_mem_inf_center hSbar.isPGroup
    inf_le_left hSN hne
  obtain ⟨habS, habC⟩ := mem_inf.mp hab
  obtain ⟨s, hsS, rfl⟩ := (mem_bar_iff Q S ab).mp habS
  have hSH : S ≤ normalizer (Q : Set G) := hS.le
  have hinj : ∀ u v : normalizer (Q : Set G), (u : G) ∈ S → (v : G) ∈ S →
      toBar Q u = toBar Q v → u = v := fun u v hu hv h => toBar_injOn_of_isPGroup hS.isPGroup hu hv h
  have hs2 : (s : G) ^ 2 = 1 := by
    have h1 : toBar Q (s ^ 2) = toBar Q 1 := by rw [map_pow, hab2, map_one]
    have := hinj _ _ (by simpa using pow_mem hsS 2) (by simp) h1
    simpa using congrArg Subtype.val this
  have hs1 : (s : G) ≠ 1 := fun h => hab1 (by rw [show s = 1 from Subtype.ext h, map_one])
  have hcomm : ∀ x ∈ S, (s : G) * x = x * s := by
    intro x hxS
    have h1 := habZ (toBar Q ⟨x, hSH hxS⟩) (toBar_mem_bar Q hxS)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hinj _ _ (mul_mem hsS hxS) (mul_mem hxS hsS) h1)
  have hzQ : z ∈ Q := (mem_inf.mp hz).2
  have hzS : z ∈ S := (mem_inf.mp hz).1
  have hcen := hE.mem_center_of_commute s.2 hs2 habC ht hzQ hz2 hz1 (hcomm t htS) hzt
    (hcomm z hzS)
  exact hM.false_of_mem_center hE hcen hs2 hs1

end MainCounterexample

@[expose] def IsOmegaInv (Q : Subgroup G) (x : G) : Prop :=
  x ^ 2 = 1 ∧ x ≠ 1 ∧ ∃ c : G, x ∈ rightConjugate Q c

omit [Finite G] in
theorem IsOmegaInv.conj {Q : Subgroup G} {x : G} (hx : IsOmegaInv Q x) (g : G) :
    IsOmegaInv Q (g * x * g⁻¹) := by
  obtain ⟨hx2, hx1, c, hxc⟩ := hx
  refine ⟨by rw [conj_pow, hx2]; group, fun h => hx1 ?_, c * g⁻¹, ?_⟩
  · rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group, h]
    group
  · rw [mem_rightConjugate_iff] at hxc ⊢
    rw [show c * g⁻¹ * (g * x * g⁻¹) * (c * g⁻¹)⁻¹ = c * x * c⁻¹ by group]
    exact hxc

structure EndSylow (Q : Subgroup G) where
  t : G
  ht : IsOverlapInv Q t
  S : Subgroup G
  hS : IsSylowOf 2 S (normalizer (Q : Set G))
  htS : t ∈ S

namespace EndSylow

variable {Q : Subgroup G} (X : EndSylow Q)

abbrev R : Subgroup G := X.S ⊓ Q

abbrev P : Subgroup G := X.R ⊔ zpowers X.t

omit [Finite G] in
theorem R_le_S : X.R ≤ X.S := inf_le_left

omit [Finite G] in
theorem P_le_S : X.P ≤ X.S := sup_le X.R_le_S ((zpowers_le).mpr X.htS)

omit [Finite G] in
theorem S_le : X.S ≤ normalizer (Q : Set G) := X.hS.le

omit [Finite G] in
theorem t_mem_normalizer_R : X.t ∈ normalizer (X.R : Set G) :=
  inf_normalizer_le_normalizer_inf _ _ (mem_inf.mpr ⟨le_normalizer X.htS, X.ht.mem_normalizer⟩)

omit [Finite G] in
theorem R_le_Q : X.R ≤ Q := inf_le_right

omit [Finite G] in
theorem R_le_P : X.R ≤ X.P := le_sup_left

omit [Finite G] in
theorem t_mem_P : X.t ∈ X.P := mem_sup_right (mem_zpowers _)

theorem mem_P_iff {x : G} : x ∈ X.P ↔ x ∈ X.R ∨ x * X.t ∈ X.R := by
  have ht2 := X.ht.1
  have ht1 := X.ht.2.1
  have htt : X.t * X.t = 1 := by rw [← pow_two]; exact ht2
  have hN : zpowers X.t ≤ normalizer (X.R : Set G) := (zpowers_le).mpr X.t_mem_normalizer_R
  constructor
  · intro hx
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hN] at hx
    obtain ⟨r, hr, b, hb, rfl⟩ := Set.mem_mul.mp hx
    rcases eq_one_or_eq_of_mem_zpowers ht2 ht1 hb with rfl | rfl
    · left
      rwa [mul_one]
    · right
      rwa [mul_assoc, htt, mul_one]
  · rintro (h | h)
    · exact X.R_le_P h
    · have : x = x * X.t * X.t := by rw [mul_assoc, htt, mul_one]
      rw [this]
      exact mul_mem (X.R_le_P h) X.t_mem_P

end EndSylow

namespace EndSetting

variable {Q : Subgroup G} (hE : EndSetting Q)
include hE

theorem mem_layer_of_mem_sup
    (hodd : Odd (Nat.card (centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))))
    {x : Bar Q} (hx : x ∈ bar Q (twoPrimeLayerIn Q) ⊔
      centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))
    (h2 : IsPGroup 2 (zpowers x)) : x ∈ bar Q (twoPrimeLayerIn Q) := by
  set L := bar Q (twoPrimeLayerIn Q) with hL
  set C := centralizer (L : Set (Bar Q)) with hC
  have hCN : C ≤ normalizer (L : Set (Bar Q)) := centralizer_le_normalizer _
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hCN] at hx
  obtain ⟨l, hl, c, hc, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 ⟨l * c, mem_zpowers _⟩
  have hk' : orderOf (l * c) = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨l * c, mem_zpowers _⟩ : zpowers (l * c))).trans hk
  have hlc : Commute l c := mem_centralizer_iff.mp hc l hl
  have hpow : l ^ 2 ^ k * c ^ 2 ^ k = 1 := by
    rw [← hlc.mul_pow, ← hk', pow_orderOf_eq_one]
  have hcL : c ^ 2 ^ k ∈ (⊥ : Subgroup (Bar Q)) := by
    rw [← hE.inf_centralizer_bar_eq_bot]
    refine mem_inf.mpr ⟨bar_mono Q (twoPrimeLayerIn_le Q) ?_, pow_mem hc _⟩
    rw [eq_inv_of_mul_eq_one_right hpow]
    exact inv_mem (pow_mem hl _)
  rw [mem_bot] at hcL
  have hco : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hcL
  have hcodd : orderOf c ∣ Nat.card C := by
    have := orderOf_dvd_natCard (⟨c, hc⟩ : C)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card C) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hco hcodd
  rw [orderOf_eq_one_iff.mp h1, mul_one]
  exact hl

end EndSetting

namespace EndSylow

variable {Q : Subgroup G} (X : EndSylow Q) (hE : EndSetting Q)
include hE

theorem mem_of_isOmegaInv
    (hodd : Odd (Nat.card (centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))))
    {x : G} (hxS : x ∈ X.S) (hx : IsOmegaInv Q x) : x ∈ X.P := by
  obtain ⟨hx2, hx1, c, hxc⟩ := hx
  by_cases hcH : c ∈ normalizer (Q : Set G)
  · rw [(rightConjugate_eq_self_iff Q c).mpr hcH] at hxc
    exact X.R_le_P (mem_inf.mpr ⟨hxS, hxc⟩)
  have hxN : x ∈ normalizer (Q : Set G) := X.S_le hxS
  have hov : IsOverlapInv Q x := ⟨hx2, hx1, hxN, c, hcH, hxc⟩
  have htN := X.ht.mem_normalizer
  have h1 := hE.mul_mem_layer_sup_centralizer X.ht hov.bar_sq (hE.hasCyclicSylowTwo_of_isOverlapInv hov)
  have htx : toBar Q ⟨X.t, htN⟩ * toBar Q ⟨x, hxN⟩ = toBar Q ⟨X.t * x, mul_mem htN hxN⟩ := by
    rw [← map_mul]
    rfl
  rw [htx] at h1
  have htxS : X.t * x ∈ X.S := mul_mem X.htS hxS
  have h2 : IsPGroup 2 (zpowers (toBar Q ⟨X.t * x, mul_mem htN hxN⟩)) :=
    (isPGroup_bar (D := Q) X.hS.isPGroup).to_le ((zpowers_le).mpr (toBar_mem_bar Q htxS))
  have h3 := hE.mem_layer_of_mem_sup hodd h1 h2
  have h4 : toBar Q ⟨X.t * x, mul_mem htN hxN⟩ ∈ bar Q (X.S ⊓ Q) := by
    rw [bar_inf_of_core_le (oddCoreIn_le Q)]
    exact mem_inf.mpr ⟨toBar_mem_bar Q htxS, bar_mono Q (twoPrimeLayerIn_le Q) h3⟩
  obtain ⟨r, hrR, hr⟩ := (mem_bar_iff Q _ _).mp h4
  have hreq : r = ⟨X.t * x, mul_mem htN hxN⟩ :=
    toBar_injOn_of_isPGroup X.hS.isPGroup (mem_inf.mp hrR).1 htxS hr
  have : x = X.t⁻¹ * (r : G) := by rw [hreq]; group
  rw [this]
  exact mul_mem (inv_mem X.t_mem_P) (X.R_le_P hrR)

theorem isOmegaInv_of_mem
    (M : PSLModel Q) {x : G} (hxP : x ∈ X.P) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) : IsOmegaInv Q x := by
  rcases X.mem_P_iff.mp hxP with h | h
  · exact ⟨hx2, hx1, 1, by rw [rightConjugate_one]; exact X.R_le_Q h⟩
  set t := X.t with htdef
  have htt : t * t = 1 := by rw [← pow_two]; exact X.ht.1
  have hrt : t⁻¹ * (x * t) * t ∈ X.R := by
    have := (mem_normalizer_iff.mp (inv_mem X.t_mem_normalizer_R) _).mp h
    simpa using this
  set r' := t⁻¹ * (x * t) * t with hr'
  have hxr : x = t * r' := by
    rw [hr', show t⁻¹ * (x * t) * t = t⁻¹ * x * (t * t) by group, htt, mul_one]
    group
  have hr'Q : r' ∈ Q := X.R_le_Q hrt
  have hr'L : toBar Q ⟨r', le_normalizer hr'Q⟩ ∈ bar Q (twoPrimeLayerIn Q) :=
    hE.mem_layer_of_isPGroup (toBar_mem_bar Q hr'Q)
      ((isPGroup_bar (D := Q) X.hS.isPGroup).to_le ((zpowers_le).mpr
        (toBar_mem_bar Q (X.R_le_S hrt))))
  obtain ⟨q, hq, hqt⟩ := M.exists_conj_eq_mul hE X.ht hr'Q hr'L (by rw [← hxr]; exact hx2)
  obtain ⟨g, -, htg⟩ := X.ht.2.2.2
  rw [hxr, ← hqt]
  exact IsOmegaInv.conj ⟨X.ht.1, X.ht.2.1, g, htg⟩ q

end EndSylow

end CFSG.ComponentClassification.Asc75T4
