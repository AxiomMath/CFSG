module

public import CFSG.GH74.Uniqueness.SU.SU4Conj
public import CFSG.GH74.Uniqueness.SU.SU1NormalFour
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

variable {G : Type} [Group G]

section Finite

variable [Finite G]

theorem isSylowIn_iff_card {X P : Subgroup G} :
    IsSylowIn X P ↔ P ≤ X ∧ ∃ k m : ℕ, Nat.card P = 2 ^ k ∧ Odd m ∧ Nat.card X = 2 ^ k * m := by
  constructor
  · rintro ⟨hPX, hP, hodd⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
    refine ⟨hPX, k, P.relIndex X, hk, hodd, ?_⟩
    have := Subgroup.relIndex_mul_card (H := P) (K := X)
    rw [inf_eq_left.mpr hPX, hk] at this
    rw [← this, mul_comm]
  · rintro ⟨hPX, k, m, hk, hm, hX⟩
    refine ⟨hPX, IsPGroup.of_card hk, ?_⟩
    have := Subgroup.relIndex_mul_card (H := P) (K := X)
    rw [inf_eq_left.mpr hPX, hk, hX] at this
    have h2 : 0 < 2 ^ k := pow_pos two_pos k
    have : P.relIndex X = m := by
      have h3 : 2 ^ k * P.relIndex X = 2 ^ k * m := by rw [mul_comm]; exact this
      exact Nat.eq_of_mul_eq_mul_left h2 h3
    rw [this]
    exact hm

omit [Finite G] in
theorem IsSylowIn.le {X P : Subgroup G} (h : IsSylowIn X P) : P ≤ X := h.1

omit [Finite G] in
theorem IsSylowIn.isPGroup {X P : Subgroup G} (h : IsSylowIn X P) : IsPGroup 2 P := h.2.1

theorem IsSylowIn.conj {X P : Subgroup G} (h : IsSylowIn X P) (g : G) :
    IsSylowIn (conjSub g X) (conjSub g P) := by
  rw [isSylowIn_iff_card] at h ⊢
  obtain ⟨hPX, k, m, hk, hm, hX⟩ := h
  exact ⟨conjSub_mono hPX, k, m, by rw [card_conjSub, hk], hm, by rw [card_conjSub, hX]⟩

omit [Finite G] in
theorem IsSylowIn.of_le {X Y P : Subgroup G} (h : IsSylowIn X P) (hPY : P ≤ Y) (hYX : Y ≤ X) :
    IsSylowIn Y P := by
  obtain ⟨hPX, hP, hodd⟩ := h
  refine ⟨hPY, hP, ?_⟩
  have := Subgroup.relIndex_mul_relIndex P Y X hPY hYX
  rw [← this] at hodd
  exact (Nat.odd_mul.mp hodd).1

theorem IsSylowIn.exists_conj_le {X P K : Subgroup G} (h : IsSylowIn X P) (hKX : K ≤ X)
    (hK : IsPGroup 2 K) : ∃ c ∈ X, conjSub c⁻¹ K ≤ P := by
  obtain ⟨c, hc, hcK⟩ := CFSG.GH74.GLS.Bg.Thompson.exists_conj_into_sylow (p := 2) hKX hK h.1 h.2.1
    (by
      have := h.2.2
      rw [Nat.odd_iff] at this
      omega)
  refine ⟨c, hc, fun y hy => ?_⟩
  rw [mem_conjSub] at hy
  have := hcK _ hy
  rwa [show c⁻¹ * (c⁻¹⁻¹ * y * c⁻¹) * c = y by group] at this

theorem exists_isSylowIn (X : Subgroup G) : ∃ P, IsSylowIn X P := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥X) := inferInstance
  refine ⟨(S : Subgroup ↥X).map X.subtype, ?_⟩
  have hsub : ((S : Subgroup ↥X).map X.subtype).subgroupOf X = S := by
    unfold Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact S.isPGroup'.map _
  · have h1 : ((S : Subgroup ↥X).map X.subtype).relIndex X = (S : Subgroup ↥X).index := by
      unfold Subgroup.relIndex
      rw [hsub]
    rw [h1]
    have := S.not_dvd_index
    rw [Nat.odd_iff]
    omega

theorem exists_isSylowIn_ge {X K : Subgroup G} (hKX : K ≤ X) (hK : IsPGroup 2 K) :
    ∃ P, IsSylowIn X P ∧ K ≤ P := by
  obtain ⟨P₀, hP₀⟩ := exists_isSylowIn X
  obtain ⟨c, hc, hcK⟩ := hP₀.exists_conj_le hKX hK
  refine ⟨conjSub c P₀, ?_, ?_⟩
  · have := hP₀.conj c
    rwa [conjSub_self_of_mem hc] at this
  · have := conjSub_mono (g := c) hcK
    rwa [conjSub_conjSub_inv] at this

theorem IsSylowIn.card_le {X P K : Subgroup G} (hP : IsSylowIn X P) (hKX : K ≤ X) (hK : IsPGroup 2 K) :
    Nat.card K ≤ Nat.card P := by
  obtain ⟨c, hc, hcK⟩ := hP.exists_conj_le hKX hK
  calc Nat.card K = Nat.card (conjSub c⁻¹ K) := (card_conjSub _ _).symm
    _ ≤ Nat.card P := Subgroup.card_le_of_le hcK

theorem IsSylowIn.exists_conj_eq {X P Q : Subgroup G} (hP : IsSylowIn X P) (hQ : IsSylowIn X Q) :
    ∃ c ∈ X, Q = conjSub c P := by
  obtain ⟨c, hc, hcP⟩ := hQ.exists_conj_le hP.1 hP.2.1
  refine ⟨c⁻¹, X.inv_mem hc, ?_⟩
  symm
  exact Subgroup.eq_of_le_of_card_ge hcP (by rw [card_conjSub]; exact hP.card_le hQ.1 hQ.2.1)

theorem IsSylowIn.eq_of_le {X P K : Subgroup G} (hP : IsSylowIn X P) (hKX : K ≤ X) (hK : IsPGroup 2 K)
    (hPK : P ≤ K) : K = P :=
  (Subgroup.eq_of_le_of_card_ge hPK (hP.card_le hKX hK)).symm

theorem IsSylowIn.of_ge {X P K : Subgroup G} (hP : IsSylowIn X P) (hKX : K ≤ X) (hK : IsPGroup 2 K)
    (hPK : P ≤ K) : IsSylowIn X K := by
  rw [hP.eq_of_le hKX hK hPK]
  exact hP

theorem IsSylowIn.pRank_eq {X P : Subgroup G} (hP : IsSylowIn X P) : Open.pRank 2 P = Open.pRank 2 X := by
  refine le_antisymm (SU1.pRank_mono (by norm_num) hP.1) ?_
  obtain ⟨E, hEX, hE, hEc⟩ := SU1.exists_pRank (p := 2) (by norm_num) X
  have hEp : IsPGroup 2 E := IsPGroup.of_card hEc
  obtain ⟨c, hc, hcE⟩ := hP.exists_conj_le hEX hEp
  exact SU1.le_pRank (by norm_num) hcE (isElemAbelian_conjSub hE) (by rw [card_conjSub]; exact hEc)

theorem sylow_isSylowIn_top (S : Sylow 2 G) : IsSylowIn ⊤ (S : Subgroup G) := by
  refine ⟨le_top, S.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  have := S.not_dvd_index
  rw [Nat.odd_iff]
  omega

end Finite

variable {G : Type} [Group G]

section Finite

variable [Finite G]

theorem exists_isNormalEp2 {P : Subgroup G} (hP : IsPGroup 2 P)
    (h3 : 3 ≤ Open.pRank 2 P) : ∃ U, SU1.IsNormalEp2 2 P U := by
  obtain ⟨U, hUP, hUn, hUe, hUc⟩ := SU1.exists_normal_fourGroup_of_pRank_ge_three hP h3
  exact ⟨U, hUP, hUn, hUe, by rw [hUc]; norm_num⟩

omit [Finite G] in
theorem sq_mem_of_relIndex_le_two [Finite G] {C P : Subgroup G} (hC : C.relIndex P ≤ 2) {y : G}
    (hy : y ∈ P) : y * y ∈ C := by
  have h0 : C.relIndex P ≠ 0 := SU1.relIndex_ne_zero_of_finite C P
  have hcases : C.relIndex P = 1 ∨ C.relIndex P = 2 := by omega
  rcases hcases with h1 | h2
  · rw [Subgroup.relIndex_eq_one] at h1
    exact C.mul_mem (h1 hy) (h1 hy)
  · have := Subgroup.mul_self_mem_of_index_two (H := C.subgroupOf P) h2 ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.mp this

theorem exists_central_involution {S : Subgroup G} (hS : IsPGroup 2 S) (hne : S ≠ ⊥) :
    ∃ z ∈ S, z * z = 1 ∧ z ≠ 1 ∧ ∀ s ∈ S, s * z = z * s := by
  obtain ⟨z, hzS, hz1, hzc⟩ := SU1.exists_central_of_normal Nat.prime_two hS le_rfl
    (fun g hg u hu => S.mul_mem (S.mul_mem hg hu) (S.inv_mem hg)) hne
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hS ⟨z, hzS⟩
  have hk' : orderOf z = 2 ^ k := (Subgroup.orderOf_coe (⟨z, hzS⟩ : S)).trans hk
  have hk1 : 1 ≤ k := by
    by_contra hcon
    have : k = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hk'
    exact hz1 hk'
  set w := z ^ (2 ^ (k - 1)) with hw
  have hdvd : 2 ^ (k - 1) ∣ orderOf z := by rw [hk']; exact pow_dvd_pow 2 (by omega)
  have hwo : orderOf w = 2 := by
    rw [hw, orderOf_pow_of_dvd (by positivity) hdvd, hk']
    rw [show 2 ^ k = 2 ^ (k - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel hk1]]
    rw [Nat.mul_div_cancel_left _ (by positivity)]
  have hw2 : w * w = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hwo])
  refine ⟨w, S.pow_mem hzS _, hw2, ?_, fun s hs => ?_⟩
  · intro h
    rw [h, orderOf_one] at hwo
    omega
  · exact (Commute.pow_right (show Commute s z from hzc s hs) _).eq

omit [Finite G] in
theorem exists_orderOf_four {P V : Subgroup G} (hP : IsPGroup 2 P) (hV : ∀ v ∈ V, v * v = 1)
    (hinv : ∀ s ∈ P, s * s = 1 → s ∈ V) {s : G} (hsP : s ∈ P) (hsV : s ∉ V) :
    ∃ y ∈ P, orderOf y = 4 ∧ y ∉ V ∧ y * y ∈ V ∧ y * y ≠ 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hP ⟨s, hsP⟩
  have hk' : orderOf s = 2 ^ k := (Subgroup.orderOf_coe (⟨s, hsP⟩ : P)).trans hk
  have hk2 : 2 ≤ k := by
    by_contra hcon
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · have : k = 0 := by omega
      rw [this, pow_zero, orderOf_eq_one_iff] at hk'
      exact hsV (hk' ▸ V.one_mem)
    · have : k = 1 := by omega
      rw [this, pow_one] at hk'
      have : s * s = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hk'])
      exact hsV (hinv s hsP this)
  set y := s ^ (2 ^ (k - 2)) with hy
  have hdvd : 2 ^ (k - 2) ∣ orderOf s := by rw [hk']; exact pow_dvd_pow 2 (by omega)
  have hyo : orderOf y = 4 := by
    rw [hy, orderOf_pow_of_dvd (by positivity) hdvd, hk']
    rw [show 2 ^ k = 2 ^ (k - 2) * 4 by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hk2]]
    rw [Nat.mul_div_cancel_left _ (by positivity)]
  have hyP : y ∈ P := P.pow_mem hsP _
  have hyy : y * y ≠ 1 := by
    intro h
    have : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h)
    rw [hyo] at this
    omega
  have hyy2 : (y * y) * (y * y) = 1 := by
    have : y ^ 4 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
    calc (y * y) * (y * y) = y ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  have hyyV : y * y ∈ V := hinv _ (P.mul_mem hyP hyP) hyy2
  refine ⟨y, hyP, hyo, fun hyV => hyy (hV y hyV), hyyV, hyy⟩

theorem eight_lt_card_of_rank_three {S : Subgroup G} (h3 : 3 ≤ Open.pRank 2 S) {x : G}
    (hx : x ∈ S) (hc : Nat.card ↥(S ⊓ centralizer ({x} : Set G)) ≤ 4) : 8 < Nat.card S := by
  obtain ⟨E, hES, hE, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two h3
  have h8 : 8 ≤ Nat.card S := by
    have := Subgroup.card_le_of_le hES
    rw [hEc] at this
    simpa using this
  by_contra hcon
  have hS8 : Nat.card S = 8 := by omega
  have hES' : E = S := Subgroup.eq_of_le_of_card_ge hES (by rw [hS8]; omega)
  have hcomm := (SU1.isElemAbelian_iff.mp hE).1
  have hle : S ≤ S ⊓ centralizer ({x} : Set G) := by
    intro s hs
    refine ⟨hs, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact hcomm s (by rw [hES']; exact hs) x (by rw [hES']; exact hx)
  have := Subgroup.card_le_of_le hle
  omega

end Finite

end CFSG.GH74.Uniqueness.SU.SU4
