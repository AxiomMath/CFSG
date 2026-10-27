module

public import CFSG.LargeExtraspecial.S14SMJWeak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMJ

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_odd_of_mem_QG (S : Setting G) {x : G} (hx : Odd (orderOf x))
    (hxQ : x ∈ S.QG) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (S.pow_four_eq_one hxQ)
  have h2 : Nat.Coprime (orderOf x) (2 ^ 2) := (Nat.coprime_two_right.mpr hx).pow_right 2
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

omit [Finite G] in
theorem odd_orderOf_of_mem {N : Subgroup G} (hodd : Odd (Nat.card N)) {x : G} (hx : x ∈ N) :
    Odd (orderOf x) :=
  Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hx)

section FPF

variable {S : Setting G} {t u : G} {N : Subgroup G} (hNH : N ≤ cent2 t u)
  (hNn : ∀ h ∈ cent2 t u, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hodd : Odd (Nat.card N))

omit [Finite G] in
include hNn in
theorem commutator_mem_N {n q : G} (hn : n ∈ N) (hq : q ∈ cent2 t u) :
    n * q * n⁻¹ * q⁻¹ ∈ N := by
  have h := hNn q hq n⁻¹ (inv_mem hn)
  rw [show n * q * n⁻¹ * q⁻¹ = n * (q * n⁻¹ * q⁻¹) by group]
  exact mul_mem hn h

include hNH hNn hodd in
theorem eq_one_of_commute_z (L : Loc S t u) {n : G} (hn : n ∈ N) (hnz : n * S.z = S.z * n) :
    n = 1 := by
  have hnM : n ∈ S.M := S.mem_M_iff.mpr hnz
  have hnQ : n ∈ S.QG := by
    refine L.cent n (hNH hn) hnM fun q hq => ?_
    obtain ⟨hqQ, hqH⟩ := mem_inf.mp hq
    have hcN := commutator_mem_N hNn hn hqH
    have hcQ : n * q * n⁻¹ * q⁻¹ ∈ S.QG := S.QG.mul_mem (S.conj_mem_QG hnM hqQ) (S.QG.inv_mem hqQ)
    have h1 := eq_one_of_odd_of_mem_QG S (odd_orderOf_of_mem hodd hcN) hcQ
    calc n * q = n * q * n⁻¹ * q⁻¹ * (q * n) := by group
      _ = q * n := by rw [h1, one_mul]
  exact eq_one_of_odd_of_mem_QG S (odd_orderOf_of_mem hodd hn) hnQ

include hNH hNn hodd in
theorem eq_one_of_commute_y (k : G) (L' : Loc S (k⁻¹ * t * k) (k⁻¹ * u * k)) {n : G}
    (hn : n ∈ N) (hny : n * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * n) : n = 1 := by
  have hnM' : k⁻¹ * n * k ∈ S.M := (SME.mem_M_conj_iff S k n).mpr hny
  have hnQ : k⁻¹ * n * k ∈ S.QG := by
    refine L'.cent_conj k (hNH hn) hny fun q hqH hqQ => ?_
    have hcN := commutator_mem_N hNn hn hqH
    have hcQ : k⁻¹ * (n * q * n⁻¹ * q⁻¹) * k ∈ S.QG := by
      rw [show k⁻¹ * (n * q * n⁻¹ * q⁻¹) * k = (k⁻¹ * n * k) * (k⁻¹ * q * k) *
        (k⁻¹ * n * k)⁻¹ * (k⁻¹ * q * k)⁻¹ by group]
      exact S.QG.mul_mem (S.conj_mem_QG hnM' hqQ) (S.QG.inv_mem hqQ)
    have h1 := eq_one_of_odd_of_mem_QG S (by rw [orderOf_kconj]; exact odd_orderOf_of_mem hodd hcN)
      hcQ
    have h2 : n * q * n⁻¹ * q⁻¹ = 1 := by
      rw [show n * q * n⁻¹ * q⁻¹ = k * (k⁻¹ * (n * q * n⁻¹ * q⁻¹) * k) * k⁻¹ by group, h1]
      group
    calc n * q = n * q * n⁻¹ * q⁻¹ * (q * n) := by group
      _ = q * n := by rw [h2, one_mul]
  have h1 := eq_one_of_odd_of_mem_QG S (by rw [orderOf_kconj]; exact odd_orderOf_of_mem hodd hn)
    hnQ
  rw [show n = k * (k⁻¹ * n * k) * k⁻¹ by group, h1]
  group

end FPF

section Odd

variable {S : Setting G} {t u : G} (C : Cfg S t u) (L : Loc S t u)
  (hext : IsExtraspecialPGroup 2 ↥(S.QG ⊓ cent2 t u))

omit [Finite G] in
theorem inv_conj_of_inverts {N : Subgroup G}
    (hNn : ∀ h ∈ cent2 t u, ∀ n ∈ N, h * n * h⁻¹ ∈ N) {b : G} (hb : b ∈ cent2 t u)
    (hbinv : ∀ n ∈ N, b * n * b⁻¹ = n⁻¹) {n : G} (hn : n ∈ N) : b⁻¹ * n * b = n⁻¹ := by
  have hm : b⁻¹ * n * b ∈ N := by simpa using hNn b⁻¹ (inv_mem hb) n hn
  have h := hbinv _ hm
  rw [show b * (b⁻¹ * n * b) * b⁻¹ = n by group] at h
  calc b⁻¹ * n * b = ((b⁻¹ * n * b)⁻¹)⁻¹ := (inv_inv _).symm
    _ = n⁻¹ := by rw [← h]

omit [Finite G] in
theorem commute_of_inverts {N : Subgroup G}
    (hNn : ∀ h ∈ cent2 t u, ∀ n ∈ N, h * n * h⁻¹ ∈ N) {a b : G} (hb : b ∈ cent2 t u)
    (hainv : ∀ n ∈ N, a * n * a⁻¹ = n⁻¹) (hbinv : ∀ n ∈ N, b * n * b⁻¹ = n⁻¹) {n : G}
    (hn : n ∈ N) : a * b⁻¹ * n = n * (a * b⁻¹) := by
  have h1 := inv_conj_of_inverts hNn hb hbinv hn
  have h2 := hainv _ (inv_mem hn)
  calc a * b⁻¹ * n = a * (b⁻¹ * n * b) * a⁻¹ * (a * b⁻¹) := by group
    _ = a * n⁻¹ * a⁻¹ * (a * b⁻¹) := by rw [h1]
    _ = n * (a * b⁻¹) := by rw [h2, inv_inv]

include C L hext in
theorem exists_commutator_not_mem {y : G} (hyM : y ∈ S.M) (hyQ : y ∉ S.QG)
    (hyH : y ∈ cent2 t u) : ∃ q ∈ S.QG, q ∈ cent2 t u ∧ y * q * y⁻¹ * q⁻¹ ≠ 1 ∧
      y * q * y⁻¹ * q⁻¹ ≠ S.z := by
  by_contra hno
  push Not at hno
  apply hyQ
  have hyM' : (⟨y, hyH⟩ : ↥(cent2 t u)) ∈ (setH C L hext).M := (mem_setH_M_iff C L hext).mpr hyM
  refine (mem_setH_QG_iff C L hext).mp ((setH C L hext).mem_QG_of_cl_conj hyM' fun x hx => ?_)
  have hxQ : (x : G) ∈ S.QG := (mem_setH_QG_iff C L hext).mp hx
  rw [(setH C L hext).cl_eq_cl_iff ((setH C L hext).conj_mem_QG hyM' hx) hx]
  by_cases h1 : y * (x : G) * y⁻¹ * (x : G)⁻¹ = 1
  · left
    apply Subtype.ext
    change (x : G) = y * (x : G) * y⁻¹
    calc (x : G) = (y * (x : G) * y⁻¹ * (x : G)⁻¹)⁻¹ * (y * (x : G) * y⁻¹) := by group
      _ = y * (x : G) * y⁻¹ := by rw [h1, inv_one, one_mul]
  · right
    have h2 := hno x hxQ x.2 h1
    apply Subtype.ext
    change (x : G) = y * (x : G) * y⁻¹ * S.z
    calc (x : G) = (x : G) * S.z * S.z := by rw [mul_assoc, S.z_mul_z, mul_one]
      _ = S.z * (x : G) * S.z := by rw [S.z_comm_QG hxQ]
      _ = y * (x : G) * y⁻¹ * (x : G)⁻¹ * (x : G) * S.z := by rw [h2]
      _ = y * (x : G) * y⁻¹ * S.z := by group

omit [Finite G] in
include C L hext in
theorem exists_commutator_eq_z {c : G} (hcQ : c ∈ S.QG) (hcH : c ∈ cent2 t u) (hc1 : c ≠ 1)
    (hcz : c ≠ S.z) : ∃ q ∈ S.QG, q ∈ cent2 t u ∧ c * q * c⁻¹ * q⁻¹ = S.z := by
  obtain ⟨q, hqQ, hqH, hne⟩ : ∃ q ∈ S.QG, q ∈ cent2 t u ∧ c * q ≠ q * c := by
    by_contra hno
    push Not at hno
    rcases (setH C L hext).eq_one_or_z_of_commute (x := ⟨c, hcH⟩)
      ((mem_setH_QG_iff C L hext).mpr hcQ)
      (fun w hw => Subtype.ext (hno w ((mem_setH_QG_iff C L hext).mp hw) w.2)) with h | h
    · exact hc1 (congrArg Subtype.val h)
    · exact hcz (congrArg Subtype.val h)
  refine ⟨q, hqQ, hqH, ?_⟩
  rcases S.commutator_eq_one_or_z hcQ hqQ with h | h
  · exfalso
    apply hne
    calc c * q = c * q * c⁻¹ * q⁻¹ * (q * c) := by group
      _ = q * c := by rw [h, one_mul]
  · exact h

include C L hext in
theorem eq_bot_of_odd
    (hM : SmithE22Module) (hLoc : SmithE23a) [IsSimpleGroup G]
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {N : Subgroup G}
    (hNH : N ≤ cent2 t u) (hNn : ∀ h ∈ cent2 t u, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  obtain ⟨y, hy, hyM, hyQ, hyH⟩ := L.exists_y
  obtain ⟨k, hk⟩ := isConj_iff.mp hy
  have L' := Loc.of hM hLoc hw hU (C.conj k (hk ▸ hyH))
  have hzH := z_mem_cent2 S C.htM C.huM
  have hinvz : ∀ n ∈ N, S.z * n * S.z⁻¹ = n⁻¹ := fun n hn =>
    conj_eq_inv_of_fixedPointFree (hNn S.z hzH) S.z_mul_z
      (fun m hm hmz => eq_one_of_commute_z hNH hNn hodd L hm hmz) hn
  have hinvy : ∀ n ∈ N, y * n * y⁻¹ = n⁻¹ := fun n hn =>
    conj_eq_inv_of_fixedPointFree (hNn y hyH) (SmithQ.mul_self_eq_one_of_isConj S hy)
      (fun m hm hmy => eq_one_of_commute_y hNH hNn hodd k L' hm (hk ▸ hmy)) hn
  have hcomm : ∀ q ∈ cent2 t u, ∀ n ∈ N,
      y * q * y⁻¹ * q⁻¹ * n = n * (y * q * y⁻¹ * q⁻¹) := by
    intro q hq n hn
    have hyq : q * y * q⁻¹ ∈ cent2 t u := mul_mem (mul_mem hq hyH) (inv_mem hq)
    have hinvyq : ∀ m ∈ N, q * y * q⁻¹ * m * (q * y * q⁻¹)⁻¹ = m⁻¹ := by
      intro m hm
      have hm' : q⁻¹ * m * q ∈ N := by simpa using hNn q⁻¹ (inv_mem hq) m hm
      have h := hinvy _ hm'
      calc q * y * q⁻¹ * m * (q * y * q⁻¹)⁻¹ = q * (y * (q⁻¹ * m * q) * y⁻¹) * q⁻¹ := by
            group
        _ = q * (q⁻¹ * m * q)⁻¹ * q⁻¹ := by rw [h]
        _ = m⁻¹ := by group
    have h := commute_of_inverts hNn hyq hinvy hinvyq hn
    rwa [show y * (q * y * q⁻¹)⁻¹ = y * q * y⁻¹ * q⁻¹ by group] at h
  obtain ⟨q₁, hq₁Q, hq₁H, hc1, hcz⟩ := exists_commutator_not_mem C L hext hyM hyQ hyH
  have hcQ : y * q₁ * y⁻¹ * q₁⁻¹ ∈ S.QG := S.commutator_mem_QG hyM hq₁Q
  have hcH : y * q₁ * y⁻¹ * q₁⁻¹ ∈ cent2 t u :=
    mul_mem (mul_mem (mul_mem hyH hq₁H) (inv_mem hyH)) (inv_mem hq₁H)
  obtain ⟨q₂, -, hq₂H, hcq⟩ := exists_commutator_eq_z C L hext hcQ hcH hc1 hcz
  set c := y * q₁ * y⁻¹ * q₁⁻¹ with hc
  have hzc : ∀ n ∈ N, S.z * n = n * S.z := by
    intro n hn
    have h1 : Commute c n := hcomm q₁ hq₁H n hn
    have hm : q₂⁻¹ * n * q₂ ∈ N := by simpa using hNn q₂⁻¹ (inv_mem hq₂H) n hn
    have h2 := hcomm q₁ hq₁H _ hm
    have h3 : Commute (q₂ * c * q₂⁻¹) n := by
      change q₂ * c * q₂⁻¹ * n = n * (q₂ * c * q₂⁻¹)
      calc q₂ * c * q₂⁻¹ * n = q₂ * (c * (q₂⁻¹ * n * q₂)) * q₂⁻¹ := by group
        _ = q₂ * ((q₂⁻¹ * n * q₂) * c) * q₂⁻¹ := by rw [h2]
        _ = n * (q₂ * c * q₂⁻¹) := by group
    have h4 : Commute (c * (q₂ * c * q₂⁻¹)⁻¹) n := h1.mul_left h3.inv_left
    rw [← hcq, show c * q₂ * c⁻¹ * q₂⁻¹ = c * (q₂ * c * q₂⁻¹)⁻¹ by group]
    exact h4.eq
  rw [eq_bot_iff]
  intro n hn
  rw [mem_bot]
  have hnn : n⁻¹ = n := by
    rw [← hinvz n hn, hzc n hn, mul_inv_cancel_right]
  have h2 : n ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [← hnn]
    exact mul_inv_cancel n
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    (Nat.coprime_two_right.mpr (odd_orderOf_of_mem hodd hn)) hdvd)

include C L hext in
theorem setH_oddCore
    (hM : SmithE22Module) (hLoc : SmithE23a) [IsSimpleGroup G]
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    timmesfeldOddCore ↥(cent2 t u) = ⊥ := by
  unfold timmesfeldOddCore
  rw [sSup_eq_bot]
  rintro N ⟨hN, hodd⟩
  have hN' := eq_bot_of_odd C L hext hM hLoc hw hU (N := N.map (cent2 t u).subtype)
    (map_subtype_le N) ?_ ?_
  · exact (map_eq_bot_iff_of_injective N (cent2 t u).subtype_injective).mp hN'
  · rintro h hh _ ⟨n, hnN, rfl⟩
    exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hN.conj_mem n hnN ⟨h, hh⟩, rfl⟩
  · rwa [card_map_of_injective (cent2 t u).subtype_injective]

include C L hext in
theorem setH_z_not_mem_center
    (hM : SmithE22Module) (hLoc : SmithE23a) [IsSimpleGroup G]
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    (setH C L hext).z ∉ center ↥(cent2 t u) := by
  intro hz
  obtain ⟨y, hy, -, hyQ, hyH⟩ := L.exists_y
  obtain ⟨k, hk⟩ := isConj_iff.mp hy
  have L' := Loc.of hM hLoc hw hU (C.conj k (hk ▸ hyH))
  have hzH := z_mem_cent2 S C.htM C.huM
  have hcomm : ∀ x ∈ cent2 t u, S.z * x = x * S.z := fun x hx =>
    (congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩)).symm
  have hzQy : k⁻¹ * S.z * k ∈ S.QG :=
    L'.cent_conj k hzH (hk ▸ hcomm y hyH) fun q hq _ => hcomm q hq
  have hne : (1 : G) * S.z * 1⁻¹ ≠ k * S.z * k⁻¹ := by
    rw [hk, one_mul, inv_one, mul_one]
    intro h
    exact hyQ (h ▸ S.z_mem_QG)
  have h := SME.mem_Qa_symm S (g := k) (k := 1) (by simpa using hzQy) hne
  apply hyQ
  rw [← hk]
  simpa using h

end Odd

end CFSG.LargeExtraspecial.S14.SMJ
