module

public import CFSG.LargeExtraspecial.S14SMJOdd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMJ

open Subgroup CFSG.Open

variable {G : Type} [Group G]

@[expose] def conjSub (X : Subgroup G) (c : G) (h1 : ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (h2 : ∀ x ∈ X, c⁻¹ * x * c ∈ X) : X ≃* X where
  toFun x := ⟨c * x * c⁻¹, h1 x x.2⟩
  invFun x := ⟨c⁻¹ * x * c, h2 x x.2⟩
  left_inv x := Subtype.ext (by
    change c⁻¹ * (c * (x : G) * c⁻¹) * c = (x : G)
    group)
  right_inv x := Subtype.ext (by
    change c * (c⁻¹ * (x : G) * c) * c⁻¹ = (x : G)
    group)
  map_mul' a b := Subtype.ext (by
    change c * ((a : G) * (b : G)) * c⁻¹ = c * (a : G) * c⁻¹ * (c * (b : G) * c⁻¹)
    group)

theorem conj_mem_map_pCore [Finite G] (X : Subgroup G) {c : G} (h1 : ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (h2 : ∀ x ∈ X, c⁻¹ * x * c ∈ X) {r : G} (hr : r ∈ (CFSG.pCore 2 X).map X.subtype) :
    c * r * c⁻¹ ∈ (CFSG.pCore 2 X).map X.subtype := by
  obtain ⟨r', hr', rfl⟩ := hr
  have hmap := CFSG.pCore_map_iso 2 (conjSub X c h1 h2)
  refine ⟨conjSub X c h1 h2 r', ?_, rfl⟩
  rw [← hmap]
  exact ⟨r', hr', rfl⟩

theorem le_map_pCore [Finite G] {X P : Subgroup G} (hPX : P ≤ X)
    (hPn : ∀ c ∈ X, ∀ p ∈ P, c * p * c⁻¹ ∈ P) (hP2 : IsPGroup 2 P) :
    P ≤ (CFSG.pCore 2 X).map X.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (P.subgroupOf X).Normal := ⟨fun p hp c => by
    rw [mem_subgroupOf] at hp ⊢
    exact hPn c c.2 p hp⟩
  have h2 : IsPGroup 2 (P.subgroupOf X) := hP2.of_equiv (subgroupOfEquivOfLe hPX).symm
  have hle : P.subgroupOf X ≤ CFSG.pCore 2 X := le_sSup ⟨hn, h2⟩
  intro p hp
  exact ⟨⟨p, hPX hp⟩, hle (by rw [mem_subgroupOf]; exact hp), rfl⟩

theorem eq_one_or_z_of_mem_zpowers (S : Setting G) {c : G} (hc : c ∈ zpowers S.z) :
    c = 1 ∨ c = S.z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  rw [← zpow_mod_orderOf, S.orderOf_z]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

section LSet

variable [Finite G] {S : Setting G} {t u : G} (C : Cfg S t u) (L : Loc S t u)
  (hext : IsExtraspecialPGroup 2 ↥(S.QG ⊓ cent2 t u)) {K : Subgroup G}
  (hKH : K ≤ cent2 t u) (hKn : ∀ h ∈ cent2 t u, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hzK : S.z ∈ K)

include C L hext hKH hKn hzK in
theorem QH_le {x : G} (hx : IsConj S.z x) (hxK : x ∈ K) (hxz : x * S.z = S.z * x)
    (hne : x ≠ S.z) : S.QG ⊓ cent2 t u ≤ K := by
  have hxM : x ∈ S.M := S.mem_M_iff.mpr hxz
  have hxH := hKH hxK
  have hxQ : x ∉ S.QG := fun h => hne (L.weak x hx h hxH)
  obtain ⟨q₁, hq₁Q, hq₁H, hc1, hcz⟩ := exists_commutator_not_mem C L hext hxM hxQ hxH
  have hzH := z_mem_cent2 S C.htM C.huM
  have hcR : x * q₁ * x⁻¹ * q₁⁻¹ ∈ (S.QG ⊓ cent2 t u) ⊓ K := by
    have hcH : x * q₁ * x⁻¹ * q₁⁻¹ ∈ cent2 t u :=
      (cent2 t u).mul_mem ((cent2 t u).mul_mem ((cent2 t u).mul_mem hxH hq₁H)
        ((cent2 t u).inv_mem hxH)) ((cent2 t u).inv_mem hq₁H)
    refine ⟨⟨S.commutator_mem_QG hxM hq₁Q, hcH⟩, ?_⟩
    rw [show x * q₁ * x⁻¹ * q₁⁻¹ = x * (q₁ * x⁻¹ * q₁⁻¹) by group]
    exact mul_mem hxK (hKn q₁ hq₁H x⁻¹ (inv_mem hxK))
  rcases L.irr ((S.QG ⊓ cent2 t u) ⊓ K) ⟨⟨S.z_mem_QG, hzH⟩, hzK⟩ inf_le_left
      (fun c hc r hr => ⟨⟨S.conj_mem_QG hc.2 hr.1.1, (cent2 t u).mul_mem
        ((cent2 t u).mul_mem hc.1 hr.1.2) ((cent2 t u).inv_mem hc.1)⟩, hKn c hc.1 r hr.2⟩)
      with h | h
  · exfalso
    rw [h] at hcR
    rcases eq_one_or_z_of_mem_zpowers S hcR with h1 | h1
    · exact hc1 h1
    · exact hcz h1
  · exact fun q hq => (h hq).2

omit [Finite G] in
include hKH in
theorem QG_inf_eq (hQK : S.QG ⊓ cent2 t u ≤ K) : S.QG ⊓ cent2 t u = S.QG ⊓ K :=
  le_antisymm (le_inf inf_le_left hQK) (inf_le_inf_left _ hKH)

omit [Finite G] in
include hKH hext in
theorem extK (hQK : S.QG ⊓ cent2 t u ≤ K) : IsExtraspecialPGroup 2 ↥(S.QG ⊓ K) :=
  CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv
    (MulEquiv.subgroupCongr (QG_inf_eq hKH hQK)) hext

omit [Finite G] in
include L hKH in
theorem centK (hQK : S.QG ⊓ cent2 t u ≤ K) :
    ∀ c ∈ K, c ∈ S.M → (∀ q ∈ S.QG ⊓ K, c * q = q * c) → c ∈ S.QG :=
  fun c hc hcM h => L.cent c (hKH hc) hcM fun q hq => h q ((QG_inf_eq hKH hQK) ▸ hq)

include L hKH hKn in
theorem oTwoK : ∀ P : Subgroup G, P ≤ K ⊓ S.M → (∀ c ∈ K ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P) →
    IsPGroup 2 P → P ≤ S.QG := by
  intro P hP hPn hP2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (le_map_pCore hP hPn hP2).trans (L.oTwo _ ?_ ?_ (CFSG.pCore_isPGroup.map _))
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨hKH x.2.1, x.2.2⟩
  · intro c hc r hr
    refine conj_mem_map_pCore (K ⊓ S.M) (fun x hx => ⟨hKn c hc.1 x hx.1, ?_⟩)
      (fun x hx => ⟨?_, ?_⟩) hr
    · exact S.M.mul_mem (S.M.mul_mem hc.2 hx.2) (S.M.inv_mem hc.2)
    · simpa using hKn c⁻¹ ((cent2 t u).inv_mem hc.1) x hx.1
    · exact S.M.mul_mem (S.M.mul_mem (S.M.inv_mem hc.2) hx.2) hc.2

@[expose] noncomputable def setL (hQK : S.QG ⊓ cent2 t u ≤ K) : Setting ↥K :=
  subSetting S K hzK (extK hext hKH hQK) (centK L hKH hQK) (oTwoK L hKH hKn)

theorem mem_setL_QG_iff (hQK : S.QG ⊓ cent2 t u ≤ K) {x : ↥K} :
    x ∈ (setL L hext hKH hKn hzK hQK).QG ↔ (x : G) ∈ S.QG :=
  mem_subSetting_QG_iff S _ _ _ _ _

theorem setL_width (hQK : S.QG ⊓ cent2 t u ≤ K) {n : ℕ}
    (hn : Nat.card ↥(S.QG ⊓ cent2 t u) = 2 ^ (1 + 2 * n)) :
    (setL L hext hKH hKn hzK hQK).width = n :=
  subSetting_width S _ _ _ _ _ (by rw [← QG_inf_eq hKH hQK, hn])

theorem setL_weak (hQK : S.QG ⊓ cent2 t u ≤ K) (g : ↥K)
    (hg : g * (setL L hext hKH hKn hzK hQK).z * g⁻¹ ∈ (setL L hext hKH hKn hzK hQK).QG) :
    g * (setL L hext hKH hKn hzK hQK).z * g⁻¹ = (setL L hext hKH hKn hzK hQK).z := by
  rw [mem_setL_QG_iff] at hg
  apply Subtype.ext
  change (g : G) * S.z * (g : G)⁻¹ = S.z
  exact L.weak _ (isConj_iff.mpr ⟨g, rfl⟩) hg (hKH (K.mul_mem (K.mul_mem g.2 hzK) (K.inv_mem g.2)))

end LSet

theorem card_centralizer_conj (S : Setting G) {t : G} (ht : IsConj S.z t) :
    Nat.card ↥(centralizer ({t} : Set G)) = Nat.card S.M := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp ht
  refine Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ * x * g, (SME.mem_M_conj_iff S g x).mpr
        (mem_centralizer_singleton_iff.mp x.2)⟩
      invFun := fun x => ⟨g * x * g⁻¹, mem_centralizer_singleton_iff.mpr
        ((SME.mem_M_conj_iff S g (g * x * g⁻¹)).mp
          (by rw [show g⁻¹ * (g * (x : G) * g⁻¹) * g = x by group]; exact x.2))⟩
      left_inv := fun x => Subtype.ext (by
        change g * (g⁻¹ * (x : G) * g) * g⁻¹ = x
        group)
      right_inv := fun x => Subtype.ext (by
        change g⁻¹ * (g * (x : G) * g⁻¹) * g = x
        group) }

theorem false_of_dvd_card [Finite G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {t : G} (ht : IsConj S.z t) {K : Subgroup G}
    (hK : K ≤ centralizer ({t} : Set G)) {p : ℕ} (hp : p = 23 ∨ p = 43)
    (hpK : p ∣ Nat.card ↥K) : False := by
  have hdvd : Nat.card ↥K ∣ Nat.card ↥(centralizer ({t} : Set G)) := Subgroup.card_dvd_of_le hK
  obtain ⟨hidx, hMc⟩ := card_M_of_U6 S hw hU
  rw [card_centralizer_conj S ht, hMc] at hdvd
  have hp' := hpK.trans hdvd
  generalize (Mbar0 S).index = k at hidx hp'
  have hk : k ≤ 6 := Nat.le_of_dvd (by norm_num) hidx
  rcases hp with rfl | rfl <;> interval_cases k <;> revert hidx hp' <;> norm_num

theorem not_co2 [Finite G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {t : G} (ht : IsConj S.z t) {K : Subgroup G}
    (hK : K ≤ centralizer ({t} : Set G)) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Co2) :
    False := by
  refine false_of_dvd_card S hw hU ht hK (Or.inl rfl) ?_
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Co2.card_Co2]
  norm_num

theorem exists_conj_commute [Finite G] (S : Setting G) {K : Subgroup G} [IsSimpleGroup K]
    (hzK : S.z ∈ K) (hnc : ¬ ∀ k ∈ K, k * S.z = S.z * k) :
    ∃ g ∈ K, g * S.z * g⁻¹ * S.z = S.z * (g * S.z * g⁻¹) ∧ g * S.z * g⁻¹ ≠ S.z := by
  by_contra hno
  push Not at hno
  set zK : K := ⟨S.z, hzK⟩
  have hz1 : zK ≠ 1 := fun h => S.z_ne_one (congrArg Subtype.val h)
  have hz2 : zK * zK = 1 := Subtype.ext S.z_mul_z
  obtain ⟨N, hN, hodd, hNz⟩ := S10.exists_odd_normal_of_isolated zK hz1 hz2 fun g hg =>
    Subtype.ext (hno g g.2 (congrArg Subtype.val hg))
  rcases hN.eq_bot_or_eq_top with h | h
  · apply hnc
    intro k hk
    have h1 := hNz ⟨k, hk⟩
    rw [h, mem_bot] at h1
    have h2 : (⟨k, hk⟩ : K) * zK = zK * ⟨k, hk⟩ := by
      calc (⟨k, hk⟩ : K) * zK = ⟨k, hk⟩ * zK * (⟨k, hk⟩ : K)⁻¹ * zK⁻¹ * (zK * ⟨k, hk⟩) := by
            group
        _ = zK * ⟨k, hk⟩ := by rw [h1, one_mul]
    exact congrArg Subtype.val h2
  · have h2 : 2 ∣ Nat.card N := by
      rw [h, Subgroup.card_top, ← orderOf_eq_prime (p := 2) (by rw [sq, hz2]) hz1]
      exact orderOf_dvd_natCard zK
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end CFSG.LargeExtraspecial.S14.SMJ
