module

public import CFSG.GH74.Uniqueness.SU.SU13TC5Q
public import CFSG.GH74.Uniqueness.SU.SU13TC5Gen
public import CFSG.Walter.W67.W2Cor32A

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

section Main

variable {e : Elts G z} {e9 : Elts9 z e} (f : FPart9 z e) (E9 : EPart9 z e e9 f.toFPart) (hWc : WAbel e)

theorem not_odd_orderOf_mul_z (hz : orderOf z = 2)
    (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) {a : G} (ha : a ∈ Asub E9 hWc) :
    ¬ Odd (orderOf (a * z)) := by
  intro ⟨k, hk⟩
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have hz2 : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have ha' : z * a * z⁻¹ ∈ Asub E9 hWc := z_conj_A f E9 hWc a ha
  have hsq : (a * z) * (a * z) = a * (z * a * z⁻¹) := by
    calc (a * z) * (a * z) = a * (z * a * z⁻¹) * (z * z) := by group
      _ = a * (z * a * z⁻¹) := by rw [hz2, mul_one]
  have hsqA : (a * z) * (a * z) ∈ Asub E9 hWc := by rw [hsq]; exact mul_mem ha ha'
  have hmem : a * z ∈ Asub E9 hWc := by
    have h2 : (a * z) = ((a * z) * (a * z)) ^ (k + 1) := by
      have h1 : (a * z) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, h1, one_mul]
    rw [h2]
    exact pow_mem hsqA _
  have hzA : z ∈ Asub E9 hWc := by
    have h := mul_mem (inv_mem ha) hmem
    have e1 : a⁻¹ * (a * z) = z := by group
    rwa [e1] at h
  have h4 := A_exp f E9 hWc hW5 hz z hzA
  apply hz1
  calc z = z ^ 3 * (z * z)⁻¹ := by group
    _ = 1 := by rw [h4, hz2, inv_one, mul_one]

theorem Q_inf_cent_z (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (l : Lem232 z e) :
    oc (normalizer ((Asub E9 hWc : Subgroup G) : Set G)) ⊓ centralizer ({z} : Set G) = E9.E := by
  set X : Subgroup G := normalizer ((Asub E9 hWc : Subgroup G) : Set G) with hX
  have hNA := NHE_le_normalizer_A f E9 hWc hz hW5 l
  have hAX : Asub E9 hWc ≤ X := le_normalizer
  have hAodd : Odd (Nat.card (Asub E9 hWc)) := by rw [A_card f E9 hWc hz hW5]; decide
  have hAQ : Asub E9 hWc ≤ oc X :=
    le_oc_of_normal_odd hAX (fun g hg a ha => (mem_normalizer_iff.mp hg a).mp ha) hAodd
  apply le_antisymm
  · refine E9.noOdd (oc X ⊓ centralizer ({z} : Set G)) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxQ, hxz⟩ := mem_inf.mp hx
      rw [← NHE_eq f E9 hWc hz hW5 l]
      exact mem_inf.mpr ⟨oc_le X hxQ, hxz⟩
    · intro g hg n hn
      have hgX : g ∈ X := hNA hg
      obtain ⟨hnQ, hnz⟩ := mem_inf.mp hn
      refine mem_inf.mpr ⟨conj_mem_oc hgX hnQ, ?_⟩
      rw [mem_centralizer_singleton_iff] at hnz ⊢
      have hgz : g * z = z * g := mem_centralizer_singleton_iff.mp (mem_inf.mp hg).2
      have hgi : g⁻¹ * z = z * g⁻¹ := (Commute.inv_left (show Commute g z from hgz)).eq
      calc g * n * g⁻¹ * z = g * n * (g⁻¹ * z) := by group
        _ = g * n * (z * g⁻¹) := by rw [hgi]
        _ = g * (n * z) * g⁻¹ := by group
        _ = g * (z * n) * g⁻¹ := by rw [hnz]
        _ = (g * z) * n * g⁻¹ := by group
        _ = (z * g) * n * g⁻¹ := by rw [hgz]
        _ = z * (g * n * g⁻¹) := by group
    · exact Odd.of_dvd_nat (odd_card_oc X) (Subgroup.card_dvd_of_le inf_le_left)
  · intro x hx
    exact mem_inf.mpr ⟨hAQ (mem_sup_left hx),
      mem_centralizer_singleton_iff.mpr (E9.Es_comm x (E9.Es_ge hx))⟩

theorem card_Q (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (l : Lem232 z e) (hm : MPart9 z e E9.E) :
    Nat.card (oc (normalizer ((Asub E9 hWc : Subgroup G) : Set G))) =
      3 * (Nat.card (oc (normalizer ((Asub E9 hWc : Subgroup G) : Set G)) ⊓ centralizer ({e.t} : Set G) :
        Subgroup G) * Nat.card (oc (normalizer ((Asub E9 hWc : Subgroup G) : Set G)) ⊓
          centralizer ({e.t} : Set G) : Subgroup G)) := by
  set X : Subgroup G := normalizer ((Asub E9 hWc : Subgroup G) : Set G) with hX
  have : IsKleinFour (kfour hz e) := isKleinFour_kfour hz e
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have ht1 : e.t ≠ 1 := by
    intro h; have := e.t_ord; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have hNA := NHE_le_normalizer_A f E9 hWc hz hW5 l
  have hQodd : Odd (Nat.card (oc X)) := odd_card_oc X
  have htzN : e.t * z ∈ NHE E9.E z := (NHE E9.E z).mul_mem (t_mem_NHE f E9) (z_mem_NHE f E9)
  have hTn : kfour hz e ≤ normalizer ((oc X : Subgroup G) : Set G) := by
    intro x hx
    rcases kfour_mem hz e hx with rfl | rfl | rfl | rfl
    · exact le_normalizer_oc X (hNA htzN)
    · exact le_normalizer_oc X (hNA (t_mem_NHE f E9))
    · exact le_normalizer_oc X (hNA (z_mem_NHE f E9))
    · exact one_mem _
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq (T := kfour hz e) (K := oc X)
    hQodd hTn (a := e.t) (b := z) (t_mem_kfour hz e) (z_mem_kfour hz e) ht1 hz1 e.t_ne
  have hQR : oc X ⊓ centralizer ((kfour hz e : Subgroup G) : Set G) = zpowers e.s₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxQ, hxK⟩ := mem_inf.mp hx
      have hxz : x * z = z * x := (mem_centralizer_iff.mp hxK z (z_mem_kfour hz e)).symm
      have hxt : e.t * x = x * e.t := mem_centralizer_iff.mp hxK e.t (t_mem_kfour hz e)
      have hxE : x ∈ E9.E := by
        have : x ∈ oc X ⊓ centralizer ({z} : Set G) :=
          mem_inf.mpr ⟨hxQ, mem_centralizer_singleton_iff.mpr hxz⟩
        rwa [Q_inf_cent_z f E9 hWc hz hW5 l] at this
      exact hm.cent_t x hxE hxt
    · intro x hx
      have hxE : x ∈ E9.E := zpowers_s₂_le_E f E9 hx
      have hAodd : Odd (Nat.card (Asub E9 hWc)) := by rw [A_card f E9 hWc hz hW5]; decide
      have hAQ : Asub E9 hWc ≤ oc X :=
        le_oc_of_normal_odd le_normalizer (fun g hg a ha => (mem_normalizer_iff.mp hg a).mp ha) hAodd
      refine mem_inf.mpr ⟨hAQ (mem_sup_left hxE), mem_centralizer_iff.mpr fun y hy => ?_⟩
      obtain ⟨k, rfl⟩ := hx
      have hcy : Commute y e.s₂ := by
        rcases kfour_mem hz e hy with rfl | rfl | rfl | rfl
        · exact Commute.mul_left e.t_s₂ e.s₂_comm.symm
        · exact e.t_s₂
        · exact e.s₂_comm.symm
        · exact Commute.one_left _
      exact (hcy.zpow_right k).eq
  have htz2 : orderOf (e.t * z) = 2 := orderOf_mul_eq_two_of_commute e.t_ord hz e.t_comm e.t_ne
  have htzz : e.t * z ≠ z := by
    intro h
    apply ht1
    calc e.t = e.t * z * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel z
  obtain ⟨g, hgN, hg⟩ := E9.invClass (e.t * z) htzN htz2 htzz
  have hconj := card_inf_centralizer_conj (Y := oc X) (le_normalizer_oc X (hNA hgN)) e.t
  rw [hg] at hconj
  rw [hQR, Q_inf_cent_z f E9 hWc hz hW5 l, hconj, Nat.card_zpowers, e.s₂_ord, E9.E_card] at hBW
  have h9 : Nat.card (oc X) * 9 = 9 * (3 * (Nat.card (oc X ⊓ centralizer ({e.t} : Set G) : Subgroup G) *
      Nat.card (oc X ⊓ centralizer ({e.t} : Set G) : Subgroup G))) := by
    nlinarith [hBW]
  omega

theorem card_A_sup_V (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) :
    Nat.card (Asub E9 hWc ⊔ Vsub z e.s₁ hWc : Subgroup G) = 3 ^ 7 := by
  have h := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer
    (V_le_normalizer_A f E9 hWc hz hW5)
  rw [A_inf_V f E9 hWc, A_card f E9 hWc hz hW5, V_card hz f hWc hW5, Z_card f E9 hWc hz hW5] at h
  have h2 : Nat.card (Asub E9 hWc ⊔ Vsub z e.s₁ hWc : Subgroup G) * 9 = 3 ^ 7 * 9 := by
    rw [h]; norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

theorem S3_ne_seven (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (l : Lem232 z e) {S₃ : Subgroup G} (hS3p : IsPGroup 3 S₃)
    (hAV : Asub E9 hWc ⊔ Vsub z e.s₁ hWc ≤ S₃)
    (hSX : ∀ x ∈ normalizer ((Asub E9 hWc : Subgroup G) : Set G), ∀ s ∈ S₃, x * s * x⁻¹ ∈ S₃)
    (hcard : Nat.card S₃ = 3 ^ 7) : False := by
  have hNA := NHE_le_normalizer_A f E9 hWc hz hW5 l
  have hSeq : Asub E9 hWc ⊔ Vsub z e.s₁ hWc = S₃ :=
    Subgroup.eq_of_le_of_card_ge hAV (by rw [hcard, card_A_sup_V f E9 hWc hz hW5])
  have hS1 : S₃ ≤ centralizer ({e.s₁} : Set G) := by
    rw [← hSeq]
    refine sup_le (fun x hx => ?_) (fun v hv => ?_)
    · exact mem_centralizer_singleton_iff.mpr
        (A_comm f E9 hWc x hx e.s₁ (mem_sup_left E9.s₁_mem))
    · exact mem_centralizer_singleton_iff.mpr (zpowers_comm_V hWc e.s₁ (mem_zpowers e.s₁) v hv).symm
  let P : Subgroup G :=
    { carrier := {x | x ∈ E9.E ∧ ∀ s ∈ S₃, x * s = s * x}
      one_mem' := ⟨E9.E.one_mem, fun s _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
        refine ⟨E9.E.mul_mem ha hb, fun s hs => ?_⟩
        calc a * b * s = a * (b * s) := by group
          _ = a * (s * b) := by rw [hbc s hs]
          _ = (a * s) * b := by group
          _ = (s * a) * b := by rw [hac s hs]
          _ = s * (a * b) := by group
      inv_mem' := by
        rintro a ⟨ha, hac⟩
        exact ⟨E9.E.inv_mem ha, fun s hs => (Commute.inv_left (show Commute a s from hac s hs)).eq⟩ }
  have hPE : P = E9.E := by
    refine E9.irred P (fun x hx => hx.1) ⟨E9.s₁_mem, fun s hs => ?_⟩ ?_
    · exact (mem_centralizer_singleton_iff.mp (hS1 hs)).symm
    · rintro g hg p ⟨hpE, hpc⟩
      have hgN : g ∈ normalizer (E9.E : Set G) := (mem_inf.mp hg).1
      refine ⟨(mem_normalizer_iff.mp hgN p).mp hpE, fun s hs => ?_⟩
      have hs' : g⁻¹ * s * g ∈ S₃ := by
        have := hSX g⁻¹ (inv_mem (hNA hg)) s hs
        simpa using this
      have h1 := hpc _ hs'
      calc g * p * g⁻¹ * s = g * (p * (g⁻¹ * s * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * s * g) * p) * g⁻¹ := by rw [h1]
        _ = s * (g * p * g⁻¹) := by group
  have hS3A : S₃ ≤ Asub E9 hWc := by
    intro s hs
    obtain ⟨a, ha, h⟩ := cent_E_le f E9 hWc hz hW5 l (g := s) (fun x hx => by
      have : x ∈ P := by rw [hPE]; exact hx
      exact (this.2 s hs).symm)
    rcases h with h | h
    · rw [h]; exact ha
    · exfalso
      have hodd : Odd (orderOf s) := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hS3p ⟨s, hs⟩
        rw [Subgroup.orderOf_mk] at hk
        rw [hk]; exact Odd.pow (by decide)
      rw [h] at hodd
      exact not_odd_orderOf_mul_z f E9 hWc hz hW5 ha hodd
  have hle := Subgroup.card_le_of_le hS3A
  rw [hcard, A_card f E9 hWc hz hW5] at hle
  norm_num at hle

include hWc in
theorem three_pow_nine_dvd (hz : orderOf z = 2)
    (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) (l : Lem232 z e)
    (hm : MPart9 z e E9.E) : 3 ^ 9 ∣ Nat.card G := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set X : Subgroup G := normalizer ((Asub E9 hWc : Subgroup G) : Set G) with hX
  set Q := oc X with hQ
  have hNA := NHE_le_normalizer_A f E9 hWc hz hW5 l
  have hAX : Asub E9 hWc ≤ X := le_normalizer
  have hAodd : Odd (Nat.card (Asub E9 hWc)) := by rw [A_card f E9 hWc hz hW5]; decide
  have hAQ : Asub E9 hWc ≤ Q :=
    le_oc_of_normal_odd hAX (fun g hg a ha => (mem_normalizer_iff.mp hg a).mp ha) hAodd
  have hQodd : Odd (Nat.card Q) := odd_card_oc X
  have hAn : ∀ q ∈ Q, ∀ a ∈ Asub E9 hWc, q * a * q⁻¹ ∈ Asub E9 hWc :=
    fun q hq a ha => (mem_normalizer_iff.mp (oc_le X hq) a).mp ha
  have hQz := Q_inf_cent_z f E9 hWc hz hW5 l
  have hzX : z ∈ X := hNA (z_mem_NHE f E9)
  have hzQ : z ∈ normalizer (Q : Set G) := le_normalizer_oc X hzX
  have hCQ : Q ⊓ centralizer ({z} : Set G) ≤ Asub E9 hWc := by rw [hQz]; exact le_sup_left
  have hcomm : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' * q⁻¹ * q'⁻¹ ∈ Asub E9 hWc :=
    fun q hq q' hq' => comm_mem_gen hQodd hz hzQ hAn hCQ hq hq'
  have hA3 : IsPGroup 3 (Asub E9 hWc) := IsPGroup.of_card (n := 5) (A_card f E9 hWc hz hW5)
  obtain ⟨S₃, hAS, hSQ, hS3p, hSidx, hScard⟩ := exists_sylow_sub_ge (p := 3) (W := Q) (P := Asub E9 hWc)
    hAQ hA3
  have hSnorm : ∀ g ∈ Q, ∀ s ∈ S₃, g * s * g⁻¹ ∈ S₃ := by
    intro g hg s hs
    have : g * s * g⁻¹ = (g * s * g⁻¹ * s⁻¹) * s := by group
    rw [this]
    exact S₃.mul_mem (hAS (hcomm g hg s (hSQ hs))) hs
  have hall : ∀ R : Subgroup G, R ≤ Q → IsPGroup 3 R → R ≤ S₃ := by
    intro R hRQ hRp y hy
    obtain ⟨w, hwQ, hw⟩ := CFSG.GH74.GLS.Bg.Thompson.exists_conj_into_sylow (p := 3) hRQ hRp hSQ hS3p hSidx
    have h1 := hw y hy
    have h2 := hSnorm w hwQ _ h1
    have : w * (w⁻¹ * y * w) * w⁻¹ = y := by group
    rwa [this] at h2
  have hSX : ∀ x ∈ X, ∀ s ∈ S₃, x * s * x⁻¹ ∈ S₃ := by
    intro x hx s hs
    have hle : S₃.map (MulAut.conj x).toMonoidHom ≤ S₃ := by
      refine hall _ ?_ (hS3p.map _)
      rintro _ ⟨y, hy, rfl⟩
      exact conj_mem_oc hx (hSQ hy)
    exact hle ⟨s, hs, by simp⟩
  have hV3 : IsPGroup 3 (Vsub z e.s₁ hWc) := IsPGroup.of_card (n := 4) (V_card hz f hWc hW5)
  have hVS : Vsub z e.s₁ hWc ≤ S₃ := hall _ (V_le_oc_X f E9 hWc hz hW5 l hm) hV3
  have hAV : Asub E9 hWc ⊔ Vsub z e.s₁ hWc ≤ S₃ := sup_le hAS hVS
  set m := (Nat.card Q).factorization 3 with hmdef
  have h7 : 7 ≤ m := by
    have h1 := Subgroup.card_le_of_le hAV
    rw [card_A_sup_V f E9 hWc hz hW5, hScard] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hQc := card_Q f E9 hWc hz hW5 l hm
  have hmodd : m % 2 = 1 := by
    set c := Nat.card (Q ⊓ centralizer ({e.t} : Set G) : Subgroup G) with hc
    have hc0 : c ≠ 0 := Nat.card_pos.ne'
    have h1 : (Nat.card Q).factorization 3 = 1 + 2 * c.factorization 3 := by
      rw [hQc, Nat.factorization_mul (by norm_num) (mul_ne_zero hc0 hc0),
        Nat.factorization_mul hc0 hc0]
      simp [Nat.Prime.factorization_self Nat.prime_three]
      ring
    rw [hmdef, h1]
    omega
  have hm9 : 9 ≤ m := by
    by_contra hlt
    have hm7 : m = 7 := by omega
    exact S3_ne_seven f E9 hWc hz hW5 l hS3p hAV hSX (by rw [hScard, hm7])
  calc 3 ^ 9 ∣ 3 ^ m := pow_dvd_pow 3 hm9
    _ = Nat.card S₃ := hScard.symm
    _ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S₃

end Main

end CFSG.GH74.Uniqueness.SU.SU13
