module

public import CFSG.GH74.Generic.BProg.B3.S3Theta52
public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup
open scoped commutatorElement

namespace S3Sec29H

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_fixed_mem_coset {P N : Subgroup G} {g : G} (hP : IsPGroup 2 ↥P)
    (hN : Odd (Nat.card ↥N)) (hPN : P ≤ normalizer (N : Set G))
    (hg : ∀ p ∈ P, g⁻¹ * (p * g * p⁻¹) ∈ N) :
    ∃ w : G, g⁻¹ * w ∈ N ∧ ∀ p ∈ P, p * w = w * p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htop : P ≤ normalizer ((⊤ : Subgroup G) : Set G) := fun p _ =>
    Subgroup.mem_normalizer_iff.2 fun h => by simp
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction P ⊤ htop
  let fibre : SubMulAction ↥P ↥(⊤ : Subgroup G) :=
    ⟨{w | g⁻¹ * (w : G) ∈ N}, by
      intro p w hw
      change g⁻¹ * ((p : G) * (w : G) * (p : G)⁻¹) ∈ N
      have e1 : g⁻¹ * ((p : G) * (w : G) * (p : G)⁻¹) =
          (g⁻¹ * ((p : G) * g * (p : G)⁻¹)) * ((p : G) * (g⁻¹ * (w : G)) * (p : G)⁻¹) := by
        group
      rw [e1]
      exact N.mul_mem (hg p p.2) ((Subgroup.mem_normalizer_iff.1 (hPN p.2) _).1 hw)⟩
  have hcard : Nat.card fibre = Nat.card ↥N := by
    refine Nat.card_congr
      { toFun := fun w => ⟨g⁻¹ * ((w : ↥(⊤ : Subgroup G)) : G), w.2⟩
        invFun := fun n => ⟨⟨g * (n : G), Subgroup.mem_top _⟩, by
          show g⁻¹ * (g * (n : G)) ∈ N
          rw [← mul_assoc, inv_mul_cancel, one_mul]
          exact n.2⟩
        left_inv := fun w => by
          apply Subtype.ext
          apply Subtype.ext
          show g * (g⁻¹ * ((w : ↥(⊤ : Subgroup G)) : G)) = _
          group
        right_inv := fun n => by
          apply Subtype.ext
          show g⁻¹ * (g * (n : G)) = n
          group }
  have hndvd : ¬ 2 ∣ Nat.card fibre := by
    rw [hcard]
    exact fun h => (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h)
  obtain ⟨w, hw⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card fibre hndvd
  refine ⟨((w : ↥(⊤ : Subgroup G)) : G), w.2, fun p hp => ?_⟩
  have h1 := congrArg (fun z : fibre => ((z : ↥(⊤ : Subgroup G)) : G))
    (hw (⟨p, hp⟩ : ↥P))
  change p * ((w : ↥(⊤ : Subgroup G)) : G) * p⁻¹ = ((w : ↥(⊤ : Subgroup G)) : G) at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

omit [Finite G] in
theorem mul_self_mem_of_coset {N : Subgroup G} {g w : G} (hgN : g ∈ normalizer (N : Set G))
    (hg2 : g * g ∈ N) (hw : g⁻¹ * w ∈ N) : w * w ∈ N := by
  have e1 : w * w = (g * (g⁻¹ * w) * g⁻¹) * (g * g) * (g⁻¹ * w) := by group
  rw [e1]
  exact N.mul_mem (N.mul_mem ((Subgroup.mem_normalizer_iff.1 hgN _).1 hw) hg2) hw

omit [Finite G] in
theorem eq_one_of_mem_of_pow_two {N : Subgroup G} (hN : Odd (Nat.card ↥N)) {n : G} (hn : n ∈ N)
    {a : ℕ} (ha : n ^ (2 ^ a) = 1) : n = 1 := by
  have h1 : orderOf n ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf n ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N hn
  have hcop : Nat.Coprime (2 ^ a) (Nat.card ↥N) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hN)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem exists_inv_fixed_mem_coset {P N : Subgroup G} {g : G} (hP : IsPGroup 2 ↥P)
    (hN : Odd (Nat.card ↥N)) (hPN : P ≤ normalizer (N : Set G))
    (hgN : g ∈ normalizer (N : Set G)) (hg2 : g * g ∈ N)
    (hg : ∀ p ∈ P, g⁻¹ * (p * g * p⁻¹) ∈ N) :
    ∃ w : G, g⁻¹ * w ∈ N ∧ w * w = 1 ∧ ∀ p ∈ P, p * w = w * p := by
  obtain ⟨w₀, hw₀N, hw₀P⟩ := exists_fixed_mem_coset hP hN hPN hg
  obtain ⟨a, m, hm, hr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w₀).ne'
  obtain ⟨k, rfl⟩ := hm
  have hww : w₀ * w₀ ∈ N := mul_self_mem_of_coset hgN hg2 hw₀N
  set w := w₀ ^ (2 * k + 1) with hwdef
  have hwN : g⁻¹ * w ∈ N := by
    have e1 : w = w₀ * (w₀ * w₀) ^ k := by
      rw [hwdef, pow_succ', pow_mul, sq]
    rw [e1, ← mul_assoc]
    exact N.mul_mem hw₀N (N.pow_mem hww k)
  have hw2 : w * w ∈ N := mul_self_mem_of_coset hgN hg2 hwN
  have hwpow : (w * w) ^ (2 ^ a) = 1 := by
    rw [← sq, ← pow_mul, hwdef, ← pow_mul]
    have e3 : (2 * k + 1) * (2 * 2 ^ a) = orderOf w₀ * 2 := by rw [hr]; ring
    rw [e3, pow_mul, pow_orderOf_eq_one, one_pow]
  refine ⟨w, hwN, eq_one_of_mem_of_pow_two hN hw2 hwpow, fun p hp => ?_⟩
  exact (Commute.pow_right (show Commute p w₀ from hw₀P p hp) _).eq

omit [Finite G] in
theorem exists_a7Act_conj {J : Subgroup G} (e e' : kBar J ≃* alternatingGroup (Fin 7)) :
    ∃ τ : Equiv.Perm (Fin 7), ∀ m : ↥(normalizer (J : Set G)),
      GLS.Th2.Obs.a7Act J e' m = τ * GLS.Th2.Obs.a7Act J e m * τ⁻¹ := by
  obtain ⟨τ, hτ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 (e.symm.trans e')
  have he' : ∀ k : kBar J, ((e' k : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      τ * (e k : Equiv.Perm (Fin 7)) * τ⁻¹ := by
    intro k
    have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin 7)) =>
      ((φ (e k) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) hτ
    simp only [MulAut.conjNormal_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    exact h1.symm
  refine ⟨τ, fun m => ?_⟩
  show (GLS.Th2.Bal.a7Theta e').symm (GLS.Th2.Obs.barAct J m) =
    τ * (GLS.Th2.Bal.a7Theta e).symm (GLS.Th2.Obs.barAct J m) * τ⁻¹
  rw [MulEquiv.symm_apply_eq]
  ext k
  apply e'.injective
  apply Subtype.ext
  rw [GLS.Th2.Bal.a7Theta_apply, he', he']
  have h2 := GLS.Th2.Bal.a7Theta_apply e ((GLS.Th2.Bal.a7Theta e).symm (GLS.Th2.Obs.barAct J m)) k
  rw [MulEquiv.apply_symm_apply] at h2
  rw [h2]
  group

omit [Finite G] in
theorem isElementaryAbelian_zpowers {v : G} (hv : v * v = 1) :
    CFSG.IsElementaryAbelian 2 ↥(zpowers v) := by
  refine C3.Layer1.Back.isElementaryAbelian_of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self v i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_add, ← two_mul, zpow_mul]
    have : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
    rw [this, one_zpow]

omit [Finite G] in
theorem mem_sup_zpowers {H : Subgroup G} {v : G} (hv : v * v = 1)
    (hc : ∀ h ∈ H, h * v = v * h) {g : G} (hg : g ∈ H ⊔ zpowers v) :
    ∃ h ∈ H, g = h ∨ g = h * v := by
  have hc' : ∀ h ∈ H, ∀ k ∈ zpowers v, h * k = k * h := by
    intro h hh k hk
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (show Commute h v from hc h hh) i).eq
  obtain ⟨h, hh, k, hk, rfl⟩ := S3Theta52.exists_mul_of_mem_sup hc' hg
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hv2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' i
  · refine ⟨h, hh, Or.inl ?_⟩
    rw [hj, zpow_mul, hv2, one_zpow, mul_one]
  · refine ⟨h, hh, Or.inr ?_⟩
    rw [hj, zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

omit [Finite G] in
theorem isElementaryAbelian_sup_zpowers {H : Subgroup G} (hH : CFSG.IsElementaryAbelian 2 ↥H)
    {v : G} (hv : v * v = 1) (hc : ∀ h ∈ H, h * v = v * h) :
    CFSG.IsElementaryAbelian 2 ↥(H ⊔ zpowers v) := by
  refine S3Theta52.isElementaryAbelian_sup hH (isElementaryAbelian_zpowers hv) ?_
  intro h hh k hk
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  exact (Commute.zpow_right (show Commute h v from hc h hh) i).eq

omit [Finite G] in
theorem card_sup_zpowers {H : Subgroup G} {v : G} (hv : v * v = 1) (hvH : v ∉ H)
    (hc : ∀ h ∈ H, h * v = v * h) :
    Nat.card ↥(H ⊔ zpowers v) = 2 * Nat.card ↥H := by
  have hv1 : v ≠ 1 := fun h => hvH (h ▸ H.one_mem)
  have hord : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv) hv1
  have hc' : ∀ h ∈ H, ∀ k ∈ zpowers v, h * k = k * h := by
    intro h hh k hk
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (show Commute h v from hc h hh) i).eq
  have hinf : H ⊓ zpowers v = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgH, hgv⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgv
    have hv2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' i
    · rw [zpow_mul, hv2, one_zpow]
      exact Subgroup.one_mem _
    · rw [zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one] at hgH
      exact absurd hgH hvH
  rw [S3Theta52.card_sup_of_commute hc' hinf, Nat.card_zpowers, hord, mul_comm]

theorem card_inf_le_two_mul {H H' X : Subgroup G} (hle : H' ≤ H)
    (h2 : 2 * Nat.card ↥H' = Nat.card ↥H) :
    Nat.card ↥(H ⊓ X) ≤ 2 * Nat.card ↥(H' ⊓ X) := by
  classical
  set T : Subgroup ↥H := H'.subgroupOf H with hTdef
  have hT : T.index = 2 := by
    have h1 := Subgroup.card_mul_index T
    have h2' : Nat.card ↥T = Nat.card ↥H' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [h2'] at h1
    have hpos : 0 < Nat.card ↥H' := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, ← h2, mul_comm])
  by_cases hX : H ⊓ X ≤ H'
  · have h3 := Subgroup.card_le_of_le (le_inf hX inf_le_right : H ⊓ X ≤ H' ⊓ X)
    omega
  · obtain ⟨a, ha, haH'⟩ := IsConcreteLE.not_le_iff_exists.1 hX
    refine S3Theta52.card_le_two_mul_of_cover (a' := a⁻¹) (inv_mem ha) (inf_le_inf_right X hle) ?_
    intro b hb
    by_cases hbH' : b ∈ H'
    · exact Or.inl ⟨hbH', (Subgroup.mem_inf.1 hb).2⟩
    · right
      obtain ⟨haH, haX⟩ := Subgroup.mem_inf.1 ha
      obtain ⟨hbH, hbX⟩ := Subgroup.mem_inf.1 hb
      refine Subgroup.mem_inf.2 ⟨?_, X.mul_mem (X.inv_mem haX) hbX⟩
      have key := (Subgroup.mul_mem_iff_of_index_two hT (a := (⟨a⁻¹, H.inv_mem haH⟩ : ↥H))
        (b := ⟨b, hbH⟩)).2 ⟨fun h => absurd (by simpa using H'.inv_mem (Subgroup.mem_subgroupOf.1 h))
          haH', fun h => absurd (Subgroup.mem_subgroupOf.1 h) hbH'⟩
      exact Subgroup.mem_subgroupOf.1 key

omit [Finite G] in
theorem le_pPrimeCoreOf_of_odd {A X : Subgroup G} (hAX : A ≤ X)
    (hnorm : X ≤ normalizer (A : Set G)) (hodd : Odd (Nat.card ↥A)) : A ≤ pPrimeCoreOf 2 X := by
  have hnormal : (A.subgroupOf X).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm h.2) a).mp ha
  have hcop' : Nat.Coprime 2 (Nat.card (A.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : A.subgroupOf X ≤ pPrimeCore 2 X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hAX]
  exact Subgroup.map_mono hle

end S3Sec29H

end CFSG.GH74.Generic.BProg.B3
