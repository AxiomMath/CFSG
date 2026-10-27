module

public import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups
public import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.GroupTheory

open Subgroup

variable {H : Type} [Group H] [Finite H]

theorem commutator_eq_bot_of_center_not_le {A S Q : Subgroup H} (hAodd : Odd (Nat.card A))
    (hS2 : IsPGroup 2 S) (hQleS : Q ≤ S) (hQrel : Q.relIndex S = 2)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set H)) {s : H} (hsS : s ∈ S) (hsQ : s ∉ Q)
    (hsN : s ∈ Subgroup.normalizer (A : Set H))
    (hBinv : ∀ x ∈ ⁅A, Subgroup.zpowers s⁆, s * x * s⁻¹ = x⁻¹)
    (hZS : ¬ (Subgroup.center ↥S).map S.subtype ≤ Q) :
    ⁅Q, ⁅A, Subgroup.zpowers s⁆⁆ = ⊥ := by
  classical
  let B : Subgroup H := ⁅A, Subgroup.zpowers s⁆
  let C : Subgroup H := Subgroup.centralizer (Q : Set H)
  have hBA : B ≤ A := by
    rw [show B = ⁅A, Subgroup.zpowers s⁆ from rfl]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hsN)
  have hQn : (Q.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hQrel
  have hsNQ : s ∈ Subgroup.normalizer (Q : Set H) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (hK := hQn) hQleS hsS
  obtain ⟨z, hzZS, hzQ⟩ := SetLike.not_le_iff_exists.mp hZS
  obtain ⟨zc, hzc, hz_eq⟩ := Subgroup.mem_map.mp hzZS
  have hzS : z ∈ S := by
    rw [← hz_eq]
    exact zc.2
  have hq0Q : s⁻¹ * z ∈ Q := by
    have hmem : (⟨s, hsS⟩ : S)⁻¹ * ⟨z, hzS⟩ ∈ Q.subgroupOf S := by
      exact (Subgroup.mul_mem_iff_of_index_two (H := Q.subgroupOf S) hQrel).mpr
        (iff_of_false
          (fun h => hsQ (by simpa using Q.inv_mem (Subgroup.mem_subgroupOf.mp h)))
          (fun h => hzQ (Subgroup.mem_subgroupOf.mp h)))
    exact Subgroup.mem_subgroupOf.mp hmem
  set q0 : H := s⁻¹ * z with hq0
  have hz_decomp : z = s * q0 := by
    rw [hq0]
    group
  have key : ∀ a ∈ B, ∃ q2 : H, q2 ∈ Q ∧ z * a * z⁻¹ * a⁻¹ = q2 * (a ^ 2)⁻¹ := by
    intro a ha
    have haA : a ∈ A := hBA ha
    have haNQ : a ∈ Subgroup.normalizer (Q : Set H) := hAQ haA
    have hq1Q : a * q0 * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp haNQ q0).mp hq0Q
    have hq2Q : s * (q0 * (a * q0 * a⁻¹)⁻¹) * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hsNQ (q0 * (a * q0 * a⁻¹)⁻¹)).mp
        (Q.mul_mem hq0Q (Q.inv_mem hq1Q))
    refine ⟨s * (q0 * (a * q0 * a⁻¹)⁻¹) * s⁻¹, hq2Q, ?_⟩
    have hsa : s * a * s⁻¹ = a⁻¹ := hBinv a ha
    have hsa2 : s * a ^ 2 * s⁻¹ = (a ^ 2)⁻¹ := by
      have hconj : (MulAut.conj s) a = a⁻¹ := by simpa [MulAut.conj_apply] using hsa
      have h1 : s * a ^ 2 * s⁻¹ = ((MulAut.conj s) a) ^ 2 := by
        rw [show s * a ^ 2 * s⁻¹ = (MulAut.conj s) (a ^ 2) from rfl, map_pow]
      rw [h1, hconj]
      group
    have hs_inv : s⁻¹ * a⁻¹ = a * s⁻¹ := by
      have h := congrArg (fun y => s⁻¹ * y) hsa
      simpa [mul_assoc] using h.symm
    have hq0comm : q0 * a * q0⁻¹ * a = q0 * (a * q0 * a⁻¹)⁻¹ * a ^ 2 := by group
    calc z * a * z⁻¹ * a⁻¹
        = s * (q0 * a * q0⁻¹ * (s⁻¹ * a⁻¹)) := by
          rw [hz_decomp]
          group
      _ = s * (q0 * a * q0⁻¹ * (a * s⁻¹)) := by rw [hs_inv]
      _ = s * (q0 * a * q0⁻¹ * a) * s⁻¹ := by group
      _ = s * (q0 * (a * q0 * a⁻¹)⁻¹ * a ^ 2) * s⁻¹ := by rw [hq0comm]
      _ = (s * (q0 * (a * q0 * a⁻¹)⁻¹) * s⁻¹) * (s * a ^ 2 * s⁻¹) := by group
      _ = (s * (q0 * (a * q0 * a⁻¹)⁻¹) * s⁻¹) * (a ^ 2)⁻¹ := by rw [hsa2]
  have hz_center : z ∈ C := by
    rw [show C = Subgroup.centralizer (Q : Set H) from rfl, Subgroup.mem_centralizer_iff]
    intro q hq
    have h := Subgroup.mem_center_iff.mp hzc (⟨q, hQleS hq⟩ : S)
    rw [← hz_eq]
    exact congrArg Subtype.val h
  have hEcent : ∀ a ∈ B, z * a * z⁻¹ * a⁻¹ ∈ C := by
    intro a ha
    have haA : a ∈ A := hBA ha
    have haNQ : a ∈ Subgroup.normalizer (Q : Set H) := hAQ haA
    have haz : a * z⁻¹ * a⁻¹ ∈ C := by
      rw [show C = Subgroup.centralizer (Q : Set H) from rfl, Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : a⁻¹ * q * a ∈ Q := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q : Set H)).inv_mem haNQ) q).mp hq
      have hcomm := Subgroup.mem_centralizer_iff.mp (C.inv_mem hz_center) (a⁻¹ * q * a) hq'
      calc q * (a * z⁻¹ * a⁻¹) = a * ((a⁻¹ * q * a) * z⁻¹) * a⁻¹ := by group
        _ = a * (z⁻¹ * (a⁻¹ * q * a)) * a⁻¹ := by rw [hcomm]
        _ = (a * z⁻¹ * a⁻¹) * q := by group
    have hprod := C.mul_mem hz_center haz
    simpa [mul_assoc] using hprod
  have ha2_cent : ∀ a ∈ B, a ^ 2 ∈ C := by
    intro a ha
    obtain ⟨q2, hq2Q, hmain⟩ := key a ha
    have hE := hEcent a ha
    have hw : a ^ 2 * q2⁻¹ ∈ C := by
      have h1 : a ^ 2 * q2⁻¹ = (z * a * z⁻¹ * a⁻¹)⁻¹ := by
        rw [hmain]
        group
      rw [h1]
      exact C.inv_mem hE
    have hcomm_wt : Commute (a ^ 2 * q2⁻¹) q2 := by
      have h := Subgroup.mem_centralizer_iff.mp hw q2 hq2Q
      exact h.symm
    have hq2S : q2 ∈ S := hQleS hq2Q
    obtain ⟨k, hk⟩ := hS2.exists_orderOf_eq_pow (⟨q2, hq2S⟩ : S)
    have hq2ord : orderOf q2 = 2 ^ k := by simpa using hk
    set m : ℕ := orderOf (a ^ 2) with hm
    have hm_odd : Odd m :=
      Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A (A.pow_mem (hBA ha) 2))
    have hcop : Nat.Coprime m (2 ^ k) := (Nat.coprime_two_right.mpr hm_odd).pow_right k
    have hrt : a ^ 2 = (a ^ 2 * q2⁻¹) * q2 := by group
    have h1 : (a ^ 2 * q2⁻¹) ^ m * q2 ^ m = 1 := by
      rw [← hcomm_wt.mul_pow, ← hrt]
      exact pow_orderOf_eq_one (a ^ 2)
    have htmpow : q2 ^ m ∈ C := by
      have h2 : q2 ^ m = ((a ^ 2 * q2⁻¹) ^ m)⁻¹ :=
        eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact C.inv_mem (C.pow_mem hw m)
    have hq2cent : q2 ∈ C := by
      have hcopq2 : Nat.Coprime m (orderOf q2) := by
        rw [hq2ord]
        exact hcop
      obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime (x := q2) (n := m) hcopq2
      rw [← hu]
      exact C.pow_mem htmpow u
    have hrt_eq : a ^ 2 = (a ^ 2 * q2⁻¹) * q2 := by group
    exact hrt_eq ▸ C.mul_mem hw hq2cent
  have hBcent : B ≤ C := by
    intro a ha
    have haodd : Odd (orderOf a) :=
      Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A (hBA ha))
    have hcop : Nat.Coprime 2 (orderOf a) := Nat.coprime_two_left.mpr haodd
    obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime (x := a) (n := 2) hcop
    rw [← hu]
    exact C.pow_mem (ha2_cent a ha) u
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (Subgroup.le_centralizer_iff.mpr hBcent)

theorem le_normalizer_center_of_le {A S Q : Subgroup H} (hAodd : Odd (Nat.card A))
    (hS2 : IsPGroup 2 S) (hQleS : Q ≤ S) (hQrel : Q.relIndex S = 2)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set H)) {s : H} (hsS : s ∈ S) (hsQ : s ∉ Q)
    (hsN : s ∈ Subgroup.normalizer (A : Set H)) (hAab : IsMulCommutative ↥A)
    (hZQ : ⁅(Subgroup.center ↥Q).map Q.subtype, ⁅A, Subgroup.zpowers s⁆⁆ = ⊥)
    (hZSle : (Subgroup.center ↥S).map S.subtype ≤ Q) :
    A ≤ Subgroup.normalizer ((Subgroup.center ↥S).map S.subtype : Set H) := by
  classical
  let B : Subgroup H := ⁅A, Subgroup.zpowers s⁆
  let C : Subgroup H := A ⊓ Subgroup.centralizer (Subgroup.zpowers s : Set H)
  let ZS : Subgroup H := (Subgroup.center ↥S).map S.subtype
  let ZQ : Subgroup H := (Subgroup.center ↥Q).map Q.subtype
  change A ≤ Subgroup.normalizer (ZS : Set H)
  have hBA : B ≤ A := by
    rw [show B = ⁅A, Subgroup.zpowers s⁆ from rfl]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hsN)
  have hQn : (Q.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hQrel
  have hsNQ : s ∈ Subgroup.normalizer (Q : Set H) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (hK := hQn) hQleS hsS
  have hZSleZQ : ZS ≤ ZQ := by
    intro z hz
    obtain ⟨zc, hzc, rfl⟩ := Subgroup.mem_map.mp hz
    have hzQ : ((zc : ↥S) : H) ∈ Q := hZSle (Subgroup.mem_map_of_mem S.subtype hzc)
    refine Subgroup.mem_map.mpr ⟨⟨(zc : H), hzQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    have h := Subgroup.mem_center_iff.mp hzc (⟨(q : H), hQleS q.2⟩ : S)
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  have hSgen : S = Q ⊔ Subgroup.zpowers s := by
    have hle : Q ⊔ Subgroup.zpowers s ≤ S :=
      sup_le hQleS (Subgroup.zpowers_le.mpr hsS)
    have hmul := Subgroup.relIndex_mul_relIndex (H := Q)
      (K := Q ⊔ Subgroup.zpowers s) (L := S) le_sup_left hle
    rw [hQrel] at hmul
    have hnot : Q.relIndex (Q ⊔ Subgroup.zpowers s) ≠ 1 := by
      intro h1
      have hQle : Q ⊔ Subgroup.zpowers s ≤ Q := Subgroup.relIndex_eq_one.mp h1
      exact hsQ (hQle (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)))
    have hdvd : Q.relIndex (Q ⊔ Subgroup.zpowers s) ∣ 2 := by
      rw [← hmul]
      exact dvd_mul_right _ _
    have hleft : Q.relIndex (Q ⊔ Subgroup.zpowers s) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hnot
      · exact h
    have hright : (Q ⊔ Subgroup.zpowers s).relIndex S = 1 := by
      rw [hleft] at hmul
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by simpa using hmul)
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hright) hle
  have hdecomp : ∀ t : H, t ∈ S → ∃ q ∈ Q, ∃ y ∈ Subgroup.zpowers s, t = q * y := by
    intro t ht
    have hSN : Subgroup.zpowers s ≤ Subgroup.normalizer (Q : Set H) :=
      Subgroup.zpowers_le.mpr hsNQ
    have ht' : t ∈ Q ⊔ Subgroup.zpowers s := by
      rw [← hSgen]
      exact ht
    exact (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := Q)
      (K := Subgroup.zpowers s) hSN).mp ht'
  have hmemZS : ∀ z : H, z ∈ ZS ↔ z ∈ ZQ ∧ s * z * s⁻¹ = z := by
    intro z
    constructor
    · intro hz
      refine ⟨hZSleZQ hz, ?_⟩
      obtain ⟨zc, hzc, rfl⟩ := Subgroup.mem_map.mp hz
      have h := Subgroup.mem_center_iff.mp hzc (⟨s, hsS⟩ : S)
      have hcoe : s * (zc : H) = (zc : H) * s := congrArg Subtype.val h
      calc s * (zc : H) * s⁻¹ = ((zc : H) * s) * s⁻¹ := by rw [hcoe]
        _ = zc := by group
    · rintro ⟨hzZQ, hzfix⟩
      obtain ⟨zc, hzc, rfl⟩ := Subgroup.mem_map.mp hzZQ
      have hzcQ : (zc : H) ∈ Q := zc.2
      have hzcS : (zc : H) ∈ S := hQleS hzcQ
      have hzfix' : s * (zc : H) * s⁻¹ = (zc : H) := by simpa using hzfix
      refine Subgroup.mem_map.mpr ⟨⟨(zc : H), hzcS⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro t
      obtain ⟨q, hq, y, hy, hqy⟩ := hdecomp (t : H) t.2
      have hzcs : Commute (zc : H) s := by
        rw [commute_iff_eq]
        have h : s * (zc : H) = (zc : H) * s := by
          calc s * (zc : H) = (s * (zc : H) * s⁻¹) * s := by group
            _ = (zc : H) * s := by rw [hzfix']
        exact h.symm
      have hyzc : (y : H) * (zc : H) = (zc : H) * (y : H) := by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (hzcs.zpow_right j).eq.symm
      have hqzc : (q : H) * (zc : H) = (zc : H) * (q : H) := by
        have h := Subgroup.mem_center_iff.mp hzc ⟨q, hq⟩
        exact congrArg Subtype.val h
      have htzc : (t : H) * (zc : H) = (zc : H) * (t : H) := by
        rw [hqy]
        calc ((q : H) * (y : H)) * (zc : H) = (q : H) * ((y : H) * (zc : H)) := by group
          _ = (q : H) * ((zc : H) * (y : H)) := by rw [hyzc]
          _ = ((q : H) * (zc : H)) * (y : H) := by group
          _ = ((zc : H) * (q : H)) * (y : H) := by rw [hqzc]
          _ = (zc : H) * ((q : H) * (y : H)) := by group
      exact Subtype.ext htzc
  have hmapZQ : ∀ c ∈ Subgroup.normalizer (Q : Set H), ∀ z ∈ ZQ,
      c * z * c⁻¹ ∈ ZQ := by
    intro c hcN z hz
    obtain ⟨zq, hzq, rfl⟩ := Subgroup.mem_map.mp hz
    let ec : MulAut ↥Q := Subgroup.normalizerMonoidHom Q ⟨c, hcN⟩
    have hcenter : (Subgroup.center ↥Q).map (ec : ↥Q →* ↥Q) = Subgroup.center ↥Q :=
      Subgroup.map_center_eq ec
    have hmem : ec zq ∈ Subgroup.center ↥Q := by
      rw [← hcenter]
      exact Subgroup.mem_map_of_mem (ec : ↥Q →* ↥Q) hzq
    refine Subgroup.mem_map.mpr ⟨ec zq, hmem, ?_⟩
    exact Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨c, hcN⟩ zq
  have hBnorm : B ≤ Subgroup.normalizer (ZS : Set H) := by
    have hZQB : ZQ ≤ Subgroup.centralizer (B : Set H) := by
      simpa [ZQ, B] using Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZQ
    have hBZQ : B ≤ Subgroup.centralizer (ZQ : Set H) :=
      Subgroup.le_centralizer_iff.mp hZQB
    have hBZS : B ≤ Subgroup.centralizer (ZS : Set H) :=
      hBZQ.trans (Subgroup.centralizer_le hZSleZQ)
    exact hBZS.trans (Subgroup.centralizer_le_normalizer (ZS : Set H))
  have hCnorm : C ≤ Subgroup.normalizer (ZS : Set H) := by
    have hforward : ∀ c ∈ C, ∀ z ∈ ZS, c * z * c⁻¹ ∈ ZS := by
      intro c hc z hz
      have hz' := (hmemZS z).mp hz
      have hcNQ : c ∈ Subgroup.normalizer (Q : Set H) := hAQ hc.1
      have hcs : s * c = c * s :=
        Subgroup.mem_centralizer_iff.mp hc.2 s (Subgroup.mem_zpowers s)
      have hci : c⁻¹ * s⁻¹ = s⁻¹ * c⁻¹ := by
        have := congrArg Inv.inv hcs
        simpa using this
      rw [hmemZS]
      refine ⟨hmapZQ c hcNQ z hz'.1, ?_⟩
      calc s * (c * z * c⁻¹) * s⁻¹
          = (s * c) * z * (c⁻¹ * s⁻¹) := by group
        _ = (c * s) * z * (c⁻¹ * s⁻¹) := by rw [hcs]
        _ = (c * s) * z * (s⁻¹ * c⁻¹) := by rw [hci]
        _ = c * (s * z * s⁻¹) * c⁻¹ := by group
        _ = c * z * c⁻¹ := by rw [hz'.2]
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact hforward c hc z
    · intro hz
      have h := hforward c⁻¹ (C.inv_mem hc) (c * z * c⁻¹) hz
      simpa [mul_assoc] using h
  have hAleBC : A ≤ B ⊔ C := by
    have hsolv : Group.IsSolvable ↥A := by
      haveI : IsMulCommutative ↥A := hAab
      infer_instance
    obtain ⟨k, hk⟩ := hS2.exists_orderOf_eq_pow (⟨s, hsS⟩ : S)
    have hk' : orderOf s = 2 ^ k := by simpa using hk
    have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers s)) (Nat.card ↥A) := by
      rw [Nat.card_zpowers, hk']
      exact (Nat.coprime_two_left.mpr hAodd).pow_left k
    exact CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite
      (R := A) (A := Subgroup.zpowers s) (Subgroup.zpowers_le.mpr hsN) hcop hsolv
  have hBC : B ≤ Subgroup.normalizer (C : Set H) := by
    have hAcentA : A ≤ Subgroup.centralizer (A : Set H) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab
    have hAcentC : A ≤ Subgroup.centralizer (C : Set H) :=
      hAcentA.trans (Subgroup.centralizer_le (show C ≤ A from inf_le_left))
    exact (hBA.trans hAcentC).trans (Subgroup.centralizer_le_normalizer (C : Set H))
  intro a ha
  have hmem := (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := C)
    (K := B) hBC).mp (by simpa [sup_comm] using hAleBC ha)
  obtain ⟨c, hcC, b, hbB, hbc⟩ := hmem
  rw [hbc]
  exact (Subgroup.normalizer (ZS : Set H)).mul_mem (hCnorm hcC) (hBnorm hbB)

end CFSG.GroupTheory
