module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec5_klein_mem {t z x : G} (ht2 : orderOf t = 2) (hz2 : orderOf z = 2)
    (htz : t * z = z * t) (hx : x ∈ zpowers t ⊔ zpowers z) :
    x = 1 ∨ x = t ∨ x = z ∨ x = t * z := by
  have ht1 : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hz1 : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have htz' : z * t = t * z := htz.symm
  have ht_mul_tz : t * (t * z) = z := by rw [← mul_assoc, ht1, one_mul]
  have hz_mul_tz : z * (t * z) = t := by rw [← mul_assoc, htz', mul_assoc, hz1, mul_one]
  have htz_mul_t : (t * z) * t = z := by rw [mul_assoc, htz', ← mul_assoc, ht1, one_mul]
  have htz_mul_z : (t * z) * z = t := by rw [mul_assoc, hz1, mul_one]
  have htz_mul_tz : (t * z) * (t * z) = 1 := by
    rw [mul_assoc, ← mul_assoc z t z, htz', mul_assoc, hz1, mul_one, ht1]
  let W : Subgroup G :=
    { carrier := ({1, t, z, t * z} : Set G)
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp only [one_mul, mul_one, ht1, hz1, htz', ht_mul_tz, hz_mul_tz, htz_mul_t,
            htz_mul_z, htz_mul_tz, true_or, or_true]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · left; simp
        · right; left; exact inv_eq_of_mul_eq_one_right ht1
        · right; right; left; exact inv_eq_of_mul_eq_one_right hz1
        · right; right; right
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hz1, inv_eq_of_mul_eq_one_right ht1, htz'] }
  have htW : t ∈ W := by
    change t ∈ ({1, t, z, t * z} : Set G)
    simp
  have hzW : z ∈ W := by
    change z ∈ ({1, t, z, t * z} : Set G)
    simp
  have hxW : x ∈ W :=
    (sup_le (Subgroup.zpowers_le.mpr htW) (Subgroup.zpowers_le.mpr hzW)) hx
  change x ∈ ({1, t, z, t * z} : Set G) at hxW
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxW

theorem sec5_klein_sq {t z w : G} (ht2 : orderOf t = 2) (hz2 : orderOf z = 2)
    (htz : t * z = z * t) (hw : w ∈ zpowers t ⊔ zpowers z) : w * w = 1 := by
  have ht1 : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hz1 : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  rcases sec5_klein_mem ht2 hz2 htz hw with rfl | rfl | rfl | rfl
  · simp
  · exact ht1
  · exact hz1
  · rw [mul_assoc, ← mul_assoc z t z, htz.symm, mul_assoc, hz1, mul_one, ht1]

theorem sec5_klein_involutions {t z x : G} (ht2 : orderOf t = 2) (hz2 : orderOf z = 2)
    (htz : t * z = z * t) (hx : x ∈ zpowers t ⊔ zpowers z) (hx2 : orderOf x = 2) :
    x = t ∨ x = z ∨ x = t * z := by
  rcases sec5_klein_mem ht2 hz2 htz hx with h1 | h2 | h3 | h4
  · exfalso
    rw [h1, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h4)

theorem sec5_conj_mem_omega1 {S : Subgroup G} {d x : G} (hd : d ∈ normalizer (S : Set G))
    (hx : x ∈ centerIn S) (hx2 : x ^ 2 = 1) : d⁻¹ * x * d ∈ omega1 (centerIn S) := by
  obtain ⟨hxS, hxcomm⟩ := sec5_mem_centerIn_iff.mp hx
  have hx'S : d⁻¹ * x * d ∈ S :=
    (Subgroup.mem_set_normalizer_iff''.mp hd x).mp hxS
  have hx'comm : ∀ y ∈ S, (d⁻¹ * x * d) * y = y * (d⁻¹ * x * d) := by
    intro y hy
    have hyS : d * y * d⁻¹ ∈ S := (Subgroup.mem_set_normalizer_iff.mp hd y).mp hy
    have h := hxcomm (d * y * d⁻¹) hyS
    calc (d⁻¹ * x * d) * y = d⁻¹ * (x * (d * y * d⁻¹)) * d := by group
      _ = d⁻¹ * ((d * y * d⁻¹) * x) * d := by rw [h]
      _ = y * (d⁻¹ * x * d) := by group
  have hx'2 : (d⁻¹ * x * d) ^ 2 = 1 := by
    have h1 : (d⁻¹ * x * d) * (d⁻¹ * x * d) = d⁻¹ * (x * x) * d := by group
    rw [pow_two, h1, ← pow_two, hx2, mul_one, inv_mul_cancel]
  exact Subgroup.subset_closure ⟨sec5_mem_centerIn_iff.mpr ⟨hx'S, hx'comm⟩, hx'2⟩

private theorem isSylow2Of_eq_of_le [Finite G] {S H T : Subgroup G} (hS : IsSylow2Of S H)
    (hT : IsPGroup 2 T) (hST : S ≤ T) (hTH : T ≤ H) : T ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.relIndex_eq_one]
  have hmul : S.relIndex T * T.relIndex H = S.relIndex H :=
    Subgroup.relIndex_mul_relIndex S T H hST hTH
  have hodd : ¬ 2 ∣ S.relIndex T := fun h =>
    hS.2.2 (hmul ▸ dvd_mul_of_dvd_left h (T.relIndex H))
  have hdvd : S.relIndex T ∣ Nat.card T := Subgroup.relIndex_dvd_card S T
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp (hn ▸ hdvd) with ⟨k, -, hk⟩
  have hk0 : k = 0 := by
    by_contra hk0
    apply hodd
    rw [hk]
    simpa using (pow_dvd_pow 2 (Nat.pos_of_ne_zero hk0) : 2 ^ 1 ∣ 2 ^ k)
  rw [hk, hk0, pow_zero]

private theorem exists_mem_normalizer_not_mem [Finite G] {S P : Subgroup G} (hP : IsPGroup 2 P)
    (hlt : S < P) : ∃ n ∈ P, n ∉ S ∧ n ∈ normalizer (S : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKtop : S.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun hPS => (ne_of_lt hlt) (le_antisymm hlt.le hPS)
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  obtain ⟨n, hn_norm, hn_notK⟩ :=
    SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (G := ↥P) (S.subgroupOf P) hKtop)
  refine ⟨(n : G), n.2, fun hnS => hn_notK (Subgroup.mem_subgroupOf.mpr hnS), ?_⟩
  have hn' : n ∈ (Subgroup.normalizer S).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hlt.le]
    exact hn_norm
  exact Subgroup.mem_subgroupOf.mp hn'

theorem sec5_isSylow2Of_top [Finite G] {t z : G} {S : Subgroup G}
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (ht2 : orderOf t = 2) (hz2 : orderOf z = 2)
    (hΩ : omega1 (centerIn S) = zpowers t ⊔ zpowers z)
    (hnt : ∀ g : G, g⁻¹ * z * g ≠ t) (hconj : ∃ h : G, h⁻¹ * z * h = t * z) :
    IsSylow2Of S ⊤ := by
  have htS : t ∈ S := sec4_t_mem_S hS ht2
  have hω_le : omega1 (centerIn S) ≤ centerIn S :=
    (Subgroup.closure_le (centerIn S)).mpr (fun x hx => hx.1)
  have hz_center : z ∈ centerIn S :=
    hω_le (by rw [hΩ]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have ht_center : t ∈ centerIn S :=
    hω_le (by rw [hΩ]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have htz : t * z = z * t :=
    ((sec5_mem_centerIn_iff.mp hz_center).2 t htS).symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hSP⟩ := hS.2.1.exists_le_sylow
  have hSPeq : S = (P : Subgroup G) := by
    by_contra hne
    have hlt : S < (P : Subgroup G) := lt_of_le_of_ne hSP hne
    obtain ⟨n, hnP, hnS, hnN⟩ := exists_mem_normalizer_not_mem P.isPGroup' hlt
    have ht2sq : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    have ha_mem : n⁻¹ * t * n ∈ zpowers t ⊔ zpowers z := by
      have h := sec5_conj_mem_omega1 hnN ht_center ht2sq
      rwa [hΩ] at h
    have ha2 : orderOf (n⁻¹ * t * n) = 2 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj n⁻¹) t
      rw [ht2] at h
      simpa [MulAut.conj_apply, inv_inv] using h
    rcases sec5_klein_involutions ht2 hz2 htz ha_mem ha2 with ha | ha | ha
    ·
      have hcomm : t * n = n * t := by
        have h := congrArg (fun x => n * x) ha
        rw [show n * (n⁻¹ * t * n) = t * n by group] at h
        exact h
      have hnH : n ∈ centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcomm.symm
      let T : Subgroup G := S ⊔ zpowers n
      have hsup2 : IsPGroup 2 T :=
        (P.isPGroup').to_le (sup_le hSP (Subgroup.zpowers_le.mpr hnP))
      have hsupH : T ≤ centralizer ({t} : Set G) :=
        sup_le hS.1 (Subgroup.zpowers_le.mpr hnH)
      have hle : T ≤ S :=
        isSylow2Of_eq_of_le hS hsup2 le_sup_left hsupH
      exact hnS (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers n)))
    ·
      refine hnt n⁻¹ ?_
      rw [inv_inv, ← ha]
      group
    ·
      obtain ⟨h, hh⟩ := hconj
      refine hnt (h * n⁻¹) ?_
      calc (h * n⁻¹)⁻¹ * z * (h * n⁻¹)
          = n * (h⁻¹ * z * h) * n⁻¹ := by group
        _ = n * (t * z) * n⁻¹ := by rw [hh]
        _ = n * (n⁻¹ * t * n) * n⁻¹ := by rw [← ha]
        _ = t := by group
  refine ⟨le_top, hS.2.1, ?_⟩
  rw [Subgroup.relIndex_top_right, hSPeq]
  exact P.not_dvd_index

end CFSG.OddStandard.SmallF3.Omega
