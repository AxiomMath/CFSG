module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Growth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Facts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec5c3q_le_of_isSylow2Of [Finite G] {S H T : Subgroup G} (hS : IsSylow2Of S H)
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

private theorem sec5c3q_exists_mem_normalizer [Finite G] {S P : Subgroup G} (hP : IsPGroup 2 P)
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

theorem sec5c3q_isSylow2Of_top [Finite G] {t z : G} {S : Subgroup G}
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (ht2 : orderOf t = 2) (hz2 : orderOf z = 2)
    (hΩ : omega1 (centerIn S) = zpowers t ⊔ zpowers z)
    (hnt : ∀ g : G, g⁻¹ * z * g ≠ t) (hnc : ¬ ∃ h : G, h⁻¹ * t * h = t * z) :
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
    obtain ⟨n, hnP, hnS, hnN⟩ := sec5c3q_exists_mem_normalizer P.isPGroup' hlt
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
      have hle : T ≤ S := sec5c3q_le_of_isSylow2Of hS hsup2 le_sup_left hsupH
      exact hnS (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers n)))
    ·
      refine hnt n⁻¹ ?_
      rw [inv_inv, ← ha]
      group
    ·
      exact hnc ⟨n, ha⟩
  refine ⟨le_top, hS.2.1, ?_⟩
  rw [Subgroup.relIndex_top_right, hSPeq]
  exact P.not_dvd_index

theorem sec5c3q_isSylow2Of_top_ctx [Finite G] (h37 : Asc82Lemma37) (h53 : Asc82Lemma53)
    {t : G} {L S : Subgroup G} {z : G} (h : Sec5Ctx G t L S z)
    (hnc : ¬ ∃ g : G, g⁻¹ * t * g = t * z) : IsSylow2Of S ⊤ :=
  sec5c3q_isSylow2Of_top h.sylow h.involution h.pocket.1 (h53 G t L S z h)
    (sec5_t_not_conj_z h37 h) hnc

end CFSG.OddStandard.SmallF3.Omega
