module

public import CFSG.Dihedral.OriginalOddCore
public import CFSG.Dihedral.OriginalSylowControl

public noncomputable section

namespace CFSG.DihedralBlueprint

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_dvd_card (p : ℕ) (hp : p.Prime) (P R : Subgroup G)
    (hP : IsSylowIn p P R) (hdiv : p ∣ Nat.card R) : p ∣ Nat.card P := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ := (isSylowIn_iff_exists_sylow p P R).mp hP
  have h := Q.dvd_card_of_dvd_card hdiv
  rw [← hQ, Subgroup.card_map_of_injective R.subtype_injective]
  exact h

theorem isSylowIn_ne_bot (p : ℕ) (hp : p.Prime) (P R : Subgroup G)
    (hP : IsSylowIn p P R) (hdiv : p ∣ Nat.card R) : P ≠ ⊥ := by
  intro hbot
  have h := isSylowIn_dvd_card p hp P R hP hdiv
  rw [hbot, Subgroup.card_bot] at h
  exact hp.not_dvd_one h

theorem isSylowIn_eq_of_card_prime (p : ℕ) (hp : p.Prime) (P R : Subgroup G)
    (hP : IsSylowIn p P R) (hRcard : Nat.card R = p) : P = R := by
  have hd := Subgroup.card_dvd_of_le hP.1
  rw [hRcard] at hd
  rcases (Nat.dvd_prime hp).mp hd with h1 | hpP
  · have hdiv := isSylowIn_dvd_card p hp P R hP (hRcard ▸ dvd_refl p)
    rw [h1] at hdiv
    exact (hp.not_dvd_one hdiv).elim
  · exact Subgroup.eq_of_le_of_card_ge hP.1 (by rw [hRcard, hpP])

theorem stationary_sylow_core_and_unique (p : ℕ) (hp : p.Prime) (P : Subgroup G)
    (hP : IsSylowIn p P (oddCoreOf (Subgroup.normalizer (P : Set G)))) :
    P = (Assembly.pCore p (oddCoreOf (Subgroup.normalizer (P : Set G)))).map
        (oddCoreOf (Subgroup.normalizer (P : Set G))).subtype ∧
    ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ oddCoreOf (Subgroup.normalizer (P : Set G)) →
      Q ≤ P := by
  let _ : Fact p.Prime := ⟨hp⟩
  let K := oddCoreOf (Subgroup.normalizer (P : Set G))
  have hPK : P ≤ K := hP.1
  have hPnormal : (P.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (oddCoreOf_le _)
  obtain ⟨P0, hP0⟩ := (isSylowIn_iff_exists_sylow p P K).mp hP
  have hP0sub : (P0 : Subgroup K) = P.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [hP0, Subgroup.map_subgroupOf_eq_of_le hPK]
  have hP0normal : (P0 : Subgroup K).Normal := hP0sub.symm ▸ hPnormal
  let _ := hP0normal
  have hall (Q : Subgroup G) (hQp : IsPGroup p Q) (hQK : Q ≤ K) : Q ≤ P := by
    have hQp' := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
    have hQle : Q.subgroupOf K ≤ (P0 : Subgroup K) := by
      let _ : Unique (Sylow p K) := Sylow.unique_of_normal P0 hP0normal
      obtain ⟨Q0, hQ0⟩ := hQp'.exists_le_sylow
      have heq : Q0 = P0 := Subsingleton.elim _ _
      rwa [heq] at hQ0
    have h := Subgroup.map_mono (f := K.subtype) hQle
    rwa [Subgroup.map_subgroupOf_eq_of_le hQK, hP0] at h
  refine ⟨le_antisymm ?_ ?_, hall⟩
  · have hPp' := hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
    have hcore : P.subgroupOf K ≤ Assembly.pCore p K :=
      le_sSup ⟨hPnormal, hPp'⟩
    have h := Subgroup.map_mono (f := K.subtype) hcore
    rwa [Subgroup.map_subgroupOf_eq_of_le hPK] at h
  · apply Subgroup.map_le_iff_le_comap.mpr
    change Assembly.pCore p K ≤ P.subgroupOf K
    rw [CFSG.pCore_eq_iSup]
    apply iSup_le
    intro Q
    apply iSup_le
    intro hQnormal
    apply iSup_le
    intro hQp
    rw [← hP0sub]
    exact hQp.le_sylow_of_normal P0

end CFSG.DihedralBlueprint
