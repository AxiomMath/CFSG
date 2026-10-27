module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem card_fiber_eq_card_comap_centralizer {K : Type*} [Group K] [Finite K]
    (Q : Subgroup K) [Q.Normal] (c : K) :
    Nat.card {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧ (s : K ⧸ Q) = (c : K ⧸ Q)} *
        Nat.card ↥(Subgroup.centralizer ({c} : Set K)) =
      Nat.card ↥((Subgroup.centralizer
          ({(c : K ⧸ Q)} : Set (K ⧸ Q))).comap (QuotientGroup.mk' Q)) := by
  classical
  let P : Subgroup K :=
    (Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))).comap (QuotientGroup.mk' Q)
  letI : MulAction ↥P K := MulAction.compHom K (MulAut.conj.comp P.subtype)
  haveI : Fintype ↥P := Fintype.ofFinite ↥P
  haveI : Fintype (MulAction.orbit ↥P c) :=
    (Finite.finite_mulAction_orbit (M := ↥P) c).fintype
  haveI : Fintype (MulAction.stabilizer ↥P c) := Fintype.ofFinite _
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥P) c
  have hsmul : ∀ (p : ↥P) (x : K), p • x = (p : K) * x * (p : K)⁻¹ := by
    intro p x
    change MulAut.conj (p : K) x = (p : K) * x * (p : K)⁻¹
    rw [MulAut.conj_apply]
  have hπc : ∀ p : ↥P, (QuotientGroup.mk' Q) (p : K) * (QuotientGroup.mk' Q) c =
      (QuotientGroup.mk' Q) c * (QuotientGroup.mk' Q) (p : K) := by
    intro p
    have hp : (QuotientGroup.mk' Q) (p : K) ∈
        Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q)) := p.2
    rw [Subgroup.mem_centralizer_iff] at hp
    exact (hp ((QuotientGroup.mk' Q) c) (by simp)).symm
  have horbit : (MulAction.orbit ↥P c : Set K) =
      {s : K | (∃ k : K, k * c * k⁻¹ = s) ∧ (s : K ⧸ Q) = (c : K ⧸ Q)} := by
    ext s
    constructor
    · intro hs
      rw [MulAction.mem_orbit_iff] at hs
      obtain ⟨p, rfl⟩ := hs
      refine ⟨⟨(p : K), ?_⟩, ?_⟩
      · rw [hsmul]
      · change (QuotientGroup.mk' Q) ((p : K) * c * (p : K)⁻¹) = (c : K ⧸ Q)
        rw [map_mul, map_mul, map_inv, hπc p, mul_assoc, mul_inv_cancel, mul_one]
        rfl
    · rintro ⟨⟨k, hk⟩, hkc⟩
      rw [MulAction.mem_orbit_iff]
      have hkP : k ∈ P := by
        change (QuotientGroup.mk' Q) k ∈
          Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have h1 : (QuotientGroup.mk' Q) (k * c * k⁻¹) = (QuotientGroup.mk' Q) s := by
          rw [hk]
        have hkc' : (QuotientGroup.mk' Q) s = (QuotientGroup.mk' Q) c := hkc
        rw [map_mul, map_mul, map_inv, hkc'] at h1
        have h3 : (QuotientGroup.mk' Q) k * (QuotientGroup.mk' Q) c =
            (QuotientGroup.mk' Q) c * (QuotientGroup.mk' Q) k := by
          have hh3 := congrArg (· * (QuotientGroup.mk' Q) k) h1
          simpa [mul_assoc] using hh3
        exact h3.symm
      refine ⟨⟨k, hkP⟩, ?_⟩
      rw [hsmul]
      exact hk
  have hcard_orbit : Nat.card ↥(MulAction.orbit ↥P c) =
      Nat.card {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧
        (s : K ⧸ Q) = (c : K ⧸ Q)} :=
    Nat.card_congr (Set.equivOfEq horbit)
  have hCP : Subgroup.centralizer ({c} : Set K) ≤ P := by
    intro k hk
    change (QuotientGroup.mk' Q) k ∈
      Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hk' : c * k = k * c := (Subgroup.mem_centralizer_iff.mp hk) c (by simp)
    have hh' := congrArg (QuotientGroup.mk' Q) hk'
    rwa [map_mul, map_mul] at hh'
  have hstab : MulAction.stabilizer ↥P c =
      (Subgroup.centralizer ({c} : Set K)).subgroupOf P := by
    ext p
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    have hpc : (p : K) * c * (p : K)⁻¹ = c ↔ c * (p : K) = (p : K) * c := by
      constructor
      · intro h
        have hh := congrArg (· * (p : K)) h
        have hh' : (p : K) * c = c * (p : K) := by simpa [mul_assoc] using hh
        exact hh'.symm
      · intro h
        rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hsmul, hpc, Subgroup.mem_centralizer_iff]
    simp
  have hcard_stab : Nat.card ↥(MulAction.stabilizer ↥P c) =
      Nat.card ↥(Subgroup.centralizer ({c} : Set K)) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv
  have hOS' : Nat.card ↥(MulAction.orbit ↥P c) *
      Nat.card ↥(MulAction.stabilizer ↥P c) = Nat.card ↥P := by
    rw [Nat.card_eq_fintype_card (α := MulAction.orbit ↥P c),
      Nat.card_eq_fintype_card (α := MulAction.stabilizer ↥P c),
      Nat.card_eq_fintype_card (α := ↥P)]
    exact hOS
  calc Nat.card {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧
          (s : K ⧸ Q) = (c : K ⧸ Q)} *
        Nat.card ↥(Subgroup.centralizer ({c} : Set K))
      = Nat.card ↥(MulAction.orbit ↥P c) * Nat.card ↥(MulAction.stabilizer ↥P c) := by
        rw [← hcard_orbit, ← hcard_stab]
    _ = Nat.card ↥P := hOS'
    _ = Nat.card ↥((Subgroup.centralizer
          ({(c : K ⧸ Q)} : Set (K ⧸ Q))).comap (QuotientGroup.mk' Q)) := rfl

private theorem card_comap_centralizer_eq {K : Type*} [Group K] [Finite K]
    (Q : Subgroup K) [Q.Normal] (c : K) :
    Nat.card ↥((Subgroup.centralizer
        ({(c : K ⧸ Q)} : Set (K ⧸ Q))).comap (QuotientGroup.mk' Q)) =
      Nat.card ↥Q * Nat.card ↥(Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))) := by
  classical
  let P : Subgroup K :=
    (Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))).comap (QuotientGroup.mk' Q)
  let g : ↥P →* K ⧸ Q := (QuotientGroup.mk' Q).comp P.subtype
  have hQP : Q ≤ P := by
    intro q hq
    change (QuotientGroup.mk' Q) q ∈
      Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    have hq1 : (QuotientGroup.mk' Q) q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
    rw [hq1, one_mul, mul_one]
  have hker : g.ker = Q.subgroupOf P := by
    change ((QuotientGroup.mk' Q).comp P.subtype).ker = Q.subgroupOf P
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hker_card : Nat.card ↥g.ker = Nat.card ↥Q := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
  have hrange : g.range =
      Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q)) := by
    change ((QuotientGroup.mk' Q).comp P.subtype).range =
      Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q) _
  have h := Subgroup.card_ker_mul_card_range g
  rw [hker_card, hrange] at h
  exact h.symm

theorem card_fiber_mul_card_centralizer {K : Type*} [Group K] [Finite K] (Q : Subgroup K)
    [Q.Normal] (c : K) :
    Nat.card {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧ (s : K ⧸ Q) = (c : K ⧸ Q)} *
        Nat.card ↥(Subgroup.centralizer ({c} : Set K)) =
      Nat.card ↥Q * Nat.card ↥(Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))) := by
  rw [card_fiber_eq_card_comap_centralizer Q c, card_comap_centralizer_eq Q c]

private theorem card_sup_mul_card_inf {K : Type*} [Group K] [Finite K]
    (Q C : Subgroup K) [Q.Normal] :
    Nat.card ↥(Q ⊔ C) * Nat.card ↥(C ⊓ Q) = Nat.card ↥Q * Nat.card ↥C := by
  classical
  have hQ : Q ≤ Q ⊔ C := le_sup_left
  have hD : C ⊓ Q ≤ C := inf_le_left
  have hcardQ : Nat.card ↥(Q.subgroupOf (Q ⊔ C)) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
  have hcardD : Nat.card ↥((C ⊓ Q).subgroupOf C) = Nat.card ↥(C ⊓ Q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv
  have hidx : (Q.subgroupOf (Q ⊔ C)).index = ((C ⊓ Q).subgroupOf C).index := by
    rw [show (Q.subgroupOf (Q ⊔ C)).index = Q.relIndex (Q ⊔ C) from rfl,
      sup_comm, Subgroup.relIndex_sup_right]
    rw [show Q.relIndex C = (Q.subgroupOf C).index from rfl,
      Subgroup.inf_subgroupOf_left]
  have h1 : Nat.card ↥(Q ⊔ C) =
      Nat.card ↥(Q.subgroupOf (Q ⊔ C)) * (Q.subgroupOf (Q ⊔ C)).index :=
    (Subgroup.card_mul_index (Q.subgroupOf (Q ⊔ C))).symm
  have h2 : Nat.card ↥C =
      Nat.card ↥((C ⊓ Q).subgroupOf C) * ((C ⊓ Q).subgroupOf C).index :=
    (Subgroup.card_mul_index ((C ⊓ Q).subgroupOf C)).symm
  have hmul : ∀ a i d : ℕ, a * i * d = a * (d * i) := by
    intro a i d
    rw [Nat.mul_assoc, Nat.mul_comm i d]
  rw [h1, h2, hcardQ, hcardD, hidx]
  exact hmul _ _ _

theorem card_dvd_card_fiber_mul {K : Type*} [Group K] [Finite K] (Q : Subgroup K) [Q.Normal]
    (c : K) :
    Nat.card ↥Q ∣
      Nat.card {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧ (s : K ⧸ Q) = (c : K ⧸ Q)} *
        Nat.card ↥(Subgroup.centralizer ({c} : Set K) ⊓ Q) := by
  classical
  let C : Subgroup K := Subgroup.centralizer ({c} : Set K)
  let P : Subgroup K :=
    (Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))).comap (QuotientGroup.mk' Q)
  have hFP : Nat.card {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧
        (s : K ⧸ Q) = (c : K ⧸ Q)} * Nat.card ↥C = Nat.card ↥P :=
    card_fiber_eq_card_comap_centralizer Q c
  have hprod : Nat.card ↥(Q ⊔ C) * Nat.card ↥(C ⊓ Q) = Nat.card ↥Q * Nat.card ↥C :=
    card_sup_mul_card_inf Q C
  have hQP : Q ≤ P := by
    intro q hq
    change (QuotientGroup.mk' Q) q ∈
      Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    have hq1 : (QuotientGroup.mk' Q) q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
    rw [hq1, one_mul, mul_one]
  have hCP : C ≤ P := by
    intro k hk
    change (QuotientGroup.mk' Q) k ∈
      Subgroup.centralizer ({(c : K ⧸ Q)} : Set (K ⧸ Q))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hk' : c * k = k * c := (Subgroup.mem_centralizer_iff.mp hk) c (by simp)
    have hh' := congrArg (QuotientGroup.mk' Q) hk'
    rwa [map_mul, map_mul] at hh'
  have hRP : Q ⊔ C ≤ P := sup_le hQP hCP
  have hdvd : Nat.card ↥(Q ⊔ C) ∣
      Nat.card {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧
        (s : K ⧸ Q) = (c : K ⧸ Q)} * Nat.card ↥C := by
    have hh := Subgroup.card_dvd_of_le hRP
    rwa [← hFP] at hh
  have hb : Nat.card ↥C ≠ 0 := by
    have hpos : 0 < Nat.card ↥C := Nat.card_pos (α := ↥C)
    exact hpos.ne'
  have h1 : Nat.card ↥Q * Nat.card ↥C ∣
      (Nat.card {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧
          (s : K ⧸ Q) = (c : K ⧸ Q)} * Nat.card ↥(C ⊓ Q)) * Nat.card ↥C := by
    rw [← hprod]
    have hh := mul_dvd_mul_right hdvd (Nat.card ↥(C ⊓ Q))
    convert hh using 1
    exact Nat.mul_right_comm _ _ _
  exact (mul_dvd_mul_iff_right hb).mp h1

end CFSG.EvenSporadicStandard.HNRecog.Section3