module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GInner
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sec5g_card_le {z : G} {S Q R D : Subgroup G} (hQS : Q ≤ S)
    (hSQ : S ≤ normalizer (Q : Set G)) (hQe : IsExtraspecialPGroup 2 ↥Q)
    (hQz : centerIn Q = zpowers z) (hz : orderOf z = 2) (hR : R = S ⊓ centralizer (Q : Set G))
    (hzR : z ∈ R) (hDS : D ≤ S) (hDnorm : ∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D)
    (hDQ : ∀ x ∈ D, x ∈ Q → x ∈ zpowers z) : Nat.card ↥D ≤ Nat.card ↥R := by
  subst hR
  have hDQR : ∀ d ∈ D, d ∈ Q ⊔ S ⊓ centralizer (Q : Set G) := by
    intro d hd
    have hdS : d ∈ S := hDS hd
    have hc : ∀ q ∈ Q, d * q * d⁻¹ * q⁻¹ ∈ centerIn Q := by
      intro q hq
      rw [hQz]
      refine hDQ _ ?_ ?_
      · have e : d * q * d⁻¹ * q⁻¹ = d * (q * d⁻¹ * q⁻¹) := by group
        rw [e]
        exact D.mul_mem hd (hDnorm q (hQS hq) d⁻¹ (D.inv_mem hd))
      · exact Q.mul_mem ((mem_normalizer_iff.mp (hSQ hdS) q).mp hq) (Q.inv_mem hq)
    obtain ⟨x, hxQ, hxc⟩ := sec5g_exists_mul_centralizer hQe (hSQ hdS) hc
    have e : d = x * (x⁻¹ * d) := by group
    rw [e]
    exact mul_mem_sup hxQ ⟨S.mul_mem (S.inv_mem (hQS hxQ)) hdS, hxc⟩
  have h1 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := D) (K := Q) (fun d hd => hSQ (hDS hd))
  have h2 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := S ⊓ centralizer (Q : Set G)) (K := Q) (fun r hr => hSQ hr.1)
  have h3 : Nat.card ↥(D ⊔ Q) ≤ Nat.card ↥(S ⊓ centralizer (Q : Set G) ⊔ Q) :=
    Subgroup.card_le_of_le (sup_le (fun d hd => by rw [sup_comm]; exact hDQR d hd) le_sup_right)
  have hzQ : z ∈ Q := (sec5_mem_centerIn_iff.mp (hQz ▸ mem_zpowers z)).1
  have h4 : Nat.card ↥(D ⊓ Q) ≤ 2 := by
    calc Nat.card ↥(D ⊓ Q) ≤ Nat.card ↥(zpowers z) :=
          Subgroup.card_le_of_le fun x hx => hDQ x hx.1 hx.2
      _ = 2 := by rw [Nat.card_zpowers, hz]
  have h5 : 2 ≤ Nat.card ↥(S ⊓ centralizer (Q : Set G) ⊓ Q) := by
    calc 2 = Nat.card ↥(zpowers z) := by rw [Nat.card_zpowers, hz]
      _ ≤ Nat.card ↥(S ⊓ centralizer (Q : Set G) ⊓ Q) :=
          Subgroup.card_le_of_le (zpowers_le.mpr ⟨hzR, hzQ⟩)
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hQpos
  calc Nat.card ↥D * Nat.card ↥Q = Nat.card ↥(D ⊔ Q) * Nat.card ↥(D ⊓ Q) := h1.symm
    _ ≤ Nat.card ↥(S ⊓ centralizer (Q : Set G) ⊔ Q) * 2 := Nat.mul_le_mul h3 h4
    _ ≤ Nat.card ↥(S ⊓ centralizer (Q : Set G) ⊔ Q) *
          Nat.card ↥(S ⊓ centralizer (Q : Set G) ⊓ Q) := Nat.mul_le_mul_left _ h5
    _ = Nat.card ↥(S ⊓ centralizer (Q : Set G)) * Nat.card ↥Q := h2

variable {X : Type} [Group X]

theorem sec5g_not_caseIII {z : G} {H S Q R T : Subgroup G} (π : ↥H →* X)
    (hker : π.ker = (zpowers z).subgroupOf H)
    (hSH : S ≤ H) (hQS : Q ≤ S) (hSQ : S ≤ normalizer (Q : Set G))
    (hQe : IsExtraspecialPGroup 2 ↥Q) (hQz : centerIn Q = zpowers z) (hz : orderOf z = 2)
    (hsq : ∀ x ∈ Q, x ^ 2 ∈ zpowers z) (hR : R = S ⊓ centralizer (Q : Set G))
    (hR16 : Nat.card ↥R ∣ 16) (hTR : T ≤ R) (hzT : z ∈ T) :
    ¬ Sec5GCaseIII ((S.subgroupOf H).map π) ((T.subgroupOf H).map π) := by
  intro hIII
  classical
  set SX : Subgroup X := (S.subgroupOf H).map π with hSX
  set A : Subgroup X := (T.subgroupOf H).map π with hA
  set M : Subgroup X := normalClosure (A : Set X) with hM
  haveI : M.Normal := Subgroup.normalClosure_normal
  let D' : Subgroup ↥H := S.subgroupOf H ⊓ M.comap π
  let D : Subgroup G := D'.map H.subtype
  have hDmem : ∀ d : G, d ∈ D ↔ ∃ hd : d ∈ H, d ∈ S ∧ π ⟨d, hd⟩ ∈ M := by
    intro d
    constructor
    · rintro ⟨d', hd', rfl⟩
      exact ⟨d'.2, hd'.1, hd'.2⟩
    · rintro ⟨hd, hdS, hdM⟩
      exact ⟨⟨d, hd⟩, ⟨hdS, hdM⟩, rfl⟩
  have hDS : D ≤ S := fun d hd => ((hDmem d).mp hd).2.1
  have hDnorm : ∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D := by
    intro s hs d hd
    obtain ⟨hdH, hdS, hdM⟩ := (hDmem d).mp hd
    have hsH : s ∈ H := hSH hs
    have hsdH : s * d * s⁻¹ ∈ H := H.mul_mem (H.mul_mem hsH hdH) (H.inv_mem hsH)
    refine (hDmem _).mpr ⟨hsdH, S.mul_mem (S.mul_mem hs hdS) (S.inv_mem hs), ?_⟩
    have e : π ⟨s * d * s⁻¹, hsdH⟩ = π ⟨s, hsH⟩ * π ⟨d, hdH⟩ * (π ⟨s, hsH⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact (inferInstance : M.Normal).conj_mem _ hdM _
  have hcardD : Nat.card ↥(SX ⊓ M) ≤ Nat.card ↥D := by
    have hle : SX ⊓ M ≤ D'.map π := by
      rintro y ⟨⟨s', hs', rfl⟩, hyM⟩
      exact ⟨s', ⟨hs', hyM⟩, rfl⟩
    haveI : Finite ↥(D'.map π) := Finite.of_surjective _ (π.subgroupMap_surjective D')
    calc Nat.card ↥(SX ⊓ M) ≤ Nat.card ↥(D'.map π) := Subgroup.card_le_of_le hle
      _ ≤ Nat.card ↥D' := Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd D' π)
      _ = Nat.card ↥D := (Subgroup.card_map_of_injective H.subtype_injective).symm
  have hDQ : ∀ x ∈ D, x ∈ Q → x ∈ zpowers z := by
    intro x hxD hxQ
    obtain ⟨hxH, hxS, hxM⟩ := (hDmem x).mp hxD
    have hsx : π ⟨x, hxH⟩ ∈ SX ⊓ M := ⟨⟨⟨x, hxH⟩, hxS, rfl⟩, hxM⟩
    have hsq1 : π ⟨x, hxH⟩ * π ⟨x, hxH⟩ = 1 := by
      rw [← map_mul]
      have hmk : (⟨x, hxH⟩ * ⟨x, hxH⟩ : ↥H) ∈ π.ker := by
        rw [hker]
        show x * x ∈ zpowers z
        rw [← sq]
        exact hsq x hxQ
      exact hmk
    obtain ⟨t', ht', hπt⟩ := hIII.2 _ hsx hsq1
    have hk : t'⁻¹ * ⟨x, hxH⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπt, inv_mul_cancel]
    rw [hker] at hk
    have hk' : (t' : G)⁻¹ * x ∈ zpowers z := hk
    have hxT : x ∈ T := by
      have := T.mul_mem (show (t' : G) ∈ T from ht') ((zpowers_le.mpr hzT) hk')
      simpa using this
    have hxR : x ∈ centralizer (Q : Set G) := ((hR ▸ hTR hxT : x ∈ S ⊓ centralizer (Q : Set G))).2
    rw [← hQz]
    exact sec5_mem_centerIn_iff.mpr ⟨hxQ, fun y hy => (mem_centralizer_iff.mp hxR y hy).symm⟩
  have hDR := sec5g_card_le hQS hSQ hQe hQz hz hR (hTR hzT) hDS hDnorm hDQ
  have h16 : Nat.card ↥R ≤ 16 := Nat.le_of_dvd (by norm_num) hR16
  have h64 : 64 ≤ Nat.card ↥(SX ⊓ M) := hIII.1
  omega

end CFSG.OddStandard.SmallF3.Omega
