module

public import CFSG.GroupTheory.CentralizerSylowFusion

public section

namespace CFSG.GroupTheory

open Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem exists_sylow_mem_le_centralizer {p : ℕ} [Fact p.Prime] (P : Sylow p X) {u : X}
    (hu : orderOf u = p) (hPu : Nat.card P ∣ Nat.card (centralizer ({u} : Set X))) :
    ∃ Q : Sylow p X, u ∈ (Q : Subgroup X) ∧ (Q : Subgroup X) ≤ centralizer ({u} : Set X) := by
  classical
  let C : Subgroup X := centralizer ({u} : Set X)
  let R : Sylow p ↥C := default
  have hp : p.Prime := Fact.out
  have hCne : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hXne : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hkle : (Nat.card C).factorization p ≤ (Nat.card X).factorization p :=
    (Nat.factorization_le_iff_dvd hCne hXne).mpr (Subgroup.card_subgroup_dvd_card C) p
  have hPX : Nat.card P = p ^ (Nat.card X).factorization p := Sylow.card_eq_multiplicity P
  have hdvd : p ^ (Nat.card X).factorization p ∣ Nat.card C := by
    rw [← hPX]
    exact hPu
  have hkge : (Nat.card X).factorization p ≤ (Nat.card C).factorization p :=
    (hp.pow_dvd_iff_le_factorization hCne).mp hdvd
  have hk : (Nat.card C).factorization p = (Nat.card X).factorization p :=
    le_antisymm hkle hkge
  have hRcard : Nat.card R = p ^ (Nat.card C).factorization p := Sylow.card_eq_multiplicity R
  have hQcard : Nat.card ((R : Subgroup ↥C).map C.subtype) =
      p ^ (Nat.card X).factorization p := by
    rw [Subgroup.card_subtype, hRcard, hk]
  let Q : Sylow p X := Sylow.ofCard ((R : Subgroup ↥C).map C.subtype) hQcard
  have hQcoe : (Q : Subgroup X) = (R : Subgroup ↥C).map C.subtype := rfl
  have hQC : (Q : Subgroup X) ≤ C := by
    rw [hQcoe]
    rintro x ⟨r, -, rfl⟩
    exact r.2
  have hcomm : ∀ q ∈ (Q : Subgroup X), u * q = q * u := fun q hq =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hQC hq)).symm
  have hUp : IsPGroup p (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  have hUnorm : Subgroup.zpowers u ≤ Subgroup.normalizer ((Q : Subgroup X) : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : Commute u k := hcomm k hk
    have hkeq : u ^ m * k * (u ^ m)⁻¹ = k := by
      rw [(hc.zpow_left m).eq]
      group
    rwa [hkeq]
  have hSupP : IsPGroup p ↥((Q : Subgroup X) ⊔ Subgroup.zpowers u) :=
    IsPGroup.to_sup_of_normal_left' Q.isPGroup' hUp hUnorm
  have hSupEq : (Q : Subgroup X) ⊔ Subgroup.zpowers u = (Q : Subgroup X) :=
    Q.is_maximal' hSupP le_sup_left
  refine ⟨Q, ?_, hQC⟩
  have huSup : u ∈ (Q : Subgroup X) ⊔ Subgroup.zpowers u := Subgroup.mem_sup_right (by simp)
  rwa [hSupEq] at huSup

theorem conj_inv_mul_mem_center_of_sylow_smul (P Q : Sylow 2 X) {g u : X}
    (hg : g • P = Q) (huQ : u ∈ (Q : Subgroup X))
    (huc : (Q : Subgroup X) ≤ centralizer ({u} : Set X)) :
    g⁻¹ * u * g ∈ (P : Subgroup X) ∧
      ∀ x : ↥(P : Subgroup X), Commute (g⁻¹ * u * g) (x : X) := by
  have hgmap : (Q : Subgroup X) = (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun S : Sylow 2 X => (S : Subgroup X)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    rw [← h]
    rfl
  have haP : g⁻¹ * u * g ∈ (P : Subgroup X) := by
    have hmem : u ∈ (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
      rw [← hgmap]
      exact huQ
    obtain ⟨p, hpP, hp⟩ := Subgroup.mem_map.mp hmem
    have hgp : g⁻¹ * ((MulAut.conj g).toMonoidHom p) * g = p := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [← hp, hgp]
  refine ⟨haP, ?_⟩
  intro x
  have hxQ : g * (x : X) * g⁻¹ ∈ (Q : Subgroup X) := by
    rw [hgmap]
    simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom x.2
  have hux : Commute u (g * (x : X) * g⁻¹) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (huc hxQ)).symm
  have h := hux.map (MulAut.conj g⁻¹).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom] at h
  have hx : (MulAut.conj g⁻¹) (g * (x : X) * g⁻¹) = (x : X) := by
    rw [MulAut.conj_apply]
    group
  rw [hx] at h
  simpa [MulAut.conj_apply] using h

theorem eq_of_mem_center_of_card_center_eq_two (P : Sylow 2 X)
    (hZ : Nat.card (center ↥(P : Subgroup X)) = 2) {a t : X}
    (haP : a ∈ (P : Subgroup X)) (htP : t ∈ (P : Subgroup X))
    (ha : (⟨a, haP⟩ : ↥(P : Subgroup X)) ∈ center ↥(P : Subgroup X))
    (ht : (⟨t, htP⟩ : ↥(P : Subgroup X)) ∈ center ↥(P : Subgroup X))
    (ha1 : a ≠ 1) (ht1 : t ≠ 1) : a = t := by
  have huniq : ∃! z : ↥(center ↥(P : Subgroup X)), z ≠ 1 :=
    (Nat.card_eq_two_iff' (1 : ↥(center ↥(P : Subgroup X)))).mp hZ
  obtain ⟨z, -, hz_unique⟩ := huniq
  have hza_ne : (⟨⟨a, haP⟩, ha⟩ : ↥(center ↥(P : Subgroup X))) ≠ 1 := by
    intro h
    apply ha1
    simpa using congrArg (fun z : ↥(center ↥(P : Subgroup X)) => ((z : ↥(P : Subgroup X)) : X)) h
  have hzt_ne : (⟨⟨t, htP⟩, ht⟩ : ↥(center ↥(P : Subgroup X))) ≠ 1 := by
    intro h
    apply ht1
    simpa using congrArg (fun z : ↥(center ↥(P : Subgroup X)) => ((z : ↥(P : Subgroup X)) : X)) h
  have hEq := (hz_unique _ hza_ne).trans (hz_unique _ hzt_ne).symm
  have := congrArg (fun z : ↥(center ↥(P : Subgroup X)) => ((z : ↥(P : Subgroup X)) : X)) hEq
  simpa using this

theorem isConj_of_card_center_eq_two (P Q : Sylow 2 X)
    (hZ : Nat.card (center ↥(P : Subgroup X)) = 2) {t u : X} (htP : t ∈ (P : Subgroup X))
    (htc : ∀ s ∈ (P : Subgroup X), Commute t s) (ht : orderOf t = 2)
    (huQ : u ∈ (Q : Subgroup X)) (huc : (Q : Subgroup X) ≤ centralizer ({u} : Set X))
    (hu : orderOf u = 2) : IsConj t u := by
  classical
  haveI : Finite (Sylow 2 X) := Sylow.finite_of_finiteIndex P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  obtain ⟨haP, ha_comm⟩ := conj_inv_mul_mem_center_of_sylow_smul P Q hg huQ huc
  have ha_center : (⟨g⁻¹ * u * g, haP⟩ : ↥(P : Subgroup X)) ∈ center ↥(P : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (ha_comm x).symm.eq
  have ht_center : (⟨t, htP⟩ : ↥(P : Subgroup X)) ∈ center ↥(P : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (htc x x.2).symm.eq
  have horder_a : orderOf (g⁻¹ * u * g) = 2 := by
    have h := (MulAut.conj g⁻¹).orderOf_eq u
    simpa [MulAut.conj_apply, hu] using h
  have ha_ne : g⁻¹ * u * g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder_a
    simp at horder_a
  have ht_ne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    simp at ht
  have ha_eq_t : g⁻¹ * u * g = t :=
    eq_of_mem_center_of_card_center_eq_two P hZ haP htP ha_center ht_center ha_ne ht_ne
  rw [isConj_iff]
  refine ⟨g, ?_⟩
  rw [← ha_eq_t]
  group

theorem card_centralizer_eq_of_card_center_eq_two (P : Sylow 2 X)
    (hZ : Nat.card (center ↥(P : Subgroup X)) = 2) {t u : X} (htP : t ∈ (P : Subgroup X))
    (htc : ∀ s ∈ (P : Subgroup X), Commute t s) (ht : orderOf t = 2) (hu : orderOf u = 2)
    (hPu : Nat.card P ∣ Nat.card (centralizer ({u} : Set X))) :
    Nat.card (centralizer ({t} : Set X)) = Nat.card (centralizer ({u} : Set X)) := by
  obtain ⟨Q, huQ, huc⟩ := exists_sylow_mem_le_centralizer (p := 2) P hu hPu
  exact card_centralizer_singleton_congr_of_isConj
    (isConj_of_card_center_eq_two P Q hZ htP htc ht huQ huc hu)

end CFSG.GroupTheory
