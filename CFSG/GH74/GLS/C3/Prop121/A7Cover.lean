module

public import CFSG.GH74.GLS.C3.Layer3.A8Cover

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Layer3
open scoped commutatorElement

theorem not_dvd_card_alt7 : ¬ 27 ∣ Nat.card (alternatingGroup (Fin 7)) := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem preimage_closure_pair_commutes_of_commute {E Q : Type*} [Group E] [Group Q] (η : E →* Q)
    (hker : η.ker ≤ Subgroup.center E) {ea eb : E} (hc : Commute ea eb)
    (hab : Commute (η ea) (η eb)) :
    ∀ p ∈ (closure ({η ea, η eb} : Set Q)).comap η,
      ∀ q ∈ (closure ({η ea, η eb} : Set Q)).comap η, p * q = q * p := by
  have hform : ∀ p ∈ (closure ({η ea, η eb} : Set Q)).comap η,
      ∃ (m n : ℤ) (z : E), z ∈ η.ker ∧ p = ea ^ m * eb ^ n * z := by
    intro p hp
    obtain ⟨m, n, hmn⟩ := mem_closure_pair_of_commute hab (Subgroup.mem_comap.1 hp)
    refine ⟨m, n, (ea ^ m * eb ^ n)⁻¹ * p, ?_, by group⟩
    rw [MonoidHom.mem_ker]
    simp [map_mul, map_zpow, hmn]
  intro p hp q hq
  obtain ⟨m, n, z, hz, rfl⟩ := hform p hp
  obtain ⟨m', n', z', hz', rfl⟩ := hform q hq
  have hXY : Commute (ea ^ m * eb ^ n) (ea ^ m' * eb ^ n') := by
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact (Commute.refl ea).zpow_zpow m m'
    · exact hc.zpow_zpow m n'
    · exact (hc.symm).zpow_zpow n m'
    · exact (Commute.refl eb).zpow_zpow n n'
  have hzc : ∀ w ∈ η.ker, ∀ x : E, Commute w x := fun w hw x =>
    (Subgroup.mem_center_iff.1 (hker hw) x).symm
  exact ((hXY.mul_right (hzc z' hz' _).symm).mul_left
    ((hzc z hz _).mul_right (hzc z hz z'))).eq

theorem alt7_ker_inf_commutator_eq_bot {E : Type*} [Group E] [Finite E]
    (η : E →* alternatingGroup (Fin 7)) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center E) (hk3 : IsPGroup 3 η.ker) {ea eb : E} (hc : Commute ea eb)
    (ha3 : η ea ^ 3 = 1) (hb3 : η eb ^ 3 = 1) (ha1 : η ea ≠ 1) (hba : η eb ∉ zpowers (η ea)) :
    η.ker ⊓ commutator E = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hab : Commute (η ea) (η eb) := hc.map η
  set K := closure ({η ea, η eb} : Set (alternatingGroup (Fin 7))) with hK
  set P := K.comap η with hP
  have hcard : Nat.card K = 9 := card_closure_pair_eq_nine hab ha3 hb3 ha1 hba not_dvd_card_alt7
  have hidx : ¬ 3 ∣ P.index := by
    rw [hP, Subgroup.index_comap_of_surjective K hη]
    have h1 := Subgroup.card_mul_index K
    rw [hcard, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 : K.index = 280 := by
      have : (7 : ℕ).factorial / 2 = 2520 := by decide
      rw [this] at h1; omega
    rw [h2]; decide
  have hcomm := preimage_closure_pair_commutes_of_commute η hker hc hab
  rw [eq_bot_iff]
  rintro z ⟨hzker, hzcomm⟩
  have hzP : z ∈ P := by
    rw [hP, Subgroup.mem_comap, (MonoidHom.mem_ker.1 hzker)]
    exact K.one_mem
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hk3) ⟨z, hzker⟩
  have hzo : orderOf z = 3 ^ k := by rw [← hk, Subgroup.orderOf_mk]
  have hmem := mem_commutator_of_central_of_transfer P Nat.prime_three hidx (hker hzker) hzP
    ⟨k, hzo⟩ hzcomm
  have hbot : commutator P = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _ y _
    exact Subtype.ext (hcomm _ y.2 _ x.2)
  rw [hbot, Subgroup.mem_bot] at hmem
  have : z = 1 := congrArg Subtype.val hmem
  rw [this]; exact Subgroup.one_mem _

theorem exists_complement_of_central_three_alt7 {E : Type*} [Group E] [Finite E]
    (η : E →* alternatingGroup (Fin 7)) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center E) (hk3 : IsPGroup 3 η.ker) {ea eb : E} (hc : Commute ea eb)
    (ha3 : η ea ^ 3 = 1) (hb3 : η eb ^ 3 = 1) (ha1 : η ea ≠ 1) (hba : η eb ∉ zpowers (η ea)) :
    ∃ L : Subgroup E, L ⊓ η.ker = ⊥ ∧ L ⊔ η.ker = ⊤ ∧
      Nonempty (L ≃* alternatingGroup (Fin 7)) := by
  classical
  have hinf : η.ker ⊓ commutator E =
      ⊥ := alt7_ker_inf_commutator_eq_bot η hη hker hk3 hc ha3 hb3 ha1 hba
  have hmap : (commutator E).map η = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective η hη]
    have h5 : 5 ≤ Nat.card (Fin 7) := by simp
    have := commutator_alternatingGroup_eq_top h5
    rw [_root_.commutator_def] at this
    exact this
  have hinj : Function.Injective (η.comp (commutator E).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : (x : E) ∈ η.ker ⊓ commutator E := ⟨hx, x.2⟩
    rw [hinf, Subgroup.mem_bot] at hx1
    exact Subtype.ext hx1
  have hsurj : Function.Surjective (η.comp (commutator E).subtype) := by
    intro y
    have : y ∈ (commutator E).map η := by rw [hmap]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨commutator E, by rw [inf_comm]; exact hinf, ?_,
    ⟨MulEquiv.ofBijective (η.comp (commutator E).subtype) ⟨hinj, hsurj⟩⟩⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ : ∃ y : commutator E, η y = η x := hsurj (η x)
  have hz : (y : E)⁻¹ * x ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    simp [hy]
  have : x = (y : E) * ((y : E)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup y.2 hz

end CFSG.GH74.GLS.C3.Prop121
