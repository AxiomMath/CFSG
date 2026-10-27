module

public import CFSG.GH74.GLS.C3.Prop121.A7Cover

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Layer3
open scoped commutatorElement

theorem not_dvd_card_alt6 : ¬ 27 ∣ Nat.card (alternatingGroup (Fin 6)) := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem alt6_ker_inf_commutator_eq_bot {E : Type*} [Group E] [Finite E]
    (η : E →* alternatingGroup (Fin 6)) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center E) (hk3 : IsPGroup 3 η.ker) {ea eb : E} (hc : Commute ea eb)
    (ha3 : η ea ^ 3 = 1) (hb3 : η eb ^ 3 = 1) (ha1 : η ea ≠ 1) (hba : η eb ∉ zpowers (η ea)) :
    η.ker ⊓ commutator E = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hab : Commute (η ea) (η eb) := hc.map η
  set K := closure ({η ea, η eb} : Set (alternatingGroup (Fin 6))) with hK
  set P := K.comap η with hP
  have hcard : Nat.card K = 9 := card_closure_pair_eq_nine hab ha3 hb3 ha1 hba not_dvd_card_alt6
  have hidx : ¬ 3 ∣ P.index := by
    rw [hP, Subgroup.index_comap_of_surjective K hη]
    have h1 := Subgroup.card_mul_index K
    rw [hcard, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 : K.index = 40 := by
      have : (6 : ℕ).factorial / 2 = 360 := by decide
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

theorem exists_complement_of_central_three_alt6 {E : Type*} [Group E] [Finite E]
    (η : E →* alternatingGroup (Fin 6)) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center E) (hk3 : IsPGroup 3 η.ker) {ea eb : E} (hc : Commute ea eb)
    (ha3 : η ea ^ 3 = 1) (hb3 : η eb ^ 3 = 1) (ha1 : η ea ≠ 1) (hba : η eb ∉ zpowers (η ea)) :
    ∃ L : Subgroup E, L ⊓ η.ker = ⊥ ∧ L ⊔ η.ker = ⊤ ∧
      Nonempty (L ≃* alternatingGroup (Fin 6)) := by
  classical
  have hinf : η.ker ⊓ commutator E =
      ⊥ := alt6_ker_inf_commutator_eq_bot η hη hker hk3 hc ha3 hb3 ha1 hba
  have hmap : (commutator E).map η = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective η hη]
    have h5 : 5 ≤ Nat.card (Fin 6) := by simp
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
