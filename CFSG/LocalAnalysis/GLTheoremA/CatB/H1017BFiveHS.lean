module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveHS

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.RankThree.Native CFSG.EvenSporadicStandard.HSStd CFSG.Sporadic.SmallOddCore Subgroup

section Model

private theorem false_of_autModel_aux {X M : Type*} [Group X] [Group M] {P R : Subgroup M}
    (hM : AutModel P R)
    (hP : ∀ x ∈ P, orderOf x = 5 → ¬ 2 ^ 4 ∣ Nat.card ↥(centralizer ({x} : Set M) ⊓ R))
    (S : Subgroup X) [S.Normal] (θ : ↥S ≃* ↥P) {W : Subgroup X} (hWc : Nat.card W = 2 ^ 4)
    (hfaith : ∀ w ∈ W, w ≠ 1 → ∃ x ∈ S, w * x ≠ x * w) (e : ↥S) (he5 : orderOf (e : X) = 5)
    (heW : ∀ w ∈ W, w * e = e * w) : False := by
  have hker : ∀ x : X, hM.embed S θ x = 1 → ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    rw [AutModel.embed, MonoidHom.comp_apply, ← map_one hM.hom] at hx
    have h2 := congrArg (fun α : MulAut P => (α (θ ⟨y, hy⟩) : P)) (hM.hom_injective hx)
    simp only [transportAut_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    have h3 := congrArg Subtype.val (θ.injective h2)
    rw [MulAut.conjNormal_apply] at h3
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h3]
  have hinj : Function.Injective ((hM.embed S θ).comp W.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hw
    rw [mem_bot]
    by_contra hne
    obtain ⟨x, hx, hxw⟩ := hfaith w w.2 fun h => hne (Subtype.ext h)
    exact hxw (hker w hw x hx)
  have hle : ((hM.embed S θ).comp W.subtype).range ≤
      centralizer ({((θ e : P) : M)} : Set M) ⊓ R := by
    rintro _ ⟨w, rfl⟩
    rw [MonoidHom.comp_apply]
    refine mem_inf.2 ⟨?_, hM.embed_mem S θ _⟩
    rw [mem_centralizer_singleton_iff, ← hM.embed_coe S θ e, ← map_mul, ← map_mul]
    exact congrArg _ (heW w w.2)
  have hcard : Nat.card ((hM.embed S θ).comp W.subtype).range = 2 ^ 4 := by
    rw [← hWc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  refine hP _ (θ e).2 ?_ (by rw [← hcard]; exact card_dvd_of_le hle)
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact (Subgroup.orderOf_coe e).symm.trans he5

theorem false_of_autModel {G M : Type*} [Group G] [Group M] {P R : Subgroup M}
    (hM : AutModel P R)
    (hP : ∀ x ∈ P, orderOf x = 5 → ¬ 2 ^ 4 ∣ Nat.card ↥(centralizer ({x} : Set M) ⊓ R))
    {E : Subgroup G} (θ : ↥E ≃* ↥P) {W : Subgroup G} (hWc : Nat.card W = 2 ^ 4)
    (hWN : W ≤ normalizer (E : Set G)) (hfaith : ∀ w ∈ W, w ≠ 1 → ∃ x ∈ E, w * x ≠ x * w)
    {e : G} (heE : e ∈ E) (he5 : orderOf e = 5) (heW : ∀ w ∈ W, w * e = e * w) : False := by
  haveI : (E.subgroupOf (normalizer (E : Set G))).Normal := normal_in_normalizer
  refine false_of_autModel_aux hM hP (E.subgroupOf (normalizer (E : Set G)))
    ((subgroupOfEquivOfLe le_normalizer).trans θ) (W := W.subgroupOf (normalizer (E : Set G)))
    ?_ ?_ ⟨⟨e, le_normalizer heE⟩, mem_subgroupOf.2 heE⟩ ((Subgroup.orderOf_mk e _).trans he5) ?_
  · rw [← hWc]
    exact Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv
  · intro w hw hw1
    obtain ⟨x, hx, hxw⟩ := hfaith w (mem_subgroupOf.1 hw) fun h => hw1 (Subtype.ext h)
    exact ⟨⟨x, le_normalizer hx⟩, mem_subgroupOf.2 hx, fun h => hxw (congrArg Subtype.val h)⟩
  · intro w hw
    exact Subtype.ext (heW w (mem_subgroupOf.1 hw))

end Model

theorem card_centralizer_hs100R_of_five {x : Equiv.Perm (Fin 100)} (hxP : x ∈ hs100P)
    (hx : orderOf x = 5) :
    Nat.card ↥(centralizer ({x} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) = 50 ∨
      Nat.card ↥(centralizer ({x} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) = 600 ∨
      Nat.card ↥(centralizer ({x} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) = 1000 := by
  classical
  obtain ⟨-, ⟨hlines, -⟩, htrans, hrecmem, -, hC0, hC2, hC23, -⟩ :=
    R3E_HS_full_five_centralizer_structures
  obtain ⟨g, hgP, hgx⟩ := exists_conj_mem_hs100FiveQ hxP hx
  have hgR : g ∈ hs100R := hs100P_le_R hgP
  set y : Equiv.Perm (Fin 100) := g * x * g⁻¹ with hy
  have hyord : orderOf y = 5 := by
    rw [hy, ← hx]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  have hzin : zpowers y ∈ {H : Subgroup (Equiv.Perm (Fin 100)) | H ≤ hs100FiveQ ∧
      Nat.card H = 5} :=
    ⟨zpowers_le.2 hgx, by rw [Nat.card_zpowers, hyord]⟩
  rw [hlines] at hzin
  obtain ⟨j, hj⟩ := hzin
  obtain ⟨e1⟩ := centralizer_inf_equiv_of_conj hs100R hgR (rfl : g * x * g⁻¹ = y)
  have e2 := centralizer_inf_eq_of_zpowers_eq hs100R hj.symm
  obtain ⟨hRj, hconj⟩ := htrans j
  obtain ⟨e3⟩ := centralizer_inf_equiv_of_conj hs100R hRj hconj
  have hcard : Nat.card ↥(centralizer ({x} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) =
      Nat.card ↥(centralizer ({hs100FiveLine (hs100FiveRecordOf j)} :
        Set (Equiv.Perm (Fin 100))) ⊓ hs100R) := by
    rw [Nat.card_congr e1.toEquiv]
    have : Nat.card ↥(centralizer ({y} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) =
        Nat.card ↥(centralizer ({hs100FiveLine j} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) := by
      rw [← e2]
    rw [this]
    exact (Nat.card_congr e3.toEquiv).symm
  rw [hcard]
  have hm := hrecmem j
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm
  · left
    rw [show hs100FiveRecordOf j = 0 from Fin.ext hm, ← hC0.1]
    exact hC0.2
  · right; left
    rw [show hs100FiveRecordOf j = 2 from Fin.ext hm, ← hC2.1]
    exact hC2.2
  · right; right
    rw [show hs100FiveRecordOf j = 23 from Fin.ext hm, ← hC23.1]
    exact hC23.2

end CFSG.LocalAnalysis.GLTheoremA.H1017
