module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open

theorem exists_elemAbelian_le_of_mulEquiv {G M : Type*} [Group G] [Group M] {J : Subgroup G}
    {P T : Subgroup M} (e : ↥J ≃* ↥P) (hTP : T ≤ P) {q m : ℕ} (hT : IsElemAbelian q T)
    (hTc : Nat.card T = q ^ m) :
    ∃ F₀ : Subgroup G, F₀ ≤ J ∧ IsElemAbelian q F₀ ∧ Nat.card F₀ = q ^ m := by
  refine ⟨((T.subgroupOf P).map e.symm.toMonoidHom).map J.subtype, Subgroup.map_subtype_le _,
    ?_, ?_⟩
  · exact IsElemAbelian.map (IsElemAbelian.map (hT.subgroupOf P) e.symm.toMonoidHom) J.subtype
  · rw [Subgroup.card_map_of_injective J.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv, hTc]

theorem exists_noncentral_of_elemAbelian {G : Type*} [Group G] {J T : Subgroup G} (hTJ : T ≤ J)
    {q : ℕ} (hq : q.Prime) (hT : IsElemAbelian q T) (hTc : Nat.card T = q ^ 2)
    (hZ : Nat.card (Subgroup.center ↥J) ∣ 3) :
    ∃ (s₀ : G) (hs₀ : s₀ ∈ J), orderOf s₀ = q ∧
      (⟨s₀, hs₀⟩ : ↥J) ∉ Subgroup.center ↥J := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hpos : 0 < Nat.card ↥(Subgroup.center ↥J) := Nat.pos_of_dvd_of_pos hZ (by norm_num)
  haveI : Finite ↥(Subgroup.center ↥J) := Nat.finite_of_card_ne_zero hpos.ne'
  have hnotle : ¬ T.subgroupOf J ≤ Subgroup.center ↥J := by
    intro hle
    have h1 : Nat.card ↥(T.subgroupOf J) ≤ Nat.card ↥(Subgroup.center ↥J) :=
      Subgroup.card_le_of_le hle
    have h2 : Nat.card ↥(T.subgroupOf J) = q ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv, hTc]
    have h3 : Nat.card ↥(Subgroup.center ↥J) ≤ 3 := Nat.le_of_dvd (by norm_num) hZ
    rw [h2] at h1
    nlinarith [hq.two_le]
  obtain ⟨s, hsT, hsZ⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hs1 : s ≠ 1 := fun h => hsZ (h ▸ Subgroup.one_mem _)
  have hsq' : s ^ q = 1 := (hT.subgroupOf J).2 s hsT
  have hsq : orderOf s = q := orderOf_eq_prime hsq' hs1
  exact ⟨(s : G), s.2, by rwa [Subgroup.orderOf_coe], hsZ⟩

theorem map_comap_commute {K M : Type*} [Group K] [Group M] {C : Subgroup K} {ψ : ↥C →* M}
    (hψ : Function.Injective ψ) {P Q : Subgroup M} (hPQ : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) :
    ∀ a ∈ (P.comap ψ).map C.subtype, ∀ b ∈ (Q.comap ψ).map C.subtype, Commute a b := by
  rintro a ⟨y, hyP, rfl⟩ b ⟨z, hzQ, rfl⟩
  have h1 : ψ (y * z) = ψ (z * y) := by
    rw [map_mul, map_mul, hPQ _ (Subgroup.mem_comap.mp hyP) _ (Subgroup.mem_comap.mp hzQ)]
  exact congrArg Subtype.val (hψ h1)

@[expose] noncomputable def comapMapMulEquiv {K M : Type*} [Group K] [Group M] {C : Subgroup K}
    {ψ : ↥C →* M} (hψ : Function.Injective ψ) {P : Subgroup M} (hP : P ≤ ψ.range) :
    ↥((P.comap ψ).map C.subtype) ≃* ↥P :=
  (Subgroup.equivMapOfInjective (P.comap ψ) C.subtype C.subtype_injective).symm.trans
    ((Subgroup.equivMapOfInjective (P.comap ψ) ψ hψ).trans
      (MulEquiv.subgroupCongr (by rw [Subgroup.map_comap_eq, inf_of_le_right hP])))

end CFSG.LocalAnalysis.GLTheoremA.Y10F
