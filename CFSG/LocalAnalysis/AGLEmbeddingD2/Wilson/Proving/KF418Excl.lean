module

public import CFSG.RankThree.Native.ONThreeFusion
public import CFSG.RankThree.Native.ONThreeCentralizer
public import CFSG.Sporadic.Recognition.McLASCert

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup

@[expose] def KF418Excl (S : Type*) [Group S] : Prop :=
  ∀ y : S, orderOf y = 3 →
    ¬ (3 ^ 4 ∣ Nat.card (Subgroup.centralizer ({y} : Set S)) ∧
      7 ∣ Nat.card (Subgroup.centralizer ({y} : Set S)))

theorem card_centralizer_mulEquiv_eq {S T : Type*} [Group S] [Group T] (e : S ≃* T) (y : S) :
    Nat.card (Subgroup.centralizer ({y} : Set S)) =
      Nat.card (Subgroup.centralizer ({e y} : Set T)) := by
  have hmap : (Subgroup.centralizer ({y} : Set S)).map e.toMonoidHom =
      Subgroup.centralizer ({e y} : Set T) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      change e z * e y = e y * e z
      rw [← map_mul, ← map_mul, hz']
    · intro hw
      refine ⟨e.symm w, ?_, by simp⟩
      show e.symm w ∈ Subgroup.centralizer ({y} : Set S)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_centralizer_singleton_iff.mp hw
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]

theorem KF418Excl.of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : KF418Excl T) : KF418Excl S := by
  intro y hy hbad
  have h3 : orderOf (e y) = 3 := (orderOf_injective e.toMonoidHom e.injective y).trans hy
  apply h (e y) h3
  rw [← card_centralizer_mulEquiv_eq e y]
  exact hbad

theorem kF418Excl_of_card {S : Type*} [Group S] [Finite S]
    (h : ¬ 3 ^ 4 ∣ Nat.card S ∨ ¬ 7 ∣ Nat.card S) : KF418Excl S := by
  intro y _ hbad
  have hd := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({y} : Set S))
  rcases h with h | h
  · exact h (dvd_trans hbad.1 hd)
  · exact h (dvd_trans hbad.2 hd)

theorem card_inf_centralizer_conj {G : Type*} [Group G] (P : Subgroup G) (g t : G)
    (hg : g ∈ P) :
    Nat.card ↥(P ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G)) =
      Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have hmap : (P ⊓ Subgroup.centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      P ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨x, ⟨hxP, hxC⟩, rfl⟩
      refine ⟨P.mul_mem (P.mul_mem hg hxP) (P.inv_mem hg), ?_⟩
      calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
        _ = g * (t * x) * g⁻¹ := by rw [hxC]
        _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group
    · rintro ⟨hwP, hwC⟩
      refine ⟨g⁻¹ * w * g, ⟨P.mul_mem (P.mul_mem (P.inv_mem hg) hwP) hg, ?_⟩, by group⟩
      have h1 : g⁻¹ * (w * (g * t * g⁻¹)) * g = g⁻¹ * ((g * t * g⁻¹) * w) * g := by rw [hwC]
      calc g⁻¹ * w * g * t = g⁻¹ * (w * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * w) * g := h1
        _ = t * (g⁻¹ * w * g) := by group
  rw [← hmap, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]

theorem kF418Excl_on :
    KF418Excl CFSG.Blueprint.NativeSporadic.ON := by
  intro y hy hbad
  obtain ⟨k, hk⟩ := CFSG.RankThree.Native.onThree_fusion
    (CFSG.RankThree.Native.orderOf_onThreeElt) hy
  have hc : Nat.card (Subgroup.centralizer ({CFSG.RankThree.Native.onThreeElt} :
      Set CFSG.Blueprint.NativeSporadic.ON)) =
      Nat.card (Subgroup.centralizer ({k * CFSG.RankThree.Native.onThreeElt * k⁻¹} :
        Set CFSG.Blueprint.NativeSporadic.ON)) :=
    card_centralizer_mulEquiv_eq (MulAut.conj k) CFSG.RankThree.Native.onThreeElt
  rw [← hk, ← hc, CFSG.RankThree.Native.card_centralizer_onThreeElt] at hbad
  norm_num at hbad

theorem perm_fin_orderOf_ne_21 {n : ℕ} (hn : n ≤ 9) (σ : Equiv.Perm (Fin n)) :
    orderOf σ ≠ 21 := by
  intro h
  have hlcm : σ.cycleType.lcm = 21 := by rw [Equiv.Perm.lcm_cycleType, h]
  have hsum : σ.cycleType.sum = σ.support.card := Equiv.Perm.sum_cycleType σ
  have hcard : σ.support.card ≤ n := by
    simpa using Finset.card_le_univ σ.support
  have hdiv : ∀ a ∈ σ.cycleType, a ∣ 21 := fun a ha => hlcm ▸ Multiset.dvd_lcm ha
  have hle : ∀ a ∈ σ.cycleType, a ≤ 9 := fun a ha => by
    have := Multiset.le_sum_of_mem ha
    omega
  have hmem : ∀ a ∈ σ.cycleType, a = 3 ∨ a = 7 := by
    intro a ha
    have h2 := Equiv.Perm.two_le_of_mem_cycleType ha
    have hd := hdiv a ha
    have hl := hle a ha
    interval_cases a <;> omega
  have h3 : 3 ∈ σ.cycleType := by
    by_contra h3
    have hl : σ.cycleType.lcm ∣ 7 := Multiset.lcm_dvd.mpr (fun a ha => by
      rcases hmem a ha with rfl | rfl
      · exact absurd ha h3
      · norm_num)
    rw [hlcm] at hl
    norm_num at hl
  have h7 : 7 ∈ σ.cycleType := by
    by_contra h7
    have hl : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.mpr (fun a ha => by
      rcases hmem a ha with rfl | rfl
      · norm_num
      · exact absurd ha h7)
    rw [hlcm] at hl
    norm_num at hl
  have hs : σ.cycleType.sum = 3 + (σ.cycleType.erase 3).sum := by
    rw [← Multiset.sum_cons, Multiset.cons_erase h3]
  have h7' : 7 ∈ σ.cycleType.erase 3 := (Multiset.mem_erase_of_ne (by norm_num)).2 h7
  have := Multiset.le_sum_of_mem h7'
  omega

theorem kF418Excl_alternatingGroup {n : ℕ} (hn : n ≤ 9) :
    KF418Excl (alternatingGroup (Fin n)) := by
  intro y hy hbad
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin n))))) 7 hbad.2
  have hzc : (x : alternatingGroup (Fin n)) ∈ Subgroup.centralizer ({y} : Set _) := x.2
  have hcomm : Commute y (x : alternatingGroup (Fin n)) :=
    (Subgroup.mem_centralizer_singleton_iff.mp hzc).symm
  have hx7 : orderOf (x : alternatingGroup (Fin n)) = 7 := (Subgroup.orderOf_coe x).trans hx
  have hord : orderOf (y * (x : alternatingGroup (Fin n))) = 21 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hy, hx7]; norm_num), hy, hx7]
  refine perm_fin_orderOf_ne_21 hn
    ((y : Equiv.Perm (Fin n)) * ((x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) ?_
  rw [← Subgroup.coe_mul, Subgroup.orderOf_coe, hord]

theorem kF418Excl_mclP :
    KF418Excl ↥CFSG.Sporadic.Schreier.mclP := by
  obtain ⟨-, -, -, -, h29160, h972, -, -, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mclP_order_three_classes
      CFSG.Sporadic.Recognition.McLAS.threeFacts_cert
  intro y hy hbad
  have hord : orderOf (y : Equiv.Perm (Fin 275)) = 3 := (Subgroup.orderOf_coe y).trans hy
  have hcenter : Nat.card (Subgroup.centralizer ({y} : Set ↥CFSG.Sporadic.Schreier.mclP)) =
      Nat.card ↥(CFSG.Sporadic.Schreier.mclP ⊓
        Subgroup.centralizer ({(y : Equiv.Perm (Fin 275))} : Set (Equiv.Perm (Fin 275)))) := by
    rw [CFSG.RankThree.Native.card_centralizer_eq_inf_of_mulEquiv (MulEquiv.refl _) y, inf_comm]
    rfl
  rw [hcenter] at hbad
  rcases hall (y : Equiv.Perm (Fin 275)) y.2 hord with ⟨g, hg, hyg⟩ | ⟨g, hg, hyg⟩
  · rw [hyg, CFSG.AGLEmbeddingD2.Wilson.Proving.card_inf_centralizer_conj
      CFSG.Sporadic.Schreier.mclP g _ hg, h29160] at hbad
    norm_num at hbad
  · rw [hyg, CFSG.AGLEmbeddingD2.Wilson.Proving.card_inf_centralizer_conj
      CFSG.Sporadic.Schreier.mclP g _ hg, h972] at hbad
    norm_num at hbad

theorem kF418Excl_mcl :
    KF418Excl (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
  KF418Excl.of_mulEquiv CFSG.Sporadic.Schreier.mclPermEquiv kF418Excl_mclP

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
