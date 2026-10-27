module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714AltAut
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714AltPerm
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Ord
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.GHInv
open scoped Nat

theorem ivk714_alt_core {n : ℕ} (hn7 : 7 ≤ n) (hn11 : n ≤ 11) {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin n)) {z : MulAut K} (hz : orderOf z = 2) (h : Ivk714Hyp K z) :
    (n = 9 ∧ sign (altAutEquiv hn7 e z) = -1) ∨ (n = 11 ∧ sign (altAutEquiv hn7 e z) = 1) := by
  classical
  have hz2 : z * z = 1 := by
    rw [← sq, ← hz]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    omega
  set θ := altAutEquiv hn7 e with hθ
  set σ : Perm (Fin n) := θ z with hσ
  have hσ2 : σ * σ = 1 := by rw [hσ, ← map_mul, hz2, map_one]
  have hσ1 : σ ≠ 1 := fun h1 => hz1 (θ.injective (h1.trans (map_one θ).symm))
  obtain ⟨k, hk⟩ := involution_cycleType_replicate hσ2
  obtain ⟨hsupp, hsign⟩ := involution_support_sign hσ2 hk
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, mul_zero, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff] at hsupp
    exact hσ1 hsupp
  have h2k : 2 * k ≤ n := by
    have := Finset.card_le_univ σ.support
    rw [Fintype.card_fin] at this
    omega
  have hCcard : Nat.card ↥(fixedSubgroup K z) =
      Nat.card ↥(centralizer ({σ} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) := by
    rw [← fixedSubgroup_map_alt hn7 e z, Subgroup.card_map_of_injective (psiAlt_injective e)]
  have h7 : 7 ∣ (n - 2 * k)! * 2 ^ k * k ! := by
    rw [← card_centralizer_involution_perm hk hk1]
    have h2520 := h.two_five_two_zero_dvd
    rw [hCcard] at h2520
    exact ((by norm_num : 7 ∣ 2520).trans h2520).trans (Subgroup.card_dvd_of_le inf_le_left)
  have h7le := seven_le_sub hn11 h2k h7
  have hch : (layer ↥(fixedSubgroup K z)).Characteristic := LocalCores.layer_characteristic
  have hEn : (layer ↥(fixedSubgroup K z)).Normal := inferInstance
  have hEperf : Group.IsPerfect (layer ↥(fixedSubgroup K z)) := LocalCores.layer_isPerfect
  let ψC : ↥(fixedSubgroup K z) →* Perm (Fin n) := (psiAlt e).comp (fixedSubgroup K z).subtype
  have hψC : Function.Injective ψC :=
    (psiAlt_injective e).comp (fixedSubgroup K z).subtype_injective
  set P : Subgroup (Perm (Fin n)) := (layer ↥(fixedSubgroup K z)).map ψC with hPdef
  have hPperf : Group.IsPerfect P := Group.IsPerfect.map ψC
  have hPc : ∀ x ∈ P, x * σ = σ * x := by
    rintro x ⟨y, -, rfl⟩
    have hy' : z (y : K) = (y : K) := y.2
    have := altAutEquiv_spec hn7 e z (y : K)
    rw [hy'] at this
    show psiAlt e (y : K) * σ = σ * psiAlt e (y : K)
    calc psiAlt e (y : K) * σ = σ * psiAlt e (y : K) * σ⁻¹ * σ := by rw [← this]
      _ = σ * psiAlt e (y : K) := by group
  have hPA : P ≤ alternatingGroup (Fin n) := by
    rintro x ⟨y, -, rfl⟩
    exact psiAlt_mem e _
  have hPn : ∀ g ∈ altOn σ.supportᶜ, ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hx
    have hgC : g ∈ centralizer ({σ} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) :=
      altOn_support_compl_le σ hg
    rw [← fixedSubgroup_map_alt hn7 e z] at hgC
    obtain ⟨c, hc, rfl⟩ := hgC
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, hEn.conj_mem y hy ⟨c, hc⟩, ?_⟩
    simp [ψC]
  obtain ⟨o, ho, hEo⟩ := h.card_layer_eq
  have hPcard : Nat.card ↥P = Nat.card ↥(layer ↥(fixedSubgroup K z)) :=
    Subgroup.card_map_of_injective hψC
  have hP1 : P ≠ ⊥ := by
    intro hP0
    rw [hP0, Subgroup.card_bot, hEo] at hPcard
    have := ho.pos
    omega
  have hPeq : P = altOn σ.supportᶜ :=
    eq_altOn_of_perfect hσ2 hk (by omega) (by omega) hPperf hPA hPc hPn hP1
  have hval : (n - 2 * k)! / 2 = 2520 * o := by
    rw [← hEo, ← hPcard, hPeq, card_altOn_support_compl hσ2 hk (by omega)]
  obtain ⟨r, hr⟩ := ho
  have hm : n - 2 * k = 7 := by
    have hm' : n - 2 * k = 7 ∨ n - 2 * k = 8 ∨ n - 2 * k = 9 := by omega
    rcases hm' with hm' | hm' | hm'
    · exact hm'
    · rw [hm'] at hval
      have : (8 : ℕ)! / 2 = 20160 := by decide
      omega
    · rw [hm'] at hval
      have : (9 : ℕ)! / 2 = 181440 := by decide
      omega
  rcases (by omega : (n = 9 ∧ k = 1) ∨ (n = 11 ∧ k = 2)) with ⟨hn9, hk1'⟩ | ⟨hn11', hk2'⟩
  · left
    exact ⟨hn9, by rw [hsign, hk1']; norm_num⟩
  · right
    exact ⟨hn11', by rw [hsign, hk2']; norm_num⟩

theorem ivk714_alt_nine {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 9)) {z : MulAut K}
    (hs : sign (altAutEquiv (by norm_num : 7 ≤ 9) e z) = -1) :
    Nonempty (↥(kz K z) ≃* Perm (Fin 9)) ∧ 2 ^ 7 ∣ Nat.card ↥(kz K z) := by
  set θ := altAutEquiv (by norm_num : 7 ≤ 9) e with hθ
  have hmap : (kz K z).map θ.toMonoidHom = ⊤ := by
    rw [kz, Subgroup.map_sup, innAut_map_alt, MonoidHom.map_zpowers]
    rw [eq_top_iff]
    intro g _
    by_cases hg : sign g = 1
    · exact Subgroup.mem_sup_left (Equiv.Perm.mem_alternatingGroup.2 hg)
    · have hg' : sign g = -1 := by
        rcases Int.units_eq_one_or (sign g) with h1 | h1
        · exact absurd h1 hg
        · exact h1
      have hA : g * (θ z)⁻¹ ∈ alternatingGroup (Fin 9) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs, hg']
        decide
      have h2 : g = (g * (θ z)⁻¹) * θ z := by group
      rw [h2]
      exact Subgroup.mul_mem_sup hA (Subgroup.mem_zpowers _)
  let e1 : ↥(kz K z) ≃* Perm (Fin 9) :=
    (Subgroup.equivMapOfInjective (kz K z) θ.toMonoidHom θ.injective).trans
      ((MulEquiv.subgroupCongr hmap).trans Subgroup.topEquiv)
  refine ⟨⟨e1⟩, ?_⟩
  rw [Nat.card_congr e1.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem ivk714_alt_eleven {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 11)) {z : MulAut K}
    (hs : sign (altAutEquiv (by norm_num : 7 ≤ 11) e z) = 1) : 2 ^ 7 ∣ Nat.card ↥(kz K z) := by
  have hn : 7 ≤ 11 := by norm_num
  have hmem : z ∈ innAut K := by
    have hA : altAutEquiv hn e z ∈ alternatingGroup (Fin 11) := Equiv.Perm.mem_alternatingGroup.2 hs
    refine ⟨e.symm ⟨altAutEquiv hn e z, hA⟩, ?_⟩
    apply (altAutEquiv hn e).injective
    have := altAutEquiv_conj hn e (e.symm ⟨altAutEquiv hn e z, hA⟩)
    show altAutEquiv hn e (MulAut.conj (e.symm ⟨altAutEquiv hn e z, hA⟩)) = altAutEquiv hn e z
    rw [this]
    simp [psiAlt]
  have hkz : kz K z = innAut K := by
    rw [kz, sup_eq_left, Subgroup.zpowers_le]
    exact hmem
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    intro a b hab
    apply psiAlt_injective e
    rw [← altAutEquiv_conj hn e a, ← altAutEquiv_conj hn e b, hab]
  rw [hkz]
  have hc : Nat.card ↥(innAut K) = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [hc, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem ivk714_alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 →
    Ivk714Fam (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n))) := by
  intro n hn7 hn11 K _ _ _ hK z hz h
  obtain ⟨e⟩ := hK
  rcases ivk714_alt_core hn7 hn11 e hz h with ⟨hn9, hs⟩ | ⟨hn11', hs⟩
  · subst hn9
    obtain ⟨h1, h2⟩ := ivk714_alt_nine e hs
    exact ⟨Or.inl h1, h2⟩
  · subst hn11'
    exact ⟨Or.inr ⟨11, le_rfl, ⟨e⟩⟩, ivk714_alt_eleven e hs⟩

end CFSG.GH74.GLS.IVK.Proofs2
