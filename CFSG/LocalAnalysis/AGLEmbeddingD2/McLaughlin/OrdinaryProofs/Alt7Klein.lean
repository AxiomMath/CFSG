module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A7PrimeOrderCentralizer
public import Mathlib.Combinatorics.Matroid.Init

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

set_option maxRecDepth 100000 in
theorem perm7_even_involution_fix_card :
    ∀ σ : Equiv.Perm (Fin 7), σ * σ = 1 → Equiv.Perm.sign σ = 1 → σ ≠ 1 →
      (Finset.univ.filter (fun i => σ i = i)).card = 3 := by
  decide +kernel

theorem alt7_involution_fix_card (x : alternatingGroup (Fin 7)) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) :
    (Finset.univ.filter (fun i => (x : Equiv.Perm (Fin 7)) i = i)).card = 3 := by
  apply perm7_even_involution_fix_card
  · rw [← Subgroup.coe_mul, ← pow_two, hx2, Subgroup.coe_one]
  · exact Equiv.Perm.mem_alternatingGroup.mp x.2
  · intro h
    apply hx1
    exact Subtype.ext (by rw [Subgroup.coe_one]; exact h)

theorem card_dvd_sum_fixedBy_card {G X : Type} [Group G] [Fintype G] [Fintype X]
    [DecidableEq X] [MulAction G X] :
    Fintype.card G ∣ ∑ g : G, (Finset.univ.filter (fun x : X => g • x = x)).card := by
  classical
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := G) (X := X)
  have hfix : ∀ g : G, (Finset.univ.filter (fun x : X => g • x = x)).card
      = Fintype.card (MulAction.fixedBy X g) := by
    intro g
    rw [Fintype.card_subtype]
    rfl
  simp only [hfix]
  rw [h]
  exact dvd_mul_left _ _

theorem alt7_elemAbelian_card_le {R : Subgroup (alternatingGroup (Fin 7))}
    (h2 : ∀ a ∈ R, a ^ 2 = 1) : Nat.card R ≤ 4 := by
  classical
  let _ : Fintype R := Fintype.ofFinite R
  let _ : MulAction R (Fin 7) :=
    MulAction.compHom (Fin 7) ((alternatingGroup (Fin 7)).subtype.comp R.subtype)
  have hact : ∀ (a : R) (i : Fin 7), a • i = ((a : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) i :=
    fun _ _ => rfl
  have hfix : ∀ a : R, (Finset.univ.filter (fun i : Fin 7 => a • i = i)).card
      = if a = 1 then 7 else 3 := by
    intro a
    by_cases ha : a = 1
    · subst ha
      simp
    · rw [if_neg ha]
      have hx2 : (a : alternatingGroup (Fin 7)) ^ 2 = 1 := h2 a a.2
      have hx1 : (a : alternatingGroup (Fin 7)) ≠ 1 := fun h => ha (Subtype.ext h)
      have := alt7_involution_fix_card _ hx2 hx1
      simpa only [hact] using this
  have hdvd := card_dvd_sum_fixedBy_card (G := R) (X := Fin 7)
  simp only [hfix] at hdvd
  have hsum : ∑ a : R, (if a = 1 then 7 else 3) = 3 * Fintype.card R + 4 := by
    have hrw : ∀ a : R, (if a = 1 then 7 else 3) = 3 + (if a = 1 then 4 else 0) := by
      intro a
      split_ifs <;> norm_num
    simp only [hrw, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hsum] at hdvd
  have h4 : Fintype.card R ∣ 4 := (Nat.dvd_add_right (dvd_mul_left _ _)).mp hdvd
  rw [Nat.card_eq_fintype_card]
  exact Nat.le_of_dvd (by norm_num) h4

theorem alt7_klein_normalizer {R : Subgroup (alternatingGroup (Fin 7))} (hR : Nat.card R = 4)
    (h2 : ∀ a ∈ R, a ^ 2 = 1)
    (h72 : 72 ≤ Nat.card (Subgroup.normalizer (R : Set (alternatingGroup (Fin 7))))) :
    ∃ E : Subgroup (alternatingGroup (Fin 7)),
      E ≤ Subgroup.normalizer (R : Set (alternatingGroup (Fin 7))) ∧ Nat.card E = 9 := by
  classical
  set N : Subgroup (alternatingGroup (Fin 7)) :=
    Subgroup.normalizer (R : Set (alternatingGroup (Fin 7))) with hNdef
  have hcent : ∀ p : ℕ, p.Prime → (p = 5 ∨ p = 7) → ¬ p ∣ Nat.card N := by
    intro p hp hp57 hdvd
    have : Fact p.Prime := ⟨hp⟩
    let _ : Fintype N := Fintype.ofFinite N
    have hdvdF : p ∣ Fintype.card N := by rw [← Nat.card_eq_fintype_card]; exact hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hdvdF
    let ψ : N →* Equiv.Perm R := (MulAut.toPerm R).comp (Subgroup.normalizerMonoidHom R)
    have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hpow : (ψ x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hdvd1 : orderOf (ψ x) ∣ p := orderOf_dvd_of_pow_eq_one hpow
    have hdvd2 : orderOf (ψ x) ∣ 24 := by
      have h := orderOf_dvd_natCard (ψ x)
      rw [Nat.card_perm, hR] at h
      have h24 : Nat.factorial 4 = 24 := rfl
      rw [h24] at h
      exact h
    have hgcd : Nat.gcd p 24 = 1 := by rcases hp57 with rfl | rfl <;> norm_num
    have hone : orderOf (ψ x) = 1 := by
      have := Nat.dvd_gcd hdvd1 hdvd2
      rw [hgcd] at this
      exact Nat.dvd_one.mp this
    have hψ1 : ψ x = 1 := orderOf_eq_one_iff.mp hone
    set g : alternatingGroup (Fin 7) := (x : alternatingGroup (Fin 7)) with hg
    have hconj : ∀ r ∈ R, g * r = r * g := by
      intro r hr
      have h1 : ((ψ x) ⟨r, hr⟩ : R) = ⟨r, hr⟩ := by rw [hψ1]; rfl
      have h3 : g * r * g⁻¹ = r := congrArg Subtype.val h1
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3
    have hord : orderOf g = p := by rw [hg]; exact (Subgroup.orderOf_coe x).trans hx
    have hg1 : g ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      exact hp.ne_one hord.symm
    have hnt : 1 < Nat.card R := by rw [hR]; norm_num
    have : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp hnt
    obtain ⟨t, ht⟩ := exists_ne (1 : R)
    have ht1 : (t : alternatingGroup (Fin 7)) ≠ 1 := fun h => ht (Subtype.ext h)
    have ht2 : (t : alternatingGroup (Fin 7)) ^ 2 = 1 := h2 t t.2
    have hPp : IsPGroup p (Subgroup.zpowers g) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    have hPne : Subgroup.zpowers g ≠ ⊥ := fun h => hg1 (Subgroup.zpowers_eq_bot.mp h)
    have hPcent : Subgroup.zpowers g ≤
        Subgroup.centralizer ({(t : alternatingGroup (Fin 7))} : Set (alternatingGroup (Fin 7))) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact (hconj _ t.2).symm
    exact CFSG.GorensteinWalter.aSeven_no_involution_centralizes_oddP_five_seven hp hp57
      (Subgroup.zpowers g) hPp hPne
      (show _ ∧ _ from ⟨ht1, ht2⟩) hPcent
  have hN : Nat.card N ∣ 72 := by
    have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      rfl
    have hdvdA : Nat.card N ∣ Nat.card (alternatingGroup (Fin 7)) :=
      Subgroup.card_subgroup_dvd_card N
    rw [hA] at hdvdA
    have h5 : Nat.Coprime 5 (Nat.card N) :=
      (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr
        (hcent 5 (by decide) (Or.inl rfl))
    have h7 : Nat.Coprime 7 (Nat.card N) :=
      (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr
        (hcent 7 (by decide) (Or.inr rfl))
    have hcop : Nat.Coprime (Nat.card N) (5 * 7) :=
      Nat.Coprime.mul_right h5.symm h7.symm
    have h2520 : Nat.card N ∣ 72 * (5 * 7) := by
      rw [show (72 : ℕ) * (5 * 7) = 2520 by norm_num]
      exact hdvdA
    exact hcop.dvd_of_dvd_mul_right h2520
  have hcardN : Nat.card N = 72 := by
    have := Nat.le_of_dvd (by norm_num) hN
    omega
  have hdiv9 : 3 ^ 2 ∣ Nat.card N := by rw [hcardN]; norm_num
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdiv9
  refine ⟨K.map N.subtype, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, _, rfl⟩ := Subgroup.mem_map.mp hy
    exact z.2
  · exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective N)).trans
      (hK.trans (by norm_num))

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
