module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Perm

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open Subgroup CFSG.Open

theorem not_sq_dvd_factorial {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ∣ p.factorial := by
  intro h
  have h1 : p * (p - 1).factorial = p.factorial := Nat.mul_factorial_pred hp.ne_zero
  rw [← h1, sq] at h
  have h2 : p ∣ (p - 1).factorial := Nat.dvd_of_mul_dvd_mul_left hp.pos h
  have h3 := (hp.dvd_factorial).1 h2
  have h4 := hp.pos
  omega

theorem injective_of_surjective_perm {p : ℕ} (hp : p.Prime) {S : Type*} [Group S] [Finite S]
    (hdvd : p ∣ Nat.card S) {V : Subgroup (Equiv.Perm (Fin p))} (f : V →* S)
    (hf : Function.Surjective f) : Function.Injective f := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  have hVcard : Nat.card V = Nat.card S * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hVdvd : Nat.card V ∣ p.factorial := by
    have h1 := Subgroup.card_subgroup_dvd_card V
    have h2 : Nat.card (Equiv.Perm (Fin p)) = p.factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rwa [h2] at h1
  have hcop : p.Coprime (Nat.card f.ker) := by
    rw [hp.coprime_iff_not_dvd]
    intro hk
    apply not_sq_dvd_factorial hp
    have : p ^ 2 ∣ Nat.card V := by
      rw [hVcard, sq]
      exact mul_dvd_mul hdvd hk
    exact this.trans hVdvd
  have hpV : p ∣ Nat.card V := hdvd.trans (hVcard ▸ dvd_mul_right _ _)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := V) p hpV
  have hc'ord : orderOf (c : Equiv.Perm (Fin p)) = p := (Subgroup.orderOf_coe c).trans hc
  have hc'1 : (c : Equiv.Perm (Fin p)) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc'ord
    exact hp.one_lt.ne hc'ord
  have hc'p : (c : Equiv.Perm (Fin p)) ^ p = 1 := by
    have h1 := pow_orderOf_eq_one (c : Equiv.Perm (Fin p))
    rwa [hc'ord] at h1
  have hcN : c ∈ normalizer (f.ker : Set V) :=
    (le_normalizer_of_normal : (⊤ : Subgroup V) ≤ normalizer (f.ker : Set V)) (Subgroup.mem_top c)
  have hkernel : f.ker.map V.subtype = ⊥ := by
    refine eq_bot_of_pCycle_mem_normalizer hp (Fintype.card_fin p) hc'1 hc'p ?_ ?_
    · rw [Subgroup.card_map_of_injective V.subtype_injective]
      exact hcop
    · exact Subgroup.le_normalizer_map V.subtype ⟨c, hcN, rfl⟩
  exact (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).1 hkernel

theorem center_eq_bot_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ center S := by rw [h]; exact Subgroup.mem_top a
    exact hab (mem_center_iff.1 this b).symm

theorem conj_injective_of_center_eq_bot {S : Type*} [Group S] (hc : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro s t h
  have h1 : t⁻¹ * s ∈ center S := by
    rw [mem_center_iff]
    intro g
    have := congrArg (fun a : MulAut S => a g) h
    simp only [MulAut.conj_apply] at this
    calc g * (t⁻¹ * s) = t⁻¹ * (t * g * t⁻¹) * s := by group
      _ = t⁻¹ * (s * g * s⁻¹) * s := by rw [this]
      _ = t⁻¹ * s * g := by group
  rw [hc, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact h1.symm

theorem GL83I203Sigma_of_centralizer (h : SigmaCentralizerPGroup) : GL83I203Sigma := by
  intro p hp h5 S _ _ _ hnab hcat hdvd hinv x hx A hAcop hAnorm
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, f, hf⟩ := hinv
  have hfinj := injective_of_surjective_perm hp hdvd f hf
  let e : V ≃* S := MulEquiv.ofBijective f ⟨hfinj, hf⟩
  have hconjinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot (center_eq_bot_of_simple hnab)
  let A' : Subgroup S := A.comap (MulAut.conj : S →* MulAut S)
  have hA'cop : p.Coprime (Nat.card A') := by
    have h1 : Nat.card A' ∣ Nat.card A := Subgroup.card_dvd_of_injective
      ((MulAut.conj : S →* MulAut S).subgroupComap A) (fun a b hab => Subtype.ext (hconjinj
        (congrArg Subtype.val hab)))
    exact hAcop.coprime_dvd_right h1
  have hxA' : x ∈ normalizer (A' : Set S) := by
    rw [mem_normalizer_iff]
    intro a
    have hconj : (MulAut.conj (x * a * x⁻¹) : MulAut S) =
        MulAut.conj x * MulAut.conj a * (MulAut.conj x)⁻¹ := by
      simp [map_mul, map_inv]
    show MulAut.conj a ∈ A ↔ MulAut.conj (x * a * x⁻¹) ∈ A
    rw [hconj]
    exact mem_normalizer_iff.1 hAnorm (MulAut.conj a)
  have hA'bot : A' = ⊥ := by
    let B : Subgroup (Equiv.Perm (Fin p)) := (A'.map e.symm.toMonoidHom).map V.subtype
    have hc'ord : orderOf (((e.symm x : V)) : Equiv.Perm (Fin p)) = p := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hx
    have hc'1 : (((e.symm x : V)) : Equiv.Perm (Fin p)) ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hc'ord
      exact hp.one_lt.ne hc'ord
    have hc'p : (((e.symm x : V)) : Equiv.Perm (Fin p)) ^ p = 1 := by
      have h1 := pow_orderOf_eq_one (((e.symm x : V)) : Equiv.Perm (Fin p))
      rwa [hc'ord] at h1
    have hBcop : p.Coprime (Nat.card B) := by
      rw [Subgroup.card_map_of_injective V.subtype_injective,
        Subgroup.card_map_of_injective e.symm.injective]
      exact hA'cop
    have hBnorm : (((e.symm x : V)) : Equiv.Perm (Fin p)) ∈ normalizer (B : Set _) := by
      have h1 : e.symm.toMonoidHom x ∈
          normalizer ((A'.map e.symm.toMonoidHom : Subgroup V) : Set V) :=
        Subgroup.le_normalizer_map e.symm.toMonoidHom ⟨x, hxA', rfl⟩
      exact Subgroup.le_normalizer_map V.subtype ⟨e.symm x, h1, rfl⟩
    have hB := eq_bot_of_pCycle_mem_normalizer hp (Fintype.card_fin p) hc'1 hc'p hBcop hBnorm
    have h2 := (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).1 hB
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1 h2
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have hax : a x = x := by
    have h1 : MulAut.conj x * a⁻¹ * (MulAut.conj x)⁻¹ ∈ A :=
      (mem_normalizer_iff.1 hAnorm a⁻¹).1 (A.inv_mem ha)
    have h2 : a * (MulAut.conj x * a⁻¹ * (MulAut.conj x)⁻¹) ∈ A := A.mul_mem ha h1
    have h3 : a * (MulAut.conj x * a⁻¹ * (MulAut.conj x)⁻¹) = MulAut.conj (a x * x⁻¹) := by
      refine MulEquiv.ext fun s => ?_
      simp [MulAut.conj_apply]
    have h4 : a x * x⁻¹ ∈ A' := by
      show MulAut.conj (a x * x⁻¹) ∈ A
      rw [← h3]
      exact h2
    rw [hA'bot, Subgroup.mem_bot] at h4
    exact mul_inv_eq_one.1 h4
  have hord : p.Coprime (orderOf a) := by
    have h1 : orderOf (⟨a, ha⟩ : A) ∣ Nat.card A := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hAcop.coprime_dvd_right h1
  exact h p hp h5 S hnab hcat hdvd ⟨V, f, hf⟩ x hx a hord hax

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
