module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20SporGrp
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20SporOrd
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Tools

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def Fi22FiveCentBig : Prop :=
  ∀ s : TauCeti.SporadicName, (s = .Co1 ∨ s = .B ∨ s = .M) →
    ∀ x : (TauCeti.CFSGIndex.sporadic s).Group, x ^ 5 = 1 → x ≠ 1 →
      ¬ Fi22Cfg (TauCeti.CFSGIndex.sporadic s).Group (MulAut.conj x)

theorem fixedSub_conj {S : Type} [Group S] (x : S) :
    fixedSub (MulAut.conj x) = Subgroup.centralizer ({x} : Set S) := by
  ext a
  rw [mem_fixedSub, Subgroup.mem_centralizer_singleton_iff]
  show x * a * x⁻¹ = a ↔ _
  rw [mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem exists_conj_of_pow_five {S : Type} [Group S] (hOut : ¬ 5 ∣ Nat.card (Outer S))
    {α : MulAut S} (h5 : α ^ 5 = 1) : ∃ a : S, MulAut.conj a = α := by
  have h5' : (QuotientGroup.mk α : Outer S) ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow, h5]
    rfl
  have hd5 := orderOf_dvd_of_pow_eq_one h5'
  rcases (Nat.dvd_prime (by norm_num)).1 hd5 with h1 | h5o
  · rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exact absurd (h5o ▸ orderOf_dvd_natCard _) hOut

theorem center_eq_bot_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

section Certificates


theorem noFi22Cfg_sporadic
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hBig : Fi22FiveCentBig)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (s : TauCeti.SporadicName) (e : S ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (α : MulAut S) (h5 : α ^ 5 = 1) (h1 : α ≠ 1) : ¬ Fi22Cfg S α := by
  intro hcfg
  obtain ⟨hsimple, hcard⟩ := fi22_facts
  have hcenFi : Subgroup.center Fi22G = ⊥ := by
    have := hsimple
    exact center_eq_bot_of_simple (by
      by_contra hc
      push Not at hc
      have hcomm : ∀ a b : Fi22G, a * b = b * a := hc
      have hprime := @IsSimpleGroup.prime_card _ ⟨fun a b => hcomm a b⟩ hsimple
      rw [hcard] at hprime
      exact absurd hprime (by norm_num))
  have hOutSs : ¬ 5 ∣ Nat.card (Outer S) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact hOutS s 5 (by norm_num) (by norm_num)
  obtain ⟨x, hx⟩ := exists_conj_of_pow_five hOutSs h5
  have hZ := center_eq_bot_of_simple hnab
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact h1 (hx.symm.trans (map_one _))
  have hx5 : x ^ 5 = 1 := by
    have : MulAut.conj (x ^ 5) = 1 := by rw [map_pow, hx, h5]
    have hmem : x ^ 5 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun β : MulAut S => β g) this
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  by_cases hbigs : s = .Co1 ∨ s = .B ∨ s = .M
  ·
    have hcfg' := Fi22Cfg.of_mulEquiv e hcfg
    have hx' : MulAut.congr e α = MulAut.conj (e x) := by
      rw [← hx]
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    rw [hx'] at hcfg'
    refine hBig s hbigs (e x) ?_ ?_ hcfg'
    · rw [← map_pow, hx5, map_one]
    · intro h
      exact hx1 (e.injective (h.trans (map_one e).symm))
  · push Not at hbigs
    obtain ⟨H, hH, N, hN, hc, ⟨φ⟩⟩ := hcfg
    have hHx : H ≤ Subgroup.centralizer ({x} : Set S) := by
      have := le_of_isSubnormal' hH
      rw [← hx, fixedSub_conj] at this
      exact this
    have hdvd := five_mul_card_dvd hcenFi hx5 hx1 hHx N hc φ
    rw [hcard] at hdvd
    obtain ⟨b⟩ := hbr s
    have hd2 : 5 * 64561751654400 ∣ Nat.card (NativeSporadic.Carrier s) := by
      rw [Nat.card_congr (b.toEquiv.trans e.symm.toEquiv)]
      exact hdvd
    exact not_five_mul_dvd_card_carrier s hbigs hd2

end Certificates

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
