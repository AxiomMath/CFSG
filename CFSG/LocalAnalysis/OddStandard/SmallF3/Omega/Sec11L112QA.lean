module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Q

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_exists_rep (v : Fin 6 → ZMod 2) :
    ∃ v' : Fin 6 → ZMod 2, (v' = v ∨ v' = v + (fun _ => 1)) ∧ v' 5 = 0 := by
  have hzm : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hzm (v 5) with h | h
  · exact ⟨v, Or.inl rfl, h⟩
  · refine ⟨v + (fun _ => 1), Or.inr rfl, ?_⟩
    simp only [Pi.add_apply, h]
    decide

theorem sec11_lam_add (c : Fin 5 → ZMod 2) (v w : Fin 6 → ZMod 2) :
    sec11Lam c (v + w) = sec11Lam c v + sec11Lam c w := by
  unfold sec11Lam
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

namespace Sec11Perm

variable {A M : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem rho_fix (h : Sec11Perm A M Alt φ) {q : G} (hq : q ∈ M) (k : Fin 6)
    (hc : q * φ (Pi.single k 1) = φ (Pi.single k 1) * q) : h.rho q k = k := by
  have h1 := h.conj_single hq k
  rw [hc, mul_inv_cancel_right] at h1
  exact (h.single_inj h1).symm

end Sec11Perm

theorem sec11_Q_structure [Finite G] {A M Q : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}
    (hm : Sec11Perm A M Alt φ) (hQM : Q ≤ M) (hQ32 : 32 ≤ Nat.card Q)
    (hQ0 : ∀ q ∈ Q, q * φ (Pi.single 0 1) = φ (Pi.single 0 1) * q)
    (hQ1 : ∀ q ∈ Q, q * φ (Pi.single 1 1) = φ (Pi.single 1 1) * q)
    (hQcomm : ∀ a ∈ Q, ∀ b ∈ Q,
      a * b * a⁻¹ * b⁻¹ ∈ zpowers (φ (Pi.single 0 1 + Pi.single 1 1)))
    (hz : φ (Pi.single 0 1 + Pi.single 1 1) ∈ Q)
    (hAQ : ∀ v, φ v ∈ Q → ∑ i, v i = 0)
    (hcen : ∀ q ∈ Q, hm.rho q = 1 → ∃ v, φ v = q)
    (hidx : ∀ v w, ∑ i, v i = 0 → ∑ i, w i = 0 → φ v ∉ Q → φ w ∉ Q → φ (v + w) ∈ Q) :
    (∀ v, φ v ∈ Q ↔ (∑ i, v i = 0 ∧ v 0 = v 1)) ∧
    (∀ q ∈ Q, ∃ s ∈ sec11V4, ∀ v, q * φ v * q⁻¹ = φ (permVec s v)) ∧
    (∀ s ∈ sec11V4, ∃ q ∈ Q, ∀ v, q * φ v * q⁻¹ = φ (permVec s v)) := by
  classical
  obtain ⟨c, hc0, hcs, hmem⟩ := hm.lambda_data Q hz hAQ hidx
  have hcomm : ∀ q ∈ Q, ∀ v, ∑ i, v i = 0 → sec11Lam c v = 0 →
      sec11InU (permVec (hm.rho q) v + v) := by
    intro q hq v hv hl
    have h1 := hQcomm q hq (φ v) ((hmem v).2 ⟨hv, hl⟩)
    apply hm.inU_of_mem_zpowers
    rw [← hm.conj_apply (hQM hq) v]
    exact h1
  let g : ↥Q →* Equiv.Perm (Fin 6) := hm.rhoHom.comp (Subgroup.inclusion hQM)
  have hg : ∀ q : ↥Q, g q = hm.rho q := fun q => rfl
  have hcard : 32 ≤ Nat.card g.ker * Nat.card g.range := by
    rw [Subgroup.card_ker_mul_card_range]
    exact hQ32
  have hker : Nat.card g.ker ≤ (sec11Uc c).card := by
    have hex : ∀ q : g.ker, ∃ v ∈ sec11Uc c, φ v = ((q : ↥Q) : G) := by
      intro q
      have hq1 : hm.rho ((q : ↥Q) : G) = 1 := by
        rw [← hg]
        exact q.2
      obtain ⟨v, hv⟩ := hcen _ (q : ↥Q).2 hq1
      obtain ⟨hev, hl⟩ := (hmem v).1 (hv ▸ (q : ↥Q).2)
      obtain ⟨v', hv', h5⟩ := sec11_exists_rep v
      have hone : φ (fun _ => 1) = 1 := (hm.ker _).2 (Or.inr rfl)
      refine ⟨v', ?_, ?_⟩
      · rw [sec11Uc, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_, h5⟩
        · rcases hv' with rfl | rfl
          · exact hev
          · simp only [Pi.add_apply, Finset.sum_add_distrib, hev]
            decide
        · rcases hv' with rfl | rfl
          · exact hl
          · rw [sec11_lam_add, hl]
            unfold sec11Lam
            simp [hcs]
      · rcases hv' with rfl | rfl
        · exact hv
        · rw [hm.mul, hone, mul_one]
          exact hv
    choose f hf hfφ using hex
    have hinj : Function.Injective fun q : g.ker => (⟨f q, hf q⟩ : ↥(sec11Uc c)) := by
      intro q q' hqq'
      have h1 : f q = f q' := congrArg Subtype.val hqq'
      apply Subtype.ext
      apply Subtype.ext
      rw [← hfφ q, ← hfφ q', h1]
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hsub : (g.range : Set (Equiv.Perm (Fin 6))) ⊆ ↑(sec11Yc c) := by
    rintro _ ⟨q, rfl⟩
    rw [Finset.mem_coe, sec11Yc, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_, fun v hv hl => hcomm q q.2 v hv hl⟩
    · exact hm.rho_fix (hQM q.2) 0 (hQ0 q q.2)
    · exact hm.rho_fix (hQM q.2) 1 (hQ1 q q.2)
  have hrange : Nat.card g.range ≤ (sec11Yc c).card := by
    have h1 : Nat.card g.range = (g.range : Set (Equiv.Perm (Fin 6))).ncard :=
      Nat.card_coe_set_eq _
    rw [h1]
    calc (g.range : Set (Equiv.Perm (Fin 6))).ncard
        ≤ (↑(sec11Yc c) : Set (Equiv.Perm (Fin 6))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = (sec11Yc c).card := Set.ncard_coe_finset _
  have hprod : 32 ≤ (sec11Uc c).card * (sec11Yc c).card := by
    calc 32 ≤ Nat.card g.ker * Nat.card g.range := hcard
      _ ≤ (sec11Uc c).card * (sec11Yc c).card := Nat.mul_le_mul hker hrange
  have hcgood := sec11_c_good c hc0 hcs hprod
  subst hcgood
  have hmemQ : ∀ v, φ v ∈ Q ↔ (∑ i, v i = 0 ∧ v 0 = v 1) := by
    intro v
    rw [hmem v]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (sec11_lam_good v h1).1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (sec11_lam_good v h1).2 h2⟩
  have hk8 : Nat.card g.ker ≤ 8 := by
    rw [← sec11_Uc_good_card]
    exact hker
  have hr4 : 4 ≤ Nat.card g.range := by
    by_contra hlt
    have h3 : Nat.card g.range ≤ 3 := by omega
    have := Nat.mul_le_mul hk8 h3
    omega
  have hsub4 : (g.range : Set (Equiv.Perm (Fin 6))) ⊆ ↑sec11V4 := by
    intro σ hσ
    exact sec11_Yc_good_sub σ (Finset.mem_coe.mp (hsub hσ))
  have hrange4 : (g.range : Set (Equiv.Perm (Fin 6))) = ↑sec11V4 := by
    refine Set.eq_of_subset_of_ncard_le hsub4 ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, sec11_v4_card, ← Nat.card_coe_set_eq]
    exact hr4
  refine ⟨hmemQ, fun q hq => ?_, fun s hs => ?_⟩
  · have hmemr : g ⟨q, hq⟩ ∈ (g.range : Set (Equiv.Perm (Fin 6))) := ⟨_, rfl⟩
    rw [hrange4] at hmemr
    exact ⟨_, Finset.mem_coe.mp hmemr, fun v => hm.conj_apply (hQM hq) v⟩
  · have hmemr : s ∈ (g.range : Set (Equiv.Perm (Fin 6))) := by
      rw [hrange4]
      exact Finset.mem_coe.mpr hs
    obtain ⟨q, hqs⟩ := hmemr
    refine ⟨q, q.2, fun v => ?_⟩
    rw [hm.conj_apply (hQM q.2) v, ← hqs, hg]

end CFSG.OddStandard.SmallF3.Omega
