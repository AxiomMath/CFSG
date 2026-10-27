module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G1Defs
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSplit

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup Equiv AltStdCycTwo AltStdBal

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

@[expose] noncomputable def rhoC (c : Config G L Q n θ z) :
    centralizer ({z} : Set G) →* Perm (Fin n) :=
  (rho θ c.hn8).comp (Subgroup.inclusion (cent_le_normalizer c.ot.std c.ot.cyc))

theorem rhoC_apply (c : Config G L Q n θ z) (x : centralizer ({z} : Set G)) :
    rhoC c x = rho θ c.hn8 ⟨x, cent_le_normalizer c.ot.std c.ot.cyc x.2⟩ := rfl

theorem mem_ker_rhoC_iff (c : Config G L Q n θ z) (x : centralizer ({z} : Set G)) :
    x ∈ (rhoC c).ker ↔ (x : G) ∈ centralizer (L : Set G) := by
  rw [MonoidHom.mem_ker, rhoC_apply, rho_eq_one_iff]

theorem card_ker_rhoC (c : Config G L Q n θ z) :
    Nat.card (rhoC c).ker =
      Nat.card (centralizer (L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  have hle : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) ≤ centralizer ({z} : Set G) :=
    inf_le_right
  have : (rhoC c).ker =
      (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf
        (centralizer ({z} : Set G)) := by
    ext x
    rw [mem_ker_rhoC_iff, mem_subgroupOf]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
  rw [this, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]

theorem factorization_card_inf (c : Config G L Q n θ z) :
    (Nat.card (centralizer (L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G)).factorization
      2 = 1 := by
  set M := centralizer (L : Set G) ⊓ centralizer ({z} : Set G) with hM
  have d := c.ot.cyc
  have hQz : zpowers z = Q := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 d.mem)
    (by rw [c.ot.card, Nat.card_zpowers, d.order])
  have hQM : Q ≤ M := by
    rw [← hQz, zpowers_le]
    exact ⟨d.le d.mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hMK : M ≤ centralizer (L : Set G) := inf_le_left
  have hi : ¬ 2 ∣ Q.relIndex M := by
    intro h2
    apply d.odd_index
    exact h2.trans (Dvd.intro _ (relIndex_mul_relIndex Q M (centralizer (L : Set G)) hQM hMK))
  have hcard : Nat.card M = 2 * Q.relIndex M := by
    rw [← c.ot.card, mul_comm, ← Subgroup.relIndex_mul_card, inf_of_le_left hQM]
  rw [hcard, Nat.factorization_mul (by norm_num)
      (show Q.relIndex M ≠ 0 from Subgroup.index_ne_zero_of_finite),
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hi]

theorem range_rhoC_of_inner (c : Config G L Q n θ z)
    (hin : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    (rhoC c).range = alternatingGroup (Fin n) := by
  apply le_antisymm
  · rintro σ ⟨x, rfl⟩
    have hx := (mem_evenAct_iff θ c.hn8 (cent_le_normalizer c.ot.std c.ot.cyc x.2)).1
      (sup_le_evenAct θ c.hn8 (hin x.2))
    exact hx
  · intro σ hσ
    set l : L := θ.symm ⟨σ, hσ⟩ with hl
    have hlC : (l : G) ∈ centralizer ({z} : Set G) := le_cent_single c.ot.std c.ot.cyc l.2
    refine ⟨⟨l, hlC⟩, ?_⟩
    rw [rhoC_apply, rho_of_mem θ c.hn8 l]
    simp [hl]

theorem range_rhoC_of_outer (c : Config G L Q n θ z) {u : G}
    (huC : u ∈ centralizer ({z} : Set G)) (huO : u ∉ L ⊔ centralizer (L : Set G)) :
    (rhoC c).range = ⊤ := by
  have hA : alternatingGroup (Fin n) ≤ (rhoC c).range := by
    intro σ hσ
    set l : L := θ.symm ⟨σ, hσ⟩ with hl
    have hlC : (l : G) ∈ centralizer ({z} : Set G) := le_cent_single c.ot.std c.ot.cyc l.2
    refine ⟨⟨l, hlC⟩, ?_⟩
    rw [rhoC_apply, rho_of_mem θ c.hn8 l]
    simp [hl]
  have hu : rhoC c ⟨u, huC⟩ ∉ alternatingGroup (Fin n) := by
    intro h
    exact huO (mem_sup_of_rho_mem θ c.hn8 (cent_le_normalizer c.ot.std c.ot.cyc huC) h)
  have hne : ¬ (rhoC c).range ≤ alternatingGroup (Fin n) := fun h =>
    hu (h ⟨⟨u, huC⟩, rfl⟩)
  have h2 : 2 ≤ n := by have := c.hn8; omega
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr h2
  have hrel1 : (alternatingGroup (Fin n)).relIndex (rhoC c).range ≠ 1 := fun h =>
    hne (Subgroup.relIndex_eq_one.mp h)
  have hcard : Nat.card (alternatingGroup (Fin n)) *
      (alternatingGroup (Fin n)).relIndex (rhoC c).range = Nat.card ((rhoC c).range) := by
    have h := Subgroup.relIndex_mul_card (H := alternatingGroup (Fin n)) (K := (rhoC c).range)
    rwa [inf_of_le_left hA, mul_comm] at h
  have htot : Nat.card ((rhoC c).range) ≤ 2 * Nat.card (alternatingGroup (Fin n)) := by
    rw [two_mul_nat_card_alternatingGroup]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hpos : 0 < Nat.card (alternatingGroup (Fin n)) := Nat.card_pos
  have hrel2 : (alternatingGroup (Fin n)).relIndex (rhoC c).range = 2 := by
    have hle2 : (alternatingGroup (Fin n)).relIndex (rhoC c).range ≤ 2 := by
      by_contra hgt
      push Not at hgt
      have : Nat.card (alternatingGroup (Fin n)) * 3 ≤
          Nat.card (alternatingGroup (Fin n)) *
            (alternatingGroup (Fin n)).relIndex (rhoC c).range :=
        Nat.mul_le_mul_left _ hgt
      omega
    have hne0 : (alternatingGroup (Fin n)).relIndex (rhoC c).range ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    omega
  apply Subgroup.eq_top_of_card_eq
  rw [← hcard, hrel2, mul_comm, two_mul_nat_card_alternatingGroup]

theorem factorization_two_of_eq {m k r : ℕ} (hm : m = 2 ^ k * r) (hr : ¬ 2 ∣ r) :
    m.factorization 2 = k := by
  have hr0 : r ≠ 0 := fun h => hr (h ▸ dvd_zero 2)
  rw [hm, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hr0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hr, add_zero]

theorem factorization_card_centralizer (c : Config G L Q n θ z) :
    (Nat.card (centralizer ({z} : Set G))).factorization 2 =
      1 + (Nat.card (rhoC c).range).factorization 2 := by
  rw [← Subgroup.card_ker_mul_card_range (rhoC c), card_ker_rhoC,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    factorization_card_inf c]

private theorem factorization_alt (m : ℕ) (hm : m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11) :
    (Nat.card (alternatingGroup (Fin m))).factorization 2 = if m ≤ 9 then 6 else 7 := by
  rcases hm with rfl | rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  · exact factorization_two_of_eq (r := 315) (by decide) (by decide)
  · exact factorization_two_of_eq (r := 2835) (by decide) (by decide)
  · exact factorization_two_of_eq (r := 14175) (by decide) (by decide)
  · exact factorization_two_of_eq (r := 155925) (by decide) (by decide)

private theorem factorization_perm (m : ℕ) (hm : m = 8 ∨ m = 9) :
    (Nat.card (Perm (Fin m))).factorization 2 = 7 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rcases hm with rfl | rfl
  · exact factorization_two_of_eq (r := 315) (by decide) (by decide)
  · exact factorization_two_of_eq (r := 2835) (by decide) (by decide)

theorem sec4CentSylowCard_holds : Sec4CentSylowCard := by
  intro G _ _ L Q n θ z c P
  have hP := Sylow.card_eq_multiplicity (p := 2) (hp := ⟨Nat.prime_two⟩) P
  have hf := factorization_card_centralizer c
  rw [hP, hf]
  rcases c.shape with hin | ⟨h9, u, huC, huO, -⟩
  · rw [range_rhoC_of_inner c hin, factorization_alt n c.n_cases]
    by_cases h9 : n ≤ 9
    · have hA : IsASmall L n z := ⟨by have := c.hn8; omega, hin⟩
      rw [if_pos h9]
      exact ⟨fun _ => rfl, fun h => absurd hA h⟩
    · rw [if_neg h9]
      exact ⟨fun h => absurd h.1 (by omega), fun _ => rfl⟩
  · have hA : ¬ IsASmall L n z := fun h => huO (h.2 huC)
    rw [range_rhoC_of_outer c huC huO, Subgroup.card_top,
      factorization_perm n (by have := c.hn8; omega)]
    exact ⟨fun h => absurd h hA, fun _ => rfl⟩

end CFSG.OddStandard.AltStdSmall4
