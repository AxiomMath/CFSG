module

public import CFSG.CGT.PushingUpLit.SolK.SevenFour
public import CFSG.CGT.PushingUpLit.SolK.LocalTI

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

theorem mul_inv_mem_of_index_le_two {H : Type*} [Group H] [Finite H] {D : Subgroup H}
    (hD : D.index ≤ 2) {u v : H} (hu : u ∉ D) (hv : v ∉ D) : u * v⁻¹ ∈ D := by
  have hne : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : D.index ≠ 1 := fun h => hu (by rw [Subgroup.index_eq_one.1 h]; trivial)
  have h2 : D.index = 2 := by omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2
  have hua : u * a ∈ D := by
    rcases ha u with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hu
  have hva : v * a ∈ D := by
    rcases ha v with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hv
  have := D.mul_mem hua (D.inv_mem hva)
  simpa [mul_assoc] using this

theorem exists_four_distinct {d : ℕ} (hd : 7 ≤ d) (i j : Fin d) :
    ∃ a b c e : Fin d, a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j ∧ c ≠ i ∧ c ≠ j ∧ e ≠ i ∧ e ≠ j ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ c ≠ e := by
  classical
  have hpick : ∀ s : Finset (Fin d), s.card + 1 ≤ d → ∃ x, x ∉ s := fun s hs => by
    by_contra hcon
    push Not at hcon
    have : s = Finset.univ := Finset.eq_univ_of_forall hcon
    rw [this, Finset.card_univ, Fintype.card_fin] at hs
    omega
  obtain ⟨a, ha⟩ := hpick {i, j} (by have := Finset.card_le_two (a := i) (b := j); omega)
  obtain ⟨b, hb⟩ := hpick {i, j, a} (by
    have := Finset.card_le_three (a := i) (b := j) (c := a); omega)
  obtain ⟨c, hc⟩ := hpick {i, j, a, b} (by
    have := Finset.card_le_four (a := i) (b := j) (c := a) (d := b); omega)
  obtain ⟨e, he⟩ := hpick {i, j, a, b, c} (by
    have := Finset.card_le_five (a := i) (b := j) (c := a) (d := b) (e := c); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc he
  exact ⟨a, b, c, e, ha.1, ha.2, hb.1, hb.2.1, hc.1, hc.2.1, he.1, he.2.1, Ne.symm hb.2.2,
    Ne.symm hc.2.2.1, Ne.symm he.2.2.1, Ne.symm hc.2.2.2, Ne.symm he.2.2.2.1,
    Ne.symm he.2.2.2.2⟩

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem hAway_seven (hT : TightData S) (hQe : QElem S) (hR : RSmall S) (hn : n = 3) :
    S.HAway := by
  intro z hz hz1 hlen k hk
  obtain ⟨l, hl⟩ := S.exists_hasLen hz
  have hkC : k ∈ CGOf z := mem_centralizer_zpowers_iff.2 hk
  by_cases hl4 : l = 4
  · subst hl4
    obtain ⟨w, hw, r, hr, rfl, hcard⟩ := hl
    exact S.centralizer_le_M_of_len_four_seven hT hQe hR hn hw hr hcard hkC
  · have hl2 : l ≠ 2 := fun h2 => hlen (h2 ▸ hl)
    exact (S.centralizer_eq_of_len S.hyp.charTwo hT hz hz1 hl hl2 hl4).2
      (Subgroup.centralizer_le_normalizer _ hkC)

theorem not_conj_len_four_seven (hT : TightData S) (hQe : QElem S) (hR : RSmall S) (hn : n = 3)
    {g h : G} (hg : g ∉ M) (hhQ : h ∈ pCoreOf 2 M) (hhg : g⁻¹ * h * g ∈ pCoreOf 2 M)
    (hl4 : S.HasLen h 4) : False := by
  classical
  have hA := S.hAway_seven hT hQe hR hn
  obtain ⟨w, hw, r, hr, rfl, hcard⟩ := hl4
  have hh1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  have hlen : ¬ S.HasLen (w * r) 2 := fun h2 => by
    have := SolCfg.HasLen.unique S ⟨w, hw, r, hr, rfl, hcard⟩ h2
    omega
  have hl2 := S.hasLen_conj hT hQe hA hg hhQ hhg hh1 hlen
  obtain ⟨w', hw', r', hr', he', hcard'⟩ := hl2
  have hCG : CGOf (w * r) ≤ M := fun k hk => hA _ hhQ hh1 hlen k (mem_centralizer_zpowers_iff.1 hk)
  have hle : Nat.card ↥(CMOf M (g⁻¹ * (w * r) * g)) ≤ Nat.card ↥(CGOf (w * r)) := by
    refine Nat.card_le_card_of_injective (fun c => ⟨g * (c : G) * g⁻¹, ?_⟩) ?_
    · have hc : (c : G) * (g⁻¹ * (w * r) * g) * (c : G)⁻¹ = g⁻¹ * (w * r) * g :=
        mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 c.2).2
      refine mem_centralizer_zpowers_iff.2 ?_
      calc g * (c : G) * g⁻¹ * (w * r) * (g * (c : G) * g⁻¹)⁻¹
          = g * ((c : G) * (g⁻¹ * (w * r) * g) * (c : G)⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * (w * r) * g) * g⁻¹ := by rw [hc]
        _ = w * r := by group
    · intro c c' hcc
      have := congrArg Subtype.val hcc
      exact Subtype.ext (by simpa using this)
  have hM4 := S.card_eq_choose_mul_card hR hw hr
  have hM2 := S.card_eq_choose_mul_card hR hw' hr'
  have hCM : CMOf M (w * r) = CGOf (w * r) := inf_eq_right.2 hCG
  rw [hcard, hCM] at hM4
  have hh'eq : g⁻¹ * (w * r) * g = w' * r' := he'
  rw [hcard', ← hh'eq] at hM2
  have hc4 : (2 * n + 1).choose 4 = 35 := by rw [hn]; decide
  have hc2 : (2 * n + 1).choose 2 = 21 := by rw [hn]; decide
  rw [hc4] at hM4
  rw [hc2] at hM2
  have hpos : 0 < Nat.card ↥(CMOf M (g⁻¹ * (w * r) * g)) := Nat.card_pos
  omega

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
