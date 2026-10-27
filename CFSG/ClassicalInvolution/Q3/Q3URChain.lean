module

public import CFSG.ClassicalInvolution.Q3.Q3URTriple
public import CFSG.ClassicalInvolution.Q3.Q3URRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped MatrixGroups


section Chain

variable {m : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem UCtx3.phanChain3U_of_end (c : UCtx3 m (conjClass3 K) K z) (nd : UNodes3 c) (hm : 4 ≤ m)
    (hN : NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n) (Su (GaloisField 3 2) 3 1 4))
    (hend : ∀ β : Subgroup G, β ∈ conjClass3 K → ∀ wβ : G, IsClassicalMember3 β wβ →
      ¬ Commutes K β → (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K β) →
      ¬ Commutes β (nd.j 0) →
      (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W β (nd.j 0)) →
      Commutes β (nd.j (m - 1)) → (∀ a, 1 ≤ a → a ≤ m - 3 → Commutes β (nd.j a)) →
      Commutes β (nd.j (m - 2))) :
    PhanChain3U K m := by
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨β, hβΩ, ⟨wβ, hwβ⟩, hnK, ⟨W1, hW1⟩, hnβ0, ⟨W2, hW2⟩, hlast, hmid⟩ :=
    c.exists_partner nd hm hsingle
  have hsecond : Commutes β (nd.j (m - 2)) :=
    hend β hβΩ wβ hwβ hnK ⟨W1, hW1⟩ hnβ0 ⟨W2, hW2⟩ hlast hmid
  obtain ⟨g, hg⟩ := hsingle (nd.j (m - 1)) (nd.mem (m - 1) (by omega)).1
  have hKβ : K ≠ β := by
    intro h
    subst h
    exact hnβ0 (nd.commK 0 (by omega))
  have hβ0 : β ≠ nd.j 0 := by
    intro h
    have h1 : Commutes β (nd.j 1) := hmid 1 le_rfl (by omega)
    rw [h] at h1
    exact nd.adj 0 (by omega) h1
  have hβ1 : β ≠ nd.j 1 := by
    intro h
    have h1 : Commutes β (nd.j 1) := hmid 1 le_rfl (by omega)
    rw [h] at h1
    exact not_commutes_self3 (nd.isCl 1 (by omega)) h1
  have hβM : β ≠ nd.j (m - 1) := by
    intro h
    have h1 := hlast
    rw [h] at h1
    exact not_commutes_self3 (nd.isCl (m - 1) (by omega)) h1
  have hzβ : z * wβ = wβ * z :=
    unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW1 c.hz.mem hwβ.mem
      c.hz.orderOf_eq_two hwβ.orderOf_eq_two
  have hβ0w : wβ * nd.w 0 = nd.w 0 * wβ :=
    unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW2 hwβ.mem
      (nd.isCl 0 (by omega)).mem hwβ.orderOf_eq_two (nd.isCl 0 (by omega)).orderOf_eq_two
  have hT0 : ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G, θ.range = (K ⊔ β) ⊔ (β ⊔ nd.j 0) ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = K ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = β ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = nd.j 0 :=
    c.triple_of_members_conj hN (by omega) hg c.hK hβΩ (nd.mem 0 (by omega)).1
      (nd.commK (m - 1) (by omega)) hlast (nd.far 0 (by omega) (m - 1) (by omega) (by omega))
      (nd.ne_K (m - 1) (by omega)).symm hβM (nd.inj 0 (by omega) (m - 1) (by omega) (by omega))
      c.hz hwβ (nd.isCl 0 (by omega)) hzβ hβ0w (nd.wz 0 (by omega)).symm hKβ hβ0
      (nd.ne_K 0 (by omega)).symm (nd.commK 0 (by omega)) hnK hnβ0
  have hT1 : ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G, θ.range = (β ⊔ nd.j 0) ⊔ (nd.j 0 ⊔ nd.j 1) ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = β ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = nd.j 0 ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = nd.j 1 :=
    c.triple_of_members_conj hN (by omega) hg hβΩ (nd.mem 0 (by omega)).1
      (nd.mem 1 (by omega)).1 hlast (nd.far 0 (by omega) (m - 1) (by omega) (by omega))
      (nd.far 1 (by omega) (m - 1) (by omega) (by omega)) hβM
      (nd.inj 0 (by omega) (m - 1) (by omega) (by omega))
      (nd.inj 1 (by omega) (m - 1) (by omega) (by omega)) hwβ (nd.isCl 0 (by omega))
      (nd.isCl 1 (by omega)) hβ0w (nd.wcomm 0 (by omega) 1 (by omega))
      (hmid 1 le_rfl (by omega) wβ hwβ.mem (nd.w 1) (nd.isCl 1 (by omega)).mem) hβ0
      (nd.inj 0 (by omega) 1 (by omega) (by omega)) hβ1 (hmid 1 le_rfl (by omega)) hnβ0
      (nd.adj 0 (by omega))
  let U : Fin (m + 2) → Subgroup G := fun i =>
    if i.val = 0 then K else if i.val = 1 then β else nd.j (i.val - 2)
  have hU : ∀ i : Fin (m + 2), (i.val = 0 ∧ U i = K) ∨ (i.val = 1 ∧ U i = β) ∨
      (∃ a, a < m ∧ i.val = a + 2 ∧ U i = nd.j a) := by
    intro i
    by_cases h0 : i.val = 0
    · exact Or.inl ⟨h0, by simp only [U, h0, ↓reduceIte]⟩
    · by_cases h1 : i.val = 1
      · exact Or.inr (Or.inl ⟨h1, by simp only [U, h1, one_ne_zero, ↓reduceIte]⟩)
      · refine Or.inr (Or.inr ⟨i.val - 2, by omega, by omega, ?_⟩)
        simp only [U, h0, h1, ↓reduceIte]
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases hU i with ⟨-, h⟩ | ⟨-, h⟩ | ⟨a, ha, -, h⟩
    · rw [h]; exact c.hK
    · rw [h]; exact hβΩ
    · rw [h]; exact (nd.mem a ha).1
  · intro i j hij
    rcases hU i with ⟨hi, h⟩ | ⟨hi, h⟩ | ⟨a, ha, hi, h⟩ <;>
    rcases hU j with ⟨hj, h'⟩ | ⟨hj, h'⟩ | ⟨b, hb, hj, h'⟩
    all_goals first | (exfalso; omega) | skip
    · rw [h, h']
      exact nd.commK b hb
    · rw [h, h']
      have hb1 : b = m - 1 ∨ b = m - 2 ∨ (1 ≤ b ∧ b ≤ m - 3) := by omega
      rcases hb1 with rfl | rfl | ⟨hb1, hb2⟩
      · exact hlast
      · exact hsecond
      · exact hmid b hb1 hb2
    · rw [h, h']
      exact nd.far a ha b hb (by omega)
  · intro i j hij
    rcases hU i with ⟨hi, h⟩ | ⟨hi, h⟩ | ⟨a, ha, hi, h⟩ <;>
    rcases hU j with ⟨hj, h'⟩ | ⟨hj, h'⟩ | ⟨b, hb, hj, h'⟩
    all_goals first | (exfalso; omega) | skip
    · rw [h, h']
      exact ⟨W1, hW1⟩
    · rw [h, h']
      have hb0 : b = 0 := by omega
      subst hb0
      exact ⟨W2, hW2⟩
    · rw [h, h']
      have hb : b = a + 1 := by omega
      subst hb
      exact nd.pair a hb
  · intro i j k hij hjk
    rcases hU i with ⟨hi, h⟩ | ⟨hi, h⟩ | ⟨a, ha, hi, h⟩ <;>
    rcases hU j with ⟨hj, h'⟩ | ⟨hj, h'⟩ | ⟨b, hb, hj, h'⟩ <;>
    rcases hU k with ⟨hk, h''⟩ | ⟨hk, h''⟩ | ⟨d, hd, hk, h''⟩
    all_goals first | (exfalso; omega) | skip
    · have hd0 : d = 0 := by omega
      subst hd0
      rw [h, h', h'']
      exact hT0
    · have hb0 : b = 0 := by omega
      have hd1 : d = 1 := by omega
      subst hb0
      subst hd1
      rw [h, h', h'']
      exact hT1
    · have hb' : b = a + 1 := by omega
      have hd' : d = a + 2 := by omega
      subst hb'
      subst hd'
      rw [h, h', h'']
      exact c.node_triple nd hN (by omega) hd

theorem UCtx3.phanChain3U (c : UCtx3 m (conjClass3 K) K z) (nd : UNodes3 c) (hm : 6 ≤ m)
    (hN : NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n) (Su (GaloisField 3 2) 3 1 4)) :
    PhanChain3U K m := by
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  exact c.phanChain3U_of_end nd (by omega) hN fun β hβ wβ hwβ hnK _ _ _ hlast hmid =>
    c.commutes_beta_second_last nd hm hsingle hβ ⟨wβ, hwβ⟩ hnK hmid hlast

end Chain

section Rows

theorem chainRow3U_of_odd3 (h3 : OddThreeFreeInput) {m : ℕ} (hm : 6 ≤ m) : ChainRow3U m := by
  intro G _ _ _ hnab K z hR hshape
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨hex, hP1⟩ := hR.setup
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictU (by omega : 2 ≤ m) hR.inClass hK hR.cls hshape
  let c : UCtx3 m (conjClass3 K) K z :=
    { hm := by omega, hΩ := hR.inClass, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1,
      hO3 := h3 G K z hR, d := d, hlift := Or.inl (by omega) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  exact c.phanChain3U nd hm noCover_su4_three

theorem piece3SU7_of_odd3 (h3 : OddThreeFreeInput) (hP : Phan3Rec) : Piece3SU7 :=
  piece3SU7_of_chain h3 hP fun _ hm => chainRow3U_of_odd3 h3 hm

end Rows

end CFSG.ClassicalInvolution.Q3.Q3W
