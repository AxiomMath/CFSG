module

public import CFSG.CGT.PushingUpLit.LIT.A4.Cent

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly

section Sylow

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {m : G}

theorem exists_sylow_le (c : A4Cfg G M X) (h : TwoConj M X m) (hSC : StrongClosureTwo M X m) :
    ∃ Q : Sylow 2 G, (Q : Subgroup G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSM, hS2, hSidx, hAS⟩ :=
    exists_sylow_ge (isPGroup_two_of_sq (baseTwo_sq c h)) (baseTwo_le c h)
  have key : ∀ g : G, (∀ s : ↥S, s • ((g : G) : G ⧸ M) = ((g : G) : G ⧸ M)) →
      ((g : G) : G ⧸ M) = ((1 : G) : G ⧸ M) := by
    intro g hg
    have hle : conjSub g⁻¹ (baseTwo X m) ≤ M := by
      intro z hz
      rw [mem_conjSub_iff, inv_inv] at hz
      have h1 := hg ⟨(g * z * g⁻¹)⁻¹, S.inv_mem (hAS hz)⟩
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, QuotientGroup.eq] at h1
      simpa [mul_assoc] using h1
    have hgM : g ∈ M := by simpa using M.inv_mem (hSC g⁻¹ hle)
    rw [QuotientGroup.eq]
    simpa using M.inv_mem hgM
  have hfixed : Nat.card (MulAction.fixedPoints ↥S (G ⧸ M)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨⟨((1 : G) : G ⧸ M), fun s => ?_⟩⟩⟩
    · have hx : ∀ x : MulAction.fixedPoints ↥S (G ⧸ M), (x : G ⧸ M) = ((1 : G) : G ⧸ M) := by
        intro x
        obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.1
        rw [← hg]
        apply key
        intro s
        rw [hg]
        exact x.2 s
      exact Subtype.ext ((hx x).trans (hx y).symm)
    · rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simpa using M.inv_mem (hSM s.2)
  have hmod := hS2.card_modEq_card_fixedPoints (G ⧸ M)
  rw [hfixed] at hmod
  have hodd : ¬ 2 ∣ M.index := by
    have h2 : Nat.card (G ⧸ M) % 2 = 1 % 2 := hmod
    intro hd
    have : 2 ∣ Nat.card (G ⧸ M) := hd
    omega
  have hSi : ¬ 2 ∣ S.index := by
    rw [← Subgroup.relIndex_mul_index hSM]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h1 | h1
    · exact hSidx h1
    · exact hodd h1
  exact ⟨hS2.toSylow hSi, by simpa using hSM⟩

end Sylow

end CFSG.CGT.PushingUpLit.A4
