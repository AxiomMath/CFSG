module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section Chev2Down


theorem chev2DownAt_holds {G : Type} [Group G] [Finite G] (p : ℕ) : Chev2DownAt G p := by
  intro hp hp2 X K y hX hK hy hyN hch J hJ
  have hA : CFSG.Open.IsElemAbelian p (Subgroup.zpowers y) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
      apply Subtype.ext
      show (a : G) * b = b * a
      rw [← hm, ← hn]
      exact (Commute.refl y).zpow_zpow m n |>.eq
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hcen : Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
    ext g
    simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      exact h y (Subgroup.mem_zpowers y)
    · intro h z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact (Commute.zpow_left (show Commute y g from h) m).eq
  exact chevClosureQAt_of_lieComp_lieComps (G := G)
    CFSG.LocalAnalysis.GLTheoremA.lieComp_holds
    (fun _ hq h5 => CFSG.LocalAnalysis.GLTheoremA.lieCompsOn_holds hq h5)
    hp hp2 hp hp2 2 Nat.prime_two X K (Subgroup.zpowers y) hX hK hch hA
    (Subgroup.zpowers_le.2 hyN) J (by rw [hcen]; exact hJ)

end Chev2Down

end CFSG.LocalAnalysis.GLTheoremA
