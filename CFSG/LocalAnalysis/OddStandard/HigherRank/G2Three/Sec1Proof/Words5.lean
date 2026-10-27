module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Words3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Words

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def letterP (l : ℕ) : List ℕ :=
  if l = 0 then gx0P () else if l = 1 then gx1P () else if l = 2 then gy0P ()
  else if l = 3 then gy1P () else gsP ()

@[expose] def k3W : List ℕ := [0, 2, 0, 0, 3, 2, 2, 3, 3, 2, 2, 3, 0, 2, 2]

@[expose] def tW : List ℕ := [3, 2, 2, 3, 1, 2, 3, 0, 0, 1, 1, 0, 1, 0, 2, 1, 1]

variable {G : Type} [Group G] [Finite G]

@[expose] def letterG (m : G23Model G) (l : ℕ) : G :=
  if l = 0 then m.gX0 else if l = 1 then m.gX1 else if l = 2 then m.gY0
  else if l = 3 then m.gY1 else m.gS

@[expose] def wordG (m : G23Model G) (w : List ℕ) : G := (w.map (letterG m)).prod

@[expose] def gen5 (m : G23Model G) (s : ℕ) : G :=
  if s < 5 then sGen (frameOf m) s else if s = 5 then wordG m k3W
  else if s = 6 then wordG m tW else 1

theorem rho_letterG (m : G23Model G) (l : ℕ) : m.ρ (letterG m l) = decPc (letterP l) := by
  unfold letterG letterP
  split_ifs
  · rw [m.ρ_gX0, decPc_gx0P]
  · rw [m.ρ_gX1, decPc_gx1P]
  · rw [m.ρ_gY0, decPc_gy0P]
  · rw [m.ρ_gY1, decPc_gy1P]
  · rw [m.ρ_gS, decPc_gsP]

theorem wordG_mem (m : G23Model G) {w : List ℕ} (hw : ∀ l ∈ w, l < 4) : wordG m w ∈ m.L := by
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  have hl4 := hw l hl
  unfold letterG
  split_ifs
  · exact m.gX0_mem
  · exact m.gX1_mem
  · exact m.gY0_mem
  · exact m.gY1_mem
  · omega

theorem gen5_mem (m : G23Model G) : wordG m k3W ∈ m.L ∧ wordG m tW ∈ m.L :=
  ⟨wordG_mem m (by simp [k3W]), wordG_mem m (by simp [tW])⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
