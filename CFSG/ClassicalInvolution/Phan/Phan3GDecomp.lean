module

public import CFSG.ClassicalInvolution.Phan.Geometry.Decomp
public import CFSG.ClassicalInvolution.Phan.Phan3GQuad

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan Module SimpleGraph

section Walks

variable {V : Type*} {G : SimpleGraph V} (E : ∀ x : V, Set (G.Walk x x))

theorem cycleHomotopic_of_length_le_five3
    (e3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil)
    (h4 : CommonNeighbour4 (G := G)) (h5 : ApexPentagon (G := G)) {u : V} (p : G.Walk u u)
    (hp : p.length ≤ 5) : CycleHomotopic E p .nil := by
  have e4 : ∀ {u : V} (p : G.Walk u u), p.length = 4 → CycleHomotopic E p .nil := by
    intro u p hp
    match u, p, hp with
    | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
      exact cycleHomotopic_quad_nil E e3 h4 h₁ h₂ h₃ h₄
  match u, p, hp with
  | _, .nil, _ => exact CycleHomotopic.refl _
  | _, .cons h₁ .nil, _ => exact absurd h₁ (G.loopless.irrefl _)
  | _, .cons h₁ (.cons _ .nil), _ => exact cycleHomotopic_cons_cons_nil E h₁
  | _, .cons _ (.cons _ (.cons _ .nil)), _ => exact e3 _ rfl
  | _, .cons _ (.cons _ (.cons _ (.cons _ .nil))), _ => exact e4 _ rfl
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil)))), _ =>
    exact cycleHomotopic_pent_nil E e3 e4 h5 h₁ h₂ h₃ h₄ h₅
  | _, .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _))))), hp =>
    simp only [Walk.length_cons] at hp
    omega

theorem cycleTrivial_of_cycles_le_five3 (hconn : G.Connected) (hdiam : G.ediam ≤ 2)
    (e3 : ∀ {u : V} (p : G.Walk u u), p.length = 3 → CycleHomotopic E p .nil)
    (h4 : CommonNeighbour4 (G := G)) (h5 : ApexPentagon (G := G)) : CycleTrivial E := by
  have hfin : G.ediam ≠ ⊤ := ne_top_of_le_ne_top (by simp) hdiam
  have hd : G.diam ≤ 2 := ENat.toNat_le_of_le_natCast hdiam
  refine cycleTrivial_of_diam E hconn hfin fun u p hp => ?_
  exact cycleHomotopic_of_length_le_five3 E e3 h4 h5 p (by omega)

end Walks

section Geometry

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ} {W : Submodule K (Fin m → K)}

theorem two_ne_zero_of_card_nine [Finite K] (hK : Nat.card K = 3 ^ 2) : (2 : K) ≠ 0 := by
  intro h2
  have h9 : ((Nat.card K : ℕ) : K) = 0 := by
    have := card_nsmul_eq_zero' (G := K) (x := (1 : K))
    rwa [nsmul_one] at this
  rw [hK] at h9
  have h1 : (1 : K) = 0 := by
    push_cast at h9
    linear_combination h9 - 4 * h2
  exact one_ne_zero h1

theorem isGeomWalk_triangle_of_five_le (hσ : IsUnitaryInvolution σ) (hW : Nondeg σ W)
    (h5 : 5 ≤ finrank K W) {x y z : ↥(nsPts σ W)} (hxy : (collGraph σ W).Adj x y)
    (hyz : (collGraph σ W).Adj y z) (hzx : (collGraph σ W).Adj z x) :
    IsGeomWalk σ W (.cons hxy (.cons hyz (.cons hzx .nil)) : (collGraph σ W).Walk x x) :=
  isGeomWalk_triangle hxy hyz hzx (inProperNondeg_of_five_le hσ hW h5 x.2 y.2 z.2 hxy)

theorem cycleHomotopic_length_three_of_five_le (hσ : IsUnitaryInvolution σ) (hW : Nondeg σ W)
    (h5 : 5 ≤ finrank K W) {u : ↥(nsPts σ W)} (p : (collGraph σ W).Walk u u)
    (hp : p.length = 3) : CycleHomotopic (geomWalks σ W) p .nil := by
  match u, p, hp with
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ =>
    exact cycleHomotopic_of_mem _ (isGeomWalk_triangle_of_five_le hσ hW h5 h₁ h₂ h₃)

section Decomp

variable (hσ : IsUnitaryInvolution σ) [Finite K]
include hσ

theorem apexPentagon_collGraph3 (hK : Nat.card K = 3 ^ 2) (hW : Nondeg σ W)
    (hd : 4 ≤ finrank K W) : ApexPentagon (G := collGraph σ W) := by
  intro a c d hcd
  obtain ⟨f, hf, hOc, hOd, haf⟩ := exists_orth_collinear_one hσ hK le_rfl hW hd c.2 d.2 hcd a.2
  exact ⟨⟨f, hf⟩, IsCollinear.of_orth hσ hf c.2 hOc, IsCollinear.of_orth hσ hf d.2 hOd, haf⟩

theorem collinear_decomp3 (hK : Nat.card K = 3 ^ 2) (hW : Nondeg σ W) (hd : 5 ≤ finrank K W)
    {x : ↥(nsPts σ W)} (w : (collGraph σ W).Walk x x) :
    CycleHomotopic (geomWalks σ W) w .nil :=
  cycleTrivial_of_cycles_le_five3 (geomWalks σ W)
    (collGraph_connected hσ hK le_rfl hW (by omega))
    (collGraph_ediam_le_two hσ hK le_rfl hW (by omega))
    (fun p hp => cycleHomotopic_length_three_of_five_le hσ hW hd p hp)
    (commonNeighbour4_collGraph3 hσ (two_ne_zero_of_card_nine hK) hW hd)
    (apexPentagon_collGraph3 hσ hK hW (by omega)) x w

end Decomp

end Geometry

end CFSG.ClassicalInvolution.Phan.Q3G
