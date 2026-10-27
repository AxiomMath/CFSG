module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelDef

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.RankThree.PartTwo.Census.Carrier.G2Three

@[expose] def gx0P (_ : Unit := ()) : List ℕ := mkPc false x0c x1c

@[expose] def gx1P (_ : Unit := ()) : List ℕ := mkPc false x1c x0c

@[expose] def gy0P (_ : Unit := ()) : List ℕ := mkPc false y0c y1c

@[expose] def gy1P (_ : Unit := ()) : List ℕ := mkPc false y1c y0c

@[expose] def gsP (_ : Unit := ()) : List ℕ := mkPc true one14 one14

@[expose] def n0P (_ : Unit := ()) : List ℕ :=
  mulPc (mulPc (gx0P ()) (mulPc (gy0P ()) (gy0P ()))) (gx0P ())

@[expose] def n1P (_ : Unit := ()) : List ℕ :=
  mulPc (mulPc (gx1P ()) (mulPc (gy1P ()) (gy1P ()))) (gx1P ())

@[expose] def n0iP (_ : Unit := ()) : List ℕ :=
  mulPc (mulPc (mulPc (gx0P ()) (gx0P ())) (gy0P ())) (mulPc (gx0P ()) (gx0P ()))

@[expose] def n1iP (_ : Unit := ()) : List ℕ :=
  mulPc (mulPc (mulPc (gx1P ()) (gx1P ())) (gy1P ())) (mulPc (gx1P ()) (gx1P ()))

@[expose] def u1P (_ : Unit := ()) : List ℕ := mulPc (mulPc (n0P ()) (gx1P ())) (n0iP ())

@[expose] def b1P (_ : Unit := ()) : List ℕ := mulPc (mulPc (n0P ()) (n1P ())) (n0iP ())

@[expose] def u2P (_ : Unit := ()) : List ℕ := mulPc (mulPc (n1P ()) (gx0P ())) (n1iP ())

@[expose] def b2P (_ : Unit := ()) : List ℕ := mulPc (mulPc (n1P ()) (n0P ())) (n1iP ())

@[expose] def h0P (_ : Unit := ()) : List ℕ := mulPc (n1P ()) (n1P ())

@[expose] def frameGensP (_ : Unit := ()) : List (List ℕ) :=
  [u1P (), b1P (), u2P (), b2P (), h0P (), gsP ()]

@[expose] def wordsCheck (_ : Unit := ()) : Bool :=
  mulPc (n0P ()) (n0iP ()) == onePc && mulPc (n0iP ()) (n0P ()) == onePc &&
    mulPc (n1P ()) (n1iP ()) == onePc && mulPc (n1iP ()) (n1P ()) == onePc

@[expose] def frameGen {G : Type} [Group G] (fr : Frame G) : ℕ → G
  | 0 => fr.u₁
  | 1 => fr.b₁
  | 2 => fr.u₂
  | 3 => fr.b₂
  | 4 => fr.h₀
  | _ => fr.σ

variable {G : Type} [Group G] [Finite G]

private theorem length_x0c : x0c.length = 196 := by decide +kernel

private theorem length_x1c : x1c.length = 196 := by decide +kernel

private theorem length_y0c : y0c.length = 196 := by decide +kernel

private theorem length_y1c : y1c.length = 196 := by decide +kernel

theorem decPc_gx0P : decPc (gx0P ()) = gx0W := by
  show decPc (mkPc false x0c x1c) = wdiag (dec14 x0c) (dec14 x1c)
  rw [decPc_mkPc_false length_x0c length_x1c]

theorem decPc_gx1P : decPc (gx1P ()) = gx1W := by
  show decPc (mkPc false x1c x0c) = wdiag (dec14 x1c) (dec14 x0c)
  rw [decPc_mkPc_false length_x1c length_x0c]

theorem decPc_gy0P : decPc (gy0P ()) = gy0W := by
  show decPc (mkPc false y0c y1c) = wdiag (dec14 y0c) (dec14 y1c)
  rw [decPc_mkPc_false length_y0c length_y1c]

theorem decPc_gy1P : decPc (gy1P ()) = gy1W := by
  show decPc (mkPc false y1c y0c) = wdiag (dec14 y1c) (dec14 y0c)
  rw [decPc_mkPc_false length_y1c length_y0c]

theorem decPc_gsP : decPc (gsP ()) = gsW := by
  show decPc (mkPc true one14 one14) = wanti 1 1
  rw [decPc_mkPc_true length_one14 length_one14, dec14_one14]

theorem rho_inv_eq (ρ : G →* Wm) {x : G} {A B : Wm} (hx : ρ x = A) (h1 : A * B = 1)
    (h2 : B * A = 1) : ρ x⁻¹ = B := by
  calc ρ x⁻¹ = ρ x⁻¹ * 1 := (mul_one _).symm
    _ = ρ x⁻¹ * (A * B) := by rw [← h1]
    _ = (ρ x⁻¹ * ρ x) * B := by rw [← hx, ← mul_assoc]
    _ = 1 * B := by rw [← map_mul, inv_mul_cancel, map_one]
    _ = B := one_mul B

theorem rho_mn0 (m : G23Model G) : m.ρ (mn0 m) = decPc (n0P ()) := by
  show m.ρ (m.gX0 * m.gY0 ^ 2 * m.gX0) =
    decPc (mulPc (mulPc (gx0P ()) (mulPc (gy0P ()) (gy0P ()))) (gx0P ()))
  simp only [map_mul, map_pow, m.ρ_gX0, m.ρ_gY0, decPc_mulPc, decPc_gx0P, decPc_gy0P,
    pow_two]

theorem rho_mn1 (m : G23Model G) : m.ρ (mn1 m) = decPc (n1P ()) := by
  show m.ρ (m.gX1 * m.gY1 ^ 2 * m.gX1) =
    decPc (mulPc (mulPc (gx1P ()) (mulPc (gy1P ()) (gy1P ()))) (gx1P ()))
  simp only [map_mul, map_pow, m.ρ_gX1, m.ρ_gY1, decPc_mulPc, decPc_gx1P, decPc_gy1P,
    pow_two]

private theorem wordsCheck_spec (h : wordsCheck () = true) :
    mulPc (n0P ()) (n0iP ()) = onePc ∧ mulPc (n0iP ()) (n0P ()) = onePc ∧
      mulPc (n1P ()) (n1iP ()) = onePc ∧ mulPc (n1iP ()) (n1P ()) = onePc := by
  simp only [wordsCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rho_mn0_inv (m : G23Model G) (h : wordsCheck () = true) :
    m.ρ (mn0 m)⁻¹ = decPc (n0iP ()) := by
  obtain ⟨h1, h2, -, -⟩ := wordsCheck_spec h
  have e1 : decPc (n0P ()) * decPc (n0iP ()) = 1 := by
    rw [← decPc_mulPc, h1, decPc_onePc]
  have e2 : decPc (n0iP ()) * decPc (n0P ()) = 1 := by
    rw [← decPc_mulPc, h2, decPc_onePc]
  exact rho_inv_eq m.ρ (rho_mn0 m) e1 e2

theorem rho_mn1_inv (m : G23Model G) (h : wordsCheck () = true) :
    m.ρ (mn1 m)⁻¹ = decPc (n1iP ()) := by
  obtain ⟨-, -, h1, h2⟩ := wordsCheck_spec h
  have e1 : decPc (n1P ()) * decPc (n1iP ()) = 1 := by
    rw [← decPc_mulPc, h1, decPc_onePc]
  have e2 : decPc (n1iP ()) * decPc (n1P ()) = 1 := by
    rw [← decPc_mulPc, h2, decPc_onePc]
  exact rho_inv_eq m.ρ (rho_mn1 m) e1 e2

theorem rho_frameGen (m : G23Model G) (h : wordsCheck () = true) :
    ∀ s < 6, m.ρ (frameGen (frameOf m) s) = decPc ((frameGensP ()).getD s []) := by
  intro s hs
  interval_cases s
  · show m.ρ (mn0 m * m.gX1 * (mn0 m)⁻¹) = decPc (u1P ())
    simp only [map_mul]
    rw [rho_mn0_inv m h, rho_mn0 m, m.ρ_gX1]
    simp only [u1P, decPc_mulPc, decPc_gx1P]
  · show m.ρ (mn0 m * mn1 m * (mn0 m)⁻¹) = decPc (b1P ())
    simp only [map_mul]
    rw [rho_mn0_inv m h, rho_mn0 m, rho_mn1 m]
    simp only [b1P, decPc_mulPc]
  · show m.ρ (mn1 m * m.gX0 * (mn1 m)⁻¹) = decPc (u2P ())
    simp only [map_mul]
    rw [rho_mn1_inv m h, rho_mn1 m, m.ρ_gX0]
    simp only [u2P, decPc_mulPc, decPc_gx0P]
  · show m.ρ (mn1 m * mn0 m * (mn1 m)⁻¹) = decPc (b2P ())
    simp only [map_mul]
    rw [rho_mn1_inv m h, rho_mn1 m, rho_mn0 m]
    simp only [b2P, decPc_mulPc]
  · show m.ρ (mn1 m ^ 2) = decPc (h0P ())
    rw [map_pow, rho_mn1 m, pow_two]
    simp only [h0P, decPc_mulPc]
  · show m.ρ m.gS = decPc (gsP ())
    rw [m.ρ_gS, decPc_gsP]

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
