module

public import CFSG.ClassicalInvolution.Phan.PhanQ59ClassC

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section Cone

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem exists_cone [Finite F] [Finite K] (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0)
    (hε : ε ≠ 0) {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x) (hσu : IsUnitaryInvolution σ) {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hFq : Nat.card F = q) (hq : 5 ≤ q) {a b c : V8 K}
    (ha : ffK D a) (hb : ffK D b) (hc : ffK D c) (hab : ColK D a b) (hbc : ColK D b c)
    (hac : ColK D a c) :
    ∃ e, ffK D e ∧ ColK D a e ∧ ColK D b e ∧ ColK D c e ∧
      (∃ W, PhanSolid D W ∧ a ∈ W ∧ b ∈ W ∧ e ∈ W) ∧
      (∃ W, PhanSolid D W ∧ b ∈ W ∧ c ∈ W ∧ e ∈ W) ∧
      (∃ W, PhanSolid D W ∧ c ∈ W ∧ a ∈ W ∧ e ∈ W) := by
  by_cases hinf : ∀ v ∈ Submodule.span K {a, b, c},
      conj D v ∈ Submodule.span K {a, b, c} → v = 0
  · obtain ⟨e, hff, h1, h2', h3, W, hW, haW, hbW, hcW, heW⟩ :=
      exists_cone_of_inf D hodd h2 hε hσ hσu hK hq ha hb hc hab hbc hac hinf
    exact ⟨e, hff, h1, h2', h3, ⟨W, hW, haW, hbW, heW⟩, ⟨W, hW, hbW, hcW, heW⟩,
      ⟨W, hW, hcW, haW, heW⟩⟩
  · obtain ⟨v, hv, hcv, hv0⟩ : ∃ v ∈ Submodule.span K {a, b, c},
        conj D v ∈ Submodule.span K {a, b, c} ∧ v ≠ 0 := by
      by_contra hcon
      exact hinf fun v hv hcv => Classical.byContradiction fun hv0 => hcon ⟨v, hv, hcv, hv0⟩
    have hstab : ∀ w ∈ Submodule.span K {a, b, c} ⊓ conjSub D (Submodule.span K {a, b, c}),
        conj D w ∈ Submodule.span K {a, b, c} ⊓ conjSub D (Submodule.span K {a, b, c}) :=
      fun w hw => by
        obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
        refine Submodule.mem_inf.2 ⟨(mem_conjSub (D := D)).1 hw2, ?_⟩
        rw [mem_conjSub, conj_conj]
        exact hw1
    obtain ⟨r, hrZ, hr0, hrc⟩ := exists_fixed_of_stable D h2 hε hstab
      (Submodule.mem_inf.2 ⟨hv, (mem_conjSub (D := D)).2 hcv⟩) hv0
    exact exists_cone_rational D hodd h2 hε hσ hσu hK hFq hq ha hb hc hab hbc hac
      (Submodule.mem_inf.1 hrZ).1 hr0 hrc

end Cone

end CFSG.ClassicalInvolution.PhanQ
