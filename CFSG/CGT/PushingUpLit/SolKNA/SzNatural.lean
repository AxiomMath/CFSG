module

public import CFSG.CGT.PushingUpLit.SolKNA.SzWeightDef
public import CFSG.CGT.PushingUpLit.SolKNA.LemmaW

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit Matrix

theorem torusMat_mulVec (a : ℕ) (x : (F a)ˣ) (v : Fin 4 → F a) :
    torusMat a x *ᵥ v = ![(x : F a) ^ (1 + 2 ^ a) * v 0, (x : F a) ^ (2 ^ a) * v 1,
      ((x : F a) ^ (2 ^ a))⁻¹ * v 2, ((x : F a) ^ (1 + 2 ^ a))⁻¹ * v 3] := by
  ext i
  fin_cases i <;> simp [torusMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem card_F (a : ℕ) : Nat.card (F a) = 2 ^ (2 * a + 1) :=
  GaloisField.card 2 (2 * a + 1) (by omega)

theorem natural_case {a : ℕ} (ha : 1 ≤ a) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) ↥(Sz a) V) (θ : (Fin 4 → F a) →+ V)
    (hθb : Function.Bijective θ)
    (hθ : ∀ (g : ↥(Sz a)) (v : Fin 4 → F a),
      θ (((g : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) *ᵥ v) = ρ g (θ v))
    (c : F a → F a → V) (h₁ : ∀ b b' b'', c (b + b') b'' = c b b'' + c b' b'')
    (h₂ : ∀ b b' b'', c b (b' + b'') = c b b' + c b b'') (halt : ∀ b, c b b = 0)
    (hS : ∀ α β b b', ρ (rootSz a α β) (c b b') = c b b')
    (hT : ∀ (x : (F a)ˣ) b b', ρ (torusSz a x) (c b b') =
      c ((x : F a) ^ (1 + 2 ^ (a + 1)) * b) ((x : F a) ^ (1 + 2 ^ (a + 1)) * b')) :
    ∀ b b', c b b' = 0 := by
  classical
  let _ : Fintype (F a) := Fintype.ofFinite (F a)
  let e := Equiv.ofBijective θ hθb
  let v : F a → F a → (Fin 4 → F a) := fun b b' => e.symm (c b b')
  have hv : ∀ b b', θ (v b b') = c b b' := fun b b' => e.apply_symm_apply _
  have hSv : ∀ α β b b', rootMat a α β *ᵥ v b b' = v b b' := by
    intro α β b b'
    apply hθb.1
    have h := hθ (rootSz a α β) (v b b')
    have h' : θ (rootMat a α β *ᵥ v b b') = ρ (rootSz a α β) (θ (v b b')) := h
    rw [h', hv, hS]
  have hcomp : ∀ b b', v b b' 1 = 0 ∧ v b b' 2 = 0 ∧ v b b' 3 = 0 := by
    intro b b'
    have h01 := hSv 0 1 b b'
    have h10 := hSv 1 0 b b'
    rw [rootMat_mulVec] at h01 h10
    have e1 := congrFun h01 1
    have e0 := congrFun h01 0
    have e10 := congrFun h10 0
    simp [zero_pow (Nat.two_pow_pos _).ne', zero_pow (show 2 + 2 ^ (a + 1) ≠ 0 by positivity),
      zero_pow (show 1 + 2 ^ (a + 1) ≠ 0 by positivity)] at e1 e0 e10
    have h3 : v b b' 3 = 0 := e1
    refine ⟨?_, ?_, h3⟩
    · rw [h3] at e10
      simpa using e10
    · rw [h3] at e0
      simpa using e0
  let γ : F a → F a → F a := fun b b' => v b b' 0
  have hvγ : ∀ b b', v b b' = ![γ b b', 0, 0, 0] := by
    intro b b'
    rw [vec_eq a (v b b')]
    obtain ⟨h1, h2, h3⟩ := hcomp b b'
    simp [γ, h1, h2, h3]
  have hadd1 : ∀ b b' b'', v (b + b') b'' = v b b'' + v b' b'' := by
    intro b b' b''
    apply hθb.1
    rw [map_add, hv, hv, hv, h₁]
  have hadd2 : ∀ b b' b'', v b (b' + b'') = v b b' + v b b'' := by
    intro b b' b''
    apply hθb.1
    rw [map_add, hv, hv, hv, h₂]
  have halt' : ∀ b, v b b = 0 := by
    intro b
    apply hθb.1
    rw [hv, halt, map_zero]
  have hTv : ∀ (x : (F a)ˣ) b b', torusMat a x *ᵥ v b b' =
      v ((x : F a) ^ (1 + 2 ^ (a + 1)) * b) ((x : F a) ^ (1 + 2 ^ (a + 1)) * b') := by
    intro x b b'
    apply hθb.1
    have h := hθ (torusSz a x) (v b b')
    have h' : θ (torusMat a x *ᵥ v b b') = ρ (torusSz a x) (θ (v b b')) := h
    rw [h', hv, hT, hv]
  have hcardF : Fintype.card (F a) = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card]
    exact card_F a
  have hγ := weight_lemma_field (K := F a) ha hcardF γ
    (fun b b' b'' => congrFun (hadd1 b b' b'') 0) (fun b b' b'' => congrFun (hadd2 b b' b'') 0)
    (fun b => congrFun (halt' b) 0) (fun x hx b b' => by
      have h0 := congrFun (hTv (Units.mk0 x hx) b b') 0
      rw [torusMat_mulVec] at h0
      simp only [Matrix.cons_val_zero, Units.val_mk0] at h0
      exact h0.symm)
  intro b b'
  have hz : (![γ b b', 0, 0, 0] : Fin 4 → F a) = 0 := by
    rw [hγ b b']
    ext i; fin_cases i <;> rfl
  calc c b b' = θ (v b b') := (hv b b').symm
    _ = θ ![γ b b', 0, 0, 0] := by rw [← hvγ b b']
    _ = 0 := by rw [hz, map_zero]

end CFSG.CGT.PushingUpLit.SolKNA
