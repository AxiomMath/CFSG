module

public import CFSG.RankThree.GF2n.SzExplicit

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit Matrix

@[expose] noncomputable def rootSz (a : ℕ) (α β : F a) : ↥(Sz a) :=
  ⟨rootGL a α β, rootGL_mem a α β⟩

@[expose] noncomputable def torusMat (a : ℕ) (x : (F a)ˣ) : Matrix (Fin 4) (Fin 4) (F a) :=
  !![(x : F a) ^ (1 + 2 ^ a), 0, 0, 0;
     0, (x : F a) ^ (2 ^ a), 0, 0;
     0, 0, ((x : F a) ^ (2 ^ a))⁻¹, 0;
     0, 0, 0, ((x : F a) ^ (1 + 2 ^ a))⁻¹]

theorem torusMat_mul_inv (a : ℕ) (x : (F a)ˣ) : torusMat a x * torusMat a x⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torusMat, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] noncomputable def torusGL (a : ℕ) (x : (F a)ˣ) : GL (Fin 4) (F a) :=
  ⟨torusMat a x, torusMat a x⁻¹, torusMat_mul_inv a x, by simpa using torusMat_mul_inv a x⁻¹⟩

@[simp] theorem coe_torusGL (a : ℕ) (x : (F a)ˣ) :
    ((torusGL a x : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) = torusMat a x := rfl

theorem torusGL_mem (a : ℕ) (x : (F a)ˣ) : torusGL a x ∈ Sz a :=
  Subgroup.subset_closure (show _ ∈ SzGenerators a from Or.inr (Or.inl ⟨x, rfl⟩))

@[expose] noncomputable def torusSz (a : ℕ) (x : (F a)ˣ) : ↥(Sz a) :=
  ⟨torusGL a x, torusGL_mem a x⟩

@[expose] def SzCommutatorWeight : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (g₀ : ↥(Sz a)) (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) ↥(Sz a) V),
    (∃ g : ↥(Sz a), orderOf g = 5 ∧ ∀ v, ρ g v = v → v = 0) →
    ∀ c : F a → F a → V,
      (∀ b b' b'', c (b + b') b'' = c b b'' + c b' b'') →
      (∀ b b' b'', c b (b' + b'') = c b b' + c b b'') →
      (∀ b, c b b = 0) →
      (∀ α β b b', ρ (g₀ * rootSz a α β * g₀⁻¹) (c b b') = c b b') →
      (∀ (x : (F a)ˣ) b b', ρ (g₀ * torusSz a x * g₀⁻¹) (c b b') =
        c ((x : F a) ^ (1 + 2 ^ (a + 1)) * b) ((x : F a) ^ (1 + 2 ^ (a + 1)) * b')) →
      ∀ b b', c b b' = 0

end CFSG.CGT.PushingUpLit.SolKNA
