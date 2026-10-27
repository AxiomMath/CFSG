module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A312Sub

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Dickson CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native.A312L

@[expose] def Q2 {X : Type} [Group X] (B : Subgroup X) : Prop := IsAlt 5 ↥B

theorem Q2.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    {B : Subgroup X} (h : Q2 (B.map e.toMonoidHom)) : Q2 B :=
  IsAlt.of_mulEquiv (mapEquiv e B) h

theorem over_l2p_psl2 {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    Over (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) Q2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))))
  have hTsyl := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  generalize (P₀ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) = T at hTsyl
  refine Over.of_sylow (fun e B h => Q2.of_mulEquiv e h) T hTsyl fun B hB hBtop => ?_
  have hB' : B ∈ cComp (B ⊔ T) := hB
  have hBperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hB'
  have hBne : B ≠ ⊥ := ne_bot_of_mem_cComp hB'
  rcases perfect_subgroup_psl2_prime hp2 B hBperf hBne with hBt | ⟨⟨eB⟩, -⟩
  · exact absurd hBt hBtop
  · exact ⟨eB⟩

theorem over_l2p
    : ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → IsPSL 2 p 1 X →
    Over X Q2 := by
  intro X _ _ p hp hp2 hX
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := equiv_psl2_zmod_of_model hX
  exact Over.of_mulEquiv e (fun B h => Q2.of_mulEquiv e h) (over_l2p_psl2 hp2)

end A312Sub

end CFSG.QuasithinUnique.Unc25G2
