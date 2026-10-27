module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BMAut
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BMCore
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BMTwoA
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Monster.Existence CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H1017
  CFSG.HardMathSupport.Dickson.I271.TabMFive CFSG.Sporadic.Co1Schreier

open scoped Matrix

section Transport

variable {X Y : Type*} [Group X] [Group Y]

private theorem map_mem_center_map (e : X ≃* Y) {R : Subgroup X} {z : X}
    (hz : z ∈ (Subgroup.center ↥R).map R.subtype) :
    e z ∈ (Subgroup.center ↥(R.map e.toMonoidHom)).map (R.map e.toMonoidHom).subtype := by
  obtain ⟨hzR, hzc⟩ := mem_center_map_iff.1 hz
  refine mem_center_map_iff.2 ⟨⟨z, hzR, rfl⟩, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact (map_mul e r z).symm.trans ((congrArg e (hzc r hr)).trans (map_mul e z r))

private theorem extraspecial_map (e : X ≃* Y) {R : Subgroup X}
    (hR : timmesfeldIsExtraspecial ↥R) : timmesfeldIsExtraspecial ↥(R.map e.toMonoidHom) :=
  CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
    (R.equivMapOfInjective e.toMonoidHom e.injective) hR

end Transport


theorem i301BRow_of_M {row : Row} {p r k : ℕ} [Fact p.Prime] (hM : row.name = .M)
    (hp : row.prime = p) (hrow : row.rank = r + 1) (h3 : 3 ≤ row.r0exp) (hp2 : p ≠ 2)
    (hk : ∀ j, 0 < j → j < k → ¬ 2 ^ j ≡ 1 [MOD p]) (hBaby : TwoRankLe p .B (r - 1))
    (hrk : GLATwoLocalRank p ↥GA < r)
    (hfixB : ∀ F : Subgroup ↥GA, IsElemAbelian p F → Nat.card F = p ^ r →
      ∀ v : Fin 24 → ZMod 2, (∀ j ∈ F, ((j : GL (Fin 24) (ZMod 2)) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) → v = 0)
    (hfixH : ∀ F H : Subgroup ↥GA, IsElemAbelian p F → Nat.card F = p ^ r → H ≤ F →
      Nat.card H * p = Nat.card F → Nat.card {v : Fin 24 → ZMod 2 // ∀ j ∈ H,
        ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} ≤ 2 ^ k) :
    I301BRow row := by
  intro S _ _ hS B I K R0 R1 y _ hBe hBc _ _ _ _ _ _ hR0 hR0c _ _ hKB hR1 hKB1 h01
  rw [hM] at hS
  obtain ⟨Φ⟩ := nonempty_mulAut_equiv_MGriess S hS
  haveI : Finite MGriess := MGriess_finite_nonabelian_simple.1
  have hB : IsElemAbelian p B := hp ▸ hBe
  have hBc' : Nat.card B = p ^ r := by rw [hBc, hp, hrow, Nat.add_sub_cancel]
  have hR0e : timmesfeldIsExtraspecial ↥R0 := hR0.resolve_right fun h2 =>
    absurd (Nat.pow_le_pow_right two_pos h3) (by rw [← hR0c, h2]; norm_num)
  obtain ⟨c, hc1, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥R0)).mp hR0e.2.2.2
  have hz : ((c : ↥R0) : MulAut S) ∈ (Subgroup.center ↥R0).map R0.subtype := ⟨c, c.2, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : MulAut S ≃* MGriess, Ψ ((c : ↥R0) : MulAut S) = xGriess := by
    obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_xGriess_of_extraspecial hp2
      ((Nat.zero_le _).trans_lt hrk) hBaby (hB.map Φ.toMonoidHom)
      ((Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective).trans hBc')
      (extraspecial_map Φ hR0e) (map_mem_center_map Φ hz)
      (fun h => hc1 (Subtype.ext (Subtype.ext (Φ.injective (h.trans (map_one Φ).symm)))))
      ((Subgroup.map_mono (le_sup_right.trans hKB)).trans (Subgroup.le_normalizer_map _)))
    refine ⟨Φ.trans (MulAut.conj g⁻¹), ?_⟩
    show g⁻¹ * Φ ((c : ↥R0) : MulAut S) * g⁻¹⁻¹ = xGriess
    rw [← hg]
    group
  exact CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
    (R1.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).symm
    (extraspecial_of_xGriess hp2 hk hrk hfixB hfixH (A := (K ⊔ B).map Ψ.toMonoidHom)
      (B := B.map Ψ.toMonoidHom) (R0 := R0.map Ψ.toMonoidHom) (R1 := R1.map Ψ.toMonoidHom)
      (Subgroup.map_mono le_sup_right) (hB.map Ψ.toMonoidHom)
      ((Subgroup.card_map_of_injective (f := Ψ.toMonoidHom) Ψ.injective).trans hBc')
      (extraspecial_map Ψ hR0e) (hΨ ▸ map_mem_center_map Ψ hz)
      ((Subgroup.map_mono hKB).trans (Subgroup.le_normalizer_map _)) (hR1.map _)
      ((Subgroup.map_mono hKB1).trans (Subgroup.le_normalizer_map _))
      ((Subgroup.map_lt_map_iff_of_injective (f := Ψ.toMonoidHom) Ψ.injective).2 h01))

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
