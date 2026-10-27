module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421Mono
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bTrans

public section

open scoped Pointwise

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421MonoProof

theorem sylow_smul_coe {G : Type} [Group G] (g : G) (P : Sylow 3 G) :
    ((g • P : Sylow 3 G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

variable {G : Type} [Group G] [Finite G] (D : Mono81 G)

theorem Mono81.exists_conj_le_A0' {k : ℕ} (hk3 : ¬ 3 ∣ k) (hk : Nat.card G = 81 * k)
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 3 E) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ D.A0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  obtain ⟨P, hEP⟩ := hp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P (D.sylow hk3 hk)
  have hP : (P : Subgroup G).map (MulAut.conj h).toMonoidHom = D.R0 := by
    rw [← sylow_smul_coe, hh, D.coe_sylow]
  have hER : E.map (MulAut.conj h).toMonoidHom ≤ D.R0 := by
    rw [← hP]
    exact Subgroup.map_mono hEP
  have hE' : CFSG.Open.IsElemAbelian 3 (E.map (MulAut.conj h).toMonoidHom) :=
    K21bTransProof.isElemAbelian_map_inj (MulAut.conj h).injective hE
  rcases D.exists_conj_le_A0 hER hE' with hA | ⟨-, g', hg'⟩
  · exact ⟨h, hA⟩
  · refine ⟨g' * h, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have := hg' (Subgroup.mem_map.mpr ⟨(MulAut.conj h) z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, rfl⟩)
    have h1 : (MulAut.conj (g' * h)) z = (MulAut.conj g') ((MulAut.conj h) z) := by
      simp [MulAut.conj_apply, mul_assoc]
    show (MulAut.conj (g' * h)) z ∈ D.A0
    rw [h1]
    exact this

end K421MonoProof

end CFSG.LocalAnalysis.RankThreeUC.S15
