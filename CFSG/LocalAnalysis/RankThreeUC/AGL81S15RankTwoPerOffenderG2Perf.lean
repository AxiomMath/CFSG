module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base11
public import CFSG.Quasithin.Vol2.Ch11G2Q8InvLong
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.SecB.K5
  CFSG.Quasithin.Vol2.Ch11.G2Q8 Matrix

private def g2p_toSix {F : Type} (w : Ix3 → F) : Fin 6 → F := fun i => w (e6.symm i)

private def g2p_ofSix {F : Type} (u : Fin 6 → F) : Ix3 → F := fun k => u (e6 k)

private theorem g2p_toSix_ofSix {F : Type} (u : Fin 6 → F) : g2p_toSix (g2p_ofSix u) = u := by
  funext i
  simp [g2p_ofSix, g2p_toSix]

private theorem g2p_mulVec_g2Six {F : Type} [Field F] [CharP F 2] (g : ↥(cayleyGroup F))
    (w : Ix3 → F) :
    ((g2Six (K := F) g : Matrix.GeneralLinearGroup (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) *ᵥ g2p_toSix w = g2p_toSix (g2Act g w) := by
  have hM : ((g2Six (K := F) g : Matrix.GeneralLinearGroup (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) =
      ((g2Mat g : Matrix.GeneralLinearGroup Ix3 F) : Matrix Ix3 Ix3 F).submatrix
        e6.symm e6.symm := rfl
  rw [hM, Matrix.submatrix_mulVec_equiv]
  funext i
  have hw : g2p_toSix w ∘ (e6.symm).symm = w := by
    funext k
    simp [g2p_toSix]
  simp only [Function.comp_apply, g2p_toSix]
  rw [hw]
  have := congrFun (g2Mat_mulVec g w) (e6.symm i)
  simpa [g2p_toSix] using this

private theorem g2p_stabL_map_conj {L : Type*} [Group L] {F : Type} [Field F] {r : ℕ}
    (Mat : L →* Matrix.GeneralLinearGroup (Fin r) F) (g : L) (u : Fin r → F) :
    (stabL Mat u).map (MulAut.conj g).toMonoidHom =
      stabL Mat ((Mat g : Matrix (Fin r) (Fin r) F) *ᵥ u) := by
  have hcoeg : ∀ x : L, (Mat (MulAut.conj g x) : Matrix (Fin r) (Fin r) F) =
      (Mat g : Matrix (Fin r) (Fin r) F) * (Mat x : Matrix (Fin r) (Fin r) F) *
        (Mat g : Matrix (Fin r) (Fin r) F)⁻¹ := by
    intro x
    simp only [MulAut.conj_apply, map_mul, map_inv,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]
  have hinv : ∀ w : Fin r → F,
      ((Mat g : Matrix (Fin r) (Fin r) F))⁻¹ *ᵥ
          ((Mat g : Matrix (Fin r) (Fin r) F) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_inv,
      ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  ext s
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    change (Mat (MulAut.conj g a) : Matrix (Fin r) (Fin r) F) *ᵥ
      ((Mat g : Matrix (Fin r) (Fin r) F) *ᵥ u) =
        (Mat g : Matrix (Fin r) (Fin r) F) *ᵥ u
    rw [hcoeg a, ← Matrix.mulVec_mulVec, hinv, ← Matrix.mulVec_mulVec, ha]
  · intro hs
    refine ⟨g⁻¹ * s * g, ?_, ?_⟩
    · have hcs : (Mat (g⁻¹ * s * g) : Matrix (Fin r) (Fin r) F) =
          ((Mat g : Matrix (Fin r) (Fin r) F))⁻¹ * (Mat s : Matrix (Fin r) (Fin r) F) *
            (Mat g : Matrix (Fin r) (Fin r) F) := by
        simp only [map_mul, map_inv, Matrix.GeneralLinearGroup.coe_mul,
          Matrix.GeneralLinearGroup.coe_inv]
      change (Mat (g⁻¹ * s * g) : Matrix (Fin r) (Fin r) F) *ᵥ u = u
      rw [hcs, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, hinv]
    · show MulAut.conj g (g⁻¹ * s * g) = s
      rw [MulAut.conj_apply]
      group

private theorem g2p_stabL_zero {F : Type} [Field F] [CharP F 2] :
    stabL (g2Six (K := F)) (0 : Fin 6 → F) = ⊤ := by
  ext g
  simp [stabL, Matrix.mulVec_zero]

private theorem g2p_cayley_perfect {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) : Group.IsPerfect ↥(cayleyGroup F) := by
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.Vol2.KGNat.exists_ne_zero_ne_one (K := F) (by omega)
  refine Subgroup.isPerfect_iff.mpr ?_
  have h := g2Derived_eq (K := F) hc0 hc1
  rwa [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup] at h

private theorem g2p_stabL_g2Six_e0 {F : Type} [Field F] [CharP F 2] :
    stabL (g2Six (K := F)) (g2p_toSix (eu 0 1)) = stabV0 F := by
  ext g
  rw [mem_stabV0]
  change ((g2Six (K := F) g : Matrix.GeneralLinearGroup (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) *ᵥ g2p_toSix (eu 0 1) = g2p_toSix (eu 0 1) ↔
    g2Act g (eu 0 1) = eu 0 1
  rw [g2p_mulVec_g2Six]
  constructor
  · intro h
    funext k
    have := congrFun h (e6 k)
    simpa [g2p_toSix] using this
  · intro h
    rw [h]

theorem g2_perfStab {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    PerfStab (g2Six (K := F)) := by
  intro u
  by_cases hu : u = 0
  · rw [hu, g2p_stabL_zero]
    exact (g2p_cayley_perfect h4).commutator_eq_top
  · have hw : g2p_ofSix u ≠ 0 := by
      intro h
      apply hu
      rw [← g2p_toSix_ofSix u, h]
      rfl
    obtain ⟨g, hg⟩ := exists_g2Act_eu_eq (F := F) hw
    have hgu : ((g2Six (K := F) g : Matrix.GeneralLinearGroup (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) *ᵥ g2p_toSix (eu 0 1) = u := by
      rw [g2p_mulVec_g2Six, hg, g2p_toSix_ofSix]
    have hstab : stabL (g2Six (K := F)) u =
        (stabL (g2Six (K := F)) (g2p_toSix (eu 0 1))).map
          (MulAut.conj g).toMonoidHom := by
      have h := g2p_stabL_map_conj (g2Six (K := F)) g (g2p_toSix (eu 0 1))
      rw [hgu] at h
      exact h.symm
    rw [hstab, ← Subgroup.map_commutator]
    rw [g2p_stabL_g2Six_e0, stabV0_perfect h4]

end CFSG.LocalAnalysis.RankThreeUC.S15

end
