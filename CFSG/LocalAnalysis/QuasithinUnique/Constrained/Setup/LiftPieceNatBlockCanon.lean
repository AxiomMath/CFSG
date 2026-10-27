module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatTools

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

theorem natCanonicalProp
    : NatCanonicalProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hcore
  classical
  have hS := ctx.setting
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hLSn := normal_L_sup_baum hS
  set L : Subgroup G := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set LS : Subgroup G := L ⊔ baum R with hLS
  set B : Subgroup G := oddOrderSubgroup P with hB
  set Q : Subgroup G := pCoreOf 2 LS with hQ
  have hPLS : P ≤ LS := hcore.res.le_LS
  have hBLS : B ≤ LS := (oddOrderSubgroup_le P).trans hPLS
  have hBimg : autOn B V = Lc i := hcore.loc.K.image
  have hker : LS ⊓ Subgroup.centralizer (V : Set G) = Q := hcore.ker.kernel.2
  have hQ2 : IsPGroup 2 ↥Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 LS
  have hQB : Q ≤ Subgroup.normalizer (B : Set G) := hcore.q.normalizes
  have hρB : ∀ b ∈ B, MulAut.conjNormal (H := V) b ∈ Lc i := by
    intro b hb
    rw [← hBimg, autOn_eq_map_conjNormal]
    exact Subgroup.mem_map_of_mem _ hb
  have hB1 : blockOf (⊤ : Subgroup G) R V hX (Lc i) = B := by
    apply le_antisymm
    · unfold blockOf
      refine oddOrderSubgroup_le_of_pow_mem fun y hy => ?_
      have hyρ : MulAut.conjNormal (H := V) y ∈ Lc i := (mem_rhoPreimage_top_iff hX _ y).1 hy.2
      rw [← hBimg, autOn_eq_map_conjNormal] at hyρ
      obtain ⟨b, hbB, hby⟩ := hyρ
      have h1 : MulAut.conjNormal (H := V) (y * b⁻¹) = 1 := by
        rw [map_mul, map_inv, hby, mul_inv_cancel]
      have hyb : y * b⁻¹ ∈ LS ⊓ Subgroup.centralizer (V : Set G) :=
        ⟨LS.mul_mem hy.1 (LS.inv_mem (hBLS hbB)), conjNormal_eq_one_iff.1 h1⟩
      have hyQ : y * b⁻¹ ∈ Q := hker ▸ hyb
      have hyBQ : y ∈ B ⊔ Q := by
        have h1 : (y * b⁻¹) * b ∈ Q ⊔ B := Subgroup.mul_mem_sup hyQ hbB
        rw [inv_mul_cancel_right] at h1
        rwa [sup_comm] at h1
      exact exists_pow_mem_of_mem_sup_pGroup hQ2 hQB hyBQ
    · unfold blockOf
      refine Subgroup.closure_mono fun x hx => ⟨⟨hPLS hx.1, ?_⟩, hx.2⟩
      exact (mem_rhoPreimage_top_iff hX _ x).2 (hρB x (Subgroup.subset_closure hx))
  refine ⟨fun t ht j hj => ?_, fun j => ?_⟩
  · have h1 : autOn (B.map (MulAut.conj t).toMonoidHom) V =
        (Lc i).map (MulAut.conj (MulAut.conjNormal (H := V) t)).toMonoidHom := by
      rw [autOn_map_conj, hBimg]
    rw [h1] at hj
    have h2 := map_conj_blockOf R hX hLSn (Lc i) t
    rw [hB1, rho_top_eq_conjNormal hX t, hj] at h2
    exact h2.symm
  · obtain ⟨t', ht', hconj⟩ := hbridge.transitive i j
    obtain ⟨p, hpR, rfl⟩ := (mem_autOn_iff_rho hX (le_top (a := R))).mp ht'
    refine ⟨(p : G), hpR, ?_⟩
    have hρp : rho V ⊤ hX p = MulAut.conjNormal (H := V) (p : G) :=
      rho_top_eq_conjNormal hX (p : G)
    rw [hρp] at hconj
    rw [autOn_map_conj, hBimg]
    exact hconj

end CFSG.QuasithinUnique.Setup.Lift
