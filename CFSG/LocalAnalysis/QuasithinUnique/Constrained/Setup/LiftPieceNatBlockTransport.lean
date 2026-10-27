module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Lift.Piece
open scoped commutatorElement

theorem natBlockTransportProp
    : NatBlockTransportProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hcore hcan
  classical
  have hS := ctx.setting
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hLSn := normal_L_sup_baum hS
  set L : Subgroup G := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set LS : Subgroup G := L ⊔ baum R with hLS
  set B : Subgroup G := oddOrderSubgroup P with hB
  have hBimg : autOn B V = Lc i := hcore.loc.K.image
  have hident : ∀ j, ∃ t ∈ R, autOn (B.map (MulAut.conj t).toMonoidHom) V = Lc j ∧
      blockOf (⊤ : Subgroup G) R V hX (Lc j) = B.map (MulAut.conj t).toMonoidHom := by
    intro j
    obtain ⟨t, ht, hj⟩ := hcan.surj j
    exact ⟨t, ht, hj, hcan.ident t ht j hj⟩
  have himg : ∀ j, autOn (blockOf (⊤ : Subgroup G) R V hX (Lc j)) V = Lc j := by
    intro j
    obtain ⟨t, ht, h1, h2⟩ := hident j
    rw [h2]
    exact h1
  have hBLS : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) ≤ LS := fun j =>
    (oddOrderSubgroup_le _).trans inf_le_left
  have hLSnorm : ∀ j, autOn LS V ≤ Subgroup.normalizer (Lc j : Set (MulAut V)) :=
    nat_autOn_LS_normalizer hS ctx.comps ctx.natural
  have hLSnormG : ∀ j, LS ≤ Subgroup.normalizer
      ((LS ⊓ rhoPreimage V ⊤ hX (Lc j) : Subgroup G) : Set G) := by
    intro j
    refine le_normalizer_inf_of_le Subgroup.le_normalizer ?_
    rw [rhoPreimage_top_eq_comap]
    exact le_normalizer_comap_conjNormal (hLSnorm j)
  have hLSnormB : ∀ j, LS ≤ Subgroup.normalizer
      ((blockOf (⊤ : Subgroup G) R V hX (Lc j) : Subgroup G) : Set G) := fun j =>
    (hLSnormG j).trans (normalizer_le_normalizer_oddOrderSubgroup _)
  have hnormB : ∀ j, ((blockOf (⊤ : Subgroup G) R V hX (Lc j)).subgroupOf LS).Normal := fun j =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hBLS j)).2 (hLSnormB j)
  have hlin : ∀ j, IsLin2Type (blockOf (⊤ : Subgroup G) R V hX (Lc j)) n := by
    intro j
    obtain ⟨t, ht, -, h2⟩ := hident j
    rw [h2]
    exact IsLin2Type.map_of_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
      hcore.ad.lin
  refine ⟨⟨?_, hnormB, ?_, ?_, ?_, ?_, ?_, himg, ?_⟩, hlin⟩
  ·
    intro j k hjk
    apply ctx.comps.injective
    have h1 := congrArg (fun B => autOn B V) hjk
    simp only [himg] at h1
    exact h1
  ·
    intro t _ j
    have hφH : rho V ⊤ hX ⟨t, Subgroup.mem_top t⟩ ∈ autOn (⊤ : Subgroup G) V :=
      (mem_autOn_self_iff hX).2 ⟨⟨t, Subgroup.mem_top t⟩, rfl⟩
    have hcomp : IsComponentIn (Lc j) (autOn (⊤ : Subgroup G) V) :=
      (isComp_iff _ _).1 (ctx.comps.isComp j)
    have hHmap : (autOn (⊤ : Subgroup G) V).map
        (MulAut.conj (rho V ⊤ hX ⟨t, Subgroup.mem_top t⟩)).toMonoidHom =
        autOn (⊤ : Subgroup G) V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hφH)
    have hc2 := (isComponentIn_map_iff (MulAut.conj (rho V ⊤ hX ⟨t, Subgroup.mem_top t⟩))).2 hcomp
    rw [hHmap] at hc2
    obtain ⟨k, hk⟩ := ctx.comps.complete _ ((isComp_iff _ _).2 hc2)
    refine ⟨k, ?_⟩
    rw [map_conj_blockOf R hX hLSn (Lc j) t, ← hk]
  ·
    intro j k
    obtain ⟨t', ht', hconj⟩ := (even_SL2_original_bridge hS ctx.comps).transitive j k
    obtain ⟨p, hpR, rfl⟩ := (mem_autOn_iff_rho hX (le_top (a := R))).mp ht'
    refine ⟨(p : G), hpR, ?_⟩
    rw [map_conj_blockOf R hX hLSn (Lc j) (p : G), hconj]
  ·
    intro j
    obtain ⟨t, ht, -, h2⟩ := hident j
    have hsub : ((blockOf (⊤ : Subgroup G) R V hX (Lc j)).subgroupOf (⊤ : Subgroup G)).IsSubnormal :=
      isSubnormal_trans (hBLS j) le_top (Subgroup.Normal.isSubnormal (hnormB j))
        (Subgroup.Normal.isSubnormal (hLSn.subgroupOf _))
    rw [h2] at hsub ⊢
    exact ⟨⟨Lin2.IsShort2.map_equiv hcore.ad.chi0.1.1 (MulAut.conj t), le_top, hsub⟩,
      Or.inl ⟨n, hS.two_le, h2 ▸ hlin j⟩⟩
  ·
    intro j
    obtain ⟨t, ht, -, h2⟩ := hident j
    rw [h2]
    have h1 : B ⊔ R = ⊤ := by
      rw [eq_top_iff, ← hcore.loc.basic.gen]
      refine sup_le ?_ le_sup_right
      calc P = B ⊔ baum R := hcore.res.P_eq
        _ ≤ B ⊔ R := sup_le_sup_left inf_le_left _
    have hRc : R.map (MulAut.conj t).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer ht)
    have h3 : (B ⊔ R).map (MulAut.conj t).toMonoidHom = B.map (MulAut.conj t).toMonoidHom ⊔ R := by
      rw [Subgroup.map_sup, hRc]
    have h4 : (B ⊔ R).map (MulAut.conj t).toMonoidHom = ⊤ := by
      rw [h1, Subgroup.map_top]
      exact MonoidHom.range_eq_top_of_surjective _ (MulAut.conj t).surjective
    exact (h3.symm.trans h4).symm
  ·
    intro j
    obtain ⟨t, ht, -, h2⟩ := hident j
    rw [h2]
    have hJc : (thompsonJ R).map (MulAut.conj t).toMonoidHom = thompsonJ R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (B6.le_normalizer_thompsonJ R ht)
    calc ⁅B.map (MulAut.conj t).toMonoidHom, thompsonJ R⁆ =
        ⁅B.map (MulAut.conj t).toMonoidHom, (thompsonJ R).map (MulAut.conj t).toMonoidHom⁆ := by
          rw [hJc]
      _ = (⁅B, thompsonJ R⁆).map (MulAut.conj t).toMonoidHom := (Subgroup.map_commutator _ _ _).symm
      _ = B.map (MulAut.conj t).toMonoidHom := by rw [hcore.res.perfect]
  ·
    intro j
    obtain ⟨t, ht, h1, h2⟩ := hident j
    rw [h2]
    have hIj : (modComm V (Lc i)).map (MulAut.conj t).toMonoidHom = modComm V (Lc j) := by
      rw [map_conj_modComm, ← h1, autOn_map_conj, hBimg]
    obtain ⟨hc1, hc2⟩ := hcore.sum.conj_comm t ht
    rw [hIj] at hc1 hc2
    exact ⟨hc2, hc1⟩

end CFSG.QuasithinUnique.Setup.Lift
