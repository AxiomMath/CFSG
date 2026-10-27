module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer.Actor

section Conj

variable {G : Type} [Group G] {V : Subgroup G}

theorem map_conj_blockOf (R : Subgroup G) (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    (hLS : (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R).Normal) (D : Subgroup (MulAut V)) (t : G) :
    (blockOf (⊤ : Subgroup G) R V hX D).map (MulAut.conj t).toMonoidHom =
      blockOf (⊤ : Subgroup G) R V hX
        (D.map (MulAut.conj (rho V ⊤ hX ⟨t, Subgroup.mem_top t⟩)).toMonoidHom) := by
  unfold blockOf
  rw [oddOrderSubgroup_map_mulEquiv, Subgroup.map_inf _ _ _ (MulAut.conj t).injective,
    map_conj_rhoPreimage]
  have hnt : t ∈ Subgroup.normalizer
      ((oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hLS]
    exact Subgroup.mem_top t
  have h1 : (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R).map (MulAut.conj t).toMonoidHom =
      oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R := Subgroup.mem_normalizer_iff_map_conj_eq.1 hnt
  rw [h1]

end Conj

section Main

theorem delBlockImageProp
    : DelBlockImageProp := by
  intro G _ _ R M V n F _ r Lc ctx hcore hall
  have hS := ctx.setting
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hfam := del_family_data hS ctx.comps ctx.deleted
  have hnormV : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    hX (Subgroup.mem_top x)
  have hr : 0 < r := hbridge.r_pos
  obtain ⟨Fs0, P0, hP0⟩ := hall ⟨0, hr⟩
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set LS := L ⊔ baum R with hLS
  have hLSn : LS.Normal := hcore.normal
  have hker : LS ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 LS := hP0.ker.kernel.2
  have hDle : ∀ j, Lc j ≤ autOn (⊤ : Subgroup G) V := fun j => (ctx.comps.isComp j).1
  have hperf : ∀ j, Group.IsPerfect ↥(Lc j) := fun j => ⟨(ctx.comps.isComp j).2.2.1⟩
  have hperf' : ∀ j, ⁅Lc j, Lc j⁆ = Lc j := fun j => Subgroup.isPerfect_iff.1 (hperf j)
  have hLK : autOn L V = ⨆ j, Lc j := hbridge.K_eq.trans hbridge.K_prod
  have hLcle : ∀ j, Lc j ≤ autOn LS V := fun j =>
    (le_iSup Lc j).trans (hLK.symm.le.trans (autOn_le_autOn V le_sup_left))
  have hLnorm : ∀ j, autOn L V ≤ Subgroup.normalizer (Lc j : Set (MulAut V)) := by
    intro j
    rw [hLK]
    refine iSup_le fun i => ?_
    by_cases hij : i = j
    · subst hij
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (hbridge.commute i j hij)).trans (Subgroup.centralizer_le_normalizer _)
  have hLSnorm : ∀ j, autOn LS V ≤ Subgroup.normalizer (Lc j : Set (MulAut V)) := by
    intro j
    have hsup : autOn LS V = autOn L V ⊔ autOn (baum R) V := by
      rw [autOn_eq_map_conjNormal, autOn_eq_map_conjNormal, autOn_eq_map_conjNormal,
        Subgroup.map_sup]
    rw [hsup]
    exact sup_le (hLnorm j) (hfam.normS j)
  have hρ : ∀ j (x : G), x ∈ rhoPreimage V ⊤ hX (Lc j) ↔
      MulAut.conjNormal (H := V) x ∈ Lc j := fun j x => by
    rw [rhoPreimage_top_eq_comap, Subgroup.mem_comap]
  have hBdef : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) =
      oddOrderSubgroup (LS ⊓ rhoPreimage V ⊤ hX (Lc j)) := fun j => rfl
  have hGle : ∀ j, LS ⊓ rhoPreimage V ⊤ hX (Lc j) ≤ LS := fun j => inf_le_left
  have hBLS : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) ≤ LS := fun j =>
    (oddOrderSubgroup_le _).trans (hGle j)
  have hLSnormGj : ∀ j, LS ≤ Subgroup.normalizer ((LS ⊓ rhoPreimage V ⊤ hX (Lc j) :
      Subgroup G) : Set G) := by
    intro j
    refine le_normalizer_inf_of_le Subgroup.le_normalizer ?_
    rw [rhoPreimage_top_eq_comap]
    exact le_normalizer_comap_conjNormal (hLSnorm j)
  have hLSnormB : ∀ j, LS ≤ Subgroup.normalizer
      ((blockOf (⊤ : Subgroup G) R V hX (Lc j) : Subgroup G) : Set G) := fun j =>
    (hLSnormGj j).trans (normalizer_le_normalizer_oddOrderSubgroup _)
  have hnormB : ∀ j, ((blockOf (⊤ : Subgroup G) R V hX (Lc j)).subgroupOf LS).Normal := fun j =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hBLS j)).2 (hLSnormB j)
  have himgG : ∀ j, autOn (LS ⊓ rhoPreimage V ⊤ hX (Lc j)) V = Lc j := by
    intro j
    apply le_antisymm
    · intro φ hφ
      rw [autOn_eq_map_conjNormal] at hφ
      obtain ⟨x, hx, rfl⟩ := hφ
      exact (hρ j x).1 hx.2
    · intro φ hφ
      have h1 := hLcle j hφ
      rw [autOn_eq_map_conjNormal] at h1 ⊢
      obtain ⟨x, hx, rfl⟩ := h1
      exact ⟨x, ⟨hx, (hρ j x).2 hφ⟩, rfl⟩
  have himgB : ∀ j, autOn (blockOf (⊤ : Subgroup G) R V hX (Lc j)) V = Lc j := by
    intro j
    rw [hBdef, autOn_oddOrderSubgroup (hnormV _), himgG j]
    exact oddOrderSubgroup_eq_of_perfect (hperf j)
  have hρB : ∀ j, (blockOf (⊤ : Subgroup G) R V hX (Lc j)).map
      (MulAut.conjNormal (H := V)) = Lc j := fun j => by
    rw [← autOn_eq_map_conjNormal]
    exact himgB j
  refine ⟨hnormB, himgB, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i j hij
    apply ctx.comps.injective
    have h1 := congrArg (fun B => autOn B V) hij
    simp only [himgB] at h1
    exact h1
  ·
    intro t _ i
    have hφH : rho V ⊤ hX ⟨t, Subgroup.mem_top t⟩ ∈ autOn (⊤ : Subgroup G) V :=
      (mem_autOn_self_iff hX).2 ⟨⟨t, Subgroup.mem_top t⟩, rfl⟩
    have hcomp : IsComponentIn (Lc i) (autOn (⊤ : Subgroup G) V) :=
      (isComp_iff _ _).1 (ctx.comps.isComp i)
    have hHmap : (autOn (⊤ : Subgroup G) V).map
        (MulAut.conj (rho V ⊤ hX ⟨t, Subgroup.mem_top t⟩)).toMonoidHom =
        autOn (⊤ : Subgroup G) V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hφH)
    have hc2 := (isComponentIn_map_iff (MulAut.conj (rho V ⊤ hX ⟨t, Subgroup.mem_top t⟩))).2 hcomp
    rw [hHmap] at hc2
    obtain ⟨j, hj⟩ := ctx.comps.complete _ ((isComp_iff _ _).2 hc2)
    refine ⟨j, ?_⟩
    rw [map_conj_blockOf R hX hLSn (Lc i) t, ← hj]
  ·
    intro i j
    obtain ⟨t', ht', hconj⟩ := hbridge.transitive i j
    obtain ⟨p, hpR, rfl⟩ := (mem_autOn_iff_rho hX (le_top (a := R))).mp ht'
    refine ⟨(p : G), hpR, ?_⟩
    rw [map_conj_blockOf R hX hLSn (Lc i) (p : G), hconj]
  ·
    intro i
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnB := hLSnormB i
    have hle := hBLS i
    apply le_antisymm
    · have h1 : pCoreOf 2 (blockOf (⊤ : Subgroup G) R V hX (Lc i)) ≤ pCoreOf 2 LS :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hle)
          (hnB.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) h1
    · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 LS).to_le inf_le_right)
      exact le_normalizer_inf_of_le Subgroup.le_normalizer
        (hle.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 LS))
  ·
    intro i
    set B := blockOf (⊤ : Subgroup G) R V hX (Lc i) with hB
    have hBn : B ≤ Subgroup.normalizer (B : Set G) := Subgroup.le_normalizer
    have hDB : ⁅B, B⁆ ≤ B := commutator_le_of_le_normalizer hBn
    have hDn : (⁅B, B⁆.subgroupOf B).Normal := normal_commutator_subgroupOf hBn
    have hodd : oddOrderSubgroup B = B := by
      rw [hB, hBdef, oddOrderSubgroup_idem]
    have himg : B.map (MulAut.conjNormal (H := V)) ≤ (⁅B, B⁆).map (MulAut.conjNormal (H := V)) := by
      rw [hρB i, Subgroup.map_commutator, hρB i, hperf' i]
    exact eq_of_map_le_of_two_kernel (MulAut.conjNormal (H := V)) (hBLS i) hDB hDn hodd
      (fun x hx h1 => two_elt_of_conjNormal_eq_one hker hx h1) himg

end Main

end CFSG.QuasithinUnique.Setup.Lift
