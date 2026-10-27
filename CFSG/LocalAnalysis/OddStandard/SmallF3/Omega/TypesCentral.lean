module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesDecomp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma aux_conj_mul_self {G : Type*} [Group G] {g s : G} (hs : s * s = 1) :
    (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := by
  simp only [mul_assoc]
  rw [← mul_assoc g⁻¹ g (s * g⁻¹), inv_mul_cancel, one_mul]
  rw [← mul_assoc s s g⁻¹, hs, one_mul, mul_inv_cancel]

theorem mem_centralizer_iff_map_commSp (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (g : OGroup Q) :
    g ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) ↔
      (commSp s).map (g : V →ₗ[ZMod 3] V) = commSp s := by
  constructor
  · intro hg
    have hgs : g * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hconj : g * s * g⁻¹ = s := by rw [hgs]; group
    have hc := commSp_conj g s
    rw [hconj] at hc
    exact hc.symm
  · intro hmap
    have hgg : (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := aux_conj_mul_self hs
    have hcomm : commSp (g * s * g⁻¹) = commSp s := by rw [commSp_conj, hmap]
    have heq : g * s * g⁻¹ = s := eq_of_commSp_eq hQ hgg hs hcomm
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc g * s = (g * s * g⁻¹) * g := by group
      _ = s * g := by rw [heq]

theorem nonempty_centralizer_mulEquiv (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    Nonempty (↥(Subgroup.centralizer ({s} : Set (OGroup Q))) ≃*
      (OGroup (Q.restrict (commSp s)) × OGroup (Q.restrict (fixSp s)))) := by
  classical
  let C : Submodule (ZMod 3) V := fixSp s
  let N : Submodule (ZMod 3) V := commSp s
  have hcompl : IsCompl C N := by
    change IsCompl (fixSp s) (commSp s)
    exact isCompl_fixSp_commSp hs
  let e : ((Q.restrict C).prod (Q.restrict N)).IsometryEquiv Q :=
    { toLinearEquiv := Submodule.prodEquivOfIsCompl C N hcompl
      map_app' := by
        intro x
        change Q ((x.1 : V) + x.2) = Q (x.1 : V) + Q x.2
        rw [QuadraticMap.map_add Q, polar_fixSp_commSp hs x.1.2 x.2.2, add_zero] }
  let P : OGroup (Q.restrict C) × OGroup (Q.restrict N) →*
      OGroup ((Q.restrict C).prod (Q.restrict N)) :=
    QuadraticMap.orthogonalGroupProd (Q.restrict C) (Q.restrict N)
  let Φ : OGroup (Q.restrict C) × OGroup (Q.restrict N) →* OGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroupCongr e).toMonoidHom.comp P
  have hΦinj : Function.Injective Φ := by
    intro a b h
    have h1 : P a = P b := (TauCeti.QuadraticMap.orthogonalGroupCongr e).injective h
    exact QuadraticMap.orthogonalGroupProd_injective (Q.restrict C) (Q.restrict N) h1
  have hrange : Φ.range = Subgroup.centralizer ({s} : Set (OGroup Q)) := by
    apply le_antisymm
    · rintro y hy
      rw [MonoidHom.mem_range] at hy
      obtain ⟨p, rfl⟩ := hy
      rw [mem_centralizer_iff_map_commSp hQ hs]
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro x ⟨n, hn, rfl⟩
        have hmem : (Φ p : V ≃ₗ[ZMod 3] V) n =
            (((p.2 : N ≃ₗ[ZMod 3] N) ⟨n, hn⟩ : N) : V) := by
          change (TauCeti.QuadraticMap.orthogonalGroupCongr e (P p) : V ≃ₗ[ZMod 3] V) n = _
          rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]
          have hsnd : e.toLinearEquiv.symm n = (0, (⟨n, hn⟩ : N)) := by
            change (Submodule.prodEquivOfIsCompl C N hcompl).symm n = (0, (⟨n, hn⟩ : N))
            exact Submodule.prodEquivOfIsCompl_symm_apply_right C N hcompl (⟨n, hn⟩ : N)
          rw [hsnd, QuadraticMap.orthogonalGroupProd_apply]
          simp only [Prod.fst, Prod.snd, map_zero]
          change (Submodule.prodEquivOfIsCompl C N hcompl)
            (0, ((p.2 : N ≃ₗ[ZMod 3] N) ⟨n, hn⟩)) = _
          rw [Submodule.coe_prodEquivOfIsCompl']
          simp
        show (Φ p : V ≃ₗ[ZMod 3] V) n ∈ N
        rw [hmem]
        exact ((p.2 : N ≃ₗ[ZMod 3] N) ⟨n, hn⟩).2
      · rw [LinearEquiv.finrank_map_eq]
    · intro g hg
      have hgN : N.map (g : V →ₗ[ZMod 3] V) = N :=
        (mem_centralizer_iff_map_commSp hQ hs g).mp hg
      have hgs : g * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      have hgCl : C.map (g : V →ₗ[ZMod 3] V) ≤ C := by
        rintro x ⟨c, hc, rfl⟩
        rw [mem_fixSp_iff]
        have hgsL : (g : V ≃ₗ[ZMod 3] V) * (s : V ≃ₗ[ZMod 3] V) =
            (s : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) := by
          have h' := congrArg (fun u : OGroup Q => (u : V ≃ₗ[ZMod 3] V)) hgs
          simpa only [Subgroup.coe_mul] using h'
        calc (s : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) c)
            = ((s : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V)) c :=
              (LinearEquiv.mul_apply _ _ _).symm
          _ = ((g : V ≃ₗ[ZMod 3] V) * (s : V ≃ₗ[ZMod 3] V)) c := by rw [hgsL]
          _ = (g : V ≃ₗ[ZMod 3] V) ((s : V ≃ₗ[ZMod 3] V) c) :=
              LinearEquiv.mul_apply _ _ _
          _ = (g : V ≃ₗ[ZMod 3] V) c := by rw [mem_fixSp_iff.mp hc]
      have hgC : C.map (g : V →ₗ[ZMod 3] V) = C :=
        Submodule.eq_of_le_of_finrank_eq hgCl (by rw [LinearEquiv.finrank_map_eq])
      have hg' : (TauCeti.QuadraticMap.orthogonalGroupCongr e).symm g ∈
          (QuadraticMap.orthogonalGroupProd (Q.restrict C)
            (Q.restrict N)).range := by
        rw [QuadraticMap.mem_range_orthogonalGroupProd_iff]
        constructor
        · intro m₁
          rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_symm_apply]
          have hd : e.toLinearEquiv (m₁, 0) = (m₁ : V) := by
            change (Submodule.prodEquivOfIsCompl C N hcompl) (m₁, 0) = (m₁ : V)
            rw [Submodule.coe_prodEquivOfIsCompl']
            simp
          rw [hd]
          have hmem : (g : V ≃ₗ[ZMod 3] V) (m₁ : V) ∈ C := by
            have h1 : (g : V ≃ₗ[ZMod 3] V) (m₁ : V) ∈ C.map (g : V →ₗ[ZMod 3] V) :=
              Submodule.mem_map_of_mem m₁.2
            rwa [hgC] at h1
          change ((Submodule.prodEquivOfIsCompl C N hcompl).symm
            ((g : V ≃ₗ[ZMod 3] V) (m₁ : V))).2 = 0
          exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero C N hcompl).mpr hmem
        · intro m₂
          rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_symm_apply]
          have hd : e.toLinearEquiv (0, m₂) = (m₂ : V) := by
            change (Submodule.prodEquivOfIsCompl C N hcompl) (0, m₂) = (m₂ : V)
            rw [Submodule.coe_prodEquivOfIsCompl']
            simp
          rw [hd]
          have hmem : (g : V ≃ₗ[ZMod 3] V) (m₂ : V) ∈ N := by
            have h1 : (g : V ≃ₗ[ZMod 3] V) (m₂ : V) ∈ N.map (g : V →ₗ[ZMod 3] V) :=
              Submodule.mem_map_of_mem m₂.2
            rwa [hgN] at h1
          change ((Submodule.prodEquivOfIsCompl C N hcompl).symm
            ((g : V ≃ₗ[ZMod 3] V) (m₂ : V))).1 = 0
          exact (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero C N hcompl).mpr hmem
      obtain ⟨p, hp⟩ := hg'
      refine ⟨p, ?_⟩
      change TauCeti.QuadraticMap.orthogonalGroupCongr e
        ((QuadraticMap.orthogonalGroupProd (Q.restrict C) (Q.restrict N)) p) = g
      rw [hp]
      exact (TauCeti.QuadraticMap.orthogonalGroupCongr e).apply_symm_apply g
  refine ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((MonoidHom.ofInjective hΦinj).symm.trans MulEquiv.prodComm)⟩

end CFSG.OddStandard.SmallF3.Omega
