module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S12EightB
public import CFSG.LargeExtraspecial.S12EightC
public import CFSG.LargeExtraspecial.S12Fuse
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] {S : Setting G}

theorem span_orbit_eq_top_or {v : S.Qt} (hv : v ≠ 0) :
    Submodule.span (ZMod 2) (Set.range fun m : S.M => (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = ⊤ ∨
      S.IsReducible12 := by
  set W := Submodule.span (ZMod 2) (Set.range fun m : S.M => (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
  by_cases hW : W = ⊤
  · exact Or.inl hW
  right
  have hvW : v ∈ W := Submodule.subset_span ⟨1, by simp⟩
  refine ⟨W, fun h => hv ((Submodule.mem_bot _).mp (h ▸ hvW)), hW, fun m w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m', rfl⟩ := hx
    refine Submodule.subset_span ⟨m * m', ?_⟩
    simp only [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]
  | zero => rw [map_zero]; exact W.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact W.smul_mem c hx

theorem rho_mem_clSub_of_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (h : S.M) (hfix : ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹)) {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  have h1 := S.s12_rho_mem_clSub h hv
  rw [S.ρ_cl h haQ] at hfix
  rcases (S.cl_eq_cl_iff haQ (S.conj_mem_QG h.2 haQ)).mp hfix.symm with e | e
  · rwa [S.Qa_eq_of_conj_eq ((S.s12_mul_conj_z _ _).trans e)] at h1
  · obtain ⟨u, huQ, hu⟩ := S.exists_conj_eq_mul_z haQ (S.s12_conj_z_ne_one g) hne
    have hug : (h : G) * g * S.z * ((h : G) * g)⁻¹ = u * g * S.z * (u * g)⁻¹ := by
      rw [S.s12_mul_conj_z, S.s12_mul_conj_z, e, hu]
    rw [S.Qa_eq_of_conj_eq hug] at h1
    set uM : S.M := ⟨u, S.QG_le_M huQ⟩
    have h2 := S.s12_rho_mem_clSub uM⁻¹ h1
    have hρ : S.ρ uM⁻¹ = 1 := (S.ρ_eq_one_iff _).mpr (S.QG.inv_mem huQ)
    rw [hρ] at h2
    have e3 : ((uM⁻¹ : S.M) : G) * (u * g) = g := by
      change u⁻¹ * (u * g) = g
      group
    rw [e3] at h2
    exact h2

theorem rho_cl_conj {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (h : S.M) :
    ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (((h : G) * g) * S.z * ((h : G) * g)⁻¹) := by
  rw [S.ρ_cl h haQ, S.s12_mul_conj_z]

@[expose] def S12RankThree (S : Setting G) (g : G) : Prop :=
  ∀ h₁ h₂ : S.M,
    ((S.ρ h₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ S.cl (g * S.z * g⁻¹) →
    ((S.ρ h₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ S.cl (g * S.z * g⁻¹) →
    polar S.q (S.cl (g * S.z * g⁻¹))
      (((S.ρ h₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0 →
    polar S.q (S.cl (g * S.z * g⁻¹))
      (((S.ρ h₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0 →
    ∃ k : S.M,
      ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) ∧
      ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (((S.ρ h₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
        ((S.ρ h₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))

theorem rho_cl_ne_zero {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (h : S.M) : ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ 0 := fun e =>
  S.s12_cl_ne_zero_of_conj haQ hne
    (((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).map_eq_zero_iff.mp e)

theorem rho_inv_mul_apply (h h' : S.M) (v : S.Qt) :
    ((S.ρ (h⁻¹ * h') : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm (((S.ρ h' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply]
  rfl

theorem orbit_mem_clSub_of_rank {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hrank : S.S12RankThree g) {h₀ : S.M}
    (hb0 : ((S.ρ h₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      S.clSub (S.QG ⊓ S.Qa g))
    (hb0ne : ((S.ρ h₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      S.cl (g * S.z * g⁻¹)) {h : S.M}
    (hne' : ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ S.cl (g * S.z * g⁻¹))
    (hpol : polar S.q (S.cl (g * S.z * g⁻¹))
      (((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0) :
    ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  have hpol0 := S.s12_polar_clSub_QG_inf_Qa hne (S.s12_cl_a_mem_clSub haQ) hb0
  obtain ⟨k, hk1, hk2⟩ := hrank h₀ h hb0ne hne' hpol0 hpol
  rw [← hk2]
  exact rho_mem_clSub_of_fix haQ hne k hk1 hb0

theorem orbit_mem_clSub_of_rank' {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hrank : S.S12RankThree g) {h₀ : S.M}
    (hb0 : ((S.ρ h₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      S.clSub (S.QG ⊓ S.Qa g))
    (hb0ne : ((S.ρ h₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      S.cl (g * S.z * g⁻¹)) (hc h : S.M)
    (hne' : ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      ((S.ρ hc : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
    (hpol : polar S.q (((S.ρ hc : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
      (((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0) :
    ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      S.clSub (S.QG ⊓ S.Qa ((hc : G) * g)) := by
  set a := S.cl (g * S.z * g⁻¹)
  set ec := ((S.ρ hc : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have h1 : ((S.ρ (hc⁻¹ * h) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    refine orbit_mem_clSub_of_rank haQ hne hrank hb0 hb0ne ?_ ?_
    · rw [rho_inv_mul_apply]
      intro e
      apply hne'
      have := congrArg ec e
      rwa [LinearEquiv.apply_symm_apply] at this
    · rw [rho_inv_mul_apply]
      have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ hc).2 a
        (ec.symm (((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a))
      change polar S.q (ec a) (ec (ec.symm _)) = _ at hiso
      rw [LinearEquiv.apply_symm_apply] at hiso
      rw [← hiso]
      exact hpol
  have h2 := S.s12_rho_mem_clSub hc h1
  rw [rho_inv_mul_apply] at h2
  change ec (ec.symm _) ∈ _ at h2
  rwa [LinearEquiv.apply_symm_apply] at h2

theorem polar_orbit_eq_zero_of_rank {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hrank : S.S12RankThree g) {h₀ : S.M}
    (hb0 : ((S.ρ h₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      S.clSub (S.QG ⊓ S.Qa g))
    (hb0ne : ((S.ρ h₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      S.cl (g * S.z * g⁻¹)) (hc hd he : S.M)
    (hcd : ((S.ρ hc : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      ((S.ρ hd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
    (hed : ((S.ρ he : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      ((S.ρ hd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
    (hpc : polar S.q (((S.ρ hd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
      (((S.ρ hc : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0)
    (hpe : polar S.q (((S.ρ hd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
      (((S.ρ he : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0) :
    polar S.q (((S.ρ hc : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
      (((S.ρ he : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0 := by
  have hcm := orbit_mem_clSub_of_rank' haQ hne hrank hb0 hb0ne hd hc hcd hpc
  have hem := orbit_mem_clSub_of_rank' haQ hne hrank hb0 hb0ne hd he hed hpe
  obtain ⟨c', hc'X, hc'Q, hc'e⟩ := S.mem_clSub_iff.mp hcm
  obtain ⟨e', he'X, he'Q, he'e⟩ := S.mem_clSub_iff.mp hem
  rw [← hc'e, ← he'e]
  by_contra hp
  have hnc : ¬ c' * e' = e' * c' := fun h => hp ((S.polar_cl_eq_zero_iff hc'Q he'Q).mpr h)
  have hz : c' * e' = S.z * (e' * c') := (S.mul_comm_or hc'Q he'Q).resolve_left hnc
  set T := S.conjBy ((hd : G) * g)
  have hT : c' * e' = T.z * (e' * c') :=
    (T.mul_comm_or (x := c') (y := e') hc'X.2 he'X.2).resolve_left hnc
  have hzd : S.z = ((hd : G) * g) * S.z * ((hd : G) * g)⁻¹ := by
    have := hz.symm.trans hT
    exact mul_right_cancel this
  apply rho_cl_ne_zero haQ hne hd
  rw [rho_cl_conj haQ hd, ← hzd]
  exact (S.cl_eq_zero_iff S.z_mem_QG).mpr (Or.inr rfl)

theorem timmesfeld_12_14_inter {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hirr : ¬ S.IsReducible12) (hrank : S.S12RankThree g)
    (h₀ : S.M) (hb0 : ((S.ρ h₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      S.clSub (S.QG ⊓ S.Qa g)) :
    ((S.ρ h₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  set a := S.cl (g * S.z * g⁻¹) with ha
  set b := ((S.ρ h₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a with hb
  by_contra hb0ne
  have ha0 : a ≠ 0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hab : polar S.q a b = 0 :=
    S.s12_polar_clSub_QG_inf_Qa hne (S.s12_cl_a_mem_clSub haQ) hb0
  have hρ1 : ((S.ρ (1 : S.M) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a := by simp
  have hB := polar_orbit_eq_zero_of_rank haQ hne hrank hb0 hb0ne
  have horth : ∀ m : S.M, polar S.q (a + b) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a) = 0 := by
    intro m
    set e := ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a with he
    rw [polar_add_left]
    by_cases hea : polar S.q a e = 0
    · have hbe : polar S.q b e = 0 := by
        by_cases hea' : e = a
        · rw [hea', polar_comm]
          exact hab
        · have := hB h₀ 1 m (by rw [hρ1]; exact hb0ne) (by rw [hρ1]; exact hea')
            (by rw [hρ1]; exact hab) (by rw [hρ1]; exact hea)
          exact this
      rw [hea, hbe, add_zero]
    · have hbe : polar S.q b e ≠ 0 := by
        intro hbe
        have heb : e ≠ b := by
          intro heb'
          rw [heb'] at hea
          exact hea hab
        have := hB 1 h₀ m (by rw [hρ1]; exact Ne.symm hb0ne) heb
          (by rw [hρ1, polar_comm]; exact hab) hbe
        rw [hρ1] at this
        exact hea this
      have h1 : polar S.q a e = 1 := by
        rcases OrthoF2.zmod2_eq_zero_or_eq_one (polar S.q a e) with h | h
        · exact absurd h hea
        · exact h
      have h2 : polar S.q b e = 1 := by
        rcases OrthoF2.zmod2_eq_zero_or_eq_one (polar S.q b e) with h | h
        · exact absurd h hbe
        · exact h
      rw [h1, h2]
      rfl
  have hspan := (span_orbit_eq_top_or ha0).resolve_right hirr
  have hker : ∀ w : S.Qt, S.q.polarBilin (a + b) w = 0 := by
    intro w
    have hw : w ∈ Submodule.span (ZMod 2)
        (Set.range fun m : S.M => ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a) := hspan ▸ trivial
    have hle : Submodule.span (ZMod 2)
        (Set.range fun m : S.M => ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a) ≤
        LinearMap.ker (S.q.polarBilin (a + b)) := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact horth m
    exact hle hw
  have hab0 : a + b = 0 := S.q_nondegenerate.1 _ hker
  apply hb0ne
  have : b = -a := eq_neg_of_add_eq_zero_right hab0
  rw [this]
  exact OrthoF2.vec_neg a

end Setting

end CFSG.LargeExtraspecial
