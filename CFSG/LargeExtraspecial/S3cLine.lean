module

public import CFSG.LargeExtraspecial.S3cDFour
public import CFSG.LargeExtraspecial.S3cIota

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2

universe u

theorem eq_zero_of_add_add {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {u₁ u₂ e : V}
    (h : u₁ + e + (u₂ + e) = u₁ + u₂ + e) : e = 0 := by
  have e5 : u₁ + e + (u₂ + e) = u₁ + u₂ + (e + e) := by abel
  rw [e5, vec_add_self, add_zero] at h
  simpa using h.symm

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem mem_Qa_of_cl_mem {g c : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hcQ : c ∈ S.QG) (hc : S.cl c ∈ S.clSub (S.QG ⊓ S.Qa g)) : c ∈ S.Qa g := by
  obtain ⟨x, hx, hxQ, hxc⟩ := S.mem_clSub_iff.mp hc
  rcases (S.cl_eq_cl_iff hxQ hcQ).mp hxc with h1 | h1
  · rw [h1]
    exact hx.2
  · rw [h1]
    exact (S.Qa g).mul_mem hx.2 (S.z_mem_Qa haQ hne)

theorem exists_mem_Dbar_mul {g k : G} (hk : k ∈ S.M) (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (ht : t ∈ S.Dbar g) (ht1 : t ≠ 1) : ∃ t' ∈ S.Dbar (k * g), t' ≠ 1 := by
  refine ⟨_, S.conj_mem_Dbar_mul hk haQ ht, fun h1 => ht1 ?_⟩
  calc t = (S.ρ ⟨k, hk⟩)⁻¹ * (S.ρ ⟨k, hk⟩ * t * (S.ρ ⟨k, hk⟩)⁻¹) * S.ρ ⟨k, hk⟩ := by group
    _ = 1 := by rw [h1]; group

theorem exists_cl_eq_add_cl (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width)
    {g h : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) {t : S.O} (ht : t ∈ S.Dbar g) (ht1 : t ≠ 1) (hh : h ∈ S.M)
    (hab : g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹))
    (hba : S.cl ((h * g) * S.z * (h * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹)) :
    ∃ k ∈ S.M, S.cl ((k * g) * S.z * (k * g)⁻¹) =
      S.cl ((h * g) * S.z * (h * g)⁻¹) + S.cl (g * S.z * g⁻¹) := by
  have hbQ := S.conj_mul_mem_QG hh haQ
  obtain ⟨s, hsL, hs⟩ : ∃ s ∈ S.Lbar g, (s : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹) + S.cl (g * S.z * g⁻¹) := by
    by_cases hbQa : (h * g) * S.z * (h * g)⁻¹ ∈ S.Qa g
    · have C := S.transvectionConfig hTI hn haQ hne hno hirr
      have hbW : S.cl ((h * g) * S.z * (h * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) :=
        S.cl_mem_clSub ⟨hbQ, hbQa⟩ hbQ
      have hw0 : (Submodule.Quotient.mk (⟨_, hbW⟩ : S.clSub (S.QG ⊓ S.Qa g)) :
          S.clSub (S.QG ⊓ S.Qa g) ⧸ C.lineW) ≠ 0 := by
        intro h0
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
          ((Submodule.Quotient.mk_eq_zero _).mp h0)
        have hc' : c • S.cl (g * S.z * g⁻¹) = S.cl ((h * g) * S.z * (h * g)⁻¹) :=
          congrArg Subtype.val hc
        rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
        · rw [zero_smul] at hc'
          exact S.cl_conj_z_ne_zero hbQ (S.conj_mul_ne_z hh hne) hc'.symm
        · rw [one_smul] at hc'
          exact hba hc'.symm
      obtain ⟨φ, hφ⟩ : ∃ φ : C.K, φ (Submodule.Quotient.mk ⟨_, hbW⟩) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hw0 ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp hcon)
      obtain ⟨s, hs, hse⟩ := S.mem_LbarLin_iff.mp (C.sOf_mem φ)
      refine ⟨s, hs, ?_⟩
      have h1 := C.sOf_apply φ ⟨_, hbW⟩
      rw [zmod2_eq_one_of_ne_zero hφ, one_smul] at h1
      rw [hse]
      exact h1
    · exact ⟨t, ht.1,
        S.apply_cl_eq_add_of_not_mem_Qa hTI hn haQ hne hno hirr hh hab hbQa ht ht1⟩
  obtain ⟨y, hys⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar g hsL)
  refine ⟨(y : G) * h, S.M.mul_mem y.2 hh, ?_⟩
  rw [← hs, ← hys, S.ρ_cl y hbQ]
  congr 1
  group

theorem exists_cl_eq_add (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width)
    {g k₁ k₂ : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) {t : S.O} (ht : t ∈ S.Dbar g)
    (ht1 : t ≠ 1) (hk₁ : k₁ ∈ S.M) (hk₂ : k₂ ∈ S.M)
    (hc : (k₁ * g) * S.z * (k₁ * g)⁻¹ * ((k₂ * g) * S.z * (k₂ * g)⁻¹) =
      (k₂ * g) * S.z * (k₂ * g)⁻¹ * ((k₁ * g) * S.z * (k₁ * g)⁻¹))
    (h12 : S.cl ((k₁ * g) * S.z * (k₁ * g)⁻¹) ≠ S.cl ((k₂ * g) * S.z * (k₂ * g)⁻¹)) :
    ∃ k ∈ S.M, S.cl ((k * g) * S.z * (k * g)⁻¹) =
      S.cl ((k₁ * g) * S.z * (k₁ * g)⁻¹) + S.cl ((k₂ * g) * S.z * (k₂ * g)⁻¹) := by
  obtain ⟨t', ht', ht'1⟩ := S.exists_mem_Dbar_mul hk₁ haQ ht ht1
  have hh : k₂ * k₁⁻¹ ∈ S.M := S.M.mul_mem hk₂ (S.M.inv_mem hk₁)
  have e : k₂ * k₁⁻¹ * (k₁ * g) = k₂ * g := by group
  obtain ⟨k, hk, hkeq⟩ := S.exists_cl_eq_add_cl hTI hn (S.conj_mul_mem_QG hk₁ haQ)
    (S.conj_mul_ne_z hk₁ hne) (fun h1 => hno (S.hasTypeAInL_of_mul hk₁ h1)) hirr ht' ht'1 hh
    (by rw [e]; exact hc) (by rw [e]; exact h12.symm)
  rw [e] at hkeq
  refine ⟨k * k₁, S.M.mul_mem hk hk₁, ?_⟩
  rw [mul_assoc k k₁ g, hkeq, add_comm]

theorem not_mem_Qa_of_not_commute {g ke kc : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hke : ke ∈ S.M) (hkc : kc ∈ S.M)
    (hae : g * S.z * g⁻¹ * ((ke * g) * S.z * (ke * g)⁻¹) ≠
      (ke * g) * S.z * (ke * g)⁻¹ * (g * S.z * g⁻¹))
    (hcQa : (kc * g) * S.z * (kc * g)⁻¹ ∈ S.Qa g)
    (hce : (kc * g) * S.z * (kc * g)⁻¹ * ((ke * g) * S.z * (ke * g)⁻¹) =
      (ke * g) * S.z * (ke * g)⁻¹ * ((kc * g) * S.z * (kc * g)⁻¹)) :
    (kc * g) * S.z * (kc * g)⁻¹ ∉ S.Qa (ke * g) := by
  intro hcQe
  have heQ := S.conj_mul_mem_QG hke haQ
  have hca : (kc * g) * S.z * (kc * g)⁻¹ ≠ g * S.z * g⁻¹ := by
    intro h1
    rw [h1] at hce
    exact hae hce
  have hce' : (kc * g) * S.z * (kc * g)⁻¹ ≠ (ke * g) * S.z * (ke * g)⁻¹ := by
    intro h1
    rw [h1] at hcQa
    exact hae (S.QG_inf_Qa_comm hne ⟨haQ, S.conj_z_mem_Qa g⟩ ⟨heQ, hcQa⟩)
  have haQc := S.mem_Qa_symm hca hcQa
  have heQc := S.mem_Qa_symm hce' hcQe
  exact hae (S.QG_inf_Qa_comm (S.conj_mul_ne_z hkc hne) ⟨haQ, haQc⟩ ⟨heQ, heQc⟩)

theorem apply_cl_eq_add_of_not_mem_Qa_mul (hTI : WeaklyClosedTITransitive.{u})
    (hn : 3 ≤ S.width) {g k₀ k : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) (hk₀ : k₀ ∈ S.M) (hk : k ∈ S.M)
    (hab : (k₀ * g) * S.z * (k₀ * g)⁻¹ * ((k * g) * S.z * (k * g)⁻¹) =
      (k * g) * S.z * (k * g)⁻¹ * ((k₀ * g) * S.z * (k₀ * g)⁻¹))
    (hbQa : (k * g) * S.z * (k * g)⁻¹ ∉ S.Qa (k₀ * g)) {t : S.O} (ht : t ∈ S.Dbar (k₀ * g))
    (ht1 : t ≠ 1) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k * g) * S.z * (k * g)⁻¹)) =
      S.cl ((k * g) * S.z * (k * g)⁻¹) + S.cl ((k₀ * g) * S.z * (k₀ * g)⁻¹) := by
  have hh : k * k₀⁻¹ ∈ S.M := S.M.mul_mem hk (S.M.inv_mem hk₀)
  have e : k * k₀⁻¹ * (k₀ * g) = k * g := by group
  have := S.apply_cl_eq_add_of_not_mem_Qa hTI hn (S.conj_mul_mem_QG hk₀ haQ)
    (S.conj_mul_ne_z hk₀ hne) (fun h1 => hno (S.hasTypeAInL_of_mul hk₀ h1)) hirr hh
    (by rw [e]; exact hab) (by rw [e]; exact hbQa) ht ht1
  rwa [e] at this

theorem false_of_two_points (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width)
    {g ke k₁ k₂ : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) {t : S.O} (ht : t ∈ S.Dbar g)
    (ht1 : t ≠ 1) (hke : ke ∈ S.M) (hk₁ : k₁ ∈ S.M) (hk₂ : k₂ ∈ S.M)
    (hae : g * S.z * g⁻¹ * ((ke * g) * S.z * (ke * g)⁻¹) ≠
      (ke * g) * S.z * (ke * g)⁻¹ * (g * S.z * g⁻¹))
    (hc₁ : (k₁ * g) * S.z * (k₁ * g)⁻¹ ∈ S.Qa g) (hc₂ : (k₂ * g) * S.z * (k₂ * g)⁻¹ ∈ S.Qa g)
    (hc₁e : (k₁ * g) * S.z * (k₁ * g)⁻¹ * ((ke * g) * S.z * (ke * g)⁻¹) =
      (ke * g) * S.z * (ke * g)⁻¹ * ((k₁ * g) * S.z * (k₁ * g)⁻¹))
    (hc₂e : (k₂ * g) * S.z * (k₂ * g)⁻¹ * ((ke * g) * S.z * (ke * g)⁻¹) =
      (ke * g) * S.z * (ke * g)⁻¹ * ((k₂ * g) * S.z * (k₂ * g)⁻¹))
    (h12 : S.cl ((k₁ * g) * S.z * (k₁ * g)⁻¹) ≠ S.cl ((k₂ * g) * S.z * (k₂ * g)⁻¹)) :
    False := by
  have heQ := S.conj_mul_mem_QG hke haQ
  have hc₁Q := S.conj_mul_mem_QG hk₁ haQ
  have hc₂Q := S.conj_mul_mem_QG hk₂ haQ
  obtain ⟨k₃, hk₃, hk₃eq⟩ := S.exists_cl_eq_add hTI hn haQ hne hno hirr ht ht1 hk₁ hk₂
    (S.QG_inf_Qa_comm hne ⟨hc₁Q, hc₁⟩ ⟨hc₂Q, hc₂⟩) h12
  have hc₃Q := S.conj_mul_mem_QG hk₃ haQ
  have hc₃ : (k₃ * g) * S.z * (k₃ * g)⁻¹ ∈ S.Qa g := by
    refine S.mem_Qa_of_cl_mem haQ hne hc₃Q ?_
    rw [hk₃eq]
    exact Submodule.add_mem _ (S.cl_mem_clSub ⟨hc₁Q, hc₁⟩ hc₁Q)
      (S.cl_mem_clSub ⟨hc₂Q, hc₂⟩ hc₂Q)
  have hc₃e : (k₃ * g) * S.z * (k₃ * g)⁻¹ * ((ke * g) * S.z * (ke * g)⁻¹) =
      (ke * g) * S.z * (ke * g)⁻¹ * ((k₃ * g) * S.z * (k₃ * g)⁻¹) := by
    refine (S.polar_cl_eq_zero_iff hc₃Q heQ).mp ?_
    rw [hk₃eq, polar_add_left, (S.polar_cl_eq_zero_iff hc₁Q heQ).mpr hc₁e,
      (S.polar_cl_eq_zero_iff hc₂Q heQ).mpr hc₂e, add_zero]
  obtain ⟨t', ht', ht'1⟩ := S.exists_mem_Dbar_mul hke haQ ht ht1
  have key : ∀ k ∈ S.M, (k * g) * S.z * (k * g)⁻¹ ∈ S.Qa g →
      (k * g) * S.z * (k * g)⁻¹ * ((ke * g) * S.z * (ke * g)⁻¹) =
        (ke * g) * S.z * (ke * g)⁻¹ * ((k * g) * S.z * (k * g)⁻¹) →
      (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k * g) * S.z * (k * g)⁻¹)) =
        S.cl ((k * g) * S.z * (k * g)⁻¹) + S.cl ((ke * g) * S.z * (ke * g)⁻¹) :=
    fun k hk hcQa hce => S.apply_cl_eq_add_of_not_mem_Qa_mul hTI hn haQ hne hno hirr hke hk
      hce.symm (S.not_mem_Qa_of_not_commute haQ hne hke hk hae hcQa hce) ht' ht'1
  have h3 := key k₃ hk₃ hc₃ hc₃e
  rw [hk₃eq, map_add, key k₁ hk₁ hc₁ hc₁e, key k₂ hk₂ hc₂ hc₂e] at h3
  exact S.cl_conj_z_ne_zero heQ (S.conj_mul_ne_z hke hne) (eq_zero_of_add_add h3)

theorem exists_not_commute_conj {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hirr : ¬ S.IsReducible) :
    ∃ k ∈ S.M, g * S.z * g⁻¹ * ((k * g) * S.z * (k * g)⁻¹) ≠
      (k * g) * S.z * (k * g)⁻¹ * (g * S.z * g⁻¹) := by
  by_contra hcon
  push Not at hcon
  apply hirr
  obtain ⟨U, hU⟩ : ∃ U : Submodule (ZMod 2) S.Qt, U = Submodule.span (ZMod 2)
      (Set.range fun k : S.M => S.cl (((k : G) * g) * S.z * ((k : G) * g)⁻¹)) := ⟨_, rfl⟩
  have hUa : U ≤ LinearMap.ker (S.q.polarBilin (S.cl (g * S.z * g⁻¹))) := by
    rw [hU, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply]
    exact (S.polar_cl_eq_zero_iff haQ (S.conj_mul_mem_QG k.2 haQ)).mpr (hcon k k.2)
  refine ⟨U, ?_, ?_, fun m v hv => ?_⟩
  · intro hbot
    apply S.cl_conj_z_ne_zero haQ hne
    have h1 : S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹) ∈ U := by
      rw [hU]
      exact Submodule.subset_span ⟨1, rfl⟩
    rw [hbot, Submodule.mem_bot] at h1
    simpa using h1
  · intro htop
    apply S.cl_conj_z_ne_zero haQ hne
    refine S.q_nondegenerate.1 _ fun w => ?_
    have hw : w ∈ U := htop ▸ Submodule.mem_top
    exact LinearMap.mem_ker.mp (hUa hw)
  · rw [hU] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [S.ρ_cl m (S.conj_mul_mem_QG k.2 haQ)]
      refine Submodule.subset_span ⟨m * k, ?_⟩
      simp only [Subgroup.coe_mul]
      congr 1
      group
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx

end Setting

end CFSG.LargeExtraspecial
