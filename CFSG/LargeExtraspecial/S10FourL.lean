module

public import CFSG.LargeExtraspecial.S10FourK
public import CFSG.LargeExtraspecial.S10FourG
public import CFSG.LargeExtraspecial.S10FourJ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

@[expose] def FixVtConj (S : Setting G) (g : G) (t : S.O) : Prop :=
  ∀ m : S.M, S.ρ m * t * (S.ρ m)⁻¹ ≠ t →
    (S.ρ m * t * (S.ρ m)⁻¹) * t = t * (S.ρ m * t * (S.ρ m)⁻¹) →
    ∀ v ∈ Vt S g t, ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v

theorem StronglyClosedL.fixVtConj (hSC : StronglyClosedL S g t) (hCE : CentralExtInput.{u})
    (X : Hyp10 S g t) (F : Frame X) (h7 : 7 ≤ S.width) : FixVtConj S g t :=
  fun _ hne hcomm => hSC.fix_Vt_of_conj hCE X F h7 hne hcomm

theorem StronglyClosedL.false_of_point_conj (hSC : StronglyClosedL S g t) (X : Hyp10 S g t)
    (F : Frame X) {m : S.M} (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t) {α : S.Qt}
    (hαo : (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) α ∈ orbit S g t)
    (hαP : ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧ α ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)))
    (hαW : α ∈ Wt S g t) : False := by
  obtain ⟨k, hk, hαk⟩ := hαP
  obtain ⟨k', -, hk'⟩ := exists_of_mem_orbit hαo X.haQ
  have hα : α = S.cl (((m * k' : S.M) : G) * g * S.z * (((m * k' : S.M) : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_mul X, ← hk', apply_inv_apply_O]
  rw [hα] at hαk hαW
  have hαV := hSC.mem_Vt_of_mem_clSub_inf_Wt' X F hk hαk hαW
  rw [← hα] at hαV
  exact hSC.not_mem_orbit_conj_of_mem_inf X F hne hαV hαo

theorem StronglyClosedL.eq_zero_of_mem_inf_of_fix (hSC : StronglyClosedL S g t)
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X) (hfixAll : FixVtConj S g t)
    {m : S.M}
    (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t)
    (hcomm : (S.ρ m * t * (S.ρ m)⁻¹) * t = t * (S.ρ m * t * (S.ρ m)⁻¹)) {v : S.Qt}
    (hv : v ∈ Vt S g t)
    (hv' : v ∈ commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) : v = 0 := by
  by_contra hv0
  have hfix := hfixAll m hne hcomm
  obtain ⟨t', ht'⟩ : ∃ t' : S.O, t' = S.ρ m * t * (S.ρ m)⁻¹ := ⟨_, rfl⟩
  have hTt : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ht', hcomm]
  obtain ⟨-, hTW⟩ := apply_mem_Vt_Wt_of_commute X hTt
  obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp (conj_mem_Mbar X m)
  have hvo := hSC.not_mem_orbit_of_mem_inf X F hne hv'
  have hv₁0 : (⟨v, hv⟩ : Vt S g t) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨k₁, k₂, hk₁, hk₂, h12, h1v, h2v⟩ := F.exists_pair_perp hv₁0 hvo
  obtain ⟨hsup, -, -, -⟩ := decomp_pair hCE X hk₁ hk₂ h12
  have hvW : v ∈ Wt S g t := Vt_le_Wt X.H X.ht1 hv
  have hv'V := (mem_commSpace_conj_iff X m).mp hv'
  have hu0 : (⟨_, hv'V⟩ : Vt S g t) ≠ 0 := fun h => hv0 (by
    have := congrArg (fun x : Vt S g t => ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) h
    simpa [apply_inv_apply_O] using this)
  have huo := hSC.not_mem_orbit_conj_of_mem_inf X F hne hv
  have hQu := F.qf_eq_one hu0 huo
  have hex : ∃ w ∈ Wt S g t, (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ≠ 0 ∧
      (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ≠ v := by
    by_contra hno
    push Not at hno
    obtain ⟨k₃, -, hk₃, -, -, h3, -⟩ := F.exists_pair_perp hu0 huo
    have hperp : ∀ w ∈ Wt S g t,
        polar S.q w (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (orbV X.haQ X.ht hk₃)) = 0 := by
      intro w hw
      have hw' := (mem_commSpace_conj_iff X m).mp (sub_mem_commSpace
        ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w)
      have e := beta_conj_sub X m (orbV X.haQ X.ht hk₃) w hw'
      rw [polar_comm, ← e]
      by_cases h0 : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = 0
      · have : (⟨_, hw'⟩ : Vt S g t) = 0 := Subtype.ext (by
          change (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ = 0
          rw [← ht', h0, map_zero])
        rw [this, map_zero]
      · have h1 := hno w hw h0
        have : (⟨_, hw'⟩ : Vt S g t) = ⟨_, hv'V⟩ := Subtype.ext (by
          change (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ = _
          rw [← ht', h1])
        rw [this]
        exact h3
    have hu'V : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (orbV X.haQ X.ht hk₃) ∈ Vt S g t := by
      have hmem : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (orbV X.haQ X.ht hk₃) ∈
          LinearMap.BilinForm.orthogonal S.q.polarBilin (Wt S g t) := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro w hw
        rw [polarBilin_apply_apply]
        exact hperp w hw
      rwa [orthogonal_Wt] at hmem
    refine hSC.not_mem_orbit_conj_of_mem_inf X F hne hu'V ?_
    rw [inv_apply_apply_O]
    exact ⟨S.ρ k₃, hk₃, coe_orbV X.haQ X.ht hk₃⟩
  obtain ⟨w, hwW, hw0, hwv⟩ := hex
  have key : ∀ {k : S.M} (hk : S.ρ k ∈ Rbar S g t), v ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) →
      ∀ p ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t,
        (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ≠ 0 → (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ≠ v →
          False := by
    intro k hk hvP p hp hp0 hpv
    have hck : ((S.ρ y₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
          S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
      rw [hy₀]
      exact hfix _ (cl_mem_Vt (mem_Lbar_mul_of_mem_Rbar X.H X.ht hk))
    have hTp : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
      have := apply_mem_clSub_of_fix X hck hp.1
      rwa [hy₀, ← ht'] at this
    set y := (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p with hydef
    have hyP : y ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := sub_mem hTp hp.1
    have hyW : y ∈ Wt S g t := sub_mem (hTW p hp.2) hp.2
    have hyC : y ∈ commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [← ht']
      exact sub_mem_commSpace _ p
    have hyV := (mem_commSpace_conj_iff X m).mp hyC
    have hβ : beta X.H X.C X.ht X.ht1 X.hVQ ⟨_, hv'V⟩ ⟨_, hyV⟩ = 0 := by
      have hyV' : (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) ∈ Vt S g t := by
        rw [← ht']
        exact hyV
      have e := beta_conj_sub X m ⟨_, hv'V⟩ p hyV'
      have e' : (⟨_, hyV⟩ : Vt S g t) = ⟨_, hyV'⟩ := Subtype.ext (by
        simp only [hydef, ht'])
      rw [e', e]
      change polar S.q (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) p = 0
      rw [apply_inv_apply_O]
      exact (mem_Wt.mp hp.2) v hv
    by_cases hQy : qf (F.φ ⟨_, hyV⟩) = 0
    · refine hSC.false_of_point_conj X F hne ?_ ⟨k, hk, hyP⟩ hyW
      have hy0 : (⟨_, hyV⟩ : Vt S g t) ≠ 0 := fun h => hp0 (by
        have := congrArg (fun x : Vt S g t => ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) h
        simpa [apply_inv_apply_O] using this)
      exact (F.mem_orbit_iff hy0).mpr hQy
    · have hQy1 : qf (F.φ ⟨_, hyV⟩) = 1 :=
        (CFSG.RankThree.Literature.FSmith.zmod2_cases _).resolve_left hQy
      have hyvV : (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (y + v) ∈ Vt S g t := by
        rw [map_add]
        exact add_mem hyV hv'V
      have hsum : (⟨_, hyvV⟩ : Vt S g t) = ⟨_, hyV⟩ + ⟨_, hv'V⟩ :=
        Subtype.ext (by simp only [map_add, Submodule.coe_add])
      have hQ : qf (F.φ ⟨_, hyvV⟩) = 0 := by
        rw [hsum, F.qf_add', hQy1, hQu, beta_symm, hβ]
        decide
      have hyv0 : (⟨_, hyvV⟩ : Vt S g t) ≠ 0 := fun h => hpv (by
        have := congrArg (fun x : Vt S g t => ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) h
        simp only [apply_inv_apply_O, ZeroMemClass.coe_zero, map_zero] at this
        have := congrArg (· + v) this
        simpa [add_assoc, ZModModule.add_self] using this)
      exact hSC.false_of_point_conj X F hne ((F.mem_orbit_iff hyv0).mpr hQ)
        ⟨k, hk, add_mem hyP hvP⟩ (add_mem hyW hvW)
  rw [← hsup] at hwW
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Submodule.mem_sup.mp hwW
  have hv1 : v ∈ S.clSub (S.QG ⊓ S.Qa ((k₁ : G) * g)) := (beta_orbV_eq_zero_iff X hk₁ _).mp h1v
  have hv2 : v ∈ S.clSub (S.QG ⊓ S.Qa ((k₂ : G) * g)) := (beta_orbV_eq_zero_iff X hk₂ _).mp h2v
  have hcases : ∀ q ∈ S.clSub (S.QG ⊓ S.Qa ((k₁ : G) * g)) ⊓ Wt S g t,
      (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q = 0 ∨ (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q = v := by
    intro q hq
    by_contra h
    push Not at h
    exact key hk₁ hv1 q hq h.1 h.2
  have hcases' : ∀ q ∈ S.clSub (S.QG ⊓ S.Qa ((k₂ : G) * g)) ⊓ Wt S g t,
      (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q = 0 ∨ (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q = v := by
    intro q hq
    by_contra h
    push Not at h
    exact key hk₂ hv2 q hq h.1 h.2
  have e : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) (p₁ + p₂) - (p₁ + p₂) =
      ((t' : S.Qt ≃ₗ[ZMod 2] S.Qt) p₁ - p₁) + ((t' : S.Qt ≃ₗ[ZMod 2] S.Qt) p₂ - p₂) := by
    rw [map_add]
    abel
  rw [e] at hw0 hwv
  rcases hcases p₁ hp₁ with h1 | h1 <;> rcases hcases' p₂ hp₂ with h2 | h2
  · exact hw0 (by rw [h1, h2, add_zero])
  · exact hwv (by rw [h1, h2, zero_add])
  · exact hwv (by rw [h1, h2, add_zero])
  · exact hw0 (by rw [h1, h2, ZModModule.add_self])

end CFSG.LargeExtraspecial.S10
