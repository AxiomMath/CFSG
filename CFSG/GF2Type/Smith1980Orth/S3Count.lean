module

public import CFSG.GF2Type.Smith1980Orth.S3Types
public import CFSG.LargeExtraspecial.S14SMKTransLift
public import CFSG.LargeExtraspecial.FS77Orth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.ClassicalGroups.Orthogonal (eichler)
open TauCeti.QuadraticMap (orthogonalGroup)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private instance instFiniteDimensionalVtCount (g : G) (t : S.O) :
    FiniteDimensional (ZMod 2) (Vt S g t) :=
  Module.Finite.of_finite

theorem clSub_Dl_apply_mem {h : G} (hxM : h * S.z * h⁻¹ ∈ S.M)
    (hxz : ¬ IsConj S.z (h * S.z * h⁻¹ * S.z)) {y : S.O} (hy : y ∈ S.Mbar)
    (hyx : y * S.ρ ⟨h * S.z * h⁻¹, hxM⟩ = S.ρ ⟨h * S.z * h⁻¹, hxM⟩ * y) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa h)) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa h) := by
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hy
  have hcomm : S14.SMK.rhoM S m * S14.SMK.rhoM S ⟨h * S.z * h⁻¹, hxM⟩ =
      S14.SMK.rhoM S ⟨h * S.z * h⁻¹, hxM⟩ * S14.SMK.rhoM S m := Subtype.ext hyx
  obtain ⟨m', hm'c, hm'⟩ := S14.SMK.exists_commute_rhoM_eq_of_not_isConj S hxM hxz m hcomm
  obtain ⟨d, hdΔ, hdQ, rfl⟩ := S.mem_clSub_iff.mp hv
  have hρ : S.ρ m' = S.ρ m := congrArg Subtype.val hm'
  rw [← hρ, S.ρ_cl m' hdQ]
  have hd' := S14.SMK.conj_mem_Dl S m'.2 hm'c hdΔ
  exact S.cl_mem_clSub hd' hd'.1

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

theorem exists_Cbar_resC_eq {e : Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t}
    (he : e ∈ RmodN S D.g D.t) :
    ∃ c : D.Cbar, D.resC c = e := by
  obtain ⟨r, hr, her⟩ := he
  have hrt : r * D.t = D.t * r := commute_of_mem_Rbar D.good.H.conj_mem hr
  rcases D.mem_Cbar_of_comm (Rbar_le_Mbar hr) hrt with hc | hc
  · refine ⟨⟨r, hc⟩, LinearEquiv.ext fun v => Subtype.ext ?_⟩
    rw [D.coe_resC_apply]
    exact (her v).symm
  · refine ⟨⟨D.t * r, hc⟩, LinearEquiv.ext fun v => Subtype.ext ?_⟩
    rw [D.coe_resC_apply, her v]
    show ((D.t * r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = _
    rw [coe_mul_apply]
    exact D.t_apply_of_mem (apply_mem_Vt_of_mem_Rbar D.good.H.conj_mem hr v.2)

theorem exists_Cbar_resC_eq_eichler (s u : Vt S D.g D.t) :
    ∃ c : D.Cbar, D.resC c = eichler D.QV s u := by
  refine D.exists_Cbar_resC_eq ?_
  rw [D.RmodN_eq_omegaGroup]
  exact FS77.eichler_mem_omegaGroup D.QV_nondegenerate s u

private theorem range_le_of_Cbar_invariant (f : Vt S D.g D.t →ₗ[ZMod 2] S.Qt)
    (hf : ∀ (c : D.Cbar) (u : Vt S D.g D.t),
      ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (f u) = f (D.resC c u))
    {W : Submodule (ZMod 2) S.Qt} (hWf : W ≤ LinearMap.range f) (hW0 : W ≠ ⊥)
    (hW : ∀ c ∈ D.Cbar, ∀ v ∈ W, ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) :
    LinearMap.range f ≤ W := by
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S D.g D.t) := by
    have := D.finrank_Vt
    have := D.four_le
    omega
  have hY : ∀ s u, D.QV s = 0 → polar D.QV s u = 0 → ∀ x ∈ W.comap f,
      eichler D.QV s u x ∈ W.comap f := by
    intro s u _ _ x hx
    obtain ⟨c, hc⟩ := D.exists_Cbar_resC_eq_eichler s u
    rw [Submodule.mem_comap] at hx ⊢
    rw [← hc, ← hf c x]
    exact hW c c.2 _ hx
  rcases FS77.eichler_invariant_submodule D.QV_nondegenerate h3 (W.comap f) hY with h | h
  · exfalso
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨u, rfl⟩ := hWf hwW
    have hu : u ∈ W.comap f := hwW
    rw [h, Submodule.mem_bot] at hu
    exact hw0 (by rw [hu, map_zero])
  · rintro _ ⟨u, rfl⟩
    have hu : u ∈ W.comap f := by rw [h]; exact Submodule.mem_top
    exact hu

theorem eq_commSpace_of_isTInv {a : S.O} (ha : D.IsTInv a) {W : Submodule (ZMod 2) S.Qt}
    (hWc : W ≤ commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt)) (hW0 : W ≠ ⊥)
    (hW : ∀ y ∈ S.Mbar, y * a = a * y → ∀ v ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) :
    W = commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have hWC : ∀ c ∈ D.Cbar, ∀ v ∈ W, ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W :=
    fun c hc v hv => hW c (D.Cbar_le_Mbar hc) (D.comm_of_isTInv_of_mem_Cbar ha hc).symm v hv
  refine le_antisymm hWc ?_
  rcases ha with rfl | rfl | rfl
  ·
    have hWf : W ≤ LinearMap.range (Vt S D.g D.t).subtype := by
      rw [Submodule.range_subtype, ← D.commSpace_eq]
      exact hWc
    have h := D.range_le_of_Cbar_invariant (Vt S D.g D.t).subtype
      (fun c u => (D.coe_resC_apply c u).symm) hWf hW0 hWC
    rw [D.commSpace_eq]
    simpa using h
  ·
    let f : Vt S D.g D.t →ₗ[ZMod 2] S.Qt :=
      (D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt).comp
        (LinearMap.prod LinearMap.id LinearMap.id)
    have hfu : ∀ u, f u = D.coord (u, u) := fun u => rfl
    have hWf : W ≤ LinearMap.range f := fun w hw => by
      obtain ⟨u, rfl⟩ := D.mem_commSpace_kt_iff_coord.mp (hWc hw)
      exact ⟨u, rfl⟩
    have h := D.range_le_of_Cbar_invariant f (fun c u => by
      rw [hfu, hfu, D.Cbar_apply_coord]) hWf hW0 hWC
    intro x hx
    obtain ⟨u, rfl⟩ := D.mem_commSpace_kt_iff_coord.mp hx
    exact h ⟨u, rfl⟩
  ·
    let f : Vt S D.g D.t →ₗ[ZMod 2] S.Qt :=
      (D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt).comp
        (LinearMap.inr (ZMod 2) (Vt S D.g D.t) (Vt S D.g D.t))
    have hfu : ∀ u, f u = D.coord (0, u) := fun u => rfl
    have hWf : W ≤ LinearMap.range f := fun w hw => by
      obtain ⟨u, rfl⟩ := D.mem_commSpace_kkt_iff_coord.mp (hWc hw)
      exact ⟨u, rfl⟩
    have h := D.range_le_of_Cbar_invariant f (fun c u => by
      rw [hfu, hfu, D.Cbar_apply_coord, map_zero]) hWf hW0 hWC
    intro x hx
    obtain ⟨u, rfl⟩ := D.mem_commSpace_kkt_iff_coord.mp hx
    exact h ⟨u, rfl⟩

private theorem exists_polar_pair_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {p p' : V} (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ∃ u, polar Q p u = 1 ∧ polar Q p' u = 1 := by
  have hli : LinearIndependent (ZMod 2) ![p, p'] :=
    OrthoF2.linearIndependent_pair_iff.mpr ⟨hp, hp', hpp'⟩
  obtain ⟨x₁, h₁p, h₁p'⟩ := OrthoF2.exists_polar_eq_one_polar_eq_zero hQ hli
  obtain ⟨x₂, h₂p', h₂p⟩ :=
    OrthoF2.exists_polar_eq_one_polar_eq_zero hQ (OrthoF2.linearIndependent_pair_symm hli)
  refine ⟨x₁ + x₂, ?_, ?_⟩
  · rw [polar_add_right, polar_comm Q p x₁, polar_comm Q p x₂, h₁p, h₂p]
    simp
  · rw [polar_add_right, polar_comm Q p' x₁, polar_comm Q p' x₂, h₁p', h₂p']
    simp

private theorem lin_apply_inv_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] V) (v : V) : g (g⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

private theorem mul_comm_of_isTypeA_of_apply_mem {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {c E : V ≃ₗ[ZMod 2] V} (hc : IsTypeA Q c 2)
    (hE : ∀ v, Q (E v) = Q v) (hEP : ∀ x ∈ commSpace c, E x ∈ commSpace c) :
    E * c = c * E := by
  have hEi : ∀ v, Q (E⁻¹ v) = Q v := fun v => by
    rw [← hE (E⁻¹ v), lin_apply_inv_apply]
  have hc' : IsTypeA Q (E * c * E⁻¹) 2 := by
    refine ⟨fun v => ?_, fun h => hc.2.1 ?_, ?_, ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hE, hc.1, hEi]
    · calc c = E⁻¹ * (E * c * E⁻¹) * E := by group
        _ = 1 := by rw [h]; group
    · calc E * c * E⁻¹ * (E * c * E⁻¹) = E * (c * c) * E⁻¹ := by group
        _ = 1 := by rw [hc.2.2.1]; group
    · rw [CFSG.RankThree.OrthogonalInvolutions.commSpace_conj, LinearEquiv.finrank_map_eq,
        hc.2.2.2.1]
    · intro v hv
      rw [CFSG.RankThree.OrthogonalInvolutions.commSpace_conj] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      rw [LinearEquiv.coe_coe, hE]
      exact hc.2.2.2.2 w hw
  have hspace : commSpace (E * c * E⁻¹) = commSpace c := by
    rw [CFSG.RankThree.OrthogonalInvolutions.commSpace_conj]
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
    rintro _ ⟨x, hx, rfl⟩
    exact hEP x hx
  have h := OrthoF2.eq_of_commSpace_eq hQ hc' hc hspace
  calc E * c = E * c * E⁻¹ * E := by group
    _ = c * E := by rw [h]

private theorem coord_add_coord (a b a' b' : Vt S D.g D.t) :
    D.coord (a, b) + D.coord (a', b') = D.coord (a + a', b + b') := by
  rw [← map_add]
  rfl

theorem eq_commSpace_of_isUInv {c : S.O} (hc : c ∈ D.Cbar)
    (hcA : IsTypeA D.QV (D.resC ⟨c, hc⟩) 2)
    {W : Submodule (ZMod 2) S.Qt} (hWc : W ≤ commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hW0 : W ≠ ⊥)
    (hW : ∀ y ∈ S.Mbar, y * c = c * y → ∀ v ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) :
    W = commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  set ĉ := D.resC ⟨c, hc⟩
  set P := commSpace ĉ
  have hWt : ∀ v ∈ W, (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W :=
    fun v hv => hW D.t D.t_mem_Mbar (D.comm_of_mem_Cbar hc).symm v hv
  have hWk : ∀ v ∈ W, (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W :=
    fun v hv => hW D.k D.k_mem_Mbar (D.Cbar_comm_k hc).symm v hv
  obtain ⟨Y, hY⟩ : ∃ Y : Submodule (ZMod 2) (Vt S D.g D.t), ∀ u, u ∈ Y ↔ D.coord (u, 0) ∈ W :=
    ⟨W.comap ((D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt).comp
      (LinearMap.inl (ZMod 2) (Vt S D.g D.t) (Vt S D.g D.t))), fun u => Iff.rfl⟩
  have hQ : ∀ x ∈ P, D.QV x = 0 := hcA.2.2.2.2
  have hpol : ∀ x ∈ P, ∀ y ∈ P, polar D.QV x y = 0 := by
    intro x hx y hy
    have h := map_add_eq D.QV x y
    rw [hQ _ (P.add_mem hx hy), hQ x hx, hQ y hy] at h
    simpa using h.symm
  have hcoordY : ∀ u v, D.coord (u, v) ∈ W → u ∈ Y ∧ v ∈ Y := by
    intro u v hw
    have h1 : D.coord (v, 0) ∈ W := by
      have h := W.add_mem hw (hWt _ hw)
      rwa [D.t_apply_coord, coord_add_coord, ← add_assoc, OrthoF2.vec_add_self u, zero_add,
        OrthoF2.vec_add_self v] at h
    have h2 : D.coord (0, v) ∈ W := by
      have h := hWk _ h1
      rwa [D.k_apply_coord, add_zero] at h
    have h3 : D.coord (u, 0) ∈ W := by
      have h := W.add_mem hw h2
      rwa [coord_add_coord, add_zero, OrthoF2.vec_add_self v] at h
    exact ⟨(hY u).mpr h3, (hY v).mpr h1⟩
  have hYP : ∀ u ∈ Y, u ∈ P := fun u hu =>
    ((D.coord_mem_commSpace_Cbar_iff ⟨c, hc⟩ u 0).mp (hWc ((hY u).mp hu))).1
  have hswap : ∀ p ∈ Y, p ≠ 0 → ∀ q ∈ P, q ≠ 0 → q ≠ p → q ∈ Y := by
    intro p hpY hp0 q hqP hq0 hqp
    have hpP := hYP p hpY
    obtain ⟨u₀, hu₁, hu₂⟩ := exists_polar_pair_eq_one D.QV_nondegenerate hp0 hq0 hqp.symm
    have haP : p + q ∈ P := P.add_mem hpP hqP
    have haQ : D.QV (p + q) = 0 := hQ _ haP
    have hau : polar D.QV (p + q) u₀ = 0 := by
      rw [polar_add_left, hu₁, hu₂]
      decide
    have hEx : ∀ x, eichler D.QV (p + q) u₀ x = x + polar D.QV x (p + q) • u₀ +
        (polar D.QV x u₀ + D.QV u₀ * polar D.QV x (p + q)) • (p + q) :=
      eichler_apply_zmod2 haQ hau
    have hEP : ∀ x ∈ commSpace ĉ, eichler D.QV (p + q) u₀ x ∈ commSpace ĉ := by
      intro x hx
      rw [hEx x, hpol x hx _ haP, zero_smul, add_zero, mul_zero, add_zero]
      exact P.add_mem hx (P.smul_mem _ haP)
    have hEp : eichler D.QV (p + q) u₀ p = q := by
      rw [hEx p, hpol p hpP _ haP, zero_smul, add_zero, mul_zero, add_zero, hu₁, one_smul,
        ← add_assoc, OrthoF2.vec_add_self p, zero_add]
    have hEQ : ∀ v, D.QV (eichler D.QV (p + q) u₀ v) = D.QV v := fun v =>
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (CFSG.ClassicalGroups.Orthogonal.eichler_mem_orthogonalGroup D.QV (p + q) u₀) v
    have hcomm := mul_comm_of_isTypeA_of_apply_mem D.QV_nondegenerate hcA hEQ hEP
    obtain ⟨c', hc'⟩ := D.exists_Cbar_resC_eq_eichler (p + q) u₀
    have hc'c : (c' : S.O) * c = c * c' := by
      have h1 : D.resC (c' * ⟨c, hc⟩) =
          D.resC (⟨c, hc⟩ * c') := by
        rw [map_mul, map_mul, hc']
        exact hcomm
      exact congrArg Subtype.val (D.resC_injective h1)
    have h := hW c' (D.Cbar_le_Mbar c'.2) hc'c _ ((hY p).mp hpY)
    rw [D.Cbar_apply_coord c' p 0, map_zero, hc', hEp] at h
    exact (hY q).mpr h
  refine le_antisymm hWc ?_
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨⟨u, v⟩, rfl⟩ := D.coord.surjective w
  obtain ⟨huY, hvY⟩ := hcoordY u v hwW
  obtain ⟨p, hpY, hp0⟩ : ∃ p ∈ Y, p ≠ 0 := by
    by_cases hu : u = 0
    · by_cases hv : v = 0
      · subst hu hv
        exact absurd (by simp) hw0
      · exact ⟨v, hvY, hv⟩
    · exact ⟨u, huY, hu⟩
  have hPY : ∀ q ∈ P, q ∈ Y := by
    intro q hqP
    by_cases hq0 : q = 0
    · rw [hq0]
      exact Y.zero_mem
    by_cases hqp : q = p
    · rw [hqp]
      exact hpY
    exact hswap p hpY hp0 q hqP hq0 hqp
  intro x hx
  obtain ⟨u', v', hu', hv', rfl⟩ := (D.mem_commSpace_iff_coord_of_mem_Cbar hc).mp hx
  have h1 : D.coord (u', 0) ∈ W := (hY u').mp (hPY u' hu')
  have h2 : D.coord (v', 0) ∈ W := (hY v').mp (hPY v' hv')
  have h3 : D.coord (0, v') ∈ W := by
    have h := hWk _ h2
    rwa [D.k_apply_coord, add_zero] at h
  have h := W.add_mem h1 h3
  rwa [coord_add_coord, add_zero, zero_add] at h

theorem clSub_Dl_eq_commSpace_of_types {h : G} (hxM : h * S.z * h⁻¹ ∈ S.M)
    (hT : D.IsTInv (S.ρ ⟨h * S.z * h⁻¹, hxM⟩) ∨ D.IsUInv (S.ρ ⟨h * S.z * h⁻¹, hxM⟩))
    (hxQ : h * S.z * h⁻¹ ∉ S.QG) (hxz : ¬ IsConj S.z (h * S.z * h⁻¹ * S.z))
    (hΔ : S.QG ⊓ S.Qa h ≠ ⊥) :
    S.clSub (S.QG ⊓ S.Qa h) = S.commQt (h * S.z * h⁻¹) := by
  have hle := S14.SMK.clSub_Dl_le_commQt S hxM hxQ hxz
  have hW0 : S.clSub (S.QG ⊓ S.Qa h) ≠ ⊥ := by
    obtain ⟨⟨d, hd⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hΔ
    have hd1' : d ≠ 1 := fun e => hd1 (Subtype.ext e)
    intro hbot
    have hcl : S.cl d ∈ S.clSub (S.QG ⊓ S.Qa h) := S.cl_mem_clSub hd hd.1
    rw [hbot, Submodule.mem_bot, S.cl_eq_zero_iff hd.1] at hcl
    rcases hcl with e | e
    · exact hd1' e
    · exact S14.SMK.z_not_mem_Dl S hxQ (e ▸ hd)
  rw [S.commQt_of_mem hxM] at hle ⊢
  have hW : ∀ y ∈ S.Mbar, y * S.ρ ⟨h * S.z * h⁻¹, hxM⟩ = S.ρ ⟨h * S.z * h⁻¹, hxM⟩ * y →
      ∀ v ∈ S.clSub (S.QG ⊓ S.Qa h), (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa h) :=
    fun y hy hyx v hv => clSub_Dl_apply_mem hxM hxz hy hyx hv
  rcases hT with ha | ⟨hs, hA⟩
  · exact D.eq_commSpace_of_isTInv ha hle hW0 hW
  · exact D.eq_commSpace_of_isUInv hs hA hle hW0 hW

private def singN : Set (Vt S D.g D.t) := {v | v ≠ 0 ∧ D.QV v = 0}

private theorem ncard_singN_odd : Odd D.singN.ncard := by
  have h := D.ncard_singV_odd
  have e : D.singV = (Vt S D.g D.t).subtype '' D.singN := by
    ext w
    rw [D.mem_singV_iff]
    constructor
    · rintro ⟨s, hs0, hsQ, rfl⟩
      exact ⟨s, ⟨hs0, hsQ⟩, rfl⟩
    · rintro ⟨s, ⟨hs0, hsQ⟩, rfl⟩
      exact ⟨s, hs0, hsQ, rfl⟩
  rwa [e, Set.ncard_image_of_injective _ (Submodule.injective_subtype _)] at h

private theorem coord_mem_orbitMbar_iff {p q : Vt S D.g D.t} :
    D.coord (p, q) ∈ D.orbitMbar ↔ (q = 0 ∧ p ≠ 0 ∧ D.QV p = 0) ∨ (p = 0 ∧ q ≠ 0 ∧ D.QV q = 0) ∨
      (p = q ∧ p ≠ 0 ∧ D.QV p = 0) := by
  rw [D.mem_orbitMbar_iff_coord]
  constructor
  · rintro ⟨s, hs0, hsQ, h | h | h⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (D.coord.injective h)
      exact Or.inl ⟨rfl, hs0, hsQ⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (D.coord.injective h)
      exact Or.inr (Or.inl ⟨rfl, hs0, hsQ⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (D.coord.injective h)
      exact Or.inr (Or.inr ⟨rfl, hs0, hsQ⟩)
  · rintro (⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩)
    · exact ⟨p, h1, h2, Or.inl rfl⟩
    · exact ⟨q, h1, h2, Or.inr (Or.inl rfl)⟩
    · exact ⟨p, h1, h2, Or.inr (Or.inr rfl)⟩

private theorem odd_ncard_orbitMbar_inter_of_injective {C : Submodule (ZMod 2) S.Qt}
    (φ : Vt S D.g D.t → S.Qt) (hφ : Function.Injective φ) (hC : ∀ x, x ∈ C ↔ ∃ u, x = φ u)
    (hmem : ∀ u, φ u ∈ D.orbitMbar ↔ u ∈ D.singN) :
    Odd (D.orbitMbar ∩ (C : Set S.Qt)).ncard := by
  have e : D.orbitMbar ∩ (C : Set S.Qt) = φ '' D.singN := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      obtain ⟨u, rfl⟩ := (hC x).mp hx2
      exact ⟨u, (hmem u).mp hx1, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(hmem u).mpr hu, (hC _).mpr ⟨u, rfl⟩⟩
  rw [e, Set.ncard_image_of_injective _ hφ]
  exact D.ncard_singN_odd

private theorem ncard_orbitMbar_inter_commSpace_Cbar (c : D.Cbar)
    (hcA : IsTypeA D.QV (D.resC c) 2) :
    (D.orbitMbar ∩ (commSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : Set S.Qt)).ncard = 9 := by
  set P := commSpace (D.resC c) with hP
  have hQ : ∀ x ∈ P, D.QV x = 0 := hcA.2.2.2.2
  set Pn : Set (Vt S D.g D.t) := {p | p ∈ P ∧ p ≠ 0} with hPn
  have hPcard : Pn.ncard = 3 := by
    have h4 : Nat.card P = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hcA.2.2.2.1]
      norm_num
    have e : Pn = (P : Set (Vt S D.g D.t)) \ {0} := by
      ext p
      simp [hPn]
    have h4' : (P : Set (Vt S D.g D.t)).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact h4
    rw [e, Set.ncard_diff_singleton_of_mem P.zero_mem, h4']
  have hinj1 : Function.Injective (fun p : Vt S D.g D.t => D.coord (p, 0)) := fun a b h =>
    (Prod.mk.inj (D.coord.injective h)).1
  have hinj2 : Function.Injective (fun p : Vt S D.g D.t => D.coord (0, p)) := fun a b h =>
    (Prod.mk.inj (D.coord.injective h)).2
  have hinj3 : Function.Injective (fun p : Vt S D.g D.t => D.coord (p, p)) := fun a b h =>
    (Prod.mk.inj (D.coord.injective h)).1
  have e : D.orbitMbar ∩ (commSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : Set S.Qt) =
      (fun p => D.coord (p, 0)) '' Pn ∪ (fun p => D.coord (0, p)) '' Pn ∪
        (fun p => D.coord (p, p)) '' Pn := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      obtain ⟨u, v, hu, hv, rfl⟩ := (D.mem_commSpace_Cbar_iff_coord c).mp hx2
      rcases (D.coord_mem_orbitMbar_iff).mp hx1 with ⟨rfl, h1, -⟩ | ⟨rfl, h1, -⟩ | ⟨rfl, h1, -⟩
      · exact Or.inl (Or.inl ⟨u, ⟨hu, h1⟩, rfl⟩)
      · exact Or.inl (Or.inr ⟨v, ⟨hv, h1⟩, rfl⟩)
      · exact Or.inr ⟨u, ⟨hu, h1⟩, rfl⟩
    · rintro ((⟨p, ⟨hp, hp0⟩, rfl⟩ | ⟨p, ⟨hp, hp0⟩, rfl⟩) | ⟨p, ⟨hp, hp0⟩, rfl⟩)
      · exact ⟨D.coord_mem_orbitMbar_iff.mpr (Or.inl ⟨rfl, hp0, hQ p hp⟩),
          (D.mem_commSpace_Cbar_iff_coord c).mpr ⟨p, 0, hp, P.zero_mem, rfl⟩⟩
      · exact ⟨D.coord_mem_orbitMbar_iff.mpr (Or.inr (Or.inl ⟨rfl, hp0, hQ p hp⟩)),
          (D.mem_commSpace_Cbar_iff_coord c).mpr ⟨0, p, P.zero_mem, hp, rfl⟩⟩
      · exact ⟨D.coord_mem_orbitMbar_iff.mpr (Or.inr (Or.inr ⟨rfl, hp0, hQ p hp⟩)),
          (D.mem_commSpace_Cbar_iff_coord c).mpr ⟨p, p, hp, hp, rfl⟩⟩
  have hd12 : Disjoint ((fun p => D.coord (p, 0)) '' Pn) ((fun p => D.coord (0, p)) '' Pn) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, ⟨-, hp0⟩, rfl⟩ ⟨q, -, hq⟩
    exact hp0 (Prod.mk.inj (D.coord.injective hq)).1.symm
  have hd3 : Disjoint ((fun p => D.coord (p, 0)) '' Pn ∪ (fun p => D.coord (0, p)) '' Pn)
      ((fun p => D.coord (p, p)) '' Pn) := by
    refine Disjoint.union_left ?_ ?_
    · rw [Set.disjoint_left]
      rintro _ ⟨p, ⟨-, hp0⟩, rfl⟩ ⟨q, -, hq⟩
      have h := Prod.mk.inj (D.coord.injective hq)
      exact hp0 (h.1.symm.trans h.2)
    · rw [Set.disjoint_left]
      rintro _ ⟨p, ⟨-, hp0⟩, rfl⟩ ⟨q, -, hq⟩
      have h := Prod.mk.inj (D.coord.injective hq)
      exact hp0 (h.2.symm.trans h.1)
  rw [e, Set.ncard_union_eq hd3 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hd12 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ hinj1, Set.ncard_image_of_injective _ hinj2,
    Set.ncard_image_of_injective _ hinj3, hPcard]

theorem odd_ncard_orbitMbar_inter_commSpace {a : S.O} (ha : D.IsTInv a ∨ D.IsUInv a) :
    Odd (D.orbitMbar ∩ (commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) : Set S.Qt)).ncard := by
  rcases ha with ha | ⟨hs, hA⟩
  · rcases ha with rfl | rfl | rfl
    · refine D.odd_ncard_orbitMbar_inter_of_injective (fun u => D.coord (u, 0)) ?_ ?_ ?_
      · exact fun a b h => (Prod.mk.inj (D.coord.injective h)).1
      · exact fun x => D.mem_commSpace_t_iff_coord
      · intro u
        show D.coord (u, 0) ∈ D.orbitMbar ↔ u ∈ D.singN
        rw [D.coord_mem_orbitMbar_iff]
        simp [singN]
    · refine D.odd_ncard_orbitMbar_inter_of_injective (fun u => D.coord (u, u)) ?_ ?_ ?_
      · exact fun a b h => (Prod.mk.inj (D.coord.injective h)).1
      · exact fun x => D.mem_commSpace_kt_iff_coord
      · intro u
        show D.coord (u, u) ∈ D.orbitMbar ↔ u ∈ D.singN
        rw [D.coord_mem_orbitMbar_iff]
        simp [singN]
    · refine D.odd_ncard_orbitMbar_inter_of_injective (fun u => D.coord (0, u)) ?_ ?_ ?_
      · exact fun a b h => (Prod.mk.inj (D.coord.injective h)).2
      · exact fun x => D.mem_commSpace_kkt_iff_coord
      · intro u
        show D.coord (0, u) ∈ D.orbitMbar ↔ u ∈ D.singN
        rw [D.coord_mem_orbitMbar_iff]
        simp [singN]
  · have h := D.ncard_orbitMbar_inter_commSpace_Cbar ⟨_, hs⟩ hA
    rw [show (D.orbitMbar ∩ (commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) : Set S.Qt)).ncard = 9 from h]
    exact ⟨4, rfl⟩

theorem odd_ncard_conj_mem_Dl_of_types {h : G} (hxM : h * S.z * h⁻¹ ∈ S.M)
    (hT : D.IsTInv (S.ρ ⟨h * S.z * h⁻¹, hxM⟩) ∨ D.IsUInv (S.ρ ⟨h * S.z * h⁻¹, hxM⟩))
    (hxQ : h * S.z * h⁻¹ ∉ S.QG) (hxz : ¬ IsConj S.z (h * S.z * h⁻¹ * S.z))
    (hΔ : S.QG ⊓ S.Qa h ≠ ⊥) :
    Odd {d : G | IsConj S.z d ∧ d ∈ S.QG ⊓ S.Qa h}.ncard := by
  have hW := D.clSub_Dl_eq_commSpace_of_types hxM hT hxQ hxz hΔ
  have himage : S.cl '' {d : G | IsConj S.z d ∧ d ∈ S.QG ⊓ S.Qa h} =
      D.orbitMbar ∩ (S.clSub (S.QG ⊓ S.Qa h) : Set S.Qt) := by
    ext v
    constructor
    · rintro ⟨d, ⟨hdc, hdΔ⟩, rfl⟩
      have hdz : d ≠ S.z := fun e => S14.SMK.z_not_mem_Dl S hxQ (e ▸ hdΔ)
      rcases D.conj_mem_Q_iff.mp ⟨hdc, hdΔ.1⟩ with e | ⟨-, hd⟩
      · exact absurd e hdz
      · exact ⟨hd, S.cl_mem_clSub hdΔ hdΔ.1⟩
    · rintro ⟨hv, hvΔ⟩
      obtain ⟨d, hdΔ, hdQ, rfl⟩ := S.mem_clSub_iff.mp hvΔ
      exact ⟨d, ⟨(D.conj_mem_Q_iff.mpr (Or.inr ⟨hdQ, hv⟩)).1, hdΔ⟩, rfl⟩
  have hinj : Set.InjOn S.cl {d : G | IsConj S.z d ∧ d ∈ S.QG ⊓ S.Qa h} :=
    fun d hd e he hde => S14.SMK.cl_injOn_Dl S hxQ hd.2 he.2 hde
  rw [← hinj.ncard_image, himage, hW, S.commQt_of_mem hxM]
  exact D.odd_ncard_orbitMbar_inter_commSpace hT

theorem odd_ncard_conj_mem_Dl (hT : D.OTypes) {h : G} (hxM : h * S.z * h⁻¹ ∈ S.M)
    (hxQ : h * S.z * h⁻¹ ∉ S.QG) (hxz : ¬ IsConj S.z (h * S.z * h⁻¹ * S.z))
    (hΔ : S.QG ⊓ S.Qa h ≠ ⊥) :
    Odd {d : G | IsConj S.z d ∧ d ∈ S.QG ⊓ S.Qa h}.ncard :=
  D.odd_ncard_conj_mem_Dl_of_types hxM (hT _ (isConj_iff.mpr ⟨h, rfl⟩) hxM hxQ) hxQ hxz hΔ

private theorem t_sub_coord (a b : Vt S D.g D.t) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, b)) - D.coord (a, b) = D.coord (b, 0) := by
  rw [D.t_apply_coord, ← map_sub D.coord]
  refine congrArg D.coord (Prod.ext ?_ ?_)
  · show a + b - a = b
    abel
  · show b - b = 0
    exact sub_self b

private theorem kt_sub_coord (a b : Vt S D.g D.t) :
    ((D.k * D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, b)) - D.coord (a, b) =
      D.coord (a + b, a + b) := by
  rw [coe_mul_apply, D.t_apply_coord, D.k_apply_coord, ← map_sub D.coord]
  refine congrArg D.coord (Prod.ext ?_ ?_)
  · show b - a = a + b
    rw [sub_eq_add_vec (ZMod 2), add_comm]
  · show a + b + b - b = a + b
    abel

private theorem kkt_sub_coord (a b : Vt S D.g D.t) :
    ((D.k * D.k * D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, b)) - D.coord (a, b) =
      D.coord (0, a) := by
  rw [coe_mul_apply, coe_mul_apply, D.t_apply_coord, D.k_apply_coord, D.k_apply_coord,
    ← map_sub D.coord]
  refine congrArg D.coord (Prod.ext ?_ ?_)
  · show a + b + b - a = 0
    calc a + b + b - a = b + b := by abel
      _ = 0 := OrthoF2.vec_add_self b
  · show b + (a + b + b) - b = a
    calc b + (a + b + b) - b = a + (b + b) := by abel
      _ = a := by rw [OrthoF2.vec_add_self, add_zero]

private theorem Cbar_sub_coord {c : S.O} (hc : c ∈ D.Cbar) (a b : Vt S D.g D.t) :
    (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, b)) - D.coord (a, b) =
      D.coord (D.resC ⟨c, hc⟩ a - a,
        D.resC ⟨c, hc⟩ b - b) := by
  have h : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, b)) =
      D.coord (D.resC ⟨c, hc⟩ a, D.resC ⟨c, hc⟩ b) :=
    D.Cbar_apply_coord ⟨c, hc⟩ a b
  rw [h, ← map_sub D.coord]
  rfl

private theorem coord_mem_orbitMbar_of_singular {σ : Vt S D.g D.t} (hσ0 : σ ≠ 0)
    (hσQ : D.QV σ = 0) :
    D.coord (σ, 0) ∈ D.orbitMbar ∧ D.coord (0, σ) ∈ D.orbitMbar ∧
      D.coord (σ, σ) ∈ D.orbitMbar :=
  ⟨D.mem_orbitMbar_iff_coord.mpr ⟨σ, hσ0, hσQ, Or.inl rfl⟩,
    D.mem_orbitMbar_iff_coord.mpr ⟨σ, hσ0, hσQ, Or.inr (Or.inl rfl)⟩,
    D.mem_orbitMbar_iff_coord.mpr ⟨σ, hσ0, hσQ, Or.inr (Or.inr rfl)⟩⟩

private theorem sub_eq_zero_or_mem_of_isTInv {a : S.O} (ha : D.IsTInv a) {σ : Vt S D.g D.t}
    (hσ0 : σ ≠ 0) (hσQ : D.QV σ = 0) {x : S.Qt}
    (hx : x = D.coord (σ, 0) ∨ x = D.coord (0, σ) ∨ x = D.coord (σ, σ)) :
    (a : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x = 0 ∨ (a : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ D.orbitMbar := by
  obtain ⟨h1, h2, h3⟩ := D.coord_mem_orbitMbar_of_singular hσ0 hσQ
  have h0 : D.coord ((0 : Vt S D.g D.t), (0 : Vt S D.g D.t)) = 0 := by
    rw [Prod.mk_zero_zero, map_zero]
  rcases ha with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl
  · left
    rw [t_sub_coord, h0]
  · right
    rw [t_sub_coord]
    exact h1
  · right
    rw [t_sub_coord]
    exact h1
  · right
    rw [kt_sub_coord, add_zero]
    exact h3
  · right
    rw [kt_sub_coord, zero_add]
    exact h3
  · left
    rw [kt_sub_coord, OrthoF2.vec_add_self, h0]
  · right
    rw [kkt_sub_coord]
    exact h2
  · left
    rw [kkt_sub_coord, h0]
  · right
    rw [kkt_sub_coord]
    exact h2

private theorem sub_eq_zero_or_mem_of_isUInv {c : S.O} (hc : c ∈ D.Cbar)
    (hcA : IsTypeA D.QV (D.resC ⟨c, hc⟩) 2) {σ : Vt S D.g D.t}
    {x : S.Qt} (hx : x = D.coord (σ, 0) ∨ x = D.coord (0, σ) ∨ x = D.coord (σ, σ)) :
    (c : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x = 0 ∨ (c : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ D.orbitMbar := by
  set s := D.resC ⟨c, hc⟩ σ - σ with hs
  have hsQ : D.QV s = 0 := hcA.2.2.2.2 s (sub_mem_commSpace _ σ)
  have h0 : D.coord ((0 : Vt S D.g D.t), (0 : Vt S D.g D.t)) = 0 := by
    rw [Prod.mk_zero_zero, map_zero]
  by_cases hs0 : s = 0
  · left
    rcases hx with rfl | rfl | rfl
    · rw [D.Cbar_sub_coord hc, map_zero, sub_zero, ← hs, hs0, h0]
    · rw [D.Cbar_sub_coord hc, map_zero, sub_zero, ← hs, hs0, h0]
    · rw [D.Cbar_sub_coord hc, ← hs, hs0, h0]
  · right
    obtain ⟨h1, h2, h3⟩ := D.coord_mem_orbitMbar_of_singular hs0 hsQ
    rcases hx with rfl | rfl | rfl
    · rw [D.Cbar_sub_coord hc, map_zero, sub_zero, ← hs]
      exact h1
    · rw [D.Cbar_sub_coord hc, map_zero, sub_zero, ← hs]
      exact h2
    · rw [D.Cbar_sub_coord hc, ← hs]
      exact h3

theorem rho_cl_sub_eq_zero_or_mem_orbitMbar (hT : D.OTypes) {w y : G} (hwc : IsConj S.z w)
    (hwM : w ∈ S.M) (hwQ : w ∉ S.QG) (hyc : IsConj S.z y) (hyQ : y ∈ S.QG) (hyz : y ≠ S.z) :
    (S.ρ ⟨w, hwM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) - S.cl y = 0 ∨
      (S.ρ ⟨w, hwM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) - S.cl y ∈ D.orbitMbar := by
  have hcl : S.cl y ∈ D.orbitMbar := by
    rcases D.conj_mem_Q_iff.mp ⟨hyc, hyQ⟩ with h | ⟨-, h⟩
    · exact absurd h hyz
    · exact h
  obtain ⟨σ, hσ0, hσQ, hx⟩ := D.mem_orbitMbar_iff_coord.mp hcl
  rcases hT w hwc hwM hwQ with ha | ⟨hs, hA⟩
  · exact D.sub_eq_zero_or_mem_of_isTInv ha hσ0 hσQ hx
  · exact D.sub_eq_zero_or_mem_of_isUInv hs hA hx

theorem cl_commutator_mem (hT : D.OTypes) {w y : G} (hwc : IsConj S.z w) (hwM : w ∈ S.M)
    (hwQ : w ∉ S.QG) (hyc : IsConj S.z y) (hyQ : y ∈ S.QG) (hyz : y ≠ S.z) :
    S.cl (w * y * w⁻¹ * y⁻¹) = 0 ∨ ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ c ≠ S.z ∧
      S.cl c = S.cl (w * y * w⁻¹ * y⁻¹) := by
  have h := D.rho_cl_sub_eq_zero_or_mem_orbitMbar hT hwc hwM hwQ hyc hyQ hyz
  rw [← S.cl_commutator hwM hyQ] at h
  rcases h with h | h
  · exact Or.inl h
  · obtain ⟨c, hcQ, hc⟩ := S.exists_cl (S.cl (w * y * w⁻¹ * y⁻¹))
    have hcmem : S.cl c ∈ D.orbitMbar := by
      rw [hc]
      exact h
    have hcz : c ≠ S.z := fun e => D.zero_notMem_orbitMbar (by rwa [e, S.cl_z] at hcmem)
    exact Or.inr ⟨c, (D.conj_mem_Q_iff.mpr (Or.inr ⟨hcQ, hcmem⟩)).1, hcQ, hcz, hc⟩

end S2Data

end CFSG.GF2Type.Smith1980Orth
