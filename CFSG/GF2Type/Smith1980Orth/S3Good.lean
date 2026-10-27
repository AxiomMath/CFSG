module

public import CFSG.GF2Type.Smith1980Orth.S3GoodType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
  CFSG.Open
open CFSG.ClassicalGroups.Orthogonal (eichler HypPair)
open TauCeti.QuadraticMap (orthogonalGroup)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

theorem nonempty_rebase (D : S2Data S) : Nonempty (Rebase D) := by
  obtain ⟨P, hP⟩ := CFSG.ClassicalGroups.Orthogonal.exists_hypPair D.QV_nondegenerate D.QV_aV
    (aV_ne_zero D.good.H D.good.ht)
  have hzQa : S.z ∈ S.Qa D.g := S.z_mem_Qa D.good.H.conj_mem D.good.H.conj_ne
  have hc₀Q : D.g⁻¹ * S.z * D.g ∈ S.QG := (SME.mem_Qa_iff S D.g S.z).mp hzQa
  have hc₀z : D.g⁻¹ * S.z * D.g ≠ S.z := by
    intro h
    apply D.good.H.conj_ne
    have h2 : D.g * S.z = S.z * D.g := by
      calc D.g * S.z = D.g * (D.g⁻¹ * S.z * D.g) := by rw [h]
        _ = S.z * D.g := by group
    calc D.g * S.z * D.g⁻¹ = S.z * D.g * D.g⁻¹ := by rw [h2]
      _ = S.z := by group
  have hconj : IsConj S.z (D.g⁻¹ * S.z * D.g) := isConj_iff.mpr ⟨D.g⁻¹, by group⟩
  have hmem : S.cl (D.g⁻¹ * S.z * D.g) ∈ D.orbitMbar := by
    rcases D.conj_mem_Q_iff.mp ⟨hconj, hc₀Q⟩ with h | ⟨-, h⟩
    · exact absurd h hc₀z
    · exact h
  obtain ⟨y, hy, hyc⟩ := hmem
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hy
  have hz : (m : G) * S.z * (m : G)⁻¹ = S.z := by
    rw [S.z_comm m.2]
    group
  refine ⟨⟨D.g * (m : G), ?_, ?_, P, hP⟩⟩
  · calc D.g * (m : G) * S.z * (D.g * (m : G))⁻¹ =
        D.g * ((m : G) * S.z * (m : G)⁻¹) * D.g⁻¹ := by group
      _ = D.g * S.z * D.g⁻¹ := by rw [hz]
  · have hmM : (m : G)⁻¹ ∈ S.M := S.M.inv_mem m.2
    have e : (D.g * (m : G))⁻¹ * S.z * (D.g * (m : G)) =
        (m : G)⁻¹ * (D.g⁻¹ * S.z * D.g) * (m : G)⁻¹⁻¹ := by group
    rw [e, ← S.ρ_cl ⟨(m : G)⁻¹, hmM⟩ hc₀Q, hyc, D.cl_base_eq_coord, ← coe_mul_apply,
      ← map_mul, ← D.cl_base_eq_coord]
    have e1 : (⟨(m : G)⁻¹, hmM⟩ : S.M) * m = 1 := Subtype.ext (inv_mul_cancel _)
    rw [e1, map_one]
    rfl

structure GoodTransport (D : S2Data S) : Prop where
  phi_f : ∀ T : D.Rebase, T.Phi (D.coord (T.P.f, 0)) = D.t
  isUInv : ∀ (T : D.Rebase) {y : G} (hyQ : y ∈ S.QG) (hy : y ∈ T.H) {u v : Vt S D.g D.t},
    S.cl y = D.coord (u, v) → polar D.QV u T.P.e = 0 → HypPerp.projZ T.P v ≠ 0 →
      D.QV v = 0 → D.IsUInv (T.Psi ⟨y, hy⟩)

theorem GoodTransport.of_six_le (D : S2Data S) (hw6 : 6 ≤ S.width) : D.GoodTransport :=
  ⟨fun T => T.Phi_f_eq_t hw6, fun T _ hyQ hy _ _ hcl hb hv0 hvQ =>
    T.isUInv_Psi hw6 hyQ hy hcl hb hv0 hvQ⟩

theorem types_of_good_base_of (D : S2Data S) (hG : D.GoodTransport) {k : G}
    (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    (ha₀ : D.g * S.z * D.g⁻¹ ∈ S.Qa k) :
    D.IsTInv (S.ρ ⟨_, hxM⟩) ∨ D.IsUInv (S.ρ ⟨_, hxM⟩) := by
  obtain ⟨T⟩ := D.nonempty_rebase
  set x := k * S.z * k⁻¹ with hx
  have hxa : x ∈ S.Qa T.g₁ := by
    have hne : D.g * S.z * D.g⁻¹ ≠ k * S.z * k⁻¹ := fun h => hxQ (by
      rw [hx, ← h]
      exact D.good.H.conj_mem)
    rw [T.Qa_g₁]
    exact S.mem_Qa_symm hne ha₀
  have hyQ : T.g₁⁻¹ * x * T.g₁ ∈ S.QG := (SME.mem_Qa_iff S T.g₁ x).mp hxa
  have hy1 : T.g₁ * (T.g₁⁻¹ * x * T.g₁) * T.g₁⁻¹ = x := by group
  have hyH : T.g₁⁻¹ * x * T.g₁ ∈ T.H := by
    refine T.mem_H.mpr ⟨S.QG_le_M hyQ, ?_⟩
    rw [hy1]
    exact hxM
  have hPsi : T.Psi ⟨_, hyH⟩ = S.ρ ⟨x, hxM⟩ := by
    rw [T.Psi_apply]
    exact congrArg S.ρ (Subtype.ext hy1)
  rw [← hPsi]
  have hconj : IsConj S.z (T.g₁⁻¹ * x * T.g₁) :=
    isConj_iff.mpr ⟨T.g₁⁻¹ * k, by rw [hx]; group⟩
  have hyz : T.g₁⁻¹ * x * T.g₁ ≠ S.z := by
    intro h
    apply hxQ
    have : x = T.g₁ * S.z * T.g₁⁻¹ := by rw [← h]; group
    rw [this]
    exact T.g₁_conj_mem
  obtain ⟨s, hs0, hsQ, hcases⟩ := (D.isConj_z_iff_coord hyQ hyz).mp hconj
  have hzX : S.z ∈ S.QG ⊓ S.Qa T.g₁⁻¹ := ⟨S.z_mem_QG, T.z_mem_Qa_inv⟩
  have hyc : T.g₁⁻¹ * x * T.g₁ ∉ S.Qa T.g₁⁻¹ := by
    rw [SME.mem_Qa_iff, inv_inv, hy1]
    exact hxQ
  have hyP : S.cl (T.g₁⁻¹ * x * T.g₁) ∉ D.Pfst (aV D.good.ht) := by
    intro hmem
    rw [← T.clSub_eq_Pfst] at hmem
    have h1 : T.g₁⁻¹ * x * T.g₁ ∈ S.clPre (S.clSub (S.QG ⊓ S.Qa T.g₁⁻¹)) := ⟨hyQ, hmem⟩
    rw [S.clPre_clSub inf_le_left hzX] at h1
    exact hyc h1.2
  have hperp : S.cl (T.g₁⁻¹ * x * T.g₁) ∈ T.perp := by
    rw [T.mem_perp, S.polar_cl_eq_zero_iff T.c_mem_QG hyQ]
    exact (T.comm_c_of_mem_H hyH).symm
  rcases hcases with hcl | hcl | hcl
  ·
    left
    have hβ : D.betaV (aV D.good.ht) s ≠ 0 := by
      intro h0
      apply hyP
      rw [hcl]
      exact D.mem_Pfst_iff.mpr ⟨s, 0, h0, by rw [zero_smul]⟩
    have hb : polar D.QV s T.P.e = 1 := by
      have h1 : polar D.QV T.P.e s ≠ 0 := by
        rw [← T.betaV_aV]
        exact hβ
      rw [polar_comm]
      exact OrthoF2.zmod2_eq_one_of_ne_zero h1
    have h : T.Psi ⟨_, hyH⟩ = D.t * T.psi (HypPerp.projZ T.P 0) := by
      rw [T.Psi_eq_of_cl hyQ hyH hcl, hb, one_smul, hG.phi_f T]
    rw [show HypPerp.projZ T.P (0 : Vt S D.g D.t) = 0 from map_zero _, T.psi_zero,
      mul_one] at h
    exact Or.inl h
  ·
    right
    rw [hcl] at hperp
    have hv : polar D.QV T.P.e s = 0 := by
      rw [← T.betaV_aV]
      exact (T.coord_mem_perp_iff 0 s).mp hperp
    have hproj : HypPerp.projZ T.P s ≠ 0 := by
      intro h0
      apply hyP
      rw [hcl]
      have h1 := HypPerp.eq_add_projZ_of_polar_e T.P hv
      rw [h0, Submodule.coe_zero, add_zero] at h1
      refine D.mem_Pfst_iff.mpr ⟨0, polar D.QV s T.P.f, map_zero _, ?_⟩
      rw [T.hP] at h1
      exact congrArg (fun w => D.coord ((0 : Vt S D.g D.t), w)) h1
    exact hG.isUInv T hyQ hyH hcl (by rw [polar_zero_left]) hproj hsQ
  ·
    right
    rw [hcl] at hperp
    have hv : polar D.QV T.P.e s = 0 := by
      rw [← T.betaV_aV]
      exact (T.coord_mem_perp_iff s s).mp hperp
    have hproj : HypPerp.projZ T.P s ≠ 0 := by
      intro h0
      apply hyP
      rw [hcl]
      have h1 := HypPerp.eq_add_projZ_of_polar_e T.P hv
      rw [h0, Submodule.coe_zero, add_zero] at h1
      refine D.mem_Pfst_iff.mpr ⟨s, polar D.QV s T.P.f, ?_, ?_⟩
      · rw [T.betaV_aV]
        exact hv
      · rw [T.hP] at h1
        exact congrArg (fun w => D.coord (s, w)) h1
    exact hG.isUInv T hyQ hyH hcl (by rw [polar_comm]; exact hv) hproj hsQ

theorem types_of_good_of (D : S2Data S) (hG : D.GoodTransport) {k : G}
    (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    (hgood : ∃ a, IsConj S.z a ∧ a ∈ S.QG ⊓ S.Qa k) :
    D.IsTInv (S.ρ ⟨_, hxM⟩) ∨ D.IsUInv (S.ρ ⟨_, hxM⟩) := by
  obtain ⟨a, haconj, haQ, haQk⟩ := hgood
  obtain ⟨h, rfl⟩ := isConj_iff.mp haconj
  have hxz : k * S.z * k⁻¹ ≠ S.z := fun h' => hxQ (by
    rw [h']
    exact S.z_mem_QG)
  have haz : h * S.z * h⁻¹ ≠ S.z := by
    intro h'
    apply hxQ
    have hz : S.z ∈ S.Qa k := h' ▸ haQk
    have h1 := S.mem_Qa_symm (g₁ := 1) (g₂ := k) (by simpa using hxz.symm) (by simpa using hz)
    rw [S.Qa_one] at h1
    exact h1
  have hF : S6.FusionCtl S D.g := S6.fusionCtl_of_lemma_3_13 D.good.H D.good.noAll
  obtain ⟨m, hm, hmh⟩ := hF h haQ haz
  have hm' : m⁻¹ ∈ S.M := S.M.inv_mem hm
  set k' := m⁻¹ * k with hk'
  have hx' : k' * S.z * k'⁻¹ = m⁻¹ * (k * S.z * k⁻¹) * m := by rw [hk']; group
  have hx'M : k' * S.z * k'⁻¹ ∈ S.M := by
    rw [hx']
    exact (S.conj_mem_M_iff hm).mpr hxM
  have hx'Q : k' * S.z * k'⁻¹ ∉ S.QG := by
    intro hQ
    apply hxQ
    rw [hx'] at hQ
    have := S.conj_mem_QG hm hQ
    rwa [show m * (m⁻¹ * (k * S.z * k⁻¹) * m) * m⁻¹ = k * S.z * k⁻¹ by group] at this
  have ha₀ : D.g * S.z * D.g⁻¹ ∈ S.Qa k' := by
    rw [hk', S.mem_Qa_mul_iff, inv_inv]
    rw [show m * (D.g * S.z * D.g⁻¹) * m⁻¹ = h * S.z * h⁻¹ from hmh]
    exact haQk
  have key := D.types_of_good_base_of hG hx'M hx'Q ha₀
  have hxe : (⟨k * S.z * k⁻¹, hxM⟩ : S.M) =
      ⟨m, hm⟩ * ⟨k' * S.z * k'⁻¹, hx'M⟩ * (⟨m, hm⟩ : S.M)⁻¹ := by
    refine Subtype.ext ?_
    show k * S.z * k⁻¹ = m * (k' * S.z * k'⁻¹) * m⁻¹
    rw [hx']
    group
  have hρ : S.ρ ⟨k * S.z * k⁻¹, hxM⟩ =
      S.ρ ⟨m, hm⟩ * S.ρ ⟨k' * S.z * k'⁻¹, hx'M⟩ * (S.ρ ⟨m, hm⟩)⁻¹ := by
    rw [hxe, map_mul, map_mul, map_inv]
  have hmb : S.ρ ⟨m, hm⟩ ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  rw [hρ]
  rcases key with h1 | h1
  · exact Or.inl (D.isTInv_conj h1 hmb)
  · exact Or.inr (D.isUInv_conj h1 hmb)

theorem types_of_good (D : S2Data S) (hw6 : 6 ≤ S.width) {k : G}
    (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    (hgood : ∃ a, IsConj S.z a ∧ a ∈ S.QG ⊓ S.Qa k) :
    D.IsTInv (S.ρ ⟨_, hxM⟩) ∨ D.IsUInv (S.ρ ⟨_, hxM⟩) :=
  D.types_of_good_of (GoodTransport.of_six_le D hw6) hxM hxQ hgood

end S2Data

end CFSG.GF2Type.Smith1980Orth
