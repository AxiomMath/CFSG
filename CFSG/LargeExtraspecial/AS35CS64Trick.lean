module

public import CFSG.LargeExtraspecial.AS35CS64Basic
public import CFSG.LargeExtraspecial.AS35Pre

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem smith_trick (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g x : G} (hgx : g * S.z * g⁻¹ = x) (hxM : x ∈ S.M) (hxz : x ≠ S.z)
    {t : G} (htQ : t ∈ S.QG) (htx : t ∈ S.Qa g) (ht1 : t ≠ 1) {c : G} (hcQ : c ∈ S.QG)
    (hct : c * t = t * c) (hj2 : (c * x * c⁻¹ * x⁻¹) ^ 2 = 1) :
    c * x * c⁻¹ * x⁻¹ = 1 ∨ c * x * c⁻¹ * x⁻¹ = S.z ∨ c * x * c⁻¹ * x⁻¹ = t ∨
      c * x * c⁻¹ * x⁻¹ = t * S.z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hj1, hjz, hjt, hjtz⟩ := hcon
  have hx2 : x * x = 1 := by rw [← hgx]; exact S.conj_mul_self g
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hjQ : c * x * c⁻¹ * x⁻¹ ∈ S.QG := S.comm_mem_QG hxM hcQ
  have hcM : c ∈ S.M := S.QG_le_M hcQ
  have hy2 : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hyinv : (c * x * c⁻¹)⁻¹ = c * x * c⁻¹ := inv_eq_of_mul_eq_one_right hy2
  have hjyx : c * x * c⁻¹ * x⁻¹ = c * x * c⁻¹ * x := by rw [hxinv]
  have hyx : c * x * c⁻¹ * x = x * (c * x * c⁻¹) := by
    have h1 : (c * x * c⁻¹ * x) * (c * x * c⁻¹ * x) = 1 := by
      rw [← hjyx, ← pow_two]
      exact hj2
    have h3 := eq_inv_of_mul_eq_one_left h1
    rwa [mul_inv_rev, hxinv, hyinv] at h3
  have hne : g * S.z * g⁻¹ ≠ S.z := by rw [hgx]; exact hxz
  have ht2 : t * t = 1 := S.mul_self_eq_one_of_mem_Qa hne htQ htx
  have hzQa : S.z ∉ S.Qa g := S.z_not_mem_Qa hW hne
  have htz : t * S.z = S.z * t := S.z_comm_QG htQ
  set T := S.conjBy g with hT
  have hTz : T.z = x := by rw [hT, conjBy_z, hgx]
  have hWT := S.weaklyClosed_conjBy hW g
  have hyT : c * T.z * c⁻¹ = c * x * c⁻¹ := by rw [hTz]
  have hyMT : c * x * c⁻¹ ∈ T.M := by rw [T.mem_M_iff, hTz]; exact hyx
  have hyneT : c * x * c⁻¹ ≠ T.z := by
    rw [hTz]
    intro h
    apply hj1
    rw [h, mul_inv_cancel]
  have hgy : (c * g) * S.z * (c * g)⁻¹ = c * x * c⁻¹ := by rw [← hgx]; group
  have hlam : ∀ e ∈ T.QG, e * (c * x * c⁻¹) * e⁻¹ ≠ c * x * c⁻¹ * T.z := by
    intro e _ he
    have hk : (e * (c * g)) * S.z * (e * (c * g))⁻¹ = c * x * c⁻¹ * x⁻¹ := by
      calc (e * (c * g)) * S.z * (e * (c * g))⁻¹
          = e * ((c * g) * S.z * (c * g)⁻¹) * e⁻¹ := by group
        _ = c * x * c⁻¹ * x⁻¹ := by rw [hgy, he, hTz, hjyx]
    exact hjz (by rw [← hk]; exact hW _ (hk ▸ hjQ))
  have htT : t ∈ T.QG := htx
  have htTc : t ∈ T.Qa c := T.mem_Qa_of_commute htT hct
  obtain ⟨e, -, he⟩ := T.exists_conj_comm_eq hWT hyT hyMT hyneT hlam htT htTc
  have hconj : (e * (c * g)) * S.z * (e * (c * g))⁻¹ = e * (c * x * c⁻¹) * e⁻¹ := by
    calc (e * (c * g)) * S.z * (e * (c * g))⁻¹ = e * ((c * g) * S.z * (c * g)⁻¹) * e⁻¹ := by
          group
      _ = e * (c * x * c⁻¹) * e⁻¹ := by rw [hgy]
  rcases he with he | he
  ·
    have hyz : c * x * c⁻¹ ≠ S.z := by
      intro h
      apply hxz
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = c⁻¹ * (S.z * c) := by rw [h, mul_assoc]
        _ = S.z := by rw [← S.z_comm hcM, inv_mul_cancel_left]
    have hyQ : c * x * c⁻¹ ∉ S.QG := by
      rw [← hgy]
      exact S.conj_not_mem_QG hW (by rw [hgy]; exact hyz)
    set R := S.conjBy (c * g) with hR
    have hRz : R.z = c * x * c⁻¹ := by rw [hR, conjBy_z, hgy]
    have htR : t ∈ R.QG := by
      change t ∈ S.Qa (c * g)
      rw [← S.Qa_conjBy g c]
      exact htTc
    have htRz : t ≠ R.z := by
      rw [hRz]
      intro h
      exact hyQ (h ▸ htQ)
    obtain ⟨u, -, hu⟩ := R.exists_conj_eq_mul_z htR ht1 htRz
    rw [hRz] at hu
    have hey : e * (c * x * c⁻¹) * e⁻¹ = t * (c * x * c⁻¹) := by
      calc e * (c * x * c⁻¹) * e⁻¹ = e * (c * x * c⁻¹) * e⁻¹ * (c * x * c⁻¹)⁻¹ *
            (c * x * c⁻¹) := by group
        _ = t * (c * x * c⁻¹) := by rw [he]
    have hk : (u⁻¹ * (e * (c * g))) * S.z * (u⁻¹ * (e * (c * g)))⁻¹ = t := by
      calc (u⁻¹ * (e * (c * g))) * S.z * (u⁻¹ * (e * (c * g)))⁻¹
          = u⁻¹ * ((e * (c * g)) * S.z * (e * (c * g))⁻¹) * u := by group
        _ = u⁻¹ * (u * t * u⁻¹) * u := by rw [hconj, hey, hu]
        _ = t := by group
    have htz' : t = S.z := by rw [← hk]; exact hW _ (hk ▸ htQ)
    exact hzQa (htz' ▸ htx)
  ·
    have hjinv : (c * x * c⁻¹ * x⁻¹)⁻¹ = x * (c * x * c⁻¹) := by
      rw [hxinv]
      calc (c * x * c⁻¹ * x)⁻¹ = x⁻¹ * c * x⁻¹ * c⁻¹ := by group
        _ = x * (c * x * c⁻¹) := by rw [hxinv]; group
    have hk : (e * (c * g)) * S.z * (e * (c * g))⁻¹ = t * (c * x * c⁻¹ * x⁻¹)⁻¹ := by
      rw [hconj]
      calc e * (c * x * c⁻¹) * e⁻¹ = e * (c * x * c⁻¹) * e⁻¹ * (c * x * c⁻¹)⁻¹ *
            (c * x * c⁻¹) := by group
        _ = t * x * (c * x * c⁻¹) := by rw [he, hTz]
        _ = t * (c * x * c⁻¹ * x⁻¹)⁻¹ := by rw [hjinv, mul_assoc]
    have hmem : t * (c * x * c⁻¹ * x⁻¹)⁻¹ ∈ S.QG := mul_mem htQ (inv_mem hjQ)
    have h1 : t * (c * x * c⁻¹ * x⁻¹)⁻¹ = S.z := by rw [← hk]; exact hW _ (hk ▸ hmem)
    apply hjtz
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    calc c * x * c⁻¹ * x⁻¹ = (t⁻¹ * (t * (c * x * c⁻¹ * x⁻¹)⁻¹))⁻¹ := by group
      _ = (t * S.z)⁻¹ := by rw [h1, hti]
      _ = S.z * t := by rw [mul_inv_rev, S.z_inv, hti]
      _ = t * S.z := htz.symm

theorem cl_mem_commSpace_of_mem_Qa [IsSimpleGroup G] (hn : 3 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g x : G} (hgx : g * S.z * g⁻¹ = x) (hxM : x ∈ S.M) (hxz : x ≠ S.z)
    {t : G} (htQ : t ∈ S.QG) (htx : t ∈ S.Qa g) (ht1 : t ≠ 1) :
    S.cl t ∈ commSpace ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  set σ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσ
  have hx2 : x * x = 1 := by rw [← hgx]; exact S.conj_mul_self g
  have h2 : σ * σ = 1 := S.ρ_mul_self hxM (by rw [pow_two]; exact hx2)
  have hO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q := (S.ρ ⟨x, hxM⟩).2
  have hxQ : (⟨x, hxM⟩ : S.M) ∉ S.Q := fun h =>
    S.conj_not_mem_QG hW (g := g) (by rw [hgx]; exact hxz) (by rw [hgx]; exact ⟨_, h, rfl⟩)
  by_contra hnot
  obtain ⟨u, hu, hu0, hqu⟩ := S.exists_singular_of_two_le
    (fun u hu v hv => polar_commSpace_eq_zero hO h2 hu hv) (S.two_le_finrank_commSpace hn hxQ)
  have hnot' := hnot
  rw [S.commSpace_eq_orthogonal hO h2, LinearMap.BilinForm.mem_orthogonal_iff] at hnot'
  push Not at hnot'
  obtain ⟨w, hw, hwt⟩ := hnot'
  have hwt' : polar S.q w (S.cl t) = 1 := by
    rcases zmod2_cases (polar S.q w (S.cl t)) with h | h
    · exact absurd (by change S.q.polarBilin w (S.cl t) = 0; rw [polarBilin_apply_apply]; exact h)
        hwt
    · exact h
  obtain ⟨v, hv⟩ := mem_commSpace.mp hu
  obtain ⟨v', hv't, hv'⟩ : ∃ v', polar S.q v' (S.cl t) = 0 ∧ σ v' - v' = u := by
    by_cases h0 : polar S.q v (S.cl t) = 0
    · exact ⟨v, h0, hv⟩
    · refine ⟨v + w, ?_, ?_⟩
      · rw [polar_add_left, hwt']
        rcases zmod2_cases (polar S.q v (S.cl t)) with h | h
        · exact absurd h h0
        · rw [h]
          decide
      · rw [map_add, (mem_fixSpace.mp hw), ← hv]
        abel
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl v'
  have hct : c * t = t * c := (S.polar_cl_eq_zero_iff hcQ htQ).mp hv't
  have hjcl : S.cl (c * x * c⁻¹ * x⁻¹) = u := by
    rw [S.cl_comm hxM hcQ, ← hv', sub_eq_add_vec (ZMod 2), add_comm]
  have hj2 : (c * x * c⁻¹ * x⁻¹) ^ 2 = 1 :=
    (S.q_cl_eq_zero_iff (S.comm_mem_QG hxM hcQ)).mp (by rw [hjcl]; exact hqu)
  rcases S.smith_trick hW hgx hxM hxz htQ htx ht1 hcQ hct hj2 with h | h | h | h
  · exact hu0 (by rw [← hjcl, h, S.cl_one])
  · exact hu0 (by rw [← hjcl, h, S.cl_z])
  · exact hnot (by rw [← h, hjcl]; exact hu)
  · exact hnot (by rw [← S.cl_mul_z htQ, ← h, hjcl]; exact hu)

theorem conj_ne_mul_z_of_mem_Qa [IsSimpleGroup G] (hn : 3 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g x : G} (hgx : g * S.z * g⁻¹ = x) (hxM : x ∈ S.M) (hxz : x ≠ S.z)
    {t : G} (htQ : t ∈ S.QG) (htx : t ∈ S.Qa g) (ht1 : t ≠ 1) :
    ∀ e ∈ S.QG, e * x * e⁻¹ ≠ x * S.z := by
  intro e heQ he
  obtain ⟨v, hv⟩ := mem_commSpace.mp (S.cl_mem_commSpace_of_mem_Qa hn hW hgx hxM hxz htQ htx ht1)
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl v
  have hjcl : S.cl (c * x * c⁻¹ * x⁻¹) = S.cl t := by
    rw [S.cl_comm hxM hcQ, ← hv, sub_eq_add_vec (ZMod 2), add_comm]
  have hcM : c ∈ S.M := S.QG_le_M hcQ
  have hWT := S.weaklyClosed_conjBy hW g
  have key : ∀ k : G, k * x * k⁻¹ ≠ t * x := by
    intro k hk
    have hxa : x ∈ S.Qa g := hgx ▸ S.conj_z_mem_Qa g
    have hmem : k * (S.conjBy g).z * k⁻¹ ∈ (S.conjBy g).QG := by
      rw [conjBy_z, hgx, hk]
      exact mul_mem htx hxa
    have h1 := hWT k hmem
    rw [conjBy_z, hgx, hk] at h1
    exact ht1 (mul_right_cancel (h1.trans (one_mul x).symm))
  rcases (S.cl_eq_cl_iff htQ (S.comm_mem_QG hxM hcQ)).mp hjcl.symm with h | h
  · apply key c
    calc c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x := by group
      _ = t * x := by rw [h]
  · apply key (c * e)
    have hcz : c * S.z * c⁻¹ = S.z := by rw [S.z_comm hcM]; group
    calc c * e * x * (c * e)⁻¹ = c * (e * x * e⁻¹) * c⁻¹ := by group
      _ = c * (x * S.z) * c⁻¹ := by rw [he]
      _ = c * x * c⁻¹ * x⁻¹ * x * (c * S.z * c⁻¹) := by group
      _ = t * S.z * x * S.z := by rw [h, hcz]
      _ = t * x * (S.z * S.z) := by rw [mul_assoc t S.z x, ← S.z_comm hxM]; group
      _ = t * x := by rw [S.z_mul_z, mul_one]

theorem q_commSpace_eq_zero {x : G} (hxM : x ∈ S.M) (hx2 : x * x = 1)
    (hlam : ∀ e ∈ S.QG, e * x * e⁻¹ ≠ x * S.z) {u : S.Qt}
    (hu : u ∈ commSpace ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.q u = 0 := by
  set σ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσ
  have h2 : σ * σ = 1 := S.ρ_mul_self hxM (by rw [pow_two]; exact hx2)
  obtain ⟨v, hv⟩ := mem_commSpace.mp hu
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl v
  have hjQ := S.comm_mem_QG hxM hcQ
  have hjcl : S.cl (c * x * c⁻¹ * x⁻¹) = u := by
    rw [S.cl_comm hxM hcQ, ← hv, sub_eq_add_vec (ZMod 2), add_comm]
  have hfix : σ (S.cl (c * x * c⁻¹ * x⁻¹)) = S.cl (c * x * c⁻¹ * x⁻¹) := by
    rw [hjcl]
    exact mem_fixSpace.mp (commSpace_le_fixSpace h2 hu)
  have hjx := S.commute_of_fix hxM hlam hjQ hfix
  have hinv := conj_comm_eq_inv hx2 c
  rw [← hjcl, S.q_cl_eq_zero_iff hjQ, pow_two]
  have h3 : x * (c * x * c⁻¹ * x⁻¹) * x⁻¹ = c * x * c⁻¹ * x⁻¹ := by
    rw [← hjx]
    group
  rw [h3] at hinv
  calc c * x * c⁻¹ * x⁻¹ * (c * x * c⁻¹ * x⁻¹) =
      (c * x * c⁻¹ * x⁻¹)⁻¹ * (c * x * c⁻¹ * x⁻¹) := by rw [← hinv]
    _ = 1 := inv_mul_cancel _

end Setting

end CFSG.LargeExtraspecial
