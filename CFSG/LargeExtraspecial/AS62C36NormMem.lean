module

public import CFSG.LargeExtraspecial.AS62C36Basic
public import CFSG.LargeExtraspecial.AS62Mbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

namespace AS62

variable {G : Type} [Group G] [Finite G] {S : Setting G} {H : Subgroup G}

namespace ConfHyp

private theorem map_rhoL_inv_eq {n : G} (hn : n ∈ S.M) {ℓ : Submodule (ZMod 2) S.Qt}
    (h : ℓ.map (S.rhoL hn : S.Qt →ₗ[ZMod 2] S.Qt) = ℓ) :
    ℓ.map (S.rhoL (S.M.inv_mem hn) : S.Qt →ₗ[ZMod 2] S.Qt) = ℓ := by
  have e : S.rhoL (S.M.inv_mem hn) = (S.rhoL hn).symm := by
    unfold Setting.rhoL
    rw [show (⟨n⁻¹, S.M.inv_mem hn⟩ : S.M) = ⟨n, hn⟩⁻¹ from rfl, map_inv]
    rfl
  rw [e]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← h] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    simpa using hw
  · intro hx
    have hmem : S.rhoL hn x ∈ ℓ.map (S.rhoL hn : S.Qt →ₗ[ZMod 2] S.Qt) := ⟨x, hx, rfl⟩
    rw [h] at hmem
    exact ⟨S.rhoL hn x, hmem, by simp⟩

private theorem conj_mem_clPre {n : G} (hn : n ∈ S.M) {ℓ : Submodule (ZMod 2) S.Qt}
    (h : ℓ.map (S.rhoL hn : S.Qt →ₗ[ZMod 2] S.Qt) = ℓ) {y : G} (hy : y ∈ S.clPre ℓ) :
    n * y * n⁻¹ ∈ S.clPre ℓ := by
  obtain ⟨hyQ, hcy⟩ := S.mem_clPre.mp hy
  refine S.mem_clPre.mpr ⟨S.conj_mem_QG hn hyQ, ?_⟩
  rw [← S.rhoL_cl hn hyQ]
  have hmem : S.rhoL hn (S.cl y) ∈ ℓ.map (S.rhoL hn : S.Qt →ₗ[ZMod 2] S.Qt) := ⟨S.cl y, hcy, rfl⟩
  rwa [h] at hmem

private theorem rhoL_fix_of_commute {x : G} (hx : x ∈ S.M) {ℓ : Submodule (ZMod 2) S.Qt}
    (hxc : ∀ y ∈ S.clPre ℓ, x * y = y * x) : ∀ v ∈ ℓ, S.rhoL hx v = v := by
  intro v hv
  obtain ⟨y, hyQ, rfl⟩ := S.exists_cl v
  rw [S.rhoL_cl hx hyQ, hxc y ⟨hyQ, hv⟩, mul_inv_cancel_right]

private theorem commSpace_eq_of_mem (hc : ConfHyp S H) {t : G} (ht : t ∈ S.zConj H)
    (htz : t ≠ S.z) {p : G} (hp : p ∈ S.zConj H) (hpz : p ≠ S.z) :
    commSpace (S.rhoL (hc.mem_M_of_mem hp)) = commSpace (S.rhoL (hc.mem_M_of_mem ht)) := by
  obtain ⟨k, hk, hkH, hD⟩ := hc.exists_conj_eq ht htz
  exact commSpace_eq_of_mem_zConj hc.sixFourConcl hc.hW hD hk (hc.mem_M_of_mem ht)
    (by rw [hkH]; exact hp) hpz (hc.mem_M_of_mem hp)

private theorem clPre_eq (hc : ConfHyp S H) {t : G} (ht : t ∈ S.zConj H) (htz : t ≠ S.z) :
    S.clPre (commSpace (S.rhoL (hc.mem_M_of_mem ht))) = closure (S.zConj H) ⊓ S.QG := by
  obtain ⟨k, hk, hkH, hD⟩ := hc.exists_conj_eq ht htz
  have h := clPre_commSpace_eq hc.sixFourConcl hc.hW hD hk (p := t) (by rw [hkH]; exact ht) htz
    (hc.mem_M_of_mem ht)
  rwa [hkH] at h

private theorem conj_mem_V_of_map_eq (hc : ConfHyp S H) {t : G} (ht : t ∈ S.zConj H)
    (htz : t ≠ S.z) {n : G} (hn : n ∈ S.M)
    (h : (commSpace (S.rhoL (hc.mem_M_of_mem ht))).map (S.rhoL hn : S.Qt →ₗ[ZMod 2] S.Qt) =
      commSpace (S.rhoL (hc.mem_M_of_mem ht))) {ω : G} (hω : ω ∈ S.zConj H) :
    n * ω * n⁻¹ ∈ closure (S.zConj H) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have htM := hc.mem_M_of_mem ht
  by_cases hωz : ω = S.z
  · rw [hωz, S.conj_z_of_mem_M hn]
    exact subset_closure (Asc77.self_mem_conjIn _ _)
  have hωM := hc.mem_M_of_mem hω
  have hωω := zConj_mul_self S hω
  obtain ⟨hA, -, -⟩ := hc.fiveOne ht htz
  have hℓ2 : finrank (ZMod 2) (commSpace (S.rhoL htM)) = 2 := hA.2.2.2.1
  have hℓq : ∀ x ∈ commSpace (S.rhoL htM), S.q x = 0 := hA.2.2.2.2
  have hpre := hc.clPre_eq ht htz
  have hcommV : ∀ y ∈ S.clPre (commSpace (S.rhoL htM)), ∀ x ∈ S.zConj H, x * y = y * x := by
    intro y hy x hx
    rw [hpre] at hy
    exact hc.commute_V (subset_closure hx) (mem_inf.mp hy).1
  obtain ⟨u, hu⟩ : ∃ u, u = n * ω * n⁻¹ := ⟨_, rfl⟩
  rw [← hu]
  have huM : u ∈ S.M := hu ▸ S.M.mul_mem (S.M.mul_mem hn hωM) (S.M.inv_mem hn)
  have hn' := map_rhoL_inv_eq hn h
  have huc : ∀ y ∈ S.clPre (commSpace (S.rhoL htM)), u * y = y * u := by
    intro y hy
    have hy' := conj_mem_clPre (S.M.inv_mem hn) hn' hy
    rw [inv_inv] at hy'
    have h1 := hcommV _ hy' ω hω
    calc u * y = n * (ω * (n⁻¹ * y * n)) * n⁻¹ := by rw [hu]; group
      _ = n * ((n⁻¹ * y * n) * ω) * n⁻¹ := by rw [h1]
      _ = y * u := by rw [hu]; group
  have hfixu := rhoL_fix_of_commute huM huc
  have hfixω := rhoL_fix_of_commute hωM fun y hy => hcommV y hy ω hω
  have hωQ : ω ∉ S.QG := hc.not_mem_QG hω hωz
  have huQ : u ∉ S.QG := by
    intro huQ
    apply hωQ
    have h1 := S.conj_mem_QG (S.M.inv_mem hn) huQ
    rwa [hu, inv_inv, show n⁻¹ * (n * ω * n⁻¹) * n = ω by group] at h1
  have hρu : S.rhoL huM = S.rhoL htM :=
    (S.mem_QG_or_rhoL_eq_of_fix hc.hw htM huM hA hfixu).resolve_left huQ
  have hρω : S.rhoL hωM = S.rhoL htM :=
    (S.mem_QG_or_rhoL_eq_of_fix hc.hw htM hωM hA hfixω).resolve_left hωQ
  have hwM : ω * u ∈ S.M := S.M.mul_mem hωM huM
  have hρw : S.rhoL hwM = 1 := by
    rw [rhoL_mul' S hωM huM, hρu, hρω, S.rhoL_mul_self htM (zConj_mul_self S ht)]
  have hwQ : ω * u ∈ S.QG := (rhoL_eq_one_iff S hwM).mp hρw
  have hwc : ∀ y ∈ S.clPre (commSpace (S.rhoL htM)), y * (ω * u) = (ω * u) * y := by
    intro y hy
    have h1 := hcommV y hy ω hω
    have h2 := huc y hy
    calc y * (ω * u) = (y * ω) * u := (mul_assoc _ _ _).symm
      _ = (ω * y) * u := by rw [h1]
      _ = ω * (y * u) := mul_assoc _ _ _
      _ = ω * (u * y) := by rw [h2]
      _ = (ω * u) * y := (mul_assoc _ _ _).symm
  have hclw : S.cl (ω * u) ∈ commSpace (S.rhoL htM) := by
    have hmem : S.cl (ω * u) ∈
        LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace (S.rhoL htM)) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro v hv
      obtain ⟨y, hyQ, rfl⟩ := S.exists_cl v
      change S.q.polarBilin (S.cl y) (S.cl (ω * u)) = 0
      rw [QuadraticMap.polarBilin_apply_apply]
      exact (S.polar_cl_eq_zero_iff hyQ hwQ).mpr (hwc y ⟨hyQ, hv⟩)
    rwa [orthogonal_eq_self_of_singular (S.finrank_Qt_of_width_two hc.hw) S.q_nondegenerate hℓ2
      hℓq] at hmem
  have hwV : ω * u ∈ closure (S.zConj H) := by
    have h1 : ω * u ∈ S.clPre (commSpace (S.rhoL htM)) := ⟨hwQ, hclw⟩
    rw [hpre] at h1
    exact (mem_inf.mp h1).1
  rw [show u = ω * (ω * u) by rw [← mul_assoc, hωω, one_mul]]
  exact mul_mem (subset_closure hω) hwV

theorem mem_normalizer_V_iff (hc : ConfHyp S H) {t : G} (ht : t ∈ S.zConj H) (htz : t ≠ S.z)
    {m : G} (hm : m ∈ S.M) :
    m ∈ normalizer ((closure (S.zConj H) : Subgroup G) : Set G) ↔
      (commSpace (S.rhoL (hc.mem_M_of_mem ht))).map (S.rhoL hm : S.Qt →ₗ[ZMod 2] S.Qt) =
        commSpace (S.rhoL (hc.mem_M_of_mem ht)) := by
  have htM := hc.mem_M_of_mem ht
  constructor
  · intro hn
    have hu := hc.conj_mem_zConj_of_mem_normalizer hn ht
    have huz : m * t * m⁻¹ ≠ S.z := by
      intro h
      apply htz
      have h1 := S.conj_z_of_mem_M (S.M.inv_mem hm)
      rw [inv_inv] at h1
      calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
        _ = m⁻¹ * S.z * m := by rw [h]
        _ = S.z := h1
    have huM : m * t * m⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hm htM) (S.M.inv_mem hm)
    rw [← commSpace_rhoL_conj hm htM huM]
    exact hc.commSpace_eq_of_mem ht htz hu huz
  · intro h
    have key : ∀ n (hn : n ∈ S.M),
        (commSpace (S.rhoL htM)).map (S.rhoL hn : S.Qt →ₗ[ZMod 2] S.Qt) =
          commSpace (S.rhoL htM) →
        ∀ v ∈ closure (S.zConj H), n * v * n⁻¹ ∈ closure (S.zConj H) := by
      intro n hn hn' v hv
      induction hv using closure_induction with
      | mem x hx => exact hc.conj_mem_V_of_map_eq ht htz hn hn' hx
      | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
      | mul x y _ _ hx hy =>
        rw [show n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) by group]
        exact mul_mem hx hy
      | inv x _ hx =>
        rw [show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ by group]
        exact inv_mem hx
    rw [mem_normalizer_iff]
    intro v
    refine ⟨key m hm h v, fun hv => ?_⟩
    have h1 := key m⁻¹ (S.M.inv_mem hm) (map_rhoL_inv_eq hm h) _ hv
    rwa [show m⁻¹ * (m * v * m⁻¹) * m⁻¹⁻¹ = v by group] at h1

end ConfHyp

end AS62

end CFSG.LargeExtraspecial
