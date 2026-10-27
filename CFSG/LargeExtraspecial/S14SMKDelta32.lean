module

public import CFSG.LargeExtraspecial.S14SMKDeltaRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module CFSG.Open CFSG.Fischer CFSG.LargeExtraspecial.SMod20
  CFSG.RankThree.OrthogonalInvolutions QuadraticMap

variable {G : Type} [Group G] [Finite G]

section General

variable (T : Setting G)

theorem card_centralizer_eq (α : G) (hαM : α ∈ T.M) :
    Nat.card (T.QG ⊓ centralizer ({α} : Set G) : Subgroup G) =
      2 * 2 ^ finrank (ZMod 2) (T.clSub (T.QG ⊓ centralizer ({α} : Set G))) := by
  have hzC : T.z ∈ T.QG ⊓ centralizer ({α} : Set G) :=
    ⟨T.z_mem_QG, mem_centralizer_singleton_iff.mpr (T.z_comm hαM).symm⟩
  have h := T.card_clPre (T.clSub (T.QG ⊓ centralizer ({α} : Set G)))
  rw [T.clPre_clSub inf_le_left hzC, T.card_submodule] at h
  exact h

theorem finrank_fixQt_le {α : G} (hαM : α ∈ T.M) (hαQ : α ∉ T.QG) (hα2 : α ^ 2 = 1) :
    finrank (ZMod 2) (T.fixQt α) ≤
      finrank (ZMod 2) (T.clSub (T.QG ⊓ centralizer ({α} : Set G))) + 1 := by
  have h := card_QG_le_mul T hαM hαQ hα2
  rw [card_centralizer_eq T α hαM, T.card_QG_eq, T.card_Qt, T.finrank_Qt_eq_two_mul_width] at h
  have h1 := finrank_commSpace_add_finrank_fixSpace (T.ρ ⟨α, hαM⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt)
  rw [← T.fixQt_of_mem hαM, ← T.commQt_of_mem hαM, T.finrank_Qt_eq_two_mul_width] at h1
  have e1 : 2 * 2 ^ (2 * T.width) = 2 ^ (2 * T.width + 1) := by rw [pow_succ, mul_comm]
  have e2 : 2 * 2 ^ finrank (ZMod 2) (T.clSub (T.QG ⊓ centralizer ({α} : Set G))) *
      2 ^ (finrank (ZMod 2) (T.commQt α) + 1) =
      2 ^ (finrank (ZMod 2) (T.clSub (T.QG ⊓ centralizer ({α} : Set G))) +
        finrank (ZMod 2) (T.commQt α) + 2) := by
    rw [pow_add, pow_add, pow_succ, pow_two]
    ring
  rw [e1, e2] at h
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  omega

end General

section Index

variable (S : Setting G) {g : G}

theorem clSub_Dl_le_orthogonal (hxQ : g * S.z * g⁻¹ ∉ S.QG) :
    S.clSub (S.QG ⊓ S.Qa g) ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin
      (S.clSub (S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G))) := by
  intro v hv
  obtain ⟨d, hd, hdQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  obtain ⟨u, hu, huQ, rfl⟩ := S.mem_clSub_iff.mp hw
  show S.q.polarBilin (S.cl u) (S.cl d) = 0
  rw [polarBilin_apply_apply, S.polar_cl_eq_zero_iff huQ hdQ]
  exact commute_of_mem_Kz_Dl S hxQ hu hd

theorem finrank_clSub_Dl_le_one (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hJ : ∀ d ∈ S.QG ⊓ S.Qa g, d ∈ S.clPre (S.commQt (g * S.z * g⁻¹)) → d = 1) :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) ≤ 1 := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  set D := S.clSub (S.QG ⊓ S.Qa g) with hD
  set W := S.commQt (g * S.z * g⁻¹) with hW
  set H := S.clSub (S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)) with hH
  set P := LinearMap.BilinForm.orthogonal S.q.polarBilin H with hP
  have hDP : D ≤ P := clSub_Dl_le_orthogonal S hxQ
  have hWP : W ≤ P := by
    rw [hW, S.commQt_eq_orthogonal hxM hx2]
    exact LinearMap.BilinForm.orthogonal_le (S.clSub_centralizer_le_fixQt hxM)
  have hDW : D ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨d, hd, hdQ, rfl⟩ := S.mem_clSub_iff.mp hv.1
    rw [hJ d hd ⟨hdQ, hv.2⟩, S.cl_one]
    exact Submodule.zero_mem _
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq D W
  rw [hDW, finrank_bot] at d1
  have d2 := Submodule.finrank_mono (sup_le hDP hWP)
  have d3 : finrank (ZMod 2) P = finrank (ZMod 2) S.Qt - finrank (ZMod 2) H :=
    LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate H
  have d4 : finrank (ZMod 2) (S.fixQt (g * S.z * g⁻¹)) ≤ finrank (ZMod 2) H + 1 :=
    finrank_fixQt_le S hxM hxQ hx2
  have d5 : finrank (ZMod 2) W + finrank (ZMod 2) (S.fixQt (g * S.z * g⁻¹)) =
      finrank (ZMod 2) S.Qt := by
    have := finrank_commSpace_add_finrank_fixSpace (S.ρ ⟨_, hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt)
    rwa [← S.fixQt_of_mem hxM, ← S.commQt_of_mem hxM] at this
  have d6 : finrank (ZMod 2) H ≤ finrank (ZMod 2) S.Qt := Submodule.finrank_le H
  omega

end Index

section Exponent

variable (S : Setting G) {g : G}

theorem sq_eq_one_of_mem_L0 (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hl5 : 5 ≤ finrank (ZMod 2) (S.commQt (g * S.z * g⁻¹)))
    (hD : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) ≤ 1) {k : G} (hk : k ∈ S.L0 g) :
    k ^ 2 = 1 := by
  rcases (S.conjBy g).sq_eq_one_or_z hk.1 with h | h
  · exact h
  exfalso
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hkx : k ^ 2 = g * S.z * g⁻¹ := h
  set K : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨k, hk.2⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hK
  have hKK : K * K = ((S.ρ ⟨_, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    have e : (⟨k, hk.2⟩ : S.M) * ⟨k, hk.2⟩ = ⟨_, hxM⟩ := Subtype.ext (by
      simp only [Subgroup.coe_mul]
      rw [← pow_two, hkx])
    rw [hK, ← Subgroup.coe_mul, ← map_mul, e]
  have hs : K * K * (K * K) = 1 := by rw [hKK]; exact S.ρ_mul_self hxM hx2
  have hfixK : fixSpace (K * K) = S.fixQt (g * S.z * g⁻¹) := by rw [hKK, S.fixQt_of_mem hxM]
  have hcommK : commSpace (K * K) = S.commQt (g * S.z * g⁻¹) := by
    rw [hKK, S.commQt_of_mem hxM]
  set H := S.clSub (S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)) with hH
  have hHle : H ≤ fixSpace (K * K) := by
    rw [hfixK]
    exact S.clSub_centralizer_le_fixQt hxM
  have hHc : finrank (ZMod 2) (fixSpace (K * K)) ≤ finrank (ZMod 2) H + 1 := by
    rw [hfixK]
    exact finrank_fixQt_le S hxM hxQ hx2
  have hKH : H.map ((K : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤ S.clSub (S.QG ⊓ S.Qa g) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu, huQ, rfl⟩ := S.mem_clSub_iff.mp hv
    have hc := commutator_mem_Dl S hk ⟨huQ, hu.2⟩
    have e : ((K : S.Qt →ₗ[ZMod 2] S.Qt) - 1) (S.cl u) = S.cl (k * u * k⁻¹ * u⁻¹) := by
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, hK,
        S.ρ_cl ⟨k, hk.2⟩ huQ]
      rw [S.cl_mul (S.conj_mem_QG hk.2 huQ) (S.QG.inv_mem huQ), S.cl_inv huQ,
        sub_eq_add_vec (ZMod 2)]
    rw [e]
    exact S.cl_mem_clSub hc hc.1
  have h4 := finrank_commSpace_le_four S.q_nondegenerate (S.ρ ⟨k, hk.2⟩).2 hs hHle hHc
    ((Submodule.finrank_mono hKH).trans hD)
  rw [hcommK] at h4
  omega

theorem isElementaryAbelian_Lbar_of_sq (hsq : ∀ k ∈ S.L0 g, k ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 (S.Lbar g) := by
  have hmul : ∀ k ∈ S.L0 g, k * k = 1 := fun k hk => by rw [← pow_two]; exact hsq k hk
  have hcomm : ∀ k ∈ S.L0 g, ∀ k' ∈ S.L0 g, k * k' = k' * k := by
    intro k hk k' hk'
    have h1 := hmul _ ((S.L0 g).mul_mem hk hk')
    have h2 := hmul k hk
    have h3 := hmul k' hk'
    calc k * k' = k * k' * (k' * k) * (k' * k)⁻¹ := by group
      _ = k * (k' * k') * k * (k' * k)⁻¹ := by group
      _ = (k' * k)⁻¹ := by rw [h3, mul_one, h2, one_mul]
      _ = k⁻¹ * k'⁻¹ := by rw [mul_inv_rev]
      _ = k' * k := by
        rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]
        have := h1
        calc k * k' = k * k' * (k * k') * (k * k')⁻¹ := by group
          _ = (k * k')⁻¹ := by rw [this, one_mul]
          _ = k'⁻¹ * k⁻¹ := mul_inv_rev _ _
          _ = k' * k := by
            rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]
  refine { is_comm := ⟨fun u v => ?_⟩, exponent_dvd_p := ?_ }
  · obtain ⟨⟨k, hkM⟩, hkL, hku⟩ := u.2
    obtain ⟨⟨k', hk'M⟩, hk'L, hkv⟩ := v.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hku, ← hkv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm k (mem_subgroupOf.mp hkL) k' (mem_subgroupOf.mp hk'L))
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun u => ?_
    obtain ⟨⟨k, hkM⟩, hkL, hku⟩ := u.2
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hku, ← map_pow]
    have e : (⟨k, hkM⟩ : S.M) ^ 2 = 1 := Subtype.ext (by
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hsq k (mem_subgroupOf.mp hkL))
    rw [e, map_one]

end Exponent


section Main

variable
  {S : Setting G}

theorem isConj_of_mem_Dl_of_le {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hle : S.L0 g ≤ ⁅zpowers S.z, (S.conjBy g).QG⁆) {d : G} (hd : d ∈ S.QG ⊓ S.Qa g)
    (hd1 : d ≠ 1) :
    IsConj (g * S.z * g⁻¹) d ∨ IsConj (S.z * (g * S.z * g⁻¹)) d := by
  set T := S.conjBy g with hT
  have e : g⁻¹ * T.z * g⁻¹⁻¹ = S.z := by
    show g⁻¹ * (g * S.z * g⁻¹) * g⁻¹⁻¹ = S.z
    group
  have hzM : g⁻¹ * T.z * g⁻¹⁻¹ ∈ T.M := by
    rw [e]
    exact mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm
  have hzQ : g⁻¹ * T.z * g⁻¹⁻¹ ∉ T.QG := by
    rw [e]
    exact z_not_mem_Qa S hxQ
  have hJ : d ∈ (⁅zpowers (g⁻¹ * T.z * g⁻¹⁻¹), T.QG⁆ : Subgroup G) := by
    rw [e]
    exact hle (Dl_le_L0 S hd)
  have hcomm : Commute (g⁻¹ * T.z * g⁻¹⁻¹) d := by
    rw [e]
    exact (S.z_comm_QG hd.1).symm
  have hQa : T.Qa g⁻¹ = S.QG := Setting.QG_eq_of_z_eq _ _ e
  have hdQa : d ∈ T.Qa g⁻¹ := by
    rw [hQa]
    exact hd.1
  have h := SMF.isConj_of_mem_J T hzM hzQ hd1 hJ hcomm hdQa
  rw [e] at h
  exact h

theorem exists_isConj_mem_Dl (ψ : Mbar0 S ≃* T46) (hw : S.width = 10) {g : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hl5 : 5 ≤ finrank (ZMod 2) (S.commQt (g * S.z * g⁻¹)))
    (hxz : IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    ∃ v, IsConj S.z v ∧ v ∈ S.QG ⊓ S.Qa g := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hxc : IsConj S.z (g * S.z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hzx : S.z * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * S.z := (S.z_comm hxM).symm
  by_cases hJ : ∃ y ∈ S.QG ⊓ S.Qa g, y ∈ S.clPre (S.commQt (g * S.z * g⁻¹)) ∧ y ≠ 1
  · obtain ⟨y, hyD, hyJ, hy1⟩ := hJ
    have hyJ' : y ∈ (⁅zpowers (g * S.z * g⁻¹), S.QG⁆ : Subgroup G) := by
      rw [S.commutator_zpowers_eq_clPre hxM hxQ hx2]
      exact hyJ
    have hyx : Commute (g * S.z * g⁻¹) y :=
      (mem_centralizer_singleton_iff.mp (mem_centralizer_of_mem_Qa S hyD.2)).symm
    rcases SMF.isConj_of_mem_J S hxM hxQ hy1 hyJ' hyx hyD.2 with h | h
    · exact ⟨y, h, hyD⟩
    · exact ⟨y, hxz.trans h, hyD⟩
  · have hJ' : ∀ d ∈ S.QG ⊓ S.Qa g, d ∈ S.clPre (S.commQt (g * S.z * g⁻¹)) → d = 1 := by
      intro d hd hdJ
      by_contra h
      exact hJ ⟨d, hd, hdJ, h⟩
    have hD1 := finrank_clSub_Dl_le_one S hxM hxQ hJ'
    have hsq : ∀ k ∈ S.L0 g, k ^ 2 = 1 := fun k hk => sq_eq_one_of_mem_L0 S hxM hxQ hl5 hD1 hk
    have := isElementaryAbelian_Lbar_of_sq S hsq
    have h1 := card_le_of_isElementaryAbelian' ψ (S.Lbar_le_Mbar g)
    have h2 := S.card_Lbar_mul g
    have h3 := card_L0_ge S hxM hxQ
    rw [hw] at h3
    have h4 : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 := by
      rw [← card_clSub_Dl S hxQ, S.card_submodule]
      calc 2 ^ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) hD1
        _ = 2 := by norm_num
    have h5 : Nat.card (S.L0 g) = 2 ^ 10 := by
      have h6 : Nat.card (S.Lbar g) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ 9 * 2 :=
        Nat.mul_le_mul h1 h4
      have : (2 : ℕ) ^ 9 * 2 = 2 ^ 10 := by norm_num
      omega
    have hDne : 1 < Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := by
      have h7 : Nat.card (S.Lbar g) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤
          2 ^ 9 * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := Nat.mul_le_mul_right _ h1
      have h6 : 2 ^ 10 ≤ 2 ^ 9 * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := by
        rw [← h5, ← h2]
        exact h7
      by_contra h
      push Not at h
      have : 2 ^ 9 * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ 9 * 1 := Nat.mul_le_mul_left _ h
      omega
    have := Finite.one_lt_card_iff_nontrivial.mp hDne
    obtain ⟨⟨d, hd⟩, hd1⟩ := exists_ne (1 : (S.QG ⊓ S.Qa g : Subgroup G))
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    set T := S.conjBy g with hT
    have hzM : S.z ∈ T.M := mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm
    have hzQ : S.z ∉ T.QG := z_not_mem_Qa S hxQ
    have hTw : T.width = 10 := by rw [S.width_conjBy g, hw]
    have hC : Nat.card (T.QG ⊓ centralizer ({S.z} : Set G) : Subgroup G) = 2 ^ 10 := h5
    have hc9 : finrank (ZMod 2) (T.clSub (T.QG ⊓ centralizer ({S.z} : Set G))) = 9 := by
      have := card_centralizer_eq T S.z hzM
      rw [hC] at this
      have e2 : (2 : ℕ) ^ 10 = 2 * 2 ^ 9 := by norm_num
      rw [e2] at this
      exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left (by norm_num) this).symm
    have hf := finrank_fixQt_le T hzM hzQ S.z_sq
    have hd5 := finrank_commSpace_add_finrank_fixSpace (T.ρ ⟨S.z, hzM⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt)
    rw [← T.fixQt_of_mem hzM, ← T.commQt_of_mem hzM, T.finrank_Qt_eq_two_mul_width, hTw] at hd5
    have hcf := Submodule.finrank_mono (T.commQt_le_fixQt hzM S.z_sq)
    have heq : T.commQt S.z = T.fixQt S.z :=
      Submodule.eq_of_le_of_finrank_eq (T.commQt_le_fixQt hzM S.z_sq) (by omega)
    have hle : S.L0 g ≤ ⁅zpowers S.z, T.QG⁆ := by
      rw [T.commutator_zpowers_eq_clPre hzM hzQ S.z_sq, heq]
      calc S.L0 g = T.QG ⊓ centralizer ({S.z} : Set G) := rfl
        _ ≤ T.clPre (T.clSub (T.QG ⊓ centralizer ({S.z} : Set G))) := T.le_clPre_clSub inf_le_left
        _ ≤ T.clPre (T.fixQt S.z) := T.clPre_mono (T.clSub_centralizer_le_fixQt hzM)
    refine ⟨d, ?_, hd⟩
    rcases isConj_of_mem_Dl_of_le hxM hxQ hle hd hd1' with h | h
    · exact hxc.trans h
    · rw [hzx] at h
      exact hxz.trans h

end Main

end CFSG.LargeExtraspecial.S14.SMK
