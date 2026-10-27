module

public import CFSG.LargeExtraspecial.S11SixA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

omit [Finite G] in
theorem mem_map_conj {u y : G} {X : Subgroup G} :
    y ∈ X.map (MulAut.conj u).toMonoidHom ↔ u⁻¹ * y * u ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨u⁻¹ * y * u, h, by simp [mul_assoc]⟩

theorem map_conj_inf_centralizer (u g' : G) :
    (S.QG ⊓ S.Qa (u⁻¹ * g') ⊓ centralizer ({u⁻¹ * S.z * u} : Set G)).map
        (MulAut.conj u).toMonoidHom = S.Qa u ⊓ S.Qa g' ⊓ S.M := by
  ext y
  rw [mem_map_conj]
  simp only [mem_inf, mem_centralizer_singleton_iff]
  rw [← S11.mem_Qa_iff S u y, S.mem_Qa_mul_iff, inv_inv]
  refine and_congr (and_congr Iff.rfl (by rw [show u * (u⁻¹ * y * u) * u⁻¹ = y by group])) ?_
  constructor
  · intro h
    calc y * S.z = u * (u⁻¹ * y * u * (u⁻¹ * S.z * u)) * u⁻¹ := by group
      _ = u * (u⁻¹ * S.z * u * (u⁻¹ * y * u)) * u⁻¹ := by rw [h]
      _ = S.z * y := by group
  · intro h
    calc u⁻¹ * y * u * (u⁻¹ * S.z * u) = u⁻¹ * (y * S.z) * u := by group
      _ = u⁻¹ * (S.z * y) * u := by rw [h]
      _ = u⁻¹ * S.z * u * (u⁻¹ * y * u) := by group

theorem map_conj_QG_inf_centralizer (u : G) :
    (S.QG ⊓ centralizer ({u⁻¹ * S.z * u} : Set G)).map (MulAut.conj u).toMonoidHom =
      S.Qa u ⊓ S.M := by
  have h := map_conj_inf_centralizer (S := S) u u
  rw [show u⁻¹ * u = (1 : G) by group, S.Qa_one, inf_idem] at h
  rw [h, inf_idem]

theorem card_ker_inf_eq {X : Subgroup G} (hXM : X ≤ S.M) :
    Nat.card (S.ρ.ker ⊓ X.subgroupOf S.M : Subgroup S.M) = Nat.card (S.QG ⊓ X : Subgroup G) := by
  rw [← Subgroup.card_map_of_injective S.M.subtype_injective,
    Subgroup.map_inf _ _ _ S.M.subtype_injective, S.ker_ρ,
    Subgroup.map_subgroupOf_eq_of_le hXM]
  rfl

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

theorem Conf.card_inf_centralizer :
    Nat.card (S.QG ⊓ S.Qa g ⊓ centralizer ({(τ : G)} : Set G) : Subgroup G) = 2 ^ S.width := by
  have hτa : (τ : G) ∈ S.Qa g := by
    have hne : g * S.z * g⁻¹ ≠ u * S.z * u⁻¹ := by
      rw [← K.conj_eq]
      intro h
      exact K.not_mem_QG (h ▸ hy.hyp4.conj_mem)
    rw [K.conj_eq]
    exact S.mem_Qa_symm hne K.mem_Qa
  exact hy.card_inf_centralizer hy.hyp4.conj_mem hy.hyp4.conj_ne ⟨hτa, τ.2⟩ K.not_mem_QG

theorem Conf.finrank_clSub_inf_centralizer :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g ⊓ centralizer ({(τ : G)} : Set G))) + 1 =
      S.width := by
  set X := S.QG ⊓ S.Qa g ⊓ centralizer ({(τ : G)} : Set G) with hX
  have hXQ : X ≤ S.QG := fun x hx => hx.1.1
  have hzX : S.z ∈ X := ⟨⟨S.z_mem_QG, S.z_mem_Qa hy.hyp4.conj_mem hy.hyp4.conj_ne⟩,
    mem_centralizer_singleton_iff.mpr (S.z_comm τ.2).symm⟩
  have h1 : Nat.card X = 2 ^ S.width := K.card_inf_centralizer hy
  rw [← S.clPre_clSub hXQ hzX, S.card_clPre, S.card_submodule] at h1
  have hw := hy.hyp4.two_lt_width
  have h2 : 2 ^ (finrank (ZMod 2) (S.clSub X) + 1) = 2 ^ S.width := by rw [pow_succ, mul_comm, h1]
  have := Nat.pow_right_injective le_rfl h2
  omega

theorem Conf.commSpace_not_le :
    ¬ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ S.clSub (S.QG ⊓ S.Qa g) := by
  intro hU
  have hPP : LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub (S.QG ⊓ S.Qa g)) =
      S.clSub (S.QG ⊓ S.Qa g) :=
    orthogonal_clSub_eq hy.hyp4.conj_mem hy.hyp4.conj_ne hy.cons.card_QG_inf_Qa
  have hfix : S.clSub (S.QG ⊓ S.Qa g) ≤ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate t.2 (coe_mul_self K.mul_self), ← hPP]
    exact LinearMap.BilinForm.orthogonal_le hU
  exact K.ne_one (hy.cons.faithful t K.mem_Lbar fun v hv => mem_fixSpace.mp (hfix hv))

omit hy in
theorem Conf.finrank_commSpace_le :
    finrank (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ S.width := by
  have h1 := finrank_commSpace_add_finrank_fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have h2 := Submodule.finrank_mono (commSpace_le_fixSpace (coe_mul_self K.mul_self))
  have h3 := S.finrank_Qt_eq_two_mul_width
  omega

theorem Conf.commSpace_le_clSub_centralizer :
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) := by
  intro v hv
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl v
  have hcτ : c * τ = τ * c := commute_of_cl_mem_commSpace K.rho_eq K.conj_eq
    (isTypeA_of_linCase hy.hyp4 K.ne_one K.lin).2.2.2.2 hcQ hv
  exact S.cl_mem_clSub ⟨hcQ, mem_centralizer_singleton_iff.mpr hcτ⟩ hcQ

omit hy in
theorem Conf.clSub_centralizer_le_fixSpace :
    S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) ≤ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have := S.clSub_centralizer_le_fixQt τ.2
  rwa [S.fixQt_of_mem τ.2, K.rho_eq] at this

theorem Conf.finrank_clSub_centralizer (hCE : CentralExtInput.{u_G}) {k : G}
    (hk : k * S.z * k⁻¹ = (τ : G) * S.z) :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G))) = S.width := by
  set C := S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) with hC
  set A := S.clSub (S.QG ⊓ S.Qa g ⊓ centralizer ({(τ : G)} : Set G)) with hA
  set U := commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hU
  have hAC : A ≤ C := S.clSub_mono fun x hx => ⟨hx.1.1, hx.2⟩
  have hUC : U ≤ C := K.commSpace_le_clSub_centralizer hy
  have hAP : A ≤ S.clSub (S.QG ⊓ S.Qa g) := S.clSub_mono fun x hx => hx.1
  have hperp : A ⊔ U ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin C := by
    refine sup_le ?_ ?_
    · intro v hv
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      obtain ⟨y, hyX, hyQ, rfl⟩ := S.mem_clSub_iff.mp hw
      obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
      change polar S.q (S.cl y) (S.cl x) = 0
      rw [S.polar_cl_eq_zero_iff hyQ hxQ]
      exact (K.commute_of_conj_mul_z' hy hCE hk
        (mem_inf.mpr ⟨mem_inf.mpr ⟨hxX.1.2, hxQ⟩, hxX.2⟩) hyX).symm
    · intro v hv
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      have h1 := K.clSub_centralizer_le_fixSpace hw
      rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate t.2 (coe_mul_self K.mul_self),
        LinearMap.BilinForm.mem_orthogonal_iff] at h1
      have h2 := h1 v hv
      change polar S.q w v = 0
      rw [polar_comm]
      exact h2
  have hlt : A < A ⊔ U := by
    refine lt_of_le_of_ne le_sup_left fun h => K.commSpace_not_le hy ?_
    exact (le_sup_right.trans h.symm.le).trans hAP
  have h1 : finrank (ZMod 2) A < finrank (ZMod 2) ↥(A ⊔ U) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : finrank (ZMod 2) A + 1 = S.width := K.finrank_clSub_inf_centralizer hy
  have h3 : finrank (ZMod 2) ↥(A ⊔ U) ≤ finrank (ZMod 2) C :=
    Submodule.finrank_mono (sup_le hAC hUC)
  have h4 : finrank (ZMod 2) ↥(A ⊔ U) ≤
      finrank (ZMod 2) (LinearMap.BilinForm.orthogonal S.q.polarBilin C) :=
    Submodule.finrank_mono hperp
  have h5 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate C
  have h6 := S.finrank_Qt_eq_two_mul_width
  have h7 := Submodule.finrank_le C
  omega

theorem Conf.card_Qa_inf_M (hCE : CentralExtInput.{u_G}) {k : G}
    (hk : k * S.z * k⁻¹ = (τ : G) * S.z) :
    Nat.card (S.Qa u ⊓ S.M : Subgroup G) = 2 ^ (S.width + 1) ∧
      Nat.card (S.Qa u ⊓ S.Qa g ⊓ S.M : Subgroup G) = 2 ^ S.width := by
  obtain ⟨hM, Kd⟩ := K.dual hy
  have hyd := hy.of_conj (K.dual_base hy).1 (K.dual_base hy).2
  have hk' := dual_mul_z_eq K.conj_eq hk
  constructor
  · have h1 := Kd.finrank_clSub_centralizer hyd hCE hk'
    set X := S.QG ⊓ centralizer ({u⁻¹ * S.z * u} : Set G) with hX
    have hXQ : X ≤ S.QG := fun x hx => hx.1
    have hzX : S.z ∈ X := ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hM).symm⟩
    have h2 : Nat.card X = 2 ^ (S.width + 1) := by
      rw [← S.clPre_clSub hXQ hzX, S.card_clPre, S.card_submodule]
      rw [h1, pow_succ, mul_comm]
    rw [← map_conj_QG_inf_centralizer (S := S) u,
      Subgroup.card_map_of_injective (MulAut.conj u).injective]
    exact h2
  · have h1 := Kd.card_inf_centralizer hyd
    rw [← map_conj_inf_centralizer (S := S) u g,
      Subgroup.card_map_of_injective (MulAut.conj u).injective]
    exact h1

theorem Conf.card_Nbar_le (hCE : CentralExtInput.{u_G}) {k : G}
    (hk : k * S.z * k⁻¹ = (τ : G) * S.z) :
    Nat.card (Nbar S g t) ≤ 2 * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
  obtain ⟨hc1, hc2⟩ := K.card_Qa_inf_M hy hCE hk
  have hE : S.QG ⊓ S.Qa u ≤ S.Qa g := fun α hα => by
    have hτQ : u * S.z * u⁻¹ ∉ S.QG := K.conj_eq ▸ K.not_mem_QG
    have hne : u * S.z * u⁻¹ ≠ S.z := fun h => hτQ (by rw [h]; exact S.z_mem_QG)
    exact hy.mem_Qa_of_commute hy.hyp4.conj_mem hy.hyp4.conj_ne hτQ K.mem_Qa hα
      (S.QG_inf_Qa_comm hne hα ⟨hy.hyp4.conj_mem, K.mem_Qa⟩)
  have h1 := card_eq_card_map_mul (S := S) (X := S.Qa u ⊓ S.M) inf_le_right
  rw [card_ker_inf_eq inf_le_right, show S.QG ⊓ (S.Qa u ⊓ S.M) = S.QG ⊓ S.Qa u by
    rw [← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left S.QG_le_M)]] at h1
  have h2 := card_eq_card_map_mul (S := S) (X := (S.Qa g ⊓ S.Qa u) ⊓ S.M) inf_le_right
  rw [card_ker_inf_eq inf_le_right, show S.QG ⊓ ((S.Qa g ⊓ S.Qa u) ⊓ S.M) = S.QG ⊓ S.Qa u by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right))
    · exact le_inf inf_le_left (le_inf (le_inf (hE) inf_le_right)
        (inf_le_left.trans S.QG_le_M)), ← K.Lbar_inf_Nbar_eq hy ⟨hy.hyp4.conj_mem, K.mem_Qa⟩]
    at h2
  have hc2' : Nat.card ((S.Qa g ⊓ S.Qa u) ⊓ S.M : Subgroup G) = 2 ^ S.width := by
    rw [inf_comm (S.Qa g)]
    exact hc2
  rw [hc1] at h1
  rw [hc2'] at h2
  have hpos : 0 < Nat.card (S.QG ⊓ S.Qa u : Subgroup G) := Nat.card_pos
  have h3 : Nat.card ((S.Qa u ⊓ S.M).subgroupOf S.M |>.map S.ρ) =
      2 * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
    have h4 : Nat.card ((S.Qa u ⊓ S.M).subgroupOf S.M |>.map S.ρ) *
        Nat.card (S.QG ⊓ S.Qa u : Subgroup G) =
        2 * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
          Nat.card (S.QG ⊓ S.Qa u : Subgroup G) := by
      rw [mul_assoc, ← h2, ← h1, pow_succ]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h4
  have h5 : Nat.card (Nbar S g t) ≤ Nat.card ((S.Qa u ⊓ S.M).subgroupOf S.M |>.map S.ρ) :=
    Subgroup.card_le_of_le (K.timmesfeld_11_5 hy hCE : Nbar S g t ≤ S.Lbar u)
  omega

end CFSG.LargeExtraspecial.S11
