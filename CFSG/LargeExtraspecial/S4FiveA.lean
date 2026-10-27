module

public import CFSG.LargeExtraspecial.S4Weak
public import CFSG.LargeExtraspecial.OrthoF2Pairs57
public import CFSG.LargeExtraspecial.S4Span

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Dset_mul (h : S.M) (t : S.O) : Dset S ((h : G) * g) t = Dset S g t := by
  ext X
  constructor
  · rintro ⟨k, rfl, ht⟩
    exact ⟨k * h, by simp [mul_assoc], ht⟩
  · rintro ⟨k, rfl, ht⟩
    refine ⟨k * h⁻¹, ?_, ht⟩
    simp [mul_assoc]

theorem Rbar_mul (h : S.M) (t : S.O) : Rbar S ((h : G) * g) t = Rbar S g t := by
  rw [Rbar, Rbar, Dset_mul]

theorem Vt_mul (h : S.M) (t : S.O) : Vt S ((h : G) * g) t = Vt S g t := by
  unfold Vt
  congr 1
  ext v
  constructor
  · rintro ⟨k, ht, rfl⟩
    exact ⟨k * h, by simpa [mul_assoc] using ht, by simp [mul_assoc]⟩
  · rintro ⟨k, ht, rfl⟩
    refine ⟨k * h⁻¹, by simpa [mul_assoc] using ht, ?_⟩
    simp [mul_assoc]

theorem Nbar_mul (h : S.M) (t : S.O) : Nbar S ((h : G) * g) t = Nbar S g t := by
  ext x
  rw [mem_Nbar, mem_Nbar, Rbar_mul, Vt_mul]

theorem V_mul (h : S.M) (t : S.O) : V S ((h : G) * g) t = V S g t := by
  rw [V, V, Vt_mul]

theorem Hyp4.mul (H : Hyp4 S g) (h : S.M) : Hyp4 S ((h : G) * g) where
  conj_mem := conj_mem_QG' S h.2 H.conj_mem
  conj_ne := conj_ne_z' S h.2 H.conj_ne
  fixSub_eq := fixSub_Lbar_mul H h
  two_lt_width := H.two_lt_width

theorem isTypeAOn_conj (h α : S.M) {l : ℕ} (hα : S.IsTypeAOn α l) :
    S.IsTypeAOn (h * α * h⁻¹) l := by
  unfold Setting.IsTypeAOn at hα ⊢
  rw [map_mul, map_mul, map_inv]
  have := isTypeA_conj hα (S.ρ h).2
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this

omit [Finite G] in
theorem QG_map_conj {h : G} (hh : h ∈ S.M) : S.QG.map (MulAut.conj h).toMonoidHom = S.QG := by
  refine le_antisymm ?_ fun x hx => ⟨h⁻¹ * x * h, ?_, by simp [mul_assoc]⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact S.conj_mem_QG hh hx
  · have := S.conj_mem_QG (S.M.inv_mem hh) hx
    simpa [mul_assoc] using this

omit [Finite G] in
theorem L0_mul (h : S.M) : S.L0 ((h : G) * g) = (S.L0 g).map (MulAut.conj (h : G)).toMonoidHom := by
  ext x
  rw [mem_L0_mul_iff S h.2]
  constructor
  · intro hx
    exact ⟨(h : G)⁻¹ * x * h, hx, by simp [mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy

omit [Finite G] in
theorem La_mul (h : S.M) : S.La ((h : G) * g) = (S.La g).map (MulAut.conj (h : G)).toMonoidHom := by
  unfold Setting.La
  rw [Subgroup.map_sup, QG_map_conj h.2]
  exact congrArg (S.QG ⊔ ·) (L0_mul h)

theorem NoA2.mul (hNo : NoA2 S g) (h : S.M) : NoA2 S ((h : G) * g) := by
  intro α hαL hαQ hα
  rw [La_mul] at hαL
  obtain ⟨y, hy, hyα⟩ := hαL
  have hyM : y ∈ S.M := La_le_M S g hy
  have e : (⟨y, hyM⟩ : S.M) = h⁻¹ * α * h := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hyα]
    simp [mul_assoc]
  refine hNo ⟨y, hyM⟩ hy ?_ ?_
  · intro hmem
    apply hαQ
    have := S.conj_mem_QG h.2 hmem
    rw [← hyα]
    exact this
  · rw [e]
    have := isTypeAOn_conj h⁻¹ α hα
    simpa using this

omit [Finite G] in
theorem QG_inf_Qa_mul (h : S.M) :
    S.QG ⊓ S.Qa ((h : G) * g) = (S.QG ⊓ S.Qa g).map (MulAut.conj (h : G)).toMonoidHom := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (h : G)).injective, QG_map_conj h.2, Qa_mul]

omit [Finite G] in
theorem mem_clSub_map_conj_iff (k : S.M) {X : Subgroup G} (hX : X ≤ S.QG) {v : S.Qt}
    [Finite G] :
    v ∈ S.clSub (X.map (MulAut.conj (k : G)).toMonoidHom) ↔
      (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub X := by
  rw [S.mem_clSub_iff, S.mem_clSub_iff]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxQ, rfl⟩
    refine ⟨x, hx, hX hx, ?_⟩
    rw [← map_inv, S.ρ_cl k⁻¹ hxQ]
    simp [mul_assoc]
  · rintro ⟨x, hx, hxQ, hxv⟩
    refine ⟨(k : G) * x * (k : G)⁻¹, ⟨x, hx, rfl⟩, S.conj_mem_QG k.2 hxQ, ?_⟩
    rw [← S.ρ_cl k hxQ, hxv, apply_inv_apply_O]

theorem Cons311.mul (H11 : Cons311 S g) (h : S.M) : Cons311 S ((h : G) * g) where
  weaklyClosed := weaklyClosed_mul H11.weaklyClosed h
  card_Lbar := by
    rw [Lbar_mul S h, Subgroup.card_map_of_injective (MulAut.conj (S.ρ h)).injective,
      H11.card_Lbar]
  card_QG_inf_Qa := by
    rw [QG_inf_Qa_mul h, Subgroup.card_map_of_injective (MulAut.conj (h : G)).injective,
      H11.card_QG_inf_Qa]
  comm_le := by
    intro x hx s hs
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
    have hx' : (h : G)⁻¹ * x * h ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨by simpa using S.conj_mem_QG (S.M.inv_mem h.2) hxQ, ?_⟩
      rw [mem_centralizer_singleton_iff] at hxc ⊢
      rw [mul_conj_z] at hxc
      calc (h : G)⁻¹ * x * h * (g * S.z * g⁻¹) =
            (h : G)⁻¹ * (x * ((h : G) * (g * S.z * g⁻¹) * (h : G)⁻¹)) * h := by group
        _ = (h : G)⁻¹ * (((h : G) * (g * S.z * g⁻¹) * (h : G)⁻¹) * x) * h := by rw [hxc]
        _ = g * S.z * g⁻¹ * ((h : G)⁻¹ * x * h) := by group
    have hs' := (mem_Lbar_mul_iff S h g).mp hs
    have key := H11.comm_le _ hx' _ hs'
    rw [QG_inf_Qa_mul h, mem_clSub_map_conj_iff h inf_le_left]
    have hcl : (((S.ρ h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl ((h : G)⁻¹ * x * h) := by
      rw [← map_inv, S.ρ_cl h⁻¹ hxQ]
      simp
    rw [← hcl] at key
    simp only [coe_mul_apply, apply_inv_apply_O] at key
    rw [map_sub]
    exact key
  faithful := by
    intro s hs hfix
    have hs' := (mem_Lbar_mul_iff S h g).mp hs
    have h1 := H11.faithful _ hs' fun v hv => by
      have hv' : ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈
          S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := by
        rw [QG_inf_Qa_mul h, mem_clSub_map_conj_iff h inf_le_left, inv_apply_apply_O]
        exact hv
      have := hfix _ hv'
      simp only [coe_mul_apply, this, inv_apply_apply_O]
    have : s = S.ρ h * ((S.ρ h)⁻¹ * s * S.ρ h) * (S.ρ h)⁻¹ := by group
    rw [this, h1, mul_one, mul_inv_cancel]

end CFSG.LargeExtraspecial.S4
