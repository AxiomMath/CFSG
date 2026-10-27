module

public import CFSG.LargeExtraspecial.S5Swap
public import CFSG.LargeExtraspecial.S5Lay
public import CFSG.LocalAnalysis.ComponentClassification.SwappedQuasisimpleProduct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open CFSG.ComponentClassification

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

namespace SwapData

variable (D : SwapData S g)

@[expose] noncomputable def Xhat : Subgroup S.O := D.chi.range

theorem isQuasisimple_Z : CFSG.Open.IsQuasisimple D.Z := D.isComponentOf.2.2

theorem Z_le_Mbar : D.Z ≤ S.Mbar := D.isComponentOf.1

theorem isQuasisimple_Xhat : CFSG.Open.IsQuasisimple D.Xhat :=
  SwappedQuasisimpleProduct.diagonal_quasisimple D.Z D.isQuasisimple_Z (MulAut.conj D.t)
    D.commutator_eq_bot

theorem chi_mem_Xhat (z : D.Z) : D.chi z ∈ D.Xhat := ⟨z, rfl⟩

theorem mem_Xhat_iff {x : S.O} : x ∈ D.Xhat ↔ ∃ z : D.Z, D.chi z = x := Iff.rfl

theorem Xhat_le_Mbar : D.Xhat ≤ S.Mbar := by
  rintro _ ⟨z, rfl⟩
  rw [chi_apply]
  exact S.Mbar.mul_mem (D.Z_le_Mbar z.2) (D.isComponentOf_W.1 (D.conj_mem_W z.2))

theorem involutive (H : Hyp4 S g) : Function.Involutive (MulAut.conj D.t) := by
  intro x
  simp only [MulAut.conj_apply]
  calc D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * x * (D.t * D.t)⁻¹ := by group
    _ = x := by rw [D.t_mul_t H, one_mul, inv_one, mul_one]

theorem conj_comp_conj (H : Hyp4 S g) :
    (MulAut.conj D.t).toMonoidHom.comp (MulAut.conj D.t).toMonoidHom = MonoidHom.id S.O :=
  MonoidHom.ext fun x => D.involutive H x

theorem Xhat_le_sup_inf (H : Hyp4 S g) :
    D.Xhat ≤ (D.Z ⊔ D.W) ⊓ centralizer ({D.t} : Set S.O) := by
  have h := SwappedQuasisimpleProduct.diagonal_le_fixed D.Z (MulAut.conj D.t) (D.involutive H)
    D.commutator_eq_bot
  intro x hx
  obtain ⟨h1, h2⟩ := h hx
  refine ⟨h1, mem_centralizer_singleton_iff.mpr ?_⟩
  have h2' : D.t * x * D.t⁻¹ = x := h2
  calc x * D.t = D.t * x * D.t⁻¹ * D.t := by rw [h2']
    _ = D.t * x := by group

theorem Xhat_le_centralizer (H : Hyp4 S g) : D.Xhat ≤ centralizer ({D.t} : Set S.O) :=
  (D.Xhat_le_sup_inf H).trans inf_le_right

theorem fixedSubgroup_eq :
    FixedCommutingProduct.fixedSubgroup (MulAut.conj D.t) = centralizer ({D.t} : Set S.O) := by
  ext x
  change D.t * x * D.t⁻¹ = x ↔ x ∈ centralizer ({D.t} : Set S.O)
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * D.t = D.t * x * D.t⁻¹ * D.t := by rw [h]
      _ = D.t * x := by group
  · intro h
    rw [← h]
    group

theorem isSubnormal_Xhat (H : Hyp4 S g) :
    IsSubnormal D.Xhat (S.Mbar ⊓ centralizer ({D.t} : Set S.O)) := by
  set P := (D.Z ⊔ D.W) ⊓ centralizer ({D.t} : Set S.O) with hP
  have hder := SwappedQuasisimpleProduct.derived_product_fixed_eq_diagonal D.Z D.isQuasisimple_Z
    (MulAut.conj D.t) (D.involutive H) D.commutator_eq_bot
  rw [D.fixedSubgroup_eq] at hder
  change ⁅P, P⁆ = D.Xhat at hder
  have hXP : D.Xhat ≤ P := D.Xhat_le_sup_inf H
  have hnorm : (D.Xhat.subgroupOf P).Normal := by
    rw [← hder]
    have e : (⁅P, P⁆).subgroupOf P = commutator P := by
      rw [← map_subtype_commutator]
      exact comap_map_eq_self_of_injective P.subtype_injective _
    rw [e]
    infer_instance
  have h1 : IsSubnormal D.Xhat P :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hXP hnorm
  have h2 : IsSubnormal P (S.Mbar ⊓ centralizer ({D.t} : Set S.O)) :=
    CFSG.ClassicalInvolution.isSubnormal_inf
      (isSubnormal_sup_of_isComponentOf D.isComponentOf D.isComponentOf_W) _
  exact CFSG.ClassicalInvolution.isSubnormal_trans h1 h2

@[expose] noncomputable def chiR : D.Z →* D.Xhat := D.chi.rangeRestrict

theorem chiR_surjective : Function.Surjective D.chiR := D.chi.rangeRestrict_surjective

theorem coe_chiR (z : D.Z) : (D.chiR z : S.O) = D.chi z := rfl

theorem center_Xhat_eq : (center D.Z).map D.chiR = center D.Xhat := by
  have : Group.IsPerfect D.Z := ⟨D.isQuasisimple_Z.1⟩
  refine Quasisimple.center_map_of_central_kernel D.chiR D.chiR_surjective ?_
  have hker : D.chiR.ker = D.chi.ker := by
    ext z
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg Subtype.val h
      simpa [coe_chiR] using this
    · intro h
      exact Subtype.ext (by simpa [coe_chiR] using h)
  rw [hker]
  exact SwappedQuasisimpleProduct.diagonal_kernel_central D.Z (MulAut.conj D.t)
    D.commutator_eq_bot

theorem eq_one_of_mem_center_Xhat {c : S.O} (hcX : c ∈ D.Xhat)
    (hc : ∀ y ∈ D.Xhat, c * y = y * c) {k : ℕ} (hk : c ^ (2 ^ k) = 1) : c = 1 := by
  have hcen : (⟨c, hcX⟩ : D.Xhat) ∈ center D.Xhat :=
    mem_center_iff.mpr fun y => Subtype.ext (hc y y.2).symm
  rw [← D.center_Xhat_eq] at hcen
  obtain ⟨w, hw, hwc⟩ := hcen
  have hZsub := D.isComponentOf.2.1
  have hodd : Odd (orderOf (w : S.O)) := by
    refine odd_orderOf_of_forall (C := {x : S.O | ∃ h : x ∈ D.Z, ⟨x, h⟩ ∈ center D.Z})
      ?_ ?_ ⟨w.2, hw⟩
    · rintro x ⟨hxZ, hxc⟩ n
      exact ⟨D.Z.pow_mem hxZ n, by
        have := (center D.Z).pow_mem hxc n
        simpa using this⟩
    · rintro y ⟨hyZ, hyc⟩ j hj
      exact eq_one_of_mem_center_of_pow S hZsub hyZ
        (fun z hz => congrArg Subtype.val ((mem_center_iff.mp hyc) ⟨z, hz⟩).symm) hj
  have hc1 : c ^ orderOf (w : S.O) = 1 := by
    have e : D.chi w = c := by
      have := congrArg Subtype.val hwc
      simpa [coe_chiR] using this
    rw [← e, ← map_pow]
    have : w ^ orderOf (w : S.O) = 1 := by
      apply Subtype.ext
      simp [pow_orderOf_eq_one]
    rw [this, map_one]
  exact eq_one_of_pow_odd_of_pow_two hodd hc1 hk

theorem commute_of_chi_commute (z : D.Z) (hz : ∀ y ∈ D.Xhat, D.chi z * y = y * D.chi z)
    {w : S.O} (hw : w ∈ D.Z) : (z : S.O) * w = w * z := by
  have : Group.IsPerfect D.Z := ⟨D.isQuasisimple_Z.1⟩
  have hker : D.chiR.ker ≤ center D.Z := by
    intro x hx
    have hx' : D.chi x = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa [coe_chiR] using this
    exact SwappedQuasisimpleProduct.diagonal_kernel_central D.Z (MulAut.conj D.t)
      D.commutator_eq_bot (MonoidHom.mem_ker.mpr hx')
  have hc := Quasisimple.center_comap_of_central_kernel D.chiR D.chiR_surjective hker
  have hzc : z ∈ (center D.Xhat).comap D.chiR :=
    mem_center_iff.mpr fun y => Subtype.ext (hz y y.2).symm
  rw [hc] at hzc
  exact congrArg Subtype.val ((mem_center_iff.mp hzc) ⟨w, hw⟩).symm

theorem map_conj_W {y : S.O} (hyt : y * D.t = D.t * y) :
    D.W.map (MulAut.conj y).toMonoidHom =
      (D.Z.map (MulAut.conj y).toMonoidHom).map (MulAut.conj D.t).toMonoidHom := by
  rw [W, map_map, map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply]
  calc y * (D.t * x * D.t⁻¹) * y⁻¹ = (y * D.t) * x * (y * D.t)⁻¹ := by group
    _ = (D.t * y) * x * (D.t * y)⁻¹ := by rw [hyt]
    _ = D.t * (y * x * y⁻¹) * D.t⁻¹ := by group

theorem map_conj_Z_eq_or (H : Hyp4 S g) {s : S.O} (hsZ : s ∈ D.Z) (hs1 : s ≠ 1) {k : ℕ}
    (hsk : s ^ (2 ^ k) = 1) (hsL : D.chi ⟨s, hsZ⟩ ∈ S.Lbar g) {y : S.O} (hy : y ∈ S.Lbar g) :
    D.Z.map (MulAut.conj y).toMonoidHom = D.Z ∨ D.Z.map (MulAut.conj y).toMonoidHom = D.W := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  have hyM : y ∈ S.Mbar := S.Lbar_le_Mbar g hy
  have hyt : y * D.t = D.t * y := S4.Lbar_comm S H.conj_mem hy D.mem_Lbar
  have hZy := isComponentOf_map_conj D.isComponentOf hyM
  have hWy := isComponentOf_map_conj D.isComponentOf_W hyM
  have h3 : D.W.map (MulAut.conj y).toMonoidHom ≠ D.Z := by
    intro h
    apply h2
    have e := congrArg (Subgroup.map (MulAut.conj D.t).toMonoidHom) h
    rw [D.map_conj_W hyt, map_map, D.conj_comp_conj H, map_id] at e
    exact e
  set c := D.chi ⟨s, hsZ⟩ with hc
  have hcy : y * c * y⁻¹ = c := by
    rw [S4.Lbar_comm S H.conj_mem hy hsL, mul_inv_cancel_right]
  have hcZ : ∀ w ∈ D.Z, c * w = w * c := by
    intro w hw
    have e : c = (y * s * y⁻¹) * (y * (D.t * s * D.t⁻¹) * y⁻¹) := by
      rw [← hcy, hc, chi_apply]
      group
    have ha : y * s * y⁻¹ ∈ D.Z.map (MulAut.conj y).toMonoidHom := ⟨s, hsZ, rfl⟩
    have hb : y * (D.t * s * D.t⁻¹) * y⁻¹ ∈ D.W.map (MulAut.conj y).toMonoidHom :=
      ⟨_, D.conj_mem_W hsZ, rfl⟩
    have hwa := mul_comm_of_isComponentOf_ne hZy D.isComponentOf h1 ha hw
    have hwb := mul_comm_of_isComponentOf_ne hWy D.isComponentOf h3 hb hw
    rw [e, mul_assoc, hwb, ← mul_assoc, hwa, mul_assoc]
  have hsc : ∀ w ∈ D.Z, s * w = w * s := by
    intro w hw
    have hts : (D.t * s * D.t⁻¹) * w = w * (D.t * s * D.t⁻¹) :=
      (D.mul_comm_of_mem hw (D.conj_mem_W hsZ)).symm
    have e : s = c * (D.t * s * D.t⁻¹)⁻¹ := by rw [hc, chi_apply]; group
    have hts' : (D.t * s * D.t⁻¹)⁻¹ * w = w * (D.t * s * D.t⁻¹)⁻¹ :=
      (Commute.inv_left hts).eq
    rw [e, mul_assoc, hts', ← mul_assoc, hcZ w hw, mul_assoc]
  exact hs1 (eq_one_of_mem_center_of_pow S D.isComponentOf.2.1 hsZ hsc hsk)

theorem conj_mem_Xhat (H : Hyp4 S g) {s : S.O} (hsZ : s ∈ D.Z) (hs1 : s ≠ 1) {k : ℕ}
    (hsk : s ^ (2 ^ k) = 1) (hsL : D.chi ⟨s, hsZ⟩ ∈ S.Lbar g) {y : S.O} (hy : y ∈ S.Lbar g)
    {x : S.O} (hx : x ∈ D.Xhat) : y * x * y⁻¹ ∈ D.Xhat := by
  have hyt : y * D.t = D.t * y := S4.Lbar_comm S H.conj_mem hy D.mem_Lbar
  have hsup : (D.Z ⊔ D.W).map (MulAut.conj y).toMonoidHom = D.Z ⊔ D.W := by
    rw [Subgroup.map_sup, D.map_conj_W hyt]
    rcases D.map_conj_Z_eq_or H hsZ hs1 hsk hsL hy with h | h
    · rw [h]
      rfl
    · rw [h, W, map_map, D.conj_comp_conj H, map_id, sup_comm]
  have hyC : y ∈ centralizer ({D.t} : Set S.O) := mem_centralizer_singleton_iff.mpr hyt
  have hcen : (centralizer ({D.t} : Set S.O)).map (MulAut.conj y).toMonoidHom =
      centralizer ({D.t} : Set S.O) :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hyC)
  have hP : ((D.Z ⊔ D.W) ⊓ centralizer ({D.t} : Set S.O)).map (MulAut.conj y).toMonoidHom =
      (D.Z ⊔ D.W) ⊓ centralizer ({D.t} : Set S.O) := by
    rw [map_inf _ _ _ (MulAut.conj y).injective, hsup, hcen]
  have hder := SwappedQuasisimpleProduct.derived_product_fixed_eq_diagonal D.Z D.isQuasisimple_Z
    (MulAut.conj D.t) (D.involutive H) D.commutator_eq_bot
  rw [D.fixedSubgroup_eq] at hder
  change ⁅(D.Z ⊔ D.W) ⊓ centralizer ({D.t} : Set S.O),
    (D.Z ⊔ D.W) ⊓ centralizer ({D.t} : Set S.O)⁆ = D.Xhat at hder
  have hXm : D.Xhat.map (MulAut.conj y).toMonoidHom = D.Xhat := by
    rw [← hder, map_commutator, hP]
  rw [← hXm]
  exact ⟨x, hx, rfl⟩

end SwapData

end CFSG.LargeExtraspecial.S5
