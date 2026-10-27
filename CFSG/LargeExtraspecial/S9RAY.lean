module

public import CFSG.LargeExtraspecial.S6Mod
public import CFSG.LargeExtraspecial.S2Three
public import CFSG.LargeExtraspecial.S6Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

section Sec

variable (X W : Submodule (ZMod 2) S.Qt)

@[expose] noncomputable def secProj : W →ₗ[ZMod 2] ↥(W.map X.mkQ) :=
  LinearMap.codRestrict (W.map X.mkQ) (X.mkQ ∘ₗ W.subtype) fun w => Submodule.mem_map_of_mem w.2

omit [Finite G] in
theorem secProj_apply (w : W) : secProj X W w = secMk X w.2 :=
  rfl

omit [Finite G] in
theorem range_secProj : LinearMap.range (secProj X W) = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  obtain ⟨w, hw, rfl⟩ := exists_secMk X m
  exact ⟨⟨w, hw⟩, rfl⟩

@[expose] noncomputable def secLift : ↥(W.map X.mkQ) →ₗ[ZMod 2] W :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective (secProj X W) (range_secProj X W))

theorem secProj_secLift (m : ↥(W.map X.mkQ)) : secProj X W (secLift X W m) = m := by
  have := Classical.choose_spec
    (LinearMap.exists_rightInverse_of_surjective (secProj X W) (range_secProj X W))
  exact LinearMap.congr_fun this m

theorem secLift_secMk_sub {w : S.Qt} (hw : w ∈ W) :
    ((secLift X W (secMk X hw) : W) : S.Qt) - w ∈ X := by
  have h := congrArg Subtype.val (secProj_secLift X W (secMk X hw))
  rw [secProj_apply, coe_secMk, coe_secMk, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq] at h
  exact h

@[expose] noncomputable def secForm : LinearMap.BilinForm (ZMod 2) ↥(W.map X.mkQ) :=
  S.q.polarBilin.compl₁₂ (W.subtype ∘ₗ secLift X W) (W.subtype ∘ₗ secLift X W)

variable {X W}

theorem secForm_secMk (hXW : X ≤ W) (hperp : ∀ v ∈ X, ∀ w ∈ W, polar S.q v w = 0) {w w' : S.Qt}
    (hw : w ∈ W) (hw' : w' ∈ W) : secForm X W (secMk X hw) (secMk X hw') = polar S.q w w' := by
  have h1 := secLift_secMk_sub X W hw
  have h2 := secLift_secMk_sub X W hw'
  set l := ((secLift X W (secMk X hw) : W) : S.Qt) with hl
  set l' := ((secLift X W (secMk X hw') : W) : S.Qt) with hl'
  have e : secForm X W (secMk X hw) (secMk X hw') = polar S.q l l' := by
    simp [secForm, hl, hl', polarBilin_apply_apply]
  rw [e, show l = w + (l - w) by abel, show l' = w' + (l' - w') by abel, polar_add_left,
    polar_add_right, polar_add_right, hperp _ h1 _ hw', hperp _ h1 _ (hXW h2),
    polar_comm S.q w (l' - w'), hperp _ h2 _ hw]
  simp

theorem secForm_nondegenerate (hXW : X ≤ W) (hperp : ∀ v ∈ X, ∀ w ∈ W, polar S.q v w = 0)
    (hrad : ∀ w ∈ W, (∀ w' ∈ W, polar S.q w w' = 0) → w ∈ X) :
    (secForm X W).Nondegenerate := by
  have hzero : ∀ {w : S.Qt} (hw : w ∈ W), w ∈ X → secMk X hw = 0 := fun hw hwX =>
    Subtype.ext (by rw [coe_secMk, Submodule.coe_zero, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]; exact hwX)
  constructor
  · intro m hm
    obtain ⟨w, hw, rfl⟩ := exists_secMk X m
    refine hzero hw (hrad w hw fun w' hw' => ?_)
    rw [← secForm_secMk hXW hperp hw hw']
    exact hm _
  · intro m hm
    obtain ⟨w, hw, rfl⟩ := exists_secMk X m
    refine hzero hw (hrad w hw fun w' hw' => ?_)
    rw [polar_comm, ← secForm_secMk hXW hperp hw' hw]
    exact hm _

end Sec

section Act

variable (X W : Submodule (ZMod 2) S.Qt) (K : Subgroup S.O)

@[expose] noncomputable def quotHomK (hX : ∀ x ∈ K, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X) :
    K →* ((S.Qt ⧸ X) ≃ₗ[ZMod 2] (S.Qt ⧸ X)) where
  toFun x := Submodule.Quotient.equiv X X ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
    (map_eq_of_le (hX x x.2))
  map_one' := by
    ext v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective X v
    rfl
  map_mul' x y := by
    ext v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective X v
    rfl

@[expose] noncomputable def secHomK (hX : ∀ x ∈ K, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
    (hW : ∀ x ∈ K, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W) :
    K →* (↥(W.map X.mkQ) ≃ₗ[ZMod 2] ↥(W.map X.mkQ)) :=
  restrictHom (quotHomK X K hX) (W.map X.mkQ) (by
    rintro x _ ⟨w, hw, rfl⟩
    exact ⟨_, hW x x.2 w hw, rfl⟩)

variable {X W K}
variable (hX : ∀ x ∈ K, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
  (hW : ∀ x ∈ K, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)

theorem coe_secHomK_secMk (x : K) {w : S.Qt} (hw : w ∈ W) :
    ((secHomK X W K hX hW x (secMk X hw) : ↥(W.map X.mkQ)) : S.Qt ⧸ X) =
      X.mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) :=
  rfl

theorem secHomK_secMk (x : K) {w : S.Qt} (hw : w ∈ W) :
    secHomK X W K hX hW x (secMk X hw) = secMk X (hW x x.2 w hw) :=
  rfl

theorem secForm_secHomK (hXW : X ≤ W) (hperp : ∀ v ∈ X, ∀ w ∈ W, polar S.q v w = 0) (x : K)
    (m n : ↥(W.map X.mkQ)) :
    secForm X W (secHomK X W K hX hW x m) (secHomK X W K hX hW x n) = secForm X W m n := by
  obtain ⟨w, hw, rfl⟩ := exists_secMk X m
  obtain ⟨w', hw', rfl⟩ := exists_secMk X n
  rw [secHomK_secMk, secHomK_secMk, secForm_secMk hXW hperp, secForm_secMk hXW hperp]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (x : S.O).2 w w'

theorem finrank_commSpace_secHomK_le (x : K) :
    finrank (ZMod 2) (commSpace (secHomK X W K hX hW x)) ≤
      finrank (ZMod 2) (commSpace ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hle : (commSpace (secHomK X W K hX hW x)).map (W.map X.mkQ).subtype ≤
      (commSpace ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)).map X.mkQ := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨n, rfl⟩ := mem_commSpace.mp hm
    obtain ⟨w, hw, rfl⟩ := exists_secMk X n
    refine ⟨((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w, sub_mem_commSpace _ w, ?_⟩
    rw [map_sub, Submodule.coe_subtype, Submodule.coe_sub, coe_secHomK_secMk, coe_secMk]
  have e1 := Submodule.finrank_mono hle
  have e2 := Submodule.finrank_map_le X.mkQ (commSpace ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have e3 : finrank (ZMod 2) ↥((commSpace (secHomK X W K hX hW x)).map (W.map X.mkQ).subtype) =
      finrank (ZMod 2) (commSpace (secHomK X W K hX hW x)) :=
    LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm
  omega

theorem apply_sub_mem_of_commSpace_eq_bot (x : K)
    (hbot : commSpace (secHomK X W K hX hW x) = ⊥) {w : S.Qt} (hw : w ∈ W) :
    ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X := by
  have h1 := sub_mem_commSpace (secHomK X W K hX hW x) (secMk X hw)
  rw [hbot, Submodule.mem_bot, sub_eq_zero, secHomK_secMk] at h1
  have h2 := congrArg Subtype.val h1
  rw [coe_secMk, coe_secMk, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq] at h2
  exact h2

omit [Finite G] in
theorem secMk_eq_secMk {w w' : S.Qt} (hw : w ∈ W) (hw' : w' ∈ W) (h : w - w' ∈ X) :
    secMk X hw = secMk X hw' :=
  Subtype.ext (by rw [coe_secMk, coe_secMk, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq]; exact h)

theorem secHomK_eq_comp (x y z : K)
    (h : ∀ w ∈ W, ((z : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w -
      ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ X)
    (m : ↥(W.map X.mkQ)) :
    secHomK X W K hX hW z m = secHomK X W K hX hW x (secHomK X W K hX hW y m) := by
  obtain ⟨w, hw, hm⟩ := exists_secMk X m
  rw [hm, secHomK_secMk, secHomK_secMk, secHomK_secMk]
  exact secMk_eq_secMk _ _ (h w hw)

theorem secHomK_comp_eq_comp (x y x' y' : K)
    (h : ∀ w ∈ W, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      ((y' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ X)
    (m : ↥(W.map X.mkQ)) :
    secHomK X W K hX hW x (secHomK X W K hX hW y m) =
      secHomK X W K hX hW y' (secHomK X W K hX hW x' m) := by
  obtain ⟨w, hw, hm⟩ := exists_secMk X m
  rw [hm, secHomK_secMk, secHomK_secMk, secHomK_secMk, secHomK_secMk]
  exact secMk_eq_secMk _ _ (h w hw)

theorem secHomK_comp_eq_self (x y : K)
    (h : ∀ w ∈ W, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      w ∈ X)
    (m : ↥(W.map X.mkQ)) : secHomK X W K hX hW x (secHomK X W K hX hW y m) = m := by
  obtain ⟨w, hw, hm⟩ := exists_secMk X m
  rw [hm, secHomK_secMk, secHomK_secMk]
  exact secMk_eq_secMk _ _ (h w hw)

theorem finrank_commSpace_secHomK_add_le (x : K) :
    finrank (ZMod 2) (commSpace (secHomK X W K hX hW x)) +
        finrank (ZMod 2) ↥(commSpace ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ X) ≤
      finrank (ZMod 2) (commSpace ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hle : (commSpace (secHomK X W K hX hW x)).map (W.map X.mkQ).subtype ≤
      (commSpace ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)).map X.mkQ := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨n, rfl⟩ := mem_commSpace.mp hm
    obtain ⟨w, hw, rfl⟩ := exists_secMk X n
    refine ⟨((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w, sub_mem_commSpace _ w, ?_⟩
    rw [map_sub, Submodule.coe_subtype, Submodule.coe_sub, coe_secHomK_secMk, coe_secMk]
  have e1 := Submodule.finrank_mono hle
  have e2 := S2.finrank_map_add_finrank_inf_ker X.mkQ
    (commSpace ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
  rw [Submodule.ker_mkQ] at e2
  have e3 : finrank (ZMod 2) ↥((commSpace (secHomK X W K hX hW x)).map (W.map X.mkQ).subtype) =
      finrank (ZMod 2) (commSpace (secHomK X W K hX hW x)) :=
    LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm
  omega

end Act

end CFSG.LargeExtraspecial.S9
