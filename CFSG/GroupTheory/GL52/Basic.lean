module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix

abbrev V5 : Type := Fin 5 → ZMod 2

abbrev M5 : Type := Matrix (Fin 5) (Fin 5) (ZMod 2)

abbrev G52 : Type := GL (Fin 5) (ZMod 2)

@[expose] def commDim (x : G52) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (Matrix.toLin' ((x : M5) - 1)))

@[expose] def affAct : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative (Fin 3 → ZMod 2)) where
  toFun B :=
    { toFun := fun v => Multiplicative.ofAdd ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.toAdd)
      invFun := fun v =>
        Multiplicative.ofAdd (((B⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          v.toAdd)
      left_inv := fun v => by
        simp only [toAdd_ofAdd, mulVec_mulVec]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
        rfl
      right_inv := fun v => by
        simp only [toAdd_ofAdd, mulVec_mulVec]
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
        rfl
      map_mul' := fun v w => by
        simp only [toAdd_mul, mulVec_add, ofAdd_add] }
  map_one' := MulEquiv.ext fun v => by
    simp only [Units.val_one, one_mulVec, MulEquiv.coe_mk, Equiv.coe_fn_mk, ofAdd_toAdd]
    rfl
  map_mul' B C := MulEquiv.ext fun v => by
    simp only [Units.val_mul, MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply, toAdd_ofAdd,
      mulVec_mulVec]

abbrev Hol8 : Type :=
  Multiplicative (Fin 3 → ZMod 2) ⋊[affAct] GL (Fin 3) (ZMod 2)

section Groups

variable {G : Type*} [Group G]

@[expose] def IsInnerDirectProduct (A B C : Subgroup G) : Prop :=
  A ⊔ B = C ∧ A ⊓ B = ⊥ ∧ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a

@[expose] def IsFrobeniusSubgroup (Y : Subgroup G) : Prop :=
  ∃ K R : Subgroup Y, IsFrobeniusGroupWithKernelComplement K R

end Groups

theorem ext_cols {A B : M5} (h : ∀ j : Fin 5, A *ᵥ Pi.single j 1 = B *ᵥ Pi.single j 1) :
    A = B := by
  ext i j
  have := congrFun (h j) i
  simpa [mulVec_single_one] using this

@[expose] def mk5 (A B : M5) (h : A * B = 1) : G52 :=
  ⟨A, B, h, mul_eq_one_comm.1 h⟩

@[simp] theorem coe_mk5 (A B : M5) (h : A * B = 1) : ((mk5 A B h : G52) : M5) = A :=
  rfl

@[simp] theorem coe_mk5_inv (A B : M5) (h : A * B = 1) :
    (((mk5 A B h)⁻¹ : G52) : M5) = B :=
  rfl

theorem mulVec_comm {g x : M5} (h : g * x = x * g) (v : V5) :
    g *ᵥ (x *ᵥ v) = x *ᵥ (g *ᵥ v) := by
  rw [mulVec_mulVec, h, ← mulVec_mulVec]

@[expose] def fixSub (S : Set V5) : Subgroup G52 where
  carrier := {g | ∀ v ∈ S, (g : M5) *ᵥ v = v}
  one_mem' := fun v _ => by simp
  mul_mem' := fun {a b} ha hb v hv => by
    simp only [Set.mem_ofPred_eq] at ha hb
    rw [Units.val_mul, ← mulVec_mulVec, hb v hv, ha v hv]
  inv_mem' := fun {a} ha v hv => by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha v hv]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem eq_zero_of_mulVec_eq_zero (g : G52) {v : V5} (h : (g : M5) *ᵥ v = 0) : v = 0 := by
  have h' := congrArg (fun w => ((g⁻¹ : G52) : M5) *ᵥ w) h
  simp only [mulVec_mulVec, mulVec_zero] at h'
  rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h'

@[expose] def colMat (b : Fin 5 → V5) : M5 :=
  Matrix.of fun i j => b j i

theorem colMat_mulVec_single (b : Fin 5 → V5) (j : Fin 5) :
    colMat b *ᵥ Pi.single j 1 = b j := by
  ext i
  simp [colMat]

theorem isConj_of_basis {x y : G52} (b : Fin 5 → V5) (hb : LinearIndependent (ZMod 2) b)
    (h : ∀ j, (x : M5) *ᵥ b j = ∑ i, (y : M5) i j • b i) : IsConj y x := by
  have hB : IsUnit (colMat b) := by
    rw [← linearIndependent_cols_iff_isUnit]
    exact hb
  obtain ⟨c, hc⟩ := hB
  have hxc : (x : M5) * (c : M5) = (c : M5) * (y : M5) := by
    refine ext_cols fun j => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, hc, colMat_mulVec_single, h j, mulVec_single_one]
    ext i
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colMat,
      of_apply, col_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  refine isConj_iff.2 ⟨c, Units.ext ?_⟩
  simp only [Units.val_mul]
  rw [← hxc, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem commDim_conj (g x : G52) : commDim (g * x * g⁻¹) = commDim x := by
  unfold commDim
  have e : ((g * x * g⁻¹ : G52) : M5) - 1 = (g : M5) * ((x : M5) - 1) * ((g⁻¹ : G52) : M5) := by
    rw [mul_sub, sub_mul, mul_one, Units.val_mul, Units.val_mul, ← Units.val_mul g g⁻¹,
      mul_inv_cancel, Units.val_one]
  rw [e, toLin'_mul, toLin'_mul, LinearMap.range_comp_of_range_eq_top]
  · rw [LinearMap.range_comp]
    let eg : V5 ≃ₗ[ZMod 2] V5 := Matrix.toLinearEquiv' (g : M5) (Units.invertible g)
    have hge : (toLin' (g : M5)) = (eg : V5 →ₗ[ZMod 2] V5) :=
      (Matrix.toLinearEquiv'_apply _ _).symm
    rw [hge, LinearEquiv.finrank_map_eq]
  · rw [LinearMap.range_eq_top]
    intro v
    refine ⟨(g : M5) *ᵥ v, ?_⟩
    rw [toLin'_apply, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mulVec]

section Conj

open scoped Pointwise

variable {G : Type*} [Group G]

theorem centralizer_conj (c x : G) :
    Subgroup.centralizer {c * x * c⁻¹} =
      (Subgroup.centralizer {x}).map (MulAut.conj c).toMonoidHom := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hg
    refine ⟨c⁻¹ * g * c, ?_, by group⟩
    calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * g) * c := by rw [hg]
      _ = x * (c⁻¹ * g * c) := by group
  · rintro ⟨h, hh, rfl⟩
    calc c * h * c⁻¹ * (c * x * c⁻¹) = c * (h * x) * c⁻¹ := by group
      _ = c * (x * h) * c⁻¹ := by rw [hh]
      _ = c * x * c⁻¹ * (c * h * c⁻¹) := by group

theorem centralizer_map_conj (c : G) (H : Subgroup G) :
    Subgroup.centralizer ((H.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (H : Set G)).map (MulAut.conj c).toMonoidHom := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro hg
    refine ⟨c⁻¹ * g * c, fun h hh => ?_, by group⟩
    have := hg h hh
    calc h * (c⁻¹ * g * c) = c⁻¹ * ((c * h * c⁻¹) * g) * c := by group
      _ = c⁻¹ * (g * (c * h * c⁻¹)) * c := by rw [this]
      _ = c⁻¹ * g * c * h := by group
  · rintro ⟨k, hk, rfl⟩ h hh
    have := hk h hh
    calc c * h * c⁻¹ * (c * k * c⁻¹) = c * (h * k) * c⁻¹ := by group
      _ = c * (k * h) * c⁻¹ := by rw [this]
      _ = c * k * c⁻¹ * (c * h * c⁻¹) := by group

theorem normalizer_map_conj (c : G) (H : Subgroup G) :
    Subgroup.normalizer ((H.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (H : Set G)).map (MulAut.conj c).toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq H (MulAut.conj c)).symm

theorem exists_eq_map_conj_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P₀ P : Sylow p G) :
    ∃ c : G, (P : Subgroup G) = (P₀ : Subgroup G).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P₀ P
  refine ⟨c, ?_⟩
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

theorem card_eq_mul_of_cosets [Finite G] {N C : Subgroup G} (hCN : C ≤ N) {φ : G} (hφ : φ ∈ N)
    {r : ℕ} (hcover : ∀ g ∈ N, ∃ j < r, (φ ^ j)⁻¹ * g ∈ C)
    (hdisj : ∀ j < r, φ ^ j ∈ C → j = 0) : Nat.card N = r * Nat.card C := by
  let f : Fin r × C → N := fun x => ⟨φ ^ (x.1 : ℕ) * x.2, mul_mem (pow_mem hφ _) (hCN x.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨j, c⟩ ⟨j', c'⟩ h
      have h' : φ ^ (j : ℕ) * (c : G) = φ ^ (j' : ℕ) * c' := congrArg Subtype.val h
      have key : ∀ {a b : ℕ}, a < r → b < r → a ≤ b → ∀ {x y : G}, x ∈ C → y ∈ C →
          φ ^ a * x = φ ^ b * y → a = b := by
        intro a b ha hb hab x y hx hy hxy
        have e : φ ^ (b - a) = x * y⁻¹ := by
          have h1 : φ ^ b = φ ^ a * φ ^ (b - a) := by
            rw [← pow_add, Nat.add_sub_cancel' hab]
          rw [h1, mul_assoc] at hxy
          have h2 := mul_left_cancel hxy
          rw [h2, mul_inv_cancel_right]
        have := hdisj (b - a) (by omega) (by rw [e]; exact mul_mem hx (inv_mem hy))
        omega
      have hjj : (j : ℕ) = j' := by
        rcases le_total (j : ℕ) j' with hle | hle
        · exact key j.2 j'.2 hle c.2 c'.2 h'
        · exact (key j'.2 j.2 hle c'.2 c.2 h'.symm).symm
      have hj : j = j' := Fin.ext hjj
      subst hj
      have hc : (c : G) = c' := mul_left_cancel h'
      rw [Subtype.ext hc]
    · rintro ⟨g, hg⟩
      obtain ⟨j, hj, hc⟩ := hcover g hg
      refine ⟨(⟨j, hj⟩, ⟨_, hc⟩), Subtype.ext ?_⟩
      change φ ^ j * ((φ ^ j)⁻¹ * g) = g
      rw [mul_inv_cancel_left]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem isFrobeniusSubgroup_of_fixedPointFree {Y K R : Subgroup G} (hKY : K ≤ Y) (hRY : R ≤ Y)
    (hnorm : Y ≤ Subgroup.normalizer (K : Set G)) (hinf : K ⊓ R = ⊥) (hsup : K ⊔ R = Y)
    (hfpf : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k) (hK : K ≠ ⊥) (hR : R ≠ ⊥) :
    IsFrobeniusSubgroup Y := by
  classical
  have hKR : ∀ y ∈ Y, ∃ k ∈ K, ∃ r ∈ R, k * r = y := by
    intro y hy
    rw [← hsup] at hy
    have hmul : ((K ⊔ R : Subgroup G) : Set G) = (K : Set G) * (R : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left K R (fun r hr => hnorm (hRY hr))
    have hy' : y ∈ ((K ⊔ R : Subgroup G) : Set G) := hy
    rw [hmul] at hy'
    obtain ⟨k, hk, r, hr, rfl⟩ := hy'
    exact ⟨k, hk, r, hr, rfl⟩
  refine ⟨K.subgroupOf Y, R.subgroupOf Y, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 hnorm
  · show Function.Bijective _
    constructor
    · rintro ⟨⟨⟨k, hk⟩, hk'⟩, ⟨⟨r, hr⟩, hr'⟩⟩ ⟨⟨⟨k', hk₂⟩, hk₂'⟩, ⟨⟨r', hr₂⟩, hr₂'⟩⟩ h
      have h' : k * r = k' * r' := congrArg (fun x : Y => (x : G)) h
      replace hk' : k ∈ K := Subgroup.mem_subgroupOf.1 hk'
      replace hr' : r ∈ R := Subgroup.mem_subgroupOf.1 hr'
      replace hk₂' : k' ∈ K := Subgroup.mem_subgroupOf.1 hk₂'
      replace hr₂' : r' ∈ R := Subgroup.mem_subgroupOf.1 hr₂'
      have e : k'⁻¹ * k = r' * r⁻¹ := by
        calc k'⁻¹ * k = k'⁻¹ * (k * r) * r⁻¹ := by group
          _ = k'⁻¹ * (k' * r') * r⁻¹ := by rw [h']
          _ = r' * r⁻¹ := by group
      have hmem : k'⁻¹ * k ∈ K ⊓ R :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hk₂') hk', by rw [e]; exact mul_mem hr₂' (inv_mem hr')⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      have hkk : k = k' := by
        calc k = k' * (k'⁻¹ * k) := by group
          _ = k' := by rw [hmem, mul_one]
      subst hkk
      have hrr : r = r' := mul_left_cancel h'
      subst hrr
      rfl
    · rintro ⟨y, hy⟩
      obtain ⟨k, hk, r, hr, rfl⟩ := hKR y hy
      exact ⟨(⟨⟨k, hKY hk⟩, hk⟩, ⟨⟨r, hRY hr⟩, hr⟩), rfl⟩
  · rintro ⟨g, hgY⟩ hg
    rw [Subgroup.disjoint_def]
    rintro ⟨x, hxY⟩ hx hx'
    replace hx : x ∈ R := Subgroup.mem_subgroupOf.1 hx
    have hgR : g ∉ R := fun h => hg (Subgroup.mem_subgroupOf.2 h)
    obtain ⟨k, hk, r, hr, rfl⟩ := hKR g hgY
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [one_mul] at hgR
      exact hgR hr
    obtain ⟨⟨y, hyY⟩, hy, hxy⟩ := hx'
    have hy : y ∈ R := Subgroup.mem_subgroupOf.1 hy
    have hxy' : x = k * r * y * (k * r)⁻¹ := by
      have := congrArg Subtype.val hxy
      simpa [MulAut.conj_apply] using this.symm
    set y' := r * y * r⁻¹ with hy'
    have hy'R : y' ∈ R := mul_mem (mul_mem hr hy) (inv_mem hr)
    have hxk : x = k * y' * k⁻¹ := by rw [hxy', hy']; group
    have hcomm : k * (y' * k⁻¹ * y'⁻¹) ∈ K ⊓ R := by
      refine Subgroup.mem_inf.2 ⟨mul_mem hk ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hnorm (hRY hy'R)) k⁻¹).1 (inv_mem hk)
        exact this
      · have e : k * (y' * k⁻¹ * y'⁻¹) = x * y'⁻¹ := by rw [hxk]; group
        rw [e]
        exact mul_mem hx (inv_mem hy'R)
    rw [hinf, Subgroup.mem_bot] at hcomm
    have hfix : y' * k * y'⁻¹ = k := by
      have e : y' * k⁻¹ * y'⁻¹ = k⁻¹ := by
        calc y' * k⁻¹ * y'⁻¹ = k⁻¹ * (k * (y' * k⁻¹ * y'⁻¹)) := by group
          _ = k⁻¹ := by rw [hcomm, mul_one]
      calc y' * k * y'⁻¹ = (y' * k⁻¹ * y'⁻¹)⁻¹ := by group
        _ = k := by rw [e, inv_inv]
    have hy'1 : y' = 1 := by
      by_contra hne
      exact hfpf y' hy'R hne k hk hk1 hfix
    apply Subtype.ext
    simp only [Subgroup.coe_one]
    rw [hxk, hy'1, mul_one, mul_inv_cancel]
  · intro h
    apply hK
    rw [eq_bot_iff]
    intro k hk
    have : (⟨k, hKY hk⟩ : Y) ∈ K.subgroupOf Y := Subgroup.mem_subgroupOf.2 hk
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · intro h
    apply hR
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, hRY hr⟩ : Y) ∈ R.subgroupOf Y := Subgroup.mem_subgroupOf.2 hr
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this

end Conj

end CFSG.GroupTheory.GL52
