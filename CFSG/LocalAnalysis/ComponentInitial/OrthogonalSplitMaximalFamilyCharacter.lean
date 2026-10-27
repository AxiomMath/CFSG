module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitStabilizer
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSubspaceCount
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasThree

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open scoped commutatorElement

section Hom

variable {G A : Type*} [Group G] [CommGroup A]

theorem le_map_ker_of_commutator_eq {O H : Subgroup G} (hHO : H ≤ O) (hH : ⁅H, H⁆ = H)
    (χ : O →* A) : H ≤ χ.ker.map O.subtype := by
  rw [← hH, Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  refine ⟨⁅(⟨g₁, hHO h₁⟩ : O), ⟨g₂, hHO h₂⟩⁆, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_commute]
  exact Commute.all _ _

theorem subgroupOf_le_ker {O H : Subgroup G} (χ : O →* A) (h : H ≤ χ.ker.map O.subtype) :
    H.subgroupOf O ≤ χ.ker := by
  intro g hg
  obtain ⟨g', hg', hgg'⟩ := h (Subgroup.mem_subgroupOf.1 hg)
  rwa [show g = g' from Subtype.ext hgg'.symm]

theorem int_units_eq_one_of_pow {u : ℤˣ} {n : ℕ} (hn : Odd n) (hu : u ^ n = 1) : u = 1 := by
  rcases Int.units_eq_one_or u with h | h
  · exact h
  · rw [h, hn.neg_one_pow] at hu
    exact absurd hu (by decide)

theorem sign_eq_neg_one_of_involution {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Equiv.Perm α} (h2 : σ ^ 2 = 1) (hfree : ∀ x, σ x ≠ x) {A : ℕ}
    (hcard : Fintype.card α = 2 * A) (hA : Odd A) : Equiv.Perm.sign σ = -1 := by
  have h0 : Fintype.card (Function.fixedPoints σ) = 0 :=
    Fintype.card_eq_zero_iff.2 ⟨fun x => hfree x.1 x.2⟩
  rw [Equiv.Perm.sign_of_pow_two_eq_one h2, h0, Nat.sub_zero, hcard,
    Nat.mul_div_cancel_left _ two_pos, hA.neg_one_pow]

end Hom

section SqOne

variable {G : Type*} [Group G] {K : Type*} [Field K]

theorem units_eq_neg_one_of_sq {u : Kˣ} (hu : u ^ 2 = 1) (h1 : u ≠ 1) : u = -1 := by
  have h : (u : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  rcases sq_eq_one_iff.1 h with h' | h'
  · exact absurd (Units.ext h') h1
  · exact Units.ext (by rw [h', Units.val_neg, Units.val_one])

@[expose] noncomputable def signOfSq (f : G →* Kˣ) (hf : ∀ g, f g ^ 2 = 1) : G →* ℤˣ :=
  open scoped Classical in
  MonoidHom.mk' (fun g => if f g = 1 then 1 else -1) fun a b => by
    by_cases ha : f a = 1 <;> by_cases hb : f b = 1
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
    · have hab : f (a * b) = 1 := by
        rw [map_mul, units_eq_neg_one_of_sq (hf a) ha, units_eq_neg_one_of_sq (hf b) hb]
        simp
      rw [ite_eq_left hab, ite_eq_right ha, ite_eq_right hb]
      decide

theorem signOfSq_eq_one {f : G →* Kˣ} {hf : ∀ g, f g ^ 2 = 1} {g : G} (h : f g = 1) :
    signOfSq f hf g = 1 := by
  rw [signOfSq, MonoidHom.mk'_apply, ite_eq_left h]

theorem signOfSq_eq_neg_one {f : G →* Kˣ} {hf : ∀ g, f g ^ 2 = 1} {g : G} (h : f g ≠ 1) :
    signOfSq f hf g = -1 := by
  rw [signOfSq, MonoidHom.mk'_apply, ite_eq_right h]

theorem coe_signOfSq (f : G →* Kˣ) (hf : ∀ g, f g ^ 2 = 1) (g : G) :
    (((signOfSq f hf g : ℤˣ) : ℤ) : K) = (f g : K) := by
  by_cases h : f g = 1
  · rw [signOfSq_eq_one h, h]
    simp
  · rw [signOfSq_eq_neg_one h, units_eq_neg_one_of_sq (hf g) h]
    simp

end SqOne

section Swap

variable {r : ℕ} {K : Type*} [Field K]

variable (K) in
@[expose] def swapPair (i : Fin r) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.swap (Sum.inl i) (Sum.inr i))

theorem swapPair_apply (i : Fin r) (v : Fin r ⊕ Fin r → K) (c : Fin r ⊕ Fin r) :
    swapPair K i v c = v (Equiv.swap (Sum.inl i) (Sum.inr i) c) :=
  rfl

theorem swapPair_single (i : Fin r) (c : Fin r ⊕ Fin r) :
    swapPair K i (Pi.single c 1) = Pi.single (Equiv.swap (Sum.inl i) (Sum.inr i) c) 1 := by
  funext d
  simp only [swapPair_apply, Pi.single_apply, Equiv.swap_apply_eq_iff]

theorem swapPair_single_inl (i : Fin r) :
    swapPair K i (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inr i) 1 := by
  rw [swapPair_single, Equiv.swap_apply_left]

theorem swapPair_single_inr (i : Fin r) :
    swapPair K i (Pi.single (Sum.inr i) 1) = Pi.single (Sum.inl i) 1 := by
  rw [swapPair_single, Equiv.swap_apply_right]

theorem swapPair_single_of_ne (i : Fin r) {c : Fin r ⊕ Fin r} (h1 : c ≠ Sum.inl i)
    (h2 : c ≠ Sum.inr i) : swapPair K i (Pi.single c 1) = Pi.single c 1 := by
  rw [swapPair_single, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem swapPair_mul_self (i : Fin r) : swapPair K i * swapPair K i = 1 := by
  refine LinearEquiv.ext fun v => funext fun c => ?_
  rw [LinearEquiv.mul_apply, swapPair_apply, swapPair_apply, Equiv.swap_apply_self]
  rfl

theorem quadPlus_swapPair (i : Fin r) (v : Fin r ⊕ Fin r → K) :
    quadPlus r K (swapPair K i v) = quadPlus r K v := by
  rw [quadPlus_apply, quadPlus_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [swapPair_apply, swapPair_apply]
  by_cases hj : j = i
  · subst hj
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]
  · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hj) Sum.inl_ne_inr,
      Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (by simpa using hj)]

theorem det_swapPair (i : Fin r) :
    LinearMap.det (swapPair K i : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = -1 := by
  have h : (swapPair K i : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
      Matrix.toLin' ((Equiv.swap (Sum.inl i) (Sum.inr i)).permMatrix K) := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec]
    rfl
  rw [h, LinearMap.det_toLin', Matrix.det_permutation, Equiv.Perm.sign_swap Sum.inl_ne_inr]
  simp

variable (K) in
@[expose] def swapIso (i : Fin r) : TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) :=
  ⟨swapPair K i, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 (quadPlus_swapPair i)⟩

theorem coe_swapIso (i : Fin r) :
    (swapIso K i : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) = swapPair K i :=
  rfl

theorem swapIso_sq (i : Fin r) : swapIso K i ^ 2 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, pow_two, coe_swapIso, swapPair_mul_self]; rfl)

theorem quadPlus_single_sub_single (i : Fin r) :
    quadPlus r K (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inr i) 1) = -1 := by
  rw [quadPlus_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem polar_single_sub_single (i : Fin r) (w : Fin r ⊕ Fin r → K) :
    polar (quadPlus r K) (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inr i) 1) w =
      w (Sum.inr i) - w (Sum.inl i) := by
  rw [polar_sub_left, polar_single_inl_quadPlus, polar_single_inr_quadPlus]

theorem swapPair_eq_add_smul (i : Fin r) (w : Fin r ⊕ Fin r → K) :
    swapPair K i w = w + polar (quadPlus r K) (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inr i) 1)
      w • (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inr i) 1) := by
  rw [polar_single_sub_single]
  funext c
  rw [swapPair_apply]
  rcases c with j | j <;> by_cases hj : j = i
  · subst hj
    simp
  · simp [hj, Equiv.swap_apply_of_ne_of_ne]
  · subst hj
    simp
  · simp [hj, Equiv.swap_apply_of_ne_of_ne]

end Swap

section Maximal

variable {r : ℕ} {K : Type*} [Field K]

theorem mem_of_forall_polar_eq_zero {L : Submodule K (Fin r ⊕ Fin r → K)}
    (hL : L ∈ singularSubspaces (quadPlus r K) r) {u : Fin r ⊕ Fin r → K}
    (hu : ∀ w ∈ L, polar (quadPlus r K) u w = 0) : u ∈ L := by
  obtain ⟨g, hg, hgL⟩ := exists_isometry_map_eq le_rfl hL
  have hu' : g.symm u ∈ flag r K r := by
    refine mem_flag_top.2 fun j => polar_flag_eq_zero_iff.1 (fun w hw => ?_) j j.2
    rw [← polar_map_of_mem hg, LinearEquiv.apply_symm_apply]
    refine hu _ ?_
    rw [← hgL]
    exact Submodule.mem_map_of_mem hw
  rw [← hgL, ← LinearEquiv.apply_symm_apply g u]
  exact Submodule.mem_map_of_mem hu'

theorem map_swapPair_ne (i : Fin r) {L : Submodule K (Fin r ⊕ Fin r → K)}
    (hL : L ∈ singularSubspaces (quadPlus r K) r) :
    L.map (swapPair K i : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) ≠ L := by
  intro hsL
  have huL : (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inr i) 1 : Fin r ⊕ Fin r → K) ∉ L :=
    fun h => by
      have h0 := hL.2 _ h
      rw [quadPlus_single_sub_single] at h0
      exact one_ne_zero (neg_eq_zero.1 h0)
  apply huL
  by_cases h : ∃ w ∈ L,
      polar (quadPlus r K) (Pi.single (Sum.inl i) 1 - Pi.single (Sum.inr i) 1) w ≠ 0
  · obtain ⟨w, hw, hw0⟩ := h
    have hsw : swapPair K i w ∈ L := by
      rw [← hsL]
      exact Submodule.mem_map_of_mem hw
    have hd := L.sub_mem hsw hw
    rw [swapPair_eq_add_smul, add_sub_cancel_left] at hd
    exact (Submodule.smul_mem_iff L hw0).1 hd
  · simp only [not_exists, not_and, not_not] at h
    exact mem_of_forall_polar_eq_zero hL h

end Maximal

section Perm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem map_mem_singularSubspaces {Q : QuadraticForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {k : ℕ} {X : Submodule K V}
    (hX : X ∈ singularSubspaces Q k) : X.map (g : V →ₗ[K] V) ∈ singularSubspaces Q k := by
  refine ⟨by rw [LinearEquiv.finrank_map_eq]; exact hX.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [LinearEquiv.coe_coe, map_of_mem hg]
  exact hX.2 x hx

theorem map_one_linearEquiv (X : Submodule K V) : X.map ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) = X :=
  Submodule.map_id X

variable (Q : QuadraticForm K V) (k : ℕ)

@[expose] def singularPerm :
    TauCeti.QuadraticMap.orthogonalGroup Q →* Equiv.Perm (singularSubspaces Q k) where
  toFun g :=
    { toFun := fun X =>
        ⟨X.1.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V), map_mem_singularSubspaces g.2 X.2⟩
      invFun := fun X =>
        ⟨X.1.map (((g⁻¹ : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) : V →ₗ[K] V),
          map_mem_singularSubspaces (g⁻¹).2 X.2⟩
      left_inv := fun X => Subtype.ext (by
        dsimp only
        rw [← map_mul_linearEquiv, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
        exact map_one_linearEquiv _)
      right_inv := fun X => Subtype.ext (by
        dsimp only
        rw [← map_mul_linearEquiv, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
        exact map_one_linearEquiv _) }
  map_one' := Equiv.ext fun X => Subtype.ext (map_one_linearEquiv _)
  map_mul' g h := Equiv.ext fun X => Subtype.ext (map_mul_linearEquiv _ _ _)

theorem coe_singularPerm_apply (g : TauCeti.QuadraticMap.orthogonalGroup Q)
    (X : singularSubspaces Q k) :
    (singularPerm Q k g X : Submodule K V) = X.1.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V) :=
  rfl

end Perm

section Characters

variable {r : ℕ} {K : Type*} [Field K]

theorem commutator_orthElementaryGroup (hr : 3 ≤ r) :
    ⁅orthElementaryGroup (quadPlus r K), orthElementaryGroup (quadPlus r K)⁆ =
      orthElementaryGroup (quadPlus r K) :=
  Subgroup.isPerfect_iff.1 (orthogonal_elementary_perfect (nondegenerate_polarBilin_quadPlus r K)
    ⟨flag r K 3, finrank_flag hr, fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩).1

theorem det_of_mem_maxStab {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ maxStab r K) :
    LinearMap.det (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = 1 := by
  obtain ⟨A, C, -, -, hM⟩ := exists_toMatrix'_of_mem_maxStab hg
  rw [← LinearMap.det_toMatrix', hM, det_fromBlocks_params]

variable (r K) in
@[expose] noncomputable def detChar :
    TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) →* ℤˣ :=
  signOfSq (orthogonalDet (quadPlus r K))
    (TauCeti.QuadraticMap.orthogonalDet_sq (nondegenerate_polarBilin_quadPlus r K).1)

theorem coe_detChar (g : TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) :
    (((detChar r K g : ℤˣ) : ℤ) : K) =
      LinearMap.det ((g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) := by
  rw [detChar, coe_signOfSq, orthogonalDet_apply, LinearEquiv.coe_det]

theorem detChar_eq_one_of_mem_maxStab {g : TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)}
    (hg : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈ maxStab r K) :
    detChar r K g = 1 := by
  refine signOfSq_eq_one (Units.ext ?_)
  rw [orthogonalDet_apply, LinearEquiv.coe_det, Units.val_one, det_of_mem_maxStab hg]

theorem neg_one_ne_one_of_odd [Finite K] (hq : Odd (Nat.card K)) : (-1 : K) ≠ 1 := by
  intro h
  have := Fintype.ofFinite K
  have h2 := FiniteField.even_card_iff_char_two.1 (neg_one_eq_one_iff.1 h)
  rw [Nat.card_eq_fintype_card] at hq
  exact (Nat.not_even_iff_odd.2 hq) (Nat.even_iff.2 h2)

theorem detChar_swapIso [Finite K] (hq : Odd (Nat.card K)) (i : Fin r) :
    detChar r K (swapIso K i) = -1 := by
  refine signOfSq_eq_neg_one fun h => neg_one_ne_one_of_odd hq ?_
  have h' := congrArg Units.val h
  rwa [orthogonalDet_apply, LinearEquiv.coe_det, coe_swapIso, det_swapPair, Units.val_one] at h'

variable (r K) in
@[expose] noncomputable def maxSign [Finite K] :
    TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) →* ℤˣ :=
  letI : Fintype (singularSubspaces (quadPlus r K) r) := Fintype.ofFinite _
  letI : DecidableEq (singularSubspaces (quadPlus r K) r) := Classical.decEq _
  Equiv.Perm.sign.comp (singularPerm (quadPlus r K) r)

theorem card_maximal [Finite K] (hr : 1 ≤ r) :
    Nat.card (singularSubspaces (quadPlus r K) r) =
      2 * ∏ i ∈ Finset.Icc 1 (r - 1), (Nat.card K ^ i + 1) := by
  have h := card_singularSubspaces_top (K := K) hr
  exact_mod_cast h

theorem odd_prod_pow_add_one {q : ℕ} (hq : Even q) (n : ℕ) :
    Odd (∏ i ∈ Finset.Icc 1 n, (q ^ i + 1)) :=
  Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun i hi =>
    (hq.pow_of_ne_zero (by have := (Finset.mem_Icc.1 hi).1; omega)).add_one

theorem maxSign_swapIso [Finite K] (hr : 1 ≤ r) (hq : Even (Nat.card K)) (i : Fin r) :
    maxSign r K (swapIso K i) = -1 := by
  let _ : Fintype (singularSubspaces (quadPlus r K) r) := Fintype.ofFinite _
  let _ : DecidableEq (singularSubspaces (quadPlus r K) r) := Classical.decEq _
  change Equiv.Perm.sign (singularPerm (quadPlus r K) r (swapIso K i)) = -1
  refine sign_eq_neg_one_of_involution ?_ (fun L hL => ?_) ?_ (odd_prod_pow_add_one hq (r - 1))
  · rw [← map_pow, swapIso_sq, map_one]
  · exact map_swapPair_ne i L.2 (congrArg Subtype.val hL)
  · rw [← Nat.card_eq_fintype_card, card_maximal hr]

theorem maxStab_le_map_ker [Finite K] (hq : Even (Nat.card K))
    (χ : TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) →* ℤˣ)
    (hE : orthElementaryGroup (quadPlus r K) ≤
      χ.ker.map (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)).subtype) :
    maxStab r K ≤ χ.ker.map (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)).subtype := by
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units]
    obtain ⟨m, hm⟩ := hq
    have : 0 < Nat.card K := Nat.card_pos
    exact ⟨m - 1, by omega⟩
  have htorus : ∀ d, torusElt r K d ∈ maxStab r K := fun d => by
    rw [maxStab_eq_closure]
    exact Subgroup.subset_closure (Or.inl (Or.inl ⟨d, rfl⟩))
  rw [maxStab_eq_closure, Subgroup.closure_le]
  rintro g ((⟨d, rfl⟩ | ⟨i, j, t, -, rfl⟩) | ⟨i, j, t, -, rfl⟩)
  · have hd : d ^ Nat.card Kˣ = 1 :=
      funext fun i => by rw [Pi.pow_apply, pow_card_eq_one', Pi.one_apply]
    have hpow : (⟨torusElt r K d, (mem_maxStab.1 (htorus d)).1⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ^ Nat.card Kˣ = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hd, map_one]; rfl)
    exact ⟨_, int_units_eq_one_of_pow hodd (by rw [← map_pow, hpow, map_one]), rfl⟩
  · exact hE (eichler_mem_elementaryGroup _ _ _)
  · exact hE (eichler_mem_elementaryGroup _ _ _)

end Characters

theorem orthogonal_geometry_split_maximal_family_character {K : Type*} [Field K] [Finite K]
    {r : ℕ} (hr : 3 ≤ r) :
    (swapIso K (⟨r - 1, by omega⟩ : Fin r) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
        (Pi.single (.inl ⟨r - 1, by omega⟩) 1) = Pi.single (.inr ⟨r - 1, by omega⟩) 1 ∧
      (swapIso K (⟨r - 1, by omega⟩ : Fin r) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
        (Pi.single (.inr ⟨r - 1, by omega⟩) 1) = Pi.single (.inl ⟨r - 1, by omega⟩) 1 ∧
      (∀ c : Fin r ⊕ Fin r, c ≠ .inl ⟨r - 1, by omega⟩ → c ≠ .inr ⟨r - 1, by omega⟩ →
        (swapIso K (⟨r - 1, by omega⟩ : Fin r) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
          (Pi.single c 1) = Pi.single c 1) ∧
      (∃ χ : TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) →* ℤˣ,
        (orthElementaryGroup (quadPlus r K)).subgroupOf
            (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ≤ χ.ker ∧
          (maxStab r K).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ≤
            χ.ker ∧
          χ (swapIso K ⟨r - 1, by omega⟩) = -1) ∧
      (Odd (Nat.card K) → ∃ χ : TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) →* ℤˣ,
        (∀ g, ((χ g : ℤ) : K) =
          LinearMap.det ((g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
            (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) ∧
        (orthElementaryGroup (quadPlus r K)).subgroupOf
            (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ≤ χ.ker ∧
          (maxStab r K).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ≤
            χ.ker ∧
          χ (swapIso K ⟨r - 1, by omega⟩) = -1) ∧
      (Even (Nat.card K) →
        (orthElementaryGroup (quadPlus r K)).subgroupOf
            (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ≤ (maxSign r K).ker ∧
          (maxStab r K).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ≤
            (maxSign r K).ker ∧
          maxSign r K (swapIso K ⟨r - 1, by omega⟩) = -1) := by
  have hE : ∀ χ : TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) →* ℤˣ,
      orthElementaryGroup (quadPlus r K) ≤
        χ.ker.map (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)).subtype := fun χ =>
    le_map_ker_of_commutator_eq (orthElementaryGroup_le _) (commutator_orthElementaryGroup hr) χ
  have hodd : Odd (Nat.card K) →
      (orthElementaryGroup (quadPlus r K)).subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ≤ (detChar r K).ker ∧
        (maxStab r K).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ≤
          (detChar r K).ker ∧
        detChar r K (swapIso K ⟨r - 1, by omega⟩) = -1 := fun hq =>
    ⟨subgroupOf_le_ker _ (hE _), fun g hg =>
      detChar_eq_one_of_mem_maxStab (Subgroup.mem_subgroupOf.1 hg), detChar_swapIso hq _⟩
  have heven : Even (Nat.card K) →
      (orthElementaryGroup (quadPlus r K)).subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ≤ (maxSign r K).ker ∧
        (maxStab r K).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ≤
          (maxSign r K).ker ∧
        maxSign r K (swapIso K ⟨r - 1, by omega⟩) = -1 := fun hq =>
    ⟨subgroupOf_le_ker _ (hE _), subgroupOf_le_ker _ (maxStab_le_map_ker hq _ (hE _)),
      maxSign_swapIso (by omega) hq _⟩
  refine ⟨swapPair_single_inl _, swapPair_single_inr _, fun c h1 h2 =>
    swapPair_single_of_ne _ h1 h2, ?_, fun hq => ⟨detChar r K, coe_detChar, hodd hq⟩, heven⟩
  rcases Nat.even_or_odd (Nat.card K) with hq | hq
  · exact ⟨maxSign r K, heven hq⟩
  · exact ⟨detChar r K, hodd hq⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
