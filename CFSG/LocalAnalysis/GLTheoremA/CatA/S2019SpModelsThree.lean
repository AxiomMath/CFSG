module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SpModels
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019.SpBlock

open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial

section Family

variable {E M : Type*} [Field E] [AddCommGroup M] [Module E M]

@[expose] def ModelThree (Γ : Subgroup (LinearMap.GeneralLinearGroup E M)) : Prop :=
  ∃ P₀ : Subgroup (LinearMap.GeneralLinearGroup E M), P₀ ≤ ⁅Γ, Γ⁆ ∧ IsPGroup 3 P₀ ∧
    9 ≤ Nat.card P₀ ∧ (∀ u ∈ P₀, (∀ j ∈ ⁅Γ, Γ⁆, u * j = j * u) → u = 1) ∧
    ∀ u ∈ P₀, (∀ w ∈ P₀, u * w = w * u) → u ^ 3 = 1 →
      (((u : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) - 1) ^ 2 = 0

variable {S : Type*} [AddCommGroup S]

@[expose] noncomputable def familyHom (ν : S →+ (M →ₗ[E] M)) (hνν : ∀ a b, ν a * ν b = 0) :
    Multiplicative S →* LinearMap.GeneralLinearGroup E M where
  toFun a := unipotentUnit (ν (Multiplicative.toAdd a)) (hνν _ _)
  map_one' := by
    apply Units.ext
    simp only [unipotentUnit_val, toAdd_one, map_zero, add_zero, Units.val_one]
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, unipotentUnit_val, toAdd_mul, map_add]
    rw [add_mul, one_mul, mul_add, mul_one, hνν, add_zero]
    abel

theorem familyHom_val (ν : S →+ (M →ₗ[E] M)) (hνν : ∀ a b, ν a * ν b = 0)
    (a : Multiplicative S) :
    ((familyHom ν hνν a : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) =
      1 + ν (Multiplicative.toAdd a) := rfl

theorem modelThree_of_family {Γ : Subgroup (LinearMap.GeneralLinearGroup E M)} [Finite S]
    (h3 : ∀ a : S, 3 • a = 0) (h9 : 9 ≤ Nat.card S) (ν : S →+ (M →ₗ[E] M))
    (hν : Function.Injective ν) (hνν : ∀ a b, ν a * ν b = 0)
    (hΓ : ∀ a, familyHom ν hνν (Multiplicative.ofAdd a) ∈ ⁅Γ, Γ⁆)
    (hnc : ∀ a, a ≠ 0 → ∃ j ∈ ⁅Γ, Γ⁆,
      ν a * ((j : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) ≠
        ((j : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) * ν a) :
    ModelThree Γ := by
  have hinj : Function.Injective (familyHom ν hνν) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup E M => (g : M →ₗ[E] M)) ha
    simp only [familyHom_val, Units.val_one] at h1
    have h2 : ν (Multiplicative.toAdd a) = ν 0 := by
      rw [map_zero]
      simpa using h1
    have h3 : Multiplicative.toAdd a = 0 := hν h2
    exact Multiplicative.toAdd.injective (by rw [h3, toAdd_one])
  refine ⟨(familyHom ν hνν).range, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact hΓ (Multiplicative.toAdd a)
  · rintro ⟨_, a, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have ha : a ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      exact h3 _
    rw [pow_one, Subgroup.coe_pow, ← map_pow, ha, map_one]
    rfl
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      ← Nat.card_congr (Multiplicative.toAdd : Multiplicative S ≃ S)] at *
    exact h9
  · rintro _ ⟨a, rfl⟩ hcomm
    by_contra hne
    have ha : Multiplicative.toAdd a ≠ 0 := fun h => hne (by
      rw [show a = 1 from Multiplicative.toAdd.injective (by rw [h, toAdd_one]), map_one])
    obtain ⟨j, hj, hnj⟩ := hnc _ ha
    apply hnj
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup E M => (g : M →ₗ[E] M))
      (hcomm j hj)
    simp only [Units.val_mul, familyHom_val, add_mul, mul_add, one_mul, mul_one] at h1
    exact add_left_cancel h1
  · rintro _ ⟨a, rfl⟩ - -
    rw [familyHom_val, add_sub_cancel_left, sq, hνν]

theorem commutator_eq_unipotentUnit {d : LinearMap.GeneralLinearGroup E M} {N : M →ₗ[E] M}
    (hN : N * N = 0) {c : E} (hc : c - 1 ≠ 0)
    (hd : (d : M →ₗ[E] M) * N = c • (N * (d : M →ₗ[E] M))) (a : E) :
    ⁅d, unipotentUnit (((c - 1)⁻¹ * a) • N) (by rw [smul_mul_smul, hN, smul_zero])⁆ =
      unipotentUnit (a • N) (by rw [smul_mul_smul, hN, smul_zero]) := by
  apply Units.ext
  have hd' : (d : M →ₗ[E] M) * (((c - 1)⁻¹ * a) • N) =
      c • ((((c - 1)⁻¹ * a) • N) * (d : M →ₗ[E] M)) := by
    rw [mul_smul_comm, hd, smul_mul_assoc, smul_comm]
  rw [commutator_val_of_conj (unipotentUnit_val _ _) (by rw [smul_mul_smul, hN, smul_zero]) hd',
    unipotentUnit_val, smul_smul, mul_inv_cancel_left₀ hc]

end Family

section Lin

variable {E M : Type*} [Field E] [AddCommGroup M] [Module E M] {ι : Type*} [DecidableEq ι]
  (b : Module.Basis ι E M) {i j : ι}

private theorem coord_self' (i : ι) : b.coord i (b i) = 1 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

private theorem coord_ne' (hij : i ≠ j) : b.coord j (b i) = 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg hij]

theorem modelThree_lin [CharP E 3] [Finite E] (b : Module.Basis ι E M) (hij : i ≠ j) {l : E}
    (hl : l ≠ 0)
    (hl2 : l ^ 2 ≠ 1) (h9 : 9 ≤ Nat.card E) :
    ModelThree (⊤ : Subgroup (LinearMap.GeneralLinearGroup E M)) := by
  have hc : l ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hl2
  have hc' : l⁻¹ ^ 2 - 1 ≠ 0 := by
    rw [inv_pow]
    intro h
    apply hl2
    have h' : (l ^ 2)⁻¹ = 1 := sub_eq_zero.1 h
    rwa [inv_eq_one] at h'
  have hN := nb_mul_self b hij
  have h3E : (3 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 3
  let ν : E →+ (M →ₗ[E] M) :=
    AddMonoidHom.mk' (fun a => a • nb b i j) (fun a a' => add_smul a a' _)
  have hνν : ∀ a a', ν a * ν a' = 0 := fun a a' => by
    change (a • nb b i j) * (a' • nb b i j) = 0
    rw [smul_mul_smul, hN, smul_zero]
  refine modelThree_of_family (S := E) (fun a => ?_) h9 ν (fun a a' h => ?_) hνν (fun a => ?_)
    (fun a ha => ?_)
  · rw [nsmul_eq_mul, Nat.cast_ofNat, h3E, zero_mul]
  · have h1 := LinearMap.congr_fun h (b j)
    change a • nb b i j (b j) = a' • nb b i j (b j) at h1
    rw [nb_apply, coord_self', one_smul] at h1
    exact smul_left_injective E (b.ne_zero i) h1
  · have key := commutator_eq_unipotentUnit (d := diagUnit b hij hl) hN hc
      (diagMap_mul_nb b hij hl) a
    have e : familyHom ν hνν (Multiplicative.ofAdd a) =
        unipotentUnit (a • nb b i j) (by rw [smul_mul_smul, hN, smul_zero]) := rfl
    rw [e, ← key]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · refine ⟨⁅diagUnit b hij hl, unipotentUnit (nb b j i) (nb_mul_self b (Ne.symm hij))⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
    rw [commutator_val_of_conj (unipotentUnit_val _ _) (nb_mul_self b (Ne.symm hij))
      (diagMap_mul_nb' b hij hl)]
    intro h
    have h1 := LinearMap.congr_fun h (b i)
    have hνa : ν a = a • nb b i j := rfl
    simp only [hνa, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.smul_apply, nb_apply, map_add, map_smul, coord_self', coord_ne' b hij,
      coord_ne' b (Ne.symm hij), smul_zero, zero_smul, add_zero, zero_add, one_smul, smul_smul,
      map_zero] at h1
    exact mul_ne_zero hc' ha ((smul_eq_zero.1 h1).resolve_right (b.ne_zero i))

end Lin

section Herm

variable {E M : Type*} [Field E] [AddCommGroup M] [Module E M] {σ : E →+* E}
  {H : M →ₛₗ[σ] M →ₗ[E] E} {v w : M}

theorem modelThree_herm [CharP E 3] (hH : H.IsSymm) (hv : H v v = 0) (hw : H w w = 0)
    (hvw : H v w = 1) (E₀ : Subfield E) [Finite E₀] (hE₀ : ∀ t ∈ E₀, σ t = t)
    (h9 : 9 ≤ Nat.card E₀) {l : E} (hlE : l ∈ E₀) (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1) {η : E}
    (hη0 : η ≠ 0) (hη : σ η = -η) : ModelThree (sesqUnitaryGroup H) := by
  have hwv := hwv_eq hH hv hw hvw
  have hc : l ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hl2
  have hc' : l⁻¹ ^ 2 - 1 ≠ 0 := by
    rw [inv_pow]
    intro h
    apply hl2
    have h' : (l ^ 2)⁻¹ = 1 := sub_eq_zero.1 h
    rwa [inv_eq_one] at h'
  have hσl : σ l = l := hE₀ l hlE
  have hN := nh_mul_self (H := H) hv
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, map_zero, LinearMap.zero_apply] at hvw
    exact zero_ne_one hvw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hvw
    exact zero_ne_one hvw
  have h3E : (3 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 3
  let ν : E₀ →+ (M →ₗ[E] M) := AddMonoidHom.mk' (fun t => ((t : E) * η) • nh H v)
    (fun t t' => by rw [Subfield.coe_add, add_mul, add_smul])
  have hνν : ∀ a a', ν a * ν a' = 0 := fun a a' => by
    change (((a : E) * η) • nh H v) * (((a' : E) * η) • nh H v) = 0
    rw [smul_mul_smul, hN, smul_zero]
  refine modelThree_of_family (S := E₀) (fun a => ?_) h9 ν (fun a a' h => ?_) hνν (fun a => ?_)
    (fun a ha => ?_)
  · rw [nsmul_eq_mul, Nat.cast_ofNat, show (3 : E₀) = 0 by exact_mod_cast CharP.cast_eq_zero E₀ 3,
      zero_mul]
  · have h1 := LinearMap.congr_fun h w
    change ((a : E) * η) • nh H v w = ((a' : E) * η) • nh H v w at h1
    rw [nh_apply, hvw, one_smul] at h1
    have h2 := smul_left_injective E hv0 h1
    exact Subtype.ext (mul_right_cancel₀ hη0 h2)
  · have hs : σ ((l ^ 2 - 1)⁻¹ * ((a : E) * η)) = -((l ^ 2 - 1)⁻¹ * ((a : E) * η)) := by
      rw [map_mul, map_mul, hη, map_inv₀, map_sub, map_pow, hσl, map_one, hE₀ _ a.2]
      ring
    have hd : ((htorus hH hv hw hvw hl : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) *
        nh H v = (l ^ 2) • (nh H v * (htorus hH hv hw hvw hl : M →ₗ[E] M)) := by
      have := htorus_mul_nh hH hv hw hvw hl 1
      rw [one_smul] at this
      rw [htorus_val]
      exact this
    have key := commutator_eq_unipotentUnit (d := htorus hH hv hw hvw hl) (N := nh H v) hN hc
      hd ((a : E) * η)
    have e : familyHom ν hνν (Multiplicative.ofAdd a) =
        unipotentUnit (((a : E) * η) • nh H v) (by rw [smul_mul_smul, hN, smul_zero]) := rfl
    rw [e, ← key]
    exact Subgroup.commutator_mem_commutator (htorus_mem hH hv hw hvw hl hσl)
      (htv_mem hH hv hw hvw hs v hv)
  · refine ⟨⁅htorus hH hv hw hvw hl, unipotentUnit (η • nh H w)
      (by rw [smul_mul_smul, nh_mul_self hw, smul_zero])⁆,
      Subgroup.commutator_mem_commutator (htorus_mem hH hv hw hvw hl hσl)
        (htv_mem hH hv hw hvw hη w hw), ?_⟩
    rw [commutator_val_of_conj (unipotentUnit_val _ _)
      (by rw [smul_mul_smul, nh_mul_self hw, smul_zero]) (htorus_mul_nh' hH hv hw hvw hl η)]
    intro h
    have h1 := LinearMap.congr_fun h w
    have hνa : ν a = ((a : E) * η) • nh H v := rfl
    simp only [hνa, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.smul_apply, nh_apply,
      map_add, map_smul, hw, hvw, hwv, smul_zero, zero_smul, add_zero, one_smul] at h1
    have h2 : ((l⁻¹ ^ 2 - 1) * (η * ((a : E) * η))) • w = 0 := by
      linear_combination (norm := module) -h1
    have ha' : (a : E) ≠ 0 := fun h0 => ha (Subtype.ext h0)
    exact mul_ne_zero hc' (mul_ne_zero hη0 (mul_ne_zero ha' hη0))
      ((smul_eq_zero.1 h2).resolve_right hw0)

end Herm

section Alt

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {B : LinearMap.BilinForm K M}
  {v w : M}

theorem modelThree_alt_root [CharP K 3] [Finite K] (hB : B.IsAlt) (hvw : B v w = 1) {l : K}
    (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1) (h9 : 9 ≤ Nat.card K) : ModelThree (sesqUnitaryGroup B) := by
  have hwv : B w v = -1 := by rw [← hB.neg, hvw]
  have hc : l ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hl2
  have hc' : l⁻¹ ^ 2 - 1 ≠ 0 := by
    rw [inv_pow]
    intro h
    apply hl2
    have h' : (l ^ 2)⁻¹ = 1 := sub_eq_zero.1 h
    rwa [inv_eq_one] at h'
  have hN := nv_mul_self hB v
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, map_zero, LinearMap.zero_apply] at hvw
    exact zero_ne_one hvw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hvw
    exact zero_ne_one hvw
  have h3K : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  let ν : K →+ (M →ₗ[K] M) :=
    AddMonoidHom.mk' (fun a => a • nv B v) (fun a a' => add_smul a a' _)
  have hνν : ∀ a a', ν a * ν a' = 0 := fun a a' => by
    change (a • nv B v) * (a' • nv B v) = 0
    rw [smul_mul_smul, hN, smul_zero]
  refine modelThree_of_family (S := K) (fun a => ?_) h9 ν (fun a a' h => ?_) hνν (fun a => ?_)
    (fun a ha => ?_)
  · rw [nsmul_eq_mul, Nat.cast_ofNat, h3K, zero_mul]
  · have h1 := LinearMap.congr_fun h w
    change a • nv B v w = a' • nv B v w at h1
    rw [nv_apply, hvw, one_smul] at h1
    exact smul_left_injective K hv0 h1
  · have key := commutator_eq_unipotentUnit (d := torus hB hvw hl) hN hc
      (torus_mul_nv hB hvw hl) a
    have e0 : familyHom ν hνν (Multiplicative.ofAdd a) =
        unipotentUnit (a • nv B v) (by rw [smul_mul_smul, hN, smul_zero]) := rfl
    rw [e0, ← key]
    refine Subgroup.commutator_mem_commutator (torus_mem hB hvw hl) ?_
    have e : unipotentUnit (((l ^ 2 - 1)⁻¹ * a) • nv B v)
        (by rw [smul_mul_smul, hN, smul_zero]) = tv hB ((l ^ 2 - 1)⁻¹ * a) v :=
      Units.ext rfl
    rw [e]
    exact tv_mem hB _ v
  · refine ⟨⁅torus hB hvw hl, tv hB 1 w⁆,
      Subgroup.commutator_mem_commutator (torus_mem hB hvw hl) (tv_mem hB 1 w), ?_⟩
    rw [commutator_val_of_conj (by rw [tv_val, one_smul]) (nv_mul_self hB w)
      (torus_mul_nw hB hvw hl)]
    intro h
    have h1 := LinearMap.congr_fun h w
    have hνa : ν a = a • nv B v := rfl
    simp only [hνa, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.smul_apply, nv_apply,
      map_add, map_smul, hB.self_eq_zero, hvw, hwv, smul_zero, zero_smul, add_zero,
      one_smul, smul_eq_mul] at h1
    have h2 : ((l⁻¹ ^ 2 - 1) * a) • w = 0 := by
      linear_combination (norm := module) h1
    exact mul_ne_zero hc' ha ((smul_eq_zero.1 h2).resolve_right hw0)

theorem modelThree_alt_two [CharP K 3] [Finite K] (hB : B.IsAlt)
    (hperf : ⁅sesqUnitaryGroup B, sesqUnitaryGroup B⁆ = sesqUnitaryGroup B) (hvw : B v w = 1)
    {v' w' : M} (hvv' : B v v' = 0) (hwv' : B w v' = 0) (hv'w' : B v' w' = 1) :
    ModelThree (sesqUnitaryGroup B) := by
  have hwv : B w v = -1 := by rw [← hB.neg, hvw]
  have hv'v : B v' v = 0 := by rw [← hB.neg, hvv', neg_zero]
  have hv'w : B v' w = 0 := by rw [← hB.neg, hwv', neg_zero]
  have hw'v' : B w' v' = -1 := by rw [← hB.neg, hv'w']
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, map_zero, LinearMap.zero_apply] at hvw
    exact zero_ne_one hvw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hvw
    exact zero_ne_one hvw
  have hv'0 : v' ≠ 0 := by
    intro h
    rw [h, map_zero, LinearMap.zero_apply] at hv'w'
    exact zero_ne_one hv'w'
  have hw'0 : w' ≠ 0 := by
    intro h
    rw [h, map_zero] at hv'w'
    exact zero_ne_one hv'w'
  have h3K : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have h12 : nv B v * nv B v' = 0 := by
    refine LinearMap.ext fun z => ?_
    rw [Module.End.mul_apply, nv_apply, nv_apply, map_smul, hvv', smul_zero, zero_smul,
      LinearMap.zero_apply]
  have h21 : nv B v' * nv B v = 0 := by
    refine LinearMap.ext fun z => ?_
    rw [Module.End.mul_apply, nv_apply, nv_apply, map_smul, hv'v, smul_zero, zero_smul,
      LinearMap.zero_apply]
  let ν : K × K →+ (M →ₗ[K] M) :=
    AddMonoidHom.mk' (fun ab => ab.1 • nv B v + ab.2 • nv B v') (fun ab ab' => by
      simp only [Prod.fst_add, Prod.snd_add, add_smul]
      abel)
  have hνν : ∀ a a', ν a * ν a' = 0 := fun a a' => by
    change (a.1 • nv B v + a.2 • nv B v') * (a'.1 • nv B v + a'.2 • nv B v') = 0
    simp only [add_mul, mul_add, smul_mul_smul, nv_mul_self hB, h12, h21, smul_zero, add_zero]
  have hν : ∀ a z, ν a z = a.1 • (B v z • v) + a.2 • (B v' z • v') := fun a z => rfl
  have hfam : ∀ a, familyHom ν hνν (Multiplicative.ofAdd a) = tv hB a.1 v * tv hB a.2 v' := by
    intro a
    apply Units.ext
    rw [familyHom_val, Units.val_mul, tv_val, tv_val]
    change 1 + (a.1 • nv B v + a.2 • nv B v') = _
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul, h12, smul_zero, add_zero]
    abel
  refine modelThree_of_family (S := K × K) (fun a => ?_) ?_ ν (fun a a' h => ?_) hνν
    (fun a => ?_) (fun a ha => ?_)
  · ext <;> simp [nsmul_eq_mul, h3K]
  · rw [Nat.card_prod]
    have : 3 ≤ Nat.card K := by
      haveI := Fintype.ofFinite K
      obtain ⟨n, hp, hn⟩ := FiniteField.card K 3
      rw [Nat.card_eq_fintype_card, hn]
      exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) n.pos)
    nlinarith
  · have h1 := LinearMap.congr_fun h w
    have h2 := LinearMap.congr_fun h w'
    simp only [hν, hvw, hv'w, hv'w', zero_smul, smul_zero, add_zero, one_smul] at h1 h2
    have ha1 : a.1 = a'.1 := smul_left_injective K hv0 h1
    rw [ha1] at h2
    exact Prod.ext ha1 (smul_left_injective K hv'0 (add_left_cancel h2))
  · rw [hfam, hperf]
    exact mul_mem (tv_mem hB _ v) (tv_mem hB _ v')
  · rw [hperf]
    by_cases ha1 : a.1 = 0
    · have ha2 : a.2 ≠ 0 := fun h => ha (Prod.ext ha1 h)
      refine ⟨tv hB 1 w', tv_mem hB 1 w', ?_⟩
      rw [tv_val, one_smul]
      intro h
      have h1 := LinearMap.congr_fun h w'
      simp only [Module.End.mul_apply, hν, LinearMap.add_apply, Module.End.one_apply, nv_apply,
        map_add, map_smul, hB.self_eq_zero, hv'w', hw'v', ha1, zero_smul, smul_zero, zero_add,
        add_zero, one_smul, smul_eq_mul] at h1
      have h2 : (a.2 * -1) • w' = 0 := by
        linear_combination (norm := module) -h1
      exact mul_ne_zero ha2 (neg_ne_zero.2 one_ne_zero) ((smul_eq_zero.1 h2).resolve_right hw'0)
    · refine ⟨tv hB 1 w, tv_mem hB 1 w, ?_⟩
      rw [tv_val, one_smul]
      intro h
      have h1 := LinearMap.congr_fun h w
      simp only [Module.End.mul_apply, hν, LinearMap.add_apply, Module.End.one_apply, nv_apply,
        map_add, map_smul, hB.self_eq_zero, hvw, hwv, hv'w, hwv', zero_smul, smul_zero, zero_add,
        add_zero, one_smul, smul_eq_mul] at h1
      have h2 : (a.1 * -1) • w = 0 := by
        linear_combination (norm := module) -h1
      exact mul_ne_zero ha1 (neg_ne_zero.2 one_ne_zero) ((smul_eq_zero.1 h2).resolve_right hw0)

end Alt

end CFSG.LocalAnalysis.GLTheoremA.S2019.SpBlock
