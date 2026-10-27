module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticTwo

open Matrix Module Submodule Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher

variable {K : Type} [Field K]

section Action

variable {r : ℕ}

theorem spAct_mul_apply (g h : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spAct (g * h) v = spAct g (spAct h v) := by
  simp only [spAct, mulVecLin_apply, Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]

theorem spAct_one_apply (v : Fin r ⊕ Fin r → K) : spAct (1 : StatedSp r K) v = v := by
  simp only [spAct, mulVecLin_apply, Subgroup.coe_one, Units.val_one, one_mulVec]

theorem spAct_inv_apply_apply (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spAct g⁻¹ (spAct g v) = v := by
  rw [← spAct_mul_apply, inv_mul_cancel, spAct_one_apply]

theorem spAct_apply_inv_apply (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spAct g (spAct g⁻¹ v) = v := by
  rw [← spAct_mul_apply, mul_inv_cancel, spAct_one_apply]

theorem eq_of_spAct_single {g g' : StatedSp r K}
    (h : ∀ x, spAct g (Pi.single x 1) = spAct g' (Pi.single x 1)) : g = g' := by
  apply SymplecticTorusWeyl.statedSp_ext
  ext i j
  have := congrFun (h j) i
  simpa [spAct, mulVecLin_apply, mulVec_single_one] using this

theorem eq_of_spAct {g g' : StatedSp r K} (h : ∀ v, spAct g v = spAct g' v) : g = g' :=
  eq_of_spAct_single fun _ => h _

theorem eq_one_of_mem_spScalars {z : StatedSp r K} (hz : z ∈ spScalars r K)
    {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) (hzv : spAct z v = v) : z = 1 := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hmul : ∀ u : Fin r ⊕ Fin r → K, spAct z u = (c : K) • u := fun u => by
    rw [spAct, mulVecLin_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply]
    ext x
    simp [mulVec_diagonal]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hc1 : (c : K) = 1 := by
    have := congrFun ((hmul v).symm.trans hzv) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_right₀ hi).mp this
  exact eq_of_spAct fun u => by rw [hmul, hc1, one_smul, spAct_one_apply]

theorem eq_of_proj_eq_of_pow_eq_one [Finite K] (hr : 1 ≤ r) (ℓ : ℕ) [CharP K ℓ]
    {x y : StatedSp r K} {a b : ℕ} (hx : x ^ ℓ ^ a = 1) (hy : y ^ ℓ ^ b = 1)
    (hxy : proj r K x = proj r K y) : x = y := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K ℓ
  rw [← Nat.card_eq_fintype_card] at hk
  have hZ : Nat.Coprime (Nat.card (spScalars r K)) ℓ := by
    refine Nat.Coprime.coprime_dvd_left (card_scalars_dvd hr) ?_
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    have hpq : ℓ ∣ Nat.card K := hk ▸ dvd_pow_self ℓ k.ne_zero
    have h1 : 1 ≤ Nat.card K := Finite.card_pos
    have := Nat.dvd_sub hpq hdvd
    rw [Nat.sub_sub_self h1] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  set z := x⁻¹ * y with hz
  have hzZ : z ∈ spScalars r K := by
    rw [← ker_proj, MonoidHom.mem_ker, hz, map_mul, map_inv, hxy, inv_mul_cancel]
  have hzc : z ∈ Subgroup.center (StatedSp r K) := spScalars_le_center hzZ
  have hyz : y = x * z := by rw [hz, mul_inv_cancel_left]
  have hzN : z ^ ℓ ^ (a + b) = 1 := by
    have h1 : y ^ ℓ ^ (a + b) = 1 := by rw [pow_add, mul_comm, pow_mul, hy, one_pow]
    have h2 : x ^ ℓ ^ (a + b) = 1 := by rw [pow_add, pow_mul, hx, one_pow]
    rw [hyz, Commute.mul_pow (Subgroup.mem_center_iff.mp hzc x), h2, one_mul] at h1
    exact h1
  have hzcard : z ^ Nat.card (spScalars r K) = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hzZ⟩ : spScalars r K)))
  have hz1 : z = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hzcard, hzN⟩
    rwa [(hZ.pow_right (a + b)).gcd_eq_one, pow_one] at this
  rw [hyz, hz1, mul_one]

end Action

theorem le_sylow_of_le_normalizer {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : IsPGroup p A) (S : Sylow p G)
    (hS : (S : Subgroup G) ≤ normalizer (A : Set G)) : A ≤ S := by
  have h := S.is_maximal' (hA.to_sup_of_normal_left' S.isPGroup' hS) le_sup_right
  rw [← h]
  exact le_sup_left

section Radical

variable {r : ℕ}

@[expose] def unipotentRadical (r : ℕ) (K : Type) [Field K]
    (T : Submodule K (Fin r ⊕ Fin r → K)) : Subgroup (StatedSp r K) where
  carrier := {g | (∀ v, spAct g v - v ∈ T) ∧ ∀ t ∈ T, spAct g t = t}
  one_mem' := ⟨fun v => by rw [spAct_one_apply, sub_self]; exact T.zero_mem,
    fun t _ => spAct_one_apply t⟩
  mul_mem' {g h} hg hh := ⟨fun v => by
      rw [spAct_mul_apply, show spAct g (spAct h v) - v =
        (spAct g (spAct h v) - spAct h v) + (spAct h v - v) by abel]
      exact T.add_mem (hg.1 _) (hh.1 v),
    fun t ht => by rw [spAct_mul_apply, hh.2 t ht, hg.2 t ht]⟩
  inv_mem' {g} hg := ⟨fun v => by
      have h := hg.1 (spAct g⁻¹ v)
      rw [spAct_apply_inv_apply] at h
      rw [show spAct g⁻¹ v - v = -(v - spAct g⁻¹ v) by abel]
      exact T.neg_mem h,
    fun t ht => by
      have := congrArg (spAct g⁻¹) (hg.2 t ht)
      rw [spAct_inv_apply_apply] at this
      exact this.symm⟩

variable {T : Submodule K (Fin r ⊕ Fin r → K)}

theorem unipotentRadical_le_stabilizer : unipotentRadical r K T ≤ stabilizer r K T := by
  intro g hg
  rw [mem_stabilizer]
  refine le_antisymm ?_ fun t ht => ⟨t, ht, hg.2 t ht⟩
  rintro _ ⟨t, ht, rfl⟩
  change spAct g t ∈ T
  rw [hg.2 t ht]
  exact ht

theorem spAct_mem_of_mem_stabilizer {h : StatedSp r K} (hh : h ∈ stabilizer r K T)
    {t : Fin r ⊕ Fin r → K} (ht : t ∈ T) : spAct h t ∈ T := by
  rw [← mem_stabilizer.mp hh]
  exact ⟨t, ht, rfl⟩

theorem conj_mem_unipotentRadical {h g : StatedSp r K} (hh : h ∈ stabilizer r K T)
    (hg : g ∈ unipotentRadical r K T) : h * g * h⁻¹ ∈ unipotentRadical r K T := by
  refine ⟨fun v => ?_, fun t ht => ?_⟩
  · have h1 := spAct_mem_of_mem_stabilizer hh (hg.1 (spAct h⁻¹ v))
    rw [map_sub, spAct_apply_inv_apply] at h1
    rwa [spAct_mul_apply, spAct_mul_apply]
  · rw [spAct_mul_apply, spAct_mul_apply,
      hg.2 _ (spAct_mem_of_mem_stabilizer (inv_mem hh) ht), spAct_apply_inv_apply]

theorem stabilizer_le_normalizer_unipotentRadical :
    stabilizer r K T ≤ normalizer (unipotentRadical r K T : Set (StatedSp r K)) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_unipotentRadical hh, fun hg => ?_⟩
  have := conj_mem_unipotentRadical (inv_mem hh) hg
  rwa [inv_inv, show h⁻¹ * (h * g * h⁻¹) * h = g by group] at this

theorem unipotentRadical_comm {g g' : StatedSp r K} (hg : g ∈ unipotentRadical r K T)
    (hg' : g' ∈ unipotentRadical r K T) : g * g' = g' * g := by
  refine eq_of_spAct fun v => ?_
  have key : ∀ {a b : StatedSp r K}, a ∈ unipotentRadical r K T →
      b ∈ unipotentRadical r K T → spAct a (spAct b v) = spAct a v + (spAct b v - v) := by
    intro a b ha hb
    have : spAct b v = v + (spAct b v - v) := by abel
    conv_lhs => rw [this]
    rw [map_add, ha.2 _ (hb.1 v)]
  rw [spAct_mul_apply, spAct_mul_apply, key hg hg', key hg' hg]
  abel

theorem pow_eq_one_of_mem_unipotentRadical (ℓ : ℕ) [CharP K ℓ] {g : StatedSp r K}
    (hg : g ∈ unipotentRadical r K T) : g ^ ℓ = 1 := by
  have hpow : ∀ (k : ℕ) (v : Fin r ⊕ Fin r → K),
      spAct (g ^ k) v = v + (k : K) • (spAct g v - v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', spAct_mul_apply, ih, map_add, map_smul, hg.2 _ (hg.1 v), Nat.cast_succ,
        add_smul, one_smul]
      abel
  refine eq_of_spAct fun v => ?_
  rw [hpow, CharP.cast_eq_zero, zero_smul, add_zero, spAct_one_apply]

theorem isPGroup_unipotentRadical (ℓ : ℕ) [CharP K ℓ] :
    IsPGroup ℓ (unipotentRadical r K T) := fun g =>
  ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_eq_one_of_mem_unipotentRadical ℓ g.2]
    rfl)⟩

theorem proj_injOn_unipotentRadical (hT : T ≠ ⊥) {g h : StatedSp r K}
    (hg : g ∈ unipotentRadical r K T) (hh : h ∈ unipotentRadical r K T)
    (hgh : proj r K g = proj r K h) : g = h := by
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
  have hz : g⁻¹ * h ∈ spScalars r K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
  have hr : g⁻¹ * h ∈ unipotentRadical r K T := mul_mem (inv_mem hg) hh
  have := eq_one_of_mem_spScalars hz ht0 (hr.2 t ht)
  rwa [inv_mul_eq_one] at this

end Radical

section Plane

theorem mem_flag_two_iff {v : Fin 2 ⊕ Fin 2 → K} : v ∈ flag 2 K 2 ↔ ∀ j, v (Sum.inr j) = 0 := by
  rw [mem_flag_of_le le_rfl, mem_isoFlag]
  exact ⟨fun h => h.1, fun h => ⟨h, fun j hj => absurd j.2 (not_lt.mpr hj)⟩⟩

@[expose] def symmetricTwo (x y z : K) : Matrix (Fin 2) (Fin 2) K := !![x, y; y, z]

omit [Field K] in
theorem transpose_symmetricTwo (x y z : K) : (symmetricTwo x y z)ᵀ = symmetricTwo x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [Field K] in
theorem symmetricTwo_inj {x y z x' y' z' : K}
    (h : symmetricTwo x y z = symmetricTwo x' y' z') : x = x' ∧ y = y' ∧ z = z' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [symmetricTwo] using congrFun₂ h 0 0
  · simpa [symmetricTwo] using congrFun₂ h 0 1
  · simpa [symmetricTwo] using congrFun₂ h 1 1

theorem upperUnipotentSp_mem_unipotentRadical {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    upperUnipotentSp 2 K hC ∈ unipotentRadical 2 K (flag 2 K 2) := by
  refine ⟨fun v => ?_, fun t ht => ?_⟩
  · rw [mem_flag_two_iff]
    intro j
    simp [spAct, coe_upperUnipotentSp, fromBlocks_mulVec]
  · rw [mem_flag_two_iff] at ht
    have htr : (t ∘ Sum.inr : Fin 2 → K) = 0 := funext ht
    ext x
    rcases x with i | j
    · simp [spAct, coe_upperUnipotentSp, fromBlocks_mulVec, htr]
    · simp [spAct, coe_upperUnipotentSp, fromBlocks_mulVec]

theorem upperUnipotentSp_inj {C C' : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (hC' : C'ᵀ = C')
    (h : upperUnipotentSp 2 K hC = upperUnipotentSp 2 K hC') : C = C' := by
  have := congrArg (fun g : StatedSp 2 K => ((g : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  simp only [coe_upperUnipotentSp] at this
  exact (fromBlocks_inj.mp this).2.1

theorem exists_abelian_normal_le_planeStabilizer [Finite K] (ℓ : ℕ) [CharP K ℓ] :
    ∃ A : Subgroup (StatedProj (StatedSp 2 K)), A ≤ projStabilizer 2 K (flag 2 K 2) ∧
      projStabilizer 2 K (flag 2 K 2) ≤ normalizer (A : Set (StatedProj (StatedSp 2 K))) ∧
      IsPGroup ℓ A ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ Nat.card K ^ 3 ≤ Nat.card A := by
  set R := unipotentRadical 2 K (flag 2 K 2)
  have hT : flag 2 K 2 ≠ ⊥ :=
    ne_bot_of_finrank_pos (by rw [finrank_flag (by norm_num)]; norm_num)
  refine ⟨R.map (proj 2 K), Subgroup.map_mono unipotentRadical_le_stabilizer, ?_,
    (isPGroup_unipotentRadical ℓ).map _, ?_, ?_⟩
  · rw [projStabilizer]
    exact (Subgroup.map_mono stabilizer_le_normalizer_unipotentRadical).trans
      (Subgroup.le_normalizer_map _)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, unipotentRadical_comm ha hb]
  · let φ : K × K × K → R.map (proj 2 K) := fun x =>
      ⟨proj 2 K (upperUnipotentSp 2 K (transpose_symmetricTwo x.1 x.2.1 x.2.2)),
        mem_map_of_mem _ (upperUnipotentSp_mem_unipotentRadical _)⟩
    have hφ : Function.Injective φ := by
      rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
      have h1 := proj_injOn_unipotentRadical hT (upperUnipotentSp_mem_unipotentRadical _)
        (upperUnipotentSp_mem_unipotentRadical _) (congrArg Subtype.val h)
      obtain ⟨rfl, rfl, rfl⟩ := symmetricTwo_inj (upperUnipotentSp_inj _ _ h1)
      rfl
    calc Nat.card K ^ 3 = Nat.card (K × K × K) := by rw [Nat.card_prod, Nat.card_prod]; ring
      _ ≤ _ := Nat.card_le_card_of_injective φ hφ

end Plane

section Point

local notation "e₁" => (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → _)
local notation "e₂" => (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → _)
local notation "f₁" => (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → _)
local notation "f₂" => (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → _)

theorem mem_flag_one_iff {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ flag 2 K 1 ↔ v = v (Sum.inl 0) • (e₁ : Fin 2 ⊕ Fin 2 → K) := by
  rw [mem_flag_of_le (by norm_num), mem_isoFlag]
  constructor
  · rintro ⟨h1, h2⟩
    funext x
    rcases x with i | j
    · match i with
      | 0 => simp
      | 1 => simp [h2 1 le_rfl]
    · simp [h1 j]
  · intro h
    rw [h]
    refine ⟨fun j => by simp, fun j hj => ?_⟩
    have hj0 : j ≠ 0 := fun h0 => by rw [h0] at hj; exact absurd hj (by norm_num)
    simp [hj0]

theorem single_inl_zero_mem_flag_one : (e₁ : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 1 := by
  rw [mem_flag_one_iff]
  simp

theorem single_inl_one_mem_flag_two : (e₂ : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 2 :=
  mem_flag_two_iff.mpr fun j => by simp

theorem spAct_f₁_inr_zero {g : StatedSp 2 K} (he : spAct g e₁ = e₁) :
    spAct g f₁ (Sum.inr 0) = 1 := by
  have := pairedSympForm_mulVec g (e₁ : Fin 2 ⊕ Fin 2 → K) f₁
  change pairedSympForm K 2 (spAct g e₁) (spAct g f₁) = _ at this
  rw [he, pairedSympForm_single_inl, pairedSympForm_single_inl] at this
  simpa using this

theorem spAct_eq_add_smul {g : StatedSp 2 K} (he : spAct g e₁ = e₁)
    {x : Fin 2 ⊕ Fin 2 → K} (hx : spAct g x - x ∈ flag 2 K 1) :
    spAct g x = x + (pairedSympForm K 2 x f₁ - pairedSympForm K 2 x (spAct g f₁)) • e₁ := by
  set c := (spAct g x - x) (Sum.inl 0) with hc
  have hgx : spAct g x = x + c • e₁ := by
    have := mem_flag_one_iff.mp hx
    rw [← this]
    abel
  have hb := pairedSympForm_mulVec g x (f₁ : Fin 2 ⊕ Fin 2 → K)
  change pairedSympForm K 2 (spAct g x) (spAct g f₁) = _ at hb
  have h1 : pairedSympForm K 2 (e₁ : Fin 2 ⊕ Fin 2 → K) (spAct g f₁) = 1 := by
    rw [pairedSympForm_single_inl]
    exact spAct_f₁_inr_zero he
  rw [hgx, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, h1, smul_eq_mul,
    mul_one] at hb
  rw [hgx]
  congr 2
  linear_combination hb

theorem eq_of_spAct_f₁_eq {g g' : StatedSp 2 K}
    (hg : spAct g e₁ = e₁ ∧ spAct g e₂ - e₂ ∈ flag 2 K 1 ∧ spAct g f₂ - f₂ ∈ flag 2 K 1)
    (hg' : spAct g' e₁ = e₁ ∧ spAct g' e₂ - e₂ ∈ flag 2 K 1 ∧ spAct g' f₂ - f₂ ∈ flag 2 K 1)
    (h : spAct g f₁ = spAct g' f₁) : g = g' := by
  refine eq_of_spAct_single ?_
  rw [Sum.forall, Fin.forall_fin_two, Fin.forall_fin_two]
  refine ⟨⟨by rw [hg.1, hg'.1], ?_⟩, h, ?_⟩
  · rw [spAct_eq_add_smul hg.1 hg.2.1, spAct_eq_add_smul hg'.1 hg'.2.1, h]
  · rw [spAct_eq_add_smul hg.1 hg.2.2, spAct_eq_add_smul hg'.1 hg'.2.2, h]

theorem swap_mem_signedPermGroup :
    Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr 1) ∈ SymplecticTorusWeyl.signedPermGroup 2 := by
  rw [SymplecticTorusWeyl.mem_signedPermGroup]
  decide

variable (K) in
@[expose] def leviWeyl : StatedSp 2 K :=
  dotW K ⟨Equiv.swap (Sum.inl 1) (Sum.inr 1), swap_mem_signedPermGroup⟩

theorem leviWeyl_e₁ : spAct (leviWeyl K) e₁ = e₁ :=
  (dotW_mulVec_inl (K := K) _ (i := 0) (j := 0) (by decide)).1

theorem leviWeyl_e₂ : spAct (leviWeyl K) e₂ = f₂ :=
  (dotW_mulVec_inr (K := K) _ (i := 1) (j := 1) (by decide)).1

theorem leviWeyl_mem_flag_one {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ flag 2 K 1) :
    spAct (leviWeyl K) v ∈ flag 2 K 1 := by
  rw [mem_flag_one_iff] at hv
  rw [hv, map_smul, leviWeyl_e₁]
  exact Submodule.smul_mem _ _ single_inl_zero_mem_flag_one

theorem leviWeyl_mem_stabilizer : leviWeyl K ∈ stabilizer 2 K (flag 2 K 1) := by
  refine mem_stabilizer_of_mulVec_mem (fun v hv => leviWeyl_mem_flag_one hv) fun v hv => ?_
  rw [mem_flag_one_iff] at hv
  change spAct (leviWeyl K)⁻¹ v ∈ flag 2 K 1
  have he : spAct (leviWeyl K)⁻¹ e₁ = e₁ := by
    conv_lhs => rw [← leviWeyl_e₁]
    exact spAct_inv_apply_apply _ _
  rw [hv, map_smul, he]
  exact Submodule.smul_mem _ _ single_inl_zero_mem_flag_one

theorem not_abelian_normal_le_pointStabilizer [Finite K] (hodd : ringChar K ≠ 2) (ℓ : ℕ)
    [Fact ℓ.Prime] [CharP K ℓ] (A : Subgroup (StatedProj (StatedSp 2 K)))
    (hnorm : projStabilizer 2 K (flag 2 K 1) ≤ normalizer (A : Set (StatedProj (StatedSp 2 K))))
    (hA : IsPGroup ℓ A) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card K ^ 3 ≤ Nat.card A) : False := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K ℓ
  rw [← Nat.card_eq_fintype_card] at hk
  have hU : IsPGroup ℓ (unipotent 2 K) :=
    IsPGroup.of_card (n := k * 2 ^ 2) (by rw [card_unipotent, hk, pow_mul])
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnipotent (K := K) ℓ (by norm_num : 1 ≤ 2)
  have hUL : projUnipotent 2 K ≤ projStabilizer 2 K (flag 2 K 1) :=
    Subgroup.map_mono (unipotent_le_borelSubgroup.trans
      (borelSubgroup_le_stabilizer_flag (by norm_num)))
  have hwL : proj 2 K (leviWeyl K) ∈ projStabilizer 2 K (flag 2 K 1) :=
    mem_map_of_mem _ leviWeyl_mem_stabilizer
  have hA1 : A ≤ projUnipotent 2 K := by
    rw [← hSU]
    exact le_sylow_of_le_normalizer hA SU (hSU ▸ hUL.trans hnorm)
  have hA2 : A ≤ (projUnipotent 2 K).map (MulAut.conj (proj 2 K (leviWeyl K))).toMonoidHom := by
    have hle : (projUnipotent 2 K).map (MulAut.conj (proj 2 K (leviWeyl K))).toMonoidHom ≤
        projStabilizer 2 K (flag 2 K 1) := by
      rintro _ ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hwL (hUL hy)) (inv_mem hwL)
    have := le_sylow_of_le_normalizer hA (proj 2 K (leviWeyl K) • SU) (by
      rw [LinearFlag.coe_sylow_smul, hSU]
      exact hle.trans hnorm)
    rw [LinearFlag.coe_sylow_smul, hSU] at this
    exact this
  set Ã := A.comap (proj 2 K) ⊓ unipotent 2 K with hÃ
  have hcond : ∀ g ∈ Ã, spAct g e₁ = e₁ ∧ spAct g e₂ - e₂ ∈ flag 2 K 1 ∧
      spAct g f₂ - f₂ ∈ flag 2 K 1 := by
    intro g hg
    obtain ⟨hgA, hgU⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨y, ⟨u', hu', rfl⟩, hyg⟩ := hA2 hgA
    have hlift : leviWeyl K * u' * (leviWeyl K)⁻¹ = g := by
      obtain ⟨a, ha⟩ := hU ⟨g, hgU⟩
      obtain ⟨b, hb⟩ := hU ⟨u', hu'⟩
      have hb' : u' ^ ℓ ^ b = 1 := by simpa using congrArg Subtype.val hb
      have ha' : g ^ ℓ ^ a = 1 := by simpa using congrArg Subtype.val ha
      refine eq_of_proj_eq_of_pow_eq_one (by norm_num) ℓ (a := b) (b := a) ?_ ha' ?_
      · rw [conj_pow, hb', mul_one, mul_inv_cancel]
      · rw [map_mul, map_mul, map_inv]
        exact hyg
    refine ⟨?_, ?_, ?_⟩
    · have := unipotent_sub_mulVec_mem_flag hgU (i := 0) single_inl_zero_mem_flag_one
      rw [flag_zero, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    · exact unipotent_sub_mulVec_mem_flag hgU (i := 1) single_inl_one_mem_flag_two
    · have h1 : spAct u' e₂ - e₂ ∈ flag 2 K 1 :=
        unipotent_sub_mulVec_mem_flag hu' (i := 1) single_inl_one_mem_flag_two
      have hgf : spAct g f₂ = spAct (leviWeyl K) (spAct u' e₂) := by
        rw [← hlift, spAct_mul_apply, spAct_mul_apply, ← leviWeyl_e₂, spAct_inv_apply_apply]
      rw [hgf, ← leviWeyl_e₂, ← map_sub]
      exact leviWeyl_mem_flag_one h1
  have hsurj : Function.Surjective fun g : Ã =>
      (⟨proj 2 K g, (Subgroup.mem_inf.mp g.2).1⟩ : A) := by
    rintro ⟨a, ha⟩
    obtain ⟨u, hu, rfl⟩ := hA1 ha
    exact ⟨⟨u, Subgroup.mem_inf.mpr ⟨ha, hu⟩⟩, rfl⟩
  have hÃcard : Nat.card K ^ 3 ≤ Nat.card Ã :=
    hcard.trans (Nat.card_le_card_of_surjective _ hsurj)
  let φ : Ã → K × K × K := fun g =>
    (spAct (g : StatedSp 2 K) f₁ (Sum.inl 0), spAct (g : StatedSp 2 K) f₁ (Sum.inl 1),
      spAct (g : StatedSp 2 K) f₁ (Sum.inr 1))
  have hφ : Function.Injective φ := by
    intro g g' h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨h0, h1, h3⟩ := h
    have hc := hcond g g.2
    have hc' := hcond g' g'.2
    refine Subtype.ext (eq_of_spAct_f₁_eq hc hc' (funext ?_))
    rw [Sum.forall, Fin.forall_fin_two, Fin.forall_fin_two]
    exact ⟨⟨h0, h1⟩, by rw [spAct_f₁_inr_zero hc.1, spAct_f₁_inr_zero hc'.1], h3⟩
  have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_prod]
    calc Nat.card K * (Nat.card K * Nat.card K) = Nat.card K ^ 3 := by ring
      _ ≤ Nat.card Ã := hÃcard)
  obtain ⟨g, hg⟩ := hbij.2 (0, 1, 0)
  obtain ⟨g', hg'⟩ := hbij.2 (0, 0, 1)
  have hc := hcond g g.2
  have hc' := hcond g' g'.2
  simp only [φ, Prod.mk.injEq] at hg hg'
  have hgf : spAct (g : StatedSp 2 K) f₁ = f₁ + e₂ := by
    funext x
    rcases x with i | j
    · match i with
      | 0 => simp [hg.1]
      | 1 => simp [hg.2.1]
    · match j with
      | 0 => simp [spAct_f₁_inr_zero hc.1]
      | 1 => simp [hg.2.2]
  have hg'f : spAct (g' : StatedSp 2 K) f₁ = f₁ + f₂ := by
    funext x
    rcases x with i | j
    · match i with
      | 0 => simp [hg'.1]
      | 1 => simp [hg'.2.1]
    · match j with
      | 0 => simp [spAct_f₁_inr_zero hc'.1]
      | 1 => simp [hg'.2.2]
  have hgf₂ : spAct (g : StatedSp 2 K) f₂ = f₂ + (1 : K) • e₁ := by
    rw [spAct_eq_add_smul hc.1 hc.2.2, hgf]
    congr 2
    simp [pairedSympForm_single_apply, lineSign]
  have hg'e₂ : spAct (g' : StatedSp 2 K) e₂ = e₂ + (-1 : K) • e₁ := by
    rw [spAct_eq_add_smul hc'.1 hc'.2.1, hg'f]
    congr 2
    simp [pairedSympForm_single_apply, lineSign]
  have hcomm' : (g : StatedSp 2 K) * (g' : StatedSp 2 K) = (g' : StatedSp 2 K) * g := by
    have hgU := (Subgroup.mem_inf.mp g.2).2
    have hg'U := (Subgroup.mem_inf.mp g'.2).2
    refine proj_injOn_unipotent (by norm_num) (mul_mem hgU hg'U) (mul_mem hg'U hgU) ?_
    rw [map_mul, map_mul]
    exact hcomm _ (Subgroup.mem_inf.mp g.2).1 _ (Subgroup.mem_inf.mp g'.2).1
  have h1 : spAct ((g : StatedSp 2 K) * (g' : StatedSp 2 K)) f₁ =
      f₁ + e₂ + (f₂ + (1 : K) • e₁) := by
    rw [spAct_mul_apply, hg'f, map_add, hgf, hgf₂]
  have h2 : spAct ((g' : StatedSp 2 K) * (g : StatedSp 2 K)) f₁ =
      f₁ + f₂ + (e₂ + (-1 : K) • e₁) := by
    rw [spAct_mul_apply, hgf, map_add, hg'f, hg'e₂]
  rw [hcomm', h2] at h1
  have h3 := congrFun h1 (Sum.inl 0)
  simp at h3
  exact Ring.two_ne_zero hodd (by linear_combination -h3)

end Point

end CFSG.ComponentClassification.CatalogueBSymplecticTwo
