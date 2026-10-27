module

public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenF4ExceptionalRootLayers

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree RootOps

section Sylow

variable {C : Type*} [Group C] [Finite C]

theorem exists_twisted_conj_mem_sylow (η : MulAut C) (hη : η ^ 2 = 1) (U : Sylow 2 C)
    (hU : ∀ c ∈ (U : Subgroup C), η c ∈ (U : Subgroup C)) {g : C} (hg : g * η g = 1) :
    ∃ c : C, c * g * (η c)⁻¹ ∈ (U : Subgroup C) := by
  have hpow : ∀ n : ℕ, ∀ c ∈ (U : Subgroup C), (η ^ n) c ∈ (U : Subgroup C) := by
    intro n
    induction n with
    | zero => exact fun c hc => hc
    | succ n ih =>
      intro c hc
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (hU c hc)
  have hHU : ∀ h : Subgroup.zpowers η, ∀ c ∈ (U : Subgroup C),
      (h : MulAut C) c ∈ (U : Subgroup C) := by
    rintro ⟨h, hh⟩ c hc
    obtain ⟨n, rfl⟩ := (isOfFinOrder_of_finite η).mem_powers_iff_mem_zpowers.2 hh
    exact hpow n c hc
  have hfin : Finite (C ⋊[(Subgroup.zpowers η).subtype] Subgroup.zpowers η) :=
    Finite.of_equiv _ SemidirectProduct.equivProd.symm
  let P₀ : Subgroup (C ⋊[(Subgroup.zpowers η).subtype] Subgroup.zpowers η) :=
    { carrier := {y | y.left ∈ (U : Subgroup C)}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, SemidirectProduct.mul_left] at ha hb ⊢
        exact mul_mem ha (hHU _ _ hb)
      one_mem' := one_mem (U : Subgroup C)
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, SemidirectProduct.inv_left] at ha ⊢
        exact hHU a.right⁻¹ _ (inv_mem ha) }
  have hmemP₀ : ∀ y, y ∈ P₀ ↔ y.left ∈ (U : Subgroup C) := fun y => Iff.rfl
  have eP : P₀ ≃ ↥(U : Subgroup C) × ↥(Subgroup.zpowers η) :=
    { toFun := fun y => (⟨y.1.left, y.2⟩, y.1.right)
      invFun := fun p => ⟨⟨(p.1 : C), p.2⟩, p.1.2⟩
      left_inv := fun y => rfl
      right_inv := fun p => rfl }
  have hcardP : Nat.card P₀ = Nat.card (U : Subgroup C) * Nat.card (Subgroup.zpowers η) := by
    rw [Nat.card_congr eP, Nat.card_prod]
  have hcardS := SemidirectProduct.card (φ := (Subgroup.zpowers η).subtype)
  have hU0 := (U : Subgroup C).card_mul_index
  have hP0 := P₀.card_mul_index
  have hpos : 0 < Nat.card (U : Subgroup C) * Nat.card (Subgroup.zpowers η) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have hidx : P₀.index = (U : Subgroup C).index := by
    rw [hcardP, hcardS, ← hU0] at hP0
    have : Nat.card (U : Subgroup C) * Nat.card (Subgroup.zpowers η) * P₀.index =
        Nat.card (U : Subgroup C) * Nat.card (Subgroup.zpowers η) * (U : Subgroup C).index := by
      rw [hP0]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hη2 : orderOf η ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hη
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hη2
  obtain ⟨n, hn⟩ := U.isPGroup'.exists_card_eq
  have hPp : IsPGroup 2 P₀ := IsPGroup.of_card (n := n + k) (by
    rw [hcardP, hn, Nat.card_zpowers, hk, pow_add])
  have hPi : ¬ 2 ∣ P₀.index := hidx ▸ U.not_dvd_index
  set x : C ⋊[(Subgroup.zpowers η).subtype] Subgroup.zpowers η :=
    ⟨g, ⟨η, Subgroup.mem_zpowers η⟩⟩ with hxdef
  have hx : x ^ 2 = 1 := by
    rw [pow_two]
    refine SemidirectProduct.ext ?_ ?_
    · exact hg
    · exact Subtype.ext (by simpa [pow_two] using hη)
  have hxo : orderOf x ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hx
  obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hxo
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := l) (by rw [Nat.card_zpowers, hl])
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq
    (C ⋊[(Subgroup.zpowers η).subtype] Subgroup.zpowers η) (hPp.toSylow hPi) Q
  have hxQ : x ∈ (Q : Subgroup _) := hQ (Subgroup.mem_zpowers x)
  rw [← ha, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    IsPGroup.toSylow_coe, MulAut.smul_def, MulAut.conj_inv_apply] at hxQ
  set b := a⁻¹ with hb
  set r := b.right
  refine ⟨((r⁻¹ : Subgroup.zpowers η) : MulAut C) b.left, ?_⟩
  have hc : SemidirectProduct.inl (((r⁻¹ : Subgroup.zpowers η) : MulAut C) b.left) =
      (SemidirectProduct.inr r⁻¹ * b : C ⋊[(Subgroup.zpowers η).subtype] Subgroup.zpowers η) := by
    conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right b]
    rw [show ((r⁻¹ : Subgroup.zpowers η) : MulAut C) = (Subgroup.zpowers η).subtype r⁻¹ from rfl,
      SemidirectProduct.inl_aut, inv_inv, mul_assoc]
  have hr : ∀ s : Subgroup.zpowers η, SemidirectProduct.inr s ∈ P₀ := fun s =>
    (hmemP₀ _).2 (one_mem (U : Subgroup C))
  have hy : SemidirectProduct.inl (((r⁻¹ : Subgroup.zpowers η) : MulAut C) b.left) * x *
      (SemidirectProduct.inl (((r⁻¹ : Subgroup.zpowers η) : MulAut C) b.left))⁻¹ ∈ P₀ := by
    rw [hc, mul_inv_rev, inv_inv]
    have := mul_mem (mul_mem (hr r⁻¹) hxQ) (hr r)
    convert this using 1
    simp only [hb, map_inv, inv_inv]
    group
  rw [hmemP₀] at hy
  simpa [SemidirectProduct.mul_left, SemidirectProduct.inv_left, hxdef] using hy

omit [Finite C] in
theorem conj_mul_sq_of_sq_eq_one (η : MulAut C) (hη : η ^ 2 = 1) (g : C) :
    (MulAut.conj g * η) ^ 2 = MulAut.conj (g * η g) := by
  have hηη : ∀ x, η (η x) = x := fun x => by
    rw [← MulAut.mul_apply, ← pow_two, hη, MulAut.one_apply]
  refine MulEquiv.ext fun x => ?_
  simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hηη]

omit [Finite C] in
theorem conj_mul_conj_twisted (η : MulAut C) (k : C) :
    MulAut.conj k * (MulAut.conj (k⁻¹ * η k) * η) * (MulAut.conj k)⁻¹ = η := by
  refine MulEquiv.ext fun x => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv]
  group

omit [Finite C] in
theorem eq_one_of_conj_eq_one (hC : Subgroup.center C = ⊥) {z : C} (h : MulAut.conj z = 1) :
    z = 1 := by
  have hz : z ∈ Subgroup.center C := Subgroup.mem_center_iff.2 fun y => by
    have := congrArg (fun α : MulAut C => α y) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rwa [hC, Subgroup.mem_bot] at hz

end Sylow

section Layers

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem finiteReeAut_mem_f4LayerGroup
    (m j : ℕ) {x : adjointGroup ReeTag.F4.tag K}
    (hx : (x : ModGL ReeTag.F4.tag K) ∈ f4LayerGroup K j) :
    ((ReeTag.F4.finiteReeAut K m x : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) ∈
      f4LayerGroup K j := by
  have h := ReeTag.map_finiteReeAut_rootSpan_le (t := ReeTag.F4) (K := K) (a := m)
    (S := f4LayerRoots j) fun _ hα => dualRoot_mem_f4LayerRoots hα
  exact Subgroup.mem_subgroupOf.1 (h (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)))

theorem finiteReeAut_f4LayerElt
    (m : ℕ) (i : Fin 12) (a b : K) :
    (ReeTag.F4.finiteReeAut K m ⟨f4LayerElt K i a b, f4LayerElt_mem_adjointGroup i a b⟩ :
        ModGL ReeTag.F4.tag K) =
      pinnedX ReeTag.F4.tag K (orbitCertRoot ReeTag.F4.tag (f4PairShort i)) (a ^ 2 ^ m) *
        pinnedX ReeTag.F4.tag K (orbitCertRoot ReeTag.F4.tag (f4PairLong i)) (b ^ (2 * 2 ^ m)) := by
  obtain ⟨hl, hs, hls, hsl⟩ := f4Pair_roots i
  have e : (⟨f4LayerElt K i a b, f4LayerElt_mem_adjointGroup i a b⟩ :
      adjointGroup ReeTag.F4.tag K) =
      ⟨_, pinnedX_mem_adjointGroup (orbitCertRoot ReeTag.F4.tag (f4PairLong i)) a⟩ *
        ⟨_, pinnedX_mem_adjointGroup (orbitCertRoot ReeTag.F4.tag (f4PairShort i)) b⟩ :=
    Subtype.ext rfl
  rw [e, map_mul, ReeTag.finiteReeAut_pinnedX_F4 hl.1, ReeTag.finiteReeAut_pinnedX_F4 hs.1,
    (ReeTag.relationExponent_pinnedData_F4 (a := m) hl.1).1 hl,
    (ReeTag.relationExponent_pinnedData_F4 (a := m) hs.1).2 hs]
  simp only [Subgroup.coe_mul, hls, hsl]

theorem finiteReeAut_f4LayerElt_mem
    (m : ℕ) (i : Fin 12) (a b : K) :
    ((f4LayerElt K i (b ^ (2 * 2 ^ m)) (a ^ 2 ^ m) : ModGL ReeTag.F4.tag K))⁻¹ *
        (ReeTag.F4.finiteReeAut K m ⟨f4LayerElt K i a b, f4LayerElt_mem_adjointGroup i a b⟩ :
          ModGL ReeTag.F4.tag K) ∈ f4LayerGroup K (i.val + 2) := by
  rw [finiteReeAut_f4LayerElt]
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hs := f4LayerRoots_subset_pos _ (f4PairShort_mem i)
  have hc := f4_commutator_mem_succ (K := K) hs (f4PairLong_mem i) (-(a ^ 2 ^ m))
    (-(b ^ (2 * 2 ^ m)))
  convert hc using 1
  simp only [f4LayerElt, ← pinnedX_neg, commutatorElement_def, mul_inv_rev, inv_inv]
  group

theorem exists_f4Layer_descent_step
    (m : ℕ) (i : Fin 12) {u : adjointGroup ReeTag.F4.tag K}
    (hu : (u : ModGL ReeTag.F4.tag K) ∈ f4LayerGroup K (i.val + 1))
    (h1 : u * ReeTag.F4.finiteReeAut K m u = 1) :
    ∃ v : adjointGroup ReeTag.F4.tag K,
      (v : ModGL ReeTag.F4.tag K) ∈ posUnipotent ReeTag.F4.tag K ∧
      ((v * u * (ReeTag.F4.finiteReeAut K m v)⁻¹ : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K) ∈ f4LayerGroup K (i.val + 2) := by
  obtain ⟨e, he⟩ := exists_f4Layer_mulEquiv (K := K) i
  let π : f4LayerGroup K (i.val + 1) →* Multiplicative (K × K) :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπL : ∀ a b, π (f4LayerElt K i a b) = Multiplicative.ofAdd (a, b) := fun a b => by
    change e.symm (QuotientGroup.mk _) = _
    rw [← he, MulEquiv.symm_apply_apply]
  have hπ1 : ∀ x, π x = 1 ↔ (x : ModGL ReeTag.F4.tag K) ∈ f4LayerGroup K (i.val + 2) :=
    fun x => by
      change e.symm (QuotientGroup.mk x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf
  have hπeq : ∀ x y, π x = π y ↔
      ((x : ModGL ReeTag.F4.tag K))⁻¹ * y ∈ f4LayerGroup K (i.val + 2) := fun x y => by
    rw [← inv_mul_eq_one, ← map_inv, ← map_mul, hπ1]
    rfl
  have hπF : ∀ (x : adjointGroup ReeTag.F4.tag K)
      (hx : (x : ModGL ReeTag.F4.tag K) ∈ f4LayerGroup K (i.val + 1)) (a b : K),
      π ⟨x, hx⟩ = Multiplicative.ofAdd (a, b) →
      π ⟨_, finiteReeAut_mem_f4LayerGroup m _ hx⟩ =
        Multiplicative.ofAdd (b ^ (2 * 2 ^ m), a ^ 2 ^ m) := by
    intro x hx a b hab
    rw [← hπL] at hab ⊢
    have hw := (hπeq _ _).1 hab.symm
    set L : adjointGroup ReeTag.F4.tag K :=
      ⟨f4LayerElt K i a b, f4LayerElt_mem_adjointGroup i a b⟩ with hL
    have hw' : ((L⁻¹ * x : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) ∈
        f4LayerGroup K (i.val + 2) := hw
    have hsplit : ((ReeTag.F4.finiteReeAut K m x : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K) =
        ((ReeTag.F4.finiteReeAut K m L : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) *
          ((ReeTag.F4.finiteReeAut K m (L⁻¹ * x) : adjointGroup ReeTag.F4.tag K) :
            ModGL ReeTag.F4.tag K) := by
      rw [← Subgroup.coe_mul, ← map_mul, mul_inv_cancel_left]
    refine ((hπeq _ _).2 ?_).symm
    change ((f4LayerElt K i _ _ : ModGL ReeTag.F4.tag K))⁻¹ *
      ((ReeTag.F4.finiteReeAut K m x : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) ∈ _
    rw [hsplit, ← mul_assoc]
    exact mul_mem (finiteReeAut_f4LayerElt_mem m i a b) (finiteReeAut_mem_f4LayerGroup m _ hw')
  obtain ⟨⟨a, b⟩, hab⟩ : ∃ p : K × K, π ⟨u, hu⟩ = Multiplicative.ofAdd p :=
    ⟨(π ⟨u, hu⟩).toAdd, rfl⟩
  have hprod : π ⟨u, hu⟩ * π ⟨_, finiteReeAut_mem_f4LayerGroup m _ hu⟩ = 1 := by
    rw [← map_mul]
    refine (hπ1 _).2 ?_
    change ((u * ReeTag.F4.finiteReeAut K m u : adjointGroup ReeTag.F4.tag K) :
      ModGL ReeTag.F4.tag K) ∈ _
    rw [h1]
    exact one_mem _
  rw [hab, hπF u hu a b hab, ← ofAdd_add, ofAdd_eq_one, Prod.mk_add_mk, Prod.mk_eq_zero] at hprod
  have hv : ((⟨f4LayerElt K i 0 b, f4LayerElt_mem_adjointGroup i 0 b⟩ :
      adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) ∈ f4LayerGroup K (i.val + 1) :=
    (f4LayerElt K i 0 b).2
  refine ⟨⟨f4LayerElt K i 0 b, f4LayerElt_mem_adjointGroup i 0 b⟩,
    f4LayerGroup_le_posUnipotent K _ hv, ?_⟩
  have hFv := hπF _ hv 0 b (hπL 0 b)
  have hmem : ((⟨f4LayerElt K i 0 b, f4LayerElt_mem_adjointGroup i 0 b⟩ :
      adjointGroup ReeTag.F4.tag K) * u *
        (ReeTag.F4.finiteReeAut K m ⟨f4LayerElt K i 0 b, f4LayerElt_mem_adjointGroup i 0 b⟩)⁻¹ :
      ModGL ReeTag.F4.tag K) ∈ f4LayerGroup K (i.val + 1) :=
    mul_mem (mul_mem hv hu) (inv_mem (finiteReeAut_mem_f4LayerGroup m _ hv))
  refine (hπ1 ⟨_, hmem⟩).1 ?_
  have hsplit : (⟨_, hmem⟩ : f4LayerGroup K (i.val + 1)) =
      f4LayerElt K i 0 b * ⟨u, hu⟩ * (⟨_, finiteReeAut_mem_f4LayerGroup m _ hv⟩)⁻¹ :=
    Subtype.ext rfl
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [hsplit, map_mul, map_mul, map_inv, hπL, hab, hFv, ← ofAdd_add, ← ofAdd_neg, ← ofAdd_add,
    ofAdd_eq_one, Prod.mk_add_mk, Prod.neg_mk, Prod.mk_add_mk, Prod.mk_eq_zero,
    zero_pow (pow_ne_zero m two_ne_zero), neg_zero, add_zero, CharTwo.add_self_eq_zero, zero_add,
    ← sub_eq_add_neg, CharTwo.sub_eq_add]
  exact ⟨hprod.1, rfl⟩

theorem exists_f4_layer_descent
    (m : ℕ) (hF : ReeTag.F4.finiteReeAut K m ^ 2 = 1) :
    ∀ n ≤ 12, ∀ u : adjointGroup ReeTag.F4.tag K,
      (u : ModGL ReeTag.F4.tag K) ∈ f4LayerGroup K (13 - n) →
      u * ReeTag.F4.finiteReeAut K m u = 1 →
      ∃ h : adjointGroup ReeTag.F4.tag K,
        (h : ModGL ReeTag.F4.tag K) ∈ posUnipotent ReeTag.F4.tag K ∧
          h * u * (ReeTag.F4.finiteReeAut K m h)⁻¹ = 1 := by
  have hFF : ∀ x, ReeTag.F4.finiteReeAut K m (ReeTag.F4.finiteReeAut K m x) = x := fun x => by
    rw [← MulAut.mul_apply, ← pow_two, hF, MulAut.one_apply]
  intro n hn
  induction n with
  | zero =>
    intro u hu _
    rw [Nat.sub_zero, f4LayerGroup_thirteen, Subgroup.mem_bot] at hu
    obtain rfl : u = 1 := Subtype.ext hu
    exact ⟨1, one_mem _, by rw [map_one, inv_one, mul_one, mul_one]⟩
  | succ n ih =>
    intro u hu h1
    have hi : 13 - (n + 1) = (⟨11 - n, by omega⟩ : Fin 12).val + 1 := by
      simp only
      omega
    rw [hi] at hu
    obtain ⟨v, hvU, hv⟩ := exists_f4Layer_descent_step m ⟨11 - n, by omega⟩ hu h1
    have hi' : (⟨11 - n, by omega⟩ : Fin 12).val + 2 = 13 - n := by
      simp only
      omega
    rw [hi'] at hv
    have h1' : v * u * (ReeTag.F4.finiteReeAut K m v)⁻¹ *
        ReeTag.F4.finiteReeAut K m (v * u * (ReeTag.F4.finiteReeAut K m v)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hFF,
        show v * u * (ReeTag.F4.finiteReeAut K m v)⁻¹ *
          (ReeTag.F4.finiteReeAut K m v * ReeTag.F4.finiteReeAut K m u * v⁻¹) =
            v * (u * ReeTag.F4.finiteReeAut K m u) * v⁻¹ by group, h1, mul_one, mul_inv_cancel]
    obtain ⟨h, hhU, hh⟩ := ih (by omega) _ hv h1'
    refine ⟨h * v, mul_mem hhU hvU, ?_⟩
    rw [map_mul, mul_inv_rev, ← hh]
    group

theorem exists_twisted_conj_eq_one_F4
    (m : ℕ) (hF : ReeTag.F4.finiteReeAut K m ^ 2 = 1)
    {g : adjointGroup ReeTag.F4.tag K} (hg : g * ReeTag.F4.finiteReeAut K m g = 1) :
    ∃ k : adjointGroup ReeTag.F4.tag K, k * g * (ReeTag.F4.finiteReeAut K m k)⁻¹ = 1 := by
  have := finite_modGL (τ := ReeTag.F4.tag) (K := K)
  have hFF : ∀ x, ReeTag.F4.finiteReeAut K m (ReeTag.F4.finiteReeAut K m x) = x := fun x => by
    rw [← MulAut.mul_apply, ← pow_two, hF, MulAut.one_apply]
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem ReeTag.F4.tag).length
  obtain ⟨⟨P, hP⟩, -⟩ :=
    exceptional_ordinary_Sylow_opposition ReeTag.F4.tag K ReeTag.F4.prime w₀ hw₀
  have hPU : ∀ x ∈ (P : Subgroup (adjointGroup ReeTag.F4.tag K)),
      ReeTag.F4.finiteReeAut K m x ∈ (P : Subgroup (adjointGroup ReeTag.F4.tag K)) := by
    intro x hx
    rw [hP] at hx ⊢
    rw [← ReeTag.map_finiteReeAut_posUnipotentSub (a := m)]
    exact Subgroup.mem_map_of_mem _ hx
  obtain ⟨c, hc⟩ := exists_twisted_conj_mem_sylow _ hF P hPU hg
  rw [hP, Subgroup.mem_subgroupOf] at hc
  have hu1 : c * g * (ReeTag.F4.finiteReeAut K m c)⁻¹ *
      ReeTag.F4.finiteReeAut K m (c * g * (ReeTag.F4.finiteReeAut K m c)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hFF,
      show c * g * (ReeTag.F4.finiteReeAut K m c)⁻¹ *
        (ReeTag.F4.finiteReeAut K m c * ReeTag.F4.finiteReeAut K m g * c⁻¹) =
          c * (g * ReeTag.F4.finiteReeAut K m g) * c⁻¹ by group, hg, mul_one, mul_inv_cancel]
  obtain ⟨h, -, hh⟩ := exists_f4_layer_descent m hF 12 le_rfl _
    (by rw [show 13 - 12 = 1 from rfl, f4LayerGroup_one]; exact hc) hu1
  refine ⟨h * c, ?_⟩
  rw [map_mul, mul_inv_rev, ← hh]
  group

end Layers


theorem even_F4_exceptional_involution_Sylow_descent
    {m f : ℕ} (hf : f = 2 * m + 1) (K : Type)
    [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f) :
    (ReeTag.F4.finiteExceptionalAut K ^ f) ^ 2 = 1 ∧
    ReeTag.F4.finiteExceptionalAut K ^ f ∉
      (MulAut.conj : adjointGroup ReeTag.F4.tag K →* MulAut (adjointGroup ReeTag.F4.tag K)).range ∧
    (∀ x : adjointGroup ReeTag.F4.tag K ⋊[(Subgroup.zpowers
        (ReeTag.F4.finiteExceptionalAut K ^ f)).subtype]
          Subgroup.zpowers (ReeTag.F4.finiteExceptionalAut K ^ f),
      x.right = ⟨ReeTag.F4.finiteExceptionalAut K ^ f, Subgroup.mem_zpowers _⟩ → x ^ 2 = 1 →
      ∃ c : adjointGroup ReeTag.F4.tag K,
        SemidirectProduct.inl c * x * (SemidirectProduct.inl c)⁻¹ =
          SemidirectProduct.inr ⟨ReeTag.F4.finiteExceptionalAut K ^ f, Subgroup.mem_zpowers _⟩) ∧
    ∀ g : adjointGroup ReeTag.F4.tag K,
      (MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ f) ^ 2 = 1 →
      ∃ h : adjointGroup ReeTag.F4.tag K,
        MulAut.conj h * (MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ f) *
          (MulAut.conj h)⁻¹ = ReeTag.F4.finiteExceptionalAut K ^ f := by
  have hf1 : 1 ≤ f := by omega
  obtain ⟨-, -, -, -, ⟨hsq, -⟩, -, hodd⟩ := even_F4_exact_automorphism_normal_form hf1 K hK
  obtain ⟨-, hη, -⟩ := hodd m hf
  have hcore : ∀ g : adjointGroup ReeTag.F4.tag K,
      g * (ReeTag.F4.finiteExceptionalAut K ^ f) g = 1 →
      ∃ k : adjointGroup ReeTag.F4.tag K,
        k * g * ((ReeTag.F4.finiteExceptionalAut K ^ f) k)⁻¹ = 1 := by
    rw [hη]
    exact fun g hg => exists_twisted_conj_eq_one_F4 m (hη ▸ hsq) hg
  refine ⟨hsq, ?_, ?_, ?_⟩
  · rintro ⟨h, hh⟩
    have hdvd := ree_two_mul_dvd_of_pow_eq_conj ReeTag.F4 hf1 hK (i₀ := ⟨0, by decide⟩)
      (by decide) hh.symm
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro x hx hx2
    have hg : x.left * (ReeTag.F4.finiteExceptionalAut K ^ f) x.left = 1 := by
      have := congrArg SemidirectProduct.left hx2
      rwa [pow_two, SemidirectProduct.mul_left, hx] at this
    obtain ⟨k, hk⟩ := hcore _ hg
    refine ⟨k, SemidirectProduct.ext ?_ ?_⟩
    · simpa [SemidirectProduct.mul_left, SemidirectProduct.inv_left, hx] using hk
    · simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hx]
  · intro g hg2
    rw [conj_mul_sq_of_sq_eq_one _ hsq] at hg2
    obtain ⟨k, hk⟩ := hcore g (eq_one_of_conj_eq_one center_adjointGroup_eq_bot hg2)
    obtain rfl : g = k⁻¹ * (ReeTag.F4.finiteExceptionalAut K ^ f) k :=
      eq_inv_mul_of_mul_eq (mul_inv_eq_one.1 hk)
    exact ⟨k, conj_mul_conj_twisted _ k⟩

end CFSG.LieType.Chevalley
