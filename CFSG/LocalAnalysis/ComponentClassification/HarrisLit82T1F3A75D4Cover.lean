module

public import CFSG.LieType.Steinberg.CentralExt.SpinPlusThree

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement

namespace F3D4

@[expose] def HasSections (S : Type) [Group S] : Prop :=
  ∀ (E : Type) [Group E] (π : E →* S), Function.Surjective π → π.ker ≤ center E →
    ∃ σ : S →* E, ∀ g, π (σ g) = g

@[expose] def pullbackSub {E H G : Type} [Group E] [Group H] [Group G] (π : E →* G)
    (ρ : H →* G) : Subgroup (H × E) where
  carrier := {x | ρ x.1 = π x.2}
  mul_mem' := fun {a b} ha hb => by
    change ρ (a.1 * b.1) = π (a.2 * b.2)
    rw [map_mul, map_mul, ha, hb]
  one_mem' := by
    change ρ 1 = π 1
    rw [map_one, map_one]
  inv_mem' := fun {a} ha => by
    change ρ a.1⁻¹ = π a.2⁻¹
    rw [map_inv, map_inv, ha]

variable {S X P : Type} [Group S] [Group X] [Group P]

theorem exists_lift_through {E : Type} [Group E] (hS : HasSections S) {π : E →* P}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) (ρ : S →* P) :
    ∃ τ : S →* E, ∀ g, π (τ g) = ρ g := by
  let fst : ↥(pullbackSub π ρ) →* S := (MonoidHom.fst S E).comp (pullbackSub π ρ).subtype
  have hfst : Function.Surjective fst := fun g => by
    obtain ⟨e, he⟩ := hπ (ρ g)
    exact ⟨⟨(g, e), he.symm⟩, rfl⟩
  have hker : fst.ker ≤ center ↥(pullbackSub π ρ) := by
    intro x hx
    rw [mem_center_iff]
    intro y
    have h1 : (x : S × E).1 = 1 := hx
    have h2 : π (x : S × E).2 = 1 := by
      have h3 : ρ (x : S × E).1 = π (x : S × E).2 := x.2
      rw [← h3, h1, map_one]
    have h4 : (x : S × E).2 ∈ center E := hcen h2
    apply Subtype.ext
    apply Prod.ext
    · show (y : S × E).1 * (x : S × E).1 = (x : S × E).1 * (y : S × E).1
      rw [h1, mul_one, one_mul]
    · exact mem_center_iff.mp h4 (y : S × E).2
  obtain ⟨σ, hσ⟩ := hS _ fst hfst hker
  refine ⟨(MonoidHom.snd S E).comp ((pullbackSub π ρ).subtype.comp σ), fun g => ?_⟩
  have h1 : ((σ g : ↥(pullbackSub π ρ)) : S × E).1 = g := hσ g
  have h2 : ρ ((σ g : ↥(pullbackSub π ρ)) : S × E).1 =
      π ((σ g : ↥(pullbackSub π ρ)) : S × E).2 := (σ g).2
  rw [h1] at h2
  exact h2.symm

theorem commutatorElement_mul_mem_center {G : Type*} [Group G] (a b : G) {z w : G}
    (hz : z ∈ center G) (hw : w ∈ center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := mem_center_iff.mp hz
  have hw' := mem_center_iff.mp hw
  have e1 : z * (b * w) * z⁻¹ = b * w := by rw [← hz' (b * w), mul_inv_cancel_right]
  have e2 : w * a⁻¹ * w⁻¹ = a⁻¹ := by rw [← hw' a⁻¹, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [e1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [e2]

theorem exists_cover (hS : HasSections S) (hX : Group.IsPerfect X) {πS : S →* P}
    (hπS : Function.Surjective πS) (hkerS : πS.ker ≤ center S) {πX : X →* P}
    (hπX : Function.Surjective πX) (hkerX : πX.ker ≤ center X) :
    ∃ θ : S →* X, Function.Surjective θ ∧ θ.ker ≤ center S ∧ ∀ g, πX (θ g) = πS g := by
  obtain ⟨θ, hθ⟩ := exists_lift_through hS hπX hkerX πS
  refine ⟨θ, ?_, fun g hg => hkerS ?_, hθ⟩
  ·
    have hdec : ∀ x : X, ∃ g : S, ∃ z ∈ center X, x = θ g * z := by
      intro x
      obtain ⟨g, hg⟩ := hπS (πX x)
      refine ⟨g, (θ g)⁻¹ * x, hkerX ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, hg, inv_mul_cancel]
    have hle : commutator X ≤ θ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨g, z, hz, rfl⟩ := hdec a
      obtain ⟨g', w, hw, rfl⟩ := hdec b
      rw [commutatorElement_mul_mem_center _ _ hz hw, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro x
    have hx : x ∈ θ.range := hle (by rw [Group.isPerfect_def.mp hX]; exact mem_top x)
    exact hx
  · rw [MonoidHom.mem_ker, ← hθ, (MonoidHom.mem_ker).mp hg, map_one]

theorem eq_of_lift (hperf : Group.IsPerfect S) {θ : S →* X} (hker : θ.ker ≤ center S)
    {α β : S →* S} (h : ∀ g, θ (α g) = θ (β g)) : α = β := by
  have hd : ∀ g, (β g)⁻¹ * α g ∈ center S := fun g => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel])
  let d : S →* ↥(center S) :=
    { toFun := fun g => ⟨(β g)⁻¹ * α g, hd g⟩
      map_one' := by
        apply Subtype.ext
        show (β 1)⁻¹ * α 1 = 1
        rw [map_one, map_one, inv_one, one_mul]
      map_mul' := fun a b => by
        apply Subtype.ext
        show (β (a * b))⁻¹ * α (a * b) = (β a)⁻¹ * α a * ((β b)⁻¹ * α b)
        have hc := mem_center_iff.mp (hd a)
        rw [map_mul, map_mul, mul_inv_rev]
        calc (β b)⁻¹ * (β a)⁻¹ * (α a * α b) = (β b)⁻¹ * ((β a)⁻¹ * α a) * α b := by group
          _ = (β a)⁻¹ * α a * (β b)⁻¹ * α b := by rw [← hc ((β b)⁻¹)]
          _ = (β a)⁻¹ * α a * ((β b)⁻¹ * α b) := by group }
  have hcomm : commutator S ≤ d.ker := Abelianization.commutator_subset_ker d
  ext g
  have hg : g ∈ d.ker := hcomm (by rw [Group.isPerfect_def.mp hperf]; exact mem_top g)
  have h1 : (β g)⁻¹ * α g = 1 := congrArg Subtype.val hg
  calc α g = β g * ((β g)⁻¹ * α g) := by group
    _ = β g := by rw [h1, mul_one]

structure Cover (S X : Type) [Group S] [Group X] where
  θ : S →* X
  surj : Function.Surjective θ
  ker_le : θ.ker ≤ center S
  sections : HasSections S
  perfect : Group.IsPerfect S

namespace Cover

variable (c : Cover S X)

theorem exists_liftAut (σ : MulAut X) : ∃ α : MulAut S, ∀ g, c.θ (α g) = σ (c.θ g) := by
  obtain ⟨α, hα⟩ := exists_lift_through c.sections c.surj c.ker_le (σ.toMonoidHom.comp c.θ)
  obtain ⟨β, hβ⟩ := exists_lift_through c.sections c.surj c.ker_le (σ.symm.toMonoidHom.comp c.θ)
  have hα' : ∀ g, c.θ (α g) = σ (c.θ g) := hα
  have hβ' : ∀ g, c.θ (β g) = σ.symm (c.θ g) := hβ
  have h1 : α.comp β = MonoidHom.id S := eq_of_lift c.perfect c.ker_le (fun g => by
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hα', hβ', MulEquiv.apply_symm_apply])
  have h2 : β.comp α = MonoidHom.id S := eq_of_lift c.perfect c.ker_le (fun g => by
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hβ', hα', MulEquiv.symm_apply_apply])
  exact ⟨{ toFun := α
           invFun := β
           left_inv := fun g => DFunLike.congr_fun h2 g
           right_inv := fun g => DFunLike.congr_fun h1 g
           map_mul' := α.map_mul }, hα'⟩

@[expose] def lift (σ : MulAut X) : MulAut S := (c.exists_liftAut σ).choose

theorem lift_spec (σ : MulAut X) (g : S) : c.θ (c.lift σ g) = σ (c.θ g) :=
  (c.exists_liftAut σ).choose_spec g

theorem eq_lift {σ : MulAut X} {α : MulAut S} (hα : ∀ g, c.θ (α g) = σ (c.θ g)) :
    α = c.lift σ := by
  have h := eq_of_lift c.perfect c.ker_le (α := α.toMonoidHom) (β := (c.lift σ).toMonoidHom)
    (fun g => by
      show c.θ (α g) = c.θ (c.lift σ g)
      rw [hα, c.lift_spec])
  ext g
  exact DFunLike.congr_fun h g

theorem lift_mul (σ τ : MulAut X) : c.lift (σ * τ) = c.lift σ * c.lift τ :=
  (c.eq_lift (σ := σ * τ) (α := c.lift σ * c.lift τ) fun g => by
    rw [MulAut.mul_apply, MulAut.mul_apply, c.lift_spec, c.lift_spec]).symm

theorem lift_one : c.lift 1 = 1 :=
  (c.eq_lift (σ := 1) (α := 1) fun _ => rfl).symm

theorem lift_pow (σ : MulAut X) (k : ℕ) : c.lift (σ ^ k) = c.lift σ ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, c.lift_one]
  | succ k ih => rw [pow_succ, pow_succ, c.lift_mul, ih]

theorem lift_conj (g : S) : c.lift (MulAut.conj (c.θ g)) = MulAut.conj g :=
  (c.eq_lift (σ := MulAut.conj (c.θ g)) (α := MulAut.conj g) fun s => by
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]).symm

theorem mem_center_map (α : MulAut S) {z : S} (hz : z ∈ center S) : α z ∈ center S := by
  rw [mem_center_iff] at hz ⊢
  intro g
  have h1 := hz (α.symm g)
  have h2 := congrArg α h1
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2

end Cover

variable {K : Type} [Field K] [Finite K]

theorem two_ne_zero_of_card {f : ℕ} (hK : Nat.card K = 3 ^ f) : (2 : K) ≠ 0 := by
  intro h
  have h1 := SpinTorus.two_eq_zero_iff_even_card.mp h
  rw [hK] at h1
  exact (Nat.not_even_iff_odd.mpr (Odd.pow (by decide))) h1

theorem spin_hasSections {f : ℕ} (hK : Nat.card K = 3 ^ f) (hf : 1 ≤ f) :
    HasSections (spinGroup (quadPlus 4 K)) := by
  intro E _ π hπ hcen
  rcases Nat.lt_or_ge f 2 with h | h
  · have hf1 : f = 1 := by omega
    rw [hf1, pow_one] at hK
    exact SpinPlusClosed.spinPlus_three_exists_section_of_central (by norm_num) hK
      (by norm_num) hπ hcen
  · have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) h
    exact SpinPlusClosed.spinPlus_exists_section_of_central (by norm_num) h4 hπ hcen

omit [Finite K] in
theorem spin_center_eq :
    center (spinGroup (quadPlus 4 K)) = SpinPlusClosed.scalarSpin 4 K :=
  (spinToStatedProj_quadPlus (K := K) (by norm_num)).2.2.symm.trans
    (spinToStatedProj_quadPlus (K := K) (by norm_num)).2.1

theorem spin_center_kleinFour {f : ℕ} (hK : Nat.card K = 3 ^ f) :
    IsKleinFour ↥(center (spinGroup (quadPlus 4 K))) := by
  rw [spin_center_eq]
  exact SpinPlusClosed.isKleinFour_scalarSpin (by norm_num) (two_ne_zero_of_card hK) (by decide)

theorem spin_center_card {f : ℕ} (hK : Nat.card K = 3 ^ f) :
    Nat.card ↥(center (spinGroup (quadPlus 4 K))) = 4 :=
  (spin_center_kleinFour hK).card_four

theorem spin_center_mul_self {f : ℕ} (hK : Nat.card K = 3 ^ f) {c : spinGroup (quadPlus 4 K)}
    (hc : c ∈ center (spinGroup (quadPlus 4 K))) : c * c = 1 := by
  have h1 := Monoid.pow_exponent_eq_one (⟨c, hc⟩ : ↥(center (spinGroup (quadPlus 4 K))))
  rw [(spin_center_kleinFour hK).exponent_two, sq] at h1
  exact congrArg Subtype.val h1

theorem exists_spin_cover {f : ℕ} (hK : Nat.card K = 3 ^ f) (hf : 1 ≤ f) {X : Type} [Group X]
    (hX : Group.IsPerfect X)
    (eX : X ⧸ center X ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) :
    Nonempty (Cover (spinGroup (quadPlus 4 K)) X) := by
  obtain ⟨hsurj, -, hker⟩ := spinToStatedProj_quadPlus (K := K) (by norm_num : 3 ≤ 4)
  have hπX : Function.Surjective (eX.toMonoidHom.comp (QuotientGroup.mk' (center X))) :=
    eX.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerX : (eX.toMonoidHom.comp (QuotientGroup.mk' (center X))).ker ≤ center X := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff eX eX.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  obtain ⟨θ, hθ, hθk, -⟩ := exists_cover (spin_hasSections hK hf) hX hsurj hker.le hπX hkerX
  exact ⟨⟨θ, hθ, hθk, spin_hasSections hK hf, isPerfect_spinGroup_quadPlus (by norm_num)⟩⟩

end F3D4

end CFSG.ComponentClassification.HarrisLit.T1
