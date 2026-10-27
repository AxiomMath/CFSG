module

public import CFSG.CGT.PushingUpLit.BHS.AltCore
public import CFSG.CGT.PushingUpLit.BHS.SL2Normalizer

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Campbell CFSG.SL2MinimalFaithful
open scoped commutatorElement LinearAlgebra.Projectivization

section SLCore

variable {W : Type} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F] [CharP F 2]
  {E A : Subgroup (MulAut W)}

structure SLNatData (E : Subgroup (MulAut W)) (F : Type) [Field F] where
  θ : E ≃* Matrix.SpecialLinearGroup (Fin 2) F
  β : W →* Multiplicative (Fin 2 → F)
  surj : Function.Surjective β
  ker_fix : ∀ w : W, β w = 1 → w ∈ fixV E
  equivar : ∀ (e : E) (w : W), β ((e : MulAut W) w) =
    Multiplicative.ofAdd ((θ e : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β w)))
  comm_top : commV E = ⊤

variable (D : SLNatData E F)

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.equivar' (e : E) (w : W) :
    Multiplicative.toAdd (D.β ((e : MulAut W) w)) = D.θ e • Multiplicative.toAdd (D.β w) := by
  rw [D.equivar]
  rfl

@[expose] def lowerUni (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

omit [Finite F] [CharP F 2] in
theorem lowerUni_smul (t : F) (v : Fin 2 → F) : lowerUni t • v = ![v 0, t * v 0 + v 1] := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  ext i
  fin_cases i <;> simp [lowerUni, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [Finite F] [CharP F 2] in
theorem eq_zero_of_forall_smul_eq {v : Fin 2 → F}
    (h : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, g • v = v) : v = 0 := by
  have h1 := congrFun (h (unipotent 1)) 0
  have h2 := congrFun (h (lowerUni 1)) 1
  rw [smul_unipotent_vec] at h1
  rw [lowerUni_smul] at h2
  simp at h1 h2
  ext i
  fin_cases i
  · simpa using h2
  · simpa using h1

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.ker_iff (w : W) : D.β w = 1 ↔ w ∈ fixV E := by
  refine ⟨D.ker_fix w, fun hw => ?_⟩
  have : Multiplicative.toAdd (D.β w) = 0 := by
    apply eq_zero_of_forall_smul_eq
    intro g
    obtain ⟨e, he⟩ := D.θ.surjective g
    rw [← he, ← D.equivar' e w, hw e e.2]
  exact Multiplicative.toAdd.injective (by simpa using this)

@[expose] def permOfMulEquiv (y : Multiplicative (Fin 2 → F) ≃* Multiplicative (Fin 2 → F)) :
    Equiv.Perm (Fin 2 → F) where
  toFun v := Multiplicative.toAdd (y (Multiplicative.ofAdd v))
  invFun v := Multiplicative.toAdd (y.symm (Multiplicative.ofAdd v))
  left_inv v := by simp
  right_inv v := by simp

omit [Finite F] [CharP F 2] in
theorem permOfMulEquiv_apply (y : Multiplicative (Fin 2 → F) ≃* Multiplicative (Fin 2 → F))
    (v : Fin 2 → F) :
    permOfMulEquiv y v = Multiplicative.toAdd (y (Multiplicative.ofAdd v)) := rfl

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.exists_perm {x : MulAut W}
    (hx : x ∈ Subgroup.normalizer (E : Set (MulAut W))) :
    ∃ π : Equiv.Perm (Fin 2 → F), ∀ w, Multiplicative.toAdd (D.β (x w)) =
      π (Multiplicative.toAdd (D.β w)) := by
  have hf : ∀ w, D.β (x w) = 1 ↔ D.β w = 1 := fun w => by
    rw [D.ker_iff, D.ker_iff]
    exact mem_fixV_normalizer_iff hx w
  obtain ⟨y, hy⟩ := exists_descent_mulEquiv D.β D.surj x hf
  exact ⟨permOfMulEquiv y, fun w => by rw [permOfMulEquiv_apply, ← hy w]; simp⟩

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.perm_unique {π π' : Equiv.Perm (Fin 2 → F)}
    (h : ∀ w, π (Multiplicative.toAdd (D.β w)) = π' (Multiplicative.toAdd (D.β w))) : π = π' := by
  apply Equiv.ext
  intro v
  obtain ⟨w, hw⟩ := D.surj (Multiplicative.ofAdd v)
  have := h w
  rw [hw] at this
  simpa using this

noncomputable def SLNatData.psiFun (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) :
    Equiv.Perm (Fin 2 → F) :=
  Classical.choose (D.exists_perm x.2)

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.psiFun_spec (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) (w : W) :
    Multiplicative.toAdd (D.β ((x : MulAut W) w)) =
      D.psiFun x (Multiplicative.toAdd (D.β w)) :=
  Classical.choose_spec (D.exists_perm x.2) w

noncomputable def SLNatData.psi :
    ↥(Subgroup.normalizer (E : Set (MulAut W))) →* Equiv.Perm (Fin 2 → F) :=
  MonoidHom.mk' D.psiFun fun a b => by
    apply D.perm_unique
    intro w
    have h1 := D.psiFun_spec (a * b) w
    have h2 := D.psiFun_spec a ((b : MulAut W) w)
    have h3 := D.psiFun_spec b w
    rw [← h1, Equiv.Perm.mul_apply, ← h3, ← h2]
    rfl

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.psi_spec (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) (w : W) :
    Multiplicative.toAdd (D.β ((x : MulAut W) w)) =
      D.psi x (Multiplicative.toAdd (D.β w)) :=
  D.psiFun_spec x w

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.psi_add (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) (v v' : Fin 2 → F) :
    D.psi x (v + v') = D.psi x v + D.psi x v' := by
  obtain ⟨w, hw⟩ := D.surj (Multiplicative.ofAdd v)
  obtain ⟨w', hw'⟩ := D.surj (Multiplicative.ofAdd v')
  have hv : Multiplicative.toAdd (D.β w) = v := by rw [hw]; rfl
  have hv' : Multiplicative.toAdd (D.β w') = v' := by rw [hw']; rfl
  have e1 : v + v' = Multiplicative.toAdd (D.β (w * w')) := by
    rw [map_mul]
    show _ = Multiplicative.toAdd (D.β w) + Multiplicative.toAdd (D.β w')
    rw [hv, hv']
  rw [e1, ← D.psi_spec x (w * w'), map_mul (x : MulAut W), map_mul D.β]
  show Multiplicative.toAdd (D.β ((x : MulAut W) w)) +
    Multiplicative.toAdd (D.β ((x : MulAut W) w')) = _
  rw [D.psi_spec x w, D.psi_spec x w', hv, hv']

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.psi_of_mem (e : E) :
    D.psi ⟨(e : MulAut W), Subgroup.le_normalizer e.2⟩ = slPerm F (D.θ e) := by
  apply D.perm_unique
  intro w
  rw [← D.psi_spec ⟨(e : MulAut W), Subgroup.le_normalizer e.2⟩ w, D.equivar' e w]
  rfl

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.beta_eq_of_psi_eq_one {x : ↥(Subgroup.normalizer (E : Set (MulAut W)))}
    (hx : D.psi x = 1) (w : W) : D.β ((x : MulAut W) w) = D.β w := by
  apply Multiplicative.toAdd.injective
  rw [D.psi_spec x w, hx]
  rfl

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.commute_of_psi_eq_one {x : ↥(Subgroup.normalizer (E : Set (MulAut W)))}
    (hx : D.psi x = 1) {e : MulAut W} (he : e ∈ E) :
    (x : MulAut W) * e = e * (x : MulAut W) := by
  have hxE : (x : MulAut W) * e * (x : MulAut W)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp x.2 e).mp he
  have hinv : ∀ w, D.β ((x : MulAut W)⁻¹ w) = D.β w := fun w => by
    have := D.beta_eq_of_psi_eq_one hx ((x : MulAut W)⁻¹ w)
    rw [show (x : MulAut W) ((x : MulAut W)⁻¹ w) = w by simp] at this
    exact this.symm
  have h1 : D.θ ⟨(x : MulAut W) * e * (x : MulAut W)⁻¹, hxE⟩ = D.θ ⟨e, he⟩ := by
    apply slPerm_injective (k := F)
    apply D.perm_unique
    intro w
    change D.θ ⟨(x : MulAut W) * e * (x : MulAut W)⁻¹, hxE⟩ • Multiplicative.toAdd (D.β w) =
      D.θ ⟨e, he⟩ • Multiplicative.toAdd (D.β w)
    rw [← D.equivar' ⟨(x : MulAut W) * e * (x : MulAut W)⁻¹, hxE⟩ w, ← D.equivar' ⟨e, he⟩ w]
    show Multiplicative.toAdd (D.β ((x : MulAut W) (e ((x : MulAut W)⁻¹ w)))) =
      Multiplicative.toAdd (D.β (e w))
    rw [D.beta_eq_of_psi_eq_one hx, D.equivar' ⟨e, he⟩, hinv, D.equivar' ⟨e, he⟩]
  have h2 := D.θ.injective h1
  have h3 : (x : MulAut W) * e * (x : MulAut W)⁻¹ = e := congrArg Subtype.val h2
  calc (x : MulAut W) * e = (x : MulAut W) * e * (x : MulAut W)⁻¹ * (x : MulAut W) := by group
    _ = e * (x : MulAut W) := by rw [h3]

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.eq_one_of_psi_eq_one {x : ↥(Subgroup.normalizer (E : Set (MulAut W)))}
    (hx : D.psi x = 1) : (x : MulAut W) = 1 := by
  have hcomm := fun e he => D.commute_of_psi_eq_one hx (e := e) he
  let K : Subgroup W :=
    { carrier := {w | (x : MulAut W) w = w}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha] }
  have hle : commV E ≤ K := by
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨e, he, w, rfl⟩
    have hφ : (x : MulAut W) w * w⁻¹ ∈ fixV E := by
      rw [← D.ker_iff, map_mul, map_inv, D.beta_eq_of_psi_eq_one hx]
      exact mul_inv_cancel _
    have hex : (x : MulAut W) (e w) = e ((x : MulAut W) w) := by
      have := hcomm e he
      exact congrArg (fun f : MulAut W => f w) this
    set φ := (x : MulAut W) w * w⁻¹ with hφdef
    have hxw : (x : MulAut W) w = φ * w := by rw [hφdef]; simp
    show (x : MulAut W) (e w * w⁻¹) = e w * w⁻¹
    have hef : e φ = φ := hφ e he
    calc (x : MulAut W) (e w * w⁻¹) = e ((x : MulAut W) w) * ((x : MulAut W) w)⁻¹ := by
          rw [map_mul, map_inv, hex]
      _ = (φ * e w) * (φ * w)⁻¹ := by rw [hxw, map_mul, hef]
      _ = e w * w⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  have htop : ∀ w : W, (x : MulAut W) w = w := fun w => by
    have : w ∈ K := hle (by rw [D.comm_top]; exact Subgroup.mem_top w)
    exact this
  exact MulEquiv.ext fun w => htop w

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.psi_injective : Function.Injective D.psi := by
  rw [injective_iff_map_eq_one]
  intro x hx
  exact Subtype.ext (D.eq_one_of_psi_eq_one hx)

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.psi_zero (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) : D.psi x 0 = 0 := by
  have := D.psi_add x 0 0
  simpa using this

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.psi_neg (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) (v : Fin 2 → F) :
    D.psi x (-v) = -D.psi x v := by
  have h0 := D.psi_add x v (-v)
  rw [add_neg_cancel, D.psi_zero] at h0
  exact (neg_eq_of_add_eq_zero_right h0.symm).symm

noncomputable def SLNatData.cd (A : Subgroup (MulAut W)) :
    Subgroup (Multiplicative (Fin 2 → F)) where
  carrier := {d | ∀ x : ↥(Subgroup.normalizer (E : Set (MulAut W))), (x : MulAut W) ∈ A →
    D.psi x (Multiplicative.toAdd d) = Multiplicative.toAdd d}
  one_mem' := fun x _ => D.psi_zero x
  mul_mem' := fun {d d'} hd hd' x hx => by
    show D.psi x (Multiplicative.toAdd d + Multiplicative.toAdd d') = _
    rw [D.psi_add, hd x hx, hd' x hx]
    rfl
  inv_mem' := fun {d} hd x hx => by
    show D.psi x (-Multiplicative.toAdd d) = -Multiplicative.toAdd d
    rw [D.psi_neg, hd x hx]

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.mem_cd_iff (A : Subgroup (MulAut W)) (d : Multiplicative (Fin 2 → F)) :
    d ∈ D.cd A ↔ Multiplicative.toAdd d ∈
      fixSet ((A.subgroupOf (Subgroup.normalizer (E : Set (MulAut W)))).map D.psi) := by
  constructor
  · intro hd b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
    exact hd x (Subgroup.mem_subgroupOf.mp hx)
  · intro hd x hx
    exact hd _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx))

omit [CharP F 2] in
theorem SLNatData.index_chain (A : Subgroup (MulAut W)) :
    (fixV A).map D.β ≤ D.cd A ∧ (D.cd A).index ≤ ((fixV A).map D.β).index ∧
      ((fixV A).map D.β).index ≤ (fixV A).index := by
  have hPC : (fixV A).map D.β ≤ D.cd A := by
    rintro _ ⟨w, hw, rfl⟩ x hx
    have hfix : (x : MulAut W) w = w := hw _ hx
    have h := D.psi_spec x w
    rw [hfix] at h
    exact h.symm
  refine ⟨hPC, Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hPC), ?_⟩
  rw [Subgroup.index_map, MonoidHom.range_eq_top.mpr D.surj, Subgroup.index_top, mul_one]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le le_sup_left)

omit [Finite W] [Finite F] [CharP F 2] in
theorem SLNatData.card_fixSet_eq (A : Subgroup (MulAut W)) :
    Nat.card (D.cd A) =
      Nat.card (fixSet ((A.subgroupOf (Subgroup.normalizer (E : Set (MulAut W)))).map D.psi)) :=
  Nat.card_congr ⟨fun d => ⟨Multiplicative.toAdd d.1, (D.mem_cd_iff A d.1).mp d.2⟩,
    fun v => ⟨Multiplicative.ofAdd v.1, (D.mem_cd_iff A (Multiplicative.ofAdd v.1)).mpr v.2⟩,
    fun _ => rfl, fun _ => rfl⟩

omit [Field F] [Finite F] [CharP F 2] in
theorem SLNatData.card_dual : Nat.card (Multiplicative (Fin 2 → F)) = Nat.card F ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp

omit [CharP F 2] in
theorem SLNatData.card_le_offender (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut W)))
    (hAw : Nat.card W ≤ Nat.card A * Nat.card (fixV A)) :
    Nat.card F ^ 2 ≤
      Nat.card ((A.subgroupOf (Subgroup.normalizer (E : Set (MulAut W)))).map D.psi) *
      Nat.card (fixSet ((A.subgroupOf (Subgroup.normalizer (E : Set (MulAut W)))).map D.psi)) := by
  have hBA : Nat.card ((A.subgroupOf (Subgroup.normalizer (E : Set (MulAut W)))).map D.psi) =
      Nat.card A := by
    rw [Subgroup.card_map_of_injective D.psi_injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  obtain ⟨-, h2, h1⟩ := D.index_chain A
  have h3 : Nat.card (D.cd A) * (D.cd A).index = Nat.card (Multiplicative (Fin 2 → F)) :=
    Subgroup.card_mul_index _
  have h4 : Nat.card (fixV A) * (fixV A).index = Nat.card W := Subgroup.card_mul_index _
  have hPpos : 0 < Nat.card (fixV A) := Nat.card_pos
  have h5 : (fixV A).index ≤ Nat.card A := by
    have : Nat.card (fixV A) * (fixV A).index ≤ Nat.card (fixV A) * Nat.card A := by
      rw [h4, mul_comm (Nat.card (fixV A))]
      exact hAw
    exact Nat.le_of_mul_le_mul_left this hPpos
  rw [← SLNatData.card_dual (F := F), ← h3, D.card_fixSet_eq A, hBA, mul_comm (Nat.card A)]
  exact Nat.mul_le_mul_left _ (h2.trans (h1.trans h5))

theorem sl_core (D : SLNatData E F) (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut W)))
    (hA : IsElemAbelian2 A) (hAw : Nat.card W ≤ Nat.card A * Nat.card (fixV A))
    (hEA : ⁅E, A⁆ ≠ ⊥) :
    A ≤ E ∧ Nat.card A = Nat.card F ∧ IsQuadratic A ∧
      Nat.card W = Nat.card A * Nat.card (fixV A) := by
  classical
  set N := Subgroup.normalizer (E : Set (MulAut W)) with hN
  set B := (A.subgroupOf N).map D.psi with hB
  have hcommB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  have hsqB : ∀ a ∈ B, a * a = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by
      have := hA.2 _ (Subgroup.mem_subgroupOf.mp hx)
      simpa [pow_two] using this)
    rw [this, map_one]
  have haddB : ∀ b ∈ B, ∀ w w' : Fin 2 → F, b (w + w') = b w + b w' := by
    rintro _ ⟨x, -, rfl⟩ w w'
    exact D.psi_add x w w'
  have hnormB : ∀ b ∈ B, ∀ g : Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ g' : Matrix.SpecialLinearGroup (Fin 2) F, b * slPerm F g * b⁻¹ = slPerm F g' := by
    rintro _ ⟨x, -, rfl⟩ g
    have hxE : ∀ e : E, (x : MulAut W) * (e : MulAut W) * (x : MulAut W)⁻¹ ∈ E := fun e =>
      (Subgroup.mem_normalizer_iff.mp x.2 e).mp e.2
    refine ⟨D.θ ⟨(x : MulAut W) * (D.θ.symm g : MulAut W) * (x : MulAut W)⁻¹,
      hxE (D.θ.symm g)⟩, ?_⟩
    rw [← D.psi_of_mem ⟨(x : MulAut W) * (D.θ.symm g : MulAut W) * (x : MulAut W)⁻¹,
      hxE (D.θ.symm g)⟩]
    have h1 : slPerm F g =
        D.psi ⟨(D.θ.symm g : MulAut W), Subgroup.le_normalizer (D.θ.symm g).2⟩ := by
      rw [D.psi_of_mem, MulEquiv.apply_symm_apply]
    rw [h1, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hneB : B ≠ ⊥ := by
    intro hbot
    apply hEA
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro e he a ha
    have hpsi : D.psi ⟨a, hAN ha⟩ = 1 := by
      have : D.psi ⟨a, hAN ha⟩ ∈ B := ⟨_, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [hbot] at this
      exact this
    have hcomm := D.commute_of_psi_eq_one hpsi he
    rw [Subgroup.mem_bot]
    exact (commutatorElement_eq_one_iff_mul_comm).mpr hcomm.symm
  obtain ⟨ℓ, hℓ⟩ := eq_rootPerm_of_offender_normalizer B haddB hnormB hcommB hsqB hneB
    (D.card_le_offender hAN hAw)
  have hBA : Nat.card B = Nat.card A := by
    rw [hB, Subgroup.card_map_of_injective D.psi_injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hAF : Nat.card A = Nat.card F := by
    rw [← hBA, hℓ, card_rootPerm]
  have hAE : A ≤ E := by
    intro a ha
    have hmem : D.psi ⟨a, hAN ha⟩ ∈ rootPerm ℓ := by
      rw [← hℓ]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    obtain ⟨g, -, hg⟩ := mem_rootPerm.mp hmem
    have h1 : D.psi ⟨(D.θ.symm g : MulAut W), Subgroup.le_normalizer (D.θ.symm g).2⟩ =
        slPerm F g := by
      rw [D.psi_of_mem, MulEquiv.apply_symm_apply]
    have h2 : (⟨a, hAN ha⟩ : ↥N) = ⟨(D.θ.symm g : MulAut W),
        Subgroup.le_normalizer (D.θ.symm g).2⟩ := D.psi_injective (by rw [← hg, h1])
    have h3 : a = (D.θ.symm g : MulAut W) := congrArg Subtype.val h2
    rw [h3]
    exact (D.θ.symm g).2
  have hcard_cd : Nat.card (D.cd A) = Nat.card F := by
    rw [D.card_fixSet_eq A, ← hB, hℓ]
    exact card_fixSet_rootPerm ℓ
  obtain ⟨hPC, h2, h1⟩ := D.index_chain A
  have h3 : Nat.card (D.cd A) * (D.cd A).index = Nat.card F ^ 2 := by
    rw [Subgroup.card_mul_index, SLNatData.card_dual (F := F)]
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have hcdi : (D.cd A).index = Nat.card F := by
    rw [hcard_cd, pow_two] at h3
    exact Nat.eq_of_mul_eq_mul_left hFpos h3
  have h4 : Nat.card (fixV A) * (fixV A).index = Nat.card W := Subgroup.card_mul_index _
  have hPpos : 0 < Nat.card (fixV A) := Nat.card_pos
  have h5 : (fixV A).index ≤ Nat.card A := by
    have : Nat.card (fixV A) * (fixV A).index ≤ Nat.card (fixV A) * Nat.card A := by
      rw [h4, mul_comm (Nat.card (fixV A))]
      exact hAw
    exact Nat.le_of_mul_le_mul_left this hPpos
  have hPi : (fixV A).index = Nat.card F := by omega
  have hβPi : ((fixV A).map D.β).index = Nat.card F := by omega
  have hmapeq : (fixV A).map D.β = D.cd A := by
    refine Subgroup.eq_of_le_of_card_ge hPC ?_
    have e1 : Nat.card ((fixV A).map D.β) * ((fixV A).map D.β).index =
        Nat.card (Multiplicative (Fin 2 → F)) := Subgroup.card_mul_index _
    have e2 : Nat.card (D.cd A) * (D.cd A).index = Nat.card (Multiplicative (Fin 2 → F)) :=
      Subgroup.card_mul_index _
    rw [hβPi, ← hcdi] at e1
    rw [← e1] at e2
    exact (Nat.eq_of_mul_eq_mul_right (by omega) e2).le
  refine ⟨hAE, hAF, ?_, ?_⟩
  ·
    unfold IsQuadratic commV
    rw [Subgroup.closure_le]
    rintro _ ⟨a, ha, w, rfl⟩
    have hmemBA : D.psi ⟨a, hAN ha⟩ ∈ rootPerm ℓ := by
      rw [← hℓ]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    obtain ⟨g, hgℓ, hg⟩ := mem_rootPerm.mp hmemBA
    have hs : Multiplicative.toAdd (D.β ((a : MulAut W) w)) =
        g • Multiplicative.toAdd (D.β w) := by
      rw [D.psi_spec ⟨a, hAN ha⟩ w, ← hg]
      rfl
    have hv : Multiplicative.toAdd (D.β ((a : MulAut W) w * w⁻¹)) =
        g • Multiplicative.toAdd (D.β w) - Multiplicative.toAdd (D.β w) := by
      rw [map_mul, map_inv]
      show Multiplicative.toAdd (D.β ((a : MulAut W) w)) +
        Multiplicative.toAdd ((D.β w)⁻¹) = _
      rw [hs, toAdd_inv, sub_eq_add_neg]
    have hvℓ : Multiplicative.toAdd (D.β ((a : MulAut W) w * w⁻¹)) ∈ ℓ.submodule := by
      rw [hv]
      exact (mem_rootGrp.mp hgℓ) _
    have hcdmem : D.β ((a : MulAut W) w * w⁻¹) ∈ D.cd A := by
      rw [D.mem_cd_iff, ← hB, hℓ, fixSet_rootPerm]
      exact hvℓ
    rw [← hmapeq] at hcdmem
    obtain ⟨p, hp, hpβ⟩ := hcdmem
    have hker : (a : MulAut W) w * w⁻¹ * p⁻¹ ∈ fixV E := by
      apply D.ker_fix
      rw [map_mul, map_inv, hpβ]
      exact mul_inv_cancel _
    have hfixA : (a : MulAut W) w * w⁻¹ * p⁻¹ ∈ fixV A := fun x hx => hker x (hAE hx)
    have := (fixV A).mul_mem hfixA hp
    simpa using this
  · rw [← h4, hPi, hAF]
    ring

end SLCore

end CFSG.CGT.PushingUpLit.BHS
