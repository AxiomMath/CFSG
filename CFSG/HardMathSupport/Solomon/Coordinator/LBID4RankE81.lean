module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankFrame
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LBID4

open QuadraticMap CFSG.Open

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def Adapted (g : V ≃ₗ[K] V) (F : EFrame Q) : Prop :=
  (g F.b = F.b ∧ g F.b' = F.b') ∨ (g F.b = F.b' ∧ g F.b' = -F.b - F.b')

section PowHom

variable {G : Type*} [Monoid G]

theorem pow_eq_pow_mod_three {r : G} (hr : r ^ 3 = 1) (k : ℕ) : r ^ k = r ^ (k % 3) := by
  conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, hr, one_pow, mul_one]

@[expose] def powHom (r : G) (hr : r ^ 3 = 1) : Multiplicative (ZMod 3) →* G where
  toFun n := r ^ (Multiplicative.toAdd n).val
  map_one' := by simp
  map_mul' n m := by
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod_three hr, pow_add]

theorem powHom_apply (r : G) (hr : r ^ 3 = 1) (n : Multiplicative (ZMod 3)) :
    powHom r hr n = r ^ (Multiplicative.toAdd n).val := rfl

end PowHom

namespace EFrame

theorem eq_zero_of_rot_pow_b (h3 : (3 : K) ≠ 0) (F : EFrame Q) {k : ℕ} (hk : k < 3)
    (h : (F.rot ^ k) F.b = F.b) : k = 0 := by
  interval_cases k
  · rfl
  · exfalso
    rw [pow_one, rot_apply, rotL_b] at h
    exact F.b_ne_b' h3 h.symm
  · exfalso
    rw [pow_two, LinearEquiv.mul_apply, rot_apply, rot_apply, rotL_b, rotL_b'] at h
    exact F.neg_b_sub_b'_ne h3 h

end EFrame

section Frames

variable (F : Fin 4 → EFrame Q)

@[expose] def frameVec : Fin 4 ⊕ Fin 4 → V
  | .inl i => (F i).b
  | .inr i => (F i).b'

@[expose] noncomputable def rotProd (e : Fin 4 → ℕ) : V ≃ₗ[K] V :=
  (F 0).rot ^ e 0 * (F 1).rot ^ e 1 * (F 2).rot ^ e 2 * (F 3).rot ^ e 3

variable {F} (hperp : ∀ i j, i ≠ j → (F i).Perp (F j))
include hperp

theorem rotProd_apply_of_orth (e : Fin 4 → ℕ) (j : Fin 4) {x : V}
    (hx : ∀ i, i ≠ j → (F i).Orth x) : rotProd F e x = ((F j).rot ^ e j) x := by
  simp only [rotProd, LinearEquiv.mul_apply]
  fin_cases j
  · rw [(F 3).rot_pow_of_orth (hx 3 (by decide)), (F 2).rot_pow_of_orth (hx 2 (by decide)),
      (F 1).rot_pow_of_orth (hx 1 (by decide))]
    rfl
  · rw [(F 3).rot_pow_of_orth (hx 3 (by decide)), (F 2).rot_pow_of_orth (hx 2 (by decide))]
    exact (F 0).rot_pow_of_orth ((F 1).orth_rot_pow (hperp 1 0 (by decide)) (hx 0 (by decide)) _) _
  · rw [(F 3).rot_pow_of_orth (hx 3 (by decide))]
    have h1 : (F 1).Orth (((F 2).rot ^ e 2) x) :=
      (F 2).orth_rot_pow (hperp 2 1 (by decide)) (hx 1 (by decide)) _
    have h0 : (F 0).Orth (((F 2).rot ^ e 2) x) :=
      (F 2).orth_rot_pow (hperp 2 0 (by decide)) (hx 0 (by decide)) _
    rw [(F 1).rot_pow_of_orth h1, (F 0).rot_pow_of_orth h0]
    rfl
  · have h2 : (F 2).Orth (((F 3).rot ^ e 3) x) :=
      (F 3).orth_rot_pow (hperp 3 2 (by decide)) (hx 2 (by decide)) _
    have h1 : (F 1).Orth (((F 3).rot ^ e 3) x) :=
      (F 3).orth_rot_pow (hperp 3 1 (by decide)) (hx 1 (by decide)) _
    have h0 : (F 0).Orth (((F 3).rot ^ e 3) x) :=
      (F 3).orth_rot_pow (hperp 3 0 (by decide)) (hx 0 (by decide)) _
    rw [(F 2).rot_pow_of_orth h2, (F 1).rot_pow_of_orth h1, (F 0).rot_pow_of_orth h0]
    rfl

theorem orth_b_of_ne {i j : Fin 4} (h : i ≠ j) : (F i).Orth (F j).b := (hperp i j h).1

theorem orth_b'_of_ne {i j : Fin 4} (h : i ≠ j) : (F i).Orth (F j).b' := (hperp i j h).2

variable (h3 : (3 : K) ≠ 0)
include h3

theorem frameVec_linearIndependent : LinearIndependent K (frameVec F) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have key : ∀ j, a (Sum.inl j) = 0 ∧ a (Sum.inr j) = 0 := by
    intro j
    have e1 := congrArg (pol Q (F j).b) ha
    have e2 := congrArg (pol Q (F j).b') ha
    rw [map_sum, map_zero, Fintype.sum_sum_type] at e1 e2
    simp only [map_smul, pol_apply, smul_eq_mul, frameVec] at e1 e2
    have z1 : ∀ i, i ≠ j → a (Sum.inl i) * polar Q (F i).b (F j).b = 0 := fun i hi => by
      rw [(orth_b_of_ne hperp (Ne.symm hi)).1, mul_zero]
    have z2 : ∀ i, i ≠ j → a (Sum.inr i) * polar Q (F i).b' (F j).b = 0 := fun i hi => by
      rw [(orth_b'_of_ne hperp (Ne.symm hi)).1, mul_zero]
    have z3 : ∀ i, i ≠ j → a (Sum.inl i) * polar Q (F i).b (F j).b' = 0 := fun i hi => by
      rw [(orth_b_of_ne hperp (Ne.symm hi)).2, mul_zero]
    have z4 : ∀ i, i ≠ j → a (Sum.inr i) * polar Q (F i).b' (F j).b' = 0 := fun i hi => by
      rw [(orth_b'_of_ne hperp (Ne.symm hi)).2, mul_zero]
    rw [Finset.sum_eq_single j (fun i _ hi => z1 i hi) (by simp),
      Finset.sum_eq_single j (fun i _ hi => z2 i hi) (by simp), (F j).polar_bb,
      (F j).polar_b'b] at e1
    rw [Finset.sum_eq_single j (fun i _ hi => z3 i hi) (by simp),
      Finset.sum_eq_single j (fun i _ hi => z4 i hi) (by simp), (F j).polar_bb',
      (F j).polar_b'b'] at e2
    have hc := (F j).c_ne
    have h0 : (3 : K) * (F j).c * a (Sum.inl j) = 0 := by linear_combination 2 * e1 + e2
    have h0' : a (Sum.inl j) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (mul_ne_zero h3 hc)
      · exact h
    refine ⟨h0', ?_⟩
    rw [h0'] at e1
    have : (F j).c * a (Sum.inr j) = 0 := by linear_combination -e1
    exact (mul_eq_zero.mp this).resolve_left hc
  rintro (j | j)
  · exact (key j).1
  · exact (key j).2

theorem exists_eq_rotProd [FiniteDimensional K V] (hdim : Module.finrank K V = 8)
    (g : V ≃ₗ[K] V) (hg : ∀ i, Adapted g (F i)) : ∃ e : Fin 4 → ℕ, g = rotProd F e := by
  classical
  let e : Fin 4 → ℕ := fun i => if g (F i).b = (F i).b then 0 else 1
  refine ⟨e, ?_⟩
  have hcard : Fintype.card (Fin 4 ⊕ Fin 4) = Module.finrank K V := by
    rw [hdim]; rfl
  let bas := basisOfLinearIndependentOfCardEqFinrank (frameVec_linearIndependent hperp h3) hcard
  apply LinearEquiv.toLinearMap_injective
  refine bas.ext fun x => ?_
  have hbx : bas x = frameVec F x := by
    simp [bas, coe_basisOfLinearIndependentOfCardEqFinrank]
  rw [hbx]
  rcases x with j | j
  · have hx : ∀ i, i ≠ j → (F i).Orth (F j).b := fun i hi => orth_b_of_ne hperp hi
    change g (F j).b = rotProd F e (F j).b
    rw [rotProd_apply_of_orth hperp e j hx]
    rcases hg j with ⟨h1, -⟩ | ⟨h1, -⟩
    · simp [e, h1]
    · have hne : g (F j).b ≠ (F j).b := by rw [h1]; exact ((F j).b_ne_b' h3).symm
      have he : e j = 1 := by simp [e, hne]
      rw [he, pow_one, EFrame.rot_apply, EFrame.rotL_b, h1]
  · have hx : ∀ i, i ≠ j → (F i).Orth (F j).b' := fun i hi => orth_b'_of_ne hperp hi
    change g (F j).b' = rotProd F e (F j).b'
    rw [rotProd_apply_of_orth hperp e j hx]
    rcases hg j with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [e, h1, h2]
    · have hne : g (F j).b ≠ (F j).b := by rw [h1]; exact ((F j).b_ne_b' h3).symm
      have he : e j = 1 := by simp [e, hne]
      rw [he, pow_one, EFrame.rot_apply, EFrame.rotL_b', h2]

omit hperp in
theorem rot_pow_mem_commutator (i : Fin 4) (n : ℕ) : (F i).rot ^ n ∈
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  Subgroup.pow_mem _ ((F i).rot_mem_commutator h3) n

theorem exists_E81_of_frames [FiniteDimensional K V] (hdim : Module.finrank K V = 8)
    (g : V ≃ₗ[K] V) (hg : ∀ i, Adapted g (F i)) :
    ∃ E : Subgroup (V ≃ₗ[K] V),
      E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ g ∈ E := by
  classical
  let ψ : ∀ i : Fin 4, Multiplicative (ZMod 3) →* (V ≃ₗ[K] V) := fun i =>
    powHom (F i).rot (F i).rot_pow_three
  have hcomm : Pairwise fun i j => ∀ x y, Commute (ψ i x) (ψ j y) := by
    intro i j hij x y
    exact Commute.pow_pow ((F i).rot_comm (hperp i j hij)) _ _
  let φ := MonoidHom.noncommPiCoprod ψ hcomm
  have hrot : ∀ (i : Fin 4) (k : ℕ), ((F i).rot ^ k) (F i).b = (F i).b → k % 3 = 0 := by
    intro i k hk
    have hk' : ((F i).rot ^ (k % 3)) (F i).b = (F i).b := by
      rwa [← pow_eq_pow_mod_three (F i).rot_pow_three]
    exact (F i).eq_zero_of_rot_pow_b h3 (Nat.mod_lt _ (by norm_num)) hk'
  have hψinj : ∀ i, Function.Injective (ψ i) := by
    intro i
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    have h : (((F i).rot) ^ (Multiplicative.toAdd n).val) (F i).b = (F i).b := by
      have := congrArg (fun f : V ≃ₗ[K] V => f (F i).b) hn
      simpa [ψ, powHom_apply] using this
    have hk := hrot i _ h
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _)] at hk
    rw [Subgroup.mem_bot, ← toAdd_eq_zero]
    exact (ZMod.val_eq_zero _).mp hk
  have hind : iSupIndep fun i => (ψ i).range := by
    intro i
    rw [Subgroup.disjoint_def]
    intro x hx hxK
    obtain ⟨n, rfl⟩ := hx
    have hstab : (⨆ (j) (_ : j ≠ i), (ψ j).range) ≤
        MulAction.stabilizer (V ≃ₗ[K] V) (F i).b := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨m, rfl⟩
      rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
      exact (F j).rot_pow_of_orth (orth_b_of_ne hperp hj) _
    have h := hstab hxK
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] at h
    have hk := hrot i _ h
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _)] at hk
    change (F i).rot ^ (Multiplicative.toAdd n).val = 1
    rw [hk, pow_zero]
  have hφ : Function.Injective φ :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep ψ hind hψinj
  have hmem : ∀ i, (F i).rot ∈ φ.range := by
    intro i
    refine ⟨Pi.mulSingle i (Multiplicative.ofAdd 1), ?_⟩
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    change (F i).rot ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3))).val = _
    rw [toAdd_ofAdd]
    exact pow_one _
  refine ⟨φ.range, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨n, rfl⟩
    exact rot_pow_mem_commutator h3 i _
  · obtain ⟨a', ha'⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨b', hb'⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : V ≃ₗ[K] V) * b = b * a
    rw [← ha', ← hb', ← map_mul, ← map_mul, mul_comm a' b']
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      funext i
      change (a i) ^ 3 = 1
      generalize a i = m
      revert m
      decide
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_fun]
    simp
  · obtain ⟨e, rfl⟩ := exists_eq_rotProd hperp h3 hdim g hg
    simp only [rotProd]
    exact φ.range.mul_mem (φ.range.mul_mem (φ.range.mul_mem
      (φ.range.pow_mem (hmem 0) _) (φ.range.pow_mem (hmem 1) _)) (φ.range.pow_mem (hmem 2) _))
      (φ.range.pow_mem (hmem 3) _)

end Frames

end CFSG.HardMathSupport.Solomon.Coordinator.LBID4
