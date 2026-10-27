module

public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open scoped commutatorElement

@[expose] def iterHom {G : Type*} [Group G] (Φ : G →* G) : ℕ → (G →* G)
  | 0 => MonoidHom.id G
  | n + 1 => Φ.comp (iterHom Φ n)

section Iter

variable {G : Type*} [Group G] (Φ : G →* G)

@[simp] theorem iterHom_zero (x : G) : iterHom Φ 0 x = x := rfl

theorem iterHom_succ (n : ℕ) (x : G) : iterHom Φ (n + 1) x = Φ (iterHom Φ n x) := rfl

theorem iterHom_add (m n : ℕ) (x : G) : iterHom Φ (m + n) x = iterHom Φ m (iterHom Φ n x) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, iterHom_succ, iterHom_succ, ih]

end Iter

structure CycFamily {G : Type*} [Group G] (F : G →* G) (s : ℕ) [NeZero s] where
  S : ZMod s → Subgroup G
  map_eq : ∀ k, (S k).map F = S (k + 1)
  comm : ∀ j k, j ≠ k → ∀ x ∈ S j, ∀ y ∈ S k, Commute x y

namespace CycFamily

variable {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s] (P : CycFamily F s)

@[expose] def A : Subgroup G := ⨆ k, P.S k

@[expose] def Z : Subgroup G := Subgroup.centralizer (P.A : Set G)

theorem mem_Z {z : G} : z ∈ P.Z ↔ ∀ a ∈ P.A, a * z = z * a := Subgroup.mem_centralizer_iff

theorem S_le_A (k : ZMod s) : P.S k ≤ P.A := le_iSup (fun k => P.S k) k

theorem comm' : Pairwise fun i j : ZMod s => ∀ x y : G, x ∈ P.S i → y ∈ P.S j → Commute x y :=
  fun i j hne x y hx hy => P.comm i j hne x hx y hy

@[expose] def mu : (∀ k, P.S k) →* G :=
  Subgroup.noncommPiCoprod P.comm'

theorem mu_mulSingle (k : ZMod s) (y : P.S k) : P.mu (Pi.mulSingle k y) = (y : G) := by
  classical
  exact Subgroup.noncommPiCoprod_mulSingle _ _

theorem mu_range : P.mu.range = P.A := by
  classical
  exact Subgroup.noncommPiCoprod_range

theorem mem_A_iff {x : G} : x ∈ P.A ↔ ∃ f : ∀ k, P.S k, P.mu f = x := by
  rw [← P.mu_range]
  rfl

theorem commute_mu_of_commute (f₁ f₂ : ∀ k, P.S k) (h : f₁ * f₂ = f₂ * f₁) :
    Commute (P.mu f₁) (P.mu f₂) := by
  unfold Commute SemiconjBy
  rw [← map_mul, ← map_mul, h]

@[expose] def Fk (k : ZMod s) : P.S k →* P.S (k + 1) :=
  (F.comp (P.S k).subtype).codRestrict (P.S (k + 1)) fun x => by
    rw [← P.map_eq k]
    exact Subgroup.mem_map_of_mem F x.2

@[simp] theorem coe_Fk (k : ZMod s) (x : P.S k) : ((P.Fk k x : P.S (k + 1)) : G) = F (x : G) :=
  rfl

@[expose] def shift : (∀ k, P.S k) →* (∀ k, P.S k) :=
  MonoidHom.noncommPiCoprod (fun k => (MonoidHom.mulSingle (fun j => P.S j) (k + 1)).comp (P.Fk k))
    (fun i j hij x y => by
      classical
      exact Pi.mulSingle_commute (fun h => hij (add_right_cancel h)) _ _)

theorem shift_mulSingle (k : ZMod s) (y : P.S k) :
    P.shift (Pi.mulSingle k y) = Pi.mulSingle (k + 1) (P.Fk k y) := by
  classical
  exact MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem val_mulSingle_of_eq {a i : ZMod s} (h : a = i) (y : P.S i) :
    ((Pi.mulSingle (M := fun j => P.S j) i y a : P.S a) : G) = (y : G) := by
  classical
  subst h
  simp

theorem val_mulSingle_of_ne {a i : ZMod s} (h : a ≠ i) (y : P.S i) :
    ((Pi.mulSingle (M := fun j => P.S j) i y a : P.S a) : G) = 1 := by
  classical
  rw [Pi.mulSingle_eq_of_ne h]
  rfl

theorem F_mu (f : ∀ k, P.S k) : F (P.mu f) = P.mu (P.shift f) := by
  classical
  have : F.comp P.mu = P.mu.comp P.shift := by
    refine MonoidHom.pi_ext fun i y => ?_
    simp only [MonoidHom.comp_apply, mu_mulSingle, shift_mulSingle]
    rfl
  exact DFunLike.congr_fun this f

theorem coe_shift_apply (f : ∀ k, P.S k) (k : ZMod s) :
    ((P.shift f k : P.S k) : G) = F ((f (k - 1) : P.S (k - 1)) : G) := by
  classical
  have : ((P.S k).subtype.comp ((Pi.evalMonoidHom (fun j => P.S j) k).comp P.shift)) =
      F.comp (((P.S (k - 1)).subtype).comp (Pi.evalMonoidHom (fun j => P.S j) (k - 1))) := by
    refine MonoidHom.pi_ext fun i y => ?_
    simp only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Subgroup.coe_subtype,
      shift_mulSingle]
    by_cases h : k = i + 1
    · have h' : k - 1 = i := by rw [h]; exact add_sub_cancel_right _ _
      rw [P.val_mulSingle_of_eq h, P.val_mulSingle_of_eq h']
      rfl
    · have h' : k - 1 ≠ i := fun h' => h (by rw [← h']; exact (sub_add_cancel k 1).symm)
      rw [P.val_mulSingle_of_ne h, P.val_mulSingle_of_ne h', map_one]
  exact DFunLike.congr_fun this f

theorem mem_Z_of_mu_eq_one (g : ∀ k, P.S k) (hg : P.mu g = 1) (k : ZMod s) : (g k : G) ∈ P.Z := by
  classical
  rw [mem_Z]
  intro a ha
  obtain ⟨h, rfl⟩ := P.mem_A_iff.1 ha
  have hg' : g = Pi.mulSingle k (g k) * Function.update g k 1 := by
    funext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
  have hh' : h = Pi.mulSingle k (h k) * Function.update h k 1 := by
    funext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
  have hdisj : ∀ (u v : ∀ j, P.S j), u k = 1 → Commute (P.mu (Pi.mulSingle k (v k))) (P.mu u) := by
    intro u v hu
    refine P.commute_mu_of_commute _ _ ?_
    funext j
    by_cases hj : j = k
    · subst hj
      simp [hu]
    · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj]
  have hgk : (g k : G) = (P.mu (Function.update g k 1))⁻¹ := by
    have h1 : P.mu g = (g k : G) * P.mu (Function.update g k 1) := by
      conv_lhs => rw [hg', map_mul, mu_mulSingle]
    rw [hg] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have c1 : Commute (g k : G) (P.mu (Function.update h k 1)) := by
    have := hdisj (Function.update h k 1) g (by simp)
    rwa [mu_mulSingle] at this
  have c2 : Commute (g k : G) (h k : G) := by
    have c := hdisj (Function.update g k 1) h (by simp)
    rw [mu_mulSingle] at c
    rw [hgk]
    exact (c.symm.inv_left)
  have hmu : P.mu h = (h k : G) * P.mu (Function.update h k 1) := by
    conv_lhs => rw [hh', map_mul, mu_mulSingle]
  rw [hmu]
  exact (c2.mul_right c1).eq.symm

theorem mu_mem_Z (f : ∀ k, P.S k) (h : ∀ k, (f k : G) ∈ P.Z) : P.mu f ∈ P.Z := by
  unfold mu
  rw [Subgroup.noncommPiCoprod_apply]
  exact Subgroup.noncommProd_mem _ _ fun k _ => h k

theorem F_A : P.A.map F = P.A := by
  refine le_antisymm ?_ ?_
  · unfold A
    rw [Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [P.map_eq k]
    exact P.S_le_A (k + 1)
  · refine iSup_le fun k => ?_
    have h := P.map_eq (k - 1)
    rw [sub_add_cancel] at h
    rw [← h]
    exact Subgroup.map_mono (P.S_le_A (k - 1))

theorem F_mem_Z {z : G} (hz : z ∈ P.Z) : F z ∈ P.Z := by
  rw [mem_Z] at hz ⊢
  intro a ha
  rw [← P.F_A] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  rw [← map_mul, ← map_mul, hz a' ha']

theorem val_apply_congr (f : ∀ k, P.S k) {a b : ZMod s} (h : a = b) :
    ((f a : P.S a) : G) = ((f b : P.S b) : G) := by
  subst h
  rfl

theorem iterHom_mem (n : ℕ) {y : G} (hy : y ∈ P.S 0) : iterHom F n y ∈ P.S (n : ZMod s) := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
    rw [iterHom_succ, Nat.cast_succ, ← P.map_eq]
    exact Subgroup.mem_map_of_mem F ih

@[expose] def iter (k : ZMod s) : P.S 0 →* P.S k :=
  ((iterHom F k.val).comp (P.S 0).subtype).codRestrict (P.S k) fun y => by
    have := P.iterHom_mem k.val y.2
    rwa [ZMod.natCast_zmod_val] at this

@[simp] theorem coe_iter (k : ZMod s) (y : P.S 0) :
    ((P.iter k y : P.S k) : G) = iterHom F k.val (y : G) := rfl

@[expose] def diag : P.S 0 →* (∀ k, P.S k) := MonoidHom.pi P.iter

@[expose] def norm : P.S 0 →* G := P.mu.comp P.diag

theorem norm_mem_A (y : P.S 0) : P.norm y ∈ P.A := by
  rw [← P.mu_range]
  exact ⟨_, rfl⟩

theorem iterHom_s_mem {y : G} (hy : y ∈ P.S 0) : iterHom F s y ∈ P.S 0 := by
  have := P.iterHom_mem s hy
  rwa [ZMod.natCast_self] at this

theorem Y_mul_aux {y y' : G} (hy : y ∈ P.S 0)
    (hyz' : iterHom F s y' * y'⁻¹ ∈ P.Z) :
    iterHom F s (y * y') * (y * y')⁻¹ = (iterHom F s y * y⁻¹) * (iterHom F s y' * y'⁻¹) := by
  have hyA : y ∈ P.A := P.S_le_A 0 hy
  have hc : Commute y (iterHom F s y' * y'⁻¹) := (P.mem_Z.1 hyz') y hyA
  rw [map_mul, mul_inv_rev]
  calc iterHom F s y * iterHom F s y' * (y'⁻¹ * y⁻¹)
      = iterHom F s y * ((iterHom F s y' * y'⁻¹) * y⁻¹) := by group
    _ = iterHom F s y * (y⁻¹ * (iterHom F s y' * y'⁻¹)) := by rw [← hc.inv_left.eq]
    _ = _ := by group

theorem Y_inv_aux {y : G} (hy : y ∈ P.S 0) (hyz : iterHom F s y * y⁻¹ ∈ P.Z) :
    iterHom F s y⁻¹ * (y⁻¹)⁻¹ = (iterHom F s y * y⁻¹)⁻¹ := by
  have hyA : y ∈ P.A := P.S_le_A 0 hy
  obtain ⟨c, hcdef⟩ : ∃ c, c = iterHom F s y * y⁻¹ := ⟨_, rfl⟩
  have hcZ : c ∈ P.Z := hcdef ▸ hyz
  have hc : y * c⁻¹ = c⁻¹ * y := (P.mem_Z.1 (inv_mem hcZ)) y hyA
  have e : iterHom F s y = c * y := by rw [hcdef]; group
  rw [← hcdef, map_inv, inv_inv, e, mul_inv_rev]
  calc y⁻¹ * c⁻¹ * y = y⁻¹ * (c⁻¹ * y) := by group
    _ = y⁻¹ * (y * c⁻¹) := by rw [hc]
    _ = c⁻¹ := by group

@[expose] def Y : Subgroup G where
  carrier := {y | y ∈ P.S 0 ∧ iterHom F s y * y⁻¹ ∈ P.Z}
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    simp
  mul_mem' := by
    rintro y y' ⟨hy, hyz⟩ ⟨hy', hyz'⟩
    refine ⟨mul_mem hy hy', ?_⟩
    rw [P.Y_mul_aux hy hyz']
    exact mul_mem hyz hyz'
  inv_mem' := by
    rintro y ⟨hy, hyz⟩
    refine ⟨inv_mem hy, ?_⟩
    rw [P.Y_inv_aux hy hyz]
    exact inv_mem hyz

theorem mem_Y {y : G} : y ∈ P.Y ↔ y ∈ P.S 0 ∧ iterHom F s y * y⁻¹ ∈ P.Z := Iff.rfl

@[simp] theorem coe_diag_apply (y : P.S 0) (k : ZMod s) :
    ((P.diag y k : P.S k) : G) = iterHom F k.val (y : G) := rfl

theorem exists_eq_zeta_norm {x : G} (hxA : x ∈ P.A) (hx : F x = x) :
    ∃ y : P.S 0, (y : G) ∈ P.Y ∧ ∃ ζ ∈ P.Z, ζ ∈ P.A ∧ x = ζ * P.norm y := by
  obtain ⟨f, rfl⟩ := P.mem_A_iff.1 hxA
  have hF : P.mu (P.shift f) = P.mu f := by rw [← P.F_mu]; exact hx
  set g : ∀ k, P.S k := P.shift f * f⁻¹ with hg
  have hgmu : P.mu g = 1 := by rw [hg, map_mul, map_inv, hF]; exact mul_inv_cancel _
  have hgZ : ∀ k, (g k : G) ∈ P.Z := fun k => P.mem_Z_of_mu_eq_one g hgmu k
  have hgk : ∀ k, ((g k : P.S k) : G) = F ((f (k - 1) : P.S (k - 1)) : G) * ((f k : P.S k) : G)⁻¹ := by
    intro k
    simp [hg, P.coe_shift_apply]
  have hrec : ∀ k : ZMod s, ((f k : P.S k) : G) = ((g k : G))⁻¹ * F ((f (k - 1) : P.S (k - 1)) : G) := by
    intro k
    rw [hgk k]
    group
  have hclaim : ∀ n : ℕ, ∃ ζ ∈ P.Z, ((f (n : ZMod s) : P.S _) : G) =
      ζ * iterHom F n ((f 0 : P.S 0) : G) := by
    intro n
    induction n with
    | zero =>
      refine ⟨1, one_mem _, ?_⟩
      rw [P.val_apply_congr f (Nat.cast_zero (R := ZMod s))]
      simp
    | succ n ih =>
      obtain ⟨ζ, hζ, hζe⟩ := ih
      have hidx : ((n + 1 : ℕ) : ZMod s) - 1 = (n : ZMod s) := by
        rw [Nat.cast_succ]
        exact add_sub_cancel_right _ _
      refine ⟨((g ((n + 1 : ℕ) : ZMod s) : G))⁻¹ * F ζ,
        mul_mem (inv_mem (hgZ _)) (P.F_mem_Z hζ), ?_⟩
      rw [hrec, P.val_apply_congr f hidx, hζe, iterHom_succ, map_mul]
      group
  obtain ⟨ζs, hζsZ, hζs⟩ := hclaim s
  have h0 : ((f ((s : ℕ) : ZMod s) : P.S _) : G) = ((f 0 : P.S 0) : G) :=
    P.val_apply_congr f (ZMod.natCast_self s)
  rw [h0] at hζs
  refine ⟨f 0, ⟨(f 0).2, ?_⟩, P.mu (f * (P.diag (f 0))⁻¹), P.mu_mem_Z _ fun k => ?_, ?_, ?_⟩
  · have : iterHom F s ((f 0 : P.S 0) : G) * ((f 0 : P.S 0) : G)⁻¹ = ζs⁻¹ := by
      generalize iterHom F s ((f 0 : P.S 0) : G) = I at hζs ⊢
      rw [hζs]
      group
    rw [this]
    exact inv_mem hζsZ
  · obtain ⟨ζ, hζ, hζe⟩ := hclaim k.val
    have h1 : ((f ((k.val : ℕ) : ZMod s) : P.S _) : G) = ((f k : P.S k) : G) :=
      P.val_apply_congr f (ZMod.natCast_zmod_val k)
    rw [h1] at hζe
    simp only [Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, coe_diag_apply]
    rw [hζe]
    simpa using hζ
  · rw [← P.mu_range]
    exact ⟨_, rfl⟩
  · show P.mu f = P.mu (f * (P.diag (f 0))⁻¹) * P.mu (P.diag (f 0))
    rw [← map_mul, inv_mul_cancel_right]

omit [NeZero s] in
theorem iterHom_periodic {y : G} (hy : iterHom F s y = y) (n : ℕ) :
    iterHom F n y = iterHom F (n % s) y := by
  have hper : ∀ m, iterHom F (m + s) y = iterHom F m y := fun m => by
    rw [iterHom_add, hy]
  have : ∀ q r : ℕ, iterHom F (r + s * q) y = iterHom F r y := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, ← add_assoc, hper, ih]
  conv_lhs => rw [← Nat.mod_add_div n s]
  exact this _ _

theorem val_sub_one_succ_mod (k : ZMod s) : ((k - 1).val + 1) % s = k.val := by
  have h : (((k - 1).val + 1 : ℕ) : ZMod s) = k := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact sub_add_cancel k 1
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast] at this

theorem F_norm {y : P.S 0} (hy : iterHom F s (y : G) = y) : F (P.norm y) = P.norm y := by
  have h1 : P.shift (P.diag y) = P.diag y := by
    funext k
    apply Subtype.ext
    rw [P.coe_shift_apply, coe_diag_apply, coe_diag_apply, ← iterHom_succ,
      iterHom_periodic hy, val_sub_one_succ_mod]
  show F (P.mu (P.diag y)) = P.mu (P.diag y)
  rw [P.F_mu, h1]

theorem mem_Z_of_norm_eq_one {y : P.S 0} (h : P.norm y = 1) : (y : G) ∈ P.Z := by
  have := P.mem_Z_of_mu_eq_one (P.diag y) h 0
  simpa using this

@[expose] def Afix : Subgroup G := P.A ⊓ F.eqLocus (MonoidHom.id G)

theorem norm_mem_Afix {y : P.S 0} (hy : iterHom F s (y : G) = y) : P.norm y ∈ P.Afix :=
  ⟨P.norm_mem_A y, P.F_norm hy⟩

theorem commutatorElement_central_mul_left {ζ a w : G} (hζa : Commute ζ a) (hζw : Commute ζ w) :
    ⁅ζ * a, w⁆ = ⁅a, w⁆ := by
  have hcw : Commute ζ (a * w * a⁻¹) := (hζa.mul_right hζw).mul_right hζa.inv_right
  calc ⁅ζ * a, w⁆ = (ζ * (a * w * a⁻¹) * ζ⁻¹) * w⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, w⁆ := by rw [hcw.mul_inv_cancel]; simp [commutatorElement_def]

theorem commutatorElement_central_mul_right {ζ a b : G} (hζa : Commute ζ a) (hζb : Commute ζ b) :
    ⁅a, ζ * b⁆ = ⁅a, b⁆ := by
  have hc : Commute ζ ⁅a, b⁆ := by
    simp only [commutatorElement_def]
    exact ((hζa.mul_right hζb).mul_right hζa.inv_right).mul_right hζb.inv_right
  calc ⁅a, ζ * b⁆ = ζ * (a * b * a⁻¹ * b⁻¹) * ζ⁻¹ := by
        have : a * ζ = ζ * a := hζa.symm.eq
        simp only [commutatorElement_def]
        calc a * (ζ * b) * a⁻¹ * (ζ * b)⁻¹ = (a * ζ) * b * a⁻¹ * b⁻¹ * ζ⁻¹ := by group
          _ = ζ * a * b * a⁻¹ * b⁻¹ * ζ⁻¹ := by rw [this]
          _ = _ := by group
    _ = ⁅a, b⁆ := by
        have := hc.mul_inv_cancel
        simpa [commutatorElement_def] using this

theorem commutatorElement_central_mul {ζ ζ' a b : G} (hζa : Commute ζ a) (hζb : Commute ζ b)
    (hζζ : Commute ζ ζ') (hζ'a : Commute ζ' a) (hζ'b : Commute ζ' b) :
    ⁅ζ * a, ζ' * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_central_mul_left hζa (hζζ.mul_right hζb),
    commutatorElement_central_mul_right hζ'a hζ'b]

theorem commutator_fixed {x x' : G} (hx : x ∈ P.Afix) (hx' : x' ∈ P.Afix) :
    ∃ y y' : P.S 0, (y : G) ∈ P.Y ∧ (y' : G) ∈ P.Y ∧ ⁅x, x'⁆ = P.norm ⁅y, y'⁆ := by
  obtain ⟨y, hy, ζ, hζZ, hζA, rfl⟩ := P.exists_eq_zeta_norm hx.1 hx.2
  obtain ⟨y', hy', ζ', hζ'Z, hζ'A, rfl⟩ := P.exists_eq_zeta_norm hx'.1 hx'.2
  refine ⟨y, y', hy, hy', ?_⟩
  rw [map_commutatorElement]
  exact commutatorElement_central_mul ((P.mem_Z.1 hζZ) _ (P.norm_mem_A y)).symm
    ((P.mem_Z.1 hζZ) _ (P.norm_mem_A y')).symm ((P.mem_Z.1 hζZ) _ hζ'A).symm
    ((P.mem_Z.1 hζ'Z) _ (P.norm_mem_A y)).symm ((P.mem_Z.1 hζ'Z) _ (P.norm_mem_A y')).symm

@[expose] def normImage (H : Subgroup G) : Subgroup G := (H.subgroupOf (P.S 0)).map P.norm

theorem mem_normImage {H : Subgroup G} {g : G} :
    g ∈ P.normImage H ↔ ∃ y : P.S 0, (y : G) ∈ H ∧ P.norm y = g := by
  unfold normImage
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => ⟨y, hy, e⟩, fun ⟨y, hy, e⟩ => ⟨y, hy, e⟩⟩

theorem commutator_Afix_le : ⁅P.Afix, P.Afix⁆ ≤ P.normImage ⁅P.Y, P.Y⁆ := by
  rw [Subgroup.commutator_le]
  intro x hx x' hx'
  obtain ⟨y, y', hy, hy', e⟩ := P.commutator_fixed hx hx'
  rw [e, mem_normImage]
  refine ⟨⁅y, y'⁆, ?_, rfl⟩
  have := Subgroup.commutator_mem_commutator hy hy'
  simpa [commutatorElement_def] using this

theorem normImage_le_Afix {H : Subgroup G} (hH : ∀ y ∈ H, y ∈ P.S 0 → iterHom F s y = y) :
    P.normImage H ≤ P.Afix := by
  intro g hg
  obtain ⟨y, hyH, rfl⟩ := (P.mem_normImage).1 hg
  exact P.norm_mem_Afix (hH _ hyH y.2)

end CycFamily

end CFSG.HardMathSupport.Timmesfeld.LangTorus
