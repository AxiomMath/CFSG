module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSevenTransvectionE7
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCover
public import Certificates.Certificate10093
public import Certificates.Certificate10097

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial

namespace SixCoverTwoKernel

open Subgroup SevenTransvectionE7
open scoped commutatorElement

local notation "tau" => binarySymplecticTransvection b0 b0_isAlt

section Central

variable {E : Type*} [Group E] {C : Subgroup E}

theorem comm_of_mem_center (hC : C ≤ center E) {c : E} (hc : c ∈ C) (g : E) : c * g = g * c :=
  (mem_center_iff.mp (hC hc) g).symm

theorem sq_mul_of_mem (hC : C ≤ center E) {x c : E} (hc : c ∈ C) (hc2 : c ^ 2 = 1) :
    (x * c) ^ 2 = x ^ 2 := by
  have h := comm_of_mem_center hC hc x
  have hcc : c * c = 1 := by rw [← pow_two, hc2]
  rw [pow_two, pow_two, mul_assoc, ← mul_assoc c x c, h, mul_assoc, hcc, mul_one]

theorem commutatorElement_mul_of_mem (hC : C ≤ center E) {x y c d : E} (hc : c ∈ C)
    (hd : d ∈ C) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  have h1 := comm_of_mem_center hC hc (y * d)
  have h2 := comm_of_mem_center hC hd x⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc x * c * (y * d) * (x * c)⁻¹ * (y * d)⁻¹ =
      x * (c * (y * d)) * c⁻¹ * x⁻¹ * (y * d)⁻¹ := by group
    _ = x * (y * d * c) * c⁻¹ * x⁻¹ * (y * d)⁻¹ := by rw [h1]
    _ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [h2]
    _ = x * y * x⁻¹ * y⁻¹ := by group

variable {H : Type*} [Group H] (ρ : E →* H)

theorem sq_eq_of_map_eq (hC : ρ.ker ≤ center E) (h2 : ∀ c ∈ ρ.ker, c ^ 2 = 1) {x y : E}
    (h : ρ x = ρ y) : y ^ 2 = x ^ 2 := by
  have hc : x⁻¹ * y ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h1 := sq_mul_of_mem hC hc (h2 _ hc) (x := x)
  rwa [mul_inv_cancel_left] at h1

theorem commutatorElement_eq_of_map_eq (hC : ρ.ker ≤ center E) {x x' y y' : E}
    (hx : ρ x = ρ x') (hy : ρ y = ρ y') : ⁅x', y'⁆ = ⁅x, y⁆ := by
  have hc : x⁻¹ * x' ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
  have hd : y⁻¹ * y' ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  have h1 := commutatorElement_mul_of_mem hC hc hd (x := x) (y := y)
  rwa [mul_inv_cancel_left, mul_inv_cancel_left] at h1

theorem central_pow_identity {a b : E} (hb : ∀ g, b * g = g * b) (n m : ℕ) :
    b ^ n * a * (a ^ n * b ^ m) = a ^ (n + 1) * b ^ (n + m) := by
  have h1 : b ^ n * a = a * b ^ n := (Commute.pow_left (hb a) n).eq
  have h2 : b ^ n * a ^ n = a ^ n * b ^ n := (Commute.pow_pow (hb a) n n).eq
  rw [pow_succ', pow_add, h1, mul_assoc, ← mul_assoc (b ^ n), h2, mul_assoc, ← mul_assoc a]

theorem sq_list_prod {lam kap : E} (hkap : ∀ g, kap * g = g * kap) (hk2 : kap ^ 2 = 1) :
    ∀ ys : List E, (∀ y ∈ ys, y ^ 2 = lam) → ys.Pairwise (fun y y' => ⁅y, y'⁆ = kap) →
      ys.prod ^ 2 = lam ^ ys.length * kap ^ ys.length.choose 2 := by
  have hkpow : ∀ n g, kap ^ n * g = g * kap ^ n := fun n g => (Commute.pow_left (hkap g) n).eq
  have hmove : ∀ (y : E) (zs : List E), (∀ z ∈ zs, ⁅y, z⁆ = kap) →
      y * zs.prod = kap ^ zs.length * (zs.prod * y) := by
    intro y zs
    induction zs with
    | nil => intro _; simp
    | cons z zs ih =>
      intro hz
      have h1 : y * z = kap * (z * y) := by
        have := hz z (List.mem_cons_self ..)
        rw [commutatorElement_def] at this
        rw [← this]
        group
      have h2 := ih fun w hw => hz w (List.mem_cons_of_mem _ hw)
      rw [List.prod_cons, List.length_cons]
      calc y * (z * zs.prod) = (y * z) * zs.prod := (mul_assoc _ _ _).symm
        _ = kap * (z * (y * zs.prod)) := by rw [h1, mul_assoc, mul_assoc]
        _ = kap * (z * (kap ^ zs.length * (zs.prod * y))) := by rw [h2]
        _ = kap * (kap ^ zs.length * (z * (zs.prod * y))) := by
          rw [← mul_assoc z, ← hkpow, mul_assoc]
        _ = kap ^ (zs.length + 1) * (z * zs.prod * y) := by
          rw [← mul_assoc, ← pow_succ', mul_assoc z]
  intro ys
  induction ys with
  | nil => intro _ _; simp
  | cons y ys ih =>
    intro hsq hpw
    rw [List.pairwise_cons] at hpw
    have hP := ih (fun w hw => hsq w (List.mem_cons_of_mem _ hw)) hpw.2
    have hy := hsq y (List.mem_cons_self ..)
    have hm := hmove y ys hpw.1
    have hkk : kap ^ ys.length * kap ^ ys.length = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, hk2, one_pow]
    have hPy : ys.prod * y = kap ^ ys.length * (y * ys.prod) := by
      rw [hm, ← mul_assoc, hkk, one_mul]
    have h1 : (y * ys.prod) ^ 2 = kap ^ ys.length * lam * ys.prod ^ 2 := by
      calc (y * ys.prod) ^ 2 = y * (ys.prod * y) * ys.prod := by
            rw [pow_two, mul_assoc, mul_assoc, mul_assoc]
        _ = y * (kap ^ ys.length * (y * ys.prod)) * ys.prod := by rw [hPy]
        _ = kap ^ ys.length * (y * y) * (ys.prod * ys.prod) := by
          rw [← mul_assoc y, ← hkpow, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
        _ = kap ^ ys.length * lam * ys.prod ^ 2 := by rw [← pow_two, hy, ← pow_two]
    rw [List.prod_cons, h1, hP, List.length_cons, Nat.choose_succ_succ', Nat.choose_one_right,
      central_pow_identity hkap]

theorem sq_mul_eq_commutatorElement {x y l : E} (hl : ∀ g, l * g = g * l) (hl2 : l ^ 2 = 1)
    (hx : x ^ 2 = l) (hy : y ^ 2 = l) : (x * y) ^ 2 = ⁅x, y⁆ := by
  have hll : l * l = 1 := by rw [← pow_two, hl2]
  have hinv : ∀ z : E, z ^ 2 = l → z⁻¹ = l * z := fun z hz => by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, ← hl z, mul_assoc, ← pow_two, hz, hll]
  rw [commutatorElement_def, hinv x hx, hinv y hy, pow_two, hl x]
  simp only [mul_assoc]
  rw [← mul_assoc l l y, hll, one_mul]

theorem mul_mul_mul_of_central {x y c d : E} (hc : ∀ g, c * g = g * c)
    (hd : ∀ g, d * g = g * d) : x * c * (y * d) = x * y * (c * d) := by
  rw [mul_assoc, hc (y * d), mul_assoc y d c, ← hd c, ← mul_assoc, ← mul_assoc]

theorem pow_three_swap {a b : E} (h : (a * b) ^ 3 = 1) : (b * a) ^ 3 = 1 := by
  have h1 : b * a = a⁻¹ * (a * b) * a⁻¹⁻¹ := by group
  rw [h1, conj_pow, h, mul_one, mul_inv_cancel]

end Central

@[expose] def tauL (c x : ℕ) : ℕ :=
  if pairing (bitVec x) (bitVec c) = 1 then x ^^^ c else x

theorem bitVec_tauL (c x : ℕ) :
    bitVec (tauL c x) = bitVec x + b0 (bitVec x) (bitVec c) • bitVec c := by
  unfold tauL
  split_ifs with h
  · rw [bitVec_xor, b0_apply, h, one_smul]
  · rcases BinarySymplecticTransvection.zmod_two_cases (pairing (bitVec x) (bitVec c)) with h0 | h1
    · rw [b0_apply, h0, zero_smul, add_zero]
    · exact absurd h1 h

@[expose] def pairSteps : List (ℕ × ℕ × ℕ) :=
  [(2, 8, 1), (2, 8, 3), (2, 8, 4), (2, 8, 5), (2, 8, 6), (2, 8, 17), (2, 8, 20), (2, 8, 21),
    (3, 8, 4), (3, 8, 5), (3, 8, 7), (3, 8, 9), (3, 8, 19), (3, 8, 33), (3, 8, 41), (1, 8, 12),
    (1, 8, 22), (6, 12, 17), (6, 12, 36), (2, 13, 7), (2, 13, 29), (2, 13, 37), (2, 13, 39),
    (4, 14, 17), (8, 19, 51), (8, 19, 59), (22, 28, 54), (2, 29, 61), (2, 29, 63), (7, 12, 9),
    (7, 12, 13), (7, 12, 45), (3, 13, 7), (4, 15, 31), (8, 10, 20), (8, 10, 21), (8, 10, 36),
    (1, 30, 62), (12, 23, 36), (4, 31, 63), (5, 7, 45), (10, 12, 36), (10, 12, 46),
    (12, 42, 46), (10, 28, 54), (10, 28, 60), (29, 31, 61), (10, 44, 60), (23, 40, 55)]

@[expose] def pairChainOK : List (ℕ × ℕ) → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | known, (a, b, c) :: rest =>
    decide ((a, b) ∈ known ∨ (b, a) ∈ known) && pairChainOK ((tauL c a, tauL c b) :: known) rest

theorem pairChainOK_pairSteps : pairChainOK [(2, 8)] pairSteps = true := by
  decide

@[expose] def pairsReached : List (ℕ × ℕ) :=
  [(2, 8)] ++ pairSteps.map fun s => (tauL s.2.2 s.1, tauL s.2.2 s.2.1)

theorem forall_of_pairChainOK (Pr : ℕ → ℕ → Prop) (hswap : ∀ a b, Pr a b → Pr b a)
    (hstep : ∀ a b c, Pr a b → Pr (tauL c a) (tauL c b)) :
    ∀ (steps : List (ℕ × ℕ × ℕ)) (known : List (ℕ × ℕ)), (∀ p ∈ known, Pr p.1 p.2) →
      pairChainOK known steps = true →
        ∀ p ∈ known ++ steps.map (fun s => (tauL s.2.2 s.1, tauL s.2.2 s.2.1)), Pr p.1 p.2
  | [], known, hk, _ => by simpa using hk
  | (a, b, c) :: rest, known, hk, hok => by
    simp only [pairChainOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hmem, hrest⟩ := hok
    have hab : Pr a b := by
      rcases hmem with h | h
      · exact hk _ h
      · exact hswap _ _ (hk _ h)
    have hall := forall_of_pairChainOK Pr hswap hstep rest ((tauL c a, tauL c b) :: known) (by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hstep a b c hab
      · exact hk p hp) hrest
    intro p hp
    apply hall
    simp only [List.mem_append, List.mem_cons, List.map_cons] at hp ⊢
    tauto

theorem labels_vE : ∀ i : Fin 7, vE i = bitVec (initLabels.getD i 0) :=
  vE_eq_bitVec

theorem nonEdge_reached : ∀ i k : Fin 7, i ≠ k → s(i, k) ∉ e7Edges →
    (initLabels.getD i 0, initLabels.getD k 0) ∈ pairsReached ∨
      (initLabels.getD k 0, initLabels.getD i 0) ∈ pairsReached := by
  decide

@[expose] def lagLabels : List ℕ := [2, 8, 10, 32, 34, 40, 42]

theorem lag_reached : ∀ w ∈ lagLabels, ∀ w' ∈ lagLabels, w ≠ w' →
    (w, w') ∈ pairsReached ∨ (w', w) ∈ pairsReached := by
  decide

theorem lag_orthogonal : ∀ w ∈ lagLabels, ∀ w' ∈ lagLabels,
    pairing (bitVec w) (bitVec w') = 0 := by
  decide

theorem lag_ne_zero : ∀ w ∈ lagLabels, bitVec w ≠ 0 := by
  decide

theorem lagLabels_nodup : lagLabels.Nodup := by
  decide

theorem lag_sum_basis : ∀ j : Fin 6,
    ((lagLabels.map bitVec).map fun w => pairing (Pi.single j 1) w • w).sum = 0 := by
  decide

theorem prod_tau_apply : ∀ (ws : List (Fin 6 → ZMod 2)),
    (∀ w ∈ ws, ∀ w' ∈ ws, b0 w w' = 0) → ∀ x : Fin 6 → ZMod 2,
      (((ws.map fun w => tau w).prod : LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2)) :
        (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) x =
        x + (ws.map fun w => b0 x w • w).sum
  | [], _, x => by simp
  | w :: ws, hws, x => by
    have ih := prod_tau_apply ws (fun u hu u' hu' =>
      hws u (List.mem_cons_of_mem _ hu) u' (List.mem_cons_of_mem _ hu')) x
    rw [List.map_cons, List.prod_cons, BinarySymplecticTransvection.gl_mul_apply, ih,
      binarySymplecticTransvection_apply]
    have hsum : ∀ us : List (Fin 6 → ZMod 2), (∀ u ∈ us, b0 u w = 0) →
        b0 (us.map fun u => b0 x u • u).sum w = 0 := by
      intro us
      induction us with
      | nil => intro _; simp
      | cons u us ihu =>
        intro hu
        rw [List.map_cons, List.sum_cons, map_add, LinearMap.add_apply, map_smul,
          LinearMap.smul_apply, hu u (List.mem_cons_self ..), smul_zero, zero_add]
        exact ihu fun v hv => hu v (List.mem_cons_of_mem _ hv)
    have horth := hsum ws fun u hu => hws u (List.mem_cons_of_mem _ hu) w (List.mem_cons_self ..)
    rw [map_add, LinearMap.add_apply, horth, add_zero, List.map_cons, List.sum_cons]
    abel

theorem prod_tau_lag : ((lagLabels.map bitVec).map fun w => tau w).prod = 1 := by
  have horth : ∀ w ∈ lagLabels.map bitVec, ∀ w' ∈ lagLabels.map bitVec, b0 w w' = 0 := by
    intro w hw w' hw'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hw'
    rw [b0_apply]
    exact lag_orthogonal u hu u' hu'
  apply Units.ext
  apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
  intro j
  rw [Pi.basisFun_apply, prod_tau_apply _ horth (Pi.single j 1)]
  simp only [b0_apply]
  rw [lag_sum_basis j, add_zero]
  rfl

section Lifts

variable {E : Type*} [Group E] {ρ : E →* LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2)}
  (hρ : ρ.range = bilinIsometryGroup b0)

include hρ in
theorem tau_mem_range (a : Fin 6 → ZMod 2) : tau a ∈ ρ.range := by
  rw [hρ]
  exact BinarySymplecticTransvection.transvection_mem_bilinIsometryGroup b0_isAlt a

noncomputable def liftT (a : Fin 6 → ZMod 2) : E :=
  (MonoidHom.mem_range.mp (tau_mem_range hρ a)).choose

theorem map_liftT (a : Fin 6 → ZMod 2) : ρ (liftT hρ a) = tau a :=
  (MonoidHom.mem_range.mp (tau_mem_range hρ a)).choose_spec

theorem liftT_sq_mem (a : Fin 6 → ZMod 2) : liftT hρ a ^ 2 ∈ ρ.ker := by
  rw [MonoidHom.mem_ker, map_pow, map_liftT, pow_two, BinarySymplecticTransvection.mul_self]

theorem map_conj_liftT (a c : Fin 6 → ZMod 2) :
    ρ (liftT hρ c * liftT hρ a * (liftT hρ c)⁻¹) = tau (a + b0 a c • c) := by
  rw [map_mul, map_mul, map_inv, map_liftT, map_liftT, BinarySymplecticTransvection.inv_eq,
    BinarySymplecticTransvection.mul_mul_self]

theorem tau_comm_of_orth {a b : Fin 6 → ZMod 2} (hab : b0 a b = 0) :
    tau a * tau b = tau b * tau a := by
  have h := BinarySymplecticTransvection.mul_mul_self b0_isAlt b a
  rw [b0_symm a b, hab, zero_smul, add_zero] at h
  calc tau a * tau b = tau a * tau b * (tau a * tau a) := by
        rw [BinarySymplecticTransvection.mul_self, mul_one]
    _ = tau b * tau a := by rw [← mul_assoc, h]

variable (hC : ρ.ker ≤ center E) (h2 : ∀ c ∈ ρ.ker, c ^ 2 = 1)

include hC h2 in
theorem liftT_sq_add {a b : Fin 6 → ZMod 2} (hab : b0 a b = 1) :
    liftT hρ (a + b) ^ 2 = liftT hρ a ^ 2 := by
  have h := map_conj_liftT hρ a b
  rw [hab, one_smul, ← map_liftT hρ (a + b)] at h
  rw [sq_eq_of_map_eq ρ hC h2 h, conj_pow,
    ← comm_of_mem_center hC (liftT_sq_mem hρ a) (liftT hρ b), mul_inv_cancel_right]

include hC h2 in
theorem liftT_sq_eq {a a' : Fin 6 → ZMod 2} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    liftT hρ a ^ 2 = liftT hρ a' ^ 2 := by
  obtain ⟨w, hw, hw'⟩ := CFSG.ClassicalGroups.Alternating.alternating_common_nonorthogonal_vector
    b0_isAlt b0_nondegenerate ha ha'
  have h1 : b0 a w = 1 := (BinarySymplecticTransvection.zmod_two_cases _).resolve_left hw
  have h1' : b0 a' w = 1 := (BinarySymplecticTransvection.zmod_two_cases _).resolve_left hw'
  have e1 := liftT_sq_add hρ hC h2 h1
  have e2 := liftT_sq_add hρ hC h2 ((b0_symm a w).trans h1)
  have e1' := liftT_sq_add hρ hC h2 h1'
  have e2' := liftT_sq_add hρ hC h2 ((b0_symm a' w).trans h1')
  rw [← e1, add_comm, e2, ← e2', add_comm, e1']

theorem commutatorElement_liftT_mem {a b : Fin 6 → ZMod 2} (hab : b0 a b = 0) :
    ⁅liftT hρ a, liftT hρ b⁆ ∈ ρ.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement, map_liftT, map_liftT,
    commutatorElement_eq_one_iff_mul_comm]
  exact tau_comm_of_orth hab

include hC in
theorem commutatorElement_liftT_conj {a b : Fin 6 → ZMod 2} (hab : b0 a b = 0)
    (c : Fin 6 → ZMod 2) :
    ⁅liftT hρ (a + b0 a c • c), liftT hρ (b + b0 b c • c)⁆ = ⁅liftT hρ a, liftT hρ b⁆ := by
  have hx := map_conj_liftT hρ a c
  have hy := map_conj_liftT hρ b c
  rw [← map_liftT hρ (a + b0 a c • c)] at hx
  rw [← map_liftT hρ (b + b0 b c • c)] at hy
  rw [commutatorElement_eq_of_map_eq ρ hC hx hy]
  have h := map_commutatorElement (MulAut.conj (liftT hρ c)) (liftT hρ a) (liftT hρ b)
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply] at h
  rw [← h, ← comm_of_mem_center hC (commutatorElement_liftT_mem hρ hab) (liftT hρ c),
    mul_inv_cancel_right]

include h2 in
theorem commutatorElement_liftT_swap {a b : Fin 6 → ZMod 2} (hab : b0 a b = 0) :
    ⁅liftT hρ b, liftT hρ a⁆ = ⁅liftT hρ a, liftT hρ b⁆ := by
  rw [← commutatorElement_inv]
  have hm := commutatorElement_liftT_mem hρ hab
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, h2 _ hm])

include hC h2 in
theorem commutatorElement_pairsReached : ∀ p ∈ pairsReached,
    pairing (bitVec p.1) (bitVec p.2) = 0 ∧
      ⁅liftT hρ (bitVec p.1), liftT hρ (bitVec p.2)⁆ =
        ⁅liftT hρ (bitVec 2), liftT hρ (bitVec 8)⁆ := by
  refine forall_of_pairChainOK (fun a b => pairing (bitVec a) (bitVec b) = 0 ∧
      ⁅liftT hρ (bitVec a), liftT hρ (bitVec b)⁆ = ⁅liftT hρ (bitVec 2), liftT hρ (bitVec 8)⁆)
    ?_ ?_ pairSteps [(2, 8)] ?_ pairChainOK_pairSteps
  · rintro a b ⟨h0, h1⟩
    have hab : b0 (bitVec a) (bitVec b) = 0 := by rw [b0_apply]; exact h0
    refine ⟨?_, ?_⟩
    · rw [← b0_apply, b0_symm]
      exact hab
    · rw [commutatorElement_liftT_swap hρ h2 hab]
      exact h1
  · rintro a b c ⟨h0, h1⟩
    have hab : b0 (bitVec a) (bitVec b) = 0 := by rw [b0_apply]; exact h0
    have hiso := BinarySymplecticTransvection.transvection_mem_bilinIsometryGroup b0_isAlt
      (bitVec c) (bitVec a) (bitVec b)
    rw [binarySymplecticTransvection_apply, binarySymplecticTransvection_apply] at hiso
    refine ⟨?_, ?_⟩
    · rw [← b0_apply, bitVec_tauL, bitVec_tauL, hiso]
      exact hab
    · rw [bitVec_tauL, bitVec_tauL, commutatorElement_liftT_conj hρ hC hab]
      exact h1
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact ⟨by decide, rfl⟩

include hC h2 in
theorem liftT_sq_eq_commutatorElement :
    liftT hρ (bitVec 2) ^ 2 = ⁅liftT hρ (bitVec 2), liftT hρ (bitVec 8)⁆ := by
  have hkapC : ⁅liftT hρ (bitVec 2), liftT hρ (bitVec 8)⁆ ∈ ρ.ker :=
    commutatorElement_liftT_mem hρ (by rw [b0_apply]; decide)
  have hlamC := liftT_sq_mem hρ (bitVec 2)
  set ys := lagLabels.map fun w => liftT hρ (bitVec w) with hys
  have hsq : ∀ y ∈ ys, y ^ 2 = liftT hρ (bitVec 2) ^ 2 := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
    exact liftT_sq_eq hρ hC h2 (lag_ne_zero w hw) (by decide)
  have hpw : ys.Pairwise (fun y y' => ⁅y, y'⁆ = ⁅liftT hρ (bitVec 2), liftT hρ (bitVec 8)⁆) := by
    rw [hys, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ lagLabels_nodup
    intro w w' hw hw' hne
    rcases lag_reached w hw w' hw' hne with h | h
    · exact (commutatorElement_pairsReached hρ hC h2 _ h).2
    · have h' := commutatorElement_pairsReached hρ hC h2 _ h
      rw [commutatorElement_liftT_swap hρ h2 (a := bitVec w') (b := bitVec w)
        (by rw [b0_apply]; exact h'.1)]
      exact h'.2
  have hprod := sq_list_prod (comm_of_mem_center hC hkapC) (h2 _ hkapC) ys hsq hpw
  have hmem : ys.prod ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_list_prod, hys, List.map_map]
    have : (ρ ∘ fun w => liftT hρ (bitVec w)) = (fun w => tau w) ∘ bitVec := by
      funext w
      exact map_liftT hρ (bitVec w)
    rw [this, ← List.map_map, prod_tau_lag]
  rw [h2 _ hmem, hys, List.length_map] at hprod
  have hl7 : lagLabels.length = 7 := rfl
  rw [hl7, show Nat.choose 7 2 = 1 + 2 * 10 by decide, pow_add, pow_mul, h2 _ hkapC, one_pow,
    mul_one, pow_one, show 7 = 1 + 2 * 3 by rfl, pow_add, pow_mul, h2 _ hlamC, one_pow,
    mul_one, pow_one] at hprod
  exact (eq_inv_of_mul_eq_one_left hprod.symm).trans
    (inv_eq_of_mul_eq_one_right (by rw [← pow_two, h2 _ hkapC]))

end Lifts

section Bound

variable {E : Type*} [Group E] {ρ : E →* LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2)}
  (hρ : ρ.range = bilinIsometryGroup b0) (hC : ρ.ker ≤ center E) (h2 : ∀ c ∈ ρ.ker, c ^ 2 = 1)

noncomputable def cubeL (i j : Fin 7) : E :=
  (liftT hρ (vE i) * liftT hρ (vE j)) ^ 3

theorem cubeL_mem {i j : Fin 7} (hij : s(i, j) ∈ e7Edges) : cubeL hρ i j ∈ ρ.ker := by
  rw [MonoidHom.mem_ker, cubeL, map_pow, map_mul, map_liftT, map_liftT]
  exact isW7Family_tau.2.1 i j hij

noncomputable def corr : Fin 7 → E :=
  ![1, cubeL hρ 0 1 * 1, cubeL hρ 1 2 * (cubeL hρ 0 1 * 1),
    cubeL hρ 2 3 * (cubeL hρ 1 2 * (cubeL hρ 0 1 * 1)), cubeL hρ 0 4 * 1,
    cubeL hρ 4 5 * (cubeL hρ 0 4 * 1), cubeL hρ 0 6 * 1]

theorem corr_mem (i : Fin 7) : corr hρ i ∈ ρ.ker := by
  have h01 := cubeL_mem hρ (i := 0) (j := 1) (by decide)
  have h12 := cubeL_mem hρ (i := 1) (j := 2) (by decide)
  have h23 := cubeL_mem hρ (i := 2) (j := 3) (by decide)
  have h04 := cubeL_mem hρ (i := 0) (j := 4) (by decide)
  have h45 := cubeL_mem hρ (i := 4) (j := 5) (by decide)
  have h06 := cubeL_mem hρ (i := 0) (j := 6) (by decide)
  have h1 : (1 : E) ∈ ρ.ker := one_mem _
  fin_cases i
  · exact h1
  · exact mul_mem h01 h1
  · exact mul_mem h12 (mul_mem h01 h1)
  · exact mul_mem h23 (mul_mem h12 (mul_mem h01 h1))
  · exact mul_mem h04 h1
  · exact mul_mem h45 (mul_mem h04 h1)
  · exact mul_mem h06 h1

noncomputable def genL (i : Fin 7) : E :=
  liftT hρ (vE i) * corr hρ i

theorem map_genL (i : Fin 7) : ρ (genL hρ i) = tau (vE i) := by
  rw [genL, map_mul, map_liftT, corr_mem hρ i, mul_one]

include hC h2 in
theorem genL_sq (i : Fin 7) : genL hρ i ^ 2 = liftT hρ (bitVec 2) ^ 2 := by
  rw [genL, sq_mul_of_mem hC (corr_mem hρ i) (h2 _ (corr_mem hρ i))]
  exact liftT_sq_eq hρ hC h2 (vE_ne_zero i) (by decide)

include hC h2 in
theorem genL_cube {p j : Fin 7} (hpj : s(p, j) ∈ e7Edges)
    (hc : corr hρ j = cubeL hρ p j * corr hρ p) : (genL hρ p * genL hρ j) ^ 3 = 1 := by
  have hu := cubeL_mem hρ hpj
  have hv := corr_mem hρ p
  have hcu := comm_of_mem_center hC hu
  have hcv := comm_of_mem_center hC hv
  have hvv : corr hρ p * corr hρ p = 1 := by rw [← pow_two, h2 _ hv]
  have hw : corr hρ p * (cubeL hρ p j * corr hρ p) = cubeL hρ p j := by
    rw [← mul_assoc, hcv (cubeL hρ p j), mul_assoc, hvv, mul_one]
  rw [genL, genL, hc, mul_mul_mul_of_central hcv (fun g => by
      rw [mul_assoc, hcv g, ← mul_assoc, hcu g, mul_assoc]), hw,
    (Commute.mul_pow (comm_of_mem_center hC hu _).symm 3), ← cubeL, ← pow_succ',
    show 3 + 1 = 2 * 2 by rfl, pow_mul, h2 _ hu, one_pow]

include hC h2 in
theorem genL_rels :
    (∀ i, genL hρ i ^ 2 = liftT hρ (bitVec 2) ^ 2) ∧
      (∀ i j, s(i, j) ∈ e7Edges → (genL hρ i * genL hρ j) ^ 3 = 1) ∧
      ∀ i k, i ≠ k → s(i, k) ∉ e7Edges →
        (genL hρ i * genL hρ k) ^ 2 = liftT hρ (bitVec 2) ^ 2 := by
  have hlamC := liftT_sq_mem hρ (bitVec 2)
  refine ⟨genL_sq hρ hC h2, fun i j hij => ?_, fun i k hne hik => ?_⟩
  · have hedge : ∀ i j : Fin 7, s(i, j) ∈ e7Edges →
        (i, j) ∈ [(0, 1), (1, 2), (2, 3), (0, 4), (4, 5), (0, 6)] ∨
          (j, i) ∈ [(0, 1), (1, 2), (2, 3), (0, 4), (4, 5), (0, 6)] := by
      decide
    have hcube : ∀ p j : Fin 7, (p, j) ∈ [(0, 1), (1, 2), (2, 3), (0, 4), (4, 5), (0, 6)] →
        (genL hρ p * genL hρ j) ^ 3 = 1 := by
      intro p j hpj
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hpj
      rcases hpj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ <;>
        exact genL_cube hρ hC h2 (by decide) rfl
    rcases hedge i j hij with h | h
    · exact hcube i j h
    · exact pow_three_swap (hcube j i h)
  · have hcomm := commutatorElement_mul_of_mem hC (corr_mem hρ i) (corr_mem hρ k)
      (x := liftT hρ (vE i)) (y := liftT hρ (vE k))
    rw [sq_mul_eq_commutatorElement (comm_of_mem_center hC hlamC) (h2 _ hlamC) (genL_sq hρ hC h2 i)
      (genL_sq hρ hC h2 k), genL, genL, hcomm, labels_vE, labels_vE,
      liftT_sq_eq_commutatorElement hρ hC h2]
    rcases nonEdge_reached i k hne hik with h | h
    · exact (commutatorElement_pairsReached hρ hC h2 _ h).2
    · have h' := commutatorElement_pairsReached hρ hC h2 _ h
      rw [commutatorElement_liftT_swap hρ h2 (by rw [b0_apply]; exact h'.1)]
      exact h'.2

end Bound

end SixCoverTwoKernel

end CFSG.LocalAnalysis.ComponentInitial
