module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Sylow
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups commutatorElement

section Roots

@[expose] def nodeZero : Fin (3 - 1) := ⟨0, by decide⟩

theorem nodeZero_ne_nodeOne : nodeZero ≠ finOne := by decide

@[expose] def epsVec (a b : ℤ) : Fin (3 - 1) → ℤ := Pi.single nodeZero a + Pi.single finOne b

@[expose] def rootOf (a b : ℤ) : Fin (3 - 1) → ℤ := ofStdB (3 - 1) (epsVec a b)

theorem toStdB_rootOf (a b : ℤ) : toStdB (3 - 1) (rootOf a b) = epsVec a b :=
  toStdB_ofStdB _ _

theorem epsVec_zero (a b : ℤ) : epsVec a b nodeZero = a := by
  simp [epsVec, nodeZero, finOne]

theorem epsVec_one (a b : ℤ) : epsVec a b finOne = b := by
  simp [epsVec, nodeZero, finOne]

theorem fin_two_cases (x : Fin (3 - 1)) : x = nodeZero ∨ x = finOne := by
  rcases x with ⟨k, hk⟩
  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem eq_epsVec (e : Fin (3 - 1) → ℤ) : e = epsVec (e nodeZero) (e finOne) := by
  funext x
  rcases fin_two_cases x with rfl | rfl
  · rw [epsVec_zero]
  · rw [epsVec_one]

theorem epsVec_add (a b a' b' : ℤ) : epsVec a b + epsVec a' b' = epsVec (a + a') (b + b') := by
  funext x
  rcases fin_two_cases x with rfl | rfl <;> simp [epsVec_zero, epsVec_one]

theorem epsVec_nsmul (k : ℕ) (a b : ℤ) : k • epsVec a b = epsVec (k * a) (k * b) := by
  funext x
  rcases fin_two_cases x with rfl | rfl <;> simp [epsVec_zero, epsVec_one]

theorem epsVec_inj {a b a' b' : ℤ} (h : epsVec a b = epsVec a' b') : a = a' ∧ b = b' := by
  have h0 := congrFun h nodeZero
  have h1 := congrFun h finOne
  rw [epsVec_zero, epsVec_zero] at h0
  rw [epsVec_one, epsVec_one] at h1
  exact ⟨h0, h1⟩

theorem sum_fin_two (f : Fin (3 - 1) → ℤ) : ∑ i, f i = f nodeZero + f finOne :=
  Fintype.sum_eq_add nodeZero finOne nodeZero_ne_nodeOne fun x hx =>
    absurd (fin_two_cases x) (by tauto)

theorem rootOf_zero (a b : ℤ) : rootOf a b nodeZero = a := by
  simp only [rootOf, ofStdB]
  rw [sum_fin_two]
  have h1 : (finOne : Fin (3 - 1)).val = 1 := rfl
  have h0 : (nodeZero : Fin (3 - 1)).val = 0 := rfl
  simp [h1, h0, epsVec_zero]

theorem rootOf_one (a b : ℤ) : rootOf a b finOne = a + b := by
  simp only [rootOf, ofStdB]
  rw [sum_fin_two]
  have h1 : (finOne : Fin (3 - 1)).val = 1 := rfl
  have h0 : (nodeZero : Fin (3 - 1)).val = 0 := rfl
  simp [h1, h0, epsVec_zero, epsVec_one]

theorem ht_rootOf (a b : ℤ) : ht (rootOf a b) = 2 * a + b := by
  change ∑ j, rootOf a b j = _
  rw [sum_fin_two, rootOf_zero, rootOf_one]
  ring

theorem rootOf_inj {a b a' b' : ℤ} (h : rootOf a b = rootOf a' b') : a = a' ∧ b = b' := by
  have h' := congrArg (toStdB (3 - 1)) h
  rw [toStdB_rootOf, toStdB_rootOf] at h'
  exact epsVec_inj h'

theorem eq_rootOf (γ : Fin (3 - 1) → ℤ) :
    γ = rootOf (toStdB (3 - 1) γ nodeZero) (toStdB (3 - 1) γ finOne) := by
  rw [rootOf, ← eq_epsVec, ofStdB_toStdB]

theorem exists_rootOf_of_mem_roots {γ : Fin (3 - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (3 - 1)) ∅) :
    ∃ a b : ℤ, γ = rootOf a b ∧ (a = 0 ∨ a = 1 ∨ a = -1) ∧ (b = 0 ∨ b = 1 ∨ b = -1) ∧
      (a = 1 ∨ a = -1 ∨ b = 1 ∨ b = -1) := by
  refine ⟨_, _, eq_rootOf γ, toStdB_apply_mem_of_mem_roots 3 hγ _,
    toStdB_apply_mem_of_mem_roots 3 hγ _, ?_⟩
  obtain ⟨x, hx⟩ := exists_toStdB_apply_ne_zero 3 hγ
  rcases fin_two_cases x with rfl | rfl
  · rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hx with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem toStdB_nsmul (k : ℕ) (v : Fin (3 - 1) → ℤ) :
    toStdB (3 - 1) (k • v) = k • toStdB (3 - 1) v := by
  induction k with
  | zero => simp [toStdB_zero]
  | succ k ih => rw [succ_nsmul, toStdB_add, ih, succ_nsmul]

theorem rootOf_cone (k l : ℕ) (a b a' b' : ℤ) :
    k • rootOf a b + l • rootOf a' b' = rootOf (k * a + l * a') (k * b + l * b') := by
  apply toStdB_injective (3 - 1)
  rw [toStdB_add, toStdB_nsmul, toStdB_nsmul, toStdB_rootOf, toStdB_rootOf, toStdB_rootOf,
    epsVec_nsmul, epsVec_nsmul, epsVec_add]

theorem first_coord_of_mem_openCone {a b a' b' : ℤ}
    {ε : Fin (3 - 1) → ℤ}
    (hε : ε ∈ openCone (roots (isFiniteType_cartanB (3 - 1)) ∅) (rootOf a b) (rootOf a' b')) :
    ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ b'' : ℤ, ε = rootOf (k * a + l * a') b'' ∧
      (k * a + l * a' = 0 ∨ k * a + l * a' = 1 ∨ k * a + l * a' = -1) ∧
      (b'' = 0 ∨ b'' = 1 ∨ b'' = -1) := by
  obtain ⟨hεr, k, l, hk, hl, hε'⟩ := hε
  rw [rootOf_cone] at hε'
  refine ⟨k, l, hk, hl, _, hε', ?_⟩
  obtain ⟨x, y, hxy, hx, hy, -⟩ := exists_rootOf_of_mem_roots hεr
  rw [hε'] at hxy
  obtain ⟨h1, h2⟩ := rootOf_inj hxy
  rw [h1, h2]
  exact ⟨hx, hy⟩

theorem linIndepPair_rootOf {a b a' b' : ℤ} (h : a * b' - a' * b ≠ 0) :
    LinIndepPair (rootOf a b) (rootOf a' b') := by
  intro k l hkl
  have h0 := congrFun hkl nodeZero
  have h1 := congrFun hkl finOne
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, rootOf_zero,
    rootOf_one] at h0 h1
  have e1 : k * (a * b' - a' * b) = 0 := by linear_combination b' * h0 - a' * h1 + a' * h0
  have e2 : l * (a * b' - a' * b) = 0 := by linear_combination a * h1 - b * h0 - a * h0
  exact ⟨(mul_eq_zero.1 e1).resolve_right h, (mul_eq_zero.1 e2).resolve_right h⟩

end Roots

theorem mul_comm_sup {G : Type*} [Group G] {A B : Subgroup G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have h1 : ∀ x ∈ A ⊔ B, (∀ a ∈ A, a * x = x * a) → (∀ a ∈ B, a * x = x * a) →
      ∀ y ∈ A ⊔ B, y * x = x * y := by
    intro x _ hxA hxB y hy
    have : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := sup_le
      (fun a ha => by rw [Subgroup.mem_centralizer_singleton_iff]; exact hxA a ha)
      (fun a ha => by rw [Subgroup.mem_centralizer_singleton_iff]; exact hxB a ha)
    have := Subgroup.mem_centralizer_singleton_iff.1 (this hy)
    exact this
  have hC : A ⊔ B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      refine h1 a (Subgroup.mem_sup_left ha) (fun a' ha' => (hA a' ha' a ha)) (fun a' ha' => ?_) y hy
      exact (hAB a ha a' ha').symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      refine h1 a (Subgroup.mem_sup_right ha) (fun a' ha' => ?_) (fun a' ha' => hB a' ha' a ha) y hy
      exact hAB a' ha' a ha
  intro x hx y hy
  have := Subgroup.mem_centralizer_iff.1 (hC hx) y hy
  exact this.symm

section Groups

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

variable (b c) in
@[expose] noncomputable def qA : Multiplicative F →* spinGroup (quadMinus 3 F b c) :=
  (minusFrame 3 b c).longRoot nodeZero_ne_nodeOne true false

variable (b c) in
@[expose] noncomputable def qC : Multiplicative F →* spinGroup (quadMinus 3 F b c) :=
  (minusFrame 3 b c).longRoot nodeZero_ne_nodeOne true true

@[expose] noncomputable def qB : Multiplicative (Fin 2 → F) →* spinGroup (quadMinus 3 F b c) :=
  twShortRoot 3 hirr nodeZero true

@[expose] noncomputable def nN : Multiplicative (Fin 2 → F) →* spinGroup (quadMinus 3 F b c) :=
  twShortRoot 3 hirr finOne true

theorem rg_one_neg : minusRootGroup 3 hirr (rootOf 1 (-1)) = (qA b c).range :=
  minusRootGroup_eq_long 3 hirr nodeZero_ne_nodeOne true false
    (by rw [toStdB_rootOf]; simp [epsVec])

theorem rg_one_one : minusRootGroup 3 hirr (rootOf 1 1) = (qC b c).range :=
  minusRootGroup_eq_long 3 hirr nodeZero_ne_nodeOne true true
    (by rw [toStdB_rootOf]; simp [epsVec])

theorem rg_one_zero : minusRootGroup 3 hirr (rootOf 1 0) = (qB hirr).range :=
  minusRootGroup_eq_short 3 hirr nodeZero true (by rw [toStdB_rootOf]; simp [epsVec])

theorem rg_zero_one : minusRootGroup 3 hirr (rootOf 0 1) = (nN hirr).range :=
  minusRootGroup_eq_short 3 hirr finOne true (by rw [toStdB_rootOf]; simp [epsVec])

theorem rootOf_mem_roots_long (s t : Bool) :
    rootOf (boolSign s) (boolSign t) ∈ roots (isFiniteType_cartanB (3 - 1)) ∅ :=
  mem_roots_of_toStdB_eq_long 3 nodeZero_ne_nodeOne s t (by rw [toStdB_rootOf]; rfl)

theorem rootOf_one_neg_mem_roots : rootOf 1 (-1) ∈ roots (isFiniteType_cartanB (3 - 1)) ∅ :=
  rootOf_mem_roots_long true false

theorem rootOf_one_one_mem_roots : rootOf 1 1 ∈ roots (isFiniteType_cartanB (3 - 1)) ∅ :=
  rootOf_mem_roots_long true true

theorem rootOf_one_zero_mem_roots : rootOf 1 0 ∈ roots (isFiniteType_cartanB (3 - 1)) ∅ :=
  mem_roots_of_toStdB_eq_short 3 nodeZero true (by rw [toStdB_rootOf]; simp [epsVec])

theorem rootOf_zero_one_mem_roots : rootOf 0 1 ∈ roots (isFiniteType_cartanB (3 - 1)) ∅ :=
  mem_roots_of_toStdB_eq_short 3 finOne true (by rw [toStdB_rootOf]; simp [epsVec])

theorem commutator_rg_eq_one {a b' a' b'' : ℤ}
    (hγ : rootOf a b' ∈ roots (isFiniteType_cartanB (3 - 1)) ∅)
    (hδ : rootOf a' b'' ∈ roots (isFiniteType_cartanB (3 - 1)) ∅)
    (hdet : a * b'' - a' * b' ≠ 0)
    (hcone : ∀ k l : ℕ, 0 < k → 0 < l →
      ¬ (k * a + l * a' = 0 ∨ k * a + l * a' = 1 ∨ k * a + l * a' = -1))
    {x y : spinGroup (quadMinus 3 F b c)} (hx : x ∈ minusRootGroup 3 hirr (rootOf a b'))
    (hy : y ∈ minusRootGroup 3 hirr (rootOf a' b'')) : ⁅x, y⁆ = 1 := by
  have h := minusDatum_commutator_mem 3 hirr _ hγ _ hδ (linIndepPair_rootOf hdet) x hx y hy
  have hbot : (⨆ ε ∈ openCone (roots (isFiniteType_cartanB (3 - 1)) ∅) (rootOf a b')
      (rootOf a' b''), minusRootGroup 3 hirr ε) = ⊥ := by
    refine eq_bot_iff.2 (iSup₂_le fun ε hε => ?_)
    obtain ⟨k, l, hk, hl, -, -, h3, -⟩ := first_coord_of_mem_openCone hε
    exact absurd h3 (hcone k l hk hl)
  rw [hbot, Subgroup.mem_bot] at h
  exact h

theorem commute_of_mem_range {G X : Type*} [CommGroup G] [Group X] (f : G →* X) {x y : X}
    (hx : x ∈ f.range) (hy : y ∈ f.range) : x * y = y * x := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

@[expose] noncomputable def Qsub : Subgroup (spinGroup (quadMinus 3 F b c)) :=
  (qA b c).range ⊔ (qB hirr).range ⊔ (qC b c).range

@[expose] noncomputable def Nsub : Subgroup (spinGroup (quadMinus 3 F b c)) := (nN hirr).range

theorem commute_qA_qB {x y : spinGroup (quadMinus 3 F b c)} (hx : x ∈ (qA b c).range)
    (hy : y ∈ (qB hirr).range) : x * y = y * x := by
  rw [← rg_one_neg hirr] at hx
  rw [← rg_one_zero hirr] at hy
  exact commutatorElement_eq_one_iff_mul_comm.1 (commutator_rg_eq_one hirr rootOf_one_neg_mem_roots
    rootOf_one_zero_mem_roots (by norm_num) (fun k l hk hl => by
      have : (0 : ℤ) < k := by exact_mod_cast hk
      have : (0 : ℤ) < l := by exact_mod_cast hl
      omega) hx hy)

include hirr in
theorem commute_qA_qC {x y : spinGroup (quadMinus 3 F b c)} (hx : x ∈ (qA b c).range)
    (hy : y ∈ (qC b c).range) : x * y = y * x := by
  rw [← rg_one_neg hirr] at hx
  rw [← rg_one_one hirr] at hy
  exact commutatorElement_eq_one_iff_mul_comm.1 (commutator_rg_eq_one hirr rootOf_one_neg_mem_roots
    rootOf_one_one_mem_roots (by norm_num) (fun k l hk hl => by
      have : (0 : ℤ) < k := by exact_mod_cast hk
      have : (0 : ℤ) < l := by exact_mod_cast hl
      omega) hx hy)

theorem commute_qB_qC {x y : spinGroup (quadMinus 3 F b c)} (hx : x ∈ (qB hirr).range)
    (hy : y ∈ (qC b c).range) : x * y = y * x := by
  rw [← rg_one_zero hirr] at hx
  rw [← rg_one_one hirr] at hy
  exact commutatorElement_eq_one_iff_mul_comm.1 (commutator_rg_eq_one hirr rootOf_one_zero_mem_roots
    rootOf_one_one_mem_roots (by norm_num) (fun k l hk hl => by
      have : (0 : ℤ) < k := by exact_mod_cast hk
      have : (0 : ℤ) < l := by exact_mod_cast hl
      omega) hx hy)

theorem Qsub_comm : ∀ x ∈ Qsub hirr, ∀ y ∈ Qsub hirr, x * y = y * x := by
  have hAB : ∀ x ∈ (qA b c).range ⊔ (qB hirr).range, ∀ y ∈ (qA b c).range ⊔ (qB hirr).range,
      x * y = y * x := mul_comm_sup (fun x hx y hy => commute_of_mem_range _ hx hy)
    (fun x hx y hy => commute_of_mem_range _ hx hy) (fun x hx y hy => commute_qA_qB hirr hx hy)
  refine mul_comm_sup hAB (fun x hx y hy => commute_of_mem_range _ hx hy) ?_
  intro x hx y hy
  have hx' : ∀ y ∈ (qC b c).range, x * y = y * x := by
    intro y hy
    have : (qA b c).range ⊔ (qB hirr).range ≤ Subgroup.centralizer ({y} : Set _) := sup_le
      (fun a ha => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact commute_qA_qC hirr ha hy)
      (fun a ha => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact commute_qB_qC hirr ha hy)
    have := Subgroup.mem_centralizer_singleton_iff.1 (this hx)
    exact this
  exact hx' y hy

theorem Nsub_comm : ∀ x ∈ Nsub hirr, ∀ y ∈ Nsub hirr, x * y = y * x :=
  fun _ hx _ hy => commute_of_mem_range _ hx hy

theorem rg_le_Qsub {b'' : ℤ} (h : b'' = -1 ∨ b'' = 0 ∨ b'' = 1) :
    minusRootGroup 3 hirr (rootOf 1 b'') ≤ Qsub hirr := by
  rcases h with rfl | rfl | rfl
  · rw [rg_one_neg]
    exact le_sup_left.trans le_sup_left
  · rw [rg_one_zero]
    exact le_sup_right.trans le_sup_left
  · rw [rg_one_one]
    exact le_sup_right

theorem Nsub_conj_Qsub {n q : spinGroup (quadMinus 3 F b c)} (hn : n ∈ Nsub hirr)
    (hq : q ∈ Qsub hirr) : n * q * n⁻¹ ∈ Qsub hirr := by
  have hn' : n ∈ minusRootGroup 3 hirr (rootOf 0 1) := by rw [rg_zero_one]; exact hn
  have hgen : ∀ {b₂ : ℤ}, (b₂ = -1 ∨ b₂ = 0 ∨ b₂ = 1) →
      minusRootGroup 3 hirr (rootOf 1 b₂) ≤ (Qsub hirr).comap (MulAut.conj n).toMonoidHom := by
    intro b₂ hb₂ x hx
    have hγ : rootOf 1 b₂ ∈ roots (isFiniteType_cartanB (3 - 1)) ∅ := by
      rcases hb₂ with rfl | rfl | rfl
      · exact rootOf_one_neg_mem_roots
      · exact rootOf_one_zero_mem_roots
      · exact rootOf_one_one_mem_roots
    have hc := minusDatum_commutator_mem 3 hirr _ rootOf_zero_one_mem_roots _ hγ
      (linIndepPair_rootOf (a := 0) (b := 1) (a' := 1) (b' := b₂) (by norm_num)) n hn' x hx
    have hle : (⨆ ε ∈ openCone (roots (isFiniteType_cartanB (3 - 1)) ∅) (rootOf 0 1)
        (rootOf 1 b₂), minusRootGroup 3 hirr ε) ≤ Qsub hirr := by
      refine iSup₂_le fun ε hε => ?_
      obtain ⟨k, l, hk, hl, b'', rfl, h1, h2⟩ := first_coord_of_mem_openCone hε
      have hl1 : (l : ℤ) = 1 := by
        have : (0 : ℤ) < l := by exact_mod_cast hl
        omega
      have : ((k : ℤ) * 0 + (l : ℤ) * 1) = 1 := by omega
      rw [this]
      exact rg_le_Qsub hirr (by omega)
    have h3 : ⁅n, x⁆ * x ∈ Qsub hirr :=
      (Qsub hirr).mul_mem (hle hc) (rg_le_Qsub hirr hb₂ hx)
    rw [commutatorElement_def, inv_mul_cancel_right] at h3
    exact h3
  have hQ : Qsub hirr ≤ (Qsub hirr).comap (MulAut.conj n).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [← rg_one_neg hirr]
      exact hgen (Or.inl rfl)
    · rw [← rg_one_zero hirr]
      exact hgen (Or.inr (Or.inl rfl))
    · rw [← rg_one_one hirr]
      exact hgen (Or.inr (Or.inr rfl))
  exact hQ hq

theorem posUnipotent_eq : posUnipotent (minusDatum 3 hirr) = Qsub hirr ⊔ Nsub hirr := by
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨a, b', rfl, ha, hb, hne⟩ := exists_rootOf_of_mem_roots hγ.1
    have hpos : 0 < 2 * a + b' := by
      rw [← ht_rootOf]
      exact hγ.2
    rcases ha with rfl | rfl | rfl
    · have h1 : b' = 1 := by omega
      subst h1
      have : (minusDatum 3 hirr).rootGroup (rootOf 0 1) = Nsub hirr := rg_zero_one hirr
      rw [this]
      exact le_sup_right
    · exact (rg_le_Qsub hirr (by omega)).trans le_sup_left
    · omega
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · rw [← rg_one_neg hirr]
      exact rootGroup_le_posUnipotent (D := minusDatum 3 hirr) rootOf_one_neg_mem_roots
        (lt_of_lt_of_eq (by norm_num) (ht_rootOf _ _).symm)
    · rw [← rg_one_zero hirr]
      exact rootGroup_le_posUnipotent (D := minusDatum 3 hirr) rootOf_one_zero_mem_roots
        (lt_of_lt_of_eq (by norm_num) (ht_rootOf _ _).symm)
    · rw [← rg_one_one hirr]
      exact rootGroup_le_posUnipotent (D := minusDatum 3 hirr) rootOf_one_one_mem_roots
        (lt_of_lt_of_eq (by norm_num) (ht_rootOf _ _).symm)
    · rw [Nsub, ← rg_zero_one hirr]
      exact rootGroup_le_posUnipotent (D := minusDatum 3 hirr) rootOf_zero_one_mem_roots
        (lt_of_lt_of_eq (by norm_num) (ht_rootOf _ _).symm)

theorem torus_pow_eq_one [Finite F] (i : Fin (3 - 1)) {g : spinGroup (quadMinus 3 F b c)}
    (hg : g ∈ minusTorus 3 hirr i) :
    g ^ (Nat.card Fˣ * Nat.card (ShortField b c)ˣ) = 1 := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  rcases fin_two_cases i with rfl | rfl
  · have hk : (nodeZero : Fin (3 - 1)).val + 1 < 3 - 1 := by decide
    rw [minusTorus_of_lt 3 hirr hk] at hg
    obtain ⟨τ, rfl⟩ := hg
    rw [← map_pow]
    have : τ ^ (Nat.card Fˣ * Nat.card (ShortField b c)ˣ) = 1 :=
      (orderOf_dvd_iff_pow_eq_one.1 (dvd_trans (orderOf_dvd_natCard τ) (dvd_mul_right _ _)))
    rw [this, map_one]
  · have hk : ¬ (finOne : Fin (3 - 1)).val + 1 < 3 - 1 := by decide
    rw [minusTorus_of_not_lt 3 hirr hk] at hg
    obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff 3 hirr finOne).1 hg
    obtain ⟨t, rfl⟩ := exists_fieldCoord_eq (b := b) (c := c) a
    have ht : t ≠ 0 := fun h => ha (by rw [h]; ext k; fin_cases k <;> rfl)
    have := shortBlock_torus hirr 3 finOne (Units.mk0 t ht)
    simp only [Units.val_mk0] at this
    rw [← this, ← map_pow, ← map_pow]
    have h1 : (Units.mk0 t ht) ^ (Nat.card Fˣ * Nat.card (ShortField b c)ˣ) = 1 :=
      (orderOf_dvd_iff_pow_eq_one.1 (dvd_trans (orderOf_dvd_natCard (Units.mk0 t ht))
        (dvd_mul_left _ _)))
    rw [h1, map_one, map_one]

theorem coprime_pred {p m : ℕ} [hp : Fact p.Prime] (hpm : p ∣ m) (hm : 1 ≤ m) :
    Nat.Coprime p (m - 1) := by
  refine (Nat.Prime.coprime_iff_not_dvd hp.out).2 fun h => ?_
  have := Nat.dvd_sub hpm h
  rw [show m - (m - 1) = 1 by omega] at this
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)

theorem card_shortField_eq : Nat.card (ShortField b c) = Nat.card F * Nat.card F := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod]

variable [Finite F]

include hirr in
theorem finite_spinGroup_minus (n : ℕ) : Finite (spinGroup (quadMinus n F b c)) :=
  finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)

theorem isPGroup_Usub {p : ℕ} [CharP F p] : IsPGroup p ↥(Qsub hirr ⊔ Nsub hirr) := by
  rw [← posUnipotent_eq hirr]
  exact isPGroup_iSup_pos (minusDatum_steinbergExtras 3 hirr)
    (fun γ hγ => isPGroup_minusRootGroup hirr hγ)

theorem not_dvd_index_Usub {p f : ℕ} [hp : Fact p.Prime] [CharP F p] (hF : Nat.card F = p ^ f)
    (hf : 1 ≤ f) (h2 : (2 : F) ≠ 0) : ¬ p ∣ (Qsub hirr ⊔ Nsub hirr).index := by
  have := finite_spinGroup_minus hirr 3
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have hq : p ∣ Nat.card F := by rw [hF]; exact dvd_pow_self p (by omega)
  have hq1 : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.2 Finite.card_pos.ne'
  have hE : Nat.card (ShortField b c) = Nat.card F * Nat.card F := card_shortField_eq
  have hMp : Nat.Coprime p (Nat.card Fˣ * Nat.card (ShortField b c)ˣ) := by
    rw [Nat.card_units, Nat.card_units]
    refine Nat.Coprime.mul_right (coprime_pred hq hq1) (coprime_pred ?_ ?_)
    · rw [hE]; exact Dvd.dvd.mul_right hq _
    · rw [hE]; exact Nat.mul_pos (Nat.pos_of_ne_zero (by omega)) (Nat.pos_of_ne_zero (by omega))
  rw [← posUnipotent_eq hirr]
  exact not_dvd_index_posUnipotent (minusDatum_isCTGroupDatum_three hirr h2)
    (minusDatum_steinbergExtras 3 hirr) (fun γ hγ => isPGroup_minusRootGroup hirr hγ) hMp
    (fun i g hg => torus_pow_eq_one hirr i hg)

end Groups

end CFSG.ClassicalInvolution.WeakCT
