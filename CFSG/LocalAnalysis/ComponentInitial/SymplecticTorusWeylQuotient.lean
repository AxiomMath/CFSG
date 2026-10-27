module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylLift
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.CentralExt

section Generation

variable {r : ℕ}

@[expose] def plane : Fin r ⊕ Fin r → Fin r := Sum.elim id id

theorem plane_swap (x : Fin r ⊕ Fin r) : plane x.swap = plane x := by
  rcases x with x | x <;> rfl

theorem eq_or_eq_swap_of_plane_eq {x y : Fin r ⊕ Fin r} (h : plane x = plane y) :
    x = y ∨ x = y.swap := by
  rcases x with x | x <;> rcases y with y | y <;> simp_all [plane]

theorem sumCongr_mem_signedPermGroup (τ : Equiv.Perm (Fin r)) :
    Equiv.sumCongr τ τ ∈ signedPermGroup r := by
  rintro (x | x) <;> rfl

theorem swap_inl_inr_mem_signedPermGroup (i : Fin r) :
    Equiv.swap (Sum.inl i) (Sum.inr i) ∈ signedPermGroup r := by
  rintro (x | x)
  · by_cases hx : x = i
    · subst hx
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
    · have h1 : (Sum.inl x : Fin r ⊕ Fin r) ≠ Sum.inl i := fun h => hx (Sum.inl_injective h)
      have h2 : (Sum.inr x : Fin r ⊕ Fin r) ≠ Sum.inr i := fun h => hx (Sum.inr_injective h)
      rw [Sum.swap_inl, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl h2,
        Equiv.swap_apply_of_ne_of_ne h1 Sum.inl_ne_inr, Sum.swap_inl]
  · by_cases hx : x = i
    · subst hx
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
    · have h1 : (Sum.inl x : Fin r ⊕ Fin r) ≠ Sum.inl i := fun h => hx (Sum.inl_injective h)
      have h2 : (Sum.inr x : Fin r ⊕ Fin r) ≠ Sum.inr i := fun h => hx (Sum.inr_injective h)
      rw [Sum.swap_inr, Equiv.swap_apply_of_ne_of_ne h1 Sum.inl_ne_inr,
        Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl h2, Sum.swap_inr]

theorem mem_of_plane_eq {K : Subgroup (Equiv.Perm (Fin r ⊕ Fin r))}
    (hsign : ∀ i : Fin r, Equiv.swap (Sum.inl i) (Sum.inr i) ∈ K) (S : Finset (Fin r)) :
    ∀ σ : Equiv.Perm (Fin r ⊕ Fin r), σ ∈ signedPermGroup r → (∀ x, plane (σ x) = plane x) →
      (∀ i, σ (Sum.inl i) = Sum.inr i → i ∈ S) → σ ∈ K := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro σ hσ hpl hS
    have hl : ∀ i, σ (Sum.inl i) = Sum.inl i := by
      intro i
      rcases eq_or_eq_swap_of_plane_eq (hpl (Sum.inl i)) with h | h
      · exact h
      · exact absurd (hS i h) (Finset.notMem_empty i)
    have : σ = 1 := by
      ext1 x
      rcases x with x | x
      · exact hl x
      · have := hσ (Sum.inl x)
        rw [hl, Sum.swap_inl] at this
        exact this
    rw [this]
    exact K.one_mem
  | insert a S ha ih =>
    intro σ hσ hpl hS
    set c := Equiv.swap (Sum.inl a) (Sum.inr a) with hc
    have hfix : ∀ x, plane x ≠ a → c x = x := by
      intro x hx
      apply Equiv.swap_apply_of_ne_of_ne <;> rintro rfl <;> exact hx rfl
    by_cases hσa : σ (Sum.inl a) = Sum.inr a
    · have hσ' : c * σ ∈ signedPermGroup r := mul_mem (swap_inl_inr_mem_signedPermGroup a) hσ
      have hpl' : ∀ x, plane ((c * σ) x) = plane x := by
        intro x
        rw [Equiv.Perm.mul_apply]
        by_cases hx : plane (σ x) = a
        · rcases eq_or_eq_swap_of_plane_eq (show plane (σ x) = plane (Sum.inl a) from hx) with
            h | h
          · rw [h, hc, Equiv.swap_apply_left, ← hpl x, h]
            rfl
          · rw [h, hc]
            simp only [Sum.swap_inl, Equiv.swap_apply_right]
            rw [← hpl x, h]
            rfl
        · rw [hfix _ hx]
          exact hpl x
      have hS' : ∀ i, (c * σ) (Sum.inl i) = Sum.inr i → i ∈ S := by
        intro i hi
        rw [Equiv.Perm.mul_apply] at hi
        by_cases hia : i = a
        · subst hia
          rw [hσa, hc, Equiv.swap_apply_right] at hi
          exact absurd hi Sum.inl_ne_inr
        · have hpi : plane (σ (Sum.inl i)) = i := hpl (Sum.inl i)
          rw [hfix _ (by rw [hpi]; exact hia)] at hi
          exact (Finset.mem_insert.1 (hS i hi)).resolve_left hia
      have hmem := ih (c * σ) hσ' hpl' hS'
      have : σ = c * (c * σ) := by rw [← mul_assoc, hc, Equiv.swap_mul_self, one_mul]
      rw [this]
      exact mul_mem (hsign a) hmem
    · refine ih σ hσ hpl fun i hi => ?_
      have hia : i ≠ a := by
        rintro rfl
        exact hσa hi
      exact (Finset.mem_insert.1 (hS i hi)).resolve_left hia

theorem signedPermGroup_le {K : Subgroup (Equiv.Perm (Fin r ⊕ Fin r))}
    (hsign : ∀ i : Fin r, Equiv.swap (Sum.inl i) (Sum.inr i) ∈ K)
    (hswap : ∀ (i : Fin r) (h : i.val + 1 < r),
      Equiv.sumCongr (Equiv.swap i ⟨i.val + 1, h⟩) (Equiv.swap i ⟨i.val + 1, h⟩) ∈ K) :
    signedPermGroup r ≤ K := by
  have hlev : ∀ τ : Equiv.Perm (Fin r), Equiv.sumCongr τ τ ∈ K := by
    cases r with
    | zero =>
      intro τ
      have : τ = 1 := Equiv.ext fun x => x.elim0
      have h1 : Equiv.sumCongr (1 : Equiv.Perm (Fin 0)) (1 : Equiv.Perm (Fin 0)) = 1 :=
        Equiv.Perm.sumCongr_one
      rw [this, h1]
      exact K.one_mem
    | succ n =>
      intro τ
      have hτ : τ ∈ Submonoid.closure
          (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        trivial
      induction hτ using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        have h := hswap i.castSucc (by simp)
        have hs : (⟨i.castSucc.val + 1, by simp⟩ : Fin (n + 1)) = i.succ := Fin.ext (by simp)
        rwa [hs] at h
      | one =>
        have h1 : Equiv.sumCongr (1 : Equiv.Perm (Fin (n + 1)))
            (1 : Equiv.Perm (Fin (n + 1))) = 1 :=
          Equiv.Perm.sumCongr_one
        rw [h1]
        exact K.one_mem
      | mul x y _ _ hx hy =>
        have h1 : Equiv.sumCongr (x * y) (x * y) = Equiv.sumCongr x x * Equiv.sumCongr y y :=
          (Equiv.Perm.sumCongr_mul x x y y).symm
        rw [h1]
        exact mul_mem hx hy
  intro σ hσ
  have hinj : Function.Injective fun i => plane (σ (Sum.inl i)) := by
    intro i j hij
    rcases eq_or_eq_swap_of_plane_eq hij with h | h
    · exact Sum.inl_injective (σ.injective h)
    · rw [← hσ (Sum.inl j), Sum.swap_inl] at h
      exact absurd (σ.injective h) Sum.inl_ne_inr
  set τ := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj) with hτ
  have hplτ : ∀ (ρ : Equiv.Perm (Fin r)) y, plane (Equiv.sumCongr ρ ρ y) = ρ (plane y) := by
    intro ρ y
    rcases y with y | y <;> rfl
  set σ' := (Equiv.sumCongr τ τ)⁻¹ * σ with hσ'def
  have hσ' : σ' ∈ signedPermGroup r :=
    mul_mem (inv_mem (sumCongr_mem_signedPermGroup τ)) hσ
  have hl : ∀ i, plane (σ' (Sum.inl i)) = i := by
    intro i
    rw [hσ'def, Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_inv, hplτ]
    have : τ i = plane (σ (Sum.inl i)) := rfl
    rw [← this]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  have hpl : ∀ x, plane (σ' x) = plane x := by
    rintro (x | x)
    · exact hl x
    · have := hσ' (Sum.inl x)
      rw [Sum.swap_inl] at this
      rw [this, plane_swap]
      exact hl x
  have hmem := mem_of_plane_eq hsign Finset.univ σ' hσ' hpl fun i _ => Finset.mem_univ i
  have : σ = Equiv.sumCongr τ τ * σ' := by rw [hσ'def, mul_inv_cancel_left]
  rw [this]
  exact mul_mem (hlev τ) hmem

end Generation

section EpsAct

variable {r : ℕ}

@[expose] def lineVal (e : Fin r → ℤ) : Fin r ⊕ Fin r → ℤ := Sum.elim e (-e)

@[expose] def epsAct (σ : Equiv.Perm (Fin r ⊕ Fin r)) (e : Fin r → ℤ) : Fin r → ℤ :=
  fun j => lineVal e (σ.symm (Sum.inl j))

theorem lineVal_swap (e : Fin r → ℤ) (x : Fin r ⊕ Fin r) : lineVal e x.swap = -lineVal e x := by
  rcases x with x | x <;> simp [lineVal]

theorem symm_apply_swap {σ : Equiv.Perm (Fin r ⊕ Fin r)} (hσ : σ ∈ signedPermGroup r)
    (x : Fin r ⊕ Fin r) : σ.symm x.swap = (σ.symm x).swap := by
  have h := inv_mem hσ x
  rwa [Equiv.Perm.inv_def] at h

theorem lineVal_epsAct {σ : Equiv.Perm (Fin r ⊕ Fin r)} (hσ : σ ∈ signedPermGroup r)
    (e : Fin r → ℤ) (x : Fin r ⊕ Fin r) : lineVal (epsAct σ e) x = lineVal e (σ.symm x) := by
  rcases x with x | x
  · rfl
  · change -(epsAct σ e x) = lineVal e (σ.symm (Sum.inl x).swap)
    rw [symm_apply_swap hσ, lineVal_swap]
    rfl

theorem epsAct_mul {σ τ : Equiv.Perm (Fin r ⊕ Fin r)} (hτ : τ ∈ signedPermGroup r)
    (e : Fin r → ℤ) : epsAct (σ * τ) e = epsAct σ (epsAct τ e) := by
  funext j
  change lineVal e (τ.symm (σ.symm (Sum.inl j))) = lineVal (epsAct τ e) (σ.symm (Sum.inl j))
  rw [lineVal_epsAct hτ]

theorem epsAct_one (e : Fin r → ℤ) : epsAct 1 e = e := rfl

theorem epsAct_sumCongr_swap (i j : Fin r) (e : Fin r → ℤ) :
    epsAct (Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j)) e = e ∘ Equiv.swap i j := by
  funext x
  simp [epsAct, lineVal, Equiv.sumCongr_symm, Equiv.symm_swap]

theorem epsAct_swap_inl_inr (i : Fin r) (e : Fin r → ℤ) :
    epsAct (Equiv.swap (Sum.inl i) (Sum.inr i)) e = fun a => (if a = i then -1 else 1) * e a := by
  funext a
  simp only [epsAct, Equiv.symm_swap]
  by_cases ha : a = i
  · subst ha
    simp [lineVal]
  · have h1 : (Sum.inl a : Fin r ⊕ Fin r) ≠ Sum.inl i := fun h => ha (Sum.inl_injective h)
    rw [Equiv.swap_apply_of_ne_of_ne h1 Sum.inl_ne_inr]
    simp [lineVal, ha]

end EpsAct

section GroupRel

variable {G : Type*} [Group G] {a b : G}

theorem pow_two_eq_one_of_commute (ha : a * a = 1) (hb : b * b = 1) (h : a * b = b * a) :
    (a * b) ^ 2 = 1 := by
  rw [sq, mul_assoc, ← mul_assoc b, ← h, mul_assoc, hb, mul_one, ha]

theorem pow_three_eq_one (ha : a * a = 1) (hb : b * b = 1) (h : b * a * b = a * b * a) :
    (a * b) ^ 3 = 1 := by
  have ha' : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have h' : ∀ x, b * (a * (b * x)) = a * (b * (a * x)) := fun x => by
    simpa only [mul_assoc] using congrArg (· * x) h
  calc (a * b) ^ 3 = a * (b * (a * (b * (a * b)))) := by simp only [pow_succ, pow_zero, one_mul,
        mul_assoc]
    _ = a * (a * (b * (a * (a * b)))) := by rw [h']
    _ = 1 := by rw [ha', ha', hb]

theorem pow_four_eq_one (hb : b * b = 1) (hc : a * b * a * (a * b * a) = 1)
    (hcomm : a * b * a * b = b * (a * b * a)) : (a * b) ^ 4 = 1 := by
  calc (a * b) ^ 4 = a * b * a * b * (a * b * a * b) := by simp only [pow_succ, pow_zero, one_mul,
        mul_assoc]
    _ = a * b * a * (b * (a * b * a)) * b := by simp only [mul_assoc]
    _ = a * b * a * (a * b * a) * (b * b) := by rw [← hcomm]; simp only [mul_assoc]
    _ = 1 := by rw [hc, hb, one_mul]

theorem pow_eq_one_comm {n : ℕ} (h : (a * b) ^ n = 1) : (b * a) ^ n = 1 := by
  have : b * a = a⁻¹ * (a * b) * a⁻¹⁻¹ := by group
  rw [this, conj_pow, h, mul_one, inv_inv, inv_mul_cancel]

end GroupRel

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E] [Finite k] [Finite E]
  {π : E →* StatedSp r k}

section Values

variable (hS : Hyp π)
include hS

theorem weylHom_sLift_of_lt {i : Fin r} (h : i.val + 1 < r) :
    (weylHom hS ⟨sLift π i, sLift_mem i⟩ : Equiv.Perm (Fin r ⊕ Fin r)) =
      Equiv.sumCongr (Equiv.swap i ⟨i.val + 1, h⟩) (Equiv.swap i ⟨i.val + 1, h⟩) := by
  apply weylHom_eq hS
  change IsLinePerm _ (((π (sLift π i) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
  rw [sLift_of_lt h, pi_vLiftRho hS]
  exact isLinePerm_rho_sl2W _

theorem weylHom_sLift_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) :
    (weylHom hS ⟨sLift π i, sLift_mem i⟩ : Equiv.Perm (Fin r ⊕ Fin r)) =
      Equiv.swap (Sum.inl i) (Sum.inr i) := by
  apply weylHom_eq hS
  change IsLinePerm _ (((π (sLift π i) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
  rw [sLift_of_not_lt h, pi_vLift hS]
  exact isLinePerm_lam_sl2W _

theorem weylHom_vLift (i : Fin r) :
    (weylHom hS ⟨vLift π i, vLift_mem hS i⟩ : Equiv.Perm (Fin r ⊕ Fin r)) =
      Equiv.swap (Sum.inl i) (Sum.inr i) := by
  apply weylHom_eq hS
  change IsLinePerm _ (((π (vLift π i) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
  rw [pi_vLift hS]
  exact isLinePerm_lam_sl2W _

theorem weylHom_eq_one_of_mem {n : liftWeyl π} (hn : (n : E) ∈ liftTorus π) :
    weylHom hS n = 1 := by
  obtain ⟨t, ht⟩ := (range_thetaHom hS).ge hn
  apply Subtype.ext
  refine weylHom_eq hS ?_
  change IsLinePerm 1 (((π n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
  rw [← ht, ← MonoidHom.comp_apply π, comp_thetaHom hS]
  exact isLinePerm_torusHom t

theorem liftTorus_le_ker_weylHom : (liftTorus π).subgroupOf (liftWeyl π) ≤ (weylHom hS).ker :=
  fun _ hn => weylHom_eq_one_of_mem hS (Subgroup.mem_subgroupOf.1 hn)

theorem weylHom_surjective : Function.Surjective (weylHom hS) := by
  rintro ⟨σ, hσ⟩
  have hle : signedPermGroup r ≤ (weylHom hS).range.map (signedPermGroup r).subtype :=
    signedPermGroup_le (fun i => ⟨_, ⟨⟨vLift π i, vLift_mem hS i⟩, rfl⟩, weylHom_vLift hS i⟩)
      (fun i h => ⟨_, ⟨⟨sLift π i, sLift_mem i⟩, rfl⟩, weylHom_sLift_of_lt hS h⟩)
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hle hσ
  exact ⟨n, Subtype.ext hn⟩

end Values

section Coxeter

variable (π) in
@[expose] noncomputable def sClass (i : Fin r) :
    liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π) :=
  QuotientGroup.mk ⟨sLift π i, sLift_mem i⟩

omit [Finite k] [Finite E] in
theorem qmk_congr {x y : E} (hx : x ∈ liftWeyl π) (hy : y ∈ liftWeyl π) (h : x = y) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) =
      QuotientGroup.mk ⟨y, hy⟩ := by
  subst h
  rfl

variable [((liftTorus π).subgroupOf (liftWeyl π)).Normal]

omit [Finite k] [Finite E] in
theorem qmk_mul {x y : E} (hx : x ∈ liftWeyl π) (hy : y ∈ liftWeyl π) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) *
      QuotientGroup.mk ⟨y, hy⟩ = QuotientGroup.mk ⟨x * y, mul_mem hx hy⟩ := rfl

omit [Finite k] [Finite E] in
theorem qmk_inv {x : E} (hx : x ∈ liftWeyl π) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π))⁻¹ =
      QuotientGroup.mk ⟨x⁻¹, inv_mem hx⟩ := rfl

omit [Finite k] [Finite E] in
theorem qmk_eq_one_iff {x : E} (hx : x ∈ liftWeyl π) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) = 1 ↔
      x ∈ liftTorus π := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

variable (hS : Hyp π)
include hS

theorem sClass_mul_self (i : Fin r) : sClass π i * sClass π i = 1 := by
  rw [sClass, qmk_mul, qmk_eq_one_iff]
  by_cases h : i.val + 1 < r
  · rw [sLift_of_lt h, vLiftRho_mul_self]
    exact hLiftRho_mem hS _ _
  · rw [sLift_of_not_lt h, vLift_mul_self]
    exact hLift_mem _ _

theorem sClass_braid {i j : Fin r} (hij : i.val + 1 = j.val) (hj : j.val + 1 < r) :
    sClass π j * sClass π i * sClass π j = sClass π i * sClass π j * sClass π i := by
  have hi : i.val + 1 < r := by omega
  simp only [sClass, qmk_mul]
  apply qmk_congr
  obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hij.symm
  rw [sLift_of_lt hi, sLift_of_lt hj]
  exact vLiftRho_braid hS _ _ (Fin.ne_of_val_ne (by simp only; omega))

theorem sClass_comm {i j : Fin r} (hij : i.val + 1 < j.val) :
    sClass π i * sClass π j = sClass π j * sClass π i := by
  have hi : i.val + 1 < r := by omega
  simp only [sClass, qmk_mul]
  apply qmk_congr
  rw [sLift_of_lt hi]
  by_cases hj : j.val + 1 < r
  · rw [sLift_of_lt hj]
    exact (commute_vLiftRho_vLiftRho hS _ _ (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by simp only; omega)) (Fin.ne_of_val_ne (by simp only; omega))
      (Fin.ne_of_val_ne (by simp only; omega))).eq
  · rw [sLift_of_not_lt hj]
    exact (commute_vLiftRho_vLift hS _ (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by simp only; omega))).eq

theorem sClass_long {i j : Fin r} (hij : i.val + 1 = j.val) (hj : ¬j.val + 1 < r) :
    sClass π i * sClass π j * sClass π i * (sClass π i * sClass π j * sClass π i) = 1 ∧
      sClass π i * sClass π j * sClass π i * sClass π j =
        sClass π j * (sClass π i * sClass π j * sClass π i) := by
  have hi : i.val + 1 < r := by omega
  have hinv : (sClass π i)⁻¹ = sClass π i := inv_eq_of_mul_eq_one_right (sClass_mul_self hS i)
  have hv : sClass π i * sClass π j * sClass π i =
      (QuotientGroup.mk ⟨vLift π i, vLift_mem hS i⟩ :
        liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) := by
    have h3 : sClass π i * sClass π j * sClass π i =
        sClass π i * sClass π j * (sClass π i)⁻¹ := by rw [hinv]
    rw [h3]
    simp only [sClass, qmk_mul, qmk_inv]
    apply qmk_congr
    obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hij.symm
    rw [sLift_of_lt hi, sLift_of_not_lt hj]
    exact vLiftRho_conj_vLift hS _
  rw [hv]
  constructor
  · rw [qmk_mul, qmk_eq_one_iff, vLift_mul_self]
    exact hLift_mem _ _
  · simp only [sClass, qmk_mul]
    apply qmk_congr
    rw [sLift_of_not_lt hj]
    exact (commute_vLift_vLift hS (Fin.ne_of_val_ne (by omega))).eq

private theorem isLiftable_sClass :
    (CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r)).IsLiftable (sClass π) := by
  have key : ∀ i j : Fin r, i < j → (sClass π i * sClass π j) ^
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r)) i j = 1 := by
    intro i j hij
    have hij' : i.val < j.val := hij
    by_cases hadj : i.val + 1 = j.val
    · by_cases hj : j.val + 1 < r
      · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_succ_short r hadj hj]
        exact pow_three_eq_one (sClass_mul_self hS i) (sClass_mul_self hS j)
          (sClass_braid hS hadj hj)
      · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_succ_long r hadj hj]
        exact pow_four_eq_one (sClass_mul_self hS j) (sClass_long hS hadj hj).1
          (sClass_long hS hadj hj).2
    · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_far r hij.ne hadj (by omega)]
      exact pow_two_eq_one_of_commute (sClass_mul_self hS i) (sClass_mul_self hS j)
        (sClass_comm hS (by omega))
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · exact key i j h
  · rw [CoxeterMatrix.diagonal, pow_one]
    exact sClass_mul_self hS i
  · rw [CoxeterMatrix.symmetric]
    exact pow_eq_one_comm (key j i h)

end Coxeter

section Kernel

variable (hS : Hyp π)
include hS

theorem normal_liftTorus_subgroupOf : ((liftTorus π).subgroupOf (liftWeyl π)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer liftTorus_le_liftWeyl).2 (liftWeyl_le_normalizer hS)

theorem ker_weylHom_le : (weylHom hS).ker ≤ (liftTorus π).subgroupOf (liftWeyl π) := by
  have := normal_liftTorus_subgroupOf hS
  set hA := CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r
  set cs := (CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem
  set L := cs.lift ⟨sClass π, isLiftable_sClass hS⟩ with hL
  set φbar := QuotientGroup.lift _ (weylHom hS) (liftTorus_le_ker_weylHom hS) with hφbar
  have hsimple : ∀ i, epsAct ((φbar (L (cs.simple i)) : signedPermGroup r) :
      Equiv.Perm (Fin r ⊕ Fin r)) = CFSG.LieType.Universal.Symplectic.stdRefl r i := by
    intro i
    rw [hL, CoxeterSystem.lift_apply_simple, sClass, hφbar, QuotientGroup.lift_mk]
    funext e
    by_cases h : i.val + 1 < r
    · rw [weylHom_sLift_of_lt hS h, epsAct_sumCongr_swap,
        CFSG.LieType.Universal.Symplectic.stdRefl_of_lt r h]
    · rw [weylHom_sLift_of_not_lt hS h, epsAct_swap_inl_inr,
        CFSG.LieType.Universal.Symplectic.stdRefl_of_not_lt r h]
  have hact : ∀ w v, CFSG.LieType.Universal.Symplectic.toStd r
      (CFSG.LieType.RootSystem.weylAction hA w v) =
        epsAct (φbar (L w) : Equiv.Perm (Fin r ⊕ Fin r))
          (CFSG.LieType.Universal.Symplectic.toStd r v) := by
    intro w
    refine cs.simple_induction_left (p := fun w => ∀ v,
      CFSG.LieType.Universal.Symplectic.toStd r (CFSG.LieType.RootSystem.weylAction hA w v) =
        epsAct (φbar (L w) : Equiv.Perm (Fin r ⊕ Fin r))
          (CFSG.LieType.Universal.Symplectic.toStd r v)) w ?_ ?_
    · intro v
      rw [map_one, map_one, map_one]
      rfl
    · intro w i ih v
      rw [CFSG.LieType.RootSystem.weylAction_mul_apply,
        CFSG.LieType.RootSystem.weylAction_simple,
        CFSG.LieType.Universal.Symplectic.toStd_reflection, ih, map_mul, map_mul,
        Subgroup.coe_mul, epsAct_mul (φbar (L w)).2, hsimple]
  have hinj : ∀ w, φbar (L w) = 1 → w = 1 := by
    intro w hw
    apply CFSG.LieType.RootSystem.weylAction_injective hA
    rw [map_one]
    refine LinearMap.ext fun v => CFSG.LieType.Universal.Symplectic.toStd_injective r ?_
    rw [hact, hw, Module.End.one_apply]
    rfl
  have hsurj : Function.Surjective L := by
    have key : ∀ x (hx : x ∈ liftWeyl π),
        (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) ∈
          L.range := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | ⟨i, rfl⟩
        · exact ⟨1, by rw [map_one]; exact ((qmk_eq_one_iff _).2 hx).symm⟩
        · exact ⟨cs.simple i, CoxeterSystem.lift_apply_simple _ _ i⟩
      | one => exact L.range.one_mem
      | mul x y hx hy ihx ihy =>
        exact mul_mem ihx ihy
      | inv x hx ihx =>
        exact inv_mem ihx
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    exact key x hx
  intro n hn
  obtain ⟨w, hw⟩ := hsurj (QuotientGroup.mk n)
  have h1 : φbar (L w) = 1 := by
    rw [hw, hφbar, QuotientGroup.lift_mk]
    exact hn
  rw [hinj w h1, map_one] at hw
  exact (QuotientGroup.eq_one_iff n).1 hw.symm

theorem ker_weylHom : (weylHom hS).ker = (liftTorus π).subgroupOf (liftWeyl π) :=
  le_antisymm (ker_weylHom_le hS) (liftTorus_le_ker_weylHom hS)

theorem injective_pi_comp : Function.Injective (π.comp (liftWeyl π).subtype) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have hn' : π n = 1 := hn
  have hw : weylHom hS n = 1 := by
    apply Subtype.ext
    refine weylHom_eq hS ?_
    change IsLinePerm 1 (((π n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
    rw [hn']
    exact isLinePerm_one
  have hH : (n : E) ∈ liftTorus π := Subgroup.mem_subgroupOf.1 (ker_weylHom_le hS hw)
  obtain ⟨t, ht⟩ := (range_thetaHom hS).ge hH
  have h1 : torusHom t = 1 := by
    rw [← comp_thetaHom hS, MonoidHom.comp_apply, ht]
    exact hn'
  have ht1 : t = 1 := torusHom_injective (h1.trans (map_one _).symm)
  apply Subtype.ext
  rw [← ht, ht1, map_one]
  rfl

end Kernel

end CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
