module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaLemmaADefs
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Six

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA

open Matrix Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
  CFSG.LocalAnalysis.EvenBN.Tits.Model

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem crd_parrottV_mem_hatE {i : ℕ} (h8 : 8 ≤ i) (h12 : i ≤ 12) : parrottV i ∈ hatE := by
  rw [hatE_eq_parrottU_eight]
  exact subset_closure ⟨i, ⟨h8, h12⟩, rfl⟩

theorem crd_parrottV_mem_titsD {i : ℕ} (h8 : 8 ≤ i) (h12 : i ≤ 12) : parrottV i ∈ titsD :=
  titsJ_le_titsD (hatE_le_titsJ (crd_parrottV_mem_hatE h8 h12))

theorem crd_pv_mem_E {i : ℕ} (h8 : 8 ≤ i) (h12 : i ≤ 12) : d.pv i ∈ d.E :=
  Data.mem_liftSub.2 ⟨parrottV i, crd_parrottV_mem_hatE h8 h12, crd_parrottV_mem_titsD h8 h12, rfl⟩

theorem crd_basisV_bounds (j : Fin 5) : 8 ≤ basisV j ∧ basisV j ≤ 12 := by
  have := j.isLt
  unfold basisV
  omega

theorem crd_basis_mem_E (j : Fin 5) : d.pv (basisV j) ∈ d.E :=
  crd_pv_mem_E (crd_basisV_bounds j).1 (crd_basisV_bounds j).2

theorem crd_basis_sq (hd : d.Hyp) (j : Fin 5) : d.pv (basisV j) * d.pv (basisV j) = 1 :=
  hd.s56_E_sq (crd_basis_mem_E j)

theorem crd_basis_comm (hd : d.Hyp) (i j : Fin 5) :
    Commute (d.pv (basisV i)) (d.pv (basisV j)) :=
  hd.s56_E_comm (crd_basis_mem_E i) (crd_basis_mem_E j)

theorem crd_val_one : (1 : ZMod 2).val = 1 := rfl

theorem crd_pv12 : d.pv 12 = d.z := by
  rw [Data.pv, parrottV_twelve, Data.lift_titsZ]

theorem crd_pow_val_add {x : G} (hx : x * x = 1) (u v : ZMod 2) :
    x ^ (u + v).val = x ^ u.val * x ^ v.val := by
  have key : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  rcases key u with rfl | rfl <;> rcases key v with rfl | rfl <;>
    simp [h11, hx, crd_val_one]

theorem crd_ofFn_prod_add {n : ℕ} (b : Fin n → G) (hc : ∀ i j, Commute (b i) (b j))
    (hs : ∀ i, b i * b i = 1) (a a' : Fin n → ZMod 2) :
    (List.ofFn fun j => b j ^ (a j + a' j).val).prod =
      (List.ofFn fun j => b j ^ (a j).val).prod * (List.ofFn fun j => b j ^ (a' j).val).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (fun i => b i.succ) (fun i j => hc _ _) (fun i => hs _) (fun i => a i.succ)
      (fun i => a' i.succ)
    have hcomm : Commute (b 0 ^ (a' 0).val)
        (List.ofFn fun i : Fin n => b i.succ ^ (a i.succ).val).prod :=
      Commute.list_prod_right _ _ fun y hy => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
        exact (hc 0 j.succ).pow_pow _ _
    simp only [List.ofFn_succ, List.prod_cons]
    rw [h, crd_pow_val_add (hs 0)]
    exact hcomm.mul_mul_mul_comm _ _

@[expose] noncomputable def crdE (d : Data G) (c : Fin 5 → ZMod 2) : G :=
  d.pv 12 ^ (c 0).val * d.pv 11 ^ (c 1).val * d.pv 10 ^ (c 2).val * d.pv 9 ^ (c 3).val *
    d.pv 8 ^ (c 4).val

theorem crd_eq_ofFn (c : Fin 5 → ZMod 2) :
    crdE d c = (List.ofFn fun j : Fin 5 => d.pv (basisV j) ^ (c j).val).prod := by
  simp [crdE, basisV, List.ofFn_succ, mul_assoc]

theorem crdE_mem (hd : d.Hyp) (c : Fin 5 → ZMod 2) : crdE d c ∈ d.E := by
  have hz : d.pv 12 ∈ d.E := by
    rw [crd_pv12]
    exact hd.s56_z_mem_E
  have hv : ∀ i, 8 ≤ i → i ≤ 12 → ∀ n : ℕ, d.pv i ^ n ∈ d.E := fun i h8 h12 n =>
    pow_mem (crd_pv_mem_E h8 h12) n
  exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem hz _) (hv 11 (by norm_num) (by norm_num) _))
    (hv 10 (by norm_num) (by norm_num) _)) (hv 9 (by norm_num) (by norm_num) _))
    (hv 8 (by norm_num) (by norm_num) _)

theorem crdE_zero : crdE d 0 = 1 := by
  simp [crdE]

theorem crdE_single (j : Fin 5) : crdE d (Pi.single j 1) = d.pv (basisV j) := by
  fin_cases j <;> simp [crdE, basisV, crd_val_one]

theorem crdE_mul (hd : d.Hyp) (c c' : Fin 5 → ZMod 2) :
    crdE d c * crdE d c' = crdE d (c + c') := by
  rw [crd_eq_ofFn, crd_eq_ofFn, crd_eq_ofFn]
  exact (crd_ofFn_prod_add (fun j => d.pv (basisV j)) (crd_basis_comm hd) (crd_basis_sq hd)
    c c').symm

theorem crd_mul_self (hd : d.Hyp) (c : Fin 5 → ZMod 2) : crdE d c * crdE d c = 1 := by
  rw [crdE_mul hd, show c + c = 0 by ext j; exact CharTwo.add_self_eq_zero (c j), crdE_zero]

theorem exists_crdE (hd : d.Hyp) {u : G} (hu : u ∈ d.E) : ∃ c, crdE d c = u := by
  obtain ⟨x, hx, hxD, rfl⟩ := Data.mem_liftSub.1 hu
  have hx' : x ∈ parrottU 8 := by rwa [hatE_eq_parrottU_eight] at hx
  have key : x ∈ titsD ∧ ∃ c, crdE d c = d.lift x := by
    refine Subgroup.closure_induction (p := fun x _ => x ∈ titsD ∧ ∃ c, crdE d c = d.lift x)
      ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨i, hi, rfl⟩
      refine ⟨crd_parrottV_mem_titsD hi.1 hi.2, ?_⟩
      obtain rfl | rfl | rfl | rfl | rfl : i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by
        have := hi.1
        have := hi.2
        omega
      · exact ⟨Pi.single 4 1, crdE_single 4⟩
      · exact ⟨Pi.single 3 1, crdE_single 3⟩
      · exact ⟨Pi.single 2 1, crdE_single 2⟩
      · exact ⟨Pi.single 1 1, crdE_single 1⟩
      · exact ⟨Pi.single 0 1, crdE_single 0⟩
    · exact ⟨one_mem _, 0, by rw [d.lift_one]; exact crdE_zero⟩
    · rintro x y _ _ ⟨hxD, c, hc⟩ ⟨hyD, c', hc'⟩
      exact ⟨mul_mem hxD hyD, c + c', by rw [← crdE_mul hd, hc, hc', d.lift_mul hxD hyD]⟩
    · rintro x _ ⟨hxD, c, hc⟩
      refine ⟨inv_mem hxD, c, ?_⟩
      rw [d.lift_inv hxD, ← hc]
      exact (inv_eq_of_mul_eq_one_right (crd_mul_self hd c)).symm
  exact key.2

theorem crdE_injective (hd : d.Hyp) : Function.Injective (crdE d) := by
  have hsurj : Function.Surjective fun c : Fin 5 → ZMod 2 =>
      (⟨crdE d c, crdE_mem hd c⟩ : d.E) := by
    rintro ⟨u, hu⟩
    obtain ⟨c, rfl⟩ := exists_crdE hd hu
    exact ⟨c, rfl⟩
  have hcard : Nat.card (Fin 5 → ZMod 2) ≤ Nat.card d.E := by
    rw [hd.A_facts.1]
    simp
  intro c c' h
  exact (hsurj.bijective_of_nat_card_le hcard).1 (Subtype.ext h)

@[expose] noncomputable def ecoord (d : Data G) (u : G) : Fin 5 → ZMod 2 :=
  open Classical in if h : ∃ c, crdE d c = u then h.choose else 0

theorem crdE_ecoord (hd : d.Hyp) {u : G} (hu : u ∈ d.E) : crdE d (ecoord d u) = u := by
  have h := exists_crdE hd hu
  unfold ecoord
  rw [dite_eq_left h]
  exact h.choose_spec

theorem ecoord_crdE (hd : d.Hyp) (c : Fin 5 → ZMod 2) : ecoord d (crdE d c) = c := by
  have h : ∃ c', crdE d c' = crdE d c := ⟨c, rfl⟩
  unfold ecoord
  rw [dite_eq_left h]
  exact crdE_injective hd h.choose_spec

theorem ecoord_mul (hd : d.Hyp) {u u' : G} (hu : u ∈ d.E) (hu' : u' ∈ d.E) :
    ecoord d (u * u') = ecoord d u + ecoord d u' := by
  have h3 : u * u' = crdE d (ecoord d u + ecoord d u') := by
    rw [← crdE_mul hd, crdE_ecoord hd hu, crdE_ecoord hd hu']
  rw [h3, ecoord_crdE hd]

theorem ecoord_inv (hd : d.Hyp) {u : G} (hu : u ∈ d.E) : ecoord d u⁻¹ = ecoord d u := by
  rw [inv_eq_of_mul_eq_one_right (hd.s56_E_sq hu)]

theorem ecoord_one (hd : d.Hyp) : ecoord d 1 = 0 := by
  have h := ecoord_crdE hd (0 : Fin 5 → ZMod 2)
  rwa [crdE_zero] at h

@[expose] noncomputable def wcoord (d : Data G) (u : G) : W4 := fun i => ecoord d u i.succ

theorem wcoord_mul (hd : d.Hyp) {u u' : G} (hu : u ∈ d.E) (hu' : u' ∈ d.E) :
    wcoord d (u * u') = wcoord d u + wcoord d u' := by
  funext i
  simp only [wcoord, ecoord_mul hd hu hu', Pi.add_apply]

theorem crd_z_eq : d.z = crdE d (Pi.single 0 1) := by
  rw [crdE_single 0, ← crd_pv12]
  rfl

theorem wcoord_eq_zero_iff (hd : d.Hyp) {u : G} (hu : u ∈ d.E) :
    wcoord d u = 0 ↔ u ∈ zpowers d.z := by
  constructor
  · intro h
    have hc0 : ∀ j : Fin 5, j ≠ 0 → ecoord d u j = 0 := by
      intro j hj
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hj
      exact congrFun h i
    have hcc : ecoord d u = Pi.single 0 (ecoord d u 0) := by
      ext j
      by_cases hj : j = 0
      · subst hj
        simp
      · rw [hc0 j hj, Pi.single_eq_of_ne hj]
    rw [← crdE_ecoord hd hu, hcc]
    have : crdE d (Pi.single 0 (ecoord d u 0)) = d.z ^ (ecoord d u 0).val := by
      rw [← crd_pv12]
      simp [crdE]
    rw [this]
    exact pow_mem (mem_zpowers _) _
  · intro h
    rcases hd.s56_mem_zpowers_z h with rfl | rfl
    · funext i
      simp [wcoord, ecoord_one hd]
    · funext i
      simp [wcoord, crd_z_eq, ecoord_crdE hd]

theorem wcoord_surj (hd : d.Hyp) (a : W4) : ∃ u ∈ d.E, wcoord d u = a := by
  refine ⟨crdE d (Fin.cons 0 a), crdE_mem hd _, ?_⟩
  funext i
  simp [wcoord, ecoord_crdE hd]

theorem wcoord_crdE (hd : d.Hyp) (c : Fin 5 → ZMod 2) :
    wcoord d (crdE d c) = fun i => c i.succ := by
  funext i
  simp only [wcoord, ecoord_crdE hd]

theorem crd_conj_crdE (hd : d.Hyp) {g : G} (A : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hA : ∀ j : Fin 5, g * d.pv (basisV j) * g⁻¹ = crdE d (fun i => A i j))
    (c : Fin 5 → ZMod 2) : g * crdE d c * g⁻¹ = crdE d (A *ᵥ c) := by
  have key : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  have hadd : ∀ w w' : Fin 5 → ZMod 2, g * crdE d w * g⁻¹ = crdE d (A *ᵥ w) →
      g * crdE d w' * g⁻¹ = crdE d (A *ᵥ w') →
      g * crdE d (w + w') * g⁻¹ = crdE d (A *ᵥ (w + w')) := by
    intro w w' hw hw'
    rw [← crdE_mul hd, Matrix.mulVec_add, ← crdE_mul hd, ← hw, ← hw']
    group
  have := Finset.sum_induction (s := Finset.univ)
    (fun i => (Pi.single i (c i) : Fin 5 → ZMod 2))
    (fun w => g * crdE d w * g⁻¹ = crdE d (A *ᵥ w)) hadd (by simp [crdE_zero])
    fun i _ => by
      rcases key (c i) with h0 | h1
      · simp [h0, crdE_zero]
      · rw [h1, Matrix.mulVec_single_one, crdE_single]
        exact hA i
  rwa [Finset.univ_sum_single] at this

theorem wcoord_conj (hd : d.Hyp) {g : G} (A : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hz : ∀ i, A i 0 = if i = 0 then 1 else 0)
    (hA : ∀ j : Fin 5, g * d.pv (basisV j) * g⁻¹ = crdE d (fun i => A i j)) {u : G} (hu : u ∈ d.E) :
    g * u * g⁻¹ ∈ d.E ∧
      wcoord d (g * u * g⁻¹) = (Matrix.of fun i j : Fin 4 => A i.succ j.succ) *ᵥ wcoord d u := by
  have hconj : g * u * g⁻¹ = crdE d (A *ᵥ ecoord d u) := by
    rw [← crd_conj_crdE hd A hA (ecoord d u), crdE_ecoord hd hu]
  refine ⟨by rw [hconj]; exact crdE_mem hd _, ?_⟩
  rw [hconj, wcoord_crdE hd]
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hz, wcoord, Fin.succ_ne_zero]

theorem crd_lift_prodE (c : Fin 5 → ZMod 2) : d.lift (prodE c) = crdE d c := by
  have hm : ∀ k, 8 ≤ k → k ≤ 12 → ∀ n : ℕ, parrottV k ^ n ∈ titsD := fun k h8 h12 n =>
    pow_mem (crd_parrottV_mem_titsD h8 h12) n
  have e : ∀ k, 8 ≤ k → k ≤ 12 → ∀ n : ℕ, d.lift (parrottV k ^ n) = d.pv k ^ n :=
    fun k h8 h12 n => d.lift_pow (crd_parrottV_mem_titsD h8 h12) n
  have h12 := hm 12 (by norm_num) le_rfl (c 0).val
  have h11 := hm 11 (by norm_num) (by norm_num) (c 1).val
  have h10 := hm 10 (by norm_num) (by norm_num) (c 2).val
  have h9 := hm 9 (by norm_num) (by norm_num) (c 3).val
  have h8 := hm 8 le_rfl (by norm_num) (c 4).val
  unfold prodE crdE
  rw [d.lift_mul (mul_mem (mul_mem (mul_mem h12 h11) h10) h9) h8,
    d.lift_mul (mul_mem (mul_mem h12 h11) h10) h9, d.lift_mul (mul_mem h12 h11) h10,
    d.lift_mul h12 h11, e 12 (by norm_num) le_rfl, e 11 (by norm_num) (by norm_num),
    e 10 (by norm_num) (by norm_num), e 9 (by norm_num) (by norm_num), e 8 le_rfl (by norm_num)]

theorem lift_action (hd : d.Hyp) {h : Equiv.Perm (Fin 1755)} (hhD : h ∈ titsD)
    (A : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hA : ∀ j : Fin 5, h * parrottV (basisV j) * h⁻¹ = prodE (fun i => A i j)) (j : Fin 5) :
    d.lift h * d.pv (basisV j) * (d.lift h)⁻¹ = crdE d (fun i => A i j) := by
  have _ := hd
  have hvD : parrottV (basisV j) ∈ titsD :=
    crd_parrottV_mem_titsD (crd_basisV_bounds j).1 (crd_basisV_bounds j).2
  rw [← crd_lift_prodE, ← hA j]
  exact (d.lift_conj hhD hvD).symm

end CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA
