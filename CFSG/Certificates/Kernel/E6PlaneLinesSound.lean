module

public import Certificates.Data.Kernel.E6PlaneLines
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc

public section

namespace CFSG.KC.E6PlaneLines

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint.Chevalley.RootCertificate
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6ShapeKernel
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

theorem pi_eq_sum_single' (v : Fin Tag.E6.rank → ℤ) :
    v = ∑ i, v i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

@[expose] def triH (b : Fin Tag.E6.rank → ZMod 3) : (Fin Tag.E6.rank → ℤ) →+ ZMod 3 where
  toFun := triPairing b
  map_zero' := triPairing_zero b
  map_add' := triPairing_add b

theorem triH_apply (b : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) :
    triH b v = triPairing b v := rfl

theorem triPairing_smul_eq_of_basis' {b b' : Fin Tag.E6.rank → ZMod 3}
    {w : WeylGroup Tag.E6}
    (h : ∀ i, triPairing b (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
      triPairing b' (Pi.single i 1)) (v : Fin Tag.E6.rank → ℤ) :
    triPairing b (w • v) = triPairing b' v := by
  conv_lhs => rw [pi_eq_sum_single' v, Finset.smul_sum]
  conv_rhs => rw [pi_eq_sum_single' v]
  rw [← triH_apply, ← triH_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, map_zsmul, map_zsmul, triH_apply, triH_apply, h i]

theorem pairZ_castL' {C : RootCertificate .E6} {k : ℕ} (hk : k < C.roots.length)
    (vec : List ℕ) :
    pairZ (RootTables.ofCert C) k (castL vec) =
      ∑ x : Fin Tag.E6.rank, C.root k x * ((vec.getD x 0 : ℕ) : ℤ) := by
  unfold pairZ castL dotL
  rw [vecs_getD C hk, sum_zipWith_ofFn_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [getD_map_natCast]

theorem pairZ_emod_eq_zero_iff' {C : RootCertificate .E6} {k : ℕ}
    (hk : k < C.roots.length) (vec : List ℕ) :
    pairZ (RootTables.ofCert C) k (castL vec) % 3 = 0 ↔
      triPairing (vec3 (τ := .E6) vec) (C.root k) = 0 := by
  have h2 : ((pairZ (RootTables.ofCert C) k (castL vec) : ℤ) : ZMod 3) =
      triPairing (vec3 (τ := .E6) vec) (C.root k) := by
    rw [pairZ_castL' hk, Int.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [vec3, Int.cast_mul, Int.cast_natCast]
    ring
  rw [← h2]
  constructor
  · intro h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast Int.dvd_of_emod_eq_zero h)
  · intro h
    exact Int.emod_eq_zero_of_dvd (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h)

theorem kernelCount_eq_ncard (a b : List ℕ) :
    kernelCount (RootTables.ofCert e6Certificate) a b =
      {γ | IsRoot .E6 γ ∧ triPairing (vec3 (τ := .E6) a) γ = 0 ∧
        triPairing (vec3 (τ := .E6) b) γ = 0}.ncard := by
  have hNodup : ((List.range e6Certificate.roots.length).map e6Certificate.root).Nodup := by
    have h := e6Certificate_checkNodup
    simp only [RootCertificate.checkNodup, decide_eq_true_eq] at h
    exact List.Nodup.of_map (fun v : Fin Tag.E6.rank → ℤ => List.ofFn v)
      (by rw [List.map_map]; exact h)
  have hinj : ∀ x ∈ List.range e6Certificate.roots.length,
      ∀ y ∈ List.range e6Certificate.roots.length,
      e6Certificate.root x = e6Certificate.root y → x = y :=
    (List.nodup_map_iff_inj_on List.nodup_range).1 hNodup
  let K : Finset ℕ := ((List.range e6Certificate.roots.length).filter fun k =>
    decide (pairZ (RootTables.ofCert e6Certificate) k (castL a) % 3 = 0) &&
    decide (pairZ (RootTables.ofCert e6Certificate) k (castL b) % 3 = 0)).toFinset
  have hKcard : kernelCount (RootTables.ofCert e6Certificate) a b = K.card := by
    rw [kernelCount]
    simp only [RootTables.ofCert, List.length_map, List.length_range, K]
    exact (List.toFinset_card_of_nodup ((List.nodup_range).filter _)).symm
  rw [hKcard]
  rw [← Set.ncard_coe_finset K]
  refine Set.ncard_congr (fun k _ => e6Certificate.root k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_coe, K, List.mem_toFinset, List.mem_filter, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq] at hk
    exact ⟨RootCertificate.isRoot_root e6Certificate_check k hk.1,
      (pairZ_emod_eq_zero_iff' hk.1 a).1 hk.2.1, (pairZ_emod_eq_zero_iff' hk.1 b).1 hk.2.2⟩
  · intro k₁ k₂ hk₁ hk₂ heq
    simp only [Finset.mem_coe, K, List.mem_toFinset, List.mem_filter, List.mem_range] at hk₁ hk₂
    exact hinj k₁ (List.mem_range.2 hk₁.1) k₂ (List.mem_range.2 hk₂.1) heq
  · intro γ hγ
    obtain ⟨hroot, h1, h2⟩ := hγ
    obtain ⟨k, hk, hkroot⟩ := (RootCertificate.isRoot_iff e6Certificate_check).1 hroot
    refine ⟨k, ?_, hkroot⟩
    rw [← hkroot] at h1 h2
    simp only [Finset.mem_coe, K, List.mem_toFinset, List.mem_filter, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hk, (pairZ_emod_eq_zero_iff' hk a).2 h1, (pairZ_emod_eq_zero_iff' hk b).2 h2⟩

theorem triPairing_comb' (c₀ c₁ : ZMod 3) (b₀ b₁ : Fin Tag.E6.rank → ZMod 3)
    (v : Fin Tag.E6.rank → ℤ) :
    triPairing (c₀ • b₀ + c₁ • b₁) v = c₀ * triPairing b₀ v + c₁ * triPairing b₁ v := by
  simp only [triPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem triPairing_single' (b : Fin Tag.E6.rank → ZMod 3) (j : Fin Tag.E6.rank) :
    triPairing b (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = b j := by
  have h := triPairing_zsmul_single b 1 j
  rwa [one_smul, Int.cast_one, mul_one] at h

theorem indep_transport {b₀ b₁ a b' : Fin Tag.E6.rank → ZMod 3} {w0 : WeylGroup .E6}
    (hp0 : ∀ u, triPairing a u = triPairing b₀ (w0 • u))
    (hp1 : ∀ u, triPairing b' u = triPairing b₁ (w0 • u))
    (hind : ∀ c₀ c₁ : ZMod 3, c₀ • b₀ + c₁ • b₁ = 0 → c₀ = 0 ∧ c₁ = 0) :
    ∀ c₀ c₁ : ZMod 3, c₀ • a + c₁ • b' = 0 → c₀ = 0 ∧ c₁ = 0 := by
  intro c₀ c₁ h
  have hz : ∀ v, triPairing (c₀ • b₀ + c₁ • b₁) v = 0 := by
    intro v
    have h1 := hp0 (w0⁻¹ • v)
    have h2 := hp1 (w0⁻¹ • v)
    rw [smul_inv_smul] at h1 h2
    calc triPairing (c₀ • b₀ + c₁ • b₁) v
        = c₀ * triPairing b₀ v + c₁ * triPairing b₁ v := triPairing_comb' c₀ c₁ b₀ b₁ v
      _ = c₀ * triPairing a (w0⁻¹ • v) + c₁ * triPairing b' (w0⁻¹ • v) := by rw [h1, h2]
      _ = triPairing (c₀ • a + c₁ • b') (w0⁻¹ • v) :=
            (triPairing_comb' c₀ c₁ a b' (w0⁻¹ • v)).symm
      _ = 0 := by rw [h]; simp [triPairing]
  have hbij : c₀ • b₀ + c₁ • b₁ = 0 := by
    funext j
    rw [← triPairing_single' (c₀ • b₀ + c₁ • b₁) j]
    exact hz (Pi.single j 1)
  exact hind c₀ c₁ hbij

theorem vec3_replicate_zero' :
    vec3 (τ := .E6) (List.replicate 6 0) = 0 := by
  funext j
  have hj : (j : ℕ) < 6 := j.2
  change (((List.replicate 6 0).getD (j : ℕ) 0 : ℕ) : ZMod 3) = 0
  rw [List.getD_replicate (0 : ℕ) hj, Nat.cast_zero]

theorem getD_map_twice' (l : List ℕ) (n : ℕ) :
    (l.map (fun x => 2 * x % 3)).getD n 0 = 2 * (l.getD n 0) % 3 := by
  have h := List.getD_map l 0 (fun x => 2 * x % 3) (n := n)
  simpa using h

theorem vec3_map_twice' (l : List ℕ) :
    vec3 (τ := .E6) (l.map (fun x => 2 * x % 3)) = (2 : ZMod 3) • vec3 (τ := .E6) l := by
  funext j
  simp only [vec3, Pi.smul_apply, smul_eq_mul]
  rw [getD_map_twice', ZMod.natCast_mod, Nat.cast_mul]; norm_num

theorem independent_of_vec_indep {l₁ l₂ : List ℕ}
    (hind : ∀ c₀ c₁ : ZMod 3,
      c₀ • vec3 (τ := .E6) l₁ + c₁ • vec3 (τ := .E6) l₂ = 0 → c₀ = 0 ∧ c₁ = 0) :
    independent l₁ l₂ = true := by
  have h10 : l₁ ≠ List.replicate 6 0 := by
    intro h
    have hz : vec3 (τ := .E6) l₁ = 0 := by
      rw [h]; exact vec3_replicate_zero'
    have hc := hind 1 0 (by rw [hz, smul_zero, zero_smul, add_zero])
    exact one_ne_zero hc.1
  have h20 : l₂ ≠ List.replicate 6 0 := by
    intro h
    have hz : vec3 (τ := .E6) l₂ = 0 := by
      rw [h]; exact vec3_replicate_zero'
    have hc := hind 0 1 (by rw [hz, smul_zero, zero_smul, zero_add])
    exact one_ne_zero hc.2
  have h21 : l₂ ≠ l₁ := by
    intro h
    have hz : (1 : ZMod 3) • vec3 (τ := .E6) l₁ +
        (2 : ZMod 3) • vec3 (τ := .E6) l₂ = 0 := by
      rw [h, ← add_smul, (by decide : (1 : ZMod 3) + 2 = 0), zero_smul]
    have hc := hind 1 2 hz
    exact one_ne_zero hc.1
  have h2m : l₂ ≠ l₁.map (fun x => 2 * x % 3) := by
    intro h
    have hz : vec3 (τ := .E6) l₂ = (2 : ZMod 3) • vec3 (τ := .E6) l₁ := by
      rw [h]
      exact vec3_map_twice' l₁
    have hcomb : (2 : ZMod 3) • vec3 (τ := .E6) l₁ +
        (2 : ZMod 3) • vec3 (τ := .E6) l₂ = 0 := by
      rw [hz, smul_smul, ← add_smul,
        (by decide : (2 : ZMod 3) + 2 * 2 = 0), zero_smul]
    have hc := hind 2 2 hcomb
    exact absurd hc.1 (by decide)
  rw [independent]
  simp only [Bool.and_eq_true, bne_iff_ne]
  exact ⟨⟨⟨h10, h20⟩, h21⟩, h2m⟩

theorem ncard_transport
    {b₀ b₁ a b' : Fin Tag.E6.rank → ZMod 3} {w0 : WeylGroup .E6}
    (hp0 : ∀ u, triPairing a u = triPairing b₀ (w0 • u))
    (hp1 : ∀ u, triPairing b' u = triPairing b₁ (w0 • u)) :
    {γ | IsRoot .E6 γ ∧ triPairing a γ = 0 ∧ triPairing b' γ = 0}.ncard =
      {γ | IsRoot .E6 γ ∧ triPairing b₀ γ = 0 ∧ triPairing b₁ γ = 0}.ncard := by
  refine Set.ncard_congr (fun γ _ => w0 • γ) ?_ ?_ ?_
  · intro γ hγ
    exact ⟨(isRoot_smul_iff w0).2 hγ.1, (hp0 γ).symm.trans hγ.2.1,
      (hp1 γ).symm.trans hγ.2.2⟩
  · intro γ₁ γ₂ _ _ heq
    exact MulAction.injective w0 heq
  · intro δ hδ
    refine ⟨w0⁻¹ • δ, ⟨(isRoot_smul_iff w0⁻¹).2 hδ.1, ?_, ?_⟩, ?_⟩
    · rw [hp0]; simp only [smul_inv_smul]; exact hδ.2.1
    · rw [hp1]; simp only [smul_inv_smul]; exact hδ.2.2
    · simp only [smul_inv_smul]

theorem shift_transport
    {b b₀ : Fin Tag.E6.rank → ZMod 3} {w0 w : WeylGroup .E6}
    (hconj : IsCharConj (triChar b) (triChar b₀) w0)
    (hw : w ∈ charStabilizer (triChar b₀)) :
    triPairing b (e6Shift (w0⁻¹ * w * w0)) = triPairing b₀ (e6Shift w) := by
  have hx : w0⁻¹ * w * w0 ∈ charStabilizer (triChar b) :=
    (charStabilizer_iff_of_isCharConj hconj).1 hw
  have hpair : ∀ v, triPairing b₀ v = triPairing b (w0⁻¹ • v) := fun v => by
    have h := hconj v
    rw [triChar_apply, triChar_apply, Z3.ofAdd_eq_ofAdd_iff] at h
    exact h
  have hcancel : triPairing b (w0⁻¹ • e6Shift w0) + triPairing b (e6Shift w0⁻¹) = 0 := by
    have h := congrArg (triPairing b) (e6Shift_mul w0⁻¹ w0)
    rw [inv_mul_cancel, e6Shift_one, triPairing_zero, triPairing_add] at h
    exact h.symm
  calc triPairing b (e6Shift (w0⁻¹ * w * w0))
      = triPairing b (e6Shift (w0⁻¹ * (w * w0))) := by rw [mul_assoc]
    _ = triPairing b (w0⁻¹ • e6Shift (w * w0) + e6Shift w0⁻¹) := by rw [e6Shift_mul]
    _ = triPairing b (w0⁻¹ • e6Shift (w * w0)) + triPairing b (e6Shift w0⁻¹) := by
          rw [triPairing_add]
    _ = triPairing b (w0⁻¹ • (w • e6Shift w0 + e6Shift w)) +
          triPairing b (e6Shift w0⁻¹) := by rw [e6Shift_mul]
    _ = triPairing b (w0⁻¹ • (w • e6Shift w0)) + triPairing b (w0⁻¹ • e6Shift w) +
          triPairing b (e6Shift w0⁻¹) := by rw [smul_add, triPairing_add]
    _ = triPairing b ((w0⁻¹ * w) • e6Shift w0) + triPairing b (w0⁻¹ • e6Shift w) +
          triPairing b (e6Shift w0⁻¹) := by rw [mul_smul]
    _ = triPairing b (w0⁻¹ • e6Shift w0) + triPairing b (w0⁻¹ • e6Shift w) +
          triPairing b (e6Shift w0⁻¹) := by
          have hs : (w0⁻¹ * w) • e6Shift w0 =
              (w0⁻¹ * w * w0) • (w0⁻¹ • e6Shift w0) := by
            conv_lhs => rw [(by group : w0⁻¹ * w = (w0⁻¹ * w * w0) * w0⁻¹)]
            rw [mul_smul]
          rw [hs, triPairing_smul_of_mem hx]
    _ = triPairing b₀ (e6Shift w) := by
          conv_lhs => rw [← hpair (e6Shift w)]
          rw [(by abel : triPairing b (w0⁻¹ • e6Shift w0) + triPairing b₀ (e6Shift w) +
              triPairing b (e6Shift w0⁻¹) = triPairing b₀ (e6Shift w) +
              (triPairing b (w0⁻¹ • e6Shift w0) + triPairing b (e6Shift w0⁻¹)))]
          rw [hcancel, add_zero]

@[expose] def ShiftFree (x : Fin Tag.E6.rank → ZMod 3) : Prop :=
  ∀ w ∈ charStabilizer (triChar x), triPairing x (e6Shift w) = 0

theorem shiftFree_of_isCharConj
    {a x : Fin Tag.E6.rank → ZMod 3} {t : WeylGroup .E6}
    (h : IsCharConj (triChar a) (triChar x) t) (ha : ShiftFree a) : ShiftFree x := by
  intro w hw
  rw [← shift_transport h hw]
  exact ha _ ((charStabilizer_iff_of_isCharConj h).1 hw)

theorem passOneCheck_spec (hp : passOneCheck () = true) {ρ : ℕ} (hρ : ρ ∈ [1, 2, 3, 4, 5]) :
    (e6ThreeStabs.getD ρ ⟨[], [], []⟩).passing e6Certificate = [List.range Tag.E6.rank] := by
  simp only [passOneCheck, passOneCheckWith, List.all_eq_true, beq_iff_eq] at hp
  exact hp ρ hρ

theorem shiftFree_rep
    (hp : passOneCheck () = true) {ρ : ℕ}
    (hρ : ρ ∈ [1, 2, 3, 4, 5]) : ShiftFree (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) := by
  have hpass := passOneCheck_spec hp hρ
  have hlt : ρ < e6ThreeStabs.length := by
    have h8 : e6ThreeStabs.length = 8 := rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    omega
  have hvec : (e6ThreeStabs.getD ρ ⟨[], [], []⟩).vec = e6ThreeReps.getD ρ [] := by
    have h := List.getD_map e6ThreeStabs ⟨[], [], []⟩ StabCert3.vec (n := ρ)
    rw [e6ThreeStabs_vec] at h
    exact h.symm
  have hmem : e6ThreeStabs.getD ρ ⟨[], [], []⟩ ∈ e6ThreeStabs := by
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  obtain ⟨hScheck, -⟩ := e6ThreeScCheck_spec.2 _ hmem
  intro w hw
  rw [← hvec] at hw ⊢
  obtain ⟨u, hu, hwu⟩ := exists_mul_mem_kernelPosStabilizer hw
  obtain ⟨t, ht, hrep⟩ := StabCert3.exists_passing_of_mem e6Certificate_check hScheck hwu
  rw [hpass, List.mem_singleton] at ht
  subst ht
  have h1 : w * u = 1 := represents_unique hrep (represents_one e6Certificate_check)
  rw [eq_inv_of_mul_eq_one_left h1]
  exact triPairing_e6Shift_of_mem_kernelWeylGroup (inv_mem hu)

theorem idx3_spec : ∀ l : List ℕ, (∀ x ∈ l, x < 3) →
    idx3 l < 3 ^ l.length ∧ ∀ j, idx3 l / 3 ^ j % 3 = l.getD j 0
  | [], _ => by simp [idx3]
  | d :: l, h => by
    have hd : d < 3 := h d (by simp)
    obtain ⟨ih1, ih2⟩ := idx3_spec l fun x hx => h x (by simp [hx])
    have he : idx3 (d :: l) = d + 3 * idx3 l := rfl
    refine ⟨?_, fun j => ?_⟩
    · rw [he, List.length_cons, pow_succ]
      generalize 3 ^ l.length = N at ih1 ⊢
      omega
    · cases j with
      | zero =>
        rw [he, pow_zero, Nat.div_one, List.getD_cons_zero]
        omega
      | succ j =>
        rw [he, pow_succ', ← Nat.div_div_eq_div_mul, List.getD_cons_succ, ← ih2 j]
        congr 2
        omega

theorem nsAux_spec (mask : ℕ) : ∀ (es : List ℕ) (m : ℕ), nsAux mask m es = true →
    ∀ k (hk : k < es.length), mask.testBit (m + k) =
      (decide (1 ≤ entryRep es[k]) && decide (entryRep es[k] ≤ 5)) := by
  intro es
  induction es with
  | nil => intro m _ k hk; exact absurd hk (by simp)
  | cons e es ih =>
    intro m h k hk
    simp only [nsAux, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    cases k with
    | zero => simpa using h1
    | succ k =>
      have := ih (m + 1) h2 k (by simpa using hk)
      rw [(by omega : m + (k + 1) = m + 1 + k)]
      simpa using this

theorem addL_lt : ∀ (a b : List ℕ) (k : ℕ), ∀ x ∈ addL a b k, x < 3
  | [], _, _, x, hx => by simp [addL] at hx
  | _ :: _, [], _, x, hx => by simp [addL] at hx
  | y :: a, z :: b, k, x, hx => by
    simp only [addL, List.zipWith_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by norm_num)
    · exact addL_lt a b k x hx

theorem digits3_lt (n : ℕ) : ∀ x ∈ digits3 .E6 n, x < 3 := by
  intro x hx
  simp only [digits3, List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact Nat.mod_lt _ (by norm_num)

theorem length_addL {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6) (k : ℕ) :
    (addL a b k).length = 6 := by
  rw [addL, List.length_zipWith, ha, hb, min_self]

theorem shiftFree_of_nsBit
    (hns : nsMaskCheck () = true) (hp : passOneCheck () = true)
    {l : List ℕ} (hlen : l.length = 6) (h3 : ∀ x ∈ l, x < 3) (hl : nsBit nsMask l = true) :
    ShiftFree (vec3 (τ := .E6) l) := by
  obtain ⟨hlt, hdig⟩ := idx3_spec l h3
  rw [hlen] at hlt
  have hvl0 : vec3 (τ := .E6) l = vec3OfIndex (idx3 l) := by
    funext j
    simp only [vec3, vec3OfIndex]
    rw [hdig]
  have horbit := e6ThreeScCheck_spec.1
  simp only [orbitCheck3, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at horbit
  obtain ⟨⟨hlenO, hreps⟩, hc⟩ := horbit
  have hk : idx3 l < e6ThreeOrbit.length := by
    rw [hlenO]
    exact hlt
  obtain ⟨-, hω⟩ := orbitAux3_spec (τ := .E6) (fun b hb => hreps b hb) e6ThreeOrbit 0 hc
    (idx3 l) hk
  rw [Nat.zero_add] at hω
  have hbit : nsMask.testBit (idx3 l) = true := hl
  have h1 := nsAux_spec nsMask e6ThreeOrbit 0 hns (idx3 l) hk
  rw [Nat.zero_add, hbit] at h1
  have h2 := h1.symm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  have hρ : entryRep e6ThreeOrbit[idx3 l] ∈ [1, 2, 3, 4, 5] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hvl : vec3 (τ := .E6) l = triAct (toFinWord3 (entryWord e6ThreeOrbit[idx3 l]))
      (vec3 (τ := .E6) (e6ThreeReps.getD (entryRep e6ThreeOrbit[idx3 l]) [])) := by
    rw [hω, hvl0]
  have hconj : IsCharConj (triChar (vec3 (τ := .E6)
      (e6ThreeReps.getD (entryRep e6ThreeOrbit[idx3 l]) [])))
      (triChar (vec3 (τ := .E6) l))
      ((coxeterSystem Tag.E6).wordProd (toFinWord3 (entryWord e6ThreeOrbit[idx3 l]))) :=
    fun v => by rw [hvl, triChar_triAct]
  exact shiftFree_of_isCharConj hconj (shiftFree_rep hp hρ)

theorem vec3_addL {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6) (k : ℕ) :
    vec3 (τ := .E6) (addL a b k) = vec3 (τ := .E6) a + (k : ZMod 3) • vec3 (τ := .E6) b := by
  funext j
  have hj : (j : ℕ) < 6 := j.2
  have hja : (j : ℕ) < a.length := by rw [ha]; exact hj
  have hjb : (j : ℕ) < b.length := by rw [hb]; exact hj
  have hjz : (j : ℕ) < (addL a b k).length := by
    rw [addL, List.length_zipWith, ha, hb, min_self]
    exact hj
  simp only [vec3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [List.getD_eq_getElem _ _ hjz, List.getD_eq_getElem _ _ hja, List.getD_eq_getElem _ _ hjb]
  simp only [addL, List.getElem_zipWith]
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]

theorem triPairing_add_smul (x y : Fin Tag.E6.rank → ZMod 3) (c : ZMod 3)
    (v : Fin Tag.E6.rank → ℤ) :
    triPairing (x + c • y) v = triPairing x v + c * triPairing y v := by
  simp only [triPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem mem_charStabilizer_add_smul {x y : Fin Tag.E6.rank → ZMod 3} {w : WeylGroup .E6}
    (hx : w ∈ charStabilizer (triChar x)) (hy : w ∈ charStabilizer (triChar y)) (c : ZMod 3) :
    w ∈ charStabilizer (triChar (x + c • y)) := by
  rw [mem_charStabilizer]
  intro v
  rw [triChar_apply, triChar_apply, Z3.ofAdd_eq_ofAdd_iff, triPairing_add_smul,
    triPairing_add_smul, triPairing_smul_of_mem hx, triPairing_smul_of_mem hy]

theorem eq_zero_of_two_lines : ∀ p q : ZMod 3, ∀ B₁ B₂ B₃ B₄ : Bool,
    2 ≤ ([B₁, B₂, B₃, B₄].filter id).length → (B₁ = true → p = 0) → (B₂ = true → q = 0) →
      (B₃ = true → p + 1 * q = 0) → (B₄ = true → p + 2 * q = 0) → p = 0 ∧ q = 0 := by
  decide

theorem shift_eq_zero_of_linesTest
    (hns : nsMaskCheck () = true) (hp : passOneCheck () = true)
    {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6) (ha3 : ∀ x ∈ a, x < 3)
    (hb3 : ∀ x ∈ b, x < 3) (hl : linesTest nsMask a b = true)
    {w : WeylGroup .E6} (hwa : w ∈ charStabilizer (triChar (vec3 (τ := .E6) a)))
    (hwb : w ∈ charStabilizer (triChar (vec3 (τ := .E6) b))) :
    triPairing (vec3 (τ := .E6) a) (e6Shift w) = 0 ∧
      triPairing (vec3 (τ := .E6) b) (e6Shift w) = 0 := by
  have hk : ∀ k : ℕ, nsBit nsMask (addL a b k) = true →
      triPairing (vec3 (τ := .E6) a) (e6Shift w) +
        (k : ZMod 3) * triPairing (vec3 (τ := .E6) b) (e6Shift w) = 0 := by
    intro k hx
    have h := shiftFree_of_nsBit hns hp (length_addL ha hb k) (addL_lt a b k) hx w
      (by rw [vec3_addL ha hb]; exact mem_charStabilizer_add_smul hwa hwb _)
    rwa [vec3_addL ha hb, triPairing_add_smul] at h
  refine eq_zero_of_two_lines _ _ (nsBit nsMask a) (nsBit nsMask b) (nsBit nsMask (addL a b 1))
    (nsBit nsMask (addL a b 2)) (of_decide_eq_true hl)
    (fun hx => shiftFree_of_nsBit hns hp ha ha3 hx w hwa)
    (fun hx => shiftFree_of_nsBit hns hp hb hb3 hx w hwb) (fun hx => ?_) (fun hx => ?_)
  · have h := hk 1 hx
    rwa [Nat.cast_one] at h
  · have h := hk 2 hx
    rwa [Nat.cast_ofNat] at h

theorem linesTest_of_check (hA : linesCheckWith (e6ThreeReps.take 4) nsMask 6 = true)
    (hB : linesCheckWith (e6ThreeReps.drop 4) nsMask 6 = true) {a : List ℕ}
    (ha : a ∈ e6ThreeReps) {code : ℕ} (hcode : code < 729)
    (hind : independent a (digits3 .E6 code) = true)
    (hlarge : 6 < kernelCount (RootTables.ofCert e6Certificate) a (digits3 .E6 code)) :
    linesTest nsMask a (digits3 .E6 code) = true := by
  have hall : linesCheckWith e6ThreeReps nsMask 6 = true := by
    rw [← List.take_append_drop 4 e6ThreeReps]
    simp only [linesCheckWith, List.all_append, Bool.and_eq_true] at hA hB ⊢
    exact ⟨hA, hB⟩
  simp only [linesCheckWith, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hall
  rcases hall a ha code hcode with h | h
  · exact h
  · rw [hind, decide_eq_true hlarge] at h
    exact absurd h (by decide)

theorem shift_eq_zero_of_checks
    (hA : linesCheckWith (e6ThreeReps.take 4) nsMask 6 = true)
    (hB : linesCheckWith (e6ThreeReps.drop 4) nsMask 6 = true)
    (hns : nsMaskCheck () = true) (hp : passOneCheck () = true)
    (b₀ b₁ : Fin Tag.E6.rank → ZMod 3)
    (hind : ∀ c₀ c₁ : ZMod 3, c₀ • b₀ + c₁ • b₁ = 0 → c₀ = 0 ∧ c₁ = 0)
    (hlarge : 6 < {γ | IsRoot .E6 γ ∧ triPairing b₀ γ = 0 ∧ triPairing b₁ γ = 0}.ncard)
    {w : WeylGroup .E6} (h₀ : w ∈ charStabilizer (triChar b₀))
    (h₁ : w ∈ charStabilizer (triChar b₁)) :
    triPairing b₀ (e6Shift w) = 0 ∧ triPairing b₁ (e6Shift w) = 0 := by
  obtain ⟨ρ, hρ, w0, hconj⟩ :=
    exists_isCharConj_of_orbitCheck3 e6ThreeScCheck_spec.1 (triChar b₀)
  set a : Fin Tag.E6.rank → ZMod 3 := vec3 (τ := .E6) (e6ThreeReps.getD ρ []) with ha
  have hpair0 : ∀ v, triPairing a v = triPairing b₀ (w0 • v) := fun v => by
    have h := hconj (w0 • v)
    rw [triChar_apply, triChar_apply, Z3.ofAdd_eq_ofAdd_iff] at h
    rw [inv_smul_smul] at h
    exact h.symm
  let b' : Fin Tag.E6.rank → ZMod 3 := fun j => triPairing b₁ (w0 • Pi.single j 1)
  have hb'pair : ∀ u, triPairing b' u = triPairing b₁ (w0 • u) := fun u => by
    exact (triPairing_smul_eq_of_basis' (b := b₁) (b' := b') (w := w0)
      (fun i => by simp [b', triPairing_single']) u).symm
  obtain ⟨n, hn, hbn⟩ := exists_vec3OfIndex b'
  have hn729 : n < 729 := hn
  have hb'vec : vec3 (τ := .E6) (digits3 .E6 n) = b' := by
    rw [vec3_digits3]; exact hbn
  have hmem : e6ThreeReps.getD ρ [] ∈ e6ThreeReps := by
    rw [List.getD_eq_getElem _ _ hρ]; exact List.getElem_mem hρ
  have hlarge' : 6 < kernelCount (RootTables.ofCert e6Certificate) (e6ThreeReps.getD ρ [])
      (digits3 .E6 n) := by
    rw [kernelCount_eq_ncard, ← ha, hb'vec, ncard_transport hpair0 hb'pair]
    exact hlarge
  have hindep : independent (e6ThreeReps.getD ρ []) (digits3 .E6 n) = true := by
    refine independent_of_vec_indep (l₁ := e6ThreeReps.getD ρ [])
      (l₂ := digits3 .E6 n) ?_
    intro c₀ c₁ h
    rw [← ha, hb'vec] at h
    exact indep_transport hpair0 hb'pair hind c₀ c₁ h
  have htest := linesTest_of_check hA hB hmem hn729 hindep hlarge'
  have hx : w0⁻¹ * w * w0 ∈ charStabilizer (triChar a) :=
    (charStabilizer_iff_of_isCharConj hconj).1 h₀
  have hconj1 : IsCharConj (triChar b') (triChar b₁) w0 := fun v => by
    have h := hb'pair (w0⁻¹ • v)
    rw [smul_inv_smul] at h
    rw [triChar_apply, triChar_apply, Z3.ofAdd_eq_ofAdd_iff]
    exact h.symm
  have hx1 : w0⁻¹ * w * w0 ∈ charStabilizer (triChar b') :=
    (charStabilizer_iff_of_isCharConj hconj1).1 h₁
  have hall : ∀ r ∈ e6ThreeReps, r.length = 6 ∧ ∀ x ∈ r, x < 3 := by decide
  obtain ⟨hφa, hφb'⟩ := shift_eq_zero_of_linesTest hns hp (hall _ hmem).1 (length_digits3 n)
    (hall _ hmem).2 (digits3_lt n) htest hx (by rw [hb'vec]; exact hx1)
  rw [hb'vec] at hφb'
  exact ⟨by rw [← shift_transport hconj h₀]; exact hφa,
    by rw [← shift_transport hconj1 h₁]; exact hφb'⟩

end CFSG.KC.E6PlaneLines
